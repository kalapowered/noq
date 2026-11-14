use alloc::collections::VecDeque;
use core::{
    cmp::{Ordering, max},
    mem,
};

use bytes::{Buf, Bytes, BytesMut};

use crate::range_set::ArrayRangeSet;

/// Helper to assemble unordered stream frames into an ordered stream
#[derive(Debug, Default)]
pub(super) struct Assembler {
    state: State,
    /// Buffered chunks, in `Buffer::cmp` order.
    data: VecDeque<Buffer>,
    /// Total number of buffered bytes, including duplicates in ordered mode.
    buffered: usize,
    /// Estimated number of allocated bytes, will never be less than `buffered`.
    allocated: usize,
    /// Number of bytes read by the application. When only ordered reads have been used, this is
    /// the length of the contiguous prefix of the stream which has been consumed by the
    /// application, aka the stream offset.
    bytes_read: u64,
    end: u64,
    #[cfg(test)]
    stats: Stats,
}

impl Assembler {
    pub(super) fn new() -> Self {
        Self::default()
    }

    /// Reset to the initial state
    pub(super) fn reinit(&mut self) {
        let old_data = mem::take(&mut self.data);
        *self = Self::default();
        self.data = old_data;
        self.data.clear();
    }

    pub(super) fn is_ordered(&self) -> bool {
        self.state.is_ordered()
    }

    pub(super) fn ensure_ordering(&mut self, ordered: bool) -> Result<(), IllegalOrderedRead> {
        if ordered && !self.state.is_ordered() {
            return Err(IllegalOrderedRead);
        } else if !ordered && self.state.is_ordered() {
            // Enter unordered mode
            if !self.data.is_empty() {
                // Get rid of possible duplicates
                self.defragment(self.bytes_read);
            }
            let mut recvd = ArrayRangeSet::new();
            recvd.insert(0..self.bytes_read);
            for chunk in &self.data {
                recvd.insert(chunk.offset..chunk.offset + chunk.bytes.len() as u64);
            }
            self.state = State::Unordered { recvd };
        }
        Ok(())
    }

    /// Get the the next chunk
    pub(super) fn read(&mut self, max_length: usize, ordered: bool) -> Option<Chunk> {
        loop {
            let chunk = self.data.front_mut()?;

            if ordered {
                if chunk.offset > self.bytes_read {
                    // Next chunk is after current read index
                    return None;
                } else if (chunk.offset + chunk.bytes.len() as u64) <= self.bytes_read {
                    // Next chunk is useless as the read index is beyond its end
                    self.buffered -= chunk.bytes.len();
                    self.allocated -= chunk.allocation_size;
                    self.data.pop_front();
                    continue;
                }

                // Determine `start` and `len` of the slice of useful data in chunk
                let start = (self.bytes_read - chunk.offset) as usize;
                // Advancing the offset can push the front past data[1]; both exits below fix that
                if start > 0 {
                    chunk.bytes.advance(start);
                    chunk.offset += start as u64;
                    self.buffered -= start;
                }
            }

            if max_length < chunk.bytes.len() {
                self.bytes_read += max_length as u64;
                let offset = chunk.offset;
                chunk.offset += max_length as u64;
                self.buffered -= max_length;
                let bytes = chunk.bytes.split_to(max_length);
                self.restore_front_order();
                return Some(Chunk::new(offset, bytes));
            }

            self.bytes_read += chunk.bytes.len() as u64;
            self.buffered -= chunk.bytes.len();
            self.allocated -= chunk.allocation_size;
            let offset = chunk.offset;
            let bytes = mem::take(&mut chunk.bytes);
            self.data.pop_front();
            return Some(Chunk::new(offset, bytes));
        }
    }

    /// Restore ordering after `read` advanced the front's offset.
    fn restore_front_order(&mut self) {
        if self.data.len() < 2 || self.data[0] <= self.data[1] {
            return;
        }
        let chunk = self.data.pop_front().unwrap();
        let idx = self.data.partition_point(|other| *other <= chunk);
        self.data.insert(idx, chunk);
    }

    /// Copy fragmented chunk data to new chunks backed by a single buffer
    ///
    /// This makes sure we're not unnecessarily holding on to many larger allocations.
    /// We merge contiguous chunks in the process of doing so. Bytes before `start`
    /// are treated as already delivered and discarded.
    fn defragment(&mut self, start: u64) {
        // Chunks smaller than min_chunk_size are merged regardless of fragmentation
        let min_chunk_size = max(self.buffered.div_ceil(MAX_CHUNKS), MIN_RETAINED_CHUNK_SIZE);
        let mut buffers = mem::take(&mut self.data);
        self.buffered = 0;
        let mut fragmented_buffered = 0;
        let mut offset = start;
        for chunk in &mut buffers {
            chunk.try_mark_defragment(offset);
            let size = chunk.bytes.len();
            offset = chunk.offset + size as u64;
            self.buffered += size;
            if !chunk.defragmented || size < min_chunk_size {
                fragmented_buffered += size;
            }
        }
        self.allocated = self.buffered;
        #[cfg(test)]
        {
            self.stats.compactions += 1;
            self.stats.copied_by_defragment += fragmented_buffered as u64;
        }
        self.data.reserve(buffers.len());
        let mut buffer = BytesMut::with_capacity(fragmented_buffered);
        let mut offset = start;
        for chunk in buffers {
            // bytes might be empty after try_mark_defragment
            if chunk.bytes.is_empty() {
                continue;
            }
            if chunk.defragmented && chunk.bytes.len() >= min_chunk_size {
                // The accumulated chunk starts before this one, so it goes first
                if !buffer.is_empty() {
                    self.data
                        .push_back(Buffer::new_defragmented(offset, buffer.split().freeze()));
                }
                offset = chunk.offset + chunk.bytes.len() as u64;
                self.data.push_back(chunk);
                continue;
            }
            // Overlap is resolved by try_mark_defragment
            if chunk.offset != offset + (buffer.len() as u64) {
                if !buffer.is_empty() {
                    self.data
                        .push_back(Buffer::new_defragmented(offset, buffer.split().freeze()));
                }
                offset = chunk.offset;
            }
            buffer.extend_from_slice(&chunk.bytes);
        }
        if !buffer.is_empty() {
            self.data
                .push_back(Buffer::new_defragmented(offset, buffer.split().freeze()));
        }
    }

    /// Joins each run of chunks in which every chunk starts where the one before it ends into
    /// one chunk
    ///
    /// `defragment` keeps a large chunk apart from the chunks next to it, so that the large
    /// chunk is not copied at every compaction. A stream of large chunks with runs of small ones
    /// between them therefore keeps about two entries for each large chunk, whether or not any
    /// data is missing. Joined, the entries are the stretches of received data, which is what
    /// `MAX_CHUNKS` is meant to bound.
    ///
    /// Must follow `defragment`, which leaves the chunks in order and without overlap. Discards
    /// nothing and never bridges a hole: only chunks that touch are joined, and a run of one
    /// chunk keeps its buffer. `buffered`, `allocated`, `end`, `bytes_read` and the set of
    /// received offsets of unordered reads are unchanged. A chunk may start below `bytes_read`,
    /// as it may after `defragment(0)`; the joined chunk keeps those bytes for `read` to trim.
    fn join_contiguous(&mut self) {
        debug_assert!(
            self.data
                .iter()
                .zip(self.data.iter().skip(1))
                .all(|(a, b)| a.offset + a.bytes.len() as u64 <= b.offset),
            "chunks must be in order and disjoint before they are joined"
        );
        let mut chunks = mem::take(&mut self.data);
        let mut joined = VecDeque::with_capacity(chunks.len());
        #[cfg(test)]
        {
            self.stats.joins += 1;
        }
        while let Some(run) = leading_run(&chunks) {
            if run.chunks == 1 {
                joined.extend(chunks.pop_front());
                continue;
            }
            let mut buffer = BytesMut::with_capacity(run.len);
            let offset = chunks[0].offset;
            // Each chunk is released as soon as it is copied
            for chunk in chunks.drain(..run.chunks) {
                buffer.extend_from_slice(&chunk.bytes);
            }
            #[cfg(test)]
            {
                self.stats.copied_by_join += run.len as u64;
                self.stats.largest_run = self.stats.largest_run.max(run.len);
            }
            joined.push_back(Buffer::new_defragmented(offset, buffer.freeze()));
        }
        self.data = joined;
        debug_assert_eq!(
            self.data.iter().map(|c| c.allocation_size).sum::<usize>(),
            self.allocated,
            "the joined chunks account for the allocation as defragmented chunks do"
        );
    }

    // Note: If a packet contains many frames from the same stream, the estimated over-allocation
    // will be much higher because we are counting the same allocation multiple times.
    pub(super) fn insert(
        &mut self,
        mut offset: u64,
        mut bytes: Bytes,
        allocation_size: usize,
    ) -> Result<(), TooManyChunks> {
        debug_assert!(
            bytes.len() <= allocation_size,
            "allocation_size less than bytes.len(): {:?} < {:?}",
            allocation_size,
            bytes.len()
        );
        self.end = self.end.max(offset + bytes.len() as u64);
        if let State::Unordered { ref mut recvd } = self.state {
            // Discard duplicate data
            let range = offset..offset + bytes.len() as u64;
            for duplicate in recvd.iter_range(range.clone()) {
                if duplicate.start > offset {
                    let buffer = Buffer::new(
                        offset,
                        bytes.split_to((duplicate.start - offset) as usize),
                        allocation_size,
                    );
                    self.buffered += buffer.bytes.len();
                    self.allocated += buffer.allocation_size;
                    insert_ordered(&mut self.data, buffer);
                    offset = duplicate.start;
                }
                bytes.advance((duplicate.end - offset) as usize);
                offset = duplicate.end;
            }
            recvd.insert(range);
        } else if offset < self.bytes_read {
            if (offset + bytes.len() as u64) <= self.bytes_read {
                return Ok(());
            } else {
                let diff = self.bytes_read - offset;
                offset += diff;
                bytes.advance(diff as usize);
            }
        }

        // No early return when empty: the dedup loop above may already have pushed chunks.
        if !bytes.is_empty() {
            let buffer = Buffer::new(offset, bytes, allocation_size);
            self.buffered += buffer.bytes.len();
            self.allocated += buffer.allocation_size;
            insert_ordered(&mut self.data, buffer);
        }
        // `self.buffered` also counts duplicate bytes, therefore we use
        // `self.end - self.bytes_read` as an upper bound of buffered unique
        // bytes. This will cause a defragmentation if the amount of duplicate
        // bytes exceedes a proportion of the receive window size.
        let buffered = self.buffered.min((self.end - self.bytes_read) as usize);
        let over_allocation = self.allocated - buffered;
        // Rationale: on the one hand, we want to defragment rarely, ideally never
        // in non-pathological scenarios. However, a pathological or malicious
        // peer could send us one-byte frames, and since we use reference-counted
        // buffers in order to prevent copying, this could result in keeping a lot
        // of memory allocated. This limits over-allocation in proportion to the
        // buffered data. The constants are chosen somewhat arbitrarily and try to
        // balance between defragmentation overhead and over-allocation.
        let threshold = 32768.max(buffered * 3 / 2);
        // Small gapped frames hold over-allocation below the threshold, so bound the count too.
        if over_allocation > threshold || self.data.len() > COMPACT_THRESHOLD {
            self.defragment(0);
            // ngtcp2 uses a threshold of 4000 -- try to be a little more conservative?
            if self.data.len() > MAX_CHUNKS {
                // Chunks that touch are not gaps. Only what is still above the bound once they
                // are joined is a peer's doing.
                self.join_contiguous();
                #[cfg(test)]
                let bound = self.stats.bound_after_join.unwrap_or(MAX_CHUNKS_AFTER_JOIN);
                #[cfg(not(test))]
                let bound = MAX_CHUNKS_AFTER_JOIN;
                if self.data.len() > bound {
                    return Err(TooManyChunks);
                }
            }
        }

        Ok(())
    }

    /// Number of bytes consumed by the application
    pub(super) fn bytes_read(&self) -> u64 {
        self.bytes_read
    }

    /// Discard all buffered data
    pub(super) fn clear(&mut self) {
        self.data.clear();
        self.buffered = 0;
        self.allocated = 0;
    }
}

/// A chunk of data from the receive stream
#[derive(Debug, PartialEq, Eq)]
pub struct Chunk {
    /// The offset in the stream
    pub offset: u64,
    /// The contents of the chunk
    pub bytes: Bytes,
}

impl Chunk {
    fn new(offset: u64, bytes: Bytes) -> Self {
        Self { offset, bytes }
    }
}

#[derive(Debug, Eq)]
struct Buffer {
    offset: u64,
    bytes: Bytes,
    /// Size of the allocation behind `bytes`, if `defragmented == false`.
    /// Otherwise this will be set to `bytes.len()` by `try_mark_defragment`.
    /// Will never be less than `bytes.len()`.
    allocation_size: usize,
    defragmented: bool,
}

impl Buffer {
    /// Constructs a new fragmented Buffer
    fn new(offset: u64, bytes: Bytes, allocation_size: usize) -> Self {
        Self {
            offset,
            bytes,
            allocation_size,
            defragmented: false,
        }
    }

    /// Constructs a new defragmented Buffer
    fn new_defragmented(offset: u64, bytes: Bytes) -> Self {
        let allocation_size = bytes.len();
        Self {
            offset,
            bytes,
            allocation_size,
            defragmented: true,
        }
    }

    /// Discards data before `offset` and flags `self` as defragmented if it has good utilization
    fn try_mark_defragment(&mut self, offset: u64) {
        let duplicate = offset.saturating_sub(self.offset) as usize;
        self.offset = self.offset.max(offset);
        if duplicate >= self.bytes.len() {
            // All bytes are duplicate
            self.bytes = Bytes::new();
            self.defragmented = true;
            self.allocation_size = 0;
            return;
        }
        self.bytes.advance(duplicate);
        // Make sure that fragmented buffers with high utilization become defragmented and
        // defragmented buffers remain defragmented
        self.defragmented = self.defragmented || self.bytes.len() * 6 / 5 >= self.allocation_size;
        if self.defragmented {
            // Make sure that defragmented buffers do not contribute to over-allocation
            self.allocation_size = self.bytes.len();
        }
    }
}

impl Ord for Buffer {
    // Ascending offset, longer chunks first at equal offsets
    fn cmp(&self, other: &Self) -> Ordering {
        self.offset
            .cmp(&other.offset)
            .then(other.bytes.len().cmp(&self.bytes.len()))
    }
}

impl PartialOrd for Buffer {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Buffer {
    fn eq(&self, other: &Self) -> bool {
        (self.offset, self.bytes.len()) == (other.offset, other.bytes.len())
    }
}

#[derive(Debug, Default)]
enum State {
    #[default]
    Ordered,
    Unordered {
        /// The set of offsets that have been received from the peer, including portions not yet
        /// read by the application.
        recvd: ArrayRangeSet,
    },
}

impl State {
    fn is_ordered(&self) -> bool {
        matches!(self, Self::Ordered)
    }
}

/// Error indicating that an ordered read was performed on a stream after an unordered read
#[derive(Debug)]
pub(crate) struct IllegalOrderedRead;

/// Error indicating that too many chunks are buffered due to maliciously small/gapped frames.
#[derive(Debug)]
pub(crate) struct TooManyChunks;

/// O(1) for a frame in order or below everything buffered, otherwise an insert that
/// shifts up to half of `data` (see `COMPACT_THRESHOLD`).
fn insert_ordered(data: &mut VecDeque<Buffer>, buffer: Buffer) {
    if data.back().is_none_or(|back| *back <= buffer) {
        data.push_back(buffer);
        return;
    }
    // Order among equal chunks is unspecified, as it was under the heap, so a duplicate
    // of the front takes this path rather than an insert
    if data.front().is_some_and(|front| buffer <= *front) {
        data.push_front(buffer);
        return;
    }
    let idx = data.partition_point(|chunk| *chunk <= buffer);
    data.insert(idx, buffer);
}

/// A run of chunks that touch one another
struct Run {
    /// Number of chunks
    chunks: usize,
    /// Total length of the chunks
    len: usize,
}

/// The run that the first chunk starts, or `None` if there are no chunks
fn leading_run(chunks: &VecDeque<Buffer>) -> Option<Run> {
    let mut iter = chunks.iter();
    let first = iter.next()?;
    let mut end = first.offset + first.bytes.len() as u64;
    let mut run = Run {
        chunks: 1,
        len: first.bytes.len(),
    };
    for chunk in iter {
        if chunk.offset != end {
            break;
        }
        end += chunk.bytes.len() as u64;
        run.chunks += 1;
        run.len += chunk.bytes.len();
    }
    Some(run)
}

/// Bound on the number of distinct spans kept for a stream.
///
/// Independent of how much memory those spans over-allocate. A frame is rejected only
/// if compaction cannot get the count back down to this, and, when it can only by joining
/// chunks that touch, to `MAX_CHUNKS_AFTER_JOIN`.
const MAX_CHUNKS: usize = 1024;

/// Bound on the number of spans that remain after chunks that touch have been joined.
///
/// A join copies every run of two or more chunks. It runs only above `MAX_CHUNKS` entries and
/// leaves at most this many, so the next one needs more than `MAX_CHUNKS - MAX_CHUNKS_AFTER_JOIN`
/// frames to arrive. With `MAX_CHUNKS` here, a peer that holds a thousand gaps open could force
/// a copy of the buffer every hundred frames or so.
const MAX_CHUNKS_AFTER_JOIN: usize = MAX_CHUNKS / 2;

/// Minimum size of a defragmented chunk that is retained without coalescing.
///
/// Chunks below this size will be copied on every compaction. 128 bytes balances
/// being cheap to copy while reducing the overhead of many small buffer nodes.
const MIN_RETAINED_CHUNK_SIZE: usize = 128;

/// Chunk count past which `insert` compacts before deciding whether to reject.
///
/// Above `MAX_CHUNKS` so a flood of mergeable frames cannot force a defragmentation
/// per frame.
const COMPACT_THRESHOLD: usize = 2 * MAX_CHUNKS;

/// What compaction and joining have done to an assembler, for the tests
#[cfg(test)]
#[derive(Debug, Default)]
struct Stats {
    /// Calls of `defragment`
    compactions: u64,
    /// Joins
    joins: u64,
    /// Bytes that `defragment` copied
    copied_by_defragment: u64,
    /// Bytes that joins copied
    copied_by_join: u64,
    /// The longest run that a join copied, which is the most that a join allocates at once
    largest_run: usize,
    /// Replaces `MAX_CHUNKS_AFTER_JOIN`
    bound_after_join: Option<usize>,
}

#[cfg(test)]
mod test {
    use alloc::{vec, vec::Vec};

    use rand::prelude::*;
    use rand_pcg::Pcg32;

    use super::*;
    use assert_matches::assert_matches;

    #[test]
    fn assemble_ordered() {
        let mut x = Assembler::new();
        assert_matches!(next(&mut x, 32), None);
        x.insert(0, Bytes::from_static(b"123"), 3).unwrap();
        assert_matches!(next(&mut x, 1), Some(ref y) if &y[..] == b"1");
        assert_matches!(next(&mut x, 3), Some(ref y) if &y[..] == b"23");
        x.insert(3, Bytes::from_static(b"456"), 3).unwrap();
        assert_matches!(next(&mut x, 32), Some(ref y) if &y[..] == b"456");
        x.insert(6, Bytes::from_static(b"789"), 3).unwrap();
        x.insert(9, Bytes::from_static(b"10"), 2).unwrap();
        assert_matches!(next(&mut x, 32), Some(ref y) if &y[..] == b"789");
        assert_matches!(next(&mut x, 32), Some(ref y) if &y[..] == b"10");
        assert_matches!(next(&mut x, 32), None);
    }

    #[test]
    fn assemble_unordered() {
        let mut x = Assembler::new();
        x.ensure_ordering(false).unwrap();
        x.insert(3, Bytes::from_static(b"456"), 3).unwrap();
        assert_matches!(next(&mut x, 32), None);
        x.insert(0, Bytes::from_static(b"123"), 3).unwrap();
        assert_matches!(next(&mut x, 32), Some(ref y) if &y[..] == b"123");
        assert_matches!(next(&mut x, 32), Some(ref y) if &y[..] == b"456");
        assert_matches!(next(&mut x, 32), None);
    }

    #[test]
    fn assemble_duplicate() {
        let mut x = Assembler::new();
        x.insert(0, Bytes::from_static(b"123"), 3).unwrap();
        x.insert(0, Bytes::from_static(b"123"), 3).unwrap();
        assert_matches!(next(&mut x, 32), Some(ref y) if &y[..] == b"123");
        assert_matches!(next(&mut x, 32), None);
    }

    #[test]
    fn assemble_duplicate_compact() {
        let mut x = Assembler::new();
        x.insert(0, Bytes::from_static(b"123"), 3).unwrap();
        x.insert(0, Bytes::from_static(b"123"), 3).unwrap();
        x.defragment(0);
        assert_matches!(next(&mut x, 32), Some(ref y) if &y[..] == b"123");
        assert_matches!(next(&mut x, 32), None);
    }

    #[test]
    fn assemble_contained() {
        let mut x = Assembler::new();
        x.insert(0, Bytes::from_static(b"12345"), 5).unwrap();
        x.insert(1, Bytes::from_static(b"234"), 3).unwrap();
        assert_matches!(next(&mut x, 32), Some(ref y) if &y[..] == b"12345");
        assert_matches!(next(&mut x, 32), None);
    }

    #[test]
    fn assemble_contained_compact() {
        let mut x = Assembler::new();
        x.insert(0, Bytes::from_static(b"12345"), 5).unwrap();
        x.insert(1, Bytes::from_static(b"234"), 3).unwrap();
        x.defragment(0);
        assert_matches!(next(&mut x, 32), Some(ref y) if &y[..] == b"12345");
        assert_matches!(next(&mut x, 32), None);
    }

    #[test]
    fn assemble_contains() {
        let mut x = Assembler::new();
        x.insert(1, Bytes::from_static(b"234"), 3).unwrap();
        x.insert(0, Bytes::from_static(b"12345"), 5).unwrap();
        assert_matches!(next(&mut x, 32), Some(ref y) if &y[..] == b"12345");
        assert_matches!(next(&mut x, 32), None);
    }

    #[test]
    fn assemble_contains_compact() {
        let mut x = Assembler::new();
        x.insert(1, Bytes::from_static(b"234"), 3).unwrap();
        x.insert(0, Bytes::from_static(b"12345"), 5).unwrap();
        x.defragment(0);
        assert_matches!(next(&mut x, 32), Some(ref y) if &y[..] == b"12345");
        assert_matches!(next(&mut x, 32), None);
    }

    #[test]
    fn assemble_overlapping() {
        let mut x = Assembler::new();
        x.insert(0, Bytes::from_static(b"123"), 3).unwrap();
        x.insert(1, Bytes::from_static(b"234"), 3).unwrap();
        assert_matches!(next(&mut x, 32), Some(ref y) if &y[..] == b"123");
        assert_matches!(next(&mut x, 32), Some(ref y) if &y[..] == b"4");
        assert_matches!(next(&mut x, 32), None);
    }

    #[test]
    fn assemble_overlapping_compact() {
        let mut x = Assembler::new();
        x.insert(0, Bytes::from_static(b"123"), 4).unwrap();
        x.insert(1, Bytes::from_static(b"234"), 4).unwrap();
        x.defragment(0);
        assert_matches!(next(&mut x, 32), Some(ref y) if &y[..] == b"1234");
        assert_matches!(next(&mut x, 32), None);
    }

    #[test]
    fn assemble_complex() {
        let mut x = Assembler::new();
        x.insert(0, Bytes::from_static(b"1"), 1).unwrap();
        x.insert(2, Bytes::from_static(b"3"), 1).unwrap();
        x.insert(4, Bytes::from_static(b"5"), 1).unwrap();
        x.insert(0, Bytes::from_static(b"123456"), 6).unwrap();
        assert_matches!(next(&mut x, 32), Some(ref y) if &y[..] == b"123456");
        assert_matches!(next(&mut x, 32), None);
    }

    #[test]
    fn assemble_complex_compact() {
        let mut x = Assembler::new();
        x.insert(0, Bytes::from_static(b"1"), 1).unwrap();
        x.insert(2, Bytes::from_static(b"3"), 1).unwrap();
        x.insert(4, Bytes::from_static(b"5"), 1).unwrap();
        x.insert(0, Bytes::from_static(b"123456"), 6).unwrap();
        x.defragment(0);
        assert_matches!(next(&mut x, 32), Some(ref y) if &y[..] == b"123456");
        assert_matches!(next(&mut x, 32), None);
    }

    #[test]
    fn assemble_old() {
        let mut x = Assembler::new();
        x.insert(0, Bytes::from_static(b"1234"), 4).unwrap();
        assert_matches!(next(&mut x, 32), Some(ref y) if &y[..] == b"1234");
        x.insert(0, Bytes::from_static(b"1234"), 4).unwrap();
        assert_matches!(next(&mut x, 32), None);
    }

    #[test]
    fn compact() {
        let mut x = Assembler::new();
        x.insert(0, Bytes::from_static(b"abc"), 4).unwrap();
        x.insert(3, Bytes::from_static(b"def"), 4).unwrap();
        x.insert(9, Bytes::from_static(b"jkl"), 4).unwrap();
        x.insert(12, Bytes::from_static(b"mno"), 4).unwrap();
        x.defragment(0);
        assert_eq!(
            next_unordered(&mut x),
            Chunk::new(0, Bytes::from_static(b"abcdef"))
        );
        assert_eq!(
            next_unordered(&mut x),
            Chunk::new(9, Bytes::from_static(b"jklmno"))
        );
    }

    #[test]
    fn defrag_with_missing_prefix() {
        let mut x = Assembler::new();
        x.insert(3, Bytes::from_static(b"def"), 3).unwrap();
        x.defragment(0);
        assert_eq!(
            next_unordered(&mut x),
            Chunk::new(3, Bytes::from_static(b"def"))
        );
    }

    #[test]
    fn defrag_read_chunk() {
        let mut x = Assembler::new();
        x.insert(3, Bytes::from_static(b"def"), 4).unwrap();
        x.insert(0, Bytes::from_static(b"abc"), 4).unwrap();
        x.insert(7, Bytes::from_static(b"hij"), 4).unwrap();
        x.insert(11, Bytes::from_static(b"lmn"), 4).unwrap();
        x.defragment(0);
        assert_matches!(x.read(usize::MAX, true), Some(ref y) if &y.bytes[..] == b"abcdef");
        x.insert(5, Bytes::from_static(b"fghijklmn"), 9).unwrap();
        assert_matches!(x.read(usize::MAX, true), Some(ref y) if &y.bytes[..] == b"ghijklmn");
        x.insert(13, Bytes::from_static(b"nopq"), 4).unwrap();
        assert_matches!(x.read(usize::MAX, true), Some(ref y) if &y.bytes[..] == b"opq");
        x.insert(15, Bytes::from_static(b"pqrs"), 4).unwrap();
        assert_matches!(x.read(usize::MAX, true), Some(ref y) if &y.bytes[..] == b"rs");
        assert_matches!(x.read(usize::MAX, true), None);
    }

    #[test]
    fn unordered_happy_path() {
        let mut x = Assembler::new();
        x.ensure_ordering(false).unwrap();
        x.insert(0, Bytes::from_static(b"abc"), 3).unwrap();
        assert_eq!(
            next_unordered(&mut x),
            Chunk::new(0, Bytes::from_static(b"abc"))
        );
        assert_eq!(x.read(usize::MAX, false), None);
        x.insert(3, Bytes::from_static(b"def"), 3).unwrap();
        assert_eq!(
            next_unordered(&mut x),
            Chunk::new(3, Bytes::from_static(b"def"))
        );
        assert_eq!(x.read(usize::MAX, false), None);
    }

    #[test]
    fn unordered_dedup() {
        let mut x = Assembler::new();
        x.ensure_ordering(false).unwrap();
        x.insert(3, Bytes::from_static(b"def"), 3).unwrap();
        assert_eq!(
            next_unordered(&mut x),
            Chunk::new(3, Bytes::from_static(b"def"))
        );
        assert_eq!(x.read(usize::MAX, false), None);
        x.insert(0, Bytes::from_static(b"a"), 1).unwrap();
        x.insert(0, Bytes::from_static(b"abcdefghi"), 9).unwrap();
        x.insert(0, Bytes::from_static(b"abcd"), 4).unwrap();
        assert_eq!(
            next_unordered(&mut x),
            Chunk::new(0, Bytes::from_static(b"a"))
        );
        assert_eq!(
            next_unordered(&mut x),
            Chunk::new(1, Bytes::from_static(b"bc"))
        );
        assert_eq!(
            next_unordered(&mut x),
            Chunk::new(6, Bytes::from_static(b"ghi"))
        );
        assert_eq!(x.read(usize::MAX, false), None);
        x.insert(8, Bytes::from_static(b"ijkl"), 4).unwrap();
        assert_eq!(
            next_unordered(&mut x),
            Chunk::new(9, Bytes::from_static(b"jkl"))
        );
        assert_eq!(x.read(usize::MAX, false), None);
        x.insert(12, Bytes::from_static(b"mno"), 3).unwrap();
        assert_eq!(
            next_unordered(&mut x),
            Chunk::new(12, Bytes::from_static(b"mno"))
        );
        assert_eq!(x.read(usize::MAX, false), None);
        x.insert(2, Bytes::from_static(b"cde"), 3).unwrap();
        assert_eq!(x.read(usize::MAX, false), None);
    }

    #[test]
    fn chunks_dedup() {
        let mut x = Assembler::new();
        x.insert(3, Bytes::from_static(b"def"), 3).unwrap();
        assert_eq!(x.read(usize::MAX, true), None);
        x.insert(0, Bytes::from_static(b"a"), 1).unwrap();
        x.insert(1, Bytes::from_static(b"bcdefghi"), 9).unwrap();
        x.insert(0, Bytes::from_static(b"abcd"), 4).unwrap();
        assert_eq!(
            x.read(usize::MAX, true),
            Some(Chunk::new(0, Bytes::from_static(b"abcd")))
        );
        assert_eq!(
            x.read(usize::MAX, true),
            Some(Chunk::new(4, Bytes::from_static(b"efghi")))
        );
        assert_eq!(x.read(usize::MAX, true), None);
        x.insert(8, Bytes::from_static(b"ijkl"), 4).unwrap();
        assert_eq!(
            x.read(usize::MAX, true),
            Some(Chunk::new(9, Bytes::from_static(b"jkl")))
        );
        assert_eq!(x.read(usize::MAX, true), None);
        x.insert(12, Bytes::from_static(b"mno"), 3).unwrap();
        assert_eq!(
            x.read(usize::MAX, true),
            Some(Chunk::new(12, Bytes::from_static(b"mno")))
        );
        assert_eq!(x.read(usize::MAX, true), None);
        x.insert(2, Bytes::from_static(b"cde"), 3).unwrap();
        assert_eq!(x.read(usize::MAX, true), None);
    }

    #[test]
    fn ordered_eager_discard() {
        let mut x = Assembler::new();
        x.insert(0, Bytes::from_static(b"abc"), 3).unwrap();
        assert_eq!(x.data.len(), 1);
        assert_eq!(
            x.read(usize::MAX, true),
            Some(Chunk::new(0, Bytes::from_static(b"abc")))
        );
        x.insert(0, Bytes::from_static(b"ab"), 2).unwrap();
        assert_eq!(x.data.len(), 0);
        x.insert(2, Bytes::from_static(b"cd"), 2).unwrap();
        assert_eq!(
            x.data.front(),
            Some(&Buffer::new(3, Bytes::from_static(b"d"), 2))
        );
    }

    #[test]
    fn ordered_insert_unordered_read() {
        let mut x = Assembler::new();
        x.insert(0, Bytes::from_static(b"abc"), 3).unwrap();
        x.insert(0, Bytes::from_static(b"abc"), 3).unwrap();
        x.ensure_ordering(false).unwrap();
        assert_eq!(
            x.read(3, false),
            Some(Chunk::new(0, Bytes::from_static(b"abc")))
        );
        assert_eq!(x.read(3, false), None);
    }

    #[test]
    fn no_duplicate_after_mode_switch() {
        // Regression test: bytes read in ordered mode should not be returned again in unordered
        // mode
        let mut x = Assembler::new();
        x.insert(0, Bytes::from_static(b"a"), 1).unwrap();
        x.insert(0, Bytes::from_static(b"a"), 1).unwrap(); // duplicate
        assert_eq!(
            x.read(1, true),
            Some(Chunk::new(0, Bytes::from_static(b"a")))
        );
        x.ensure_ordering(false).unwrap();
        assert_eq!(x.read(1, false), None); // should be None, byte 0 already returned
    }

    #[test]
    fn ordered_lossless_stream_is_not_rejected() {
        const FRAME_LEN: usize = 32;

        let mut x = Assembler::new();
        let data = Bytes::from(vec![0; FRAME_LEN]);
        let mut offset = 0u64;
        while offset < (2 * COMPACT_THRESHOLD * FRAME_LEN) as u64 {
            x.insert(offset, data.clone(), FRAME_LEN)
                .expect("contiguous lossless data must not be rejected");
            offset += FRAME_LEN as u64;
        }
    }

    #[test]
    fn defrag_respects_max_chunks_at_rounding_boundary() {
        let mut x = Assembler::new();
        let data = Bytes::from(vec![0; MIN_RETAINED_CHUNK_SIZE]);
        let mut offset = 0;
        // Fill with minimum sized chunks.
        for _ in 0..MAX_CHUNKS {
            x.insert(offset, data.clone(), data.len()).unwrap();
            offset += data.len() as u64;
        }
        // Add 1 extra chunk, defragment must coalesce the previous
        // chunks to stay within MAX_CHUNKS
        x.insert(offset, Bytes::from_static(b"x"), 1).unwrap();
        x.defragment(0);
        assert!(x.data.len() <= MAX_CHUNKS);
    }

    #[test]
    fn unordered_compaction_keeps_unread_data() {
        let mut x = Assembler::new();
        x.ensure_ordering(false).unwrap();
        x.insert(10_000, Bytes::from(vec![1; 1000]), 1000).unwrap();
        assert_eq!(x.read(usize::MAX, false).unwrap().offset, 10_000);
        // The large allocation pushes over-allocation past the threshold, so this compacts
        x.insert(0, Bytes::from(vec![2; 500]), 100_000).unwrap();
        let next = x
            .read(usize::MAX, false)
            .expect("unread data was discarded");
        assert_eq!((next.offset, next.bytes.len()), (0, 500));
    }

    #[test]
    fn bounded_chunks_under_low_over_allocation() {
        // Gapped frames whose `allocation_size` equals their length hold
        // `over_allocation` at zero, so that trigger never fires.
        let mut x = Assembler::new();
        // Withhold offset 0 so an ordered reader can never drain anything.
        let mut offset = 1u64;
        let mut result = Ok(());
        for _ in 0..(MAX_CHUNKS * 8) {
            result = x.insert(offset, Bytes::from_static(b"gap"), 3);
            if result.is_err() {
                break;
            }
            offset += 3 + 1; // 3 data bytes, 1 byte gap
        }
        assert_matches!(result, Err(TooManyChunks));
        assert!(
            x.data.len() <= COMPACT_THRESHOLD + 1,
            "chunk count {} exceeded the bound",
            x.data.len()
        );
    }

    #[test]
    fn bounded_chunks_unordered_overlap_flood() {
        // Overlapping frames whose tail is already received: the dedup loop pushes
        // the fresh head byte and leaves `bytes` empty, and `end` never rises, so
        // the flood costs the peer no flow control.
        let mut x = Assembler::new();
        x.ensure_ordering(false).unwrap();
        let top = 1_000_000u64;
        x.insert(top, Bytes::from_static(b"ab"), 2).unwrap();
        for k in 0..(4 * MAX_CHUNKS as u64) {
            x.insert(top - k - 1, Bytes::from_static(b"ab"), 2).unwrap();
            assert!(
                x.data.len() <= COMPACT_THRESHOLD + 1,
                "chunk count {} exceeded the bound at k={k}",
                x.data.len()
            );
        }
    }

    #[test]
    fn bounded_chunks_duplicate_flood() {
        // Duplicates against a stream already at the cap. Ordered mode does not dedup,
        // so each one pushes a chunk; they must not be rejected, or compact every frame.
        let mut x = Assembler::new();
        // Withhold offset 0 so nothing can be drained.
        for i in 0..MAX_CHUNKS as u64 {
            x.insert(1 + i * 4, Bytes::from_static(b"abc"), 3).unwrap();
        }
        let mut max_len = x.data.len();
        for _ in 0..(3 * MAX_CHUNKS) {
            x.insert(1, Bytes::from_static(b"abc"), 3)
                .expect("duplicate flood must not be rejected");
            max_len = max_len.max(x.data.len());
            assert!(
                x.data.len() <= COMPACT_THRESHOLD + 1,
                "chunk count {} exceeded the bound",
                x.data.len()
            );
        }
        // Compacting on every frame would pin the count at `MAX_CHUNKS`.
        assert!(
            max_len > MAX_CHUNKS,
            "buffer compacted on every frame (max observed len {max_len})"
        );
    }

    // The tests that follow send a stream whose byte at position `p` is `content(p)`, so that
    // every byte that comes back can be compared with what was inserted.

    /// What a packet carries besides the stream data of one frame
    pub(super) const FRAME_OVERHEAD: usize = 8;

    /// The byte at `position` of the stream that the tests send
    fn content(position: u64) -> u8 {
        (position.wrapping_mul(0x9E37_79B9_7F4A_7C15) >> 56) as u8
    }

    /// The first `len` bytes of the stream
    fn stream_prefix(len: usize) -> Vec<u8> {
        (0..len as u64).map(content).collect()
    }

    /// The frame `[offset, offset + len)` of the stream
    pub(super) fn frame(offset: u64, len: usize) -> Bytes {
        Bytes::from(
            (offset..offset + len as u64)
                .map(content)
                .collect::<Vec<u8>>(),
        )
    }

    /// Reads one chunk, checking it against `stream` and that no byte comes twice. Returns
    /// whether anything could be read.
    #[track_caller]
    fn read_once(
        x: &mut Assembler,
        max: usize,
        ordered: bool,
        stream: &[u8],
        delivered: &mut [bool],
    ) -> bool {
        let Some(chunk) = x.read(max, ordered) else {
            return false;
        };
        let start = chunk.offset as usize;
        let end = start + chunk.bytes.len();
        assert_eq!(
            &chunk.bytes[..],
            &stream[start..end],
            "wrong bytes at offset {start}"
        );
        for d in &mut delivered[start..end] {
            assert!(!*d, "offset {start} delivered twice");
            *d = true;
        }
        assert_sorted(x);
        true
    }

    /// Reads `x` dry with reads of changing length
    #[track_caller]
    fn drain_varied(x: &mut Assembler, ordered: bool, stream: &[u8], delivered: &mut [bool]) {
        let lengths = [1, 7, 64, 333, usize::MAX];
        let mut i = 0;
        while read_once(x, lengths[i % lengths.len()], ordered, stream, delivered) {
            i += 1;
        }
    }

    /// Inserts one frame to a packet, of the lengths in `pattern` in turn, for the frame numbers
    /// in `frames`, from `*offset` on
    #[track_caller]
    fn insert_pattern(
        x: &mut Assembler,
        offset: &mut u64,
        pattern: &[usize],
        frames: core::ops::Range<usize>,
    ) {
        for i in frames {
            let len = pattern[i % pattern.len()];
            let result = x.insert(*offset, frame(*offset, len), len + FRAME_OVERHEAD);
            assert!(
                result.is_ok(),
                "frame {i} ({len} bytes at offset {offset}) was refused with {} chunks buffered, \
                 although the buffered data has at most one gap",
                x.data.len()
            );
            *offset += len as u64;
        }
    }

    fn pattern_len(pattern: &[usize], frames: usize) -> usize {
        (0..frames).map(|i| pattern[i % pattern.len()]).sum()
    }

    /// The application reads the first frame and then stops reading while the peer sends the rest
    #[track_caller]
    fn reader_behind(pattern: &[usize], frames: usize, ordered: bool) {
        let total = pattern_len(pattern, frames);
        let stream = stream_prefix(total);
        let mut delivered = vec![false; total];
        let mut x = Assembler::new();
        if !ordered {
            x.ensure_ordering(false).unwrap();
        }
        let mut offset = 0;
        insert_pattern(&mut x, &mut offset, pattern, 0..1);
        assert!(read_once(
            &mut x,
            usize::MAX,
            ordered,
            &stream,
            &mut delivered
        ));
        insert_pattern(&mut x, &mut offset, pattern, 1..frames);
        drain_varied(&mut x, ordered, &stream, &mut delivered);
        assert!(delivered.iter().all(|d| *d), "not every byte was delivered");
    }

    /// Offset 0 is missing while the peer sends the frames behind it. It is repaired afterwards.
    #[track_caller]
    fn missing_prefix(pattern: &[usize], frames: usize, ordered: bool) {
        let total = 1 + pattern_len(pattern, frames);
        let stream = stream_prefix(total);
        let mut delivered = vec![false; total];
        let mut x = Assembler::new();
        if !ordered {
            x.ensure_ordering(false).unwrap();
        }
        let mut offset = 1;
        insert_pattern(&mut x, &mut offset, pattern, 0..frames);
        if ordered {
            assert_eq!(x.read(usize::MAX, true), None, "nothing precedes the hole");
        } else {
            // A part of the first chunk, which the join may have made large
            assert!(read_once(&mut x, 5, false, &stream, &mut delivered));
        }
        x.insert(0, frame(0, 1), 1 + FRAME_OVERHEAD).unwrap();
        drain_varied(&mut x, ordered, &stream, &mut delivered);
        assert!(delivered.iter().all(|d| *d), "not every byte was delivered");
    }

    #[test]
    fn reader_behind_424_104_104_104() {
        reader_behind(&[424, 104, 104, 104], 2400, true);
    }

    #[test]
    fn reader_behind_424_104_104_104_unordered() {
        reader_behind(&[424, 104, 104, 104], 2400, false);
    }

    #[test]
    fn reader_behind_604_104_104() {
        reader_behind(&[604, 104, 104], 2400, true);
    }

    #[test]
    fn reader_behind_604_104_104_unordered() {
        reader_behind(&[604, 104, 104], 2400, false);
    }

    #[test]
    fn missing_prefix_424_104_104_104() {
        missing_prefix(&[424, 104, 104, 104], 2400, true);
    }

    #[test]
    fn missing_prefix_424_104_104_104_unordered() {
        missing_prefix(&[424, 104, 104, 104], 2400, false);
    }

    #[test]
    fn missing_prefix_604_104_104() {
        missing_prefix(&[604, 104, 104], 2400, true);
    }

    #[test]
    fn missing_prefix_604_104_104_unordered() {
        missing_prefix(&[604, 104, 104], 2400, false);
    }

    /// Large chunks with runs of small ones between them, behind one missing byte, as in a
    /// lossy bulk transfer
    #[test]
    fn large_and_small_chunks_behind_one_missing_byte() {
        missing_prefix(&[5000, 400, 400, 400], 2400, true);
    }

    #[test]
    fn large_and_small_chunks_behind_one_missing_byte_unordered() {
        missing_prefix(&[5000, 400, 400, 400], 2400, false);
    }

    const LARGE: usize = 400;
    const SMALL: usize = 4;

    /// What `staircase` leaves behind
    struct Staircase {
        x: Assembler,
        result: Result<(), TooManyChunks>,
        /// Offsets of the one-byte holes that separate the runs, the first one at 0
        holes: Vec<u64>,
        /// End of the data sent
        end: u64,
    }

    /// `runs` runs of contiguous chunks with a one-byte hole before each. A run is a large chunk
    /// and a small one; the first `long` runs have a second large chunk after the small one.
    /// Compaction keeps each large chunk as it is, since it is above a 1,024th of the buffer,
    /// and merges each small one, so it leaves `2 * runs + long` entries, which a join turns into
    /// `runs`. The packet of the very last small chunk has the size that `last_allocation` gives
    /// it; everything else is sent in packets of its own size, so that no compaction is due
    /// before it.
    fn staircase(
        runs: usize,
        long: usize,
        ordered: bool,
        last_allocation: impl Fn(&Assembler) -> usize,
    ) -> Staircase {
        assert!(long < runs, "the last run ends with a small chunk");
        let mut x = Assembler::new();
        if !ordered {
            x.ensure_ordering(false).unwrap();
        }
        let mut holes = vec![0];
        let mut offset = 1;
        let mut result = Ok(());
        for run in 0..runs {
            let lengths: &[usize] = if run < long {
                &[LARGE, SMALL, LARGE]
            } else {
                &[LARGE, SMALL]
            };
            for (i, &len) in lengths.iter().enumerate() {
                let last = run + 1 == runs && i + 1 == lengths.len();
                let allocation = if last {
                    last_allocation(&x)
                } else {
                    len + FRAME_OVERHEAD
                };
                if result.is_ok() {
                    result = x.insert(offset, frame(offset, len), allocation);
                }
                offset += len as u64;
            }
            if run + 1 < runs {
                holes.push(offset);
                offset += 1;
            }
        }
        Staircase {
            x,
            result,
            holes,
            end: offset,
        }
    }

    /// Allocation for the last chunk that makes over-allocation as large as `delta` above what
    /// the compaction threshold is with that chunk in
    fn allocation_at_threshold(x: &Assembler, delta: isize) -> usize {
        let buffered = x.buffered + SMALL;
        let threshold = 32768.max(buffered * 3 / 2);
        // over_allocation = (allocated + allocation) - buffered
        (threshold + buffered - x.allocated)
            .checked_add_signed(delta)
            .unwrap()
    }

    /// Fills every hole with a one-byte frame and reads everything back
    #[track_caller]
    fn repair_and_read(mut s: Staircase, ordered: bool) {
        for &hole in &s.holes {
            s.x.insert(hole, frame(hole, 1), 1 + FRAME_OVERHEAD)
                .expect("a repair is accepted");
        }
        let stream = stream_prefix(s.end as usize);
        let mut delivered = vec![false; s.end as usize];
        drain_varied(&mut s.x, ordered, &stream, &mut delivered);
        assert!(delivered.iter().all(|d| *d), "not every byte was delivered");
    }

    #[test]
    fn join_keeps_runs_that_fit_the_bound() {
        for ordered in [true, false] {
            // 1,025 entries after compaction, which the join turns into 512
            let s = staircase(MAX_CHUNKS / 2, 1, ordered, |_| 1 << 20);
            assert!(s.result.is_ok(), "512 runs fit the bound");
            assert_eq!(s.x.data.len(), MAX_CHUNKS / 2);
            repair_and_read(s, ordered);
        }
    }

    #[test]
    fn join_refuses_one_run_more_than_the_bound() {
        for ordered in [true, false] {
            // 1,026 entries after compaction, then 513 after the join
            let s = staircase(MAX_CHUNKS / 2 + 1, 0, ordered, |_| 1 << 20);
            assert_matches!(s.result, Err(TooManyChunks));
            let s = staircase(MAX_CHUNKS / 2 + 1, 1, ordered, |_| 1 << 20);
            assert_matches!(s.result, Err(TooManyChunks));
        }
    }

    #[test]
    fn real_gaps_beyond_max_chunks_are_still_refused() {
        for ordered in [true, false] {
            let s = staircase(MAX_CHUNKS + 1, 0, ordered, |_| 1 << 20);
            assert_matches!(s.result, Err(TooManyChunks));
        }
    }

    #[test]
    fn no_join_while_compaction_leaves_max_chunks() {
        for ordered in [true, false] {
            // Exactly 1,024 entries after compaction: accepted as they are
            let s = staircase(MAX_CHUNKS / 2, 0, ordered, |_| 1 << 20);
            assert!(s.result.is_ok());
            assert_eq!(s.x.data.len(), MAX_CHUNKS);
            repair_and_read(s, ordered);
        }
    }

    #[test]
    fn join_runs_one_entry_above_max_chunks() {
        for ordered in [true, false] {
            // 1,025 entries after compaction, with fewer runs than the join may leave
            let s = staircase(MAX_CHUNKS / 2 - 1, 3, ordered, |_| 1 << 20);
            assert!(s.result.is_ok(), "contiguous chunks are not gaps");
            assert_eq!(s.x.data.len(), MAX_CHUNKS / 2 - 1);
            repair_and_read(s, ordered);
        }
    }

    #[test]
    fn allocation_trigger_at_its_threshold() {
        for ordered in [true, false] {
            // At the threshold nothing is compacted: all 1,025 entries of the arrangement stay
            let s = staircase(MAX_CHUNKS / 2, 1, ordered, |x| {
                allocation_at_threshold(x, 0)
            });
            assert!(s.result.is_ok());
            assert_eq!(s.x.data.len(), 2 * (MAX_CHUNKS / 2) + 1);
            // One byte more compacts, and the join leaves one entry for each run
            let s = staircase(MAX_CHUNKS / 2, 1, ordered, |x| {
                allocation_at_threshold(x, 1)
            });
            assert!(
                s.result.is_ok(),
                "compaction must not refuse contiguous data"
            );
            assert_eq!(s.x.data.len(), MAX_CHUNKS / 2);
            repair_and_read(s, ordered);
        }
    }

    #[test]
    fn count_trigger_at_its_threshold() {
        let pattern = [424, 104, 104, 104];
        let stream = stream_prefix(pattern_len(&pattern, COMPACT_THRESHOLD + 1));
        let mut delivered = vec![false; stream.len()];
        let mut x = Assembler::new();
        let mut offset = 0;
        // 2,048 chunks do not compact
        insert_pattern(&mut x, &mut offset, &pattern, 0..COMPACT_THRESHOLD);
        assert_eq!(x.data.len(), COMPACT_THRESHOLD);
        // The 2,049th does: 513 large chunks stay and 512 runs of small ones are merged, which
        // is 1,025 entries; the join makes the contiguous stream one chunk
        insert_pattern(
            &mut x,
            &mut offset,
            &pattern,
            COMPACT_THRESHOLD..COMPACT_THRESHOLD + 1,
        );
        assert_eq!(x.data.len(), 1);
        drain_varied(&mut x, true, &stream, &mut delivered);
        assert!(delivered.iter().all(|d| *d), "not every byte was delivered");
    }

    #[test]
    fn allocation_trigger_compacts_one_byte_above_its_threshold() {
        let mut x = Assembler::new();
        let mut offset = 0;
        for _ in 0..8 {
            x.insert(offset, frame(offset, 100), 100).unwrap();
            offset += 100;
        }
        // Over-allocation is now exactly the threshold
        x.insert(offset, frame(offset, 100), 100 + 32768).unwrap();
        offset += 100;
        assert_eq!(x.data.len(), 9);
        x.insert(offset, frame(offset, 1), 2).unwrap();
        assert_eq!(x.data.len(), 1);
    }

    /// The front of the buffer has been partly read when the join happens
    #[test]
    fn join_after_a_partial_ordered_read() {
        let pattern = [424, 104, 104, 104];
        let frames = 2400;
        let stream = stream_prefix(pattern_len(&pattern, frames));
        let mut delivered = vec![false; stream.len()];
        let mut x = Assembler::new();
        let mut offset = 0;
        insert_pattern(&mut x, &mut offset, &pattern, 0..10);
        assert!(read_once(&mut x, 37, true, &stream, &mut delivered));
        insert_pattern(&mut x, &mut offset, &pattern, 10..frames);
        drain_varied(&mut x, true, &stream, &mut delivered);
        assert!(delivered.iter().all(|d| *d), "not every byte was delivered");
    }

    /// The reader moves to unordered reads after the join has run
    #[test]
    fn switch_to_unordered_reads_after_the_join() {
        let pattern = [424, 104, 104, 104];
        let frames = 2400;
        let stream = stream_prefix(pattern_len(&pattern, frames));
        let mut delivered = vec![false; stream.len()];
        let mut x = Assembler::new();
        let mut offset = 0;
        insert_pattern(&mut x, &mut offset, &pattern, 0..1);
        assert!(read_once(&mut x, usize::MAX, true, &stream, &mut delivered));
        insert_pattern(&mut x, &mut offset, &pattern, 1..frames);
        x.ensure_ordering(false).unwrap();
        drain_varied(&mut x, false, &stream, &mut delivered);
        assert!(delivered.iter().all(|d| *d), "not every byte was delivered");
    }

    /// The reader moves to unordered reads first. Its read count is then no stream position, and
    /// the join must not trim chunks by it.
    #[test]
    fn join_after_a_switch_to_unordered_reads() {
        let pattern = [424, 104, 104, 104];
        let frames = 2400;
        let stream = stream_prefix(pattern_len(&pattern, frames));
        let mut delivered = vec![false; stream.len()];
        let mut x = Assembler::new();
        let mut offset = 0;
        insert_pattern(&mut x, &mut offset, &pattern, 0..20);
        assert!(read_once(&mut x, 1000, true, &stream, &mut delivered));
        x.ensure_ordering(false).unwrap();
        insert_pattern(&mut x, &mut offset, &pattern, 20..frames);
        drain_varied(&mut x, false, &stream, &mut delivered);
        assert!(delivered.iter().all(|d| *d), "not every byte was delivered");
    }

    /// Frames of the mixed pattern, every 31st sent twice if `twice`, and after every 31st a
    /// retransmission that starts and ends inside other frames
    #[track_caller]
    fn retransmissions(ordered: bool, twice: bool) {
        let pattern = [604usize, 104, 104];
        let frames = 2400;
        let stream = stream_prefix(pattern_len(&pattern, frames));
        let mut delivered = vec![false; stream.len()];
        let mut x = Assembler::new();
        if !ordered {
            x.ensure_ordering(false).unwrap();
        }
        let mut starts = Vec::new();
        let mut offset = 0u64;
        for i in 0..frames {
            let len = pattern[i % pattern.len()];
            starts.push(offset);
            let copies = if twice && i % 31 == 30 { 2 } else { 1 };
            for _ in 0..copies {
                let result = x.insert(offset, frame(offset, len), len + FRAME_OVERHEAD);
                assert!(result.is_ok(), "frame {i} was refused");
            }
            offset += len as u64;
            if i % 31 == 30 {
                // From inside the frame two back to the end of this one
                let start = starts[i - 2] + 17;
                let len = (offset - start) as usize;
                let result = x.insert(start, frame(start, len), len + FRAME_OVERHEAD);
                assert!(
                    result.is_ok(),
                    "the retransmission after frame {i} was refused"
                );
            }
        }
        assert_sorted(&x);
        drain_varied(&mut x, ordered, &stream, &mut delivered);
        assert!(delivered.iter().all(|d| *d), "not every byte was delivered");
    }

    #[test]
    fn join_with_overlapping_retransmissions() {
        retransmissions(true, false);
    }

    #[test]
    fn join_with_overlapping_retransmissions_unordered() {
        retransmissions(false, false);
    }

    #[test]
    fn join_with_duplicated_frames() {
        retransmissions(true, true);
    }

    #[test]
    fn join_with_duplicated_frames_unordered() {
        retransmissions(false, true);
    }

    /// Frame lengths bimodal, frames delayed and sent twice, retransmissions from other
    /// boundaries, a reader that stalls and reads in bursts of random length, and a switch to
    /// unordered reads. Each read is compared with the stream, and the reads that return
    /// nothing with what a plain array of received bytes says is readable.
    struct Session<'a> {
        stream: &'a [u8],
        x: Assembler,
        ordered: bool,
        received: Vec<bool>,
        delivered: Vec<bool>,
        /// Bytes that have arrived and have not been read
        unread: usize,
        /// Every position below this one has been read
        read_to: usize,
        seed: u64,
        frames_sent: usize,
    }

    impl Session<'_> {
        #[track_caller]
        fn send(&mut self, offset: u64, len: usize, allocation: usize) {
            let range = offset as usize..offset as usize + len;
            let bytes = Bytes::copy_from_slice(&self.stream[range.clone()]);
            let result = self.x.insert(offset, bytes, allocation);
            assert!(
                result.is_ok(),
                "seed {}: frame {} ({len} bytes at offset {offset}) was refused with {} chunks \
                 buffered, although at most 24 holes are open",
                self.seed,
                self.frames_sent,
                self.x.data.len()
            );
            self.frames_sent += 1;
            for received in &mut self.received[range] {
                if !*received {
                    *received = true;
                    self.unread += 1;
                }
            }
            if self.frames_sent & 15 == 0 {
                assert_sorted(&self.x);
            }
        }

        #[track_caller]
        fn read(&mut self, max: usize) -> bool {
            let Some(chunk) = self.x.read(max, self.ordered) else {
                if self.ordered {
                    while self.read_to < self.delivered.len() && self.delivered[self.read_to] {
                        self.read_to += 1;
                    }
                    assert!(
                        self.read_to == self.received.len() || !self.received[self.read_to],
                        "seed {}: an ordered read returned nothing, but byte {} has arrived",
                        self.seed,
                        self.read_to
                    );
                } else {
                    assert_eq!(
                        self.unread, 0,
                        "seed {}: an unordered read returned nothing, with data unread",
                        self.seed
                    );
                }
                return false;
            };
            let start = chunk.offset as usize;
            let end = start + chunk.bytes.len();
            assert!(chunk.bytes.len() <= max);
            assert_eq!(
                &chunk.bytes[..],
                &self.stream[start..end],
                "seed {}",
                self.seed
            );
            for delivered in &mut self.delivered[start..end] {
                assert!(
                    !*delivered,
                    "seed {}: offset {start} delivered twice",
                    self.seed
                );
                *delivered = true;
            }
            self.unread -= end - start;
            assert_sorted(&self.x);
            true
        }
    }

    fn random_allocation(rng: &mut Pcg32, len: usize) -> usize {
        match rng.random_range(0..1500u32) {
            0..=1199 => len + FRAME_OVERHEAD,
            // Frames of several streams share a packet
            1200..=1498 => len + rng.random_range(0..1200),
            _ => len + 1_000_000,
        }
    }

    fn random_session(seed: u64, stream: &[u8]) -> Assembler {
        let mut rng = Pcg32::seed_from_u64(seed);
        // Frame lengths either follow a shape (a large frame, then 2 or 3 small ones) with some
        // jitter, or are drawn independently
        let per_large = rng
            .random_ratio(4, 5)
            .then(|| if rng.random_ratio(7, 10) { 2usize } else { 3 });
        let large_len = rng.random_range(300..=1400usize);
        let small_len = rng.random_range(10..=large_len / 6);
        let large_share = rng.random_range(3..=5u32);
        let hole_every = rng.random_range(60..=300u32);
        let burst_every = rng.random_range(400..=4000u32);
        let switch_at = match rng.random_range(0..4u32) {
            0 => Some(0),
            1 => Some(rng.random_range(100..3000)),
            _ => None,
        };
        let mut s = Session {
            stream,
            x: Assembler::new(),
            ordered: true,
            received: vec![false; stream.len()],
            delivered: vec![false; stream.len()],
            unread: 0,
            read_to: 0,
            seed,
            frames_sent: 0,
        };
        // Held-back frames: (the round in which they arrive, offset, length)
        let mut delayed: Vec<(u32, u64, usize)> = Vec::new();
        let mut frames: Vec<(u64, usize)> = Vec::new();
        let mut next = 0u64;
        let mut round = 0u32;
        while next + 1400 <= stream.len() as u64 {
            round += 1;
            if switch_at == Some(round) && s.ordered {
                s.x.ensure_ordering(false).unwrap();
                s.ordered = false;
            }
            let len = match per_large {
                Some(per_large) => {
                    let phase = round as usize % (1 + per_large);
                    let shape = if phase == 0 { large_len } else { small_len };
                    (shape * rng.random_range(90..=110usize) / 100).max(1)
                }
                None if rng.random_ratio(large_share, 10) => rng.random_range(700..=1400),
                None => rng.random_range(1..=160),
            };
            let offset = next;
            next += len as u64;
            frames.push((offset, len));
            if delayed.len() < 24 && rng.random_ratio(1, hole_every) {
                delayed.push((round + rng.random_range(20..800), offset, len));
            } else {
                let allocation = random_allocation(&mut rng, len);
                s.send(offset, len, allocation);
            }
            let mut i = 0;
            while i < delayed.len() {
                if delayed[i].0 <= round {
                    let (_, offset, len) = delayed.swap_remove(i);
                    s.send(offset, len, len + FRAME_OVERHEAD);
                } else {
                    i += 1;
                }
            }
            if rng.random_ratio(1, 30) {
                let (offset, len) = frames[rng.random_range(0..frames.len())];
                s.send(offset, len, len + FRAME_OVERHEAD);
            }
            if rng.random_ratio(1, 40) {
                // The same bytes again, cut at other boundaries
                let (offset, len) = frames[rng.random_range(0..frames.len())];
                let start = offset + rng.random_range(0..len as u64);
                let end = (start + rng.random_range(1..=2500u64)).min(next);
                let mut at = start;
                while at < end {
                    let piece = rng.random_range(1..=700usize).min((end - at) as usize);
                    s.send(at, piece, piece + FRAME_OVERHEAD);
                    at += piece as u64;
                }
            }
            if rng.random_ratio(1, burst_every) {
                let max = [1, 7, 64, 700, 5000, usize::MAX][rng.random_range(0..6)];
                let mut reads = rng.random_range(1..=2000);
                while reads > 0 && s.read(max) {
                    reads -= 1;
                }
            }
        }
        for (_, offset, len) in mem::take(&mut delayed) {
            s.send(offset, len, len + FRAME_OVERHEAD);
        }
        while s.read(usize::MAX) {}
        assert!(
            s.delivered[..next as usize].iter().all(|d| *d),
            "seed {seed}: not every byte was delivered"
        );
        s.x
    }

    #[test]
    fn random_sessions_match_a_byte_model() {
        const SESSIONS: u64 = 128;
        let stream = stream_prefix(3_000_000);
        let (mut joined_sessions, mut joins, mut joined_bytes, mut compacted_bytes) = (0, 0, 0, 0);
        for seed in 0..SESSIONS {
            let stats = random_session(seed, &stream).stats;
            joined_sessions += (stats.joins > 0) as u64;
            joins += stats.joins;
            joined_bytes += stats.copied_by_join;
            compacted_bytes += stats.copied_by_defragment;
        }
        std::println!(
            "{joined_sessions} of {SESSIONS} sessions entered the join, {joins} joins in all, \
             {joined_bytes} bytes copied by joins and {compacted_bytes} by compaction"
        );
        assert!(
            joined_sessions >= SESSIONS / 4,
            "too few sessions entered the join: {joined_sessions} of {SESSIONS}"
        );
    }

    fn new_rng() -> impl Rng {
        Pcg32::from_seed(0xdeadbeefdeadbeefdeadbeefdeadbeef_u128.to_le_bytes())
    }

    /// Panics unless `data` is in `Buffer::cmp` order.
    #[track_caller]
    fn assert_sorted(x: &Assembler) {
        for i in 1..x.data.len() {
            assert!(
                x.data[i - 1] <= x.data[i],
                "data out of order at {i}: (offset {}, len {}) then (offset {}, len {})",
                x.data[i - 1].offset,
                x.data[i - 1].bytes.len(),
                x.data[i].offset,
                x.data[i].bytes.len(),
            );
        }
    }

    #[test]
    fn assemble_random() {
        random_stream(true);
    }

    #[test]
    fn assemble_random_unordered() {
        random_stream(false);
    }

    /// Fragments arriving retransmitted and shuffled must still read back as the exact stream.
    fn random_stream(ordered: bool) {
        const LEN: usize = 2048;
        let mut rng = new_rng();
        let stream: Vec<u8> = (0..LEN).map(|_| rng.random()).collect();
        for _ in 0..64 {
            let mut frags = Vec::new();
            let mut at = 0;
            while at < LEN {
                let size = rng.random_range(1..=32).min(LEN - at);
                frags.push((at as u64, size));
                at += size;
            }
            // Retransmits are refragmented from scratch, so they overlap the original frames at
            // arbitrary boundaries rather than repeating them
            for _ in 0..frags.len() / 4 {
                let start = rng.random_range(0..LEN);
                let end = (start + rng.random_range(1..=64)).min(LEN);
                let mut at = start;
                while at < end {
                    let size = rng.random_range(1..=32).min(end - at);
                    frags.push((at as u64, size));
                    at += size;
                }
            }
            frags.shuffle(&mut rng);

            let mut x = Assembler::new();
            if !ordered {
                x.ensure_ordering(false).unwrap();
            }
            let mut delivered = vec![false; LEN];
            for (offset, size) in frags {
                let bytes =
                    Bytes::copy_from_slice(&stream[offset as usize..offset as usize + size]);
                x.insert(offset, bytes, size).unwrap();
                assert_sorted(&x);
                if rng.random_ratio(1, 3) {
                    let max = rng.random_range(1..=64);
                    drain(&mut x, max, ordered, &stream, &mut delivered);
                }
            }
            drain(&mut x, usize::MAX, ordered, &stream, &mut delivered);
            assert!(
                delivered.iter().all(|d| *d),
                "stream did not fully assemble"
            );
        }
    }

    /// Read `x` dry, checking chunks against `stream` and that no byte arrives twice.
    #[track_caller]
    fn drain(x: &mut Assembler, max: usize, ordered: bool, stream: &[u8], delivered: &mut [bool]) {
        while let Some(chunk) = x.read(max, ordered) {
            let start = chunk.offset as usize;
            let end = start + chunk.bytes.len();
            assert_eq!(&chunk.bytes[..], &stream[start..end]);
            for d in &mut delivered[start..end] {
                assert!(!*d, "offset {start} delivered twice");
                *d = true;
            }
            assert_sorted(x);
        }
    }

    #[test]
    fn ordered_partial_overlap() {
        let mut x = Assembler::new();
        x.insert(0, Bytes::from_static(b"0123456789"), 10).unwrap();
        x.insert(2, Bytes::from_static(b"23456789abcdef"), 14)
            .unwrap();
        let chunk = x.read(5, true).unwrap();
        assert_eq!(&chunk.bytes[..], b"01234");
        assert_sorted(&x);
        let mut got = chunk.bytes.to_vec();
        while let Some(chunk) = x.read(usize::MAX, true) {
            got.extend_from_slice(&chunk.bytes);
        }
        assert_eq!(&got[..], b"0123456789abcdef");
    }

    #[test]
    fn defrag_mixed_order() {
        let mut x = Assembler::new();
        // Too badly utilized to be marked defragmented, unlike the chunk after it
        x.insert(0, Bytes::from_static(b"a"), 4096).unwrap();
        x.insert(1, Bytes::from_static(b"bcdefghij"), 9).unwrap();
        x.defragment(0);
        assert_sorted(&x);
        let mut got = Vec::new();
        while let Some(chunk) = x.read(usize::MAX, true) {
            got.extend_from_slice(&chunk.bytes);
        }
        assert_eq!(&got[..], b"abcdefghij");
    }

    fn next_unordered(x: &mut Assembler) -> Chunk {
        x.read(usize::MAX, false).unwrap()
    }

    fn next(x: &mut Assembler, size: usize) -> Option<Bytes> {
        x.read(size, true).map(|chunk| chunk.bytes)
    }
}

#[cfg(all(test, not(target_family = "wasm")))]
mod proptests {
    use alloc::{vec, vec::Vec};

    use proptest::prelude::*;
    use rand::RngExt;
    use test_strategy::{Arbitrary, proptest};

    use super::*;

    const MAX_OFFSET: u64 = 512;
    const MAX_LEN: usize = 64;

    #[derive(Debug, Clone, Arbitrary)]
    enum Op {
        #[weight(10)]
        Insert {
            #[strategy(0..MAX_OFFSET)]
            offset: u64,
            #[strategy(1..MAX_LEN)]
            len: usize,
        },
        #[weight(10)]
        Read {
            #[strategy(1..MAX_LEN)]
            max_len: usize,
        },
        #[weight(1)]
        EnsureOrdering { ordered: bool },
        #[weight(1)]
        Defragment,
    }

    /// Tracks the state of the assembler for verification
    struct RefState {
        received: Vec<bool>,
        returned: Vec<bool>,
        ordered: bool,
    }

    fn set_range(bits: &mut [bool], start: u64, len: usize) {
        for i in start..(start + len as u64).min(bits.len() as u64) {
            bits[i as usize] = true;
        }
    }

    impl RefState {
        fn new() -> Self {
            Self {
                received: vec![false; MAX_OFFSET as usize],
                returned: vec![false; MAX_OFFSET as usize],
                ordered: true,
            }
        }

        fn insert(&mut self, offset: u64, len: usize) {
            set_range(&mut self.received, offset, len);
        }

        fn ensure_ordering(&mut self, ordered: bool) -> bool {
            if ordered && !self.ordered {
                return false;
            }
            self.ordered = ordered;
            true
        }

        fn bytes_read(&self) -> u64 {
            self.returned.iter().filter(|&&x| x).count() as u64
        }
    }

    fn make_data() -> Vec<u8> {
        use rand::SeedableRng;
        let mut rng = rand::rngs::StdRng::seed_from_u64(0xDEADBEEF);
        let mut data = vec![0u8; MAX_OFFSET as usize];
        rng.fill(data.as_mut_slice());
        data
    }

    fn get_slice(data: &[u8], offset: u64, len: usize) -> Bytes {
        let start = offset as usize;
        let end = (start + len).min(data.len());
        Bytes::copy_from_slice(&data[start..end])
    }

    fn verify_chunk(data: &[u8], chunk: &Chunk) -> bool {
        let start = chunk.offset as usize;
        chunk.bytes[..] == data[start..start + chunk.bytes.len()]
    }

    #[proptest]
    fn assembler_matches_reference(
        #[strategy(proptest::collection::vec(any::<Op>(), 1..100))] ops: Vec<Op>,
    ) {
        let data = make_data();
        let mut asm = Assembler::new();
        let mut reference = RefState::new();

        for op in ops {
            match op {
                Op::Insert { offset, len } => {
                    let bytes = get_slice(&data, offset, len);
                    asm.insert(offset, bytes, len).unwrap();
                    reference.insert(offset, len);
                }
                Op::Read { max_len } => {
                    let ordered = reference.ordered;
                    let actual = asm.read(max_len, ordered);

                    match actual {
                        None => {
                            // Should only be None if no unreturned received bytes available
                            let has_available = if ordered {
                                // In ordered mode, check if the first unreturned byte is received
                                reference
                                    .returned
                                    .iter()
                                    .position(|&x| !x)
                                    .is_some_and(|pos| reference.received[pos])
                            } else {
                                // In unordered mode, check if any unreturned received byte exists
                                reference
                                    .received
                                    .iter()
                                    .zip(&reference.returned)
                                    .any(|(&r, &ret)| r && !ret)
                            };
                            prop_assert!(
                                !has_available,
                                "read returned None but data was available"
                            );
                        }
                        Some(chunk) => {
                            prop_assert!(chunk.bytes.len() <= max_len, "chunk exceeds max_len");
                            prop_assert!(verify_chunk(&data, &chunk), "data corruption");
                            // Mark as returned, check for duplicates
                            for i in 0..chunk.bytes.len() {
                                let offset = chunk.offset as usize + i;
                                prop_assert!(
                                    reference.received[offset],
                                    "returned unreceived byte at {offset}"
                                );
                                prop_assert!(
                                    !reference.returned[offset],
                                    "duplicate byte at {offset}"
                                );
                                reference.returned[offset] = true;
                            }
                        }
                    }
                }
                Op::EnsureOrdering { ordered } => {
                    let actual = asm.ensure_ordering(ordered).is_ok();
                    let expected = reference.ensure_ordering(ordered);
                    prop_assert_eq!(actual, expected, "ensure_ordering result mismatch");
                }
                Op::Defragment => {
                    if asm.state.is_ordered() {
                        asm.defragment(0);
                    }
                }
            }
        }

        // Invariant: bytes_read matches
        prop_assert_eq!(
            asm.bytes_read(),
            reference.bytes_read(),
            "bytes_read mismatch"
        );
    }
}

/// What a join costs when the peer arranges the data against it, in bytes copied, the most that
/// the insert that joined allocated, and time, against what had been received since the join
/// before. Run with `--nocapture` to print the table, and with `--release` for times worth
/// reading.
#[cfg(all(test, not(target_family = "wasm")))]
mod join_cost {
    use alloc::vec::Vec;
    use core::{
        alloc::{GlobalAlloc, Layout},
        cell::Cell,
    };
    use std::{alloc::System, println, time::Instant};

    use super::test::{FRAME_OVERHEAD, frame};
    use super::*;

    struct CountingAllocator;

    std::thread_local! {
        /// Bytes that this thread has allocated and not freed
        static LIVE: Cell<isize> = const { Cell::new(0) };
        /// The most that `LIVE` has been since it was last set to the live bytes
        static PEAK: Cell<isize> = const { Cell::new(0) };
    }

    fn account(delta: isize) {
        LIVE.with(|live| {
            let now = live.get() + delta;
            live.set(now);
            PEAK.with(|peak| peak.set(peak.get().max(now)));
        });
    }

    // SAFETY: every call is forwarded to `System`, which keeps the contract; only counters are
    // added.
    unsafe impl GlobalAlloc for CountingAllocator {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            let ptr = unsafe { System.alloc(layout) };
            if !ptr.is_null() {
                account(layout.size() as isize);
            }
            ptr
        }

        unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
            unsafe { System.dealloc(ptr, layout) };
            account(-(layout.size() as isize));
        }

        unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
            let new = unsafe { System.realloc(ptr, layout, new_size) };
            if !new.is_null() {
                account(new_size as isize - layout.size() as isize);
            }
            new
        }
    }

    #[global_allocator]
    static ALLOCATOR: CountingAllocator = CountingAllocator;

    /// One join, with what had been received since the one before it
    struct JoinRow {
        frames: u64,
        stream_bytes: u64,
        packet_bytes: u64,
        copied: u64,
        copied_by_compaction: u64,
        buffered: usize,
        longest_run: usize,
        peak_allocation: isize,
        micros: u128,
        entries_after: usize,
    }

    struct Meter {
        name: &'static str,
        bound: usize,
        x: Assembler,
        frames: u64,
        stream_bytes: u64,
        packet_bytes: u64,
        /// `frames`, `stream_bytes` and `packet_bytes` at the last join
        last_join: (u64, u64, u64),
        rows: Vec<JoinRow>,
        refused_at: Option<u64>,
    }

    impl Meter {
        fn new(name: &'static str, bound: usize) -> Self {
            let mut x = Assembler::new();
            x.stats.bound_after_join = Some(bound);
            Self {
                name,
                bound,
                x,
                frames: 0,
                stream_bytes: 0,
                packet_bytes: 0,
                last_join: (0, 0, 0),
                rows: Vec::new(),
                refused_at: None,
            }
        }

        /// Inserts a frame that arrives in a packet of `allocation` bytes. Returns false once
        /// the stream has been refused.
        fn insert(&mut self, offset: u64, len: usize, allocation: usize) -> bool {
            if self.refused_at.is_some() {
                return false;
            }
            let bytes = frame(offset, len);
            let stats = &mut self.x.stats;
            let (joins, copied, by_compaction) = (
                stats.joins,
                stats.copied_by_join,
                stats.copied_by_defragment,
            );
            stats.largest_run = 0;
            let live = LIVE.with(Cell::get);
            PEAK.with(|peak| peak.set(live));
            let start = Instant::now();
            let result = self.x.insert(offset, bytes, allocation);
            let micros = start.elapsed().as_micros();
            let peak_allocation = PEAK.with(Cell::get) - live;
            self.frames += 1;
            self.stream_bytes += len as u64;
            self.packet_bytes += allocation as u64;
            let stats = &self.x.stats;
            if stats.joins > joins {
                self.rows.push(JoinRow {
                    frames: self.frames - self.last_join.0,
                    stream_bytes: self.stream_bytes - self.last_join.1,
                    packet_bytes: self.packet_bytes - self.last_join.2,
                    copied: stats.copied_by_join - copied,
                    copied_by_compaction: stats.copied_by_defragment - by_compaction,
                    buffered: self.x.buffered,
                    longest_run: stats.largest_run,
                    peak_allocation,
                    micros,
                    entries_after: self.x.data.len(),
                });
                self.last_join = (self.frames, self.stream_bytes, self.packet_bytes);
            }
            if result.is_err() {
                self.refused_at = Some(self.frames);
            }
            result.is_ok()
        }

        fn report(&self) {
            for (i, row) in self.rows.iter().enumerate() {
                println!(
                    "{:<30} bound {:>4} join {:>2}: {:>6} frames {:>9} stream B {:>10} packet B | \
                     copied {:>9} B = {:>8.1} per stream B, {:>5.2} per packet B | compaction \
                     {:>9} B | buffered {:>8} | longest run {:>8} | peak alloc {:>9} B | \
                     {:>6} us | entries {:>4}",
                    self.name,
                    self.bound,
                    i + 1,
                    row.frames,
                    row.stream_bytes,
                    row.packet_bytes,
                    row.copied,
                    row.copied as f64 / row.stream_bytes as f64,
                    row.copied as f64 / row.packet_bytes as f64,
                    row.copied_by_compaction,
                    row.buffered,
                    row.longest_run,
                    row.peak_allocation,
                    row.micros,
                    row.entries_after,
                );
            }
            match self.refused_at {
                Some(frame) => println!(
                    "{:<30} bound {:>4}: refused at frame {frame}, after {} joins",
                    self.name,
                    self.bound,
                    self.rows.len()
                ),
                None => println!(
                    "{:<30} bound {:>4}: accepted all {} frames, {} joins",
                    self.name,
                    self.bound,
                    self.frames,
                    self.rows.len()
                ),
            }
        }
    }

    /// A packet of a full-size datagram
    const PACKET: usize = 1200;

    fn mixed(m: &mut Meter) {
        let pattern = [424usize, 104, 104, 104];
        let mut offset = 0;
        for i in 0..2400 {
            let len = pattern[i % pattern.len()];
            if !m.insert(offset, len, len + FRAME_OVERHEAD) {
                return;
            }
            offset += len as u64;
        }
    }

    fn large_and_small_behind_a_hole(m: &mut Meter) {
        let pattern = [5000usize, 400, 400, 400];
        let mut offset = 1;
        for i in 0..2400 {
            let len = pattern[i % pattern.len()];
            if !m.insert(offset, len, len + FRAME_OVERHEAD) {
                return;
            }
            offset += len as u64;
        }
    }

    /// Many small frames that each count a whole packet, between frames that fill theirs
    fn tiny_frames_in_full_packets(m: &mut Meter) {
        let mut offset = 0;
        for _ in 0..1000 {
            if !m.insert(offset, 300, 300 + FRAME_OVERHEAD) {
                return;
            }
            offset += 300;
            for _ in 0..7 {
                if !m.insert(offset, 4, PACKET) {
                    return;
                }
                offset += 4;
            }
        }
    }

    /// `gaps` runs of a large and a small chunk behind one-byte holes, the first `long` of them
    /// with a second large chunk, and then one-byte frames in full packets until a compaction runs
    fn many_gaps(m: &mut Meter, gaps: usize, long: usize) {
        let mut offset = 1;
        for run in 0..gaps {
            let lengths: &[usize] = if run < long {
                &[1000, 4, 1000]
            } else {
                &[1000, 4]
            };
            for &len in lengths {
                if !m.insert(offset, len, len + FRAME_OVERHEAD) {
                    return;
                }
                offset += len as u64;
            }
            if run + 1 < gaps {
                offset += 1;
            }
        }
        let compactions = m.x.stats.compactions;
        for _ in 0..8000 {
            if m.x.stats.compactions > compactions || !m.insert(offset, 1, PACKET) {
                return;
            }
            offset += 1;
        }
    }

    /// A peer that holds `gaps` gaps open with one byte each, with a bulk run of data behind
    /// them, makes the bulk run carry new chunks that compaction keeps apart, and then forces a
    /// compaction with one-byte frames in full packets, again and again until twelve joins have run
    fn hostile_repeat(m: &mut Meter, gaps: usize) {
        let mut offset = 1;
        for _ in 0..gaps {
            if !m.insert(offset, 1, 1 + FRAME_OVERHEAD) {
                return;
            }
            offset += 2;
        }
        for _ in 0..310 {
            if !m.insert(offset, 128, 128 + FRAME_OVERHEAD) {
                return;
            }
            offset += 128;
        }
        for _ in 0..60_000 {
            if m.rows.len() == 12 {
                return;
            }
            let (len, allocation) = if m.x.data.len() <= MAX_CHUNKS {
                (160, 160 + FRAME_OVERHEAD)
            } else {
                (1, PACKET)
            };
            if !m.insert(offset, len, allocation) {
                return;
            }
            offset += len as u64;
        }
    }

    fn run(name: &'static str, bound: usize, scenario: impl Fn(&mut Meter)) -> Meter {
        let mut meter = Meter::new(name, bound);
        scenario(&mut meter);
        meter.report();
        meter
    }

    #[test]
    fn join_cost_with_and_without_the_bound() {
        for bound in [MAX_CHUNKS_AFTER_JOIN, MAX_CHUNKS] {
            let meters = [
                run("mixed 424/104/104/104", bound, mixed),
                run(
                    "5000/400/400/400 behind a hole",
                    bound,
                    large_and_small_behind_a_hole,
                ),
                run(
                    "tiny frames in full packets",
                    bound,
                    tiny_frames_in_full_packets,
                ),
                run("512 gaps, one run longer", bound, |m| many_gaps(m, 512, 1)),
                run("513 gaps", bound, |m| many_gaps(m, 513, 0)),
                run("700 gaps", bound, |m| many_gaps(m, 700, 0)),
                run("1000 gaps", bound, |m| many_gaps(m, 1000, 0)),
                run("hostile repeat, 400 gaps", bound, |m| {
                    hostile_repeat(m, 400)
                }),
                run("hostile repeat, 500 gaps", bound, |m| {
                    hostile_repeat(m, 500)
                }),
                run("hostile repeat, 1000 gaps", bound, |m| {
                    hostile_repeat(m, 1000)
                }),
            ];
            if bound != MAX_CHUNKS_AFTER_JOIN {
                continue;
            }
            for meter in &meters {
                for (i, row) in meter.rows.iter().enumerate() {
                    assert!(
                        row.copied as usize <= row.buffered,
                        "{}: a join copied more than the buffer holds",
                        meter.name
                    );
                    assert!(
                        row.peak_allocation as usize <= 2 * row.buffered + 64 * 1024,
                        "{}: a join allocated {} bytes for {} buffered",
                        meter.name,
                        row.peak_allocation,
                        row.buffered
                    );
                    // Back from at most the bound to above `MAX_CHUNKS` takes one more frame
                    // than the difference, as no frame adds more than one entry
                    if i > 0 {
                        assert!(
                            row.frames > (MAX_CHUNKS - MAX_CHUNKS_AFTER_JOIN) as u64,
                            "{}: joins {} frames apart",
                            meter.name,
                            row.frames
                        );
                    }
                }
            }
            let [_, _, _, _, refused, _, _, _, repeated, thousand] = &meters;
            assert!(refused.refused_at.is_some());
            assert!(
                repeated.rows.len() >= 2,
                "the repeated join was not exercised"
            );
            assert!(thousand.refused_at.is_some());
        }
    }
}
