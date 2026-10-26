"""Tape-faithful routing of the 2D FastDFT: MS Lemma 2.4 ``lem:routing`` executed literally, pass by
pass, on record lists (MS §2.2 "Sequential Matrix Transposition and Odd-Stride Routing on a Turing
Machine", [MS] source lines 207-226).

Tape model.  A *tape* is a Python list of opaque records read by a head that only moves forward;
writing appends at the end; "rewind" resets a head to cell 0.  Every pass below reads its input tape
once from left to right, writes the auxiliary tapes T1 and T2 by appending, rewinds them and reads them
once from left to right (asserted: each auxiliary tape is consumed exactly).  Blocks of consecutive
cells may be copied as one slice -- a sequential read of consecutive cells.  Records are never decoded:
the only values inspected are the k1-bit destination tags and the record / block counters, which are
word-size ints.  The list itself is the RAM backend of a tape (DEVIATIONS D2): no head-step counts are
simulated, but the sequence of passes, scans and record moves is the proof's.

Matrices.  A t1 x r matrix (t1 = 2^k1 rows, r = 2^k2 columns, t1 | r) is stored either row-major,
cell j1 r + j2 holding entry (j1, j2), or column-major, cell j2 t1 + j1 holding entry (j1, j2).

Instrument counters: "routing.transpose_pass" (one per pass of (i); k1 per transpose),
"routing.tag_scan" (the tagging scan of (ii)) and "routing.merge_pass" (k1 per odd-stride route).
"""

from __future__ import annotations

from .checks import require

__all__ = ["transpose_rows_to_columns", "transpose_columns_to_rows", "odd_stride_route_tape",
           "bit_reverse_tape", "index_rows_to_columns", "index_columns_to_rows", "index_odd_stride_route"]


def _dims(t1: int, r: int, n: int) -> tuple[int, int]:
    """(k1, k2) for Lemma 2.4's hypotheses: t1 = 2^k1 and r = 2^k2 powers of two with t1 | r, and a
    t1 x r matrix of n = t1 r records."""
    if t1 < 1 or t1 & (t1 - 1) or r < 1 or r & (r - 1):
        raise ValueError(f"Lemma 2.4 needs powers of two t1 = {t1}, r = {r}")
    if r % t1:
        raise ValueError(f"Lemma 2.4 needs t1 | r (t1 = {t1}, r = {r})")
    if n != t1 * r:
        raise ValueError(f"expected t1 r = {t1 * r} records, got {n}")
    return t1.bit_length() - 1, r.bit_length() - 1


def _hit(inst, name: str, n: int = 1) -> None:
    if inst is not None:
        inst.hit(name, n)


# -- Lemma 2.4 (i): transposition by k1 split/interleave passes ----------------------------------------


def _rows_to_columns_pass(tape: list, s: int, r: int) -> list:
    """Pass s (1 <= s <= k1) of Lemma 2.4(i), row-major -> column-major (MS L223).

    On entry the tape holds t1 / 2^(s-1) blocks, each of r contiguous sub-columns of 2^(s-1) records.
    Scan 1 copies the even-indexed blocks to T1 and the odd-indexed blocks to T2 (block parity from the
    (k2 + s - 1)-bit record counter, i.e. one flip per r 2^(s-1) records).  After rewinding, scan 2 reads
    T1 and T2 in lockstep and interleaves each pair of 2^(s-1)-record sub-columns (T1's, then T2's) into
    one 2^s-record sub-column: t1 / 2^s blocks of r sub-columns of length 2^s."""
    sub = 1 << (s - 1)
    blk = r * sub                                  # records per block = 2^(k2 + s - 1)
    T1: list = []
    T2: list = []
    head, parity = 0, 0
    while head < len(tape):                        # scan 1: distribute whole blocks
        (T2 if parity else T1).extend(tape[head:head + blk])
        head += blk
        parity ^= 1
    out: list = []
    h1 = h2 = 0                                    # T1, T2 rewound
    while h1 < len(T1):                            # scan 2: lockstep interleave
        for _ in range(r):
            out += T1[h1:h1 + sub]
            out += T2[h2:h2 + sub]
            h1 += sub
            h2 += sub
    require(h1 == len(T1) and h2 == len(T2), "auxiliary tapes not consumed exactly (MS Lemma 2.4)")
    return out


def _columns_to_rows_pass(tape: list, s: int, r: int) -> list:
    """The reverse of pass s (MS L223, "Reversing the k1 passes"): on entry t1 / 2^s blocks of r
    sub-columns of 2^s records.  Scan 1 splits every sub-column into its first half (to T1) and its
    second half (to T2), 2^(s-1) records each.  After rewinding, scan 2 concatenates block-wise: for each
    block, its r first halves read from T1, then its r second halves read from T2, giving t1 / 2^(s-1)
    blocks of r sub-columns of 2^(s-1) records."""
    half = 1 << (s - 1)
    T1: list = []
    T2: list = []
    head = 0
    while head < len(tape):                        # scan 1: split sub-columns
        T1 += tape[head:head + half]
        T2 += tape[head + half:head + 2 * half]
        head += 2 * half
    blk = r * half
    out: list = []
    h1 = h2 = 0                                    # T1, T2 rewound
    while h1 < len(T1):                            # scan 2: concatenate block-wise
        out += T1[h1:h1 + blk]
        out += T2[h2:h2 + blk]
        h1 += blk
        h2 += blk
    require(h1 == len(T1) and h2 == len(T2), "auxiliary tapes not consumed exactly (MS Lemma 2.4)")
    return out


def transpose_rows_to_columns(records: list, t1: int, r: int, inst=None) -> list:
    """MS Lemma 2.4(i), row-major (j1, j2) -> column-major (j2, j1) of a t1 x r matrix of opaque
    records by k1 = lg t1 passes of :func:`_rows_to_columns_pass` (MS L223); one
    "routing.transpose_pass" per pass.  Returns a new list; ``records`` is not modified."""
    k1, _ = _dims(t1, r, len(records))
    tape = list(records)
    for s in range(1, k1 + 1):
        tape = _rows_to_columns_pass(tape, s, r)
        _hit(inst, "routing.transpose_pass")
    return tape


def transpose_columns_to_rows(records: list, t1: int, r: int, inst=None) -> list:
    """MS Lemma 2.4(i) reversed, column-major (j2, j1) -> row-major (j1, j2) by the k1 reverse passes
    s = k1, ..., 1 of :func:`_columns_to_rows_pass` (MS L223).  This is the de-interleave of x indexed by
    j = j1 + t1 j2 into t1 rows of length r (MS L197, L620) and the output transpose from column-major
    (u2, u1) to natural frequency order u = u2 + r u1 (MS L203, L493).  One "routing.transpose_pass"
    per pass."""
    k1, _ = _dims(t1, r, len(records))
    tape = list(records)
    for s in range(k1, 0, -1):
        tape = _columns_to_rows_pass(tape, s, r)
        _hit(inst, "routing.transpose_pass")
    return tape


# -- Lemma 2.4 (ii): odd-stride routing by tagging and k1 bottom-up merge passes -------------------------


def _tag_scan(tape: list, t1: int, r: int) -> list:
    """The tagging scan of Lemma 2.4(ii) (MS L225): over the columns u2 = 0, ..., r-1 keep the stride
    s(u2) = (2 u2 - 1) mod t1 (s(0) = t1 - 1, then +2 per column) and a k1-bit accumulator, reset to 0
    at each column start, that adds s(u2) mod t1 as v1 runs; prepend the tag u1 = (2 u2 - 1) v1 mod t1
    to each record (a tagged record is the pair (tag, record))."""
    mask = t1 - 1
    stride = mask                                  # (2*0 - 1) mod t1
    out: list = []
    head = 0
    for _ in range(r):
        acc = 0
        for _ in range(t1):
            out.append((acc, tape[head]))
            head += 1
            acc = (acc + stride) & mask
        stride = (stride + 2) & mask
    require(head == len(tape), "tagging scan did not consume the tape exactly (MS Lemma 2.4(ii), L225)")
    return out


def _merge_pass(tape: list, s: int, t1: int) -> list:
    """Pass s (0 <= s < k1) of the bottom-up merge sort of Lemma 2.4(ii) inside every column at once
    (MS L225).  Scan 1 distributes the alternating sorted runs of 2^s tagged records to T1 and T2, the
    run parity being bit s of the k1-bit record counter (the position inside the column).  After
    rewinding, scan 2 merges each pair of runs, one from T1 and one from T2, into a sorted run of
    2^(s+1) records by comparing the k1-bit tags (ties, which cannot occur inside a column, go to T1)."""
    run = 1 << s
    mask = t1 - 1
    T1: list = []
    T2: list = []
    head, counter = 0, 0
    while head < len(tape):                        # scan 1: distribute runs (bit s constant on a run)
        (T2 if (counter >> s) & 1 else T1).extend(tape[head:head + run])
        head += run
        counter = (counter + run) & mask
    out: list = []
    h1 = h2 = 0                                    # T1, T2 rewound
    n1 = len(T1)
    while h1 < n1:                                 # scan 2: merge one pair of runs per iteration
        e1, e2 = h1 + run, h2 + run
        while h1 < e1 and h2 < e2:
            a, b = T1[h1], T2[h2]
            if a[0] <= b[0]:
                out.append(a)
                h1 += 1
            else:
                out.append(b)
                h2 += 1
        if h1 < e1:
            out += T1[h1:e1]
            h1 = e1
        if h2 < e2:
            out += T2[h2:e2]
            h2 = e2
    require(h1 == len(T1) and h2 == len(T2), "auxiliary tapes not consumed exactly (MS Lemma 2.4)")
    return out


def odd_stride_route_tape(records: list, t1: int, r: int, inst=None) -> list:
    """MS Lemma 2.4(ii): the child outputs C_{v1}[u2] in natural row order (row-major (v1, u2), cell
    v1 r + u2) routed by (v1, u2) -> (u1, u2), u1 = (2 u2 - 1) v1 mod t1 (MS eq. (odd-perm)), into
    column-major order (u2, u1) (cell u2 t1 + u1).  The proof's procedure (MS L225): transpose by (i);
    one tagging scan (:func:`_tag_scan`); k1 bottom-up merge passes within all r columns
    (:func:`_merge_pass`); strip the tags (asserting that every column now carries the tags
    0, ..., t1 - 1 in order).  Counters: k1 "routing.transpose_pass", one "routing.tag_scan", k1
    "routing.merge_pass"."""
    k1, _ = _dims(t1, r, len(records))
    tape = transpose_rows_to_columns(records, t1, r, inst)
    tape = _tag_scan(tape, t1, r)
    _hit(inst, "routing.tag_scan")
    for s in range(k1):
        tape = _merge_pass(tape, s, t1)
        _hit(inst, "routing.merge_pass")
    out: list = []
    mask, counter = t1 - 1, 0
    for tag, rec in tape:                          # strip the tags
        if tag != counter:
            raise AssertionError("odd-stride merge sort left a column out of tag order")
        out.append(rec)
        counter = (counter + 1) & mask
    return out


# -- bit reversal by k split-and-concatenate passes (synthetic FFT, leaf FFT) ---------------------------


def bit_reverse_tape(records: list, k: int, unit: int = 1, inst=None, counter: str | None = None) -> list:
    """Bit-reversal permutation of 2^k units of ``unit`` consecutive records each, by k sequential
    split-and-concatenate passes (MS Lemma 2.5 ``lem:syn-fft`` proof, L282, with units = the t1 input
    polynomials of r records; MS L199 and L693 for BaseRadix2FFT's "K_L sequential even/odd split
    passes", units = single records).  In pass s = 1, ..., k, within each of the 2^(s-1) segments of
    2^(k-s+1) units, the even-indexed units are copied to T1 and the odd-indexed units to T2 (a 1-bit
    unit counter), and T1, T2 are concatenated.  The last pass (segments of two units) moves nothing
    but is executed, as written.  Output: unit i of the result is input unit rev_k(i) (equivalently
    out[rev(j)] = in[j], as ``basefft.bit_reverse_perm``).  One ``counter`` hit per pass."""
    if k < 0 or unit < 1 or len(records) != unit << k:
        raise ValueError(f"expected 2^{k} units of {unit} records, got {len(records)} records")
    tape = list(records)
    for s in range(1, k + 1):
        seg_units = 1 << (k - s + 1)
        out: list = []
        head = 0
        while head < len(tape):                    # one segment: split, then concatenate
            T1: list = []
            T2: list = []
            for i in range(seg_units):
                (T2 if i & 1 else T1).extend(tape[head:head + unit])
                head += unit
            out += T1
            out += T2
        tape = out
        if counter:
            _hit(inst, counter)
    return tape


# -- index-map oracles (routing="index"; DEVIATIONS D2) --------------------------------------------------


def index_rows_to_columns(records: list, t1: int, r: int) -> list:
    """Oracle for Lemma 2.4(i): out[j2 t1 + j1] = records[j1 r + j2] (one RAM index map)."""
    _dims(t1, r, len(records))
    return [records[j1 * r + j2] for j2 in range(r) for j1 in range(t1)]


def index_columns_to_rows(records: list, t1: int, r: int) -> list:
    """Oracle for Lemma 2.4(i) reversed: out[j1 r + j2] = records[j2 t1 + j1]."""
    _dims(t1, r, len(records))
    return [records[j2 * t1 + j1] for j1 in range(t1) for j2 in range(r)]


def index_odd_stride_route(records: list, t1: int, r: int) -> list:
    """Oracle for Lemma 2.4(ii): out[u2 t1 + u1] = records[v1 r + u2], u1 = (2 u2 - 1) v1 mod t1
    (the flat-list form of :func:`subnlogn.synthetic.odd_stride_route`)."""
    _dims(t1, r, len(records))
    out = [None] * (t1 * r)
    for v1 in range(t1):
        for u2 in range(r):
            out[u2 * t1 + ((2 * u2 - 1) * v1) % t1] = records[v1 * r + u2]
    return out
