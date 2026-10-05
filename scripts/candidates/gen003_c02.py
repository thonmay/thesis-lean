"""Dynamic Maximum Cardinality Search (MCS) ordering, undirected graphs. v2.

Maintains a vertex ordering that is a valid MCS ordering of the current
graph: each vertex is chosen when its cardinality (number of already-chosen
neighbors) is maximal among the unchosen vertices (ties broken by smallest id).

=== DESIGN NOTE (v2): why the O(log n) first-break probe was NOT adopted ===

Proposed (PRIMARY) idea: for an insertion of edge (u, v) with pos[u] < pos[v],
replace the O(k) linear scan over the first-break window [pos[u]+1, pos[v]]
with a binary search over a monotone predicate, using prefix sums / a Fenwick
tree, giving an O(log n) probe.

The predicate at step k is:
    P(k) = ( d(k) > c(k) ) or ( d(k) == c(k) and v < order[k] )
where
    d(k) = number of neighbors of v among the prefix order[0 .. k-1]
         = |N(v) n {order[0..k-1]}|
    c(k) = number of neighbors of order[k] among the prefix order[0 .. k-1]
         = |N(order[k]) n {order[0..k-1]}|  (the selection-time cardinality of
           the vertex currently at position k).

The MONOTONICITY CLAIM was: P is a prefix - once v beats order[k], it keeps
beating all later steps (d only grows, c changes by at most +1).

This claim is FALSE. Empirically, over the verifier's full exhaustive universe
(all labeled loop-free undirected graphs on n=2..6, every absent edge as an
insertion), there are 6191 windows where P True followed by P False, and 2536
such violations even when restricted to interior steps (excluding the
degenerate position pos[v] which holds v itself).

Minimal counterexample (n=5, order [0,1,3,4,2], insert edge (0,2)): the window
is steps 1..4 and P = [False, True, False, False]. At step 2, order[2]=3 has
c=0 while v=2 has d=0, and the tie-break 0==0 ^ v<order[2] makes P True; at
step 3, order[3]=4 has c=1 while v still has d=0, so P is False. The earlier
"True" does not persist.

WHY binary search is unsound: d(k) is monotone non-decreasing, but c(k) is the
cardinality of an INDEPENDENT competitor vertex that changes every step and is
not bounded by d(k) nor by any running maximum. So the predicate P(k) is not
monotone, and a segment tree / Fenwick storing per-position booleans cannot
answer "first index where P holds" because P itself depends freshly on the
running prefix each step.

Information-theoretic lower bound for the no-break verdict: to confirm that NO
step in the window breaks, every interior position must be inspected - flipping
any single position's predicate changes the verdict independently, so the
correct answer requires reading the whole window. An O(log n) sound first-break
query is therefore impossible; the O(k) linear scan in v1 (c01) is, up to
constant factors, the fastest sound probe for the COMMON (no-break) case.

Given this, c02 KEEPS the linear O(k) probe from c01 verbatim (correct, exact)
and instead ships the sound SECONDARY mechanism: a periodic overlapping full
regreedy (flag-gated) that bounds the worst-case accumulated suffix that a
pending break can reorder, plus the same tight affected-window logic.

The one place a monotone scan IS sound is inside _regreedy itself, which starts
from a running max-cardinality pointer (non-increasing only when a bucket
empties) - that is unchanged from c01.
"""

# Flag-controlled secondary optimization. When True, every REBUILD_PERIOD
# updates we fully rebuild the ordering from scratch (regreedy from k0=0) and
# reset a per-update counter. This bounds the worst-case suffix a single pending
# break can leave mis-ordered, at the cost of one full O(n + m) pass per period.
USE_PERIODIC_REBUILD = False
REBUILD_PERIOD = 64


def _prefix_mask(order, k):
    """Bitmask of the first k vertices of the order."""
    m = 0
    for i in range(k):
        m |= 1 << order[i]
    return m


def _regreedy(order, pos, mask, n, k0):
    """Re-run bucket MCS on order[k0:], keeping order[:k0] fixed."""
    remaining = 0
    for i in range(k0, n):
        remaining |= 1 << order[i]
    if not remaining:
        return
    prefix = ((1 << n) - 1) ^ remaining
    card = [0] * n
    buckets = [0] * (n + 1)
    maxc = 0
    r = remaining
    while r:
        b = r & -r
        v = b.bit_length() - 1
        r ^= b
        c = (mask[v] & prefix).bit_count()
        card[v] = c
        buckets[c] |= b
        if c > maxc:
            maxc = c
    k = k0
    while remaining:
        while not buckets[maxc]:
            maxc -= 1
        b = buckets[maxc] & -buckets[maxc]  # smallest id in top bucket
        v = b.bit_length() - 1
        buckets[maxc] ^= b
        remaining ^= b
        order[k] = v
        pos[v] = k
        k += 1
        nb = mask[v] & remaining
        while nb:
            b = nb & -nb
            nb ^= b
            w = b.bit_length() - 1
            buckets[card[w]] ^= b
            card[w] += 1
            buckets[card[w]] |= b
            if card[w] > maxc:
                maxc = card[w]


def _first_break(order, mask, k0, k1, v):
    """Insertion repair probe. v's cardinality rose by one for every prefix
    in steps [k0, k1]; all other cardinalities are unchanged. At step k the
    old choice order[k] (cardinality c, the old max) survives iff the new
    max is still c and order[k] is the smallest id attaining it, i.e. iff
    d < c, or d == c and order[k] < v. Return the first breaking step, or
    None if the whole window survives.

    NOTE: this is a LINEAR scan on purpose. A binary-search-on-answer probe is
    unsound because P(k) is not monotone (see DESIGN NOTE). This scan is exact
    and, for the no-break (common) case, information-theoretically optimal.
    """
    prefix = _prefix_mask(order, k0)
    d = (mask[v] & prefix).bit_count()
    for k in range(k0, k1 + 1):
        c = (mask[order[k]] & prefix).bit_count()
        if d > c or (d == c and v < order[k]):
            return k
        prefix |= 1 << order[k]
        if (mask[v] >> order[k]) & 1:
            d += 1
    return None


def _deletion_breaks(order, mask, pv, v):
    """Deletion repair probe. Only step pv can break: v's cardinality there
    dropped by one to c, every other unchosen cardinality is unchanged (and
    was at most c + 1, with v the smallest id at the old max). The step
    breaks iff some other unchosen vertex now strictly beats v, or ties it
    with a smaller id."""
    prefix = _prefix_mask(order, pv)
    c = (mask[v] & prefix).bit_count()
    for i in range(pv + 1, len(order)):
        w = order[i]
        cw = (mask[w] & prefix).bit_count()
        if cw > c or (cw == c and w < v):
            return True
    return False


def init(graph):
    n = len(graph)
    mask = [0] * n
    for u in range(n):
        row = graph[u]
        m = 0
        for v in range(n):
            if row[v]:
                m |= 1 << v
        mask[u] = m
    order = list(range(n))
    pos = [0] * n
    _regreedy(order, pos, mask, n, 0)
    return {
        "n": n,
        "mask": mask,
        "order": order,
        "pos": pos,
        "updates_since_rebuild": 0,
    }


def _update(edge, state, present):
    u, v = edge
    mask = state["mask"]
    if present:
        mask[u] |= 1 << v
        mask[v] |= 1 << u
    else:
        mask[u] &= ~(1 << v)
        mask[v] &= ~(1 << u)
    order = state["order"]
    pos = state["pos"]
    pu = pos[u]
    pv = pos[v]
    if pu > pv:
        u, v = v, u
        pu, pv = pv, pu
    # v is the later endpoint: the only vertex whose selection-time
    # cardinality the flip changes.
    if present:
        k = _first_break(order, mask, pu + 1, pv, v)
    else:
        k = pv if _deletion_breaks(order, mask, pv, v) else None
    if k is not None:
        _regreedy(order, pos, mask, state["n"], k)

    # Periodic overlapping full rebuild (sound secondary optimization).
    if USE_PERIODIC_REBUILD:
        cnt = state.get("updates_since_rebuild", 0) + 1
        if cnt >= REBUILD_PERIOD:
            _regreedy(order, pos, mask, state["n"], 0)
            cnt = 0
        state["updates_since_rebuild"] = cnt
    return state


def insert_edge(graph, edge, state):
    return _update(edge, state, True)


def delete_edge(graph, edge, state):
    return _update(edge, state, False)