"""
J-TWIST Canon v5.1 -- Gold Master Anchor Test
==============================================

One axiom. One operator. One index. Two piston pairs. Everything
else depends on perspective.

The axiom:  J = 1 + zeta_5^2,  where zeta_5 = e^{2 pi i / 5}.

J is a unit in the ring of integers Z[zeta_5]. Its norm is 1,
its modulus is 1/phi. Multiplication by J contracts in one Galois
embedding (matter) and expands in the other (energy). Physics is
the interplay of these two eigenspaces.

This script implements the Cayley kernel: five generators acting
on Z_5^6, driven by the Thue-Morse sequence. It verifies the
algebraic structure exhaustively (15,625 states) and measures
the emergent attractor.

Zero external dependencies. Zero modulo operator. Zero floating
point in the truth path. The kernel step and all validation checks
use integer arithmetic only. The report section (TPS, duration)
uses standard float arithmetic for human readability.

References: Canon SS66 (generators), SS74 (driver), SS77 (phase
transitions), SS78 (gyron), SS80 (collapse), SS85 (attractor).
"""

import time
import itertools
from collections import Counter, defaultdict

# --- CONFIG (Canon v5.1 - Gold Master) ---
TICKS_RHO = 2_000_000   # Long run for density measurement
BURN_IN = 50_000         # Transient ticks before sampling
WINDOW = 20_000          # Stability window size (x2)

# =====================================================================
# ARITHMETIC Z/5
# =====================================================================
# All arithmetic in the kernel lives in Z/5 = {0,1,2,3,4}.
# No modulo operator (%) is used anywhere. Tables are built once
# at startup by repeated subtraction (Z_LUT) and conditional
# addition/subtraction (ADD5, SUB5). This is the "Zero Modulo"
# policy: the kernel computes by addition and table lookup only.
#
# Why Z/5? The cyclotomic polynomial Phi_5 has degree 4, so the
# ring Z[zeta_5] embeds into Z^4. The Cayley kernel acts on
# Z_5^6: six coordinates for the state (four piston values plus
# a two-component internal phase), and mod 5 because the kernel
# is defined over Z_5 and the axiom is pentagonal (zeta_5).
# =====================================================================

# Trace reduction: sum of six values in {0..4} ranges 0..24.
# Map each possible sum to its Z/5 residue without division.
_Z = []
for _s in range(25):
    _v = _s
    while _v >= 5: _v -= 5
    _Z.append(_v)
Z_LUT = tuple(_Z)

# Negation in Z/5: neg(x) = 5 - x (with neg(0) = 0).
NEG5 = (0, 4, 3, 2, 1)

# Addition in Z/5: ADD5[a][b] = (a + b) mod 5, no % operator.
_A = []
for _a in range(5):
    r = []
    for _b in range(5):
        _s = _a + _b; r.append(_s - 5 if _s >= 5 else _s)
    _A.append(tuple(r))
ADD5 = tuple(_A)

# Subtraction in Z/5: SUB5[a][b] = (a - b) mod 5, no % operator.
_S = []
for _a in range(5):
    r = []
    for _b in range(5):
        r.append((_a - _b + 5) if _a < _b else (_a - _b))
    _S.append(tuple(r))
SUB5 = tuple(_S)

del _Z, _A, _S, _a, _b, _s, _v, r

# =====================================================================
# KERNEL: Five generators of the SS66 action on Z_5^6
# =====================================================================
# State x = (p1, p4, p1', p4', q, ts) in Z_5^6.
#
# The six coordinates encode internal quantum numbers, not spatial
# positions. The first four (p1, p4, p1', p4') are the "pistons",
# the last two (q, ts) are the internal phase.
#
# The five generators {a, b, c, d, e} act as involutions (a,b,d,e
# square to identity) with the relation (b*c)^5 = id. Together
# they generate a finite group action on Z_5^6 determined by
# these relations (see SS66). Their physical roles (after collapse):
#
#   b = Time Inversion (weight 2/3, dominates)
#   d = Mirror          (weight 1/6, Flow phase)
#   e = Mirror          (weight 1/6, Snap phase)
#   a = Swap            (frozen out, weight 0)
#   c = Transport       (frozen out, weight 0)
#
# The 2:1 ratio (b vs d+e) is not a parameter. It falls out of
# the algebra: 2 = -(4-1) mod 5, so the driver shift 2*t exactly
# compensates the z-inversion between Snap and Flow, routing both
# majority populations to generator b.
# =====================================================================

def gen_a(x): return (x[1], x[0], x[3], x[2], x[4], x[5])

def gen_b(x, n=NEG5):
    return (n[x[2]], n[x[3]], n[x[0]], n[x[1]], n[x[4]], n[x[5]])

def gen_c(x, n=NEG5, a=ADD5, s=SUB5):
    p1, p4, p1p, p4p, q, ts = x
    nts = n[ts]
    return (a[n[p1p]][2], a[a[n[p4p]][1]][ts], a[n[p1]][2],
            a[a[n[p4]][1]][nts], s[1][q], nts)

def gen_d(x, s=SUB5):
    return (s[2][x[0]], s[1][x[1]], s[3][x[2]], s[4][x[3]], s[1][x[4]], s[1][x[5]])

def gen_e(x, s=SUB5):
    return (s[2][x[0]], s[1][x[1]], s[3][x[2]], s[4][x[3]], s[2][x[4]], s[1][x[5]])

GENS = (gen_a, gen_b, gen_c, gen_d, gen_e)

# =====================================================================
# DRIVER: i_n = (z_n + 2*t_n) mod 5   [Canon SS74]
# =====================================================================
# At each tick n:
#   z = Tr(x) = sum of coordinates mod 5   (the trace observable)
#   t = TM(n) = popcount(n) mod 2          (the Thue-Morse bit)
#   i = (z + 2*t) mod 5                    (generator index)
#
# IDX_MAP encodes this: IDX_MAP[z] = (i when t=0, i when t=1).
# For z in {0..4}, these are (z, z+2 mod 5).
#
# The Thue-Morse sequence is aperiodic, cube-free, and balanced
# (density 1/2 for both 0 and 1). It is the simplest non-trivial
# deterministic binary sequence. TM(n) = popcount(n) & 1.
# =====================================================================

IDX_MAP = ((0, 2), (1, 3), (2, 4), (3, 0), (4, 1))

# =====================================================================
# TRACE MAP: z_5(x) = Tr(x) = sum(x_i) mod 5   [Canon SS73/SS85.10]
# =====================================================================
# The trace is the unique linear map Z_5^6 -> Z_5 that makes the
# effective phase transitions (SS77) hold pointwise over all 15,625
# states. It is the canonical observable: the one the algebra
# itself selects.
# =====================================================================

def get_z(x):
    return Z_LUT[x[0] + x[1] + x[2] + x[3] + x[4] + x[5]]

# =====================================================================
# PRE-FLIGHT: Exhaustive algebraic verification
# =====================================================================
# Two relations define the algebra:
#   1. Involutions: a^2 = b^2 = d^2 = e^2 = id
#   2. Pentagonal: (b*c)^5 = id
# Checked over all 5^6 = 15,625 states. No sampling, no statistics.
# If any state fails, the witness is printed.
# =====================================================================

def verify_algebra():
    """Exhaustive check of all 15,625 states: involutions + (bc)^5 = id."""
    print("Pre-flight: Exhaustive Check (15,625 states)...")
    ga, gb, gc, gd, ge = GENS
    for s in itertools.product(range(5), repeat=6):
        if ga(ga(s)) != s: print("FAIL a^2 at", s); return False
        if gb(gb(s)) != s: print("FAIL b^2 at", s); return False
        if gd(gd(s)) != s: print("FAIL d^2 at", s); return False
        if ge(ge(s)) != s: print("FAIL e^2 at", s); return False
        c = s
        for _ in range(5): c = gb(gc(c))
        if c != s: print("FAIL (bc)^5 at", s); return False
    return True

# =====================================================================
# WINDOW SAMPLER
# =====================================================================
# After burn-in, the orbit settles onto a 20-state attractor.
# Two consecutive windows of equal length must see the same set
# of states (stability). This is the core of Status (A) Anchor
# certification: deterministic, repeatable, no statistics needed.
# =====================================================================

def sample_window(x, start, count):
    """Run `count` ticks from `start`, return (final_state, visited, z_vals, usage)."""
    zlut, gens, imap = Z_LUT, GENS, IDX_MAP
    visited, z_vals, usage = set(), set(), Counter()
    va, za = visited.add, z_vals.add
    for n in range(start, start + count):
        z = zlut[x[0]+x[1]+x[2]+x[3]+x[4]+x[5]]
        t = n.bit_count() & 1
        idx = imap[z][t]
        va(x); za(z); usage[idx] += 1
        x = gens[idx](x)
    return x, visited, z_vals, usage

# =====================================================================
# TOPOLOGY CHECK: Piston decomposition
# =====================================================================
# The 20-state attractor factors as 4 x 5:
#   4 piston configurations (p1, p4, p1', p4')
#   5 internal phases (q, ts) per piston
# This is an internal quantum number decomposition, not geometry.
# The coincidence with the icosahedron's 20 faces is noted but
# unproved in this context.
# =====================================================================

def check_pistons(dataset):
    """Piston decomposition: 4 base states x 5 fibre states = 20."""
    pistons = defaultdict(set)
    for s in dataset: pistons[s[:4]].add(s[4:])
    return sorted(len(v) for v in pistons.values())

# =====================================================================
# MAIN: Gold Master Anchor Certification
# =====================================================================

def run_gold_anchor():
    algebra_ok = verify_algebra()
    if not algebra_ok:
        print("CRITICAL: Algebra failed."); return

    x = (1, 0, 0, 0, 0, 0)
    zlut, gens, imap = Z_LUT, GENS, IDX_MAP

    # Burn-in: let transients decay (z=0, z=2 states flush out)
    print(f"Burn-in ({BURN_IN} ticks)...")
    for n in range(BURN_IN):
        x = gens[imap[zlut[x[0]+x[1]+x[2]+x[3]+x[4]+x[5]]][n.bit_count() & 1]](x)

    # Two stability windows: S1 must equal S2
    print(f"Window 1 ({WINDOW} ticks)...")
    x, S1, Z1, U1 = sample_window(x, BURN_IN, WINDOW)
    print(f"Window 2 ({WINDOW} ticks)...")
    x, S2, Z2, U2 = sample_window(x, BURN_IN + WINDOW, WINDOW)

    # Rho measurement: count gyron events over long run.
    # Gyron(n) := [z_n = 4] AND [TM(n) = 0]     [Canon SS78.2]
    # Target density: rho = 1/6 asymptotically, i.e. 6*gyrons ≈ N.
    # This is the matter density of the universe, measured as a
    # pure counting ratio. No floats.
    print(f"Rho Measurement ({TICKS_RHO:,} ticks)...")
    gyrons = 0
    rho_start = BURN_IN + 2 * WINDOW
    start_t = time.time()
    for n in range(rho_start, rho_start + TICKS_RHO):
        z = zlut[x[0]+x[1]+x[2]+x[3]+x[4]+x[5]]
        t = n.bit_count() & 1
        if z == 4 and t == 0: gyrons += 1
        x = gens[imap[z][t]](x)
    duration = time.time() - start_t

    # --- VALIDATION (all integer, no floats in the truth path) ---
    p1, p2 = check_pistons(S1), check_pistons(S2)
    z_dist1 = Counter(get_z(s) for s in S1)
    z_dist2 = Counter(get_z(s) for s in S2)

    checks = {
        # Algebraic integrity: involutions + pentagonal relation
        "Algebra (15k states)":    algebra_ok,
        # Attractor stability: same set in both windows
        "Set Stability (S1==S2)":  S1 == S2,
        # Attractor size: 20 = 4 pistons x 5 phases
        "Attractor Size (20)":     len(S2) == 20,
        # Fibre structure: each piston has exactly 5 phases
        "Pistons 4x5 (W1&W2)":    p1 == [5,5,5,5] and p2 == [5,5,5,5],
        # Phase collapse: trace values restricted to {1,4} (SS80)
        "Z-Stream {1,4} (W1&W2)":  Z1 == {1, 4} and Z2 == {1, 4},
        # Frozen alphabet: only b,d,e fire; a,c are dead (SS85.1)
        "Frozen Alpha {1,3,4}":    set(U1) == {1,3,4} and set(U2) == {1,3,4},
        # Z-split: exactly 10 states at z=1, 10 at z=4
        "Z-Split 10/10 (W1&W2)":   z_dist1[1] == 10 and z_dist1[4] == 10 and z_dist2[1] == 10 and z_dist2[4] == 10,
        # Rho = 1/6: asymptotically 6*gyrons -> N, finite run gives 6*gyrons ≈ N.
        # Integer check: |6g - N| < 6N/10000, equivalent to |g/N - 1/6| < 1e-4.
        "Rho = 1/6 (integer)":     abs(6 * gyrons - TICKS_RHO) < 6 * TICKS_RHO // 10000,
    }

    # --- REPORT ---
    print(f"\n--- J-TWIST CANON v5.1 GOLD REPORT ---")
    for name, ok in checks.items():
        print(f"  {name:30s} {'PASS' if ok else 'FAIL'}")
    print(f"  {'Attractor':30s} {len(S1)}/{len(S2)}")
    delta = 6 * gyrons - TICKS_RHO
    print(f"  {'Rho (6g vs N)':30s} 6 x {gyrons} = {6*gyrons}  (N = {TICKS_RHO}, delta = {delta})")
    print(f"  {'Speed':30s} {TICKS_RHO/duration:,.0f} TPS")

    if all(checks.values()):
        print("\n[VERDICT] STATUS (A) ANCHOR SECURED. GOLD MASTER.")
    else:
        print("\n[VERDICT] FAILED. INTEGRITY COMPROMISED.")

if __name__ == "__main__":
    run_gold_anchor()