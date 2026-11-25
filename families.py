"""
Parameter families for conjecture mode. Each family is a generator yielding
(name, lean_statement, description). Add your own: the engine will try to
refute, recognise or prove every instance.
"""

SUB = "₀₁₂₃₄₅₆₇₈₉"


def _vars(n):
    return [f"v{SUB[i]}" for i in range(n)]


def path_gap_one():
    """Open chain with n sites: is the gap above the vacuum at least 1?
    Mean-zero states v, energy Σ (v_{i+1} - v_i)², norm Σ v_i².
    True gaps are 2 - 2cos(π/n): 2, 1, 0.586, ... so the claim should fail from n = 4.
    This is the massless gap closing, found by the engine rather than assumed."""
    for n in range(2, 6):
        v = _vars(n)
        binders = f"({' '.join(v)} : ℝ) (h : {' + '.join(v)} = 0)"
        energy = " + ".join(f"({v[i + 1]} - {v[i]}) ^ 2" for i in range(n - 1))
        norm = " + ".join(f"{x} ^ 2" for x in v)
        yield (f"path_gap_one_{n}", f"theorem path_gap_one_{n} {binders} : {energy} ≥ {norm}",
               f"{n}-site chain has gap ≥ 1")


def complete_graph_gap():
    """Every site coupled to every other: gap n, for every n (a mean-field lattice)."""
    for n in range(2, 6):
        v = _vars(n)
        binders = f"({' '.join(v)} : ℝ) (h : {' + '.join(v)} = 0)"
        energy = " + ".join(f"({v[i]} - {v[j]}) ^ 2" for i in range(n) for j in range(i + 1, n))
        norm = " + ".join(f"{x} ^ 2" for x in v)
        yield (f"complete_gap_{n}", f"theorem complete_gap_{n} {binders} : {energy} ≥ {n} * ({norm})",
               f"complete graph on {n} sites has gap ≥ {n}")


def massive_chain_gap():
    """Massive chain: gap ≥ m² with no mean-zero condition, at every size."""
    for n in range(2, 5):
        v = _vars(n)
        binders = f"({' '.join(v)} m : ℝ)"
        energy = " + ".join(f"({v[i + 1]} - {v[i]}) ^ 2" for i in range(n - 1))
        norm = " + ".join(f"{x} ^ 2" for x in v)
        yield (f"massive_chain_gap_{n}",
               f"theorem massive_chain_gap_{n} {binders} : {energy} + m ^ 2 * ({norm}) ≥ m ^ 2 * ({norm})",
               f"{n}-site massive chain has gap ≥ m²")


FAMILIES = [path_gap_one, complete_graph_gap, massive_chain_gap]
