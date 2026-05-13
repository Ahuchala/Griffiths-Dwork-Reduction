"""
Sharpness tracking for the six conjectured strengthenings of Snow's bounds.

For each conjecture, slack = RHS - LHS in the cleared-integer form.
  slack < 0  ->  conjecture fails on that instance
  slack = 0  ->  conjecture is tight (equality holds)
  slack > 0  ->  conjecture holds strictly

A "tight" instance gives strong evidence that the conjecture cannot be
strengthened further (at least for that family of parameters).
"""

from sage.all import Cores, Partition, flatten, isqrt
from math import inf


def is_kn_bounded(p, k, n):
    return len(p) <= k and (len(p) == 0 or p[0] <= n - k)


def snow_partitions(t, j):
    if t < 2:
        if j == 0:
            yield Partition([]), 0
        return
    for c in Cores(t, size=j):
        p = c.to_partition()
        hl = flatten(p.hook_lengths())
        i = sum(1 for h in hl if h > t)
        yield p, i


def slacks(k, n, j, t, i):
    """Return dict: conjecture index -> slack (RHS - LHS, integer form).

    For C1-C3 the slack equals the ordinary slack (no rational clearing).
    For C4-C6 the slack is in cleared-integer form: slack = 0 iff equality
    holds in the original rational inequality.
    """
    return {
        1: (t + (n - 4) ** 2 // 4) - (j - i),
        2: ((j - i) ** 2) - ((t - 1) * (j + i) - (t - 1) ** 2 // 4),
        3: (n - 1 - isqrt(4 * i - 3)) - t,
        4: k * (n - k) * (n - t) - 2 * n * i,
        5: k * (n - k) * (n + t) - 2 * n * j,
        6: k * (k + 1) ** 2 * (t - 1) - 2 * (k + 1) * i - 4 * j,
    }


def verify_with_sharpness(j_max=20, t_max=20, n_max=15, max_examples=5):
    """Exhaustive verification + per-conjecture tightness tracking."""
    summary = {
        c: {'min_slack': inf, 'tight_count': 0, 'failures': 0, 'examples': []}
        for c in range(1, 7)
    }
    total = 0

    for j in range(1, j_max + 1):
        for t in range(2, t_max + 1):
            for p, i in snow_partitions(t, j):
                if i == 0:
                    continue
                for n in range(4, n_max + 1):
                    for k in range(2, n - 1):  # 2 <= k <= n-2
                        if not is_kn_bounded(p, k, n):
                            continue
                        total += 1
                        sl = slacks(k, n, j, t, i)
                        for c, s in sl.items():
                            entry = summary[c]
                            if s < 0:
                                entry['failures'] += 1
                            if s < entry['min_slack']:
                                entry['min_slack'] = s
                                entry['tight_count'] = 1
                                entry['examples'] = [(k, n, j, t, i, tuple(p))]
                            elif s == entry['min_slack']:
                                entry['tight_count'] += 1
                                if len(entry['examples']) < max_examples:
                                    entry['examples'].append((k, n, j, t, i, tuple(p)))
        print(f"j={j} done")

    return summary, total


if __name__ == "__main__":
    summary, total = verify_with_sharpness(j_max=20, t_max=20, n_max=20)
    print(f"\nTested {total} Snow partition instances.\n")
    for c in range(1, 7):
        entry = summary[c]
        status = "OK" if entry['failures'] == 0 else f"FAIL ({entry['failures']} counterexamples)"
        if entry['min_slack'] == 0:
            sharp = "TIGHT (equality achieved)"
        elif entry['min_slack'] < 0:
            sharp = f"VIOLATED (min slack = {entry['min_slack']})"
        else:
            sharp = f"strict (min slack = {entry['min_slack']})"
        print(f"Conjecture {c}: {status}, {sharp}, {entry['tight_count']} witnesses at min slack")
        for ex in entry['examples'][:3]:
            k, n, j, t, i, lam = ex
            print(f"    k={k} n={n} j={j} t={t} i={i}  lambda={lam}")
        print()