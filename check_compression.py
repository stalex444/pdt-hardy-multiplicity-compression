"""Independent replay using orthogonal projections and exact pair arithmetic."""
from fractions import Fraction
from itertools import combinations

import numpy as np


def projection_score(frame, spectrum, p, q):
    target = spectrum[:, None] ** p * frame
    image = spectrum[:, None] ** q * frame
    basis, _ = np.linalg.qr(image, mode="reduced")
    residual = target - basis @ (basis.conj().T @ target)
    return np.linalg.norm(residual) ** 2


def positive_root(values, vectors):
    return (vectors * np.sqrt(np.clip(values, 0, 1))) @ vectors.conj().T


def compress(frame, k):
    top = frame[:k]
    values, vectors = np.linalg.eigh(top @ top.conj().T)
    return np.vstack((positive_root(values, vectors), positive_root(1 - values, vectors)))


def edge(x, y):
    return Fraction(x*y**5-y*x**5, x**5+y**5) ** 2


def rational_examples():
    b, a, c = 1, 2, 3
    assert edge(b, a) + edge(c, a) > edge(b, c)
    assert (edge(b, a) + edge(c, a))/(3*a*a + b*b + c*c) == Fraction(4292, 33275)
    for (b, c), exact in [
        ((2, 3), Fraction(1521, 12100)),
        ((4, 7), Fraction(7452900, 44669897)),
    ]:
        d = [1, 1, 1, b, c]
        total = sum(x*x for x in d)
        edges = {(i, j): edge(d[i], d[j]) for i, j in combinations(range(5), 2)}
        deletion = (max(edges.values()) + min(
            max(e for pair, e in edges.items() if k not in pair) for k in range(5)
        )) / total
        matching = max(v + w for ij, v in edges.items() for kl, w in edges.items()
                       if set(ij).isdisjoint(kl)) / total
        assert matching == max(edge(b, c), edge(1, b) + edge(1, c)) / total == exact
        assert exact < Fraction(174, 1000) < Fraction(175, 1000) < deletion
        print(f"{d}  maximum {exact}  deletion bound {deletion}")


def main():
    rng = np.random.default_rng(20261123)
    max_error, count = 0, 0
    for k, m in [(1, 0), (1, 4), (2, 1), (2, 3), (3, 2), (3, 9), (6, 20)]:
        n = k + m
        for rank in sorted({0, 1, n//2, n}):
            for _ in range(5):
                raw = rng.standard_normal((n, rank)) + 1j*rng.standard_normal((n, rank))
                frame, _ = np.linalg.qr(raw, mode="reduced")
                small = compress(frame, k)
                identity_error = np.linalg.norm(small.conj().T @ small - np.eye(k))
                assert identity_error < 1e-11
                for _ in range(3):
                    d = rng.uniform(0.55, 1.85, size=k)
                    for p, q in [(0, 0), (1, 1), (1, 3), (1, 5), (2, 7), (4, 2)]:
                        before = projection_score(frame, np.r_[d, np.ones(m)], p, q)
                        after = projection_score(small, np.r_[d, np.ones(k)], p, q)
                        error = abs(before - after)
                        max_error = max(max_error, error)
                        assert error < 5e-10, (k, m, rank, p, q, before, after)
                        count += 1
    print(f"{count} projection-score comparisons, largest absolute discrepancy {max_error:.3g}")
    rational_examples()


if __name__ == "__main__":
    main()
