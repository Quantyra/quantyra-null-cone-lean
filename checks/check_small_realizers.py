"""Exhaust all labeled five-event permutation orders and all candidate realizers.

Checks the orientation forcing rule independently of the grid construction.
Not a replacement for a formal proof.
"""

from itertools import permutations


def positions(order):
    return {vertex: rank for rank, vertex in enumerate(order)}


def main(n=5):
    orders = list(permutations(range(n)))
    valid = 0
    for latent_second in orders:
        latent = positions(latent_second)
        p = {(i, j) for i in range(n) for j in range(n) if i < j and latent[i] < latent[j]}
        inc = {(i, j) for i in range(n) for j in range(n) if i != j and (i, j) not in p and (j, i) not in p}
        for first in orders:
            pos = positions(first)
            if any(pos[i] >= pos[j] for i, j in p):
                continue
            second_rel = p | {(i, j) for i, j in inc if pos[j] < pos[i]}
            second_ranks = {j: sum((i, j) in second_rel for i in range(n)) for j in range(n)}
            if len(set(second_ranks.values())) != n:
                continue
            if any(second_ranks[i] >= second_ranks[j] for i, j in second_rel):
                continue
            valid += 1
            for x, y in inc:
                for z in range(n):
                    if (z, y) in inc and ((x, z) in p or (z, x) in p):
                        assert (pos[x] < pos[y]) == (pos[z] < pos[y])
    print(f"PASS: {len(orders)} latent permutation orders; {valid} realizers; every forcing triple")


if __name__ == "__main__":
    main()
