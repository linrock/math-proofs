# Erdős Problem 962: prime runs and the square-root bound

Proves `Erdos962.erdos_962_variants_tao_upper_bound`, the pointwise bound $k(n) \le \sqrt{n}$,
where $k(n)$ is the largest $k$ such that for some $m \le n$ each of $m+1, \dots, m+k$ has a
prime divisor strictly greater than $k$. It also records the exact plateau values
$k(n) = 1, 2, 3, 4, 5$ on $[1,3]$, $[4,11]$, $[12,17]$, $[18,53]$, and $[54,63]$.

The main sub-exponential conjecture on k(n) remains open. Tang's lower bound is known in the
literature but is not formalized in this package. None of the plateau results bears on either.

The pointwise bound proved here is not the strongest known. Laishram and Murty (*Grimm's conjecture and smooth numbers*, Michigan Math. J. 61 (2012), 151-160, Theorem 1(i)) prove $g(n) < n^{\alpha}$ for large $n$ with some $\alpha < 1/2$, where $g$ requires the divisors to be *distinct* primes. Two primes exceeding $k$ cannot both divide $m+i$ and $m+j$ for distinct offsets in $[1,k]$, since their difference is less than $k$, so the primes in the definition of $k(n)$ are automatically distinct and $k(n) \le \max_{m \le n} g(m)$. The published bound therefore dominates $k(n) \le \sqrt{n}$ asymptotically. This package supplies a self-contained proof of the upstream Formal Conjectures statement; it claims no improvement over the literature.

## Verification

Run `./verify.sh`.
