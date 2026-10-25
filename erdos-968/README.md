# Erdős 968: total variation and decreasing steps of normalized primes

Let $u_n = p_n / (n + 1)$, where $p_n$ is the $n$-th prime (indexed from $n = 0$ with $p_0 = 2$).
Erdős and Prachar (1961/62) studied the oscillation and step distribution of $u_n$.

This standalone Lean 4 (`leanprover/lean4:v4.35.0-rc2`) package proves two unlinked solved
variants in `FormalConjectures/ErdosProblems/968.lean`:

- `Erdos968.erdos_968.variants.sum_abs_diff_isTheta_log_sq`:
  $$\sum_{p_n < x} |u_{n+1} - u_n| \asymp (\log x)^2.$$
- `Erdos968.erdos_968.variants.decreasing_steps_pos_lower_density`:
  The set $\{n \in \mathbb{N} \mid u_n > u_{n+1}\}$ has strictly positive lower asymptotic density.

## Package Structure

- [Challenge.lean](Challenge.lean): Mathlib-only target declarations in `namespace Erdos968`.
- [Solution.lean](Solution.lean): Proved target theorems matching [Challenge.lean](Challenge.lean).
- [AxiomAudit.lean](AxiomAudit.lean): `#print axioms` verification for all exported theorems.
- [Proofs/Erdos968Proofs.lean](Proofs/Erdos968Proofs.lean): Main Erdős–Prachar step-variation and lower-density proofs.
- [BUILD.md](BUILD.md): Build and verification commands (`./verify.sh`).
- [THIRD_PARTY.md](THIRD_PARTY.md): Attribution and license notices.
