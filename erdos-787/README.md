# Erdős Problem 787: the logarithmic restricted sum-avoiding lower bound

For a finite set $A$ of real numbers, this package studies the largest size of a
subset $B \subseteq A$ whose restricted pairwise sums avoid $A$: no sum
$b_1 + b_2$ of two distinct elements of $B$ lies in $A$. Let $g(n)$ be the
largest $m$ such that every $n$-element set $A \subseteq \mathbb{R}$ has such a
$B$ with $|B| \ge m$. This is the function in
[Erdős problem 787](https://www.erdosproblems.com/787).

The package proves **Klarner's logarithmic lower bound** in the exact form used
by Formal Conjectures:

$$\exists c > 0,\quad \forall \text{ sufficiently large } n,\quad c \log n \le g(n).$$

The proof is quantitative. It shows that for every $n$-element $A \subseteq \mathbb{R}$
there is $B \subseteq A$ with $|B| \ge \lfloor \log_2 n \rfloor - 4$ whose
restricted pairwise sums avoid $A$, and therefore that $c = 1/16$ works for
every $n \ge 1024$. The argument separates $A$ into positive and negative parts.
On either part it repeatedly removes the largest element and keeps those
surviving elements whose sum with it avoids $A$. Each removed conflict consumes
a distinct larger element of $A$, so at most one element is lost per halving.
This yields $\lfloor \log_2 |P| \rfloor + 1$ on a same-sign part $P$; the
constant additive losses and the possibility of a zero element give the stated
bound. The treatment of negative reals uses invariance of the maximum under
negation.

**The package does not prove the full Erdős problem.** The estimate of $g(n)$ up
to asymptotic order is open. Choi's upper bound $g(n) \ll n^{2/5+o(1)}$, the
superlogarithmic lower bounds of Sanders and Beker, Ruzsa's upper bound
$\exp(O(\sqrt{\log n}))$, and the equivalence $g(\mathbb{Z}, n) = g(\mathbb{R}, n)$
are not formalized. Only the logarithmic lower bound for sets of reals is proved
here.

## Attribution

Erdős, in *Extremal problems in number theory* (Proc. Sympos. Pure Math. VIII,
1965, pp. 181–189, especially p. 187), states the problem and attributes the
$\Omega(\log n)$ lower bound to Klarner. Choi, in *On a combinatorial problem in
number theory* (Proc. London Math. Soc. (3) 23, 1971, pp. 629–642, especially
p. 630), records the attribution and notes that Klarner's proof appears lost.
Ruzsa, in *Sum-avoiding subsets* (Ramanujan J. 9, 2005, pp. 77–82), gives a
published greedy proof with a better constant. The formal proof here is a new
self-contained conflict-peeling argument for Klarner's lower bound, with an
explicit constant and threshold. The conflict-peeling argument is package-local;
the two interface lemmas `disjoint_restrictedSumset_iff` and `le_g` are adapted
from the Formal Conjectures statement file.

## Files

- `Challenge.lean` states the target and the definitions it uses, with the target
  left as `sorry`.
- `Solution.lean` proves the target from the modules in `Proofs/`.
- `Proofs/Erdos787Base.lean` defines the restricted sumset, sum-avoidance in an
  ambient set, and the maximum size of a sum-avoiding subset.
- `Proofs/Erdos787Proofs.lean` contains the greedy peeling argument, the
  same-sign and sign-splitting estimates, the logarithmic conversion, and the
  final explicit bound.
- `AxiomAudit.lean` prints the transitive axioms of the exported theorem.
- `comparator.json`, `formalization.yaml`, and `verify.sh` configure and run the
  package checks.

## Build and verification

The package uses Lean 4.35.0-rc2 and Mathlib revision
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. From this directory, run

```bash
./verify.sh
```

This checks the module headers and line limits, verifies the pinned toolchain
and Mathlib revision, builds `Solution`, `Challenge`, and `AxiomAudit`, and
confirms that the exported theorem depends only on `propext`,
`Classical.choice`, and `Quot.sound`. `./verify.sh` does not run Comparator.

To run Comparator under its built-in `bwrap` sandbox, which is the trustworthy
mode, use

```bash
lake env lake comparator --config comparator.json
```

The sandbox needs a host that permits unprivileged mount namespaces.
`./verify.sh --no-sandbox` is a local diagnostic only and is not a trustworthy
Comparator verification.

For a direct build, run `lake build`. The source is released under Apache-2.0;
see [LICENSE](LICENSE) and [THIRD_PARTY.md](THIRD_PARTY.md).
