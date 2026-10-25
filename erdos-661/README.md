# Erdős Problem 661: Lenz's construction in R^4

Formalizes Lenz's 1955 construction in `R^4`: for every `n`, two orthogonal circles of radius
`1/sqrt(2)` carry `n` points each whose cross-distances are all `1`
(`Erdos661.erdos_661_variants_lenz`). The construction is Lenz's; this package supplies the
formal proof. An internal supporting lemma reproves the textbook comparison
`erdos_661.variants.le_minimalDistinctDistances`, which already carries a complete inline proof
upstream in Formal Conjectures as of PR #7490; it is not exported as a result. The main planar conjecture and the little-o comparison remain open.

## Verification

Run `./verify.sh`.
