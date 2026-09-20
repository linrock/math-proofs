# Provenance and licenses for Erdős #973

The statement adapted from google-deepmind/formal-conjectures retains its
Apache-2.0 header in `Challenge.lean`, `Solution.lean`, and
`Proofs/Statement973.lean`. The accompanying license is in
`third_party/FORMAL-CONJECTURES-LICENSE.txt`. Challenge names the exact
upstream revision and statement-file hash. These modules reproduce or adapt
the problem statement. The stronger target and proof adapters are local work.

The mathematical negative answer was presented by Luo, Yang, and Zhu. The
local qualitative formalization follows the residual-polynomial method of
Tan, Wang, Huang, and Chen. Their papers are cited in `README.md`. No theorem
from either paper is imported as an axiom. Mathlib and its dependencies retain
their own upstream licenses and commit pins.

The locally authored material in this repository is released under the MIT
license in the repository-root `LICENSE`, matching `formalization.yaml`. This
grant does not claim authorship of prior mathematics or change the licenses
of third-party sources. `source-manifest.json` binds every included proof
module to its research origin and hash. It is provenance, not a proof
certificate.
