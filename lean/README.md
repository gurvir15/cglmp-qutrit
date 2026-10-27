# Fixed-state qutrit CGLMP global optimality

The final theorem is `CGLMP3SOS.full_global_optimality` in
`CGLMP3_GlobalOptimality.lean`. It states both:

- Every quadruple of complete qutrit measurement bases gives
  `I3 <= 4/3 + 8/(3*sqrt(3))` on the fixed maximally entangled state.
- An explicit quadruple of such bases attains equality.

Measurements are represented by arbitrary complex 3-by-3 unitary matrices,
whose columns are the orthonormal outcome vectors. The normalized joint
Born probability is explicitly
`normSq (sum_j A[j,a]*B[j,b]) / 3` for
`|Phi3>=(|00>+|11>+|22>)/sqrt(3)`.

## Proof method

The global upper bound uses an exact tracial sum-of-squares certificate,
instead of the manuscript's angular-budget route. The delivered final
theorem takes no analytic certificate, angular-budget, spectral, or other
mathematical hypothesis beyond the four unitary measurement bases.

Writing `tau(X)=Tr(X)/3`, `kappa=1-i*sqrt(3)/3`, and
`gamma=-1-i*sqrt(3)/3`, the trace expression is

```text
Re tau(kappa*(u0*u2^-1 + u2*u1^-1 + u1*u3^-1) + gamma*u3*u0^-1).
```

The word basis is the four `u_i` and the twelve ordered products
`u_i^2*u_j^2` with `i != j`. The checked identity expresses the difference
from `beta=4/3+8*sqrt(3)/9` as
`sum(i,j) Q[i,j]*tau(w_j^-1*w_i)`, with
`Q=V*diag(D)*V^dagger` and every `D[k]>=0`. This is a sum of thirteen
nonnegative trace squares.

Each basis E determines a cubic unitary observable `E*Z*E^-1`. The physical
modular Bell expression is proved equal to a trace expression in four such
observables. A 16-by-16 Hermitian Gram matrix proves that the gap to the
claimed bound is nonnegative. Its coefficients belong to
`Q(sqrt(3), i)` and its positive factorization has 13 nonnegative weights.

The source checks the exact Gram factorization, signs of the weights,
finite word-reduction tables, and coefficient identity. The word checker
is proved sound from the cubic-unitary relations and cyclicity of trace.
All finite arithmetic checks use Lean kernel computation; none uses a
native decision procedure. Numerical optimization was used only to find
the certificate and is not part of its verification or assumptions.

The attaining strategy is checked independently. Its effective bases are
`E0=1`, `E1=Q^2`, `F0=Q`, `F1=Q^3`; Alice's physical bases are the entrywise
complex conjugates of E0 and E1. For `s=sqrt(3)`, Q has first row
`[(3+s+i*(1+s))/6, -i/3, (3-s+i*(1-s))/6]` and cyclic subsequent rows.
Its unitarity, fourth power equal to the lowering shift, and exact Bell
value are all proved.

This certificate establishes the physical global bound by the algebraic
route. It does not claim to formalize Thompson's theorem or the
angular-budget lemma from the manuscript. Those are unnecessary for the
final theorem in this file.

## Audit and reproduction

Pinned versions: Lean 4.24.0 and Mathlib v4.24.0. The exact source hash,
compiler exit status, final theorem type, and axiom audit are recorded in
`verification.log`. The final theorem is required to depend only on
`propext`, `Classical.choice`, and `Quot.sound`.

With the pinned toolchain installed, run from this folder:

```text
lake update
lake exe cache get
lake env lean CGLMP3_GlobalOptimality.lean
```

The first two commands fetch the pinned dependencies if needed. Verification
of the delivered file needs Lean and Mathlib only; no numerical solver or
Python package is needed. Exact arithmetic checks may take several minutes.

The original manuscript and source files have not been modified or uploaded
to an external proof-checking service.
