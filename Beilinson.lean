module

public import Beilinson.Foundation
public import Beilinson.Kronecker
public import Beilinson.KroneckerEnd
public import Beilinson.KroneckerYoneda
public import Beilinson.KroneckerEndModules
public import Beilinson.KroneckerModule
public import Beilinson.KroneckerCategory
public import Beilinson.KroneckerResolution
public import Beilinson.KroneckerDimension
public import Beilinson.KroneckerIdeals

/-!
# Beilinson Lean: library entry point

This module is intentionally separate from the Verso book.
The concrete four-dimensional Kronecker algebra and its right actions
in terms of reverse-arrow linear maps are formalized, including the category
equivalence and its restriction to finite-dimensional objects.
Every right module has a short exact projective presentation of length one
and projective dimension at most one. A finite-dimensional simple module
attains projective dimension one. The vertex right ideals are explicitly
identified with the standard projective representations.
A categorical algebra equivalence identifies the endomorphism algebra of a pair
with scalar diagonals, zero reverse Hom and a two-element forward Hom basis
with the Kronecker model. Hom precomposition agrees with the reverse-arrow
right action, and the length-one projective resolution transports to this End
ring. Its geometric hypotheses are not yet instantiated.
The geometric Beilinson equivalence is not yet formalized.

Formal declarations will be imported from `Beilinson/` as they become available.
-/
