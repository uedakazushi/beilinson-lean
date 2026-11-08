module

public import Beilinson.Foundation
public import Beilinson.DerivedDevissage
public import Beilinson.Kronecker
public import Beilinson.KroneckerEnd
public import Beilinson.EndTransport
public import Beilinson.EndTransportYoneda
public import Beilinson.KroneckerYoneda
public import Beilinson.KroneckerEndModules
public import Beilinson.KroneckerModule
public import Beilinson.KroneckerCategory
public import Beilinson.KroneckerResolution
public import Beilinson.KroneckerFinite
public import Beilinson.KroneckerPerfect
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
ring. The separate pinned Stacks integration instantiates the geometric Hom
hypotheses on the projective line.
A general bounded devissage lemma reconstructs an object inside a strictly full
triangulated subcategory from its cohomology objects in any abelian category.
For Kronecker, bounded finite-dimensional cohomology then suffices for membership
in every such subcategory containing the finite projective modules.
Finite-dimensional right modules also form a Serre subcategory, and their finite
projective covers lift through epimorphisms.
The optional integration checks the actual unbounded dg equivalence, its ordinary
right-module form and the compact-source bounded restriction in every dimension.
In dimension one it composes an equivalence from the actual bounded derived category
of finite-dimensional Kronecker modules to the actual bounded coherent derived category.
The positive-window functor and the general finite-dimensional source remain to be connected.

Formal declarations will be imported from `Beilinson/` as they become available.
-/
