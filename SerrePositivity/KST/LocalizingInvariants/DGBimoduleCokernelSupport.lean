module

public import SerrePositivity.KST.LocalizingInvariants.DGBimoduleCokernel
public import SerrePositivity.KST.LocalizingInvariants.CochainSeparatedBounds

/-!
概要：実係数 cokernel の集中次数は元の標的双加群から継承される。
方針：元の次数全射な商射で、零対象性を各次数へ移す。
規約：商の underlying 複体を変更しない。使われ方：LT の集中した像係数の商。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGBimoduleCokernel
variable {R : Type u} [CommRing R] {A : Mon (Complex R)} {M N : Bimod A A} (f : M ⟶ N)

lemma upperBound (k : ℤ) [N.X.IsStrictlyLE k] : (obj f).X.IsStrictlyLE k := by
  have := projection_epi f
  apply (CochainComplex.isStrictlyLE_iff _ _).2
  intro p hp
  exact IsZero.of_epi ((projection f).hom.f p) (N.X.isZero_of_isStrictlyLE k p hp)

lemma lowerBound (k : ℤ) [N.X.IsStrictlyGE k] : (obj f).X.IsStrictlyGE k := by
  have := projection_epi f
  apply (CochainComplex.isStrictlyGE_iff _ _).2
  intro p hp
  exact IsZero.of_epi ((projection f).hom.f p) (N.X.isZero_of_isStrictlyGE k p hp)

end SerrePositivity.KST.LocalizingInvariants.DGBimoduleCokernel
