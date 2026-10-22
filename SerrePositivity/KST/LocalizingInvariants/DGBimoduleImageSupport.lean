module

public import SerrePositivity.KST.LocalizingInvariants.DGBimoduleImage
public import SerrePositivity.KST.LocalizingInvariants.CochainSeparatedBounds

/-!
概要：実 dg 双加群の像は標的の集中次数を保ち、cokernel 消滅から鎖写像を制限する。
方針：包含の各次数の単射性と、cokernel の kernel と像の実同型を使う。
規約：元の包含への合成式を保持。使われ方：像の shift 係数への derivation の降下。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGBimoduleImage
variable {R : Type u} [CommRing R] {A : Mon (Complex R)} {M N : Bimod A A} (f : M ⟶ N)

lemma upperBound (k : ℤ) [N.X.IsStrictlyLE k] : (obj f).X.IsStrictlyLE k := by
  have := inclusion_mono f
  apply (CochainComplex.isStrictlyLE_iff _ _).2
  intro p hp
  exact IsZero.of_mono ((inclusion f).hom.f p) (N.X.isZero_of_isStrictlyLE k p hp)

lemma lowerBound (k : ℤ) [N.X.IsStrictlyGE k] : (obj f).X.IsStrictlyGE k := by
  have := inclusion_mono f
  apply (CochainComplex.isStrictlyGE_iff _ _).2
  intro p hp
  exact IsZero.of_mono ((inclusion f).hom.f p) (N.X.isZero_of_isStrictlyGE k p hp)

variable {K : Complex R} (d : K ⟶ N.X) (hd : d ≫ cokernel.π f.hom = 0)

def chainLift : K ⟶ (obj f).X :=
  kernel.lift (cokernel.π f.hom) d hd ≫ (Abelian.imageIsoImage f.hom).hom

lemma chainLift_inclusion : chainLift f d hd ≫ (inclusion f).hom = d := by
  change (kernel.lift (cokernel.π f.hom) d hd ≫ (Abelian.imageIsoImage f.hom).hom) ≫
    image.ι f.hom = d
  rw [Category.assoc, Abelian.imageIsoImage_hom_comp_image_ι, kernel.lift_ι]

end SerrePositivity.KST.LocalizingInvariants.DGBimoduleImage
