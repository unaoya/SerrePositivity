module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovBaseChangedLayer

/-!
概要：底変更した拡大の標準係数層の積は、元の包含を通して厳密に零となる。
方針：底と元の上段への共同単射族で判定し、元の層の平方零性を回収する。
規約：実 kernel 自体の積が零とは主張しない。使われ方：底変更した拡大の係数。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory HomologicalComplex
open scoped MonObj
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0] (n : ℤ)
  {P : Mon (Complex R)} (b : P ⟶ postnikov R B n)

lemma postnikovBaseChangedLayer_mul_zero (hn : 0 ≤ n) :
    (postnikovBaseChangedLayerInclusion R B n b ⊗ₘ postnikovBaseChangedLayerInclusion R B n b) ≫
      μ[(postnikovExtensionBaseChange R B n b).X] = 0 := by
  let k := postnikovBaseChangedLayerInclusion R B n b
  apply pullback.hom_ext
  · change ((k ⊗ₘ k) ≫ μ[(postnikovExtensionBaseChange R B n b).X]) ≫
      (postnikovExtensionBaseChangeBase R B n b).hom =
        (0 : _ ⟶ (postnikovExtensionBaseChange R B n b).X) ≫
          (postnikovExtensionBaseChangeBase R B n b).hom
    rw [zero_comp, Category.assoc, IsMonHom.mul_hom, ← Category.assoc,
      tensorHom_comp_tensorHom, postnikovBaseChangedLayerInclusion_base]
    rw [MonoidalPreadditive.zero_tensor, zero_comp]
  · change ((k ⊗ₘ k) ≫ μ[(postnikovExtensionBaseChange R B n b).X]) ≫
      (postnikovExtensionBaseChangeUpper R B n b).hom =
        (0 : _ ⟶ (postnikovExtensionBaseChange R B n b).X) ≫
          (postnikovExtensionBaseChangeUpper R B n b).hom
    rw [zero_comp, Category.assoc, IsMonHom.mul_hom, ← Category.assoc,
      tensorHom_comp_tensorHom, postnikovBaseChangedLayerInclusion_upper]
    exact postnikovLayer_mul_zero R B n hn

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
