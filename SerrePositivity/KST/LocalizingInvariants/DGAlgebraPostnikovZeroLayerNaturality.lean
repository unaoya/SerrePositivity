module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroLayerBimodule

/-!
概要：元の代数射による層射は、零切断上でも元の左右作用を保つ。
方針：零切断への全射で前合成し、元の代数上の層作用の自然性へ戻す。
規約：層と元の射を保持。使われ方：零底と高次層の平方零代数の厳密な関手化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (f : B ⟶ C) (n : ℤ)

lemma postnikovLayerZero_left_naturality :
    (postnikovLayerZeroBimodule R B n).actLeft ≫ postnikovLayerMap R f n =
      ((postnikovMap R f 0).hom ⊗ₘ postnikovLayerMap R f n) ≫
        (postnikovLayerZeroBimodule R C n).actLeft := by
  have : Epi ((postnikovQuotient R B 0).hom ▷ postnikovLayer R B n) := by
    rw [← tensorHom_id]
    exact TruncationDesc.tensor_epi _ _
  apply (cancel_epi ((postnikovQuotient R B 0).hom ▷ postnikovLayer R B n)).1
  rw [← Category.assoc, postnikovLayerZero_left_projection,
    postnikovLayerOriginal_left_naturality]
  simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.id_comp]
  have hp : (postnikovQuotient R B 0).hom ≫ (postnikovMap R f 0).hom =
      f.hom ≫ (postnikovQuotient R C 0).hom :=
    congrArg Mon.Hom.hom (postnikovQuotient_naturality R f 0)
  rw [hp]
  simp only [tensorHom_def', comp_whiskerRight_assoc, Category.assoc,
    postnikovLayerZero_left_projection]

lemma postnikovLayerZero_right_naturality :
    (postnikovLayerZeroBimodule R B n).actRight ≫ postnikovLayerMap R f n =
      (postnikovLayerMap R f n ⊗ₘ (postnikovMap R f 0).hom) ≫
        (postnikovLayerZeroBimodule R C n).actRight := by
  have : Epi (postnikovLayer R B n ◁ (postnikovQuotient R B 0).hom) := by
    rw [← id_tensorHom]
    exact TruncationDesc.tensor_epi _ _
  apply (cancel_epi (postnikovLayer R B n ◁ (postnikovQuotient R B 0).hom)).1
  rw [← Category.assoc, postnikovLayerZero_right_projection,
    postnikovLayerOriginal_right_naturality]
  simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp]
  have hp : (postnikovQuotient R B 0).hom ≫ (postnikovMap R f 0).hom =
      f.hom ≫ (postnikovQuotient R C 0).hom :=
    congrArg Mon.Hom.hom (postnikovQuotient_naturality R f 0)
  rw [hp]
  simp only [tensorHom_def, whiskerLeft_comp_assoc, Category.assoc,
    postnikovLayerZero_right_projection]

def postnikovLayerZeroMap : postnikovLayerZeroBimodule R B n ⟶
    bimoduleRestrict (postnikovMap R f 0) (postnikovLayerZeroBimodule R C n) where
  hom := postnikovLayerMap R f n
  left_act_hom := by
    change (postnikovLayerZeroBimodule R B n).actLeft ≫ postnikovLayerMap R f n =
      ((postnikov R B 0).X ◁ postnikovLayerMap R f n) ≫
        ((postnikovMap R f 0).hom ▷ postnikovLayer R C n) ≫
          (postnikovLayerZeroBimodule R C n).actLeft
    rw [← tensorHom_def'_assoc]
    exact postnikovLayerZero_left_naturality R f n
  right_act_hom := by
    change (postnikovLayerZeroBimodule R B n).actRight ≫ postnikovLayerMap R f n =
      (postnikovLayerMap R f n ▷ (postnikov R B 0).X) ≫
        (postnikovLayer R C n ◁ (postnikovMap R f 0).hom) ≫
          (postnikovLayerZeroBimodule R C n).actRight
    rw [← tensorHom_def_assoc]
    exact postnikovLayerZero_right_naturality R f n

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
