module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerBase
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerActionNaturality

/-!
概要：底へ降ろした Postnikov 層の左右作用の、元の代数射に対する自然性。
方針：元の商射の tensor 全射性で消去し、上の層作用の自然性へ戻す。
規約：底の代数射は元の postnikovMap。使われ方：pro 系上の係数と derivation。
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
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (f : B ⟶ C) (n : ℤ) (hn : 0 ≤ n)

lemma postnikovLayerBase_left_naturality :
    (postnikovLayerBaseBimodule R B n hn).actLeft ≫ postnikovLayerMap R f n =
      ((postnikovMap R f n).hom ⊗ₘ postnikovLayerMap R f n) ≫
        (postnikovLayerBaseBimodule R C n hn).actLeft := by
  have : Epi ((postnikovQuotient R B n).hom ▷ postnikovLayer R B n) := by
    rw [← tensorHom_id]
    exact TruncationDesc.tensor_epi _ _
  apply (cancel_epi ((postnikovQuotient R B n).hom ▷ postnikovLayer R B n)).1
  rw [← Category.assoc, postnikovLayerBase_left_projection, Category.assoc,
    postnikovLayerActLeft_naturality]
  simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.id_comp]
  have hp (m : ℤ) : (postnikovQuotient R B m).hom ≫ (postnikovMap R f m).hom =
      f.hom ≫ (postnikovQuotient R C m).hom :=
    congrArg Mon.Hom.hom (postnikovQuotient_naturality R f m)
  rw [hp, hp]
  simp only [tensorHom_def', comp_whiskerRight_assoc, Category.assoc,
    postnikovLayerBase_left_projection]

lemma postnikovLayerBase_right_naturality :
    (postnikovLayerBaseBimodule R B n hn).actRight ≫ postnikovLayerMap R f n =
      (postnikovLayerMap R f n ⊗ₘ (postnikovMap R f n).hom) ≫
        (postnikovLayerBaseBimodule R C n hn).actRight := by
  have : Epi (postnikovLayer R B n ◁ (postnikovQuotient R B n).hom) := by
    rw [← id_tensorHom]
    exact TruncationDesc.tensor_epi _ _
  apply (cancel_epi (postnikovLayer R B n ◁ (postnikovQuotient R B n).hom)).1
  rw [← Category.assoc, postnikovLayerBase_right_projection, Category.assoc,
    postnikovLayerActRight_naturality]
  simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp]
  have hp (m : ℤ) : (postnikovQuotient R B m).hom ≫ (postnikovMap R f m).hom =
      f.hom ≫ (postnikovQuotient R C m).hom :=
    congrArg Mon.Hom.hom (postnikovQuotient_naturality R f m)
  rw [hp, hp]
  simp only [tensorHom_def, whiskerLeft_comp_assoc, Category.assoc,
    postnikovLayerBase_right_projection]

def postnikovLayerBaseMap : postnikovLayerBaseBimodule R B n hn ⟶
    bimoduleRestrict (postnikovMap R f n) (postnikovLayerBaseBimodule R C n hn) where
  hom := postnikovLayerMap R f n
  left_act_hom := by
    change (postnikovLayerBaseBimodule R B n hn).actLeft ≫ postnikovLayerMap R f n =
      ((postnikov R B n).X ◁ postnikovLayerMap R f n) ≫
        ((postnikovMap R f n).hom ▷ postnikovLayer R C n) ≫
          (postnikovLayerBaseBimodule R C n hn).actLeft
    rw [← tensorHom_def'_assoc]
    exact postnikovLayerBase_left_naturality R f n hn
  right_act_hom := by
    change (postnikovLayerBaseBimodule R B n hn).actRight ≫ postnikovLayerMap R f n =
      (postnikovLayerMap R f n ▷ (postnikov R B n).X) ≫
        (postnikovLayer R C n ◁ (postnikovMap R f n).hom) ≫
          (postnikovLayerBaseBimodule R C n hn).actRight
    rw [← tensorHom_def_assoc]
    exact postnikovLayerBase_right_naturality R f n hn

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
