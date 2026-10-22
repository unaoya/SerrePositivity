module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerActionNaturality
public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestriction

/-!
概要：元の代数射による Postnikov 層射を、上段の切断代数上の実双加群射にする。
方針：構成済みの左右作用の自然性を、そのまま実射の二つの保存則へ渡す。
規約：源の上段へ制限した標的層を使う。使われ方：微分変更代数の実自然性。
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

def postnikovLayerBimoduleMap : postnikovLayerBimodule R B n ⟶
    bimoduleRestrict (postnikovMap R f (n + 1)) (postnikovLayerBimodule R C n) where
  hom := postnikovLayerMap R f n
  left_act_hom := by
    change postnikovLayerActLeft R B n ≫ postnikovLayerMap R f n =
      ((postnikov R B (n + 1)).X ◁ postnikovLayerMap R f n) ≫
        ((postnikovMap R f (n + 1)).hom ▷ postnikovLayer R C n) ≫
          postnikovLayerActLeft R C n
    rw [← tensorHom_def'_assoc]
    exact postnikovLayerActLeft_naturality R f n
  right_act_hom := by
    change postnikovLayerActRight R B n ≫ postnikovLayerMap R f n =
      (postnikovLayerMap R f n ▷ (postnikov R B (n + 1)).X) ≫
        (postnikovLayer R C n ◁ (postnikovMap R f (n + 1)).hom) ≫
          postnikovLayerActRight R C n
    rw [← tensorHom_def_assoc]
    exact postnikovLayerActRight_naturality R f n

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
