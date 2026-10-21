module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackLift

/-!
概要：元の厳密な実代数 pullback から、経路を保持する cospan 模型へ比較する。
方針：元の二射影と定数の乗法的経路を、実持ち上げに渡す。
規約：比較射の準同型性はここでは主張しない。使われ方：実拡大の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
variable (R : Type u) [CommRing R] {A B C : Mon (Complex R)} (f : A ⟶ B) (g : C ⟶ B)

def strictWitness : Path.Witness R (MonoidPullback.fst f g ≫ f) (MonoidPullback.snd f g ≫ g) where
  hom := MonoidPullback.fst f g ≫ f ≫ Path.diagonal R B
  source_eq := by
    rw [Category.assoc, Category.assoc, Path.diagonal_source, Category.comp_id]
  target_eq := by
    rw [Category.assoc, Category.assoc, Path.diagonal_target, Category.comp_id]
    exact MonoidPullback.condition f g

def comparison : MonoidPullback.obj f g ⟶ algebra R f g :=
  lift R f g (MonoidPullback.fst f g) (MonoidPullback.snd f g) (strictWitness R f g)

lemma comparison_left : comparison R f g ≫ left R f g = MonoidPullback.fst f g :=
  lift_left R _ _ _ _ _

lemma comparison_right : comparison R f g ≫ right R f g = MonoidPullback.snd f g :=
  lift_right R _ _ _ _ _

lemma comparison_path : comparison R f g ≫ path R f g =
    MonoidPullback.fst f g ≫ f ≫ Path.diagonal R B := lift_path R _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
