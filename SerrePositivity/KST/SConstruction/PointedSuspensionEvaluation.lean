module
public import SerrePositivity.KST.SConstruction.PointedClosedEvaluation
public import SerrePositivity.KST.Spectra.SuspensionLoop

/-! # suspension の全写像族の元の積上での評価
概要：円との smash に誘導した全族を、元の円と元の対象の直積上で評価する。
方針：点つき評価の包含式と忘却の monoidal 結合式を使う。
規約：全次数・全パラメータを保持する。使われ方：元の suspension 組み立ての自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open Spectra PointedSimplicialSet

/-- 点つき suspension の全 Hom 作用は、元の直積上で円の因子を固定する。 -/
lemma suspensionHom_underlying_evaluation (X Y : PointedSimplicialSet.{u}) :
    (productToSmash circle X ▷ (PointedObject.basedHom X Y).right) ≫
      uncurry ((suspensionHom X Y).right ≫
        PointedObject.basedHomι (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Y)) =
    (α_ circle.right X.right (PointedObject.basedHom X Y).right).hom ≫
      (circle.right ◁ uncurry (PointedObject.basedHomι X Y)) ≫ productToSmash circle Y := by
  have hn := productToSmash_naturality (𝟙 (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X)) (suspensionHom X Y)
  simp only [Under.id_right, id_tensorHom] at hn
  rw [uncurry_natural_left, ← pointedClosedEvaluation]
  erw [reassoc_of% hn]
  have he := congrArg Under.Hom.right (suspensionHom_evaluation X Y)
  change (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X ◁ suspensionHom X Y).right ≫
    ((ihom.ev (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X)).app (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Y)).right =
      (α_ circle X (PointedObject.basedHom X Y)).hom.right ≫
        (circle ◁ ((ihom.ev X).app Y)).right at he
  erw [he]
  erw [reassoc_of% (productToSmash_associator circle X (PointedObject.basedHom X Y))]
  have hev := productToSmash_naturality (𝟙 circle) ((ihom.ev X).app Y)
  simp only [Under.id_right, id_tensorHom] at hev
  erw [← hev, ← whiskerLeft_comp_assoc, pointedClosedEvaluation]
  rfl

/-- 任意の入力族でも、suspension の作用は元の円の因子を厳密に固定する。 -/
lemma suspensionHom_family_app {P : SSet.{u}} (X Y : PointedSimplicialSet.{u})
    (a : P ⟶ (PointedObject.basedHom X Y).right) (n : SimplexCategoryᵒᵖ)
    (c : circle.right.obj n) (x : X.right.obj n) (p : P.obj n) :
    (uncurry (a ≫ (suspensionHom X Y).right ≫
      PointedObject.basedHomι (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Y))).app n
        ((productToSmash circle X).app n (c, x), p) =
    (productToSmash circle Y).app n
      (c, (uncurry (a ≫ PointedObject.basedHomι X Y)).app n (x, p)) := by
  have h := types_congr_hom (NatTrans.congr_app
    (suspensionHom_underlying_evaluation X Y) n) ((c, x), a.app n p)
  simp only [uncurry_natural_left]
  exact h

end SerrePositivity.KST.SConstruction
