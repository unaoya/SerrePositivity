module
public import SerrePositivity.KST.SConstruction.PointedClosedHomInclusion

/-! # 点つき閉 Hom の評価を元の直積上で回収する
概要：smash の評価と基点を忘れた全写像族の評価を同じ商射で比較する。
方針：点つき curry の包含式を uncurry し、全パラメータの前合成を保つ。
規約：Kan 性は不要。使われ方：suspension の全族作用の具体的な評価。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet

/-- 元の直積から smash へ写して点つき評価する射は、同じ basedHom の評価。 -/
lemma pointedClosedEvaluation (X Y : PointedSimplicialSet.{u}) :
    PointedSimplicialSet.productToSmash X (PointedObject.basedHom X Y) ≫
      ((ihom.ev X).app Y).right = uncurry (PointedObject.basedHomι X Y) := by
  have h := congrArg (uncurry (C := SSet.{u})) (pointedLaxClosedFamilyMap_eq X Y)
  change uncurry (curry (PointedSimplicialSet.productToSmash X
    (PointedObject.basedHom X Y) ≫ ((ihom.ev X).app Y).right)) = _ at h
  exact (uncurry_curry _).symm.trans h

/-- 任意の全入力族について、smash への商と点つき評価が同じ直積作用を回収する。 -/
lemma pointedClosedEvaluation_family {P : SSet.{u}} (X Y : PointedSimplicialSet.{u})
    (a : P ⟶ (PointedObject.basedHom X Y).right) :
    (X.right ◁ a) ≫ PointedSimplicialSet.productToSmash X (PointedObject.basedHom X Y) ≫
      ((ihom.ev X).app Y).right = uncurry (a ≫ PointedObject.basedHomι X Y) := by
  rw [pointedClosedEvaluation, uncurry_natural_left]

/-- 全点つき写像族の後合成は、元の直積上の作用の後合成となる。 -/
lemma pointedFamily_post_evaluation {P : SSet.{u}} (X : PointedSimplicialSet.{u})
    {Y Z : PointedSimplicialSet.{u}} (a : P ⟶ (PointedObject.basedHom X Y).right)
    (f : Y ⟶ Z) :
    uncurry (a ≫ (PointedObject.basedHomMap X f).right ≫ PointedObject.basedHomι X Z) =
      uncurry (a ≫ PointedObject.basedHomι X Y) ≫ f.right := by
  rw [PointedObject.basedHomMap_ι, ← Category.assoc, uncurry_natural_right]

/-- 全点つき写像族の前合成は、元の直積上の作用の第一因子への前合成となる。 -/
lemma pointedFamily_pre_evaluation {P : SSet.{u}} {X Y : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (Z : PointedSimplicialSet.{u})
    (a : P ⟶ (PointedObject.basedHom Y Z).right) :
    uncurry (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre f Z ≫ PointedObject.basedHomι X Z) =
      (f.right ▷ P) ≫ uncurry (a ≫ PointedObject.basedHomι Y Z) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_ι, ← Category.assoc, uncurry_pre_app]

end SerrePositivity.KST.SConstruction
