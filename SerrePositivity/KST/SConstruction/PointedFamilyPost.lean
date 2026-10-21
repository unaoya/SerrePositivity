module
public import SerrePositivity.KST.SConstruction.PointedClosedEvaluation

/-! # 基点固定写像族の同じ後合成の明示的な基礎射
概要：元の点つき後合成を、定義域・値域を明示した同じ単体的写像として保持する。
方針：元の basedHomMap の基礎射をそのまま使い、元の直積作用の評価を回収する。
規約：実際の射・全高次入力を変えない。使われ方：大きな実 dg 模型の型照合。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet

/-- 元の同じ点つき Hom 後合成を、三対象を明示した基礎射として保持する。 -/
def pointedFamilyPost (X Y Z : PointedSimplicialSet.{u}) (f : Y ⟶ Z) :
    (PointedObject.basedHom X Y).right ⟶ (PointedObject.basedHom X Z).right :=
  (PointedObject.basedHomMap X f).right

/-- 明示した後合成は、元の同じ直積上の作用の後合成を回収する。 -/
lemma pointedFamilyPost_evaluation {P : SSet.{u}} (X Y Z : PointedSimplicialSet.{u})
    (a : P ⟶ (PointedObject.basedHom X Y).right) (f : Y ⟶ Z) :
    uncurry (a ≫ pointedFamilyPost X Y Z f ≫ PointedObject.basedHomι X Z) =
      uncurry (a ≫ PointedObject.basedHomι X Y) ≫ f.right :=
  pointedFamily_post_evaluation X a f

end SerrePositivity.KST.SConstruction
