module

public import SerrePositivity.InfinityCategories.F2.LaxPullbackMappingKanObjects
public import SerrePositivity.InfinityCategories.F2.SpaceSquareLimits

/-!
概要：原典の二つの下側の写像空間への cospan。
方針：両端評価と p・q の二射の直積を Kan 対象の射にする。
規約：元の頂点と pinched 単体の値を保持する。
使われ方：Tamme Remark 6 の写像空間の引き戻し正方形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C)
variable (x y : (laxPullback p q) _⦋0⦌)
/-- 概要：原典の二つの下側の写像空間への cospan。
方針：両端評価と p・q の二射の直積を Kan 対象の射にする。
規約：元の四隅と対象間写像空間を保つ。
使われ方：Tamme Remark 6 のホモトピー引き戻しの公開界面。 -/
def laxPullbackMappingEndpointArrow [Quasicategory C] :
    laxPullbackArrowMappingKanObject p q x y ⟶ laxPullbackBaseMappingKanObject p q x y :=
  laxPullbackMappingEndpointMap p q x y
/-- 概要：原典の二つの下側の写像空間への cospan。
方針：両端評価と p・q の二射の直積を Kan 対象の射にする。
規約：元の四隅と対象間写像空間を保つ。
使われ方：Tamme Remark 6 のホモトピー引き戻しの公開界面。 -/
def laxPullbackMappingInputArrow [Quasicategory A] [Quasicategory B] [Quasicategory C] :
    laxPullbackInputsMappingKanObject p q x y ⟶ laxPullbackBaseMappingKanObject p q x y :=
  pinchedHomMap p ((laxPullbackFst p q).app (Opposite.op ⦋0⦌) x)
      ((laxPullbackFst p q).app (Opposite.op ⦋0⦌) y) ⊗ₘ
    pinchedHomMap q ((laxPullbackSnd p q).app (Opposite.op ⦋0⦌) x)
      ((laxPullbackSnd p q).app (Opposite.op ⦋0⦌) y)
/-- 概要：原典の二つの下側の写像空間への cospan。
方針：両端評価と p・q の二射の直積を Kan 対象の射にする。
規約：元の四隅と対象間写像空間を保つ。
使われ方：Tamme Remark 6 のホモトピー引き戻しの公開界面。 -/
def laxPullbackMappingSpaceDiagram [Quasicategory A] [Quasicategory B] [Quasicategory C] :
    AsSmall.{u} WalkingCospan ⥤ KanObject.{u} :=
  HomotopyLimits.kanPullbackDiagram (laxPullbackMappingEndpointArrow p q x y)
    (laxPullbackMappingInputArrow p q x y)

end SerrePositivity.InfinityCategories.F2
