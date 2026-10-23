module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackMappingSpaceDiagram

/-!
概要：対象間写像空間を頂点とする空間の native な極限錐。
方針：指定正方形の極限性と右脚の Kan fibration 性を γ3 の判定へ渡す。
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
variable [Quasicategory A] [Quasicategory B] [Quasicategory C]
/-- 概要：対象間写像空間を頂点とする空間の native な極限錐。
方針：指定正方形の極限性と右脚の Kan fibration 性を γ3 の判定へ渡す。
規約：元の四隅と対象間写像空間を保つ。
使われ方：Tamme Remark 6 のホモトピー引き戻しの公開界面。 -/
def laxPullbackMappingSpaceCone :
    JoinCone (kanDiagramCoherentNerve (laxPullbackMappingSpaceDiagram p q x y)) :=
  spaceSquareCone (K := laxPullbackMappingKanObject p q x y)
    (laxPullbackMappingEndpointArrow p q x y) (laxPullbackMappingInputArrow p q x y)
    (pinchedHomMap (laxPullbackArrow p q) x y) (laxPullbackMappingProjections p q x y)
    (laxPullbackMappingProduct_isPullback p q x y)
/-- 概要：対象間写像空間を頂点とする空間の native な極限錐。
方針：指定正方形の極限性と右脚の Kan fibration 性を γ3 の判定へ渡す。
規約：元の四隅と対象間写像空間を保つ。
使われ方：Tamme Remark 6 のホモトピー引き戻しの公開界面。 -/
lemma laxPullbackMappingSpaceCone_isLimit : IsLimitCone (laxPullbackMappingSpaceCone p q x y) := by
  have : Fibration (show (laxPullbackArrowMappingKanObject p q x y).obj ⟶
      (laxPullbackBaseMappingKanObject p q x y).obj from laxPullbackMappingEndpointArrow p q x y) :=
    laxPullbackMappingEndpointMap_fibration p q x y
  exact spaceSquareCone_isLimit _ _ _ _ _
/-- 概要：対象間写像空間を頂点とする空間の native な極限錐。
方針：指定正方形の極限性と右脚の Kan fibration 性を γ3 の判定へ渡す。
規約：元の四隅と対象間写像空間を保つ。
使われ方：Tamme Remark 6 のホモトピー引き戻しの公開界面。 -/
lemma laxPullbackMappingSpaceCone_vertex :
    (laxPullbackMappingSpaceCone p q x y).vertex =
      coherentVertex (laxPullbackMappingKanObject p q x y) :=
  spaceSquareCone_vertex _ _ _ _ _

end SerrePositivity.InfinityCategories.F2
