module

public import SerrePositivity.InfinityCategories.F2.CoherentRestrictedPrismComparison
public import SerrePositivity.InfinityCategories.F2.CoherentCospanRestrictedPrismVertexEquality

/-!
概要：元の局所指定比較の合成と、全 native 錐からの指定長辺比較を同定する。
方針：元の普遍 prism と長辺の実頂点を共通空間で揃え、指定像同士を合成する。
規約：終域での類から反映せず、同じ始点固定選択空間で指定同型の等式を証明する。
使われ方：縮小・下降後の実際の fiber 三角形同型との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "q" => coherentCospanNativeLongBase F X Y Z C b
local notation "hq" => coherentCospanNativeLongBase_initial F X Y Z C b

/-- 元の左の二 prism の局所指定比較を共通空間へ写した同型。 -/
def coherentCospanRestrictedLeftComparisonIso :
    VertexIso (coherentCospanRestrictedUniversalLeft F X Y Z C b)
      (coherentCospanRestrictedLongLeft F X Y Z C b) :=
  coherentRestrictedPrismComparisonIso F X Z C.toLeft C.fromLeft C.leftTriangle b q hq
    (coherentCospanRestrictedPrismBase_left F X Y Z C b)

/-- 元の右の二 prism の局所指定比較を同じ共通空間へ写した同型。 -/
def coherentCospanRestrictedRightComparisonIso :
    VertexIso (coherentCospanRestrictedUniversalRight F X Y Z C b)
      (coherentCospanRestrictedLongRight F X Y Z C b) :=
  coherentRestrictedPrismComparisonIso F Y Z C.toRight C.fromRight C.rightTriangle b q hq
    (coherentCospanRestrictedPrismBase_right F X Y Z C b)

/-- 同じ元の普遍 prism を介する二つの局所指定比較の、元の長辺同士の合成。 -/
def coherentCospanRestrictedPrismPathIso :
    VertexIso (coherentCospanNativeLeftOldLongVertex F X Y Z C b)
      (coherentCospanNativeRightOldLongVertex F X Y Z C b) :=
  (eqToIso (congrArg SSet.HomotopyCategory.mk
    (coherentCospanRestrictedLongLeft_eq F X Y Z C b))).symm ≪≫
  (coherentCospanRestrictedLeftComparisonIso F X Y Z C b).symm ≪≫
  eqToIso (congrArg SSet.HomotopyCategory.mk (coherentCospanRestrictedUniversal_eq F X Y Z C b)) ≪≫
  coherentCospanRestrictedRightComparisonIso F X Y Z C b ≪≫
  eqToIso (congrArg SSet.HomotopyCategory.mk (coherentCospanRestrictedLongRight_eq F X Y Z C b))

/-- 元の局所指定比較の合成は、同じ実長辺の native 全錐からの指定比較に等しい。 -/
lemma coherentCospanRestrictedPrismPathIso_eq_native :
    coherentCospanRestrictedPrismPathIso F X Y Z C b =
      coherentCospanNativeCommonLongPathIso F X Y Z C b := by
  have h := coherentCospanNativeLongExtensionSpace_contractible F X Y Z C b
  have := h.kanComplex
  apply Iso.ext
  have ht := h.isTerminalVertex (coherentCospanNativeRightOldLongVertex F X Y Z C b)
  exact ht.isTerminalHo.hom_ext _ _

end SerrePositivity.InfinityCategories.F2
