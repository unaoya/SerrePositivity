module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.CoslicePinchedLeft
public import SerrePositivity.InfinityCategories.F1B.Diagrams.PointJoinPrism
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap

/-!
概要：一点からの全左 Hom の族を、同じ始点・終点を持つ底の円柱として表示する。
方針：左 Hom と coslice fiber の厳密な同型で普遍余錐を展開し、点との join の prism を使う。
規約：Hom の個別の辺は選ばない。全ての単体を同じ射で保つ。
使われ方：始点 fiber 全体に依存する輸送作用と、既存の点の全 Hom 族との比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {B : SSet.{u}} (a b : B _⦋0⦌)

/-- 全左 Hom の同じ普遍余錐。 -/
def pointHomBaseCone : join (Δ[0] : SSet.{u}) (pinchedHomLeft a b) ⟶ B :=
  sliceUnderUncurry ((pinchedLeftCosliceFiberIso a b).hom ≫
    vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm a)) b)

/-- 全 Hom の普遍余錐の始点は元の指定点。 -/
lemma pointHomBaseCone_source :
    joinInl (Δ[0] : SSet.{u}) (pinchedHomLeft a b) ≫ pointHomBaseCone a b =
      SSet.yonedaEquiv.symm a :=
  sliceUnderUncurry_fixed _

/-- 全 Hom の普遍余錐の終点側は、全パラメータで同じ指定点に固定される。 -/
lemma pointHomBaseCone_target :
    joinInr (Δ[0] : SSet.{u}) (pinchedHomLeft a b) ≫ pointHomBaseCone a b = SSet.const b := by
  rw [pointHomBaseCone, sliceUnderUncurry_projection, Category.assoc,
    vertexFiberι_comp, SSet.comp_const]

/-- 同じ全左 Hom の族を、時間を第一因子とする実際の円柱へ移す。 -/
def pointHomBasePrism : (Δ[1] : SSet.{u}) ⊗ pinchedHomLeft a b ⟶ B :=
  cofinalPointJoinPrism (pinchedHomLeft a b) ≫ pointHomBaseCone a b

/-- 全 Hom の円柱の始点は、指定した始点上で定値。 -/
lemma pointHomBasePrism_zero :
    prismEndpoint 0 (pinchedHomLeft a b) ≫ pointHomBasePrism a b = SSet.const a := by
  rw [pointHomBasePrism, ← Category.assoc, cofinalPointJoinPrism_zero,
    Category.assoc, pointHomBaseCone_source, SSet.yonedaEquiv_symm_zero, SSet.comp_const]

/-- 全 Hom の円柱の終点も、指定した終点上で定値。 -/
lemma pointHomBasePrism_one :
    prismEndpoint 1 (pinchedHomLeft a b) ≫ pointHomBasePrism a b = SSet.const b := by
  rw [pointHomBasePrism, ← Category.assoc, cofinalPointJoinPrism_one, pointHomBaseCone_target]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
