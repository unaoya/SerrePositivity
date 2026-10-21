module

public import SerrePositivity.InfinityCategories.F2.FunctorCospanPointwise
public import SerrePositivity.InfinityCategories.F2.CoherentCospanNativeLimitCone
public import SerrePositivity.InfinityCategories.F2.CoherentCospanNativeComparisonEquivalence

/-!
概要：元の関手 cospan 錐の各点の極限性を、a6 の元の native 比較と極限錐へ接続する。
方針：元の全錐の厳密な一致から既存の filtered 比較を適用する。
規約：元の二三角形・頂点 F・共通対角円柱を保持。使われ方：有限形状の貼り合わせ。
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
  {F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F X} {b : SSet.Homotopy F Y}
  {f : SSet.Homotopy X Z} {g : SSet.Homotopy Y Z} {d : SSet.Homotopy F Z}
  (L : FunctorCompositionTriangle a f d) (R : FunctorCompositionTriangle b g d)
local notation "C" => coherentCospanOfFunctorTriangles L R

/-- 元の全関手錐の点ごとの極限性は、同じ全錐の native 表示の極限性を与える。 -/
lemma functorCospanPointwiseLimit_native
    (hc : IsPointwiseLimitCone (functorCospanCone L R)) (v : B _⦋0⦌) :
    IsLimitCone (coherentCospanConePointwiseCone F X Y Z C v) :=
  (coherentCospanOfFunctorTriangles_pointwise_isLimit_iff L R v).mpr (hc (ULift.up v))

/-- 元の点ごとの関手極限錐から、同じ native 比較そのものの弱同値性が従う。 -/
lemma functorCospanNativeComparison_isWeakHomotopyEquivalence [Quasicategory B]
    [IsFilteredInfinity B] (hc : IsPointwiseLimitCone (functorCospanCone L R)) :
    IsWeakHomotopyEquivalence (coherentCospanConeNativeComparison F X Y Z C) :=
  coherentCospanConeNativeComparison_isWeakHomotopyEquivalence F X Y Z C
    (functorCospanPointwiseLimit_native L R hc)

/-- 元の頂点 F の余極限を頂点とし、元の二三角形から構成した native 極限錐。 -/
def functorCospanNativeLimitCone [Quasicategory B] [IsFilteredInfinity B]
    (hc : IsPointwiseLimitCone (functorCospanCone L R)) :=
  coherentCospanNativeLimitCone F X Y Z C (functorCospanPointwiseLimit_native L R hc)

/-- 元の点ごとの極限錐に a6 を適用して得た同じ錐は、native な極限錐。 -/
lemma functorCospanNativeLimitCone_isLimit [Quasicategory B] [IsFilteredInfinity B]
    (hc : IsPointwiseLimitCone (functorCospanCone L R)) :
    IsLimitCone (functorCospanNativeLimitCone L R hc) :=
  coherentCospanNativeLimitCone_isLimit F X Y Z C (functorCospanPointwiseLimit_native L R hc)

/-- 構成した錐の頂点は、元の入力頂点関手 F の余極限頂点そのもの。 -/
lemma functorCospanNativeLimitCone_vertex [Quasicategory B] [IsFilteredInfinity B]
    (hc : IsPointwiseLimitCone (functorCospanCone L R)) :
    (functorCospanNativeLimitCone L R hc).vertex = coherentDiagramTotalVertex F :=
  coherentCospanNativeLimitCone_vertex F X Y Z C (functorCospanPointwiseLimit_native L R hc)

end SerrePositivity.InfinityCategories.F2
