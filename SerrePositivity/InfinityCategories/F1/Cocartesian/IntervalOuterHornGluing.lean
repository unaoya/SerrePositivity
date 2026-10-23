module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.IntervalOuterHornSquare
public import SerrePositivity.InfinityCategories.F1.CompositionTriangleFamilyFaces

/-!
概要：外ホーン上で一致する元の二三角形を、同じ三辺固定の標準正方形へ貼る。
方針：対角の一致を使い、第一三角形の二辺と第二三角形の標的辺を回収する。
規約：与えられた二三角形と全パラメーターを保持する。
使われ方：実際の固定成分 Hom fiber の外ホーン pullback の持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (F G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
local notation "c" => (ULift.up (1 : Fin 2))
variable (v : (intervalMappingSpace (coherentNerveVertex (cocartesianTransportDiagramValue F c))
  (coherentNerveVertex (cocartesianTransportDiagramValue G c))) _⦋0⦌)
variable {T : SSet.{u + 1}}
  (a : T ⟶ (ihom (Δ[2] : SSet.{u + 1})).obj CatInfinity.{u})
  (b : T ⟶ cocartesianIntervalCompositionSpace F G v)
  (h : a ≫ ((pre (horn 2 2).ι).app CatInfinity.{u}) =
    b ≫ cocartesianIntervalOuterHornMap F G v)
local notation "D₀" => (qCatDiagramCoherentNerve (cocartesianTransportDiagramValueFunctor F))
local notation "D₁" => (qCatDiagramCoherentNerve (cocartesianTransportDiagramValueFunctor G))

/-- 元の外ホーンで一致する二三角形を、同じ対角で標準正方形へ貼る。 -/
def cocartesianIntervalOuterHornComparisonSquare :
    ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) ⊗ T ⟶ CatInfinity.{u} :=
  parameterizedSquareLift (innerTriangleExtensionUncurry b) (uncurry a)
    (cocartesianIntervalOuterHornComparison_diagonal F G v a b h)

local notation "H" => (cocartesianIntervalOuterHornComparisonSquare F G v a b h)

/-- 貼った正方形の第一三角形は、元の第一三角形の全族。 -/
lemma cocartesianIntervalOuterHornComparisonSquare_first :
    (squareTriangle 0 ▷ T) ≫ H = innerTriangleExtensionUncurry b :=
  parameterizedSquareLift_zero _ _ _

/-- 貼った正方形の第二三角形は、元の第二三角形の全族。 -/
lemma cocartesianIntervalOuterHornComparisonSquare_second :
    (squareTriangle 1 ▷ T) ≫ H = uncurry a := parameterizedSquareLift_one _ _ _

/-- 貼った正方形の始点の辺は、元の始域図式の辺に全パラメーターで定値。 -/
lemma cocartesianIntervalOuterHornComparisonSquare_zero :
    (prismEndpoint 0 Δ[1] ▷ T) ≫ H =
      fst (Δ[1] : SSet.{u + 1}) T ≫ (localKanDiagramBaseIso 1).hom ≫ D₀ := by
  rw [← triangleSquare_upper_left, comp_whiskerRight, Category.assoc,
    cocartesianIntervalOuterHornComparisonSquare_first]
  calc
    _ = fst (Δ[1] : SSet.{u + 1}) T ≫
        SSet.yonedaEquiv.symm (cocartesianIntervalCompositionFirstEdge F).edge :=
      compositionTriangleFamily_first _ _ b
    _ = _ := by rw [← cocartesianIntervalCompositionFirstEdge_map]

/-- 貼った正方形の終点の辺は、元の標的図式の辺に全パラメーターで定値。 -/
lemma cocartesianIntervalOuterHornComparisonSquare_one :
    (prismEndpoint 1 Δ[1] ▷ T) ≫ H =
      fst (Δ[1] : SSet.{u + 1}) T ≫ (localKanDiagramBaseIso 1).hom ≫ D₁ := by
  rw [← triangleSquare_lower_right, comp_whiskerRight, Category.assoc,
    cocartesianIntervalOuterHornComparisonSquare_second,
    cocartesianIntervalOuterHornComparison_target F G v a b h,
    ← cocartesianIntervalCompositionFirstEdge_map]

/-- 貼った正方形の右側の辺は、元の指定成分に全パラメーターで定値。 -/
lemma cocartesianIntervalOuterHornComparisonSquare_at_one :
    (lift (𝟙 (Δ[1] : SSet.{u + 1}))
      (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ▷ T) ≫ H =
      intervalMappingUncurry (SSet.const v : T ⟶ _) := by
  change (SSet.ι₁ ▷ T) ≫ H = _
  rw [← triangleSquare_upper_top, comp_whiskerRight, Category.assoc,
    cocartesianIntervalOuterHornComparisonSquare_first]
  exact (compositionTriangleFamily_last _ _ b).trans (intervalMappingUncurry_const_vertex v).symm

end SerrePositivity.InfinityCategories
