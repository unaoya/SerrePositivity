module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitRawTriangleUniversalChoice
public import SerrePositivity.InfinityCategories.F2.PointedIntervalTransportPointPrismNaturality
public import SerrePositivity.InfinityCategories.F2.PrismFiberWitnessReindex
public import SerrePositivity.InfinityCategories.F2.RelativeExtensionFiberEndpointDataEquality

/-!
概要：元の指定普遍三角形比較は、任意の係数射による再制限と値まで可換する。
方針：元の全三角形を制限し、二辺固定の比較の一意性で元の選択へ戻す。
規約：元の二実辺と全長区間を保持。使われ方：全係数同値による整合の反映。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d) {K L : SSet.{u + 1}}
  (f : K ⟶ vertexFiber pointedSpaceProjection (coherentDiagramTotalCocone F).vertex)
  (r : L ⟶ K)
local notation "X" => coherentColimitRawUniversalTrianglePrism B T f
local notation "Y" => (Δ[2] ◁ r) ≫ X

/-- 元の全三角形を係数制限しても、元の指定普遍比較そのものを回収する。 -/
lemma coherentColimitRawUniversalTriangleComparison_precomp :
    HEq ((coherentColimitRawUniversalTriangleComparison B T f).precomp r)
      (coherentColimitRawUniversalTriangleComparison B T (r ≫ f)) := by
  have hp : Y ≫ pointedSpaceProjection =
      fst Δ[2] L ≫ T.diagram ≫ coherentColimitFunctor B := by
    rw [Category.assoc, coherentColimitRawUniversalTrianglePrism_projection,
      ← Category.assoc, whiskerLeft_fst]
  have hf : (stdSimplex.δ (2 : Fin 3) ▷ L) ≫ Y =
      coherentColimitRawTransportPointPrism B a (r ≫ f) := by
    rw [trianglePrism_restrict_baseChange, coherentColimitRawUniversalTrianglePrism_first,
      coherentColimitRawTransportPointPrism_precomp]
  have hl : (stdSimplex.δ (0 : Fin 3) ▷ L) ≫ Y =
      coherentColimitRawTransportPointPrism B b
        ((r ≫ f) ≫ coherentColimitRawFiberTransport B a) := by
    rw [trianglePrism_restrict_baseChange, coherentColimitRawUniversalTrianglePrism_last,
      coherentColimitRawTransportPointPrism_precomp]
    rfl
  have ho := coherentColimitRawTriangleLongPointComparison_eq_universal B T f X
    (coherentColimitRawUniversalTrianglePrism_projection B T f)
    (coherentColimitRawUniversalTrianglePrism_first B T f)
    (coherentColimitRawUniversalTrianglePrism_last B T f)
  have hn := coherentColimitRawTriangleLongPointComparison_eq_universal B T (r ≫ f) Y hp hf hl
  rw [← ho, ← hn]
  unfold coherentColimitRawTriangleLongPointComparison
  rw [prismFiberWitnessIso_precomp]
  apply relativeExtensionFiberEndpoint_witnessIso_heq_of_dataEq
  · rw [← Category.assoc, whiskerLeft_fst]
  · rfl
  · exact (trianglePrism_restrict_baseChange r X 1).symm
  · exact coherentColimitRawTransportPointPrism_precomp B d f r
  · rfl
  · rfl

end SerrePositivity.InfinityCategories.F2
