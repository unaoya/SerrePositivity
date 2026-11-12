module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitConstantTriangleLongEndpoint
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ConstantDiagramTransportComparison

/-!
概要：元の定値余極限三角形の二実輸送の一点終点を、元の長辺作用と二辺合成へ戻す。
方針：元の三辺の厳密な定値族表示と同じ長辺の実終点式を使う。
規約：元の実射と同じ係数を保持。使われ方：輸送比較の因子消去の両端の整合。
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
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
local notation "z₃" => JoinCocone.vertex (coherentDiagramTotalCocone J)
local notation "A" => coherentVertexOfHomotopy
  (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B a))
local notation "R" => coherentVertexOfHomotopy
  (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B b))
local notation "C" => coherentVertexOfHomotopy
  (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B c))
local notation "C₀" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B c)

/-- 元の普遍長辺輸送の同じ一点終点は、元の長辺作用の同じ fiber 射影。 -/
lemma coherentColimitConstantTransport_endpoint_point (v : (Δ[0] : SSet.{u + 1}) _⦋0⦌) :
    lift (𝟙 _) (SSet.const v) ≫ (constantDiagramTransportWitness
      (constantDiagramMappingFamilyWitness ((SSet.uliftFunctor.{u + 1, u}).obj B) C₀)).endpoint =
      (leftUnstraighteningMappingVertexMap _ _ C).val ≫
        constantUnstraighteningFiberProjection ((SSet.uliftFunctor.{u + 1, u}).obj B) z₃ := by
  have hc := (coherentColimitRawIntervalVertex_constant B c).trans
    (SSet.yonedaEquiv_symm_zero C)
  rw [constantDiagramTransportWitness_endpoint]
  change lift (𝟙 _) (SSet.const v) ≫
    relativeFunctorUncurry (constantDiagramTransformation _ C₀ ≫
      leftUnstraighteningMappingSpaceMap _ _) ≫ _ = _
  rw [hc, unstraighteningMappingConst_uncurry]
  simp only [← Category.assoc, lift_fst, Category.id_comp]

/-- 元の指定長辺輸送の同じ一点終点は、元の二辺作用の合成の同じ fiber 射影。 -/
lemma coherentColimitConstantTriangleLongTransport_endpoint_point
    (T : FunctorCompositionTriangle a b c) (v : (Δ[0] : SSet.{u + 1}) _⦋0⦌) :
    lift (𝟙 _) (SSet.const v) ≫ (coherentColimitConstantTriangleLongTransport B T).endpoint =
      ((leftUnstraighteningMappingVertexMap _ _ A).val ≫
        (leftUnstraighteningMappingVertexMap _ _ R).val) ≫
          constantUnstraighteningFiberProjection ((SSet.uliftFunctor.{u + 1, u}).obj B) z₃ := by
  rw [coherentColimitConstantTriangleLongTransport_endpoint]
  simp only [← Category.assoc, lift_fst, Category.id_comp]

end SerrePositivity.InfinityCategories.F2
