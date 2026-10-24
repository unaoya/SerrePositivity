module

public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexFirstValueSquare
public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexFirstValueVertices
public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexFirstFixedValue
public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexFirstRatioAction
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.VertexIsoCompositionTransport
/-!
概要：元の中間比較の値と raw 第一辺値の合成を、元の第一射の評価比較へ戻す。
方針：同じ指定対角値と比の逆の二因子を、元の三実頂点の値を保持して照合する。
規約：元の全初期係数・raw 辺値・指定対角比較を保持する。
使われ方：Ncomp の元の二辺値から二射の評価合成への帰還。
-/

@[expose] public section
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "s" => coherentColimitApexTriangle B T
local notation "K₀" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))
local notation "K₁" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 1))
local notation "f" => coherentEdgeHom (SpaceInfinity.δ 2 s)
local notation "q" => coherentColimitApexCoefficientMap B T
local notation "V₀" => pointedFiberValueTo (coherentColimitApex_raw_zero_vertex B T)
local notation "V₁" => pointedFiberValueTo (coherentColimitApex_raw_one_vertex B T)
local notation "C" => pointedCoherentFiberComparison K₀ ≫
  eqToHom (congrArg (vertexFiber pointedSpaceProjection)
    (Eq.symm (spaceInfinityVertex_eq_coherent K₀)))
local notation "P" => NatTrans.app (pre C)
  (CategoryTheory.Functor.obj SSet.uliftFunctor (KanObject.obj K₁))
local notation "v" => (SSet.const (coherentColimitRawIntervalVertex B a) :
  spaceSimplexPointedCoefficients s ⟶ _)
local notation "Γ" => intervalMappingCurryOfEndpoints (intervalMappingUncurry v)
  (intervalMappingUncurry_zero v) (intervalMappingUncurry_one v)
local notation "R" => coherentColimitApexFirstSquareRawValueRatio B T
local notation "N" => FunctorIso.postcomp (coherentColimitApexFirstDiagonalComparison B T) V₁
local notation "M" => VertexIso.map (pointedValueHomActionAt f) P
/-- 概要：元の中間比較と raw 第一辺値は、同じ第一射の元の評価比較。
方針：実三頂点と指定二因子をそれぞれ照合する。
規約：全係数と指定値を保持。使われ方：二辺評価の合成。 -/
lemma coherentColimitApexFirstValueComposite_heq_evaluation :
    HEq (coherentColimitApexFirstValueComposite B T)
      (pointedHomMorphismEvaluationComparison f) := by
  have ha := coherentColimitApexFirstValue_source_vertex B T
  have hb : functorVertex (diagonalFiberTransport pointedSpaceProjection q Γ ≫ V₁) =
      NatTrans.app P (Opposite.op ⦋0⦌)
        ((pointedValueHomTransport K₀ K₁).app (Opposite.op ⦋0⦌)
          (ULift.up (functorVertex f))) := by
    exact (congrArg functorVertex
      (coherentColimitRawPointDiagonal_native_at_yoneda B a q V₁)).trans
        (coherentColimitApexFirstValue_action_target_vertex B T)
  have hc : functorVertex (q ≫ (V₀ ≫ (SSet.uliftFunctor.{u + 1, u}).map f)) =
      NatTrans.app P (Opposite.op ⦋0⦌)
        (functorVertex ((pointedSpaceFiberValueEquivalence (spaceInfinityVertex K₀)).hom ≫
          (SSet.uliftFunctor.{u + 1, u}).map f)) := by
    simpa only [Category.assoc] using coherentColimitApexFirstValue_action_source_vertex B T
  have hr := coherentColimitApexFirstSquareRawValueRatio_heq_evaluation B T
  have hs := vertexIso_symm_heq_of_heq R M hc hb hr
  have he := vertexIso_trans_heq_of_heq N (R).symm
    (pointedHomMorphismValueComparison f) (M).symm ha hb hc
    (coherentColimitApexFirstDiagonal_post_value_heq_morphism B T) hs
  exact (heq_of_eq (coherentColimitApexFirstValueComposite_eq_diagonal_ratio B T)).trans he
end
end SerrePositivity.InfinityCategories.F2
