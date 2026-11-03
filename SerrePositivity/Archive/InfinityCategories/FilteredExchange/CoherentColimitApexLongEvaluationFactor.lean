module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexLongValueComposite
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexLongValueVertices
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexLongFixedValue
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.VertexIsoCompositionTransport
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedHomTriangleLongMorphism

/-!
概要：元の全実長辺比較と raw 長辺値比較の合成を、元の同じ射の評価比較へ戻す。
方針：元の二因子の比を消去し、三つの実頂点の値と二指定因子の値を同時に移す。
規約：元の指定比較・全係数を保持。使われ方：元の長辺値式と二辺値式の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "s" => coherentColimitApexTriangle B T
local notation "K₀" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))
local notation "K₂" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2))
local notation "f" => coherentEdgeHom (SpaceInfinity.δ 1 s)
local notation "q" => coherentColimitApexCoefficientMap B T
local notation "V₀" => pointedFiberValueTo (coherentColimitApex_raw_zero_vertex B T)
local notation "V₂" => pointedFiberValueTo (coherentColimitApex_raw_two_vertex B T)
local notation "D" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B d)
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "E" => Equiv.symm (functorVertexEquiv _ _)
  (NatTrans.app (parametrizedFiberTransport pointedSpaceProjection
    (JoinCocone.vertex (coherentDiagramTotalCocone F))
    (JoinCocone.vertex (coherentDiagramTotalCocone J))) (Opposite.op ⦋0⦌)
      (NatTrans.app D (Opposite.op ⦋0⦌) l))
local notation "C" => pointedCoherentFiberComparison K₀ ≫
  eqToHom (congrArg (vertexFiber pointedSpaceProjection)
    (Eq.symm (spaceInfinityVertex_eq_coherent K₀)))
local notation "P" => NatTrans.app (pre C)
  (CategoryTheory.Functor.obj SSet.uliftFunctor (KanObject.obj K₂))
local notation "R" => coherentColimitApexLongRawValueRatio B T
local notation "M" => VertexIso.map (pointedValueHomActionAt f) P
local notation "N" => functorIsoOfEq
  (FunctorIso.postcomp (coherentColimitApexPointedLongNativeComparison B T) V₂)
    rfl (Category.assoc q E V₂)

/-- 元の全実長辺比較と raw 長辺値比較の合成は、元の同じ固定射の評価比較の値。 -/
lemma coherentColimitApexLongValueComposite_heq_evaluation :
    HEq (coherentColimitApexLongValueComposite B T)
      (pointedHomMorphismEvaluationComparison f) := by
  have h := congrArg (fun e => e ≪≫ (R).symm)
    (coherentColimitApexLongValueComposite_trans_ratio B T)
  have hd : coherentColimitApexLongValueComposite B T = N ≪≫ (R).symm := by
    simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using h
  have ha := coherentColimitApexLongValue_source_vertex B T
  have hb : functorVertex (q ≫ (E ≫ V₂)) = NatTrans.app P (Opposite.op ⦋0⦌)
      ((pointedValueHomTransport K₀ K₂).app (Opposite.op ⦋0⦌)
        (ULift.up (functorVertex f))) := by
    simpa only [Category.assoc] using coherentColimitApexLongValue_action_target_vertex B T
  have hc : functorVertex (q ≫ (V₀ ≫ (SSet.uliftFunctor.{u + 1, u}).map f)) =
      NatTrans.app P (Opposite.op ⦋0⦌)
        (functorVertex ((pointedSpaceFiberValueEquivalence (spaceInfinityVertex K₀)).hom ≫
          (SSet.uliftFunctor.{u + 1, u}).map f)) := by
    simpa only [Category.assoc] using coherentColimitApexLongValue_action_source_vertex B T
  have hn : HEq N (pointedHomMorphismValueComparison f) :=
    (functorIsoOfEq_heq _ _ _).trans
      (coherentColimitApexPointedLongNativeComparison_post_value_heq_morphism B T)
  have hr := coherentColimitApexLongRawValueRatio_heq_evaluation B T
  have hs := vertexIso_symm_heq_of_heq R M hc hb hr
  have he := vertexIso_trans_heq_of_heq N (R).symm
    (pointedHomMorphismValueComparison f) (M).symm ha hb hc hn hs
  exact (heq_of_eq hd).trans he

/-- 元の全三角形の長辺評価比較は、同じ実長辺比較と raw 長辺値比較の指定合成。 -/
lemma coherentColimitApexLongEvaluationComparison_heq_value_composite :
    HEq (pointedHomTriangleLongEvaluationComparison s)
      (coherentColimitApexLongValueComposite B T) :=
  (heq_of_eq (pointedHomTriangleLongEvaluationComparison_eq_morphism s)).trans
    (coherentColimitApexLongValueComposite_heq_evaluation B T).symm

end SerrePositivity.InfinityCategories.F2
