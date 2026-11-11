module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexCoefficientValues
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexRawLongCanonical
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedUniversalEdgeTargetValue
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedValueMorphismUniversalAction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalDiagramRestriction

/-!
概要：元の長辺比較と元の右評価成分の三頂点の値を、元の実射の等式で揃える。
方針：元の全係数の値と、元の実辺の指定普遍比較の実終点を計算する。
規約：HEq から端点等式を取り出さない。使われ方：元の長辺二因子の指定値の合成。
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
local notation "g" => coherentColimitApexTargetCoefficientMap B T
local notation "V₀" => pointedFiberValueTo (coherentColimitApex_raw_zero_vertex B T)
local notation "V₂" => pointedFiberValueTo (coherentColimitApex_raw_two_vertex B T)
local notation "V" => QCatEquivalence.hom
  (pointedSpaceFiberValueEquivalence (spaceInfinityVertex K₂))
local notation "C" => pointedCoherentFiberComparison K₀ ≫
  eqToHom (congrArg (vertexFiber pointedSpaceProjection)
    (Eq.symm (spaceInfinityVertex_eq_coherent K₀)))
local notation "D" => CategoryTheory.Functor.map SSet.uliftFunctor
  (CategoryTheory.Functor.map SSet.opFunctor (eHomWhiskerLeft SSet pointKanObject f))
local notation "Vcoh" => eqToHom (congrArg (vertexFiber pointedSpaceProjection)
  (Eq.symm (spaceInfinityVertex_eq_coherent K₂))) ≫ V
local notation "P" => NatTrans.app (pre C)
  (CategoryTheory.Functor.obj SSet.uliftFunctor (KanObject.obj K₂))
local notation "R" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B d)
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)

/-- 元の実長辺比較の始点の値は、元の固定射値比較の同じ始点。 -/
lemma coherentColimitApexLongValue_source_vertex :
    functorVertex (g ≫ V₂) = functorVertex ((D ≫ pointedCoherentFiberComparison K₂) ≫ Vcoh) := by
  apply congrArg functorVertex
  simpa only [Category.assoc] using coherentColimitApexTargetCoefficientMap_value B T

/-- 元の raw 長辺値比較の終点は、同じ右作用成分の前合成の始点。 -/
lemma coherentColimitApexLongValue_action_source_vertex :
    functorVertex ((q ≫ V₀) ≫ (SSet.uliftFunctor.{u + 1, u}).map f) =
      NatTrans.app P (Opposite.op ⦋0⦌)
        (functorVertex ((pointedSpaceFiberValueEquivalence (spaceInfinityVertex K₀)).hom ≫
          (SSet.uliftFunctor.{u + 1, u}).map f)) := by
  rw [functorVertex_precomposition]
  have h := congrArg (fun k => k ≫ (SSet.uliftFunctor.{u + 1, u}).map f)
    (coherentColimitApexCoefficientMap_value B T)
  simpa only [Category.assoc] using congrArg functorVertex h

/-- 元の指定普遍比較の実終点の値は、同じ元の右作用成分の前合成の終点。 -/
lemma coherentColimitApexLongValue_action_target_vertex :
    functorVertex ((q ≫ (functorVertexEquiv _ _).symm
      ((parametrizedFiberTransport pointedSpaceProjection _ _).app (Opposite.op ⦋0⦌)
        (NatTrans.app R (Opposite.op ⦋0⦌) l))) ≫ V₂) =
      NatTrans.app P (Opposite.op ⦋0⦌)
        ((pointedValueHomTransport K₀ K₂).app (Opposite.op ⦋0⦌)
          (ULift.up (functorVertex f))) := by
  rw [pointedValueHomTransport_morphism_vertex, functorVertex_precomposition]
  apply congrArg functorVertex
  have h := pointedIntervalUniversalIso_target_value_change f
    (coherentColimitRawSpaceEdge B d) (coherentColimitApex_raw_zero_vertex B T)
    (coherentColimitApex_raw_two_vertex B T)
    ((coherentColimitRawSpaceEdge_long B a T).trans
      (pointedRightMorphismEdge_recover (SpaceInfinity.δ 1 s)).symm) q
  rw [coherentColimitApexCoefficientMap_standard] at h
  exact h

end SerrePositivity.InfinityCategories.F2
