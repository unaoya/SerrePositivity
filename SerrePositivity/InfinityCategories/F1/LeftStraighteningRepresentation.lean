module

public import SerrePositivity.InfinityCategories.F1.NerveStraighteningRepresentation
public import SerrePositivity.InfinityCategories.F1.TransportSimplexUnderBaseChange
public import SerrePositivity.InfinityCategories.F1.LeftStraighteningVertices

/-!
概要：実際の straightening の対象での図式と相対表現の比較。
方針：初頂点写像上の strict transport の比較を局所化の充満忠実性で降下する。
規約：底は任意の小さい単体集合。対象ごとの関手同型を全対象の自然性とは区別する。
使われ方：§5.6.5 の分類図式と実際の straightening の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 局所化に沿う前合成は、周囲の関手圏への射としても充満忠実。 -/
lemma localization_pre_isFullyFaithful {X D : SSet.{u}} {F : X ⟶ D}
    {W : Set (X _⦋1⦌)} (h : IsLocalization F W) (K : SSet.{u}) [Quasicategory K] :
    IsFullyFaithful ((pre F).app K) := by
  rw [← localizationPrecomposition_ι F W h.choose K]
  exact (h.choose_spec K).isFullyFaithful.comp
    (isFullyFaithful_fullSubcomplexOnVertices_ι _ _)

/-- 実際の分類関手を一つの left fibration に評価して得られる底全体の図式。 -/
def leftStraighteningInfinityDiagram {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] :
    (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u} :=
  (functorVertexEquiv _ _).symm
    ((leftStraighteningInfinityMap B).app (Opposite.op ⦋0⦌) (leftFibrationInfinityVertex p))

/-- 図式の頂点表示は、実際の coherent な分類関手の値そのもの。 -/
lemma leftStraighteningInfinityDiagram_vertex {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] :
    functorVertex (leftStraighteningInfinityDiagram p) =
      (leftStraighteningInfinityMap B).app (Opposite.op ⦋0⦌)
        (leftFibrationInfinityVertex p) :=
  (functorVertexEquiv _ _).apply_symm_apply _

local instance {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (g : D ⟶ B) :
    LeftFibration (pullback.snd p g) :=
  ⟨leftFibrations.pullback_snd p g (LeftFibration.mem (p := p))⟩

/-- 実際の対象図式の初頂点制限は、引き戻した射影の strict transport と同型。 -/
def leftStraighteningInfinityDiagram_firstVertexIso {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B) ≫
        leftStraighteningInfinityDiagram p)
      (leftStraighteningCandidate (pullback.snd p (transportSimplexFirstVertexMap B))) := by
  let k := transportSimplexFirstVertexMap B
  let P := (pre ((SSet.uliftFunctor.{u + 1, u}).map k)).app SpaceInfinity.{u}
  have h₁ : functorVertex ((SSet.uliftFunctor.map k) ≫ leftStraighteningInfinityDiagram p) =
      P.app (Opposite.op ⦋0⦌) ((leftStraighteningInfinityMap B).app (Opposite.op ⦋0⦌)
        (leftFibrationInfinityVertex p)) :=
    congrArg (P.app (Opposite.op ⦋0⦌)) (leftStraighteningInfinityDiagram_vertex p)
  have h₂ : (leftFibrationInfinityBaseChange k ≫
      leftStraighteningCoherentMap (TransportSimplexCategory B)).app (Opposite.op ⦋0⦌)
        (leftFibrationInfinityVertex p) =
      functorVertex (leftStraighteningCandidate (pullback.snd p k)) :=
    (congrArg ((leftStraighteningCoherentMap (TransportSimplexCategory B)).app
      (Opposite.op ⦋0⦌)) (leftFibrationInfinityBaseChange_vertex k
        (leftFibrationObjectOf p))).trans (leftStraighteningCoherentMap_vertex (pullback.snd p k))
  exact eqToIso (congrArg HomotopyCategory.mk h₁) ≪≫
    (leftStraighteningInfinityMap_firstVertexRestrictionIso B).app
      (leftFibrationInfinityVertex p) ≪≫ eqToIso (congrArg HomotopyCategory.mk h₂)

/-- 任意の相対表現の分類図式は、実際の straightening の対象図式と関手同型。 -/
def leftStraighteningInfinityDiagram_representationIso {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p]
    (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p)) :
    FunctorIso (leftStraighteningInfinityDiagram p) R.diagram := by
  have e := leftStraighteningInfinityDiagram_firstVertexIso p ≪≫
    nerveStraighteningRepresentationIso (pullback.snd p (transportSimplexFirstVertexMap B))
      (R.nativeRestrict (transportSimplexFirstVertexMap B))
  exact (localization_pre_isFullyFaithful
    (transportSimplexFirstVertexMap_ulift_isLocalization.{u, u + 1} B)
    SpaceInfinity.{u}).preimageVertexIso e

end SerrePositivity.InfinityCategories
