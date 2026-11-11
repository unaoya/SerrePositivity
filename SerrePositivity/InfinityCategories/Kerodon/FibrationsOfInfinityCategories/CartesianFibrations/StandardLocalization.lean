module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.StandardInvertingComparison
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.RestrictedPrecomposition
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FullSubcomplexFunctorFaithful

/-!
概要：標準単体上の初頂点写像の局所化普遍性。
方針：標準切断による制限を逆とし、反転関手の全パラメーター上で比較を同型にする。
規約：一般の底への貼り合わせはここでは主張しない。
使われ方：共同切断評価の元の底への降下の局所的な普遍性。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 標準比較の全ての縦辺は、局所化で指定した辺の集合に属する。 -/
lemma transportStandardSectionHomotopy_component_mem (n : ℕ)
    (x : (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory (Δ[n] : SSet.{u}))) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportStandardSectionHomotopy n) x).edge ∈
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges Δ[n] := by
  have hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (x.obj 0) = x := ComposableArrows.ext₀ rfl
  rw [← hx]
  exact ⟨_, _, (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportStandardSectionComparison n).app (x.obj 0),
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportStandardSectionComparison_preservesFirst _,
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.ordinaryComparisonHomotopy_vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportStandardSectionComparison n) (x.obj 0)).symm⟩

/-- 初頂点写像と標準切断の合成を通常の有限順序の関手で表示する。 -/
lemma transportStandardFirstVertexMap_section (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap (Δ[n] : SSet.{u}) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportStandardFirstVertexSection n =
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportStandardFirstVertex n) ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportStandardSection n) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportStandardFirstVertex_nerve]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportStandardFirstVertexSection]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- 反転する関手全体を同時に動かした標準比較の同型。 -/
def transportStandardInvertingFamilyIso (n : ℕ) (E : SSet.{u}) [Quasicategory E] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory Δ[n])) E
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges Δ[n])).ι ≫
          (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap Δ[n] ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportStandardFirstVertexSection n)).app E)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory Δ[n])) E
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges Δ[n])).ι := by
  let K := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory Δ[n])) E
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges Δ[n])
  have h := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIsoRestrictedPrecompositionOfHomotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportStandardSectionHomotopy n) K.ι (by
      intro v U hU x
      have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v
      change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsInvertingFunctorVertex _ E (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges Δ[n]) v.val at hv
      unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsInvertingFunctorVertex at hv
      rw [show v.val = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ E) U from hU,
        Equiv.symm_apply_apply] at hv
      have hi := hv (transportStandardSectionHomotopy_component_mem n x)
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportStandardSectionHomotopy n) x).edge).map
          ((truncation 2).map U))
        (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportStandardSectionHomotopy n) x).toTruncated.map
            ((truncation 2).map U)) rfl).mp hi)
  simpa only [transportStandardFirstVertexMap_section, pre_id, NatTrans.id_app,
    Category.comp_id] using h

/-- 局所化による前合成の逆となる、標準切断に沿う制限。 -/
def transportStandardLocalizationRestriction (n : ℕ) (E : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory Δ[n])) E
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges Δ[n]) : SSet.{u}) ⟶ (ihom (Δ[n] : SSet.{u})).obj E :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory Δ[n])) E
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges Δ[n])).ι ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportStandardFirstVertexSection n)).app E

/-- 標準単体上の初頂点写像の前合成は、反転関手の全部分圏への同値。 -/
def transportStandardLocalizationEquivalence (n : ℕ) (E : SSet.{u}) [Quasicategory E] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((ihom (Δ[n] : SSet.{u})).obj E)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory Δ[n])) E
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges Δ[n]) : SSet.{u}) where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap Δ[n])
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges Δ[n]) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap_inverts Δ[n]) E
  inv := transportStandardLocalizationRestriction n E
  homInvIso := by
    have h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap Δ[n])
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges Δ[n]) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap_inverts Δ[n]) E ≫
        transportStandardLocalizationRestriction n E = 𝟙 _ := by
      dsimp only [transportStandardLocalizationRestriction]
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition_ι, ← NatTrans.comp_app,
        ← pre_map, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportStandardFirstVertexSection_comp, pre_id, NatTrans.id_app]
    rw [h]
  invHomIso := by
    let K := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory Δ[n])) E
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges Δ[n])
    let U := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap Δ[n])
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges Δ[n]) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap_inverts Δ[n]) E
    let V := transportStandardLocalizationRestriction n E
    have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((V ≫ U) ≫ K.ι) ((𝟙 (K : SSet.{u})) ≫ K.ι) := by
      simpa only [V, U, K, transportStandardLocalizationRestriction, Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition_ι, pre_map, NatTrans.comp_app, Category.id_comp] using
        transportStandardInvertingFamilyIso n E
    let hf := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.fullSubcomplexFunctorInclusionHoFullyFaithful (K : SSet.{u})
      ((ihom (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory Δ[n]))).obj E)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsInvertingFunctorVertex _ E (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges Δ[n]))
    exact hf.preimageIso
      (X := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (V ≫ U)))
      (Y := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 (K : SSet.{u})))) h

/-- 初頂点写像は、標準単体上では指定辺に関する局所化を表す。 -/
lemma transportSimplexFirstVertexMap_standard_isLocalization (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap (Δ[n] : SSet.{u}))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges Δ[n]) := by
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap_inverts Δ[n], fun E _ ↦ ?_⟩
  exact (transportStandardLocalizationEquivalence n E).isQCatEquivalence

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
