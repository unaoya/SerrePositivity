module

public import SerrePositivity.InfinityCategories.F1.Transport.StandardInvertingComparison
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.RestrictedPrecomposition
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FullSubcomplexFunctorFaithful

/-!
概要：標準単体上の初頂点写像の局所化普遍性。
方針：標準切断による制限を逆とし、反転関手の全パラメーター上で比較を同型にする。
規約：一般の底への貼り合わせはここでは主張しない。
使われ方：共同切断評価の元の底への降下の局所的な普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 標準比較の全ての縦辺は、局所化で指定した辺の集合に属する。 -/
lemma transportStandardSectionHomotopy_component_mem (n : ℕ)
    (x : (nerve (TransportSimplexCategory (Δ[n] : SSet.{u}))) _⦋0⦌) :
    (simplicialHomotopyVertexEdge (transportStandardSectionHomotopy n) x).edge ∈
      transportSimplexInitialEdges Δ[n] := by
  have hx : nerveVertex (x.obj 0) = x := ComposableArrows.ext₀ rfl
  rw [← hx]
  exact ⟨_, _, (transportStandardSectionComparison n).app (x.obj 0),
    transportStandardSectionComparison_preservesFirst _,
    (ordinaryComparisonHomotopy_vertex (transportStandardSectionComparison n) (x.obj 0)).symm⟩

/-- 初頂点写像と標準切断の合成を通常の有限順序の関手で表示する。 -/
lemma transportStandardFirstVertexMap_section (n : ℕ) :
    transportSimplexFirstVertexMap (Δ[n] : SSet.{u}) ≫
      transportStandardFirstVertexSection n =
      nerveMap (transportStandardFirstVertex n) ≫ nerveMap (transportStandardSection n) := by
  rw [← transportStandardFirstVertex_nerve]
  dsimp only [transportStandardFirstVertexSection]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- 反転する関手全体を同時に動かした標準比較の同型。 -/
def transportStandardInvertingFamilyIso (n : ℕ) (E : SSet.{u}) [Quasicategory E] :
    FunctorIso
      ((invertingFunctors (nerve (TransportSimplexCategory Δ[n])) E
        (transportSimplexInitialEdges Δ[n])).ι ≫
          (pre (transportSimplexFirstVertexMap Δ[n] ≫
            transportStandardFirstVertexSection n)).app E)
      (invertingFunctors (nerve (TransportSimplexCategory Δ[n])) E
        (transportSimplexInitialEdges Δ[n])).ι := by
  let K := invertingFunctors (nerve (TransportSimplexCategory Δ[n])) E
    (transportSimplexInitialEdges Δ[n])
  have h := functorIsoRestrictedPrecompositionOfHomotopy
    (transportStandardSectionHomotopy n) K.ι (by
      intro v U hU x
      have hv := fullSubcomplexOnVertices_vertex v
      change IsInvertingFunctorVertex _ E (transportSimplexInitialEdges Δ[n]) v.val at hv
      unfold IsInvertingFunctorVertex at hv
      rw [show v.val = (functorVertexEquiv _ E) U from hU,
        Equiv.symm_apply_apply] at hv
      have hi := hv (transportStandardSectionHomotopy_component_mem n x)
      exact (isInvertibleEdge_congr (e := (edgeOfSimplex
        (simplicialHomotopyVertexEdge (transportStandardSectionHomotopy n) x).edge).map
          ((truncation 2).map U))
        (f := (simplicialHomotopyVertexEdge
          (transportStandardSectionHomotopy n) x).toTruncated.map
            ((truncation 2).map U)) rfl).mp hi)
  simpa only [transportStandardFirstVertexMap_section, pre_id, NatTrans.id_app,
    Category.comp_id] using h

/-- 局所化による前合成の逆となる、標準切断に沿う制限。 -/
def transportStandardLocalizationRestriction (n : ℕ) (E : SSet.{u}) :
    (invertingFunctors (nerve (TransportSimplexCategory Δ[n])) E
      (transportSimplexInitialEdges Δ[n]) : SSet.{u}) ⟶ (ihom (Δ[n] : SSet.{u})).obj E :=
  (invertingFunctors (nerve (TransportSimplexCategory Δ[n])) E
    (transportSimplexInitialEdges Δ[n])).ι ≫ (pre (transportStandardFirstVertexSection n)).app E

/-- 標準単体上の初頂点写像の前合成は、反転関手の全部分圏への同値。 -/
def transportStandardLocalizationEquivalence (n : ℕ) (E : SSet.{u}) [Quasicategory E] :
    QCatEquivalence ((ihom (Δ[n] : SSet.{u})).obj E)
      (invertingFunctors (nerve (TransportSimplexCategory Δ[n])) E
        (transportSimplexInitialEdges Δ[n]) : SSet.{u}) where
  hom := localizationPrecomposition (transportSimplexFirstVertexMap Δ[n])
    (transportSimplexInitialEdges Δ[n]) (transportSimplexFirstVertexMap_inverts Δ[n]) E
  inv := transportStandardLocalizationRestriction n E
  homInvIso := by
    have h : localizationPrecomposition (transportSimplexFirstVertexMap Δ[n])
        (transportSimplexInitialEdges Δ[n]) (transportSimplexFirstVertexMap_inverts Δ[n]) E ≫
        transportStandardLocalizationRestriction n E = 𝟙 _ := by
      dsimp only [transportStandardLocalizationRestriction]
      rw [← Category.assoc, localizationPrecomposition_ι, ← NatTrans.comp_app,
        ← pre_map, transportStandardFirstVertexSection_comp, pre_id, NatTrans.id_app]
    rw [h]
  invHomIso := by
    let K := invertingFunctors (nerve (TransportSimplexCategory Δ[n])) E
      (transportSimplexInitialEdges Δ[n])
    let U := localizationPrecomposition (transportSimplexFirstVertexMap Δ[n])
      (transportSimplexInitialEdges Δ[n]) (transportSimplexFirstVertexMap_inverts Δ[n]) E
    let V := transportStandardLocalizationRestriction n E
    have h : FunctorIso ((V ≫ U) ≫ K.ι) ((𝟙 (K : SSet.{u})) ≫ K.ι) := by
      simpa only [V, U, K, transportStandardLocalizationRestriction, Category.assoc,
        localizationPrecomposition_ι, pre_map, NatTrans.comp_app, Category.id_comp] using
        transportStandardInvertingFamilyIso n E
    let hf := fullSubcomplexFunctorInclusionHoFullyFaithful (K : SSet.{u})
      ((ihom (nerve (TransportSimplexCategory Δ[n]))).obj E)
      (IsInvertingFunctorVertex _ E (transportSimplexInitialEdges Δ[n]))
    exact hf.preimageIso
      (X := HomotopyCategory.mk (functorVertex (V ≫ U)))
      (Y := HomotopyCategory.mk (functorVertex (𝟙 (K : SSet.{u})))) h

/-- 初頂点写像は、標準単体上では指定辺に関する局所化を表す。 -/
lemma transportSimplexFirstVertexMap_standard_isLocalization (n : ℕ) :
    IsLocalization (transportSimplexFirstVertexMap (Δ[n] : SSet.{u}))
      (transportSimplexInitialEdges Δ[n]) := by
  refine ⟨transportSimplexFirstVertexMap_inverts Δ[n], fun E _ ↦ ?_⟩
  exact (transportStandardLocalizationEquivalence n E).isQCatEquivalence

end SerrePositivity.InfinityCategories
