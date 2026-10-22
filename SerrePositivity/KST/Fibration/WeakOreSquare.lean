module
public import SerrePositivity.KST.Fibration.WeakOreDiagrams

/-! # 元の全高次 Ore 図式の四角形・cospan・分母の厳密な回収 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B : StableCategory.{u}} (i : ExactMap A B)

def weakOreSquare (v : (weakOreDiagrams i) _⦋0⦌) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ B.obj :=
  (functorVertexEquiv _ _).symm
    ((pullback.fst (pullbackProjection B.obj)
      (weakDenominatorCospanInclusion i)).app (Opposite.op ⦋0⦌) v).val

lemma weakOreSquare_isPullback (v : (weakOreDiagrams i) _⦋0⦌) :
    IsPullbackSquare (weakOreSquare i v) :=
  fullSubcomplexOnVertices_vertex ((pullback.fst (pullbackProjection B.obj)
    (weakDenominatorCospanInclusion i)).app (Opposite.op ⦋0⦌) v)

lemma weakOreSquare_cospan (v : (weakOreDiagrams i) _⦋0⦌) :
    pullbackCospan (weakOreSquare i v) =
      (functorVertexEquiv (horn 2 2 : SSet.{u}) B.obj).symm
        (((weakOreProjection i).app (Opposite.op ⦋0⦌) v).val) := by
  apply (functorVertexEquiv (horn 2 2 : SSet.{u}) B.obj).injective
  rw [(functorVertexEquiv _ _).apply_symm_apply]
  have hr : functorVertex (weakOreSquare i v) =
      ((pullback.fst (pullbackProjection B.obj)
        (weakDenominatorCospanInclusion i)).app (Opposite.op ⦋0⦌) v).val :=
    (functorVertexEquiv _ _).apply_symm_apply _
  change ((pre cospanSquareBoundary).app B.obj).app (Opposite.op ⦋0⦌)
    (functorVertex (weakOreSquare i v)) = _
  rw [hr]
  have hc :
      pullback.fst (pullbackProjection B.obj)
          (weakDenominatorCospanInclusion i) ≫ pullbackProjection B.obj =
        weakOreProjection i ≫ weakDenominatorCospanInclusion i := pullback.condition
  exact congrArg (fun k : weakOreDiagrams i ⟶
      (ihom (horn 2 2 : SSet.{u})).obj B.obj =>
    k.app (Opposite.op ⦋0⦌) v) hc

lemma weakOreSquare_top_mem (v : (weakOreDiagrams i) _⦋0⦌) :
    (squareTopArrow (weakOreSquare i v)).edge ∈ weakEquivalences i := by
  have hv := fullSubcomplexOnVertices_vertex ((weakOreProjection i).app (Opposite.op ⦋0⦌) v)
  change SSet.yonedaEquiv (horn₂₂.ι₁₂ ≫ _) ∈ weakEquivalences i at hv
  rw [← weakOreSquare_cospan, pullbackCospan, ← Category.assoc,
    cospanSquareBoundary_topEdge] at hv
  exact (squareTopArrow_edge (weakOreSquare i v)).symm ▸ hv

lemma weakOreSquare_bottom_mem {C : StableCategory.{u}} {q : ExactMap B C}
    (h : IsVerdierSequence i q) (v : (weakOreDiagrams i) _⦋0⦌) :
    (squareBottomArrow (weakOreSquare i v)).edge ∈ weakEquivalences i :=
  (weakEquivalences_pullback_bottom_top h _ (weakOreSquare_isPullback i v)).mpr
    (weakOreSquare_top_mem i v)

end SerrePositivity.KST.Fibration
