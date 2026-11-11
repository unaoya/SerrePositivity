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
variable {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B)

def weakOreSquare (v : (weakOreDiagrams i) _⦋0⦌) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ B.obj :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm
    ((pullback.fst (pullbackProjection B.obj)
      (weakDenominatorCospanInclusion i)).app (Opposite.op ⦋0⦌) v).val

lemma weakOreSquare_isPullback (v : (weakOreDiagrams i) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (weakOreSquare i v) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex ((pullback.fst (pullbackProjection B.obj)
    (weakDenominatorCospanInclusion i)).app (Opposite.op ⦋0⦌) v)

lemma weakOreSquare_cospan (v : (weakOreDiagrams i) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (weakOreSquare i v) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (horn 2 2 : SSet.{u}) B.obj).symm
        (((weakOreProjection i).app (Opposite.op ⦋0⦌) v).val) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (horn 2 2 : SSet.{u}) B.obj).injective
  rw [(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply]
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (weakOreSquare i v) =
      ((pullback.fst (pullbackProjection B.obj)
        (weakDenominatorCospanInclusion i)).app (Opposite.op ⦋0⦌) v).val :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply _
  change ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary).app B.obj).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (weakOreSquare i v)) = _
  rw [hr]
  have hc :
      pullback.fst (pullbackProjection B.obj)
          (weakDenominatorCospanInclusion i) ≫ pullbackProjection B.obj =
        weakOreProjection i ≫ weakDenominatorCospanInclusion i := pullback.condition
  exact congrArg (fun k : weakOreDiagrams i ⟶
      (ihom (horn 2 2 : SSet.{u})).obj B.obj =>
    k.app (Opposite.op ⦋0⦌) v) hc

lemma weakOreSquare_top_mem (v : (weakOreDiagrams i) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopArrow (weakOreSquare i v)).edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i := by
  have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex ((weakOreProjection i).app (Opposite.op ⦋0⦌) v)
  change SSet.yonedaEquiv (horn₂₂.ι₁₂ ≫ _) ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i at hv
  rw [← weakOreSquare_cospan, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_topEdge] at hv
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareTopArrow_edge (weakOreSquare i v)).symm ▸ hv

lemma weakOreSquare_bottom_mem {C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (v : (weakOreDiagrams i) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow (weakOreSquare i v)).edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i :=
  (weakEquivalences_pullback_bottom_top h _ (weakOreSquare_isPullback i v)).mpr
    (weakOreSquare_top_mem i v)

end SerrePositivity.KST.Fibration
