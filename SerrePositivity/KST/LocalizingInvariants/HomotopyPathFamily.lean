module

public import SerrePositivity.KST.LocalizingInvariants.EquivalencePathFamily

/-!
概要：点ごとに可逆な指定ホモトピーを、同じ円柱を持つ可逆 path の族へ入れる。
方針：curry した頂点成分の辺を元の成分へ照合し、全部分複体に持ち上げる。
規約：端点と境界上の元の円柱を保持する。使われ方：正方形の四辺の指定変形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {A B K X : SSet.{u}} {F G : A ⟶ X} {F' G' : B ⟶ X}

lemma ofHomotopy_component_edge (H : SSet.Homotopy F G) (x : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge ((ZeroArrowFamily.ofHomotopy H).app (Opposite.op ⦋0⦌) x) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).edge := by
  rw [ZeroArrowFamily.ofHomotopy, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_curry]
  change H.h.app (Opposite.op ⦋1⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1, SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) =
      H.h.app (Opposite.op ⦋1⦌)
        ((Truncated.Edge.id (X := (truncation 2).obj A) x).edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge := by
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> rfl
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one, hi]

def homotopyPathFamily (H : SSet.Homotopy F G)
    (hi : ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated) :
    A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex (ZeroArrowFamily.ofHomotopy H) (by
    intro x
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated)
      (ofHomotopy_component_edge H x)).mpr
    exact hi x)

lemma homotopyPathFamily_inclusion (H : SSet.Homotopy F G)
    (hi : ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated) :
    homotopyPathFamily H hi ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X = ZeroArrowFamily.ofHomotopy H :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

lemma homotopyPathFamily_source (H : SSet.Homotopy F G)
    (hi : ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated) :
    homotopyPathFamily H hi ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0 = F := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint, ← Category.assoc, homotopyPathFamily_inclusion]
  exact ZeroArrowFamily.ofHomotopy_source H

lemma homotopyPathFamily_target (H : SSet.Homotopy F G)
    (hi : ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated) :
    homotopyPathFamily H hi ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 1 = G := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint, ← Category.assoc, homotopyPathFamily_inclusion]
  exact ZeroArrowFamily.ofHomotopy_target H

lemma ofHomotopy_restriction_eq (H : SSet.Homotopy F G) (J : SSet.Homotopy F' G')
    (i : K ⟶ A) (j : K ⟶ B)
    (he : (i ▷ (Δ[1] : SSet.{u})) ≫ H.h = (j ▷ (Δ[1] : SSet.{u})) ≫ J.h) :
    i ≫ ZeroArrowFamily.ofHomotopy H = j ≫ ZeroArrowFamily.ofHomotopy J := by
  apply uncurry_injective
  simp only [ZeroArrowFamily.ofHomotopy, uncurry_natural_left, uncurry_curry]
  change (β_ (Δ[1] : SSet.{u}) K).hom ≫ ((i ▷ (Δ[1] : SSet.{u})) ≫ H.h) =
    (β_ (Δ[1] : SSet.{u}) K).hom ≫ ((j ▷ (Δ[1] : SSet.{u})) ≫ J.h)
  rw [he]

end SerrePositivity.KST.LocalizingInvariants
