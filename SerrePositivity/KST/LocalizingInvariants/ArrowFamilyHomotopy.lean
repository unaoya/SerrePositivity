module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.ArrowFamilyHomotopy

public import SerrePositivity.KST.LocalizingInvariants.ArrowFamilyRoundTrip

/-!
概要：元の矢印族を、その prism を変えず自然変換として読む。
方針：uncurry と対称性を使い、端点評価と各頂点の辺を照合する。
規約：代表辺を選び直さない。使われ方：cofiber の指定された右辺。
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

lemma arrowFamilyHomotopy_roundTrip {A X : SSet.{u}}
    (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    ZeroArrowFamily.ofHomotopy (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.arrowFamilyHomotopy a) = a :=
  ZeroArrowFamily.ofHomotopy_eq_of_h _ a rfl

lemma arrowFamilyHomotopy_vertex_edge {A X : SSet.{u}}
    (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X) (x : A _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.arrowFamilyHomotopy a) x).edge =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (a.app (Opposite.op ⦋0⦌) x) := by
  conv_rhs => rw [← arrowFamilyHomotopy_roundTrip a]
  rw [ZeroArrowFamily.ofHomotopy, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_curry]
  change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.arrowFamilyHomotopy a).h.app (Opposite.op ⦋1⦌)
    ((Truncated.Edge.id (X := (truncation 2).obj A) x).edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) =
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.arrowFamilyHomotopy a).h.app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1, SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge := by
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> rfl
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one, hi]

end SerrePositivity.KST.LocalizingInvariants
