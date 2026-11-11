module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.SpecifiedFunctorEdgeLift
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise

/-!
概要：指定された可逆ホモトピーの単射に沿う延長。
方針：関手単体集合の辺の持ち上げを元のホモトピーへ戻す。
規約：制限の一致はホモトピー類の等式に弱めない。
使われ方：Cat_∞ の錐の指定した比較データの保存。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries

/-- 概要：指定した可逆ホモトピーを終端と単射上の制限を保って持ち上げる。
方針：指定された関手の可逆辺を厳密に持ち上げて uncurry する。
規約：元のホモトピー全体と全頂点での可逆性を保持する。
使われ方：頂点を固定した極限錐の輸送で指定自然変換を追跡する。 -/
lemma exists_mono_homotopy_lift_target {A B X : SSet.{u}} [Quasicategory X]
    (i : A ⟶ B) [Mono i] (f : A ⟶ X) (g : B ⟶ X)
    (H : SSet.Homotopy f (i ≫ g))
    (hH : ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated) :
    ∃ (w : B ⟶ X) (G : SSet.Homotopy w g),
      i ≫ w = f ∧ (i ▷ (Δ[1] : SSet.{u})) ≫ G.h = H.h ∧
      ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge G x).toTruncated := by
  obtain ⟨w, hw, l, hl, hi⟩ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.exists_precomposition_edge_lift i f g
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise H hH)
  let G := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge l
  refine ⟨w, G, hw, ?_, ?_⟩
  · apply curry_injective
    rw [← curry_pre_app]
    change SSet.yonedaEquiv.symm l.edge ≫ (pre i).app X = curry H.h
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact hl
  · intro x
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.simplicialHomotopyOfFunctorEdge_vertex_isInvertible l hi x


end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
