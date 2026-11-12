module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.UniverseHornDiagramDown
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InvertibleEdge

/-!
概要：元の指定 cocartesian 辺の外側ホーン充填条件は宇宙持ち上げで保存される。
方針：同じ最初の辺を保って図式を戻し、元の充填を同じ形状同型で持ち上げる。
規約：モデル構造も充填性の追加仮定も不要。使われ方：weighted 射影の cocartesian 性の宇宙移送。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories


/-- 元の cocartesian 外側ホーンの充填は、同じ持ち上げた辺について成立する。 -/
lemma hasCocartesianHornLifting_ulift {E B : SSet.{u}} (p : E ⟶ B)
    {x y : E _⦋0⦌} (e : SSet.Truncated.Edge (X := (truncation 2).obj E) x y)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting p e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting ((SSet.uliftFunctor.{v, u}).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u, v} e) := by
  intro n σ β hσ hw
  have hι : (SSet.uliftFunctor.{v, u}).map (horn.{u} (n + 2) 0).ι ≫
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIso.{v, u} ⦋n + 2⦌).hom =
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornIso.{v, u} (n + 2) 0).hom ≫ (horn.{max u v} (n + 2) 0).ι := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  have hι' : (horn.{max u v} (n + 2) 0).ι ≫ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIso.{v, u} ⦋n + 2⦌).inv =
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornIso.{v, u} (n + 2) 0).inv ≫ (SSet.uliftFunctor.{v, u}).map (horn.{u} (n + 2) 0).ι := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.universeHornDiagramDown (n + 2) 0 σ).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge.{u} n) = e.edge :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.universeHornDiagramDown_initialEdge n σ).trans (congrArg ULift.down hσ)
  have hw₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.universeHornDiagramDown (n + 2) 0 σ ≫ p =
      (horn.{u} (n + 2) 0).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.universeSimplexDiagramDown (n + 2) β := by
    apply (SSet.uliftFunctor.{v, u}).map_injective
    rw [CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.universeHornDiagramDown_map,
      CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.universeSimplexDiagramDown_map]
    rw [Category.assoc, hw, ← Category.assoc, ← hι, Category.assoc]
  obtain ⟨φ, hφ, hφp⟩ := he n (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.universeHornDiagramDown (n + 2) 0 σ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.universeSimplexDiagramDown (n + 2) β) hs hw₀
  refine ⟨(_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIso.{v, u} ⦋n + 2⦌).inv ≫ (SSet.uliftFunctor.{v, u}).map φ, ?_, ?_⟩
  · rw [← Category.assoc, hι', Category.assoc, ← CategoryTheory.Functor.map_comp,
      hφ, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.universeHornDiagramDown_map, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  · rw [Category.assoc, ← CategoryTheory.Functor.map_comp, hφp,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.universeSimplexDiagramDown_map, Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
