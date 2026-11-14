module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.UniverseLift
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianEdge

/-!
概要：大きい宇宙のホーン・標準単体の図式を、同じ小さい宇宙の図式へ厳密に戻す。
方針：元の形状の比較同型と ULift の完全忠実性を使う。
規約：最初の辺の値も保持。使われ方：cocartesian 外側ホーン充填の宇宙移送。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories


/-- 同じホーン図式を比較同型で戻し、元の全単体の射として読む。 -/
def universeHornDiagramDown {E : SSet.{u}} (n : ℕ) (i : Fin (n + 1))
    (σ : (horn n i : SSet.{max u v}) ⟶ (SSet.uliftFunctor.{v, u}).obj E) :
    (horn n i : SSet.{u}) ⟶ E :=
  (SSet.uliftFunctor.{v, u}).preimage ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornIso.{v, u} n i).hom ≫ σ)

lemma universeHornDiagramDown_map {E : SSet.{u}} (n : ℕ) (i : Fin (n + 1))
    (σ : (horn n i : SSet.{max u v}) ⟶ (SSet.uliftFunctor.{v, u}).obj E) :
    (SSet.uliftFunctor.{v, u}).map (universeHornDiagramDown n i σ) =
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornIso.{v, u} n i).hom ≫ σ := (SSet.uliftFunctor.{v, u}).map_preimage _

/-- 同じ標準単体の図式を元の宇宙の図式として読む。 -/
def universeSimplexDiagramDown {E : SSet.{u}} (n : ℕ)
    (β : (Δ[n] : SSet.{max u v}) ⟶ (SSet.uliftFunctor.{v, u}).obj E) :
    (Δ[n] : SSet.{u}) ⟶ E :=
  (SSet.uliftFunctor.{v, u}).preimage ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIso.{v, u} ⦋n⦌).hom ≫ β)

lemma universeSimplexDiagramDown_map {E : SSet.{u}} (n : ℕ)
    (β : (Δ[n] : SSet.{max u v}) ⟶ (SSet.uliftFunctor.{v, u}).obj E) :
    (SSet.uliftFunctor.{v, u}).map (universeSimplexDiagramDown n β) =
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIso.{v, u} ⦋n⦌).hom ≫ β := (SSet.uliftFunctor.{v, u}).map_preimage _

/-- 同じ最初の辺の値は、ホーン図式を元の宇宙へ戻しても厳密に保たれる。 -/
lemma universeHornDiagramDown_initialEdge {E : SSet.{u}} (n : ℕ)
    (σ : (horn (n + 2) 0 : SSet.{max u v}) ⟶ (SSet.uliftFunctor.{v, u}).obj E) :
    (universeHornDiagramDown (n + 2) 0 σ).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge.{u} n) =
      (σ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge.{max u v} n)).down := by
  have h := congrArg (fun f => (f.app (Opposite.op ⦋1⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge.{u} n))).down)
    (universeHornDiagramDown_map (n + 2) 0 σ)
  exact h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
