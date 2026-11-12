module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialEdgeSimplices
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialSimplexGluing

/-!
概要：任意の指定可算辺列を可算鎖の nerve 上の一つの全図式として実現する。
方針：指定辺を保つ全単体列を選び、有限始区間から貼り合わせる。
規約：辺のホモトピー類ではなく指定された一単体射を厳密に保持する。
使われ方：compact 表示の交互列を coherent な図式として実現する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：可算鎖の n 番目から n+1 番目への辺の全単体表示。
方針：有限始区間の最後の辺を元の nerve へ含める。
規約：最初の辺だけは標準一単体そのもの。
使われ方：指定辺を保つ可算図式の公開条件。 -/
def sequentialNerveSuccessorEdge : ∀ _ : ℕ, (Δ[1] : SSet.{u}) ⟶ nerve (ULift.{u} ℕ)
  | 0 => (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStageSimplexIso 1).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage 1).ι
  | n + 1 => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}) Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1).hom) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStageSimplexIso (n + 2)).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage (n + 2)).ι

/-- 概要：指定した有限始区間の辺は元の自然数の隣接辺そのもの。
方針：一単体を表す二頂点の関手を計算する。
規約：元の nerve の一単体の厳密な等式。
使われ方：余極限の部分列比較へ接続する。 -/
lemma sequentialNerveSuccessorEdge_simplex (n : ℕ) :
    SSet.yonedaEquiv (sequentialNerveSuccessorEdge.{u} n) =
      (nerve.edgeMk (homOfLE (show (ULift.up n : ULift.{u} ℕ) ≤ ULift.up (n + 1) from
        Nat.le_succ n))).edge := by
  cases n with
  | zero =>
    refine ComposableArrows.ext (fun i ↦ ?_) (fun _ _ ↦ Subsingleton.elim _ _)
    fin_cases i <;> rfl
  | succ n =>
    refine ComposableArrows.ext (fun i ↦ ?_) (fun _ _ ↦ Subsingleton.elim _ _)
    fin_cases i <;> rfl

/-- 概要：任意の指定可算辺列を含む元の可算 nerve 上の全図式が存在する。
方針：指定辺を保つ全有限単体を貼り合わせ、各最後の辺への制限を回収する。
規約：標的の quasicategory 性だけを使い、余極限や filtered 性を仮定しない。
使われ方：交互に選んだ比較辺の列に全ての高次整合を付ける。 -/
lemma exists_sequentialDiagram_realizing_edges {X : SSet.{u}} [Quasicategory X]
    (x : ℕ → X _⦋0⦌) (e : ∀ n, X.Edge (x n) (x (n + 1))) :
    ∃ F : nerve (ULift.{u} ℕ) ⟶ X, ∀ n,
      sequentialNerveSuccessorEdge n ≫ F = SSet.yonedaEquiv.symm (e n).edge := by
  obtain ⟨f, hzero, hf, _, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_sequentialEdgeSimplices x e
  obtain ⟨F, hF⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_sequentialDiagram_of_simplices f hf
  refine ⟨F, fun n ↦ ?_⟩
  cases n with
  | zero =>
    simp only [sequentialNerveSuccessorEdge, Category.assoc, hF,
      Iso.inv_hom_id_assoc, hzero]
  | succ n =>
    simp only [sequentialNerveSuccessorEdge, Category.assoc, hF, Iso.inv_hom_id_assoc]
    exact he n

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
