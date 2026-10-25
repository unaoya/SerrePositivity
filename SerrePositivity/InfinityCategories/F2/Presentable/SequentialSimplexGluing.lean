module

public import SerrePositivity.InfinityCategories.F2.Presentable.SequentialNerveStageModel
public import SerrePositivity.InfinityCategories.F2.Presentable.SequentialDiagramExtension

/-!
概要：整合する有限全単体列を元の可算鎖の nerve へ貼り合わせる。
方針：有限始区間の標準単体表示で段階の全射を輸送する。
規約：各有限段階の全射への制限が厳密に一致する。
使われ方：交互に選んだ比較辺を coherent な可算図式へ変換する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：最終面で整合する標準単体列は可算 nerve 上の一つの全図式を定める。
方針：標準単体列を始区間へ輸送し、零段階を第一段階からの制限で定める。
規約：全段階の厳密な射の等式を結論する。
使われ方：指定辺列を含む全図式の可算貼り合わせ。 -/
lemma exists_sequentialDiagram_of_simplices {X : SSet.{u}}
    (f : ∀ n, (Δ[n + 1] : SSet.{u}) ⟶ X)
    (hf : ∀ n, SSet.stdSimplex.map (PinchedHom.front (n + 1)) ≫ f (n + 1) = f n) :
    ∃ F : nerve (ULift.{u} ℕ) ⟶ X, ∀ n,
      (sequentialNerveStage (n + 1)).ι ≫ F =
        (sequentialNerveStageSimplexIso (n + 1)).hom ≫ f n := by
  let g : ∀ n, (sequentialNerveStage.{u} n : SSet.{u}) ⟶ X
    | 0 => Subcomplex.homOfLE (sequentialNerveStage_monotone (Nat.le_succ 0)) ≫
        (sequentialNerveStageSimplexIso 1).hom ≫ f 0
    | n + 1 => (sequentialNerveStageSimplexIso (n + 1)).hom ≫ f n
  have hg n : Subcomplex.homOfLE (sequentialNerveStage_monotone (Nat.le_succ n)) ≫
      g (n + 1) = g n := by
    cases n with
    | zero => rfl
    | succ n =>
      change Subcomplex.homOfLE (sequentialNerveStage_monotone (Nat.le_succ (n + 1))) ≫
        ((sequentialNerveStageSimplexIso (n + 2)).hom ≫ f (n + 1)) = _
      rw [← Category.assoc, sequentialNerveStageSimplexIso_transition, Category.assoc, hf n]
  obtain ⟨F, hF⟩ := exists_sequentialDiagram_of_extensions
    (fun n h ↦ h = g n) ⟨g 0, rfl⟩ (by
      intro n h hh
      exact ⟨g (n + 1), rfl, (hg n).trans hh.symm⟩)
  exact ⟨F, fun n ↦ hF (n + 1)⟩

end SerrePositivity.InfinityCategories.F2.Presentable
