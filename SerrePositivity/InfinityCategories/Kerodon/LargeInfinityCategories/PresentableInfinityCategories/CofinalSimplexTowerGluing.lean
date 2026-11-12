module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialCofinalStageGluing
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialSimplexPrefix
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialDiagramFiniteStages

/-!
概要：共終な次数の全標準単体列を可算 nerve 上の一つの図式へ貼り合わせる。
方針：有限始区間の標準同型で移送し、共終な部分段階の貼り合わせを使う。
規約：隣接する選択段階の全前置面の等式を要求する。
使われ方：全交互段列の偶数段階をそのまま全可算図式にする。

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

/-- 概要：共終な全前置単体列から全可算図式を構成し、各選択単体を厳密に回収する。
方針：標準単体と有限始区間の全遷移を対応させて貼り合わせる。
規約：頂点列や辺列だけの整合ではない。
使われ方：全交互段の可算貼り合わせ。 -/
lemma exists_sequentialDiagram_of_cofinalSimplices {X : SSet.{u}}
    (d : ℕ → ℕ) (hm : Monotone d) (hd : ∀ m, ∃ n, m ≤ d n)
    (f : ∀ n, (Δ[d n] : SSet.{u}) ⟶ X)
    (hf : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefix (hm (Nat.le_succ n)) ≫ f (n + 1) = f n) :
    ∃ F : nerve (ULift.{u} ℕ) ⟶ X, ∀ n,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex (d n) ≫ F = f n := by
  obtain ⟨F, hF⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_sequentialNerve_map_cofinalStageSteps d hm hd
    (fun n ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStageSimplexIso (d n)).hom ≫ f n) (fun n ↦ by
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStageSimplexIso_prefix (hm (Nat.le_succ n)), Category.assoc, hf n])
  refine ⟨F, fun n ↦ ?_⟩
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex]
  rw [Category.assoc, hF n, Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
