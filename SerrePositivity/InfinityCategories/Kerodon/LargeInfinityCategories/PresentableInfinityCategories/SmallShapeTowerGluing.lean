module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CofinalSimplexTowerGluing

/-!
概要：元の小さい添字圏内で、前置形状上の全図式列を可算図式へ貼り合わせる。
方針：指定形状同型で全前置標準単体列へ移し、公開 P の貼合入口を使う。
規約：元の小さい宇宙に留まる。使われ方：二つの元の表示内の添字図式の構成。

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

/-- 元の小さい形状列上の全図式は、元の宇宙の可算 nerve 上へ貼り合わさる。 -/
lemma exists_diagram_of_shapeTower {X : SSet.{u}}
    (d : ℕ → ℕ) (hm : Monotone d) (hd : ∀ m, ∃ n, m ≤ d n)
    (K : ℕ → SSet.{u}) (i : ∀ n, K n ⟶ K (n + 1))
    (e : ∀ n, K n ≅ (Δ[d n] : SSet.{u}))
    (he : ∀ n, i n ≫ (e (n + 1)).hom =
      (e n).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefix (hm (Nat.le_succ n)))
    (F : ∀ n, K n ⟶ X) (hf : ∀ n, i n ≫ F (n + 1) = F n) :
    ∃ G : nerve (ULift.{u} ℕ) ⟶ X,
      ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex (d n) ≫ G = (e n).inv ≫ F n := by
  have hi n : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefix (hm (Nat.le_succ n)) ≫ (e (n + 1)).inv =
      (e n).inv ≫ i n := by
    apply (cancel_epi (e n).hom).mp
    rw [← Category.assoc, ← he n, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, Iso.hom_inv_id_assoc]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_sequentialDiagram_of_cofinalSimplices d hm hd (fun n ↦ (e n).inv ≫ F n)
  intro n
  rw [← Category.assoc, hi n, Category.assoc, hf n]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
