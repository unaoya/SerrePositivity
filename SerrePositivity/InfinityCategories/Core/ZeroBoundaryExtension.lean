module
public import SerrePositivity.InfinityCategories.Core.InitialExtension
public import SerrePositivity.InfinityCategories.Core.TerminalExtension

/-! # 零対角を含む図式の相対延長
概要：新しい単体の両端のどちらかが普遍的な頂点なら相対延長できる。
方針：相対骨格のセルごとに始対象または終対象で境界を埋める。
規約：単体ごとに使う端点を変えてよい。使われ方：第一行への零対角の追加。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits SSet SSet.relativeCellComplexOfMono
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：新しい単体の始点が始対象、または終点が終対象なら図式を延長できる。
方針：各相対セルの境界を、指定部分で固定された端点の普遍性で充填する。
規約：全頂点を既存部分に含める。周囲の quasicategory 性は不要。
使われ方：BGT Lemma 7.3 の零対角の coherent な補完。 -/
lemma exists_extension_of_initial_or_terminal_endpoints {B X : SSet.{u}}
    (A : B.Subcomplex) (hA : ∀ v : B _⦋0⦌, v ∈ A.obj (Opposite.op ⦋0⦌))
    (a : (A : SSet.{u}) ⟶ X)
    (ht : ∀ (n : ℕ) (s : B _⦋n + 1⦌), s ∉ A.obj (Opposite.op ⦋n + 1⦌) →
      IsInitialVertex (a.app (Opposite.op ⦋0⦌) ⟨simplexFirstVertex s, hA _⟩) ∨
      IsTerminalVertex (a.app (Opposite.op ⦋0⦌) ⟨simplexLastVertex s, hA _⟩)) :
    ∃ F : B ⟶ X, A.ι ≫ F = a := by
  apply exists_extension_of_skeletal_extensions A.ι a
  intro d f hf
  apply exists_extension_skeletonOfMono_succ A.ι d f
  intro c
  cases d with
  | zero =>
    exact False.elim (c.notMem ⟨⟨c.simplex, hA c.simplex⟩, rfl⟩)
  | succ n =>
    rcases ht n c.simplex (fun h ↦ c.notMem ⟨⟨c.simplex, h⟩, rfl⟩) with hi | ht
    · let z : (A : SSet.{u}) _⦋0⦌ := ⟨simplexFirstVertex c.simplex, hA _⟩
      have hterm := hi
      have hb : boundaryVertex n (0) ≫
          (c.ιSigmaBoundary ≫ t A.ι (n + 1)) =
            SSet.yonedaEquiv.symm z ≫ skeletonBase A.ι (n + 1) := by
        apply (cancel_mono (skeletonOfMono A.ι (n + 1)).ι).1
        have hcι : c.ιSigmaBoundary ≫ t A.ι (n + 1) ≫
            (skeletonOfMono A.ι (n + 1)).ι = (boundary (n + 1)).ι ≫ c.map := by
          simp [Cell.ιSigmaBoundary, t]
        simp only [Category.assoc]
        rw [hcι]
        rw [← Category.assoc, boundaryVertex_ι]
        simp only [skeletonBase, Subcomplex.lift_ι,
          SSet.yonedaEquiv_symm_comp]
        rfl
      apply hterm n (c.ιSigmaBoundary ≫ t A.ι (n + 1) ≫ f)
      have hw := congrArg (fun g ↦ g ≫ f) hb
      simp only [Category.assoc] at hw
      rw [hf, SSet.yonedaEquiv_symm_comp] at hw
      simpa only [Category.assoc] using hw
    · let z : (A : SSet.{u}) _⦋0⦌ := ⟨simplexLastVertex c.simplex, hA _⟩
      have hterm := ht
      have hb : boundaryVertex n (Fin.last (n + 1)) ≫
          (c.ιSigmaBoundary ≫ t A.ι (n + 1)) =
            SSet.yonedaEquiv.symm z ≫ skeletonBase A.ι (n + 1) := by
        apply (cancel_mono (skeletonOfMono A.ι (n + 1)).ι).1
        have hcι : c.ιSigmaBoundary ≫ t A.ι (n + 1) ≫
            (skeletonOfMono A.ι (n + 1)).ι = (boundary (n + 1)).ι ≫ c.map := by
          simp [Cell.ιSigmaBoundary, t]
        simp only [Category.assoc]
        rw [hcι]
        rw [← Category.assoc, boundaryVertex_ι]
        simp only [skeletonBase, Subcomplex.lift_ι,
          SSet.yonedaEquiv_symm_comp]
        rfl
      apply hterm n (c.ιSigmaBoundary ≫ t A.ι (n + 1) ≫ f)
      have hw := congrArg (fun g ↦ g ≫ f) hb
      simp only [Category.assoc] at hw
      rw [hf, SSet.yonedaEquiv_symm_comp] at hw
      simpa only [Category.assoc] using hw

end SerrePositivity.InfinityCategories
