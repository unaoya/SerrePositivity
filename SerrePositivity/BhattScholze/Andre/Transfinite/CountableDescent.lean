module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.Data.Set.Countable
/-! # 非可算共終性の極限での可算データの降下

BS Thm 7.14（著者版 p.61）の超限反復で使う。原典の一文を補うため、
可算集合の上界という具体的な仮定を明示する。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.Andre.Transfinite
variable {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R : ι → Type u) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)
/-- ## 概要
添字の任意の可算集合が上界を持てば、余極限の可算族を一つの段へ同時に降ろせる。
BS Thm 7.14（著者版 p.61）の非可算共終性の極限段に用いる補助命題。

## 方針
各元の代表段を選び、それらの段全体の可算性から共通上界を取る。

## 規約
環と塔の添字は Type u。可算族の添字の宇宙は任意。遷移写像の単射性は不要。

## 使われ方
Cauchy 列や可算個の係数を一つの完備な段へ降ろす入口となる。
-/
theorem exists_stage_countable_family (hbound : ∀ s : Set ι, s.Countable → ∃ j, ∀ i ∈ s, i ≤ j)
    {κ : Type v} [Countable κ]
    (x : κ → Ring.DirectLimit R (fun i j h ↦ f i j h)) :
    ∃ (i : ι) (y : κ → R i), ∀ k, Ring.DirectLimit.of R (fun i j h ↦ f i j h) i (y k) = x k := by
  classical
  choose i y hy using fun k ↦ Ring.DirectLimit.exists_of (x k)
  obtain ⟨j, hj⟩ := hbound (Set.range i) (Set.countable_range i)
  refine ⟨j, fun k ↦ f (i k) j (hj (i k) ⟨k, rfl⟩) (y k), ?_⟩
  intro k
  rw [Ring.DirectLimit.of_f]
  exact hy k

end SerrePositivity.BhattScholze.Andre.Transfinite
