module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.OverlapIntervals
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapCoverage

/-!
模型。文献の定義との比較は後で
# 同じ区間から復元した重なる分割の開始位置

Berger–Fresse §1.2.4、M14 L12a。
同じ共有端点と元のstart_nextを使い、構成済み分割のstartを読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C418：同じ共有端点から作った分割の開始位置は元の始点（BF §1.2.4）。 -/
lemma overlapOfIntervals_start {t L : ℕ} (ht : 0 < t) (a b : Fin t → ℕ)
    (hab : ∀ j, a j ≤ b j) (hb : ∀ j, b j < L)
    (hfirst : ∀ j, j.val = 0 → a j = 0)
    (hlast : ∀ j, j.val + 1 = t → b j + 1 = L)
    (hnext : ∀ i j, i.val + 1 = j.val → b i = a j) (j : Fin t) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.overlapOfIntervals ht a b hab hb hfirst hlast hnext).start j = a j := by
  let r := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.overlapOfIntervals ht a b hab hb hfirst hlast hnext
  have hval (x : Fin t) : (r.val x).val = b x - a x + 1 := rfl
  have haux : ∀ i, ∀ hi : i < t, r.start ⟨i, hi⟩ = a ⟨i, hi⟩ := by
    intro i
    induction i with
    | zero =>
      intro hi
      rw [r.start_zero ht]
      exact (hfirst ⟨0, hi⟩ rfl).symm
    | succ i ih =>
      intro hi
      let x : Fin t := ⟨i, by omega⟩
      let y : Fin t := ⟨i + 1, hi⟩
      change r.start y = a y
      rw [r.start_next x y rfl, show r.start x = a x from ih x.isLt, hval]
      have ha := hab x
      have hn := hnext x y rfl
      omega
  exact haux j.val j.isLt

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
