module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! # 二つのεを消す順序の交換と有限和の相殺

最初の消去位置iと、消去後の位置jを、反対の順序の二つの位置へ移す。
固定点のない対合で相殺するため、標数2でも加法群の追加仮定を必要としない。
実際のpath cochainへの適用には、対応する二つの項が互いに負になることの証明が必要。
-/
@[expose] public section
namespace SerrePositivity.DifferentialGraded.DGQuotient

/-- 二回の消去順序を交換する。第二添字は最初の消去後の語で数える。 -/
def swapErasure (p : ℕ × ℕ) : ℕ × ℕ :=
  if p.2 < p.1 then (p.2, p.1 - 1) else (p.2 + 1, p.1)

lemma swapErasure_involutive (p : ℕ × ℕ) : swapErasure (swapErasure p) = p := by
  rcases p with ⟨i, j⟩
  by_cases h : j < i
  · have hs : swapErasure (i, j) = (j, i - 1) := ite_eq_left h
    have hs' : swapErasure (j, i - 1) = (i - 1 + 1, j) :=
      ite_eq_right (by omega)
    rw [hs, hs']
    exact Prod.ext (by omega) rfl
  · have hs : swapErasure (i, j) = (j + 1, i) := ite_eq_right h
    have hs' : swapErasure (j + 1, i) = (i, j + 1 - 1) := ite_eq_left (by omega)
    rw [hs, hs']
    exact Prod.ext rfl (by omega)

lemma swapErasure_ne (p : ℕ × ℕ) : swapErasure p ≠ p := by
  rcases p with ⟨i, j⟩
  unfold swapErasure
  split_ifs <;> simp_all only [ne_eq, Prod.mk.injEq] <;> omega

lemma swapErasure_mem {n : ℕ} {p : ℕ × ℕ}
    (h : p ∈ (Finset.range n).product (Finset.range (n - 1))) :
    swapErasure p ∈ (Finset.range n).product (Finset.range (n - 1)) := by
  rcases p with ⟨i, j⟩
  have hi : i < n := Finset.mem_range.mp (Finset.mem_product.mp h).1
  have hj : j < n - 1 := Finset.mem_range.mp (Finset.mem_product.mp h).2
  by_cases hij : j < i
  · have hs : swapErasure (i, j) = (j, i - 1) := ite_eq_left hij
    rw [hs]
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
      Finset.mem_range.mpr (by omega)⟩
  · have hs : swapErasure (i, j) = (j + 1, i) := ite_eq_right hij
    rw [hs]
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
      Finset.mem_range.mpr (by omega)⟩

/-- 二重消去の項が順序交換で負になるなら、有限二重和は零。 -/
lemma erasure_double_sum_cancel {G : Type*} [AddCommGroup G] (n : ℕ) (f : ℕ → ℕ → G)
    (h : ∀ i < n, ∀ j < n - 1,
      f i j = -f (swapErasure (i, j)).1 (swapErasure (i, j)).2) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (n - 1), f i j = 0 := by
  rw [← Finset.sum_product' (Finset.range n) (Finset.range (n - 1)) f]
  apply Finset.sum_involution (fun p _ => swapErasure p)
  · intro p hp
    have hp' := hp
    simp only [Finset.mem_product, Finset.mem_range] at hp'
    exact eq_neg_iff_add_eq_zero.mp (h p.1 hp'.1 p.2 hp'.2)
  · intro p _ _
    exact swapErasure_ne p
  · intro p hp
    exact swapErasure_mem hp
  · intro p _
    exact swapErasure_involutive p

end SerrePositivity.DifferentialGraded.DGQuotient
