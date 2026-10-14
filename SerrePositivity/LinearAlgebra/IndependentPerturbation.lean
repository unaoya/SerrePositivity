module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # 生成集合による独立な摂動

Gabber の微分の選択で用いる一般線形代数。体が無限であるという仮定は不要。
-/

public section
namespace SerrePositivity

/-- 真部分空間の外に、指定ベクトルの生成集合による摂動を選べる。 -/
theorem exists_perturbation_notMem_submodule
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {W : Set V} (hW : Submodule.span K W = ⊤)
    (P : Submodule K V) (hP : P ≠ ⊤) (b : V) :
    ∃ w ∈ insert 0 W, b + w ∉ P := by
  classical
  by_cases hb : b ∈ P
  · have hex : ∃ w ∈ W, w ∉ P := by
      by_contra h
      have hle : Submodule.span K W ≤ P := Submodule.span_le.mpr (by aesop)
      exact hP (top_le_iff.mp (hW ▸ hle))
    obtain ⟨w, hw, hwP⟩ := hex
    refine ⟨w, Set.mem_insert_of_mem _ hw, ?_⟩
    intro hbw
    exact hwP (by simpa using P.sub_mem hbw hb)
  · exact ⟨0, Set.mem_insert _ _, by simpa using hb⟩

/-- 任意の `n` 個のベクトルを、生成集合（または零）からの摂動で独立にできる。
空列・有限体も含む。 -/
theorem exists_linearIndependent_perturbation
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {W : Set V} (hW : Submodule.span K W = ⊤)
    {n : ℕ} (b : Fin n → V) (hn : n ≤ Module.finrank K V) :
    ∃ w : Fin n → V, (∀ i, w i ∈ insert 0 W) ∧
      LinearIndependent K (fun i ↦ b i + w i) := by
  classical
  induction n with
  | zero => exact ⟨Fin.elim0, (fun i ↦ Fin.elim0 i), linearIndependent_empty_type⟩
  | succ n ih =>
    obtain ⟨w, hw, hind⟩ := ih (Fin.tail b) (by omega)
    let v : Fin n → V := fun i ↦ Fin.tail b i + w i
    have hP : Submodule.span K (Set.range v) ≠ ⊤ := by
      intro heq
      have hdim := finrank_le_of_span_eq_top heq
      simp only [Fintype.card_fin] at hdim
      omega
    obtain ⟨x, hx, hxP⟩ := exists_perturbation_notMem_submodule hW _ hP (b 0)
    refine ⟨Fin.cons x w, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simpa using hx
      · simpa using hw j
    · apply linearIndependent_finSucc.mpr
      constructor
      · change LinearIndependent K (fun i ↦ b i.succ + w i)
        exact hind
      · change b 0 + x ∉ Submodule.span K (Set.range v)
        exact hxP

end SerrePositivity
