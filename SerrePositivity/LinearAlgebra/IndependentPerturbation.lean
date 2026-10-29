module

public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! # 生成集合による独立な摂動

生成集合 `W` の元（または零）を足して、真部分加群を避けたり、有限個のベクトルを独立にしたりする。
Gabber の微分の選択で用いる一般線形代数。
係数体が無限である仮定は不要で、有限体でも成り立つ（足す元を `W ∪ {0}` から選ぶため）。
部分加群の回避は任意の環上の加群で、独立化は除法環上で任意の階数（無限次元を含む）で成り立つ。
Mathlib の `exists_linearIndependent_cons_of_lt_rank`（足す元に制約のない延長）の、生成集合から選ぶ版にあたる。
-/

@[expose] public section
namespace SerrePositivity

/-- 真部分加群 `P` と生成集合 `W` について、`b + w ∉ P` となる `w ∈ W ∪ {0}` がある。 -/
theorem exists_add_notMem_of_span_eq_top {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {W : Set M} (hW : Submodule.span R W = ⊤) (P : Submodule R M) (hP : P ≠ ⊤) (b : M) :
    ∃ w ∈ insert 0 W, b + w ∉ P := by
  by_cases hb : b ∈ P
  · obtain ⟨w, hw, hwP⟩ : ∃ w ∈ W, w ∉ P := by
      by_contra! h
      exact hP (top_le_iff.mp (hW ▸ Submodule.span_le.mpr h))
    exact ⟨w, Set.mem_insert_of_mem _ hw, fun hbw ↦ hwP (by simpa using P.sub_mem hbw hb)⟩
  · exact ⟨0, Set.mem_insert _ _, by simpa using hb⟩

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- `Fin n` で添字づけた場合（`exists_linearIndependent_add_of_span_eq_top` の帰納法の本体）。 -/
private theorem exists_linearIndependent_add_of_span_eq_top_fin
    {W : Set V} (hW : Submodule.span K W = ⊤)
    {n : ℕ} (b : Fin n → V) (hn : (n : Cardinal) ≤ Module.rank K V) :
    ∃ w : Fin n → V, (∀ i, w i ∈ insert 0 W) ∧ LinearIndependent K (fun i ↦ b i + w i) := by
  induction n with
  | zero => exact ⟨Fin.elim0, (fun i ↦ Fin.elim0 i), linearIndependent_empty_type⟩
  | succ n ih =>
    obtain ⟨w, hw, hind⟩ := ih (Fin.tail b) ((Nat.cast_le.mpr n.le_succ).trans hn)
    let v : Fin n → V := fun i ↦ Fin.tail b i + w i
    have hP : Submodule.span K (Set.range v) ≠ ⊤ := by
      intro heq
      have h1 : Module.rank K (Submodule.span K (Set.range v)) ≤ Cardinal.mk (Set.range v) :=
        rank_span_le _
      rw [heq, rank_top] at h1
      have h2 : Cardinal.mk (Set.range v) ≤ n := by
        simpa using Cardinal.mk_range_le_lift (f := v)
      exact absurd (Nat.cast_le.mp (hn.trans (h1.trans h2))) (by omega)
    obtain ⟨x, hx, hxP⟩ := exists_add_notMem_of_span_eq_top hW _ hP (b 0)
    refine ⟨Fin.cons x w, Fin.cases (by simpa using hx) (fun j ↦ by simpa using hw j), ?_⟩
    exact linearIndependent_finSucc.mpr ⟨hind, hxP⟩

/-- 有限個のベクトルの族は、個数が階数以下なら、生成集合（または零）の元を足して独立にできる。
空の族・有限体・無限次元の空間も含む。 -/
theorem exists_linearIndependent_add_of_span_eq_top {ι : Type*} [Finite ι]
    {W : Set V} (hW : Submodule.span K W = ⊤)
    (b : ι → V) (hn : (Nat.card ι : Cardinal) ≤ Module.rank K V) :
    ∃ w : ι → V, (∀ i, w i ∈ insert 0 W) ∧ LinearIndependent K (fun i ↦ b i + w i) := by
  let e := Finite.equivFin ι
  obtain ⟨w, hw, hind⟩ := exists_linearIndependent_add_of_span_eq_top_fin hW (b ∘ e.symm) hn
  refine ⟨w ∘ e, fun i ↦ hw (e i), ?_⟩
  simpa [Function.comp_def] using hind.comp e e.injective

end SerrePositivity
