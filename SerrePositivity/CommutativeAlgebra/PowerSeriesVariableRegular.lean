module

public import Mathlib.RingTheory.MvPowerSeries.Ideal
public import Mathlib.RingTheory.Regular.RegularSequence

/-! # 係数の商をとった冪級数環で変数は正則列

## 概要

任意の可換環 `D` と有限生成イデアル `P ⊆ D` について、`D[[Y_1, …, Y_n]] / P D[[Y]]` の上で
変数の列 `Y_1, …, Y_n` は弱正則列である。

## 方針

変数の有限集合 `s` について、`f ∈ P D[[Y]] + (Y_j : j ∈ s)` は
「`s` の変数を含まない単項式の係数がすべて `P` に入る」ことと同値（`mem_map_C_sup_span_X_iff`）。
一方向は右辺がイデアルを定めることから、他方向は `f = Y_j g + h`（`h` は `Y_j` を含まない単項式の部分）
と分けて `s` についての帰納法で示す。`j ∉ s` なら `Y_j f` の係数は `f` の係数をずらしたものなので、
この特徴づけから `Y_j` は商の上で正則。

## 使われ方

`formalization-plans/serre-equal-characteristic.md` の K3。
`D' = R[[Y]] / P R[[Y]]` が `Y_i` を通した `R` 作用で平坦であることを、
局所平坦性判定法（正則列版）から導くのに使う。
-/

@[expose] public section

universe u

open MvPowerSeries

namespace SerrePositivity

variable {D : Type u} [CommRing D] {σ : Type*}

/-- 一つの変数で冪級数を分ける：`f = Y_j g + h`、`h` は `Y_j` を含まない単項式の部分。 -/
theorem exists_X_mul_add_of_coeff (f : MvPowerSeries σ D) (j : σ) :
    ∃ g h : MvPowerSeries σ D, f = X j * g + h ∧
      (∀ α : σ →₀ ℕ, coeff α h = if α j = 0 then coeff α f else 0) ∧
      ∀ β : σ →₀ ℕ, coeff β g = coeff (β + Finsupp.single j 1) f := by
  classical
  let g : MvPowerSeries σ D := fun β ↦ coeff (β + Finsupp.single j 1) f
  let h : MvPowerSeries σ D := fun α ↦ if α j = 0 then coeff α f else 0
  refine ⟨g, h, ?_, fun α ↦ rfl, fun β ↦ rfl⟩
  ext α
  rw [map_add, X_def, coeff_monomial_mul]
  change _ = _ + (if α j = 0 then coeff α f else 0)
  by_cases hα : α j = 0
  · have : ¬ Finsupp.single j 1 ≤ α := by
      intro hle
      have := hle j
      simp [hα] at this
    simp [this, hα]
  · have hle : Finsupp.single j 1 ≤ α := by
      intro i
      by_cases hi : i = j
      · subst hi
        simp only [Finsupp.single_eq_same]
        omega
      · simp [Finsupp.single_eq_of_ne hi]
    simp only [hle, ite_true, one_mul, hα, ite_false, add_zero]
    change coeff α f = coeff (α - Finsupp.single j 1 + Finsupp.single j 1) f
    rw [tsub_add_cancel_of_le hle]

/-- **係数による所属の判定**：`f ∈ P D[[Y]] + (Y_j : j ∈ s)` は、`s` の変数を含まない単項式の
係数がすべて `P` に入ることと同値。 -/
theorem mem_map_C_sup_span_X_iff (P : Ideal D) (hP : P.FG) (s : Finset σ)
    (f : MvPowerSeries σ D) :
    f ∈ P.map C ⊔ Ideal.span (X '' (s : Set σ)) ↔
      ∀ α : σ →₀ ℕ, (∀ j ∈ s, α j = 0) → coeff α f ∈ P := by
  classical
  constructor
  · -- 右辺の条件はイデアルを定める
    let J : Ideal (MvPowerSeries σ D) :=
      { carrier := {f | ∀ α : σ →₀ ℕ, (∀ j ∈ s, α j = 0) → coeff α f ∈ P}
        add_mem' := fun ha hb α hα ↦ by
          rw [map_add]
          exact P.add_mem (ha α hα) (hb α hα)
        zero_mem' := fun α _ ↦ by simp
        smul_mem' := fun c f hf α hα ↦ by
          rw [smul_eq_mul, coeff_mul]
          refine P.sum_mem fun p hp ↦ P.mul_mem_left _ (hf _ fun j hj ↦ ?_)
          have h := hα j hj
          have hle : p.2 ≤ α := by
            rw [← (Finset.mem_antidiagonal.mp hp)]
            exact le_add_left le_rfl
          have := hle j
          omega }
    have hJ : P.map C ⊔ Ideal.span (X '' (s : Set σ)) ≤ J := by
      refine sup_le ?_ ?_
      · intro f hf α _
        exact (mem_map_C_iff_of_fg hP).mp hf α
      · rw [Ideal.span_le]
        rintro _ ⟨j, hj, rfl⟩ α hα
        rw [coeff_X]
        split_ifs with h
        · subst h
          exact absurd (hα j hj) (by simp)
        · exact P.zero_mem
    exact fun hf ↦ hJ hf
  · induction s using Finset.induction_on generalizing f with
    | empty =>
      intro hf
      simp only [Finset.coe_empty, Set.image_empty, Ideal.span_empty, sup_bot_eq]
      exact (mem_map_C_iff_of_fg hP).mpr fun α ↦ hf α (by simp)
    | insert j s hj ih =>
      intro hf
      obtain ⟨g, h, hfgh, hh, -⟩ := exists_X_mul_add_of_coeff f j
      have hhs : h ∈ P.map C ⊔ Ideal.span (X '' (s : Set σ)) := by
        apply ih
        intro α hα
        rw [hh]
        split_ifs with h0
        · exact hf α (by
            intro i hi
            rcases Finset.mem_insert.mp hi with rfl | hi
            · exact h0
            · exact hα i hi)
        · exact P.zero_mem
      have hspan : Ideal.span ((X : σ → MvPowerSeries σ D) '' (s : Set σ)) ≤
          Ideal.span ((X : σ → MvPowerSeries σ D) '' ((insert j s : Finset σ) : Set σ)) :=
        Ideal.span_mono (Set.image_mono (by simp))
      rw [hfgh]
      refine add_mem (Ideal.mem_sup_right (Ideal.mul_mem_right _ _
        (Ideal.subset_span ⟨j, by simp, rfl⟩))) ((sup_le_sup_left hspan _) hhs)

/-- `j ∉ s` なら、`Y_j f ∈ P D[[Y]] + (Y_i : i ∈ s)` から `f` も同じイデアルに入る。 -/
theorem mem_of_X_mul_mem (P : Ideal D) (hP : P.FG) (s : Finset σ) {j : σ} (hj : j ∉ s)
    (f : MvPowerSeries σ D) (h : X j * f ∈ P.map C ⊔ Ideal.span (X '' (s : Set σ))) :
    f ∈ P.map C ⊔ Ideal.span (X '' (s : Set σ)) := by
  classical
  rw [mem_map_C_sup_span_X_iff P hP] at h ⊢
  intro α hα
  have := h (Finsupp.single j 1 + α) (by
    intro i hi
    have hij : j ≠ i := fun e ↦ hj (e ▸ hi)
    simp only [Finsupp.add_apply, Finsupp.single_apply, hij, ite_false, hα i hi, add_zero])
  rwa [X_def, coeff_add_monomial_mul, one_mul] at this

/-- 商加群での所属：`f mod J ∈ I · (S/J)` は `f ∈ I + J` と同値。 -/
theorem Ideal.Quotient.mk_mem_smul_top_iff {S : Type*} [CommRing S] (I J : Ideal S) (f : S) :
    (Ideal.Quotient.mk J f : S ⧸ J) ∈ (I • ⊤ : Submodule S (S ⧸ J)) ↔ f ∈ I ⊔ J := by
  have h : (I • ⊤ : Submodule S (S ⧸ J)) = Submodule.map J.mkQ (I : Submodule S S) := by
    calc (I • ⊤ : Submodule S (S ⧸ J)) = I • Submodule.map J.mkQ ⊤ := by
          rw [Submodule.map_top, Submodule.range_mkQ]
      _ = Submodule.map J.mkQ (I • ⊤) := (Submodule.map_smul'' _ _ _).symm
      _ = Submodule.map J.mkQ (I : Submodule S S) := by
          rw [Ideal.smul_eq_mul, Ideal.mul_top]
  change J.mkQ f ∈ _ ↔ _
  rw [h, ← Submodule.mem_comap, Submodule.comap_map_mkQ, sup_comm]

/-- 変数の列の先頭 `i` 個が生成するイデアル。 -/
theorem ofList_take_ofFn_X {n : ℕ} (i : ℕ) :
    Ideal.ofList ((List.ofFn (X : Fin n → MvPowerSeries (Fin n) D)).take i) =
      Ideal.span (X '' ((Finset.univ.filter fun j : Fin n ↦ (j : ℕ) < i : Finset (Fin n)) :
        Set (Fin n))) := by
  unfold Ideal.ofList
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_image]
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨k, hk, rfl⟩
    simp only [List.length_take, List.length_ofFn, lt_min_iff] at hk
    refine ⟨⟨k, hk.2⟩, hk.1, ?_⟩
    simp
  · rintro ⟨j, hj, rfl⟩
    refine ⟨j, by simp [hj, j.2], ?_⟩
    simp

/-- **冪級数環で変数は正則列**：有限生成イデアル `P ⊆ D` について、`D[[Y]] / P D[[Y]]` の上で
`Y_1, …, Y_n` は弱正則列。 -/
theorem isWeaklyRegular_quotient_map_C_ofFn_X (P : Ideal D) (hP : P.FG) (n : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular (MvPowerSeries (Fin n) D ⧸ P.map C)
      (List.ofFn (X : Fin n → MvPowerSeries (Fin n) D)) := by
  classical
  rw [RingTheory.Sequence.isWeaklyRegular_iff]
  intro i hi
  have hin : i < n := by simpa using hi
  set s : Finset (Fin n) := Finset.univ.filter fun j : Fin n ↦ (j : ℕ) < i
  have hjs : (⟨i, hin⟩ : Fin n) ∉ s := by simp [s]
  rw [ofList_take_ofFn_X, List.getElem_ofFn]
  rw [isSMulRegular_iff_right_eq_zero_of_smul]
  intro z hz
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hz
  rw [Submodule.Quotient.mk_eq_zero, Ideal.Quotient.mk_mem_smul_top_iff, sup_comm]
  apply mem_of_X_mul_mem P hP s hjs
  have : (X ⟨i, hin⟩ : MvPowerSeries (Fin n) D) • Ideal.Quotient.mk (P.map C) f =
      Ideal.Quotient.mk (P.map C) (X ⟨i, hin⟩ * f) := rfl
  rw [this, Ideal.Quotient.mk_mem_smul_top_iff, sup_comm] at hz
  exact hz

/-- 環自身の商での正則性は、イデアルへの所属で言い換えられる。 -/
theorem isSMulRegular_quotient_smul_top_self_iff {S : Type*} [CommRing S] (I : Ideal S) (r : S) :
    IsSMulRegular (S ⧸ (I • ⊤ : Submodule S S)) r ↔ ∀ a : S, r * a ∈ I → a ∈ I := by
  have hI : (I • ⊤ : Submodule S S) = I := by rw [Ideal.smul_eq_mul, Ideal.mul_top]
  rw [isSMulRegular_iff_right_eq_zero_of_smul]
  constructor
  · intro h a ha
    have := h (Submodule.Quotient.mk a) (by
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hI]
      exact ha)
    rwa [Submodule.Quotient.mk_eq_zero, hI] at this
  · intro h z hz
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hI] at hz
    rw [Submodule.Quotient.mk_eq_zero, hI]
    exact h a hz

/-- **定数の正則列**：`R` の弱正則列は、定数として冪級数環 `R[[Y]]` の上でも弱正則列。
有限生成イデアルの拡張への所属は係数ごとの所属なので、各係数で正則性を使う。 -/
theorem isWeaklyRegular_mvPowerSeries_map_C (rs : List D)
    (h : RingTheory.Sequence.IsWeaklyRegular D rs) :
    RingTheory.Sequence.IsWeaklyRegular (MvPowerSeries σ D)
      (rs.map (C : D →+* MvPowerSeries σ D)) := by
  classical
  rw [RingTheory.Sequence.isWeaklyRegular_iff] at h ⊢
  intro i hi
  have hi' : i < rs.length := by simpa using hi
  have hreg := h i hi'
  rw [isSMulRegular_quotient_smul_top_self_iff] at hreg ⊢
  rw [← List.map_take, ← Ideal.map_ofList, List.getElem_map]
  have hfg : (Ideal.ofList (rs.take i)).FG := by
    unfold Ideal.ofList
    exact ⟨(rs.take i).toFinset, by congr 1; ext; simp⟩
  intro a ha
  rw [mem_map_C_iff_of_fg hfg] at ha ⊢
  intro α
  apply hreg
  have := ha α
  rwa [coeff_C_mul] at this

end SerrePositivity
