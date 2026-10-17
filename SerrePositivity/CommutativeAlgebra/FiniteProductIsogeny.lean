module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Quotient.Basic

/-! # 有限個の実写像の冪零化指数の合流

各成分の核・余核を消す指数から、元の直積写像の一つの指数を得る。
加群の有限生成性や平坦性は不要。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 有限個の成分ごとの指数を、実直積写像の核・余核の同じ一つの指数へまとめる。 -/
theorem exists_uniform_pow_ker_coker_piMap
    {ι : Type u} [Finite ι] {R : Type u} [CommRing R]
    {M N : ι → Type u} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    (f : ∀ i, M i →ₗ[R] N i) (g : R)
    (h : ∀ i, ∃ n : ℕ,
      (∀ x : (f i).ker, g ^ n • x = 0) ∧
        (∀ y : (N i) ⧸ (f i).range, g ^ n • y = 0)) :
    ∃ n : ℕ, (∀ x : (LinearMap.piMap f).ker, g ^ n • x = 0) ∧
      (∀ y : ((i : ι) → N i) ⧸ (LinearMap.piMap f).range, g ^ n • y = 0) := by
  classical
  letI := Fintype.ofFinite ι
  choose n hn using h
  let k := Finset.univ.sup n
  have hle (i : ι) : n i ≤ k := Finset.le_sup (Finset.mem_univ i)
  have hk (i : ι) (x : (f i).ker) : g ^ k • x = 0 := by
    rw [show k = (k - n i) + n i from (Nat.sub_add_cancel (hle i)).symm,
      pow_add, mul_smul, (hn i).1 x, smul_zero]
  have hc (i : ι) (y : (N i) ⧸ (f i).range) : g ^ k • y = 0 := by
    rw [show k = (k - n i) + n i from (Nat.sub_add_cancel (hle i)).symm,
      pow_add, mul_smul, (hn i).2 y, smul_zero]
  refine ⟨k, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    change g ^ k • (x : (i : ι) → M i) = 0
    ext i
    have hi : f i (x.1 i) = 0 := congrFun x.property i
    exact congrArg Subtype.val (hk i ⟨x.1 i, hi⟩)
  · intro y
    obtain ⟨y, rfl⟩ := (LinearMap.piMap f).range.mkQ_surjective y
    have hm (i : ι) : g ^ k • y i ∈ (f i).range := by
      apply (Submodule.Quotient.mk_eq_zero (f i).range).mp
      exact ((f i).range.mkQ.map_smul (g ^ k) (y i)).trans (hc i _)
    choose x hx using hm
    rw [← map_smul]
    apply (Submodule.Quotient.mk_eq_zero (LinearMap.piMap f).range).mpr
    exact ⟨x, funext hx⟩

end SerrePositivity
