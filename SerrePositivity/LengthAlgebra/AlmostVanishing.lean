module

public import SerrePositivity.CommutativeAlgebra.Almost.Zero
public import SerrePositivity.PerfectComplex.SupProperty
public import Mathlib.RingTheory.Ideal.Colon

/-!
# almost zero から長さ零への巡回加群への還元

正規化長さが有限生成部分加群の上限で与えられるとき、
`J^n` と `I` が消す加群の長さ零は、巡回加群 `R/(J^n + I)` の長さ零から従う。
加群を各元の生成する巡回部分加群の和として表す。
この還元には Noether 性も almost ideal の冪等性も必要ない。
-/

@[expose] public section
universe u
namespace SerrePositivity.LengthAlgebra

variable {R : Type u} [CommRing R] (I J : Ideal R) (lam : NormalizedLength R J)

/-- 固定した冪で消える almost zero 加群の長さ零を、一つの巡回商の長さ零に還元する。 -/
theorem length_eq_zero_of_cyclic_quotient (hsup : lam.HasSup) (n : ℕ)
    (hcyclic : lam.len (R ⧸ (J ^ n ⊔ I)) = 0)
    (M : Type u) [AddCommGroup M] [Module R M]
    (hM : Module.IsTorsionBySet R M (J ^ n : Ideal R))
    (halmost : Almost.IsAlmostZero I M) : lam.len M = 0 := by
  let K : Ideal R := J ^ n ⊔ I
  have hK : K ≤ Module.annihilator R M := by
    apply sup_le
    · rw [Module.isTorsionBySet_iff_subset_annihilator] at hM
      exact hM
    · exact halmost
  have hquot : IsPowTorsion J (R ⧸ K) := by
    refine ⟨n, ?_⟩
    rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe,
      Ideal.annihilator_quotient]
    exact le_sup_left
  let g : M → (R ⧸ K) →ₗ[R] M := fun x ↦
    K.liftQ (LinearMap.toSpanSingleton R M x) (fun a ha ↦ by
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      exact Module.mem_annihilator.mp (hK ha) x)
  have hzero : ∀ x, lam.len (LinearMap.range (g x)) = 0 := by
    intro x
    exact le_antisymm ((lam.len_range_le (g x) hquot).trans (le_of_eq hcyclic)) zero_le
  have htop : (⨆ x, LinearMap.range (g x)) = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    apply Submodule.mem_iSup_of_mem x
    refine ⟨Submodule.Quotient.mk 1, ?_⟩
    simp only [g, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]
  have he := NormalizedLength.len_iSup_eq_zero hsup ⟨n, hM⟩
    (fun x ↦ LinearMap.range (g x)) hzero
  rw [htop] at he
  exact (lam.len_congr _ _ Submodule.topEquiv.symm).trans he

/-- 各冪に対応する巡回商が長さ零なら、冪ねじれ almost zero 加群はすべて長さ零。 -/
theorem length_eq_zero_of_cyclic_quotients (hsup : lam.HasSup)
    (hcyclic : ∀ n : ℕ, lam.len (R ⧸ (J ^ n ⊔ I)) = 0)
    (M : Type u) [AddCommGroup M] [Module R M]
    (hM : IsPowTorsion J M) (halmost : Almost.IsAlmostZero I M) : lam.len M = 0 := by
  obtain ⟨n, hn⟩ := hM
  exact length_eq_zero_of_cyclic_quotient I J lam hsup n (hcyclic n) M hn halmost

/-- almost zero の長さ消滅は、冪ごとの巡回商での確認と同値。
外部から必要な消滅定理をこの具体的な商の評価に限定できる。 -/
theorem length_eq_zero_for_almost_zero_iff (hsup : lam.HasSup) :
    (∀ (M : Type u) [AddCommGroup M] [Module R M],
      IsPowTorsion J M → Almost.IsAlmostZero I M → lam.len M = 0) ↔
      ∀ n : ℕ, lam.len (R ⧸ (J ^ n ⊔ I)) = 0 := by
  constructor
  · intro h n
    apply h
    · refine ⟨n, ?_⟩
      rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe,
        Ideal.annihilator_quotient]
      exact le_sup_left
    · change I ≤ Module.annihilator R (R ⧸ (J ^ n ⊔ I))
      rw [Ideal.annihilator_quotient]
      exact le_sup_right
  · intro h M _ _ hM halmost
    exact length_eq_zero_of_cyclic_quotients I J lam hsup h M hM halmost

end SerrePositivity.LengthAlgebra
