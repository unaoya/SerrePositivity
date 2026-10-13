module

public import SerrePositivity.LengthAlgebra.AlmostVanishing
public import Mathlib.RingTheory.Finiteness.Ideal

/-! # 巡回商の一次評価から冪評価への還元

有限生成イデアル J について、R/(J+I) の長さ零は R/(J^n+I) の長さ零を含意する。
冪で消える有限生成加群を J M と M/J M に分けて帰納する。
環の Noether 性や上限の性質を要求しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.LengthAlgebra
open scoped ENNReal
variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)

/-- 有限生成加群が長さ零の巡回商 R/K の全射像の有限和なら、その長さは零。
加法性を適用するため、巡回商と加群の冪ねじれ性を明示する。 -/
theorem length_eq_zero_of_finite_of_cyclic_quotient (K : Ideal R)
    (hK : IsPowTorsion J (R ⧸ K)) (hzero : lam.len (R ⧸ K) = 0)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : IsPowTorsion J M) (hann : K ≤ Module.annihilator R M) : lam.len M = 0 := by
  let f (x : M) : R ⧸ K →ₗ[R] M :=
    K.liftQ (LinearMap.toSpanSingleton R M x) (fun a ha ↦ by
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      exact Module.mem_annihilator.mp (hann ha) x)
  let V (x : M) := LinearMap.range (f x)
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  have htop : s.sup V = ⊤ := by
    apply top_unique
    rw [← hs]
    apply Submodule.span_le.mpr
    intro x hx
    apply (Finset.le_sup hx : V x ≤ s.sup V)
    refine ⟨Submodule.Quotient.mk 1, ?_⟩
    change (1 : R) • x = x
    exact one_smul R x
  have hle := lam.len_finset_sup_le hM s V
  rw [← Finset.sup_eq_iSup, htop,
    ← lam.len_congr M (⊤ : Submodule R M) Submodule.topEquiv.symm] at hle
  apply le_antisymm _ zero_le
  refine hle.trans (le_of_eq (Finset.sum_eq_zero fun x _ ↦ ?_))
  exact lam.len_range_eq_zero (f x) hK hzero

/-- 一次の巡回商の長さ零から、有限生成の冪ねじれ almost zero 加群の長さ零を導く。
J M の有限生成性だけに J.FG を用いる。 -/
theorem length_eq_zero_of_finite_of_first_cyclic_quotient (I : Ideal R) (hJ : J.FG)
    (hzero : lam.len (R ⧸ (J ⊔ I)) = 0) (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Module.IsTorsionBySet R M (J ^ n : Ideal R))
    (hI : Almost.IsAlmostZero I M) : lam.len M = 0 := by
  induction n generalizing M with
  | zero =>
      have hz (x : M) : x = 0 := by
        simpa using hM (x := x) (a := ⟨1, by simp⟩)
      let : Subsingleton M := ⟨fun x y ↦ (hz x).trans (hz y).symm⟩
      exact lam.len_eq_zero_of_subsingleton M
  | succ n ih =>
      let N : Submodule R M := J • ⊤
      let : Module.Finite R N := Module.Finite.of_fg (Submodule.FG.smul hJ Module.Finite.fg_top)
      have hN : Module.IsTorsionBySet R N (J ^ n : Ideal R) := by
        intro x a
        apply Subtype.ext
        change (a : R) • (x : M) = 0
        refine Submodule.smul_induction_on (p := fun z : M ↦ (a : R) • z = 0) x.2 ?_ ?_
        · intro b hb m _
          rw [← mul_smul]
          exact hM (x := m) (a := ⟨(a : R) * b, by
            rw [pow_succ]
            exact Ideal.mul_mem_mul a.2 hb⟩)
        · intro x y hx hy
          rw [smul_add, hx, hy, add_zero]
      have hQ : Module.IsTorsionBySet R (M ⧸ N) (J ^ 1 : Ideal R) := by
        intro q a
        induction q using Submodule.Quotient.induction_on with
        | _ x =>
          apply (Submodule.Quotient.mk_eq_zero N).mpr
          exact Submodule.smul_mem_smul (by simpa using a.2) (Submodule.mem_top : x ∈ ⊤)
      have hquot : IsPowTorsion J (R ⧸ (J ⊔ I)) := by
        refine ⟨1, ?_⟩
        rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe,
          Ideal.annihilator_quotient, pow_one]
        exact le_sup_left
      have hQann : J ⊔ I ≤ Module.annihilator R (M ⧸ N) := by
        apply sup_le
        · rw [← pow_one J]
          have hh := hQ
          rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe] at hh
          exact hh
        · exact hI.quotient N
      have hNzero := ih N hN (hI.submodule N)
      have hQzero := length_eq_zero_of_finite_of_cyclic_quotient lam (J ⊔ I) hquot hzero
        (M ⧸ N) ⟨1, hQ⟩ hQann
      rw [lam.len_eq_add_quotient ⟨n + 1, hM⟩ N, hNzero, hQzero, add_zero]

/-- 一次の巡回商の長さ零から、全ての冪の巡回商の長さ零を証明する。 -/
theorem cyclic_quotient_pow_length_eq_zero_of_first (I : Ideal R) (hJ : J.FG)
    (hzero : lam.len (R ⧸ (J ⊔ I)) = 0) (n : ℕ) :
    lam.len (R ⧸ (J ^ n ⊔ I)) = 0 := by
  apply length_eq_zero_of_finite_of_first_cyclic_quotient lam I hJ hzero n
  · rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe,
      Ideal.annihilator_quotient]
    exact le_sup_left
  · change I ≤ Module.annihilator R (R ⧸ (J ^ n ⊔ I))
    rw [Ideal.annihilator_quotient]
    exact le_sup_right

end SerrePositivity.LengthAlgebra
