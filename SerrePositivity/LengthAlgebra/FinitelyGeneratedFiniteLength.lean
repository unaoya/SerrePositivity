module

public import SerrePositivity.PerfectComplex.SupProperty

/-! # 有限生成な冪ねじれ加群の長さの有限性

冪商の長さの有限性を、有限個の巡回像と長さの劣加法性で一般の有限生成加群へ移す。
環のNoether性やHasSupは不要。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.NormalizedLength
variable {R M : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)
    [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- 全ての冪商の長さが有限なら、有限生成な冪ねじれ加群の長さも有限。 -/
theorem len_ne_top_of_finite_of_powQuotient_ne_top
    (hquot : ∀ n : ℕ, lam.len (R ⧸ J ^ n) ≠ ⊤) (hM : IsPowTorsion J M) : lam.len M ≠ ⊤ := by
  obtain ⟨n, hn⟩ := hM
  have hann : J ^ n ≤ Module.annihilator R M := by
    have h := hn
    rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe] at h
    exact h
  have htquot : IsPowTorsion J (R ⧸ J ^ n) := by
    refine ⟨n, ?_⟩
    rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe,
      Ideal.annihilator_quotient]
  let f (x : M) : R ⧸ J ^ n →ₗ[R] M :=
    (J ^ n).liftQ (LinearMap.toSpanSingleton R M x) (fun r hr ↦ by
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      exact Module.mem_annihilator.mp (hann hr) x)
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
  have hle := lam.len_finset_sup_le ⟨n, hn⟩ s V
  rw [← Finset.sup_eq_iSup, htop,
    ← lam.len_congr M (⊤ : Submodule R M) Submodule.topEquiv.symm] at hle
  apply ne_top_of_le_ne_top ?_ hle
  apply ENNReal.sum_ne_top.mpr
  intro x hx
  exact ne_top_of_le_ne_top (hquot n) (lam.len_range_le (f x) htquot)

end SerrePositivity.NormalizedLength
