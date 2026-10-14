module

public import SerrePositivity.CommutativeAlgebra.LocalizationPowerBound

/-! # 分母払いによる局所化逆写像の持ち上げ -/

@[expose] public noncomputable section
namespace SerrePositivity
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- 有限自由な始域を持つ局所化上の写像には、共通の分母を払った持ち上げがある。 -/
theorem exists_clear_denominators (g : R) (r : ℕ)
    (u : LocalizedModule (Submonoid.powers g) (Fin r → R) →ₗ[R]
      LocalizedModule (Submonoid.powers g) M) :
    ∃ (k : ℕ) (ψ : (Fin r → R) →ₗ[R] M), awayModuleMap g ψ = g ^ k • u := by
  classical
  let ιM := LocalizedModule.mkLinearMap (Submonoid.powers g) M
  let ιF := LocalizedModule.mkLinearMap (Submonoid.powers g) (Fin r → R)
  let b := Pi.basisFun R (Fin r)
  choose n x hx using fun i : Fin r ↦
    IsLocalizedModule.Away.surj ιM g (u (ιF (b i)))
  let k := Finset.univ.sup n
  let ψ := b.constr R (fun i ↦ g ^ (k - n i) • x i)
  refine ⟨k, ψ, ?_⟩
  apply IsLocalizedModule.ext (Submonoid.powers g) ιF
    (IsLocalizedModule.map_units ιM)
  apply b.ext
  intro i
  change awayModuleMap g ψ (ιF (b i)) = g ^ k • u (ιF (b i))
  rw [show awayModuleMap g ψ (ιF (b i)) = ιM (ψ (b i)) from
    IsLocalizedModule.map_apply _ _ _ _ _]
  rw [show ψ (b i) = g ^ (k - n i) • x i from b.constr_basis R _ i, map_smul, ← hx i]
  have hi : n i ≤ k := Finset.le_sup (Finset.mem_univ i)
  rw [smul_smul, ← pow_add, Nat.sub_add_cancel hi]

/-- 局所化同型の逆写像を、g冪倍して元の加群上へ持ち上げる。 -/
theorem exists_away_inverse (g : R) (r : ℕ) (f : M →ₗ[R] (Fin r → R))
    (hf : Function.Bijective (awayModuleMap g f)) :
    ∃ (k : ℕ) (ψ : (Fin r → R) →ₗ[R] M),
      awayModuleMap g ψ =
        g ^ k • (LinearEquiv.ofBijective (awayModuleMap g f) hf).symm.toLinearMap ∧
      Function.Bijective (awayModuleMap g ψ) := by
  let e := LinearEquiv.ofBijective (awayModuleMap g f) hf
  obtain ⟨k, ψ, hψ⟩ := exists_clear_denominators g r e.symm.toLinearMap
  refine ⟨k, ψ, hψ, ?_⟩
  rw [hψ]
  let ιM := LocalizedModule.mkLinearMap (Submonoid.powers g) M
  have hu := IsLocalizedModule.map_units ιM (⟨g ^ k, k, rfl⟩ : Submonoid.powers g)
  have hb := (Module.End.isUnit_iff _).mp hu
  exact hb.comp e.symm.bijective

end SerrePositivity
