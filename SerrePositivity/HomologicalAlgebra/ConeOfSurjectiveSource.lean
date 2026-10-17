module

public import SerrePositivity.HomologicalAlgebra.TwoTermConeAnnihilator

/-! # 全射による始域の変更と実錐の零化

同じ終域への可換三角形を使う。始域の全射の核の零化は不要。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
variable {R L M N : Type u} [CommRing R]
    [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]

/-- 全射な始域変更の下で、元の錐の零射から変更後の錐の零射を得る。
核と余核を各々移すため、スカラーは二乗となる。 -/
theorem moduleMapConeScalar_of_surjective_source
    (t : L →ₗ[R] M) (ht : Function.Surjective t)
    (α : M →ₗ[R] N) (β : L →ₗ[R] N) (hsq : α.comp t = β)
    (g : R) (q : ℕ) (hβ : moduleMapConeScalar R β (g ^ q) = 0) :
    moduleMapConeScalar R α (g ^ (2 * q)) = 0 := by
  obtain ⟨hk, hc⟩ := moduleMapCone_pow_scalar_eq_zero_annihilates R β g q hβ
  have hs (x : L) : α (t x) = β x := LinearMap.congr_fun hsq x
  rw [two_mul, pow_add]
  apply moduleMapConeScalar_eq_zero_of_ker_coker_annihilated R α
  · intro y hy
    obtain ⟨x, rfl⟩ := ht y
    have hx : β x = 0 := (hs x).symm.trans hy
    have he := congrArg (fun z : β.ker => t z) (hk ⟨x, hx⟩)
    simpa only [Submodule.coe_smul, map_smul, Submodule.coe_zero, map_zero] using he
  · intro y
    obtain ⟨y, rfl⟩ := α.range.mkQ_surjective y
    have hm : g ^ q • y ∈ β.range := by
      apply (Submodule.Quotient.mk_eq_zero β.range).mp
      exact (map_smul β.range.mkQ (g ^ q) y).trans (hc _)
    obtain ⟨x, hx⟩ := hm
    rw [← map_smul]
    apply (Submodule.Quotient.mk_eq_zero α.range).mpr
    exact ⟨t x, (hs x).trans hx⟩

end SerrePositivity
