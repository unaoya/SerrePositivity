module

public import SerrePositivity.CommutativeAlgebra.PrincipalCoverNumerators
public import SerrePositivity.HomologicalAlgebra.TwoTermConeAnnihilator

/-! # 有限主開被覆からの実錐の冪零化の合流 -/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
set_option backward.isDefEq.respectTransparency false

/-- 有限被覆上の局所錐零化を、既存の加群族の指数合流で元の g へ戻す。
大域的な一つの有限自由比較を要求しない。 -/
theorem moduleMapConeScalar_of_finite_cover
    {R M N : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (g : R) (t : Finset R)
    (hcover : ∃ k : ℕ, g ^ k ∈ Ideal.span (t : Set R))
    (hlocal : ∀ a ∈ t, ∃ q : ℕ, moduleMapConeScalar R f (a ^ q) = 0) :
    ∃ q : ℕ, moduleMapConeScalar R f (g ^ q) = 0 := by
  obtain ⟨q, hq⟩ := exists_uniform_family_pow_smul_zero_of_cover
    (fun _ : Unit => f.ker × (N ⧸ f.range)) g t hcover (by
      intro a ha
      obtain ⟨q, hq⟩ := hlocal a ha
      obtain ⟨hk, hc⟩ := moduleMapCone_pow_scalar_eq_zero_annihilates R f a q hq
      exact ⟨q, fun _ x => Prod.ext (hk x.1) (hc x.2)⟩)
  refine ⟨2 * q, ?_⟩
  rw [two_mul, pow_add]
  apply moduleMapConeScalar_eq_zero_of_ker_coker_annihilated R f
  · intro x hx
    exact congrArg (fun z : f.ker × (N ⧸ f.range) => (z.1 : M))
      (hq () (⟨x, hx⟩, 0))
  · intro y
    exact congrArg Prod.snd (hq () (0, y))

end SerrePositivity
