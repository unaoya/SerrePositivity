module

public import SerrePositivity.LengthAlgebra.AlmostVanishing
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # almost zero な核を持つ巡回商間の長さ比較

イデアルの包含による商の全射を直接扱う。核のalmost零性はイデアルの積の包含で
確認でき、テンソル積を新たに構成せずに巡回商の帰着を行える。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.LengthAlgebra
variable {R : Type u} [CommRing R]

/-- イデアルの積の包含は、商間の自然な全射の核のalmost零性を与える。 -/
theorem quotientFactorKernel_isAlmostZero_of_mul_le (I H L : Ideal R) (hIH : I ≤ H)
    (hLH : L * H ≤ I) :
    Almost.IsAlmostZero L (LinearMap.ker (Ideal.Quotient.factorₐ R hIH).toLinearMap) := by
  intro a ha
  apply Module.mem_annihilator.mpr
  intro x
  apply Subtype.ext
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (x : R ⧸ I)
  have hbH : b ∈ H := by
    have hx := x.property
    rw [LinearMap.mem_ker] at hx
    rw [← hb] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mp hx
  change a • (x : R ⧸ I) = 0
  rw [← hb]
  change Ideal.Quotient.mk I (a * b) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hLH (Ideal.mul_mem_mul ha hbH))

/-- 核がalmost zeroで、対応する巡回商が全て長さ零なら、商間で長さは一致する。 -/
theorem length_quotient_eq_of_factor_kernel_almost_zero
    {J : Ideal R} (lam : NormalizedLength R J) (hsup : lam.HasSup)
    (L I H : Ideal R) (hIH : I ≤ H) (hI : IsPowTorsion J (R ⧸ I))
    (hL : ∀ n : ℕ, lam.len (R ⧸ (J ^ n ⊔ L)) = 0)
    (hker : Almost.IsAlmostZero L
      (LinearMap.ker (Ideal.Quotient.factorₐ R hIH).toLinearMap)) :
    lam.len (R ⧸ I) = lam.len (R ⧸ H) := by
  let f := (Ideal.Quotient.factorₐ R hIH).toLinearMap
  have hk := length_eq_zero_of_cyclic_quotients L J lam hsup hL
    (LinearMap.ker f) (hI.submodule (LinearMap.ker f)) hker
  rw [lam.len_eq_add_ker_range f hI, hk, zero_add,
    LinearMap.range_eq_top.mpr (Ideal.Quotient.factor_surjective hIH)]
  exact lam.len_congr _ _ Submodule.topEquiv

/-- 関係式J^nを加えた後の核のalmost零性は、L H⊆J^n+Iという弱い包含で十分。 -/
theorem length_quotient_sup_eq_of_almost_factor
    {J : Ideal R} (lam : NormalizedLength R J) (hsup : lam.HasSup)
    (L I H : Ideal R) (hIH : I ≤ H) (n : ℕ) (hLH : L * H ≤ J ^ n ⊔ I)
    (hL : ∀ a : ℕ, lam.len (R ⧸ (J ^ a ⊔ L)) = 0) :
    lam.len (R ⧸ (J ^ n ⊔ I)) = lam.len (R ⧸ (J ^ n ⊔ H)) := by
  have hquot : J ^ n ⊔ I ≤ J ^ n ⊔ H := sup_le_sup_left hIH _
  have hprod : L * (J ^ n ⊔ H) ≤ J ^ n ⊔ I := by
    rw [Ideal.mul_sup]
    exact sup_le (Ideal.mul_le_right.trans le_sup_left) hLH
  have htor : IsPowTorsion J (R ⧸ (J ^ n ⊔ I)) := by
    refine ⟨n, ?_⟩
    rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe,
      Ideal.annihilator_quotient]
    exact le_sup_left
  exact length_quotient_eq_of_factor_kernel_almost_zero lam hsup L _ _ hquot htor hL
    (quotientFactorKernel_isAlmostZero_of_mul_le _ _ _ hquot hprod)

end SerrePositivity.LengthAlgebra
