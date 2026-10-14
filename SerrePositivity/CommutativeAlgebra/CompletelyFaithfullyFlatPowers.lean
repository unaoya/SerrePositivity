module

public import SerrePositivity.CommutativeAlgebra.CompletelyFlatPowerTorsion

/-! # 完全忠実平坦性の冪剰余への持ち上げ

mod aでの忠実性を有限のa冪ねじれ加群に沿って持ち上げる。
元環上の通常の忠実平坦性は要求しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits TensorProduct
open scoped TensorProduct
variable {R : Type u} [CommRing R]

/-- 有限冪ねじれ加群では、mod aの零性が元の零性を検出する。
有限生成性に依存しない、冪零作用に対する有限帰納法。 -/
theorem subsingleton_of_principal_power_torsion_of_reduction
    (a : R) (n : ℕ) (N : Type u) [AddCommGroup N] [Module R N]
    (hN : ∀ x : N, a ^ n • x = 0)
    (hQ : Subsingleton (AdicReduction (Ideal.span {a}) N)) : Subsingleton N := by
  let I := Ideal.span {a}
  have htop : I • (⊤ : Submodule R N) = ⊤ := Submodule.Quotient.subsingleton_iff.mp hQ
  have hp : ∀ k : ℕ, I ^ k • (⊤ : Submodule R N) = ⊤ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, Submodule.mul_smul, htop, ih]
  have hann : Ideal.span {a ^ n} ≤ Module.annihilator R N :=
    (Ideal.span_singleton_le_iff_mem _).mpr (Module.mem_annihilator.mpr hN)
  have hbot : I ^ n • (⊤ : Submodule R N) = ⊥ := by
    apply le_antisymm ?_ bot_le
    apply Submodule.smul_le.mpr
    intro r hr x _
    rw [Submodule.mem_bot]
    have hr' : r ∈ Ideal.span {a ^ n} := by simpa only [I, Ideal.span_singleton_pow] using hr
    exact Module.mem_annihilator.mp (hann hr') x
  have htopbot : (⊤ : Submodule R N) = ⊥ := (hp n).symm.trans hbot
  have hz (x : N) : x = 0 := by
    suffices x ∈ (⊥ : Submodule R N) by simpa only [Submodule.mem_bot] using this
    rw [← htopbot]
    trivial
  exact ⟨fun x y ↦ (hz x).trans (hz y).symm⟩

/-- mod aで忠実平坦な通常剰余テンソルは、aⁿねじれ試験加群の零性を検出する。 -/
theorem subsingleton_of_power_torsion_of_residueTensor
    (a : R) (M : Type u) [AddCommGroup M] [Module R M]
    [Module.FaithfullyFlat (R ⧸ Ideal.span {a}) ((R ⧸ Ideal.span {a}) ⊗[R] M)]
    (n : ℕ) (N : Type u) [AddCommGroup N] [Module R N]
    (hN : ∀ x : N, a ^ n • x = 0) (hTensor : Subsingleton (N ⊗[R] M)) : Subsingleton N := by
  let I := Ideal.span {a}
  let P := I • (⊤ : Submodule R N)
  let Q := AdicReduction I N
  have : Subsingleton (N ⊗[R] M) := hTensor
  have hQT : Subsingleton (Q ⊗[R] M) :=
    (LinearMap.rTensor_surjective M P.mkQ_surjective).subsingleton
  have : IsScalarTower R (R ⧸ I) Q := inferInstance
  let e := AlgebraTensorModule.cancelBaseChange R (R ⧸ I) (R ⧸ I) Q M
  have hQA : Subsingleton (Q ⊗[R ⧸ I] ((R ⧸ I) ⊗[R] M)) := e.injective.subsingleton
  have hQ : Subsingleton Q := Module.FaithfullyFlat.rTensor_reflects_triviality
    (R ⧸ I) ((R ⧸ I) ⊗[R] M) Q
  exact subsingleton_of_principal_power_torsion_of_reduction a n N hN hQ

/-- a完全忠実平坦性から、全てのmod aⁿでの通常の忠実平坦性を得る。
n=0では基底と剰余テンソルは零環・零加群であり、同じ型の自明な枝を含む。 -/
theorem faithfullyFlat_power_residueTensor_of_completelyFaithfullyFlat
    (a : R) (M : Type u) [AddCommGroup M] [Module R M]
    (hM : IsCompletelyFaithfullyFlat (Ideal.span {a}) M) (n : ℕ) :
    Module.FaithfullyFlat (R ⧸ Ideal.span {a ^ n}) ((R ⧸ Ideal.span {a ^ n}) ⊗[R] M) := by
  apply (Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality _ _).mpr
  refine ⟨flat_power_residueTensor_of_completelyFlat a M hM.1 n, ?_⟩
  intro N _ _ hTensor
  let I := Ideal.span {a ^ n}
  let _ : Module R N := Module.compHom N (Ideal.Quotient.mk I)
  have : IsScalarTower R (R ⧸ I) N := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  have : Subsingleton (N ⊗[R ⧸ I] ((R ⧸ I) ⊗[R] M)) := hTensor
  let e := AlgebraTensorModule.cancelBaseChange R (R ⧸ I) (R ⧸ I) N M
  have hTN : Subsingleton (N ⊗[R] M) := e.surjective.subsingleton
  have hN : ∀ x : N, a ^ n • x = 0 := by
    intro x
    change Ideal.Quotient.mk I (a ^ n) • x = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)), zero_smul]
  have : Module.FaithfullyFlat (R ⧸ Ideal.span {a}) ((R ⧸ Ideal.span {a}) ⊗[R] M) := hM.2
  exact subsingleton_of_power_torsion_of_residueTensor a M n N hN hTN

/-- 各冪剰余で、底変換後の零射は元の零射を検出する。 -/
theorem power_residue_lTensor_eq_zero_iff
    (a : R) (M : Type u) [AddCommGroup M] [Module R M]
    (hM : IsCompletelyFaithfullyFlat (Ideal.span {a}) M) (n : ℕ)
    {N N' : Type u} [AddCommGroup N] [Module (R ⧸ Ideal.span {a ^ n}) N]
    [AddCommGroup N'] [Module (R ⧸ Ideal.span {a ^ n}) N']
    (f : N →ₗ[R ⧸ Ideal.span {a ^ n}] N') :
    f.lTensor ((R ⧸ Ideal.span {a ^ n}) ⊗[R] M) = 0 ↔ f = 0 := by
  have := faithfullyFlat_power_residueTensor_of_completelyFaithfullyFlat a M hM n
  exact (Module.FaithfullyFlat.zero_iff_lTensor_zero (R := R ⧸ Ideal.span {a ^ n})
    (M := (R ⧸ Ideal.span {a ^ n}) ⊗[R] M) f).symm

/-- 各冪剰余で、底変換後の全射性は元の全射性を検出する。 -/
theorem power_residue_lTensor_surjective_iff
    (a : R) (M : Type u) [AddCommGroup M] [Module R M]
    (hM : IsCompletelyFaithfullyFlat (Ideal.span {a}) M) (n : ℕ)
    {N N' : Type u} [AddCommGroup N] [Module (R ⧸ Ideal.span {a ^ n}) N]
    [AddCommGroup N'] [Module (R ⧸ Ideal.span {a ^ n}) N']
    (f : N →ₗ[R ⧸ Ideal.span {a ^ n}] N') :
    Function.Surjective (f.lTensor ((R ⧸ Ideal.span {a ^ n}) ⊗[R] M)) ↔
      Function.Surjective f := by
  have := faithfullyFlat_power_residueTensor_of_completelyFaithfullyFlat a M hM n
  exact Module.FaithfullyFlat.lTensor_surjective_iff_surjective _ _ f

attribute [local instance] adicQuotientAlgebra

/-- 通常の環商による、各mod aⁿでの忠実平坦性。 -/
theorem faithfullyFlat_power_algebraQuotient_of_completelyFaithfullyFlat
    (a : R) (S : Type u) [CommRing S] [Algebra R S]
    (hS : IsCompletelyFaithfullyFlat (Ideal.span {a}) S) (n : ℕ) :
    Module.FaithfullyFlat (R ⧸ Ideal.span {a ^ n})
      (S ⧸ (Ideal.span {a ^ n}).map (algebraMap R S)) := by
  have := faithfullyFlat_power_residueTensor_of_completelyFaithfullyFlat a S hS n
  exact Module.FaithfullyFlat.of_linearEquiv _ _
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S (Ideal.span {a ^ n})).toLinearEquiv

/-- aⁿねじれ加群に、Mathlib標準の剰余環作用を局所的に与える。 -/
abbrev principalPowerTorsionModule (a : R) (n : ℕ) (N : Type u)
    [AddCommGroup N] [Module R N] (hN : ∀ x : N, a ^ n • x = 0) :
    Module (R ⧸ Ideal.span {a ^ n}) N :=
  (show Module.IsTorsionBy R N (a ^ n) from fun {x} ↦ hN x).module

/-- aⁿねじれ加群間のR線形写像は、標準の剰余環作用に関しても線形。 -/
def principalPowerTorsionLinearMap (a : R) (n : ℕ)
    {N N' : Type u} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (hN : ∀ x : N, a ^ n • x = 0) (hN' : ∀ x : N', a ^ n • x = 0)
    (f : N →ₗ[R] N') :
    let _ := principalPowerTorsionModule a n N hN
    let _ := principalPowerTorsionModule a n N' hN'
    N →ₗ[R ⧸ Ideal.span {a ^ n}] N' := by
  let _ := principalPowerTorsionModule a n N hN
  let _ := principalPowerTorsionModule a n N' hN'
  exact
    { toFun := f
      map_add' := f.map_add
      map_smul' := by
        intro r x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
        change f (r • x) = r • f x
        exact f.map_smul r x }

@[simp] theorem principalPowerTorsionLinearMap_apply (a : R) (n : ℕ)
    {N N' : Type u} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (hN : ∀ x : N, a ^ n • x = 0) (hN' : ∀ x : N', a ^ n • x = 0)
    (f : N →ₗ[R] N') (x : N) : principalPowerTorsionLinearMap a n hN hN' f x = f x := rfl

/-- 標準の剰余環線形化は、元のR線形写像の零性を保存・反映する。 -/
theorem principalPowerTorsionLinearMap_eq_zero_iff (a : R) (n : ℕ)
    {N N' : Type u} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (hN : ∀ x : N, a ^ n • x = 0) (hN' : ∀ x : N', a ^ n • x = 0)
    (f : N →ₗ[R] N') :
    let _ := principalPowerTorsionModule a n N hN
    let _ := principalPowerTorsionModule a n N' hN'
    principalPowerTorsionLinearMap a n hN hN' f = 0 ↔ f = 0 := by
  let _ := principalPowerTorsionModule a n N hN
  let _ := principalPowerTorsionModule a n N' hN'
  constructor
  · intro h
    ext x
    exact congrArg (fun g ↦ g x) h
  · intro h
    ext x
    exact congrArg (fun g ↦ g x) h

/-- aⁿねじれ加群間のR線形写像の、冪剰余での忠実な零性検出。 -/
theorem power_torsion_lTensor_eq_zero_iff
    (a : R) (M : Type u) [AddCommGroup M] [Module R M]
    (hM : IsCompletelyFaithfullyFlat (Ideal.span {a}) M) (n : ℕ)
    {N N' : Type u} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (hN : ∀ x : N, a ^ n • x = 0) (hN' : ∀ x : N', a ^ n • x = 0)
    (f : N →ₗ[R] N') :
    let _ := principalPowerTorsionModule a n N hN
    let _ := principalPowerTorsionModule a n N' hN'
    (principalPowerTorsionLinearMap a n hN hN' f).lTensor
      ((R ⧸ Ideal.span {a ^ n}) ⊗[R] M) = 0 ↔ f = 0 := by
  let _ := principalPowerTorsionModule a n N hN
  let _ := principalPowerTorsionModule a n N' hN'
  exact (power_residue_lTensor_eq_zero_iff a M hM n
    (principalPowerTorsionLinearMap a n hN hN' f)).trans
      (principalPowerTorsionLinearMap_eq_zero_iff a n hN hN' f)

/-- 同じ線形化により、冪剰余での底変換後の全射性も元のR線形写像に反映される。 -/
theorem power_torsion_lTensor_surjective_iff
    (a : R) (M : Type u) [AddCommGroup M] [Module R M]
    (hM : IsCompletelyFaithfullyFlat (Ideal.span {a}) M) (n : ℕ)
    {N N' : Type u} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (hN : ∀ x : N, a ^ n • x = 0) (hN' : ∀ x : N', a ^ n • x = 0)
    (f : N →ₗ[R] N') :
    let _ := principalPowerTorsionModule a n N hN
    let _ := principalPowerTorsionModule a n N' hN'
    Function.Surjective ((principalPowerTorsionLinearMap a n hN hN' f).lTensor
      ((R ⧸ Ideal.span {a ^ n}) ⊗[R] M)) ↔ Function.Surjective f := by
  let _ := principalPowerTorsionModule a n N hN
  let _ := principalPowerTorsionModule a n N' hN'
  exact power_residue_lTensor_surjective_iff a M hM n (principalPowerTorsionLinearMap a n hN hN' f)

end SerrePositivity
