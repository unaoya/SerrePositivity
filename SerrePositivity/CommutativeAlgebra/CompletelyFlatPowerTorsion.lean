module

public import SerrePositivity.CommutativeAlgebra.CompletelyFlat
public import SerrePositivity.CommutativeAlgebra.AdicFaithfulDescentAlgebra
public import SerrePositivity.HomologicalAlgebra.TorDimensionShift
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Quotient

/-! # 完全平坦性と主元の冪で消える加群

aで消える加群の高次Tor消滅を、aNとN/aNの短完全列に沿って
任意のaⁿねじれ加群へ拡張する。aの正則性やNoether性は不要。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
open TensorProduct
open scoped TensorProduct
variable {R : Type u} [CommRing R]

/-- a完全平坦な加群との高次Torは、aの任意の冪で消える試験加群について消える。 -/
theorem torModule_subsingleton_of_completelyFlat_powerTorsion
    (a : R) (M : Type u) [AddCommGroup M] [Module R M]
    (hM : IsCompletelyFlat (Ideal.span {a}) M) :
    ∀ (n : ℕ) (N : Type u) [AddCommGroup N] [Module R N],
      (∀ x : N, a ^ n • x = 0) → ∀ i : ℕ, 0 < i → Subsingleton (TorModule R i M N) := by
  intro n
  induction n with
  | zero =>
    intro N _ _ hN i _
    have hx : ∀ x : N, x = 0 := by simpa only [pow_zero, one_smul] using hN
    have : Subsingleton N := ⟨fun x y ↦ (hx x).trans (hx y).symm⟩
    exact torModule_subsingleton_right_of_subsingleton M N i
  | succ n ih =>
    intro N _ _ hN i hi
    let P : Submodule R N := (a • (LinearMap.id : N →ₗ[R] N)).range
    have hP : ∀ x : P, a ^ n • x = 0 := by
      intro x
      apply Subtype.ext
      obtain ⟨y, hy⟩ := x.property
      change a ^ n • (x : N) = 0
      rw [← hy]
      simpa only [LinearMap.smul_apply, LinearMap.id_apply, ← mul_smul, ← pow_succ] using hN y
    have hQ : ∀ x : N ⧸ P, a • x = 0 := by
      intro x
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        change Submodule.Quotient.mk (a • x) = (0 : N ⧸ P)
        exact (Submodule.Quotient.mk_eq_zero P).mpr ⟨x, rfl⟩
    have hspan : Ideal.span {a} ≤ Module.annihilator R (N ⧸ P) :=
      (Ideal.span_singleton_le_iff_mem _).mpr (Module.mem_annihilator.mpr hQ)
    have hQT := (isConcentratedInDegreeZero_derivedTensor_iff M (N ⧸ P)).mp
      (hM (N ⧸ P) (fun r hr ↦ Module.mem_annihilator.mp (hspan hr))) i hi
    exact torModule_subsingleton_of_exact M P.subtype P.mkQ P.injective_subtype
      P.mkQ_surjective (LinearMap.exact_subtype_mkQ P) i (ih P hP i hi) hQT

/-- 主元aに関する完全平坦性は、全てのaⁿに関する完全平坦性を与える。 -/
theorem isCompletelyFlat_principal_power (a : R) (M : Type u) [AddCommGroup M] [Module R M]
    (hM : IsCompletelyFlat (Ideal.span {a}) M) (n : ℕ) :
    IsCompletelyFlat (Ideal.span {a ^ n}) M := by
  intro N _ _ hN
  apply (isConcentratedInDegreeZero_derivedTensor_iff M N).mpr
  exact torModule_subsingleton_of_completelyFlat_powerTorsion a M hM n N
    (fun x ↦ hN _ (Ideal.subset_span (Set.mem_singleton _)) x)

/-- 完全平坦性の定義から、通常の剰余テンソルの平坦性を得る。
一般のイデアルで成立し、元環上の通常平坦性は仮定しない。 -/
theorem flat_residueTensor_of_completelyFlat (I : Ideal R)
    (M : Type u) [AddCommGroup M] [Module R M] (hM : IsCompletelyFlat I M) :
    Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M) := by
  apply Module.Flat.iff_rTensor_preserves_injective_linearMap.mpr
  intro N N' _ _ _ _ f hf
  let _ : Module R N := Module.compHom N (Ideal.Quotient.mk I)
  let _ : Module R N' := Module.compHom N' (Ideal.Quotient.mk I)
  let _ : IsScalarTower R (R ⧸ I) N := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  let _ : IsScalarTower R (R ⧸ I) N' := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  let Q := N' ⧸ f.range
  let _ : Module R Q := Module.compHom Q (Ideal.Quotient.mk I)
  let _ : IsScalarTower R (R ⧸ I) Q := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  let fR := f.restrictScalars R
  let gR := f.range.mkQ.restrictScalars R
  have hQ : ∀ r ∈ I, ∀ x : Q, r • x = 0 := by
    intro r hr x
    change Ideal.Quotient.mk I r • x = 0
    rw [(Ideal.Quotient.eq_zero_iff_mem).mpr hr, zero_smul]
  have hQT := (isConcentratedInDegreeZero_derivedTensor_iff (R := R) M Q).mp (hM Q hQ) 1 (by omega)
  have he : Function.Exact fR gR := by
    change Function.Exact f f.range.mkQ
    rw [LinearMap.exact_iff, Submodule.ker_mkQ]
  have hl : Function.Injective (fR.lTensor M) :=
    lTensor_injective_of_torModule_one M fR gR hf f.range.mkQ_surjective he hQT
  have hr : Function.Injective (fR.rTensor M) := (fR.lTensor_inj_iff_rTensor_inj M).mp hl
  let e := AlgebraTensorModule.cancelBaseChange R (R ⧸ I) (R ⧸ I) N M
  let e' := AlgebraTensorModule.cancelBaseChange R (R ⧸ I) (R ⧸ I) N' M
  have hn (x : N ⊗[R ⧸ I] ((R ⧸ I) ⊗[R] M)) :
      e' (f.rTensor ((R ⧸ I) ⊗[R] M) x) = fR.rTensor M (e x) := by
    induction x using TensorProduct.inductionOn with
    | tmul x y =>
      induction y using TensorProduct.inductionOn with
      | tmul a m => simp [e, e', AlgebraTensorModule.cancelBaseChange_tmul, fR]
      | add y z hy hz => simp_all only [TensorProduct.tmul_add, map_add]
    | add x y hx hy => simp_all only [map_add]
  intro x y hxy
  apply e.injective
  apply hr
  rw [← hn x, ← hn y, hxy]

/-- a完全平坦性から、各mod aⁿでの通常の平坦性を得る。 -/
theorem flat_power_residueTensor_of_completelyFlat (a : R)
    (M : Type u) [AddCommGroup M] [Module R M]
    (hM : IsCompletelyFlat (Ideal.span {a}) M) (n : ℕ) :
    Module.Flat (R ⧸ Ideal.span {a ^ n}) ((R ⧸ Ideal.span {a ^ n}) ⊗[R] M) :=
  flat_residueTensor_of_completelyFlat _ M (isCompletelyFlat_principal_power a M hM n)

/-- 同じ結果を主イデアルの冪そのもので表す。 -/
theorem isCompletelyFlat_principal_ideal_pow (a : R)
    (M : Type u) [AddCommGroup M] [Module R M]
    (hM : IsCompletelyFlat (Ideal.span {a}) M) (n : ℕ) :
    IsCompletelyFlat ((Ideal.span {a}) ^ n) M := by
  simpa only [Ideal.span_singleton_pow] using isCompletelyFlat_principal_power a M hM n

attribute [local instance] adicQuotientAlgebra

/-- 完全平坦な代数の通常商は、基底の剰余環上平坦である。 -/
theorem flat_algebraQuotient_of_completelyFlat (I : Ideal R)
    (S : Type u) [CommRing S] [Algebra R S] (hS : IsCompletelyFlat I S) :
    Module.Flat (R ⧸ I) (S ⧸ I.map (algebraMap R S)) := by
  have : Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] S) :=
    flat_residueTensor_of_completelyFlat I S hS
  exact Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).toLinearEquiv

/-- a完全平坦な代数は、全てのmod aⁿで平坦な通常の環商を与える。 -/
theorem flat_power_algebraQuotient_of_completelyFlat (a : R)
    (S : Type u) [CommRing S] [Algebra R S]
    (hS : IsCompletelyFlat (Ideal.span {a}) S) (n : ℕ) :
    Module.Flat (R ⧸ Ideal.span {a ^ n})
      (S ⧸ (Ideal.span {a ^ n}).map (algebraMap R S)) :=
  flat_algebraQuotient_of_completelyFlat _ S (isCompletelyFlat_principal_power a S hS n)

end SerrePositivity
