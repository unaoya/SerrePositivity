module

public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Basic
public import SerrePositivity.CommutativeAlgebra.Adic.Reduction
public import SerrePositivity.HomologicalAlgebra.TorDimensionShift
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # 完全平坦性と冪ねじれ

## 概要

完全平坦な拡大のもとでの冪ねじれ加群の振る舞い：冪ねじれのテンソル積、冪での完全忠実平坦性、テンソル積で閉じること、完全忠実平坦な写像の単射性を与える。

## 方針

冪ねじれは Mathlib の `Module.IsTorsionBy` で書き、Tor の消滅を冪ごとに使う。

## 規約

`CompletelyFlat/Basic` の上に置く。

## 使われ方

BhattScholze の完全忠実平坦な拡大、同種写像の降下。
-/

@[expose] public noncomputable section

universe u

section CompletelyFlatPowerTorsionPart

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

end CompletelyFlatPowerTorsionPart

section CompletelyFaithfullyFlatPowersPart

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

end SerrePositivity

end CompletelyFaithfullyFlatPowersPart

section CompletelyFaithfullyFlatTensorPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits TensorProduct
open scoped TensorProduct
variable {R : Type u} [CommRing R]

/-- Ordinary tensoring reflects zero maps between finite-power-torsion modules. -/
theorem power_torsion_rTensor_eq_zero_iff
    (a : R) (M : Type u) [AddCommGroup M] [Module R M]
    (hM : IsCompletelyFaithfullyFlat (Ideal.span {a}) M) (n : ℕ)
    {N N' : Type u} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (hN : ∀ x : N, a ^ n • x = 0) (hN' : ∀ x : N', a ^ n • x = 0)
    (f : N →ₗ[R] N') : f.rTensor M = 0 ↔ f = 0 := by
  constructor
  · intro hf
    let A := R ⧸ Ideal.span {a ^ n}
    let _ := principalPowerTorsionModule a n N hN
    let _ := principalPowerTorsionModule a n N' hN'
    let fA := principalPowerTorsionLinearMap a n hN hN' f
    have : Module.FaithfullyFlat A (A ⊗[R] M) :=
      faithfullyFlat_power_residueTensor_of_completelyFaithfullyFlat a M hM n
    have hq : fA.rTensor (A ⊗[R] M) = 0 := by
      apply TensorProduct.ext'
      intro x y
      induction y using TensorProduct.inductionOn with
      | tmul r m =>
        apply (AlgebraTensorModule.cancelBaseChange R A A N' M).injective
        simp only [LinearMap.rTensor_tmul, LinearMap.zero_apply,
          map_zero]
        change (r • fA x) ⊗ₜ[R] m = 0
        have hz : fA (r • x) ⊗ₜ[R] m = 0 :=
          congrArg (fun g => g ((r • x) ⊗ₜ[R] m)) hf
        simpa only [fA.map_smul] using hz
      | add y z hy hz =>
        simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hy hz
    have hz := (Module.FaithfullyFlat.zero_iff_rTensor_zero A (A ⊗[R] M) fA).mpr hq
    exact (principalPowerTorsionLinearMap_eq_zero_iff a n hN hN' f).mp hz
  · rintro rfl
    simp

/-- The same reflection in the left tensor convention used by scalar extension. -/
theorem power_torsion_ordinary_lTensor_eq_zero_iff
    (a : R) (M : Type u) [AddCommGroup M] [Module R M]
    (hM : IsCompletelyFaithfullyFlat (Ideal.span {a}) M) (n : ℕ)
    {N N' : Type u} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (hN : ∀ x : N, a ^ n • x = 0) (hN' : ∀ x : N', a ^ n • x = 0)
    (f : N →ₗ[R] N') : f.lTensor M = 0 ↔ f = 0 := by
  constructor
  · intro hf
    apply (power_torsion_rTensor_eq_zero_iff a M hM n hN hN' f).mp
    ext x m
    have hz := congrArg (fun g => (TensorProduct.comm R M N') (g (m ⊗ₜ[R] x))) hf
    simpa using hz
  · rintro rfl
    simp

end SerrePositivity

end CompletelyFaithfullyFlatTensorPart

section CompletelyFaithfullyFlatInjectivePart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
attribute [local instance] adicQuotientAlgebra

/-- A completely faithfully flat map is injective when its original base is adically separated. -/
theorem algebraMap_injective_of_completelyFaithfullyFlat_of_isHausdorff
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (a : R) [IsHausdorff (Ideal.span {a}) R]
    (hS : IsCompletelyFaithfullyFlat (Ideal.span {a}) S) :
    Function.Injective (algebraMap R S) := by
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  apply eq_bot_iff.mpr
  intro x hx
  change x = 0
  change algebraMap R S x = 0 at hx
  apply IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {a}) R) x
  intro n
  let I := Ideal.span {a ^ n}
  let : Module.FaithfullyFlat (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
    faithfullyFlat_power_algebraQuotient_of_completelyFaithfullyFlat a S hS n
  have hi : Function.Injective (algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S))) :=
    FaithfulSMul.algebraMap_injective _ _
  have hm : Ideal.Quotient.mk I x = 0 := by
    apply hi
    rw [map_zero]
    change Ideal.Quotient.mk (I.map (algebraMap R S)) (algebraMap R S x) = 0
    rw [hx, map_zero]
  apply SModEq.zero.mpr
  change x ∈ (Ideal.span {a}) ^ n • (⊤ : Ideal R)
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mp hm

end SerrePositivity

end CompletelyFaithfullyFlatInjectivePart
