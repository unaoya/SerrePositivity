module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionReflection
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerTower
import all SerrePositivity.CommutativeAlgebra.Koszul.Basic
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerTower

/-!
# 正則なスカラーの冪商と完備化同値

## 概要
各項でスカラーの作用が単射なら、通常の冪商で完備化同値を判定できる。

## 方針
スカラー作用の短完全列に写像錐の比較を適用し、冪ごとに Koszul 商と通常の商を照合する。

## 規約
余鎖複体は整数添字。正則性は環ではなく複体の各項に課す。

## 使われ方
BS 著者版 Theorem 6.4 の完備 de Rham 模型を有限冪商から検証する。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

namespace SerrePositivity.DerivedCompletion

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] (a : R)
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

private theorem powerScalarCokernelShortExact (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : ∀ i, Function.Injective (fun x : K.X i => a • x)) (n : ℕ) :
    (powerScalarCokernelShortComplex a K n).ShortExact := by
  have hm : Mono (smulId (a ^ n) K) := by
    apply mono_of_mono_f
    intro i
    apply (ModuleCat.mono_iff_injective _).mpr
    change Function.Injective (fun x : K.X i => a ^ n • x)
    induction n with
    | zero =>
      simp only [pow_zero, one_smul]
      intro x y h
      exact h
    | succ n ih =>
      simpa only [pow_succ', mul_smul, Function.comp_def] using (hK i).comp ih
  exact { exact := ShortComplex.exact_cokernel _ }

private theorem powerCokernelAugmentation_natural (f : K ⟶ L) (n : ℕ) :
    (scalarConeFunctor (a ^ n)).map f ≫ koszulPowerCokernelAugmentation a L n =
      koszulPowerCokernelAugmentation a K n ≫ powerCokernelMap a f n := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply homotopyCofiber.ext_from_X (smulId (a ^ n) K) (i + 1) i rfl
  · simp only [HomologicalComplex.comp_f, scalarConeFunctor_inl_map_assoc]
    change f.f (i + 1) ≫ (CochainComplex.mappingCone.inl (smulId (a ^ n) L)).v
      (i + 1) i (by simp) ≫ _ =
      (CochainComplex.mappingCone.inl (smulId (a ^ n) K)).v (i + 1) i (by simp) ≫ _ ≫ _
    have hz (M : CochainComplex (ModuleCat.{u} R) ℤ) :
        (CochainComplex.mappingCone.inl (smulId (a ^ n) M)).v (i + 1) i (by simp) ≫
          (koszulPowerCokernelAugmentation a M n).f i = 0 :=
      CochainComplex.mappingCone.inl_v_descShortComplex_f
        (powerScalarCokernelShortComplex a M n) (i + 1) i (by simp)
    rw [hz L, comp_zero, ← Category.assoc, hz K, zero_comp]
  · simp only [HomologicalComplex.comp_f, scalarConeFunctor_inr_map_assoc]
    change f.f i ≫ (CochainComplex.mappingCone.inr (smulId (a ^ n) L)).f i ≫ _ =
      (CochainComplex.mappingCone.inr (smulId (a ^ n) K)).f i ≫ _ ≫ _
    have hπ (M : CochainComplex (ModuleCat.{u} R) ℤ) :
        (CochainComplex.mappingCone.inr (smulId (a ^ n) M)).f i ≫
          (koszulPowerCokernelAugmentation a M n).f i = (cokernel.π (smulId (a ^ n) M)).f i :=
      CochainComplex.mappingCone.inr_f_descShortComplex_f (powerScalarCokernelShortComplex a M n) i
    rw [hπ L, ← Category.assoc, hπ K]
    exact congrArg (fun g => g.f i) (powerCokernelMap_π a f n).symm

/-- 各項で正則なら、通常の冪商の擬同型から完備化の擬同型が従う。 -/
theorem complexCompletionFunctor_map_quasiIso_of_powerCokernel
    (f : K ⟶ L) (hK : ∀ i, Function.Injective (fun x : K.X i => a • x))
    (hL : ∀ i, Function.Injective (fun x : L.X i => a • x))
    (hf : ∀ n, QuasiIso (powerCokernelMap a f n)) :
    QuasiIso ((complexCompletionFunctor R a).map f) := by
  apply complexCompletionFunctor_map_quasiIso_of_koszul R a f
  intro n
  have h₁ : QuasiIso (koszulPowerCokernelAugmentation a K n) :=
    CochainComplex.mappingCone.quasiIso_descShortComplex (powerScalarCokernelShortExact a K hK n)
  have h₂ : QuasiIso (koszulPowerCokernelAugmentation a L n) :=
    CochainComplex.mappingCone.quasiIso_descShortComplex (powerScalarCokernelShortExact a L hL n)
  have := hf n
  have h : QuasiIso ((scalarConeFunctor (a ^ n)).map f ≫
      koszulPowerCokernelAugmentation a L n) := by
    rw [powerCokernelAugmentation_natural]
    infer_instance
  exact quasiIso_of_comp_right _ (koszulPowerCokernelAugmentation a L n)

end SerrePositivity.DerivedCompletion
