module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Closure
public import SerrePositivity.CommutativeAlgebra.Almost.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import SerrePositivity.HomologicalAlgebra.QuotientTorOneConormal
public import SerrePositivity.HomologicalAlgebra.DerivedTensorModuleComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.BoundedAboveCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedDiscreteAlgebraMaps

/-! # 完備な almost 拡大閉性

## 概要

導来完備加群の圏での almost 零の拡大閉性 `CompleteIdealExtensionClosed` を定め、conormal 加群 `I/I²` へのスカラーの全射性から全ての冪の商での像の冪等性と拡大閉性を、商の第一 Tor から拡大閉性を、`R/I` の導来自己テンソルの完備化した乗法の同型から拡大閉性と冪等性を導く。

## 方針

conormal のスカラーの全射性は数学的な仮定で、mod aⁿ の像の冪等性からは導かない。

## 規約

旧 `CompleteIdealExtension`・`ConormalIdempotentImage`・`ConormalExtension`・`TorOneCompleteExtension`・`CompletedQuotientTensorExtension`。

## 使われ方

BhattScholze の Almost（BS 著者版 Prop 10.2・Rem 10.7）、`PowerTorsionTor`。
-/

@[expose] public noncomputable section

universe u

section CompleteIdealExtensionPart

namespace SerrePositivity.DerivedCompletion
open CategoryTheory

/-- Extension closure of I-annihilated objects inside actual derived-a-complete modules. -/
def CompleteIdealExtensionClosed (B : Type u) [CommRing B] (a : B) (I : Ideal B) : Prop :=
  ∀ S : ShortComplex (ModuleCat.{u} B), S.ShortExact →
    IsModuleComplete B a S.X₁ → IsModuleComplete B a S.X₂ → IsModuleComplete B a S.X₃ →
    I ≤ Module.annihilator B S.X₁ → I ≤ Module.annihilator B S.X₃ →
      I ≤ Module.annihilator B S.X₂

end SerrePositivity.DerivedCompletion

end CompleteIdealExtensionPart

section ConormalIdempotentImagePart

namespace SerrePositivity
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Divisibility on I/I² supplies idempotence of the actual image of I modulo aⁿ,
including n=0. No completeness, regularity, or Noetherian hypotheses are needed. -/
lemma ideal_mod_power_idempotent_of_conormal_surjective {R : Type u} [CommRing R] (a : R)
    (I : Ideal R)
    (h : Function.Surjective (fun x : I.Cotangent => a • x)) (n : ℕ) :
    IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a ^ n}))) := by
  have hn : Function.Surjective (fun x : I.Cotangent => a ^ n • x) := by
    induction n with
    | zero =>
      intro x
      exact ⟨x, by simp⟩
    | succ n ih =>
      intro x
      obtain ⟨y, hy⟩ := ih x
      obtain ⟨z, hz⟩ := h y
      refine ⟨z, ?_⟩
      change a ^ (n + 1) • z = x
      change a ^ n • y = x at hy
      change a • z = y at hz
      rw [pow_succ, mul_smul, hz, hy]
  let φ := Ideal.Quotient.mk (Ideal.span {a ^ n})
  apply le_antisymm Ideal.mul_le_left
  rw [← Ideal.map_mul, Ideal.map_le_iff_le_comap]
  intro x hx
  obtain ⟨y, hy⟩ := hn (I.toCotangent ⟨x, hx⟩)
  obtain ⟨z, rfl⟩ := I.toCotangent_surjective y
  change a ^ n • I.toCotangent z = I.toCotangent ⟨x, hx⟩ at hy
  have hz : I.toCotangent (⟨x, hx⟩ - a ^ n • z) = 0 := by
    rw [map_sub, map_smul, hy, sub_self]
  have hmem : x - a ^ n * (z : R) ∈ I * I := by
    have hz₂ := (I.toCotangent_eq_zero _).mp hz
    change x - a ^ n * (z : R) ∈ I ^ 2 at hz₂
    simpa only [pow_two] using hz₂
  have hφ : φ (a ^ n) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hm := Ideal.mem_map_of_mem φ hmem
  change φ x ∈ (I * I).map φ
  simpa only [map_sub, map_mul, hφ, zero_mul, sub_zero] using hm

end SerrePositivity

end ConormalIdempotentImagePart

section ConormalExtensionPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable {R : Type u} [CommRing R] (a : R) (I : Ideal R)

/-- If the actual conormal is a-divisible, square annihilation of a derived-complete
module improves to annihilation by I itself. -/
lemma ideal_annihilates_of_square_annihilates_of_conormal_surjective
    (hI : Function.Surjective (fun x : I.Cotangent => a • x))
    (N : ModuleCat.{u} R) (hN : IsModuleComplete R a N)
    (hsq : I ^ 2 ≤ Module.annihilator R N) : I ≤ Module.annihilator R N := by
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  let μ : I →ₗ[R] N := (LinearMap.toSpanSingleton R N x).comp I.subtype
  have hk : (I • (⊤ : Submodule R I)) ≤ μ.ker := by
    intro y hy
    have hyk : y ∈ LinearMap.ker I.toCotangent := by
      change I.toCotangent y = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr hy
    have hy₂ := I.mem_toCotangent_ker.mp hyk
    change (y : R) • x = 0
    exact Module.mem_annihilator.mp (hsq hy₂) x
  let q : I.Cotangent →ₗ[R] N := (I • (⊤ : Submodule R I)).liftQ μ hk
  have hq := linearMap_eq_zero_of_smul_surjective_of_isModuleComplete a
    (ModuleCat.of R I.Cotangent) N hI hN q
  exact congrArg (fun f : I.Cotangent →ₗ[R] N => f (I.toCotangent ⟨r, hr⟩)) hq

/-- The actual conormal criterion supplies the complete extension-closure property. -/
lemma completeIdealExtensionClosed_of_conormal_surjective
    (hI : Function.Surjective (fun x : I.Cotangent => a • x)) :
    CompleteIdealExtensionClosed R a I := by
  intro S hS _ h₂ _ h₁ h₃
  have he : Function.Exact S.f.hom S.g.hom := by
    intro x
    constructor
    · exact (ShortComplex.moduleCat_exact_iff S).mp hS.exact x
    · rintro ⟨y, rfl⟩
      exact congrArg (fun f => f.hom y) S.zero
  have hs : I * I ≤ Module.annihilator R S.X₂ :=
    Almost.IsAlmostZero.of_exact_mul S.f.hom S.g.hom
      he h₁ h₃
  apply ideal_annihilates_of_square_annihilates_of_conormal_surjective a I hI S.X₂ h₂
  simpa only [pow_two] using hs

end SerrePositivity.DerivedCompletion

end ConormalExtensionPart

section TorOneCompleteExtensionPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (a : R) (I : Ideal R)

/-- Only scalar surjectivity on the actual first self-Tor of the quotient is
needed for extension closure. No condition on ordinary mod-aⁿ ideal images is assumed. -/
lemma completeIdealExtensionClosed_of_quotientTorOne_surjective
    (h : Function.Surjective (fun x : TorModule R 1 (R ⧸ I) (R ⧸ I) => a • x)) :
    CompleteIdealExtensionClosed R a I :=
  completeIdealExtensionClosed_of_conormal_surjective a I
    ((quotientTorOne_smul_surjective_iff_conormal R I a).mp h)

end SerrePositivity.DerivedCompletion

end TorOneCompleteExtensionPart

section CompletedQuotientTensorExtensionPart

namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type u} [CommRing R] (a : R) (I : Ideal R)

/-- Inverting the actual derived product after completion makes the original first
quotient self-Tor a-divisible. No vanishing of higher ordinary Tor is assumed. -/
lemma quotientTorOne_smul_surjective_of_completed_mul_isIso
    (hμ : IsIso ((derivedComplexCompletionFunctor R a).map
      (boundedAboveDerivedAlgebraMul (R := R) (R ⧸ I)).hom)) :
    Function.Surjective (fun x : TorModule R 1 (R ⧸ I) (R ⧸ I) => a • x) := by
  have hH : Function.Surjective
      (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) (-1)).obj
        ((boundedAboveDerivedTensorModuleFunctor (ModuleCat.of R (R ⧸ I))).obj
          (ModuleCat.of R (R ⧸ I))) => a • x) := by
    apply boundedAbove_homology_smul_surjective_of_completion_map_isIso R a
      (boundedAboveDerivedAlgebraMul (R := R) (R ⧸ I)) hμ (-1)
    change IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) (-1)).obj
      ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R (R ⧸ I))))
    exact (DerivedCategory.isGE_iff _ 0).mp (inferInstance) (-1) (by omega)
  let e := ((boundedAboveDerivedTensorModuleTorNatIso (ModuleCat.of R (R ⧸ I)) 1).app
    (ModuleCat.of R (R ⧸ I))).toLinearEquiv
  intro x
  obtain ⟨y, hy⟩ := hH (e.symm x)
  refine ⟨e y, ?_⟩
  change a • e y = x
  change a • y = e.symm x at hy
  rw [← e.map_smul, hy, e.apply_symm_apply]

/-- The completed standard quotient product supplies extension closure inside
actual derived-complete modules. -/
lemma completeIdealExtensionClosed_of_completed_quotient_mul_isIso
    (hμ : IsIso ((derivedComplexCompletionFunctor R a).map
      (boundedAboveDerivedAlgebraMul (R := R) (R ⧸ I)).hom)) :
    CompleteIdealExtensionClosed R a I :=
  completeIdealExtensionClosed_of_quotientTorOne_surjective a I
    (quotientTorOne_smul_surjective_of_completed_mul_isIso a I hμ)

/-- The same completed standard product supplies all ordinary power-quotient
idempotence conditions, using the original ideal and quotient map. -/
lemma ideal_mod_power_idempotent_of_completed_quotient_mul_isIso
    (hμ : IsIso ((derivedComplexCompletionFunctor R a).map
      (boundedAboveDerivedAlgebraMul (R := R) (R ⧸ I)).hom)) (n : ℕ) :
    IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a ^ n}))) :=
  ideal_mod_power_idempotent_of_conormal_surjective a I
    ((quotientTorOne_smul_surjective_iff_conormal R I a).mp
      (quotientTorOne_smul_surjective_of_completed_mul_isIso a I hμ)) n

end SerrePositivity.DerivedCompletion

end CompletedQuotientTensorExtensionPart
