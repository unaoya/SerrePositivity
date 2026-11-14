module

public import SerrePositivity.BhattScholze.PerfectoidIdeal.Roots
public import SerrePositivity.BhattScholze.Semiperfectoid.Surjectivity.Surjectivity
public import SerrePositivity.BhattScholze.Perfectoidization.CompletedTensor
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.KoszulModel
public import SerrePositivity.HomologicalAlgebra.Koszul.ParameterAnnihilators
public import SerrePositivity.BhattScholze.Almost.Lemma103
public import SerrePositivity.BhattScholze.Almost.PerfectoidAlmost

/-! # perfectoid イデアルによる商の完備な積と Tor の入力の移送

## 概要

主イデアル商の選んだ perfectoid 化への写像が全射であること（`perfectoidIdeal_quotientMap_surjective`）、perfectoid イデアルによる商の完備化した積の写像が同型であること（`perfectoidIdeal_completedQuotientMul_map_isIso`）、完備な almost 零加群が拡大で閉じることを示す。perfectoid イデアルの Tor の入力が、almost 比較のどちらの向きでも変わらないこと、像のイデアルでの言い換えも与える。
BS 著者版 Lemma 10.3 の積の計算を、単項商の完備テンソルと Tor の入力に使う。

## 方針

B4 の一般の全射性と、商が integral perfectoid であること（`perfectoidIdeal_quotient_isIntegralPerfectoid`、`Almost/Lemma103`）から、完備な積の同型と拡大閉性を得る。mod pᴺ の像の冪等性は `perfectoidIdealMod_idempotent`（`Almost/PerfectoidAlmost`）を使う。

## 規約

`Almost/Lemma103` の `perfectoidIdeal_completedQuotientMul_map_isIso` は、この写像に標準の単位同型を合成したものの同型性。旧 `CLMST/PerfectoidIdealCompletedMul`・`PerfectoidIdealTorTransport`。CLMST にあった重複（商の perfectoid 性、mod pᴺ の冪等性）は削除した。

## 使われ方

`Perfectoidization/ExcisionTor`、CLMST の KL 比較と Prop 4.0.10。
-/

@[expose] public noncomputable section

universe u

section PerfectoidIdealCompletedMulPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.SerrePositivity.DerivedCompletion _root_.SerrePositivity.BhattScholze
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R)

/-- The original selected perfectoidization of the principal quotient is surjective. -/
lemma perfectoidIdeal_quotientMap_surjective :
    Function.Surjective (_root_.SerrePositivity.BhattScholze.Semiperfectoid.toQuotientPerfectoidization R (Ideal.span {g}) p hR) :=
  _root_.SerrePositivity.BhattScholze.Semiperfectoid.surjective_of_isPerfectoidization_of_semiperfectoid_quotient hR
    (Ideal.Quotient.mk (Ideal.span {g})) Ideal.Quotient.mk_surjective
    (isModuleComplete_principal_quotient_natCast R p g (hR.isModuleComplete R p))
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.toQuotientPerfectoidization R (Ideal.span {g}) p hR)
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.isPerfectoidization_toQuotientPerfectoidization R (Ideal.span {g}) p hR)

/-- The original completed quotient product for the actual CLMST perfectoid ideal is invertible. -/
lemma perfectoidIdeal_completedQuotientMul_map_isIso :
    IsIso ((derivedComplexCompletionFunctor R (p : R)).map
      (boundedAboveDerivedAlgebraMul (R := R) (R ⧸ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g)).hom) :=
  integralPerfectoid_completedQuotientMul_isIso p R (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g) hR
    (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_quotient_isIntegralPerfectoid R p hR g)

/-- The complete almost-zero modules for the actual ideal are extension closed. -/
lemma perfectoidIdeal_completeIdealExtensionClosed :
    CompleteIdealExtensionClosed R (p : R) (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g) :=
  integralPerfectoid_completeIdealExtensionClosed p R (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g) hR
    (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_quotient_isIntegralPerfectoid R p hR g)

end SerrePositivity.BhattScholze

end PerfectoidIdealCompletedMulPart

section PerfectoidIdealTorTransportPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R)
    (C D : Type u) [CommRing C] [CommRing D] [Algebra R C] [Algebra R D]

/-- The full original power-torsion Tor input is invariant under an actual almost
comparison. All test modules, exponents, positive degrees, and original scalars are retained. -/
theorem perfectoidIdeal_powerTorsionTorInput_iff_of_almost_comparison
    (f : C →ₗ[R] D)
    (hk : ∀ a ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g, ∀ x : f.ker, a • x = 0)
    (hc : ∀ b ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g, ∀ y : D ⧸ f.range, b • y = 0) :
    (∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
      ∀ i : ℕ, 0 < i → ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g,
        torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0) ↔
    (∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
      ∀ i : ℕ, 0 < i → ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g,
        torCoefficientScalarEndomorphism D N i (algebraMap R D s) = 0) := by
  constructor
  · intro h N k hN i hi
    exact (torCoefficientIdeal_eq_zero_iff_of_almost_comparison f
      (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g) hk hc N ((p : R) ^ k) hN
      (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod_idempotent R p hR g k) i).mp (h N k hN i hi)
  · intro h N k hN i hi
    exact (torCoefficientIdeal_eq_zero_iff_of_almost_comparison f
      (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g) hk hc N ((p : R) ^ k) hN
      (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod_idempotent R p hR g k) i).mpr (h N k hN i hi)

/-- A reverse finite free almost comparison supplies the original full Tor input,
without assuming an almost inverse is represented by one fixed module map. -/
theorem perfectoidIdeal_powerTorsionTorInput_of_reverse_finiteFree_comparison
    (r : ℕ) (f : (Fin r → R) →ₗ[R] C)
    (hk : ∀ a ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g, ∀ x : f.ker, a • x = 0)
    (hc : ∀ b ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g, ∀ y : C ⧸ f.range, b • y = 0) :
    ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
      ∀ i : ℕ, 0 < i → ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g,
        torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 := by
  intro N k hN i hi s hs
  exact torCoefficientScalar_eq_zero_of_reverse_finiteFree_almost_comparison r f
    (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g) hk hc N ((p : R) ^ k) hN
    (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod_idempotent R p hR g k) i hi s hs

end SerrePositivity.BhattScholze

end PerfectoidIdealTorTransportPart
