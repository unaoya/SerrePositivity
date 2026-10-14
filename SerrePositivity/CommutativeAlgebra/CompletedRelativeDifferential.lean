module

public import SerrePositivity.CommutativeAlgebra.AdicCompletenessSup
public import SerrePositivity.CommutativeAlgebra.AdicModuleMaps
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.AdicCompletion.Exactness

/-! # 有限型代数の通常の相対微分と完備化

Noether局所環Sの完備イデアルIについて、有限型（より一般にはessentially finite
type）代数S/Rの通常の相対微分はI進完備。係数制限の完備化からの全射と、
通常の微分の推移列の像の閉性も確認する。絶対微分の有限生成性は要求しない。
-/

@[expose] public noncomputable section
namespace SerrePositivity

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.EssFiniteType R S] [IsNoetherianRing S] [IsLocalRing S]
  (I : Ideal S) (hI : I ≤ IsLocalRing.maximalIdeal S) [IsAdicComplete I S]

include hI

/-- 有限型相対微分の有限性はMathlibから、完備性は有限加群の共通APIから供給する。 -/
theorem isAdicComplete_relativeDifferential : IsAdicComplete I (KaehlerDifferential R S) :=
  isAdicComplete_finite_of_ideal_complete I hI (KaehlerDifferential R S)

/-- 通常の相対微分とそのイデアル進完備化の同型。 -/
def relativeDifferentialCompletionEquiv :
    KaehlerDifferential R S ≃ₗ[S] AdicCompletion I (KaehlerDifferential R S) := by
  let : IsAdicComplete I (KaehlerDifferential R S) := isAdicComplete_relativeDifferential I hI
  exact AdicCompletion.ofLinearEquiv I (KaehlerDifferential R S)

@[simp] theorem relativeDifferentialCompletionEquiv_apply (ω : KaehlerDifferential R S) :
    relativeDifferentialCompletionEquiv I hI ω = AdicCompletion.of I (KaehlerDifferential R S) ω :=
  rfl

@[simp] theorem relativeDifferentialCompletionEquiv_symm_of (ω : KaehlerDifferential R S) :
    (relativeDifferentialCompletionEquiv I hI).symm
      (AdicCompletion.of I (KaehlerDifferential R S) ω) = ω :=
  (relativeDifferentialCompletionEquiv I hI).symm_apply_apply ω

variable (k : Type*) [CommRing k] [Algebra k R] [Algebra k S] [IsScalarTower k R S]

/-- 完備化した係数制限を、完備な通常の相対微分に戻す写像。 -/
def completedDifferentialRestriction :
    AdicCompletion I (KaehlerDifferential k S) →ₗ[S] KaehlerDifferential R S :=
  (relativeDifferentialCompletionEquiv I hI).symm.toLinearMap.comp
    ((AdicCompletion.map I (KaehlerDifferential.map k R S S)).restrictScalars S)

@[simp] theorem completedDifferentialRestriction_of (ω : KaehlerDifferential k S) :
    completedDifferentialRestriction I hI k (AdicCompletion.of I (KaehlerDifferential k S) ω) =
      KaehlerDifferential.map k R S S ω := by
  change (relativeDifferentialCompletionEquiv I hI).symm
    (AdicCompletion.map I (KaehlerDifferential.map k R S S)
      (AdicCompletion.of I (KaehlerDifferential k S) ω)) = _
  rw [AdicCompletion.map_of, relativeDifferentialCompletionEquiv_symm_of]

/-- 完備化した元の微分を、相対微分の普遍導分へ送る。 -/
@[simp] theorem completedDifferentialRestriction_D (s : S) :
    completedDifferentialRestriction I hI k
      (AdicCompletion.of I (KaehlerDifferential k S) (KaehlerDifferential.D k S s)) =
        KaehlerDifferential.D R S s := by
  rw [completedDifferentialRestriction_of, KaehlerDifferential.map_D]
  rfl

/-- 係数制限の全射性は完備化でも保たれる。絶対微分の有限性は不要。 -/
theorem completedDifferentialRestriction_surjective :
    Function.Surjective (completedDifferentialRestriction (R := R) I hI k) := by
  exact (relativeDifferentialCompletionEquiv I hI).symm.surjective.comp
    (AdicCompletion.map_surjective I (KaehlerDifferential.map_surjective k R S))

omit [IsAdicComplete I S] in
/-- 通常の推移列の最初の写像の像は、相対微分の分離性により閉。完備性は不要。 -/
theorem isClosed_range_kaehlerMapBaseChange_adic :
    @IsClosed (KaehlerDifferential k S) (I.adicModuleTopology (KaehlerDifferential k S))
      (LinearMap.range (KaehlerDifferential.mapBaseChange k R S) :
        Set (KaehlerDifferential k S)) := by
  let : IsHausdorff I (KaehlerDifferential R S) := IsHausdorff.of_isLocalRing I
    (KaehlerDifferential R S)
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal S).ne_top hI)
  rw [KaehlerDifferential.range_mapBaseChange]
  exact isClosed_ker_linearMap_adic I (KaehlerDifferential.map k R S S)

/-- 完備化後の係数制限の核も閉。通常の像の完備化との一致は別の課題。 -/
theorem isClosed_ker_completedDifferentialRestriction_adic :
    @IsClosed (AdicCompletion I (KaehlerDifferential k S))
      (I.adicModuleTopology (AdicCompletion I (KaehlerDifferential k S)))
      (LinearMap.ker (completedDifferentialRestriction (R := R) I hI k) :
        Set (AdicCompletion I (KaehlerDifferential k S))) := by
  let : IsAdicComplete I (KaehlerDifferential R S) := isAdicComplete_relativeDifferential I hI
  exact isClosed_ker_linearMap_adic I (completedDifferentialRestriction I hI k)

end SerrePositivity
