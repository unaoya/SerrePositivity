module

public import SerrePositivity.CommutativeAlgebra.CompletedRelativeDifferential
public import SerrePositivity.CommutativeAlgebra.AdicCompletionKernelClosure

/-! # 完備微分の推移列：像の閉包と核

通常の微分の推移列へ、有限性を要求しない核の近似定理を適用する。
最初の項は通常のテンソル積の完備化であり、テンソル積と完備化を交換しない。
像自体の閉性と、完備した基底微分からのテンソル積との比較は別途必要。
-/

@[expose] public noncomputable section
namespace SerrePositivity

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.EssFiniteType R S] [IsNoetherianRing S] [IsLocalRing S]
  (I : Ideal S) (hI : I ≤ IsLocalRing.maximalIdeal S) [IsAdicComplete I S]
  (k : Type*) [CommRing k] [Algebra k R] [Algebra k S] [IsScalarTower k R S]

/-- 通常の推移列の最初の写像を、テンソル積のS上の完備化へ延長する。 -/
def completedDifferentialBaseChange :
    AdicCompletion I (TensorProduct R S (KaehlerDifferential k R)) →ₗ[S]
      AdicCompletion I (KaehlerDifferential k S) :=
  (AdicCompletion.map I (KaehlerDifferential.mapBaseChange k R S)).restrictScalars S

omit [Algebra.EssFiniteType R S] [IsNoetherianRing S] [IsLocalRing S] [IsAdicComplete I S] in
@[simp] theorem completedDifferentialBaseChange_of
    (ω : TensorProduct R S (KaehlerDifferential k R)) :
    completedDifferentialBaseChange I k (AdicCompletion.of I _ ω) =
      AdicCompletion.of I _ (KaehlerDifferential.mapBaseChange k R S ω) :=
  AdicCompletion.map_of I _ ω

/-- 通常の相対微分への比較同型は核を変えない。 -/
theorem completedDifferentialRestriction_eq_zero_iff
    (x : AdicCompletion I (KaehlerDifferential k S)) :
    completedDifferentialRestriction (R := R) I hI k x = 0 ↔
      AdicCompletion.map I (KaehlerDifferential.map k R S S) x = 0 := by
  constructor
  · intro h
    apply (relativeDifferentialCompletionEquiv (R := R) I hI).symm.injective
    exact h.trans ((relativeDifferentialCompletionEquiv I hI).symm.map_zero).symm
  · intro h
    change (relativeDifferentialCompletionEquiv I hI).symm
      (AdicCompletion.map I (KaehlerDifferential.map k R S S) x) = 0
    rw [h, map_zero]

/-- 完備化した推移列の最初の写像の像の閉包が、係数制限の核と一致する。
絶対微分・中項の有限性は仮定しない。 -/
theorem closure_range_completedDifferentialBaseChange_eq_ker :
    @closure (AdicCompletion I (KaehlerDifferential k S))
      (I.adicModuleTopology (AdicCompletion I (KaehlerDifferential k S)))
      (LinearMap.range (completedDifferentialBaseChange (R := R) I k) :
        Set (AdicCompletion I (KaehlerDifferential k S))) =
      (LinearMap.ker (completedDifferentialRestriction (R := R) I hI k) :
        Set (AdicCompletion I (KaehlerDifferential k S))) := by
  rw [completedDifferentialBaseChange,
    closure_range_adicCompletion_map_eq_ker I I.fg_of_isNoetherianRing
      (KaehlerDifferential.mapBaseChange k R S) (KaehlerDifferential.map k R S S)
      (KaehlerDifferential.exact_mapBaseChange_map k R S)
      (KaehlerDifferential.map_surjective k R S)]
  ext x
  exact (completedDifferentialRestriction_eq_zero_iff I hI k x).symm

/-- 完備絶対微分の有限性を供給すると、閉包を除いて実際の像と核が一致する。
有限性を与える具体的な冪級数・有限代数の証明は、この一般入口と分ける。 -/
theorem range_completedDifferentialBaseChange_eq_ker
    [Module.Finite S (AdicCompletion I (KaehlerDifferential k S))] :
    LinearMap.range (completedDifferentialBaseChange (R := R) I k) =
      LinearMap.ker (completedDifferentialRestriction (R := R) I hI k) := by
  have he := adicCompletion_map_exact_of_finite_completion I
    (hI.trans (IsLocalRing.maximalIdeal_le_jacobson ⊥))
    (KaehlerDifferential.mapBaseChange k R S) (KaehlerDifferential.map k R S S)
    (KaehlerDifferential.exact_mapBaseChange_map k R S)
    (KaehlerDifferential.map_surjective k R S)
  apply Submodule.ext
  intro x
  change x ∈ LinearMap.range
    ((AdicCompletion.map I (KaehlerDifferential.mapBaseChange k R S)).restrictScalars S) ↔ _
  rw [← he.linearMap_ker_eq]
  exact (completedDifferentialRestriction_eq_zero_iff I hI k x).symm

end SerrePositivity
