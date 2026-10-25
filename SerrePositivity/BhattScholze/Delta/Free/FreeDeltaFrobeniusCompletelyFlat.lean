module

public import SerrePositivity.BhattScholze.Delta.Free.FreeDeltaFrobeniusModPFlat
public import SerrePositivity.CommutativeAlgebra.CompletelyFlatCriterion

/-! # G3による自由整数δ環Frobeniusのp完全忠実平坦性 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable (p : ℕ) [Fact p.Prime] (σ : Type u)
local notation "A₀" => FreeDeltaRing σ
local notation "Q₀" => ModP A₀ p

/-- 元の環とFrobeniusで作用される終域を区別するための標準ULift。 -/
def FreeDeltaFrobeniusTarget (_p : ℕ) (σ : Type u) := ULift.{0} (FreeDeltaRing σ)

instance freeDeltaFrobeniusTargetCommRing : CommRing (FreeDeltaFrobeniusTarget p σ) := by
  unfold FreeDeltaFrobeniusTarget
  infer_instance

local notation "B₀" => FreeDeltaFrobeniusTarget p σ
local notation "M₀" => FreeDeltaModPFrobeniusTarget p σ

/-- 実Frobeniusによる混標数の係数作用。 -/
abbrev freeDeltaFrobeniusAlgebra : Algebra A₀ B₀ :=
  (((ULift.ringEquiv : B₀ ≃+* A₀).symm.toRingHom).comp (freeDeltaFrobenius p σ)).toAlgebra

attribute [local instance] freeDeltaFrobeniusAlgebra freeDeltaModPFrobeniusAlgebra
attribute [local instance] adicQuotientAlgebra

omit [Fact p.Prime] in
/-- 混標数の係数作用は、元の実Frobeniusそのものである。 -/
theorem freeDeltaFrobeniusAlgebra_algebraMap (x : A₀) :
    (algebraMap A₀ B₀ x).down = freeDeltaFrobenius p σ x := rfl
local notation "I₀" => Ideal.span ({(p : A₀)} : Set A₀)
local notation "J₀" => Ideal.map (algebraMap A₀ B₀) I₀

omit [Fact p.Prime] in
/-- p主イデアルのFrobenius係数作用による拡大は、終域のp主イデアル。 -/
theorem freeDeltaFrobenius_pIdeal_map : J₀ = Ideal.span {(p : B₀)} := by
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

/-- 終域の実p剰余と既存mod p Frobenius終域の環同型。 -/
def freeDeltaFrobeniusResidueEquiv : B₀ ⧸ J₀ ≃+* M₀ :=
  (Ideal.quotEquivOfEq (freeDeltaFrobenius_pIdeal_map p σ)).trans
    ((Ideal.quotientEquiv I₀ (Ideal.span {(p : B₀)})
      (ULift.ringEquiv : B₀ ≃+* A₀).symm
      (by rw [Ideal.map_span, Set.image_singleton, map_natCast])).symm.trans
        (ULift.ringEquiv : M₀ ≃+* Q₀).symm)

omit [Fact p.Prime] in
/-- 剰余比較は元の標準商像をそのまま保つ。 -/
theorem freeDeltaFrobeniusResidueEquiv_mk (x : B₀) :
    freeDeltaFrobeniusResidueEquiv p σ (Ideal.Quotient.mk J₀ x) =
      ULift.up (Ideal.Quotient.mk I₀ x.down) := by
  rw [freeDeltaFrobeniusResidueEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingEquiv.trans_apply, Ideal.quotientEquiv_symm_mk]
  rfl

/-- 商比較は、Frobeniusを持つ正確なA/p作用について線形。 -/
def freeDeltaFrobeniusResidueLinearEquiv : (B₀ ⧸ J₀) ≃ₗ[Q₀] M₀ :=
  { (freeDeltaFrobeniusResidueEquiv p σ).toAddEquiv with
    map_smul' := by
      intro r x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      change freeDeltaFrobeniusResidueEquiv p σ
        (Ideal.Quotient.mk J₀ (algebraMap A₀ B₀ a * b)) =
          ULift.up (Ideal.Quotient.mk I₀ (freeDeltaFrobenius p σ a) *
            Ideal.Quotient.mk I₀ b.down)
      rw [freeDeltaFrobeniusResidueEquiv_mk]
      change ULift.up (Ideal.Quotient.mk I₀ (freeDeltaFrobenius p σ a * b.down)) = _
      rw [map_mul] }

/-- G3の通常商テンソルと既存mod p Frobenius加群との線形同値。 -/
def freeDeltaFrobeniusResidueTensorEquiv : (Q₀ ⊗[A₀] B₀) ≃ₗ[Q₀] M₀ :=
  (quotientTensorReductionEquiv I₀ B₀).trans
    ((adicReductionEquivAlgebraQuotient I₀ B₀).trans (freeDeltaFrobeniusResidueLinearEquiv p σ))

/-- 実Frobeniusで作用される終域のmod pテンソルは忠実平坦。 -/
theorem freeDeltaFrobenius_residueTensor_faithfullyFlat :
    Module.FaithfullyFlat Q₀ (Q₀ ⊗[A₀] B₀) := by
  have := freeDeltaModPFrobenius_moduleFaithfullyFlat p σ
  exact Module.FaithfullyFlat.of_linearEquiv Q₀ M₀ (freeDeltaFrobeniusResidueTensorEquiv p σ)

/-- pは実Frobeniusで作用される終域加群でも正則。 -/
theorem freeDeltaFrobeniusTarget_p_regular : IsSMulRegular B₀ (p : A₀) := by
  intro x y h
  apply ULift.ext
  apply freeDeltaRing_p_mul_injective p σ
  change algebraMap A₀ B₀ (p : A₀) * x = algebraMap A₀ B₀ (p : A₀) * y at h
  rw [map_natCast] at h
  exact congrArg ULift.down h

/-- G3による、自由整数δ環の実Frobeniusのp完全忠実平坦性。 -/
theorem freeDeltaFrobenius_isCompletelyFaithfullyFlat :
    IsCompletelyFaithfullyFlat I₀ B₀ :=
  isCompletelyFaithfullyFlat_principal_of_regular (p : A₀)
    (freeDeltaRing_p_mul_injective p σ) B₀ (freeDeltaFrobeniusTarget_p_regular p σ)
    (freeDeltaFrobenius_residueTensor_faithfullyFlat p σ)

end SerrePositivity.BhattScholze
