module

public import SerrePositivity.BhattScholze.FreeDeltaModP
public import SerrePositivity.BhattScholze.PrimePolynomialFrobeniusFlat
public import SerrePositivity.CommutativeAlgebra.PerfectoidUntiltNaturality

/-! # B4-6：自由整数δ環の実際のmod p Frobeniusの自由性

標準商同型と素数体の単項式基底を半線形同値で接続する。
混標数Frobeniusの完全平坦性をこの結果だけから推論しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (σ : Type u)
attribute [local instance] polynomialExpandAlgebra

/-- 自由δ環の剰余環にFrobenius作用を持たせるための標準ULift型。 -/
def FreeDeltaModPFrobeniusTarget := ULift.{0} (ModP (FreeDeltaRing σ) p)

instance freeDeltaModPFrobeniusTargetCommRing : CommRing (FreeDeltaModPFrobeniusTarget p σ) := by
  unfold FreeDeltaModPFrobeniusTarget
  infer_instance

/-- 自由δ環の実際の剰余Frobeniusによるスカラー作用。 -/
abbrev freeDeltaModPFrobeniusAlgebra : Algebra (ModP (FreeDeltaRing σ) p)
    (FreeDeltaModPFrobeniusTarget p σ) :=
  (((ULift.ringEquiv : FreeDeltaModPFrobeniusTarget p σ ≃+*
    ModP (FreeDeltaRing σ) p).symm.toRingHom).comp (modPMap p (freeDeltaFrobenius p σ))).toAlgebra

attribute [local instance] freeDeltaModPFrobeniusAlgebra

/-- 標準商同型は、実際の剰余Frobeniusを素数体のexpand射へ移す。 -/
theorem freeDeltaModPEquiv_modPMap_frobenius (a : ModP (FreeDeltaRing σ) p) :
    freeDeltaModPEquiv p σ (modPMap p (freeDeltaFrobenius p σ) a) =
      MvPolynomial.expand p (freeDeltaModPEquiv p σ a) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  change freeDeltaModPEquiv p σ (Ideal.Quotient.mk _ (freeDeltaFrobenius p σ x)) = _
  rw [freeDeltaModPEquiv_frobenius_mk]
  exact RingHom.congr_fun (primePolynomial_frobenius_eq_expand p (σ × ℕ)) _

/-- 標準商同型の順逆環射のMathlib逆対。 -/
abbrev freeDeltaModPInvPair :
    RingHomInvPair (freeDeltaModPEquiv p σ).toRingHom
      (freeDeltaModPEquiv p σ).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (freeDeltaModPEquiv p σ)

/-- 標準商同型の逆順環射のMathlib逆対。 -/
abbrev freeDeltaModPSymmInvPair :
    RingHomInvPair (freeDeltaModPEquiv p σ).symm.toRingHom
      (freeDeltaModPEquiv p σ).toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (freeDeltaModPEquiv p σ)

attribute [local instance] freeDeltaModPInvPair freeDeltaModPSymmInvPair

/-- 実際の剰余Frobenius作用と、素数体上のexpand作用を結ぶ半線形同値。 -/
def freeDeltaModPFrobeniusEquiv :
    LinearEquiv (σ' := (freeDeltaModPEquiv p σ).symm.toRingHom)
      (freeDeltaModPEquiv p σ).toRingHom (FreeDeltaModPFrobeniusTarget p σ)
        (PolynomialExpandTarget p (σ × ℕ) (ZMod p)) where
  toFun x := ULift.up (freeDeltaModPEquiv p σ x.down)
  invFun x := ULift.up ((freeDeltaModPEquiv p σ).symm x.down)
  left_inv x := by
    apply ULift.ext
    exact (freeDeltaModPEquiv p σ).symm_apply_apply x.down
  right_inv x := by
    apply ULift.ext
    exact (freeDeltaModPEquiv p σ).apply_symm_apply x.down
  map_add' x y := by
    change ULift.up (freeDeltaModPEquiv p σ (x.down + y.down)) =
      ULift.up (freeDeltaModPEquiv p σ x.down + freeDeltaModPEquiv p σ y.down)
    rw [map_add]
  map_smul' a x := by
    change ULift.up (freeDeltaModPEquiv p σ
      (modPMap p (freeDeltaFrobenius p σ) a * x.down)) =
        ULift.up (MvPolynomial.expand p (freeDeltaModPEquiv p σ a) *
          freeDeltaModPEquiv p σ x.down)
    rw [map_mul, freeDeltaModPEquiv_modPMap_frobenius]

/-- 自由δ環の実際のmod p Frobenius作用の剰余環は自由加群。 -/
theorem freeDeltaModPFrobenius_moduleFree :
    Module.Free (ModP (FreeDeltaRing σ) p) (FreeDeltaModPFrobeniusTarget p σ) := by
  let := polynomialExpand_moduleFree p (σ × ℕ) (ZMod p) (Fact.out : p.Prime).pos
  exact Module.Free.of_equiv (freeDeltaModPFrobeniusEquiv p σ).symm

/-- 自由δ環の実際のmod p Frobenius作用の剰余環は忠実平坦。 -/
theorem freeDeltaModPFrobenius_moduleFaithfullyFlat :
    Module.FaithfullyFlat (ModP (FreeDeltaRing σ) p) (FreeDeltaModPFrobeniusTarget p σ) := by
  let : Nontrivial (ModP (FreeDeltaRing σ) p) :=
    (freeDeltaModPEquiv p σ).toRingHom.domain_nontrivial
  let : Nontrivial (FreeDeltaModPFrobeniusTarget p σ) := by
    unfold FreeDeltaModPFrobeniusTarget
    infer_instance
  let := freeDeltaModPFrobenius_moduleFree p σ
  infer_instance

end SerrePositivity.BhattScholze
