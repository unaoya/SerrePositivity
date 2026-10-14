module

public import SerrePositivity.BhattScholze.WittDelta
public import SerrePositivity.BhattScholze.PerfectDeltaFrobenius
public import SerrePositivity.CommutativeAlgebra.StrictPRecovery

/-! # 受領F4による完全p進完備δ環のWitt復元

零環を含む復元環同型と標準商図式を、完全δ構造からのp正則性に接続する。
標準Witt δ構造との比較では剰余環のCharPを明示し、零環の一般復元と区別する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 完全p進完備δ環は、零環を含めてそのmod p環のWitt環と同型。 -/
def perfectDeltaWittRecoveryEquiv (D : DeltaStructure p A) (hD : D.IsPerfect)
    [IsAdicComplete (Ideal.span {(p : A)}) A] : WittVector p (ModP A p) ≃+* A := by
  let := hD.perfectRing_mod_p
  exact strictPRecoveryEquiv p A hD.p_mul_injective

/-- 復元同型は標準mod p写像と第0Witt座標を両立させる。 -/
theorem perfectDeltaWittRecoveryEquiv_mod_p (D : DeltaStructure p A) (hD : D.IsPerfect)
    [IsAdicComplete (Ideal.span {(p : A)}) A] :
    (Ideal.Quotient.mk (Ideal.span {(p : A)})).comp
      (perfectDeltaWittRecoveryEquiv D hD).toRingHom = WittVector.constantCoeff := by
  let := hD.perfectRing_mod_p
  exact strictPRecoveryEquiv_mod_p p A hD.p_mul_injective

/-- 標準Witt環からp正則p進完備δ環への任意の環射はδ射。
Witt持上げの一意性を使い、環射の連続性は仮定しない。 -/
theorem wittDeltaStructure_ringHom_isDeltaHom_of_complete
    {k : Type u} [CommRing k] [CharP k p] [PerfectRing k p]
    (D : DeltaStructure p A) [IsAdicComplete (Ideal.span {(p : A)}) A]
    (hp : Function.Injective (fun x : A ↦ (p : A) * x)) (f : WittVector p k →+* A) :
    (wittDeltaStructure p k).IsDeltaHom D f := by
  let W := wittDeltaStructure p k
  let q := Ideal.Quotient.mk (Ideal.span {(p : A)})
  have hqp : q (p : A) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hqfp : (q.comp f) (p : WittVector p k) = 0 := by
    change q (f (p : WittVector p k)) = 0
    rw [map_natCast, hqp]
  have he : f.comp W.frobeniusLift = D.frobeniusLift.comp f := by
    apply wittLift_unique
    apply RingHom.ext
    intro x
    change (q.comp f) (W.frobeniusLift x) = q (D.frobeniusLift (f x))
    rw [W.map_frobeniusLift_of_map_p_eq_zero (q.comp f) hqfp,
      D.map_frobeniusLift_of_map_p_eq_zero q hqp]
    rfl
  exact DeltaStructure.isDeltaHom_of_map_frobeniusLift f hp (RingHom.congr_fun he)

/-- 剰余環が標数pを持つ場合、復元同型の順射は標準Witt δ構造からのδ射。 -/
theorem perfectDeltaWittRecoveryEquiv_isDeltaHom
    (D : DeltaStructure p A) (hD : D.IsPerfect)
    [IsAdicComplete (Ideal.span {(p : A)}) A] [CharP (ModP A p) p] :
    letI := hD.perfectRing_mod_p
    (wittDeltaStructure p (ModP A p)).IsDeltaHom D
      (perfectDeltaWittRecoveryEquiv D hD).toRingHom := by
  let := hD.perfectRing_mod_p
  exact wittDeltaStructure_ringHom_isDeltaHom_of_complete D hD.p_mul_injective _

/-- 標準Witt δ構造との復元同型の逆射もδ射。 -/
theorem perfectDeltaWittRecoveryEquiv_symm_isDeltaHom
    (D : DeltaStructure p A) (hD : D.IsPerfect)
    [IsAdicComplete (Ideal.span {(p : A)}) A] [CharP (ModP A p) p] :
    letI := hD.perfectRing_mod_p
    D.IsDeltaHom (wittDeltaStructure p (ModP A p))
      (perfectDeltaWittRecoveryEquiv D hD).symm.toRingHom := by
  let := hD.perfectRing_mod_p
  exact (perfectDeltaWittRecoveryEquiv_isDeltaHom D hD).symm

end SerrePositivity.BhattScholze
