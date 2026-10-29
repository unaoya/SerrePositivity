-- lake build の後、lake env lean scripts/audit_f4.lean で実行する。
import SerrePositivity.CommutativeAlgebra.Witt.Lift
import Mathlib.Util.AssertNoSorry

open SerrePositivity
universe u

-- BS F4の正確な署名。剰余環のCharP、非零性、非単元性は仮定しない。
theorem f4_audit_bs_signature (A : Type u) [CommRing A] (p : ℕ) [Fact p.Prime]
    [IsAdicComplete (Ideal.span {(p : A)}) A]
    [PerfectRing (A ⧸ Ideal.span {(p : A)}) p]
    (hp : Function.Injective (fun x : A ↦ (p : A) * x)) :
    ∃ e : WittVector p (A ⧸ Ideal.span {(p : A)}) ≃+* A,
      (Ideal.Quotient.mk (Ideal.span {(p : A)})).comp e.toRingHom =
        WittVector.constantCoeff :=
  exists_strictPRecoveryEquiv p A hp

-- 連続性、p正則性を追加せず、任意の二つの環準同型の一意性を検証。
theorem f4_audit_unique (A : Type u) [CommRing A] (p : ℕ) [Fact p.Prime]
    [IsAdicComplete (Ideal.span {(p : A)}) A]
    [PerfectRing (A ⧸ Ideal.span {(p : A)}) p]
    (f g : WittVector p (A ⧸ Ideal.span {(p : A)}) →+* A)
    (hf : (Ideal.Quotient.mk (Ideal.span {(p : A)})).comp f = WittVector.constantCoeff)
    (hg : (Ideal.Quotient.mk (Ideal.span {(p : A)})).comp g = WittVector.constantCoeff) : f = g :=
  strictPRecovery_unique p A f g hf hg

-- 零環の同型の構成はPerfectRingやCharPを要求しない。
theorem f4_audit_zero_ring (A : Type u) [CommRing A] [Subsingleton A]
    (p : ℕ) [Fact p.Prime] :
    ∃ e : WittVector p (A ⧸ Ideal.span {(p : A)}) ≃+* A,
      (Ideal.Quotient.mk (Ideal.span {(p : A)})).comp e.toRingHom =
        WittVector.constantCoeff := by
  refine ⟨strictPRecoveryEquivOfSubsingleton p A, ?_⟩
  ext x
  exact Subsingleton.elim _ _

-- 零環でも同じ公開復元定理を適用できる。CharP pは供給しない。
theorem f4_audit_zero_ring_public (A : Type u) [CommRing A] [Subsingleton A]
    (p : ℕ) [Fact p.Prime] [IsAdicComplete (Ideal.span {(p : A)}) A] :
    ∃ e : WittVector p (A ⧸ Ideal.span {(p : A)}) ≃+* A,
      (Ideal.Quotient.mk (Ideal.span {(p : A)})).comp e.toRingHom =
        WittVector.constantCoeff := by
  have : PerfectRing (ModP A p) p :=
    ⟨⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun x ↦ ⟨0, Subsingleton.elim _ _⟩⟩⟩
  exact exists_strictPRecoveryEquiv p A
    (fun _ _ _ ↦ Subsingleton.elim _ _)

-- 一般完全標数p環の指定した剰余写像の、一意な持上げ。
theorem f4_audit_general_lift (A k : Type u) [CommRing A] [CommRing k]
    (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]
    [IsAdicComplete (Ideal.span {(p : A)}) A]
    (s : k →+* A ⧸ Ideal.span {(p : A)}) :
    ∃! f : WittVector p k →+* A,
      (Ideal.Quotient.mk (Ideal.span {(p : A)})).comp f = s.comp WittVector.constantCoeff :=
  existsUnique_wittResidueLift_of_complete p A k s

assert_no_sorry f4_audit_bs_signature
assert_no_sorry f4_audit_unique
assert_no_sorry f4_audit_zero_ring
assert_no_sorry f4_audit_general_lift

assert_no_sorry f4_audit_zero_ring_public
