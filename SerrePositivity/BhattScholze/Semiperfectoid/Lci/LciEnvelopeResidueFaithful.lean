module

public import SerrePositivity.BhattScholze.Semiperfectoid.Lci.LciEnvelopeResidue
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import all SerrePositivity.BhattScholze.Semiperfectoid.Lci.LciEnvelopeResidue

/-!
# 普遍除算の生成元剰余の完全忠実平坦性

## 概要
自由変数の除算の剰余について、既存の完全平坦性に忠実性を加える。
## 方針
既存の実 mod (p,d) の忠実平坦性を、標準二重商比較へ移す。
## 規約
BS 著者版 Example 7.9・Proposition 7.10。Fil₀ の分裂は仮定しない。
## 使われ方
有限 T の関係商への完備底変換の忠実性。
-/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
open DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {p : ℕ} [Fact p.Prime] {A S : Type u} [CommRing A]

/-- 普遍自由変数除算の生成元剰余は、初期関係商上 p 完全忠実平坦。 -/
theorem exists_freeVariable_generatorResidue_completelyFaithfullyFlat
    (D : DeltaStructure p A) (d : A)
    (hp : Function.Injective (fun x : A => (p : A) * x))
    (hpd : Function.Injective (fun x : A ⧸ Ideal.span {d} => (p : A ⧸ Ideal.span {d}) * x))
    (u : Aˣ) (hu : (u : A) = D.delta d) :
    let U := RelativeFreeDeltaRing (R := A) S
    let K : Ideal U := Ideal.span {MvPolynomial.C d}
    let J : Ideal U := K ⊔ Ideal.span (Set.range fun s : S => MvPolynomial.X (s, 0))
    ∃ b : U ⧸ J →+* U ⧸ K,
      (∀ z : U, b (Ideal.Quotient.mk J z) =
        Ideal.Quotient.mk K (deltaDivisionSourceMap D d z)) ∧
      letI := b.toAlgebra
      IsCompletelyFaithfullyFlat (Ideal.span {(p : U ⧸ J)}) (U ⧸ K) := by
  let U := RelativeFreeDeltaRing (R := A) S
  let C : A →+* U := MvPolynomial.C
  let K : Ideal U := Ideal.span {C d}
  let x : S → U := fun s => MvPolynomial.X (s, 0)
  let J := K ⊔ Ideal.span (Set.range x)
  let T := U ⧸ J
  let E := U ⧸ K
  obtain ⟨b, hb, hflat⟩ := exists_freeVariable_generatorResidue_completelyFlat (S := S) D d hp hpd u hu
  letI := b.toAlgebra
  let IT : Ideal T := Ideal.span {(p : T)}
  let IE := IT.map b
  let IP : Ideal U := Ideal.span {(p : U), C d}
  let JP := deltaDivisionFirstBaseIdeal (p := p) (C d) x
  have hIE : IE = Ideal.span {(p : E)} := by
    change (Ideal.span {(p : T)}).map b = _
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hIP : IP = Ideal.span {(p : U)} ⊔ K := by
    rw [← Ideal.span_union]
    congr 1
  have hJP : J ⊔ Ideal.span {(p : U)} = JP := by
    change (K ⊔ Ideal.span (Set.range x)) ⊔ Ideal.span {(p : U)} =
      IP ⊔ Ideal.span (Set.range x)
    rw [hIP]
    ac_rfl
  have hKP : K ⊔ Ideal.span {(p : U)} = IP := by rw [hIP, sup_comm]
  obtain ⟨eT, heT⟩ := exists_primeDoubleQuotient_equiv U J p
  obtain ⟨eE, heE⟩ := exists_primeDoubleQuotient_equiv U K p
  let eSrc := eT.trans (Ideal.quotEquivOfEq hJP)
  let eTgt := ((Ideal.quotEquivOfEq hIE).trans eE).trans (Ideal.quotEquivOfEq hKP)
  have heSrc (z : U) : eSrc (Ideal.Quotient.mk IT (Ideal.Quotient.mk J z)) =
      Ideal.Quotient.mk JP z := by
    change (Ideal.quotEquivOfEq hJP) (eT _) = _
    rw [heT]
    rfl
  have heTgt (z : U) : eTgt (Ideal.Quotient.mk IE (Ideal.Quotient.mk K z)) =
      Ideal.Quotient.mk IP z := by
    change (Ideal.quotEquivOfEq hKP) (eE (Ideal.Quotient.mk _ (Ideal.Quotient.mk K z))) = _
    rw [heE]
    rfl
  obtain ⟨b0, hb0, hf0⟩ := exists_deltaDivision_freeVariable_residue_faithfullyFlat (S := S) D d hp u hu
  let bbar : T ⧸ IT →+* E ⧸ IE := Ideal.quotientMap IE b Ideal.le_comap_map
  have hbar : eTgt.toRingHom.comp bbar = b0.comp eSrc.toRingHom := by
    apply Ideal.Quotient.ringHom_ext
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro z
    change eTgt (Ideal.Quotient.mk IE (b (Ideal.Quotient.mk J z))) =
      b0 (eSrc (Ideal.Quotient.mk IT (Ideal.Quotient.mk J z)))
    rw [hb, heSrc, heTgt, hb0]
  have hf0' : b0.FaithfullyFlat := by
    letI := b0.toAlgebra
    exact hf0
  have hff : bbar.FaithfullyFlat := by
    have hs : (b0.comp eSrc.toRingHom).FaithfullyFlat :=
      RingHom.FaithfullyFlat.stableUnderComposition _ _
        (RingHom.FaithfullyFlat.of_bijective eSrc.bijective) hf0'
    have ht : (eTgt.symm.toRingHom.comp (b0.comp eSrc.toRingHom)).FaithfullyFlat :=
      RingHom.FaithfullyFlat.stableUnderComposition _ _ hs
        (RingHom.FaithfullyFlat.of_bijective eTgt.symm.bijective)
    have heq : eTgt.symm.toRingHom.comp (b0.comp eSrc.toRingHom) = bbar := by
      rw [← hbar]
      apply RingHom.ext
      intro y
      exact eTgt.symm_apply_apply (bbar y)
    rwa [heq] at ht
  refine ⟨b, hb, hflat, ?_⟩
  letI := adicQuotientAlgebra IT E
  letI : Module.FaithfullyFlat (T ⧸ IT) (E ⧸ IE) := by
    apply RingHom.faithfullyFlat_algebraMap_iff.mp
    exact hff
  exact Module.FaithfullyFlat.of_linearEquiv _ _
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor E IT).symm.toLinearEquiv

end SerrePositivity.BhattScholze
