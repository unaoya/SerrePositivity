module

public import SerrePositivity.BhattScholze.Semiperfectoid.Lci.LciEnvelopeCoefficient
public import SerrePositivity.BhattScholze.Semiperfectoid.Lci.LciEnvelopePresentation
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Criterion
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.PowerTorsion
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.RingTheory.RingHom.Flat

/-!
# 普遍除算の生成元剰余の完全平坦性

## 概要
自由変数を d で割る置換は、d 剰余で初期関係を除いた係数環上 p 完全平坦。

## 方針
二つの係数環の p 正則性と、Witt 表示による mod (p,d) の忠実平坦性を使う。

## 規約
BS 著者版 Example 7.9 の普遍未完備模型。

## 使われ方
有界 p 冪ねじれを持つ一般の正則列の商への完備導来底変換。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace SerrePositivity.BhattScholze

open scoped TensorProduct

private theorem exists_primeDoubleQuotient_equiv (R : Type u) [CommRing R]
    (I : Ideal R) (p : ℕ) :
    ∃ e : ((R ⧸ I) ⧸ Ideal.span {(p : R ⧸ I)}) ≃+*
        R ⧸ (I ⊔ Ideal.span {(p : R)}),
      ∀ x : R, e (Ideal.Quotient.mk _ (Ideal.Quotient.mk I x)) =
        Ideal.Quotient.mk _ x := by
  have hI : (Ideal.span {(p : R ⧸ I)}) =
      (Ideal.span {(p : R)}).map (Ideal.Quotient.mk I) := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  let e := (Ideal.quotEquivOfEq hI).trans
    (DoubleQuot.quotQuotEquivQuotSup I (Ideal.span {(p : R)}))
  refine ⟨e, fun x => ?_⟩
  change DoubleQuot.quotQuotEquivQuotSup I (Ideal.span {(p : R)})
    (DoubleQuot.quotQuotMk I (Ideal.span {(p : R)}) x) = _
  exact DoubleQuot.quotQuotEquivQuotSup_quotQuotMk I (Ideal.span {(p : R)}) x

variable {p : ℕ} [Fact p.Prime] {A S : Type u} [CommRing A]

/-- 概要：普遍的な d 除算の d 剰余は、初期関係の商の上で p 完全平坦。
方針：初期関係の商と生成元商で p の正則性を確認し、二重商上の平坦性判定を使う。
規約：BS 著者版 Example 7.9。係数環とその d 商の p 正則性を仮定する。
使われ方：正則列の商の有界ねじれから、完備底変換の離散性を得る。 -/
theorem exists_freeVariable_generatorResidue_completelyFlat
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
      IsCompletelyFlat (Ideal.span {(p : U ⧸ J)}) (U ⧸ K) := by
  let U := RelativeFreeDeltaRing (R := A) S
  let C : A →+* U := MvPolynomial.C
  let x : S → U := fun s => MvPolynomial.X (s, 0)
  let K : Ideal U := Ideal.span {C d}
  let J : Ideal U := K ⊔ Ideal.span (Set.range x)
  let IP : Ideal U := Ideal.span {(p : U), C d}
  let JP := deltaDivisionFirstBaseIdeal (p := p) (C d) x
  let T := U ⧸ J
  let E := U ⧸ K
  let a : U →+* U := deltaDivisionSourceMap D d
  have hJK : J ≤ K.comap a := by
    apply sup_le
    · apply (K.comap a).span_singleton_le_iff_mem.mpr
      change a (C d) ∈ K
      rw [deltaDivisionSourceMap_C]
      exact Ideal.subset_span (Set.mem_singleton _)
    · apply Ideal.span_le.mpr
      rintro _ ⟨s, rfl⟩
      change a (x s) ∈ K
      have hx : a (x s) = C d * x s := by
        simpa only [Function.iterate_zero_apply] using deltaDivisionSourceMap_X D d s 0
      rw [hx]
      exact K.mul_mem_right _ (Ideal.subset_span (Set.mem_singleton _))
  let b : T →+* E := Ideal.quotientMap K a hJK
  have hb (z : U) : b (Ideal.Quotient.mk J z) = Ideal.Quotient.mk K (a z) := rfl
  let := b.toAlgebra
  have hT : IsSMulRegular T (p : T) := by
    have h := freeDelta_initialQuotient_scalar_regular (S := S) d (p : A)
      (by simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using hpd)
    change Function.Injective (fun x : T => (p : T) * x)
    simpa only [map_natCast, IsLeftRegular] using h.left
  have hK : K = (Ideal.span {d}).map C := by
    rw [Ideal.map_span, Set.image_singleton]
  let eK := (Ideal.quotEquivOfEq hK).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := S × ℕ) (Ideal.span {d})).symm.toRingEquiv
  have hE : IsSMulRegular E (p : E) := by
    have hV : IsSMulRegular (MvPolynomial (S × ℕ) (A ⧸ Ideal.span {d}))
        (p : MvPolynomial (S × ℕ) (A ⧸ Ideal.span {d})) := by
      simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
        (show IsSMulRegular (A ⧸ Ideal.span {d}) (p : A ⧸ Ideal.span {d}) from hpd).of_flat
          (S := MvPolynomial (S × ℕ) (A ⧸ Ideal.span {d}))
    intro y z hyz
    apply eK.injective
    apply hV
    simpa only [map_mul, map_natCast, smul_eq_mul] using congrArg eK hyz
  let IT : Ideal T := Ideal.span {(p : T)}
  let IE := IT.map b
  have hIE : IE = Ideal.span {(p : E)} := by
    change (Ideal.span {(p : T)}).map b = Ideal.span {(p : E)}
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hIP : IP = Ideal.span {(p : U)} ⊔ K := by
    rw [← Ideal.span_union]
    congr 1
  have hJP : J ⊔ Ideal.span {(p : U)} = JP := by
    change (K ⊔ Ideal.span (Set.range x)) ⊔ Ideal.span {(p : U)} =
      IP ⊔ Ideal.span (Set.range x)
    rw [hIP]
    ac_rfl
  have hKP : K ⊔ Ideal.span {(p : U)} = IP := by
    rw [hIP, sup_comm]
  obtain ⟨eT, heT⟩ := exists_primeDoubleQuotient_equiv U J p
  obtain ⟨eE, heE⟩ := exists_primeDoubleQuotient_equiv U K p
  let eSrc := eT.trans (Ideal.quotEquivOfEq hJP)
  let eTgt := ((Ideal.quotEquivOfEq hIE).trans eE).trans (Ideal.quotEquivOfEq hKP)
  have heSrc (z : U) :
      eSrc (Ideal.Quotient.mk IT (Ideal.Quotient.mk J z)) = Ideal.Quotient.mk JP z := by
    change (Ideal.quotEquivOfEq hJP) (eT _) = _
    rw [heT]
    rfl
  have heTgt (z : U) :
      eTgt (Ideal.Quotient.mk IE (Ideal.Quotient.mk K z)) = Ideal.Quotient.mk IP z := by
    change (Ideal.quotEquivOfEq hKP) (eE (Ideal.Quotient.mk _ (Ideal.Quotient.mk K z))) = _
    rw [heE]
    rfl
  obtain ⟨b₀, hb₀, hflat₀⟩ :=
    exists_deltaDivision_freeVariable_residue_faithfullyFlat (S := S) D d hp u hu
  let bbar : T ⧸ IT →+* E ⧸ IE := Ideal.quotientMap IE b Ideal.le_comap_map
  have hbar : eTgt.toRingHom.comp bbar = b₀.comp eSrc.toRingHom := by
    apply Ideal.Quotient.ringHom_ext
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro z
    change eTgt (Ideal.Quotient.mk IE (b (Ideal.Quotient.mk J z))) =
      b₀ (eSrc (Ideal.Quotient.mk IT (Ideal.Quotient.mk J z)))
    rw [hb, heSrc, heTgt, hb₀]
  have hflatbar : bbar.Flat := by
    have hflat₀' : b₀.Flat := by
      let := b₀.toAlgebra
      let := hflat₀
      exact RingHom.flat_algebraMap_iff.mpr inferInstance
    have hcomp : (eTgt.toRingHom.comp bbar).Flat := by
      rw [hbar]
      exact (RingHom.Flat.of_bijective eSrc.bijective).comp hflat₀'
    exact (RingHom.Flat.comp_iff_of_bijective_left eTgt.bijective).mp hcomp
  refine ⟨b, hb, ?_⟩
  let := adicQuotientAlgebra IT E
  have hflat : Module.Flat (T ⧸ IT) (E ⧸ IE) := by
    apply RingHom.flat_algebraMap_iff.mp
    exact hflatbar
  have hM : IsSMulRegular E (p : T) := by
    intro y z hyz
    apply hE
    change (p : E) * y = (p : E) * z
    change b (p : T) * y = b (p : T) * z at hyz
    have hbp : b (p : T) = (p : E) := map_natCast b p
    exact (congrArg (fun t : E => t * y) hbp.symm).trans
      (hyz.trans (congrArg (fun t : E => t * z) hbp))
  apply isCompletelyFlat_principal_of_regular (p : T) hT E hM
  exact Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor E IT).symm.toLinearEquiv

end SerrePositivity.BhattScholze
