module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDEnvelopeCrystalline
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Frames.AffineCechFrameLift
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineEnvelopeCoefficients
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDFrobeniusLift

/-!
# 完備分冪枠への有限 affine な橋

## 概要
結晶 prism となる完備分冪枠へ、有限 affine 枠の頂点変数を p 乗に送る。

## 方針
頂点差が分冪イデアルに入れば、その Frobenius 像は (p) に入る。
この合同式と affine 包の普遍性で、厳密な環射とその仕様を得る。

## 規約
基底の射を prism 射として指定し、標的の選択生成元が p であることを明記する。

## 使われ方
BS 著者版 Theorem 6.4 の Witt 係数への小さい結晶の橋。
-/

public noncomputable section

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable {p : ℕ} [Fact p.Prime] {k A : Type u} [CommRing k] [CommRing A]
variable {J : Ideal k} (γ : DividedPowers J)
variable (r n : ℕ) {K : Ideal (MvPolynomial (ULift.{u} (Fin r) × Fin (n + 1)) k)}
variable (E : CompletedPDEnvelopeData p γ K)
variable (T : OrientedPrism p E.carrier) (hgen : T.generator = p)
variable (P : OrientedPrism p A) {κ : Cardinal.{u}} (U : AffineEnvelopeTerm P r n κ)

variable (hdiff : ∀ (j : Fin r) (i : Fin (n + 1)),
  E.unit (MvPolynomial.X (ULift.up j, i)) -
    E.unit (MvPolynomial.X (ULift.up j, 0)) ∈ E.ideal)

include hgen hdiff in
private theorem pdEnvelopeAffineBridge_powers_mod (j : Fin r) (i : Fin (n + 1)) :
    Ideal.Quotient.mk (T).ideal (E.unit (MvPolynomial.X (ULift.up j, i)) ^ p) =
      Ideal.Quotient.mk (T).ideal (E.unit (MvPolynomial.X (ULift.up j, 0)) ^ p) := by
  have hI : (T).ideal = Ideal.span {(p : E.carrier)} := by
    change Ideal.span {(T).generator} = _
    rw [hgen]
  rw [hI]
  let q := Ideal.Quotient.mk (Ideal.span {(p : E.carrier)})
  have hzero : (p : E.carrier ⧸ Ideal.span {(p : E.carrier)}) = 0 := by
    rw [← map_natCast q]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton _))
  let F := (frobeniusOfPrimeZero hzero).comp q
  have h := RingHom.mem_ker.mp (frobenius_ideal_le_ker γ E (hdiff j i))
  change F (E.unit (MvPolynomial.X (ULift.up j, i)) -
    E.unit (MvPolynomial.X (ULift.up j, 0))) = 0 at h
  rw [map_sub, sub_eq_zero] at h
  simpa only [F, RingHom.comp_apply, frobeniusOfPrimeZero, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk, map_pow] using h

include hgen hdiff in
private theorem pdEnvelopeAffineBridge_existsUnique (b : OrientedPrism.Hom P T) :
    ∃! f : U.X.B →+* E.carrier,
      U.X.Q.deltaStructure.IsDeltaHom (T).deltaStructure f ∧
      f.comp U.X.toHom.toRingHom = b.toRingHom ∧
      ∀ j i, f (U.η (affineVariable P r n j i)) =
        E.unit (MvPolynomial.X (ULift.up j, i)) ^ p :=
  U.existsUnique_liftVariables (T) b
    (fun j i => E.unit (MvPolynomial.X (ULift.up j, i)) ^ p)
    (pdEnvelopeAffineBridge_powers_mod γ r n E T hgen hdiff)

/-- 各頂点変数を p 乗へ送る有限 affine 枠から完備分冪枠への橋。 -/
def pdEnvelopeAffineBridge (b : OrientedPrism.Hom P T) : U.X.B →+* E.carrier :=
  (pdEnvelopeAffineBridge_existsUnique γ r n E T hgen P U hdiff b).choose

/-- 実際の橋の δ 両立、基底脚、頂点での像。 -/
theorem pdEnvelopeAffineBridge_spec (b : OrientedPrism.Hom P T) :
    U.X.Q.deltaStructure.IsDeltaHom (T).deltaStructure
        (pdEnvelopeAffineBridge γ r n E T hgen P U hdiff b) ∧
      (pdEnvelopeAffineBridge γ r n E T hgen P U hdiff b).comp
        U.X.toHom.toRingHom = b.toRingHom ∧
      ∀ j i, pdEnvelopeAffineBridge γ r n E T hgen P U hdiff b
        (U.η (affineVariable P r n j i)) = E.unit (MvPolynomial.X (ULift.up j, i)) ^ p :=
  (pdEnvelopeAffineBridge_existsUnique γ r n E T hgen P U hdiff b).choose_spec.1


variable {k' A' : Type u} [CommRing k'] [CommRing A']
variable {J' : Ideal k'} (γ' : DividedPowers J')
variable {K' : Ideal (MvPolynomial (ULift.{u} (Fin r) × Fin (n + 1)) k')}
variable (E' : CompletedPDEnvelopeData p γ' K')
variable (T' : OrientedPrism p E'.carrier) (hgen' : T'.generator = p)
variable (P' : OrientedPrism p A') {κ' : Cardinal.{u}} (V : AffineEnvelopeTerm P' r n κ')
variable (hdiff' : ∀ (j : Fin r) (i : Fin (n + 1)),
  E'.unit (MvPolynomial.X (ULift.up j, i)) -
    E'.unit (MvPolynomial.X (ULift.up j, 0)) ∈ E'.ideal)

/-- 基底脚と頂点を保つ係数変更に対し、有限分冪枠への橋は厳密に自然。 -/
theorem pdEnvelopeAffineBridge_coefficients
    (b : OrientedPrism.Hom P T) (b' : OrientedPrism.Hom P' T')
    (f : OrientedPrism.Hom P P') (g : E.carrier →+* E'.carrier)
    (hg : T.deltaStructure.IsDeltaHom T'.deltaStructure g)
    (hb : g.comp b.toRingHom = b'.toRingHom.comp f.toRingHom)
    (hv : ∀ j i, g (E.unit (MvPolynomial.X (ULift.up j, i))) =
      E'.unit (MvPolynomial.X (ULift.up j, i))) :
    g.comp (pdEnvelopeAffineBridge γ r n E T hgen P U hdiff b) =
      (pdEnvelopeAffineBridge γ' r n E' T' hgen' P' V hdiff' b').comp
        (affineEnvelopeCoefficientMap f U V) := by
  have hS := pdEnvelopeAffineBridge_spec γ r n E T hgen P U hdiff b
  have hT := pdEnvelopeAffineBridge_spec γ' r n E' T' hgen' P' V hdiff' b'
  have hF := affineEnvelopeCoefficientMap_spec f U V
  apply (U.existsUnique_liftVariables T' (b'.comp f)
    (fun j i => E'.unit (MvPolynomial.X (ULift.up j, i)) ^ p)
    (pdEnvelopeAffineBridge_powers_mod γ' r n E' T' hgen' hdiff')).unique
  · refine ⟨hg.comp hS.1, ?_, ?_⟩
    · rw [RingHom.comp_assoc, hS.2.1, hb]
      rfl
    · intro j i
      change g (pdEnvelopeAffineBridge γ r n E T hgen P U hdiff b
        (U.η (affineVariable P r n j i))) = _
      rw [hS.2.2, map_pow, hv]
  · refine ⟨hT.1.comp hF.1, ?_, ?_⟩
    · rw [RingHom.comp_assoc, hF.2.1]
      change (pdEnvelopeAffineBridge γ' r n E' T' hgen' P' V hdiff' b').comp
        (V.X.toHom.toRingHom.comp f.toRingHom) = _
      rw [← RingHom.comp_assoc, hT.2.1]
      rfl
    · intro j i
      change pdEnvelopeAffineBridge γ' r n E' T' hgen' P' V hdiff' b'
        (affineEnvelopeCoefficientMap f U V (U.η (affineVariable P r n j i))) = _
      rw [hF.2.2, hT.2.2]

end SerrePositivity.BhattScholze.Prismatic
