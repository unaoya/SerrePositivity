module

public import SerrePositivity.BhattScholze.Semiperfectoid.Lci.LciEnvelopeCoefficient
public import SerrePositivity.CommutativeAlgebra.KoszulRegular.MonicRelation
public import SerrePositivity.CommutativeAlgebra.KoszulRegular.Powers
public import SerrePositivity.HomologicalAlgebra.KoszulRegularBaseChange
public import Mathlib.RingTheory.Polynomial.Quotient

/-!
# 自由な初期関係の Koszul 分解

## 概要
自由 δ 環の d 商の初期変数は Koszul 分解を与える。
分類射の像が正則列なら、その商の導来底変換は通常の商になる。

## 方針
係数の d 商上の多項式環へ移して、異なる変数のモニック関係の分解を使う。

## 規約
BS 著者版 Example 7.9 の初期関係。後続の δ 関係は課さない。

## 使われ方
普遍置換の d 剰余を、指定の正則列の商へ底変換する。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace SerrePositivity.BhattScholze

variable {A S : Type u} [CommRing A] {r : ℕ}

/-- 概要：自由 δ 環を係数の d で割った環では、有限個の初期変数が Koszul 分解を与える。
方針：係数商上の多項式環に同定し、異なる変数をモニック関係として扱う。
規約：BS 著者版 Example 7.9。係数環に p 正則性や有界性は仮定しない。
使われ方：一般の正則列への分類射で、初期関係の商を導来底変換する。 -/
theorem Semiperfectoid.freeDelta_initialVariables_modGenerator_isKoszulResolution (d : A)
    (s : Fin r → S) (hs : Function.Injective s) :
    let U := _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) S
    let K : Ideal U := Ideal.span {MvPolynomial.C d}
    _root_.SerrePositivity.IsKoszulResolution (fun i : Fin r => Ideal.Quotient.mk K (MvPolynomial.X (s i, 0))) := by
  let U := _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) S
  let K : Ideal U := Ideal.span {MvPolynomial.C d}
  have hK : K = (Ideal.span {d}).map (MvPolynomial.C : A →+* U) := by
    rw [Ideal.map_span, Set.image_singleton]
  let e := (Ideal.quotEquivOfEq hK).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial
      (σ := S × ℕ) (Ideal.span {d})).symm.toRingEquiv
  have hX (i : Fin r) : e (Ideal.Quotient.mk K (MvPolynomial.X (s i, 0))) =
      (MvPolynomial.X (s i, 0) : MvPolynomial (S × ℕ) (A ⧸ Ideal.span {d})) := by
    change (MvPolynomial.quotientEquivQuotientMvPolynomial
      (σ := S × ℕ) (Ideal.span {d})).symm
      ((Ideal.quotEquivOfEq hK) (Ideal.Quotient.mk K (MvPolynomial.X (s i, 0)))) = _
    rw [Ideal.quotEquivOfEq_mk]
    change MvPolynomial.eval₂Hom _ MvPolynomial.X (MvPolynomial.X (s i, 0)) = _
    exact MvPolynomial.eval₂Hom_X' ..
  apply _root_.SerrePositivity.isKoszulResolution_of_ringEquiv e
  have hvar := _root_.SerrePositivity.BhattScholze.Andre.monicRelation_fin_isKoszulResolution
    (fun _ : S × ℕ => (Polynomial.X : Polynomial (A ⧸ Ideal.span {d})))
    (fun _ => Polynomial.monic_X) (fun i : Fin r => (s i, 0))
    (fun _ _ h => hs (Prod.mk.inj h).1)
  have he : e.toRingHom ∘ (fun i : Fin r => Ideal.Quotient.mk K (MvPolynomial.X (s i, 0))) =
      fun i => (MvPolynomial.X (s i, 0) : MvPolynomial (S × ℕ) (A ⧸ Ideal.span {d})) :=
    funext hX
  rw [he]
  simpa only [_root_.SerrePositivity.BhattScholze.Andre.monicRelation, Polynomial.eval₂_X] using hvar

end SerrePositivity.BhattScholze
