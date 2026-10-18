module

public import SerrePositivity.KST.DerivedBlowup.LiftedUniversalSpecialization

/-!
概要：KST Lemma3.6 の普遍関係式列の解消性を宇宙移送した基底でも確認する。
方針：係数 ULift の環同型をチャート多項式環へ延長し、弱正則性を移送する。
規約：宇宙移送に正則性の仮定を追加しない。
使われ方：任意宇宙の係数環への底変更で使う普遍 Koszul 解消。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

variable {r : ℕ}

/-- 概要：係数を宇宙移送した普遍表示環と元の普遍表示環の環同型。
方針：ULift の環同型を多項式環の係数に適用する。
規約：KST Def3.1。使われ方：普遍関係式列の正則性の移送。 -/
def liftedUniversalPresentationEquiv (i : Fin (r + 1)) :
    ChartRing (LiftedUniversalBase.{u} r) i ≃+* ChartRing (UniversalBase (Fin (r + 1))) i :=
  MvPolynomial.mapEquiv (ChartIndex i) ULift.ringEquiv

/-- 概要：表示環の宇宙移送同型はチャート関係式を保つ。
方針：係数・変数・積・差をそれぞれ比較する。
規約：KST Lemma3.6。使われ方：弱正則性を元の普遍列へ帰着する。 -/
theorem liftedUniversalPresentationEquiv_relation (i j : Fin (r + 1)) :
    liftedUniversalPresentationEquiv.{u} i
      (chartRelation (LiftedUniversalBase.{u} r) (liftedUniversalCoefficients r) i j) =
        chartRelation (UniversalBase (Fin (r + 1))) MvPolynomial.X i j := by
  by_cases h : j = i
  · subst j
    simp [chartRelation, chartCoordinate]
  · simp [liftedUniversalPresentationEquiv, MvPolynomial.mapEquiv_apply, chartRelation,
      chartCoordinate, h, liftedUniversalCoefficients, ULift.ringEquiv]

/-- 概要：宇宙移送した普遍チャートの有限関係式列も弱正則。
方針：表示環同型の加法部分でスカラー作用を比較し、元の普遍列の弱正則性を戻す。
規約：KST Lemma3.6。使われ方：任意宇宙での普遍 Koszul 解消。 -/
theorem liftedUniversalChartSequence_isWeaklyRegular (i : Fin (r + 1)) :
    RingTheory.Sequence.IsWeaklyRegular (ChartRing (LiftedUniversalBase.{u} r) i)
      (List.ofFn (chartKoszulSequence (liftedUniversalCoefficients r) i)) := by
  let rs := List.ofFn (chartKoszulSequence (liftedUniversalCoefficients.{u} r) i)
  let e := liftedUniversalPresentationEquiv.{u} i
  refine (e.toAddEquiv.isWeaklyRegular_congr (as := rs) (bs := rs.map e) ?_).mpr ?_
  · apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro a _ x
    exact e.map_mul a x
  · have heq : rs.map e = List.ofFn
        (chartKoszulSequence (R := UniversalBase (Fin (r + 1))) MvPolynomial.X i) := by
      dsimp only [rs]
      rw [List.map_ofFn]
      apply congrArg List.ofFn
      funext j
      exact liftedUniversalPresentationEquiv_relation i (i.succAbove j)
    rw [heq]
    exact universalChartSequence_isWeaklyRegular i

/-- 概要：宇宙移送した普遍チャートの有限 Koszul 複体は関係式商を解消する。
方針：移送した弱正則性に既存の有限 Koszul 解消定理を適用する。
規約：KST Lemma3.6。使われ方：任意係数環の宇宙での普遍解消の入力。 -/
theorem liftedUniversalChartSequence_isKoszulResolution (i : Fin (r + 1)) :
    SerrePositivity.IsKoszulResolution
      (chartKoszulSequence (liftedUniversalCoefficients.{u} r) i) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (liftedUniversalChartSequence_isWeaklyRegular i)

end SerrePositivity.KST.DerivedBlowup
