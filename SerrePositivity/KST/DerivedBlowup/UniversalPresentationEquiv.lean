module

public import SerrePositivity.KST.DerivedBlowup.UniversalPresentation

/-!
概要：KST Def3.1・Lemma3.6 の普遍チャートの関係式商は ℤ[T_i,S_j] と同型。
方針：radial 座標と比座標を関係式商へ戻す写像を構成し、両側逆を生成元で示す。
規約：通常の可換環同型。Koszul 解消の正則性は別工程。
使われ方：普遍 blowup の局所環と Koszul 表示の接続。
-/

@[expose] public noncomputable section

universe v

namespace SerrePositivity.KST.DerivedBlowup

variable {I : Type v} [DecidableEq I]

/-- 概要：自由な普遍チャートから関係式商への逆代入射。
方針：none を T_i、some j を比変数 S_j の剰余類へ送る。
規約：KST Def3.1。使われ方：普遍商表示の逆写像。 -/
def universalChartToQuotient (i : I) : UniversalChart i →+* UniversalPresentationQuotient i :=
  MvPolynomial.eval₂Hom (Int.castRingHom _)
    (fun j => match j with
      | none => Ideal.Quotient.mk (universalRelationIdeal i) (MvPolynomial.C (MvPolynomial.X i))
      | some j => Ideal.Quotient.mk (universalRelationIdeal i) (MvPolynomial.X j))

/-- 概要：関係式商では T_i S_j=T_j が成り立つ。
方針：生成関係式が商で零であることを使う。
規約：KST Def3.1。使われ方：逆代入の係数上の逆元律。 -/
theorem universalQuotient_relation (i : I) (j : ChartIndex i) :
    Ideal.Quotient.mk (universalRelationIdeal i) (MvPolynomial.C (MvPolynomial.X i)) *
        Ideal.Quotient.mk (universalRelationIdeal i) (MvPolynomial.X j) =
      Ideal.Quotient.mk (universalRelationIdeal i) (MvPolynomial.C (MvPolynomial.X j.val)) := by
  have h : Ideal.Quotient.mk (universalRelationIdeal i) (universalRelation i j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)
  simpa [universalRelation, chartRelation, chartCoordinate, j.property,
    map_sub, map_mul, sub_eq_zero] using h

/-- 概要：代入後の逆代入は関係式商への標準射になる。
方針：比変数と係数の各 T_j を比較し、pivot 以外では商の関係式を使う。
規約：KST Def3.1。使われ方：商環上の左逆。 -/
theorem universalChartToQuotient_comp_presentation (i : I) :
    (universalChartToQuotient i).comp (universalPresentationMap i) =
      Ideal.Quotient.mk (universalRelationIdeal i) := by
  apply MvPolynomial.ringHom_ext'
  · apply MvPolynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · intro j
      by_cases hj : j = i
      · subst j
        simp [universalChartToQuotient, radialCoordinate]
      · have hr : universalRatio i j = MvPolynomial.X (some (⟨j, hj⟩ : ChartIndex i)) :=
          universalRatio_other i ⟨j, hj⟩
        simpa [universalChartToQuotient, universalPresentationMap_C, universalBaseMap_X,
          radialCoordinate, hr] using universalQuotient_relation i ⟨j, hj⟩
  · intro j
    simp [universalChartToQuotient]

/-- 概要：自由普遍チャート上で逆代入後の代入は恒等。
方針：none と some の変数で比較する。
規約：KST Def3.1。使われ方：商表示の右逆。 -/
theorem universalQuotientToChart_comp_inverse (i : I) :
    (universalQuotientToChart i).comp (universalChartToQuotient i) =
      RingHom.id (UniversalChart i) := by
  apply MvPolynomial.ringHom_ext'
  · exact Subsingleton.elim _ _
  · intro j
    cases j with
    | none => simp [universalChartToQuotient, universalQuotientToChart, radialCoordinate]
    | some j => simp [universalChartToQuotient, universalQuotientToChart]

/-- 概要：関係式商上で代入後の逆代入は恒等。
方針：商射の全射性と多項式上の合成公式を使う。
規約：KST Def3.1。使われ方：商表示の左逆。 -/
theorem universalChartToQuotient_comp_inverse (i : I) :
    (universalChartToQuotient i).comp (universalQuotientToChart i) =
      RingHom.id (UniversalPresentationQuotient i) := by
  apply RingHom.ext
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  change universalChartToQuotient i
    (universalQuotientToChart i (Ideal.Quotient.mk (universalRelationIdeal i) p)) = _
  rw [universalQuotientToChart, Ideal.Quotient.lift_mk]
  exact RingHom.congr_fun (universalChartToQuotient_comp_presentation i) p

/-- 概要：普遍チャートの関係式商と自由多項式表示環の環同型。
方針：両側の逆代入と証明済みの逆元律を組み合わせる。
規約：KST Def3.1・Lemma3.6。使われ方：普遍チャートの通常の環表示の確定。 -/
def universalPresentationEquiv (i : I) :
    UniversalPresentationQuotient i ≃+* UniversalChart i :=
  RingEquiv.ofRingHom (universalQuotientToChart i) (universalChartToQuotient i)
    (universalQuotientToChart_comp_inverse i) (universalChartToQuotient_comp_inverse i)

end SerrePositivity.KST.DerivedBlowup
