module

public import SerrePositivity.KST.DerivedBlowup.UniversalClassicalCenter

/-!
概要：KST Def3.1 の普遍自由多項式チャートを L7 の Rees–Proj 標準チャートと同定する。
方針：radial と比座標を Rees チャートへ戻し、正則な pivot による消去で両側逆を示す。
規約：古典的 blowup の構成と一意性は L7 の既存定理を使用する。
使われ方：普遍 blowup の通常チャートを Koszul dg 解消へ接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v

namespace SerrePositivity.KST.DerivedBlowup

variable {I : Type v} [DecidableEq I]

/-- 概要：古典チャートの斉次比は自由チャートの比座標へ送られる。
方針：pivot を掛けた比の公式を移し、radial 座標の非零性で消去する。
規約：KST Def3.1。使われ方：自由チャート上の逆写像の確認。 -/
@[simp] theorem universalClassicalToChart_ratio (i j : I) :
    universalClassicalToChart i (SchemeLemmas.chartRatio _
      (universalCenterGenerator i) (universalCenterGenerator j)) = universalRatio i j := by
  apply mul_left_cancel₀ (MvPolynomial.X_ne_zero (R := ℤ) (none : Option (ChartIndex i)))
  have h := congrArg (universalClassicalToChart i)
    (SchemeLemmas.chartBaseMap_mul_ratio (universalCenter (I := I))
      (universalCenterGenerator i) (universalCenterGenerator j))
  rw [map_mul] at h
  change universalClassicalToChart i
      (SchemeLemmas.chartBaseMap _ (universalCenterGenerator i) (MvPolynomial.X i)) *
      universalClassicalToChart i (SchemeLemmas.chartRatio _
        (universalCenterGenerator i) (universalCenterGenerator j)) =
    universalClassicalToChart i
      (SchemeLemmas.chartBaseMap _ (universalCenterGenerator i) (MvPolynomial.X j)) at h
  rw [universalClassicalToChart_base, universalClassicalToChart_base,
    universalBaseMap_pivot, universalBaseMap_X] at h
  exact h

/-- 概要：自由多項式チャートから古典 Rees チャートへの逆代入。
方針：radial は基底の T_i、比変数は斉次比 T_j/T_i へ送る。
規約：KST Def3.1。使われ方：古典チャートの明示的な多項式表示。 -/
def universalChartToClassical (i : I) : UniversalChart i →+* UniversalClassicalChart i :=
  MvPolynomial.eval₂Hom (Int.castRingHom _)
    (fun j => match j with
      | none => SchemeLemmas.chartBaseMap _ (universalCenterGenerator i) (MvPolynomial.X i)
      | some j => SchemeLemmas.chartRatio _ (universalCenterGenerator i)
          (universalCenterGenerator j.val))

omit [DecidableEq I] in
/-- 概要：逆代入は radial 変数を基底の pivot へ送る。
方針：多項式評価の生成元公式。
規約：KST Def3.1。使われ方：基底上の相互逆の確認。 -/
@[simp] theorem universalChartToClassical_radial (i : I) :
    universalChartToClassical i (radialCoordinate i) =
      SchemeLemmas.chartBaseMap _ (universalCenterGenerator i) (MvPolynomial.X i) :=
  MvPolynomial.eval₂Hom_X' _ _ none

omit [DecidableEq I] in
/-- 概要：逆代入は比変数を Rees チャートの斉次比へ送る。
方針：多項式評価の生成元公式。
規約：KST Def3.1。使われ方：基底上の相互逆の確認。 -/
@[simp] theorem universalChartToClassical_ratio (i : I) (j : ChartIndex i) :
    universalChartToClassical i (MvPolynomial.X (some j)) =
      SchemeLemmas.chartRatio _ (universalCenterGenerator i) (universalCenterGenerator j.val) :=
  MvPolynomial.eval₂Hom_X' _ _ (some j)

/-- 概要：逆代入と普遍構造射の合成は Rees チャートの基底構造射。
方針：独立変数 T_j で pivot と非 pivot を分け、比の分母消去を使う。
規約：KST Def3.1。使われ方：古典チャート上の逆元律と基底保存。 -/
theorem universalChartToClassical_comp_base (i : I) :
    (universalChartToClassical i).comp (universalBaseMap i).toRingHom =
      SchemeLemmas.chartBaseMap _ (universalCenterGenerator i) := by
  apply MvPolynomial.ringHom_ext'
  · exact Subsingleton.elim _ _
  · intro j
    by_cases hj : j = i
    · subst j
      simp [universalChartToClassical, radialCoordinate]
    · have hr := universalRatio_other i (⟨j, hj⟩ : ChartIndex i)
      change universalChartToClassical i (universalBaseMap i (MvPolynomial.X j)) = _
      rw [universalBaseMap_X, hr, map_mul]
      rw [universalChartToClassical_radial, universalChartToClassical_ratio]
      exact SchemeLemmas.chartBaseMap_mul_ratio (universalCenter (I := I))
        (universalCenterGenerator i) (universalCenterGenerator j)

/-- 概要：自由チャート上で古典チャートへの逆代入と比較射は互いに逆。
方針：none と some の生成元上で基底保存と比座標公式を使う。
規約：KST Def3.1。使われ方：古典チャート環同型の右逆。 -/
theorem universalClassicalToChart_comp_inverse (i : I) :
    (universalClassicalToChart i).comp (universalChartToClassical i) =
      RingHom.id (UniversalChart i) := by
  apply MvPolynomial.ringHom_ext'
  · exact Subsingleton.elim _ _
  · intro j
    cases j with
    | none => simp [universalChartToClassical, radialCoordinate]
    | some j => simp [universalChartToClassical]

/-- 概要：古典 Rees チャート上でも比較射と逆代入は互いに逆。
方針：正則 pivot を保つ Rees チャートからの環射の一意性を使う。
規約：KST Def3.1。使われ方：古典チャート環同型の左逆。 -/
theorem universalChartToClassical_comp_inverse (i : I) :
    (universalChartToClassical i).comp (universalClassicalToChart i) =
      RingHom.id (UniversalClassicalChart i) := by
  apply SchemeLemmas.chart_hom_ext_of_regular (universalCenter (I := I))
    (SchemeLemmas.chartBaseMap _ (universalCenterGenerator i)) (universalCenterGenerator i)
    (SchemeLemmas.chartBaseMap_mem_nonZeroDivisors _ _)
  · intro p
    change universalChartToClassical i (universalClassicalToChart i
      (SchemeLemmas.chartBaseMap _ (universalCenterGenerator i) p)) = _
    rw [universalClassicalToChart_base]
    exact RingHom.congr_fun (universalChartToClassical_comp_base i) p
  · intro p
    rfl

/-- 概要：L7 の古典 Rees–Proj 普遍チャートと自由多項式チャートの明示環同型。
方針：構成した比較射・逆代入と証明済みの両側逆を束ねる。
規約：KST Def3.1・Lemma3.6。使われ方：古典普遍 blowup の局所 dg 解消の幾何的入力。 -/
def universalClassicalChartEquiv (i : I) : UniversalClassicalChart i ≃+* UniversalChart i :=
  RingEquiv.ofRingHom (universalClassicalToChart i) (universalChartToClassical i)
    (universalClassicalToChart_comp_inverse i) (universalChartToClassical_comp_inverse i)

end SerrePositivity.KST.DerivedBlowup
