module


public meta import SerrePositivity.Util.Citation
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
    universalClassicalToChart i (_root_.SerrePositivity.AlgebraicGeometry.chartRatio _
      (universalCenterGenerator i) (universalCenterGenerator j)) = universalRatio i j := by
  apply mul_left_cancel₀ (MvPolynomial.X_ne_zero (R := ℤ) (none : Option (ChartIndex i)))
  have h := congrArg (universalClassicalToChart i)
    (_root_.SerrePositivity.AlgebraicGeometry.chartBaseMap_mul_ratio (universalCenter (I := I))
      (universalCenterGenerator i) (universalCenterGenerator j))
  rw [map_mul] at h
  change universalClassicalToChart i
      (_root_.SerrePositivity.AlgebraicGeometry.chartBaseMap _ (universalCenterGenerator i) (MvPolynomial.X i)) *
      universalClassicalToChart i (_root_.SerrePositivity.AlgebraicGeometry.chartRatio _
        (universalCenterGenerator i) (universalCenterGenerator j)) =
    universalClassicalToChart i
      (_root_.SerrePositivity.AlgebraicGeometry.chartBaseMap _ (universalCenterGenerator i) (MvPolynomial.X j)) at h
  rw [universalClassicalToChart_base, universalClassicalToChart_base,
    universalBaseMap_pivot, universalBaseMap_X] at h
  exact h

/-- 概要：自由多項式チャートから古典 Rees チャートへの逆代入。
方針：radial は基底の T_i、比変数は斉次比 T_j/T_i へ送る。
規約：KST Def3.1。使われ方：古典チャートの明示的な多項式表示。 -/
def universalChartToClassical (i : I) : UniversalChart i →+* UniversalClassicalChart i :=
  MvPolynomial.eval₂Hom (Int.castRingHom _)
    (fun j => match j with
      | none => _root_.SerrePositivity.AlgebraicGeometry.chartBaseMap _ (universalCenterGenerator i) (MvPolynomial.X i)
      | some j => _root_.SerrePositivity.AlgebraicGeometry.chartRatio _ (universalCenterGenerator i)
          (universalCenterGenerator j.val))

omit [DecidableEq I] in
/-- 概要：逆代入は radial 変数を基底の pivot へ送る。
方針：多項式評価の生成元公式。
規約：KST Def3.1。使われ方：基底上の相互逆の確認。 -/
@[simp] theorem universalChartToClassical_radial (i : I) :
    universalChartToClassical i (radialCoordinate i) =
      _root_.SerrePositivity.AlgebraicGeometry.chartBaseMap _ (universalCenterGenerator i) (MvPolynomial.X i) :=
  MvPolynomial.eval₂Hom_X' _ _ none

omit [DecidableEq I] in
/-- 概要：逆代入は比変数を Rees チャートの斉次比へ送る。
方針：多項式評価の生成元公式。
規約：KST Def3.1。使われ方：基底上の相互逆の確認。 -/
@[simp] theorem universalChartToClassical_ratio (i : I) (j : ChartIndex i) :
    universalChartToClassical i (MvPolynomial.X (some j)) =
      _root_.SerrePositivity.AlgebraicGeometry.chartRatio _ (universalCenterGenerator i) (universalCenterGenerator j.val) :=
  MvPolynomial.eval₂Hom_X' _ _ (some j)

/-- 概要：逆代入と普遍構造射の合成は Rees チャートの基底構造射。
方針：独立変数 T_j で pivot と非 pivot を分け、比の分母消去を使う。
規約：KST Def3.1。使われ方：古典チャート上の逆元律と基底保存。 -/
theorem universalChartToClassical_comp_base (i : I) :
    (universalChartToClassical i).comp (universalBaseMap i).toRingHom =
      _root_.SerrePositivity.AlgebraicGeometry.chartBaseMap _ (universalCenterGenerator i) := by
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
      exact _root_.SerrePositivity.AlgebraicGeometry.chartBaseMap_mul_ratio (universalCenter (I := I))
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
  apply _root_.SerrePositivity.AlgebraicGeometry.chart_hom_ext_of_regular (universalCenter (I := I))
    (_root_.SerrePositivity.AlgebraicGeometry.chartBaseMap _ (universalCenterGenerator i)) (universalCenterGenerator i)
    (_root_.SerrePositivity.AlgebraicGeometry.chartBaseMap_mem_nonZeroDivisors _ _)
  · intro p
    change universalChartToClassical i (universalClassicalToChart i
      (_root_.SerrePositivity.AlgebraicGeometry.chartBaseMap _ (universalCenterGenerator i) p)) = _
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

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite KST "Def 3.1" (partial := component) "仮定：多項式基底の普遍チャートと有限列（Lean が強い）。結論：チャート上の古典的商表示と Koszul の底変換の同型。全導来スキームの正方形は未接続（Lean が弱い）。"] _root_.SerrePositivity.KST.DerivedBlowup.universalClassicalChartEquiv
attribute [cite KST "Eq (1.7)" (partial := component) "仮定：有限列の普遍チャート、または有限生成中心の正の冪の通常ブローアップ（Lean が強い）。結論：局所チャート同定と通常の冪比較を供給するが、原典の普遍正則列の厚化付きの全塔は含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.DerivedBlowup.universalClassicalChartEquiv
attribute [cite KST "Eq (3.1)" (partial := component) "仮定：多項式基底の普遍チャートと有限列（Lean が強い）。結論：チャート上の古典的商表示と Koszul の底変換の同型。全導来スキームの正方形は未接続（Lean が弱い）。"] _root_.SerrePositivity.KST.DerivedBlowup.universalClassicalChartEquiv
attribute [cite KST "Lemma 3.5" (partial := component) "仮定：指定普遍チャートとその底変換（Lean が強い）。結論：例外因子の dg チャートの比較と古典チャートの表示。正則列を保つ射全般の通常ブローアップと全厚化の導来 Cartesian 性は含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.DerivedBlowup.universalClassicalChartEquiv
attribute [cite LT "Eq (22)" (partial := component) "仮定：指定普遍多項式模型のチャートと係数環の有限列（Lean が強い）。結論：局所的な通常チャートと導来 Koszul の底変換を比較。全 qcqs スキームのブローアップ四角形は含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.DerivedBlowup.universalClassicalChartEquiv
attribute [cite LT "Eq (23)" (partial := component) "仮定：指定普遍多項式模型のチャートと係数環の有限列（Lean が強い）。結論：局所的な通常チャートと導来 Koszul の底変換を比較。全 qcqs スキームのブローアップ四角形は含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.DerivedBlowup.universalClassicalChartEquiv
