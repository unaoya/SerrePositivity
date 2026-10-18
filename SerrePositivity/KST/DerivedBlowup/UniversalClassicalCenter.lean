module

public import SerrePositivity.KST.DerivedBlowup.UniversalPresentationEquiv
public import SerrePositivity.KST.SchemeLemmas.ChartRegularLift

/-!
概要：KST Def3.1 の普遍中心を L7 の古典 Rees–Proj blowup の入力に接続する。
方針：普遍変数の生成イデアルのチャートでの像が正則な radial 座標で生成されることを示す。
規約：L7 の構成は読み取り専用で使用し、比較宣言を L5 に置く。
使われ方：通常の普遍多項式チャートと Rees–Proj の標準チャートの同型。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe v

namespace SerrePositivity.KST.DerivedBlowup

variable {I : Type v} [DecidableEq I]

/-- 概要：普遍 affine blowup の中心イデアル。
方針：全ての独立変数 T_j の span を取る。
規約：KST Def3.1。使われ方：L7 の Rees–Proj チャートの中心。 -/
def universalCenter : Ideal (UniversalBase I) := Ideal.span (Set.range MvPolynomial.X)

/-- 概要：普遍中心の指定生成元。
方針：T_i の span への所属を添える。
規約：KST Def3.1。使われ方：Rees–Proj の次数一チャートを指定する。 -/
def universalCenterGenerator (i : I) : universalCenter (I := I) :=
  ⟨MvPolynomial.X i, Ideal.subset_span ⟨i, rfl⟩⟩

/-- 概要：普遍チャートでは中心の像は radial 座標により生成される。
方針：各 T_j の像は T_i S_j であり、pivot 自身は T_i に写る。
規約：KST Def3.1。使われ方：L7 の正則チャート持ち上げの単項性条件。 -/
theorem universalCenter_image (i : I) :
    (universalCenter (I := I)).map (universalBaseMap i).toRingHom =
      Ideal.span {radialCoordinate i} := by
  rw [universalCenter, Ideal.map_span]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro z ⟨p, ⟨j, rfl⟩, rfl⟩
    change universalBaseMap i (MvPolynomial.X j) ∈ _
    rw [universalBaseMap_X]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
  · apply Ideal.span_le.mpr
    rintro z (rfl : z = radialCoordinate i)
    exact Ideal.subset_span ⟨MvPolynomial.X i, ⟨i, rfl⟩, by simp⟩

/-- 概要：普遍 radial 座標は非零因子。
方針：整数上の自由多項式環の整域性と変数の非零性を使う。
規約：KST Def3.1。使われ方：L7 の正則チャート持ち上げの正則性条件。 -/
theorem universalCenter_pivot_regular (i : I) :
    universalBaseMap i (universalCenterGenerator i).val ∈ nonZeroDivisors (UniversalChart i) := by
  change universalBaseMap i (MvPolynomial.X i) ∈ _
  rw [universalBaseMap_pivot]
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (MvPolynomial.X_ne_zero none)

/-- 概要：L7 の Rees–Proj の普遍中心の標準チャート環。
方針：普遍中心の pivot を L7 の BlowupChartRing に渡す。
規約：KST Def3.1。使われ方：普遍自由多項式チャートとの比較の始域。 -/
abbrev UniversalClassicalChart (i : I) :=
  SchemeLemmas.BlowupChartRing (universalCenter (I := I)) (universalCenterGenerator i)

/-- 概要：Rees–Proj の普遍チャートから自由多項式チャートへの環射。
方針：中心像の正則単項性から L7 の実際の chartRegularLift を構成する。
規約：KST Def3.1。使われ方：普遍チャートの古典模型との同型。 -/
def universalClassicalToChart (i : I) : UniversalClassicalChart i →+* UniversalChart i :=
  SchemeLemmas.chartRegularLift _ (universalBaseMap i).toRingHom _
    (universalCenter_pivot_regular i)
    (by simpa [universalCenterGenerator] using universalCenter_image i)

/-- 概要：古典チャート比較射は普遍基底の係数を保つ。
方針：L7 の正則持ち上げの基底保存公式を使う。
規約：KST Def3.1。使われ方：逆写像の生成元計算。 -/
@[simp] theorem universalClassicalToChart_base (i : I) (p : UniversalBase I) :
    universalClassicalToChart i
      (SchemeLemmas.chartBaseMap _ (universalCenterGenerator i) p) = universalBaseMap i p :=
  SchemeLemmas.chartRegularLift_base _ _ _ _ _ p

end SerrePositivity.KST.DerivedBlowup
