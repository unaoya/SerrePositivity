module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.ChartAlgebra
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
概要：KST §5、Stacks 0815 の境界外でのチャート元の可逆性と自由化開集合への係数写像。
方針：中心に入る境界の冪を使い、チャート元とその分数表示の係数を単元にする。
規約：境界元の正則性は可逆性の計算には不要。
使われ方：境界外で平坦な加群を自由な局所化から基底変更する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R : Type*} [CommRing R] (I : Ideal R) (a : I) (f : R)

/--
概要：中心が境界の冪を含めば、チャート元は境界を可逆化すると単元になる。
方針：境界の冪がチャート元の倍であることと単元の約数の単元性を使う。
規約：KST §5、Stacks 0815、境界の冪の所属を明示する。
使われ方：境界外のチャートから元の自由な基本開への写像。
-/
theorem chartBoundaryAway_center_isUnit (n : ℕ) (hn : f ^ n ∈ I) :
    IsUnit (algebraMap (BlowupChartRing I a) (Localization.Away (chartBaseMap I a f))
      (chartBaseMap I a a.val)) := by
  have hdvd : chartBaseMap I a a.val ∣ chartBaseMap I a f ^ n := by
    apply Ideal.mem_span_singleton.mp
    rw [← chart_map_ideal_eq_span, ← map_pow]
    exact Ideal.mem_map_of_mem _ hn
  apply isUnit_of_dvd_unit (map_dvd _ hdvd)
  simpa only [map_pow] using
    ((IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away (chartBaseMap I a f)) (chartBaseMap I a f)).pow n)

/--
概要：境界外の基礎環から境界外のチャート環への係数準同型。
方針：境界元の可逆性で一元局所化の普遍性を使う。
規約：KST §5、Stacks 0815、二つの局所化環を区別する。
使われ方：自由化被覆の係数をチャートの境界外へ送る。
-/
def chartBoundaryBaseLift : Localization.Away f →+*
    Localization.Away (chartBaseMap I a f) :=
  IsLocalization.Away.lift f (g :=
    (algebraMap (BlowupChartRing I a) (Localization.Away (chartBaseMap I a f))).comp
      (chartBaseMap I a)) (IsLocalization.Away.algebraMap_isUnit (chartBaseMap I a f))

/--
概要：境界外の係数準同型は元の基礎環の係数を保存する。
方針：局所化の持ち上げの公式を使う。
規約：KST §5、Stacks 0815、チャート環への写像を明示する。
使われ方：分子と境界外の元の像の比較。
-/
@[simp] theorem chartBoundaryBaseLift_base (r : R) :
    chartBoundaryBaseLift I a f (algebraMap R (Localization.Away f) r) =
      algebraMap (BlowupChartRing I a) (Localization.Away (chartBaseMap I a f))
        (chartBaseMap I a r) := IsLocalization.Away.lift_eq _ _ _

/--
概要：チャート元が自由化係数の分子なら、その係数の像は境界外のチャートで単元。
方針：係数と分子が単元倍であることを係数準同型で送り、チャート元の単元性を使う。
規約：KST §5、Stacks 0815、分子には標準の選択を使う。
使われ方：自由化する基本開への係数写像の持ち上げ。
-/
theorem chartBoundaryBaseLift_isUnit_of_numerator (n : ℕ) (hn : f ^ n ∈ I)
    (x : Localization.Away f) (hx : (IsLocalization.Away.sec f x).1 = a.val) :
    IsUnit (chartBoundaryBaseLift I a f x) := by
  have hu : IsUnit (chartBoundaryBaseLift I a f
      (algebraMap R (Localization.Away f) (IsLocalization.Away.sec f x).1)) := by
    rw [chartBoundaryBaseLift_base, hx]
    exact chartBoundaryAway_center_isUnit I a f n hn
  exact ((IsLocalization.Away.associated_sec_fst f x).map
    (chartBoundaryBaseLift I a f)).isUnit_iff.mp hu

/--
概要：境界外のチャートから自由化基本開への環の反変写像。
方針：自由化係数の像の可逆性でさらに局所化の普遍性を使う。
規約：KST §5、Stacks 0815、分子が指定されたチャート元と一致すると仮定する。
使われ方：自由化した加群をチャートの境界外へ基底変更する。
-/
def chartBoundaryFreeOpenLift (n : ℕ) (hn : f ^ n ∈ I)
    (x : Localization.Away f) (hx : (IsLocalization.Away.sec f x).1 = a.val) :
    Localization.Away x →+* Localization.Away (chartBaseMap I a f) :=
  IsLocalization.Away.lift x (chartBoundaryBaseLift_isUnit_of_numerator I a f n hn x hx)

/--
概要：自由化基本開からの係数写像は境界外の基礎環の係数を保存する。
方針：二度目の局所化の持ち上げの公式を使う。
規約：KST §5、Stacks 0815、境界外の環からの係数写像を明示する。
使われ方：二段の基底変更のスカラー塔の交換式。
-/
@[simp] theorem chartBoundaryFreeOpenLift_base (n : ℕ) (hn : f ^ n ∈ I)
    (x : Localization.Away f) (hx : (IsLocalization.Away.sec f x).1 = a.val)
    (y : Localization.Away f) :
    chartBoundaryFreeOpenLift I a f n hn x hx
      (algebraMap (Localization.Away f) (Localization.Away x) y) =
      chartBoundaryBaseLift I a f y := IsLocalization.Away.lift_eq _ _ _

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
