module

public import SerrePositivity.KST.DerivedBlowup.Overlaps
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
概要：KST §3.1 の全有限チャート重なりの係数環を構成する。
方針：固定チャートの有限個の比座標の積を可逆化する。
規約：空の添字集合も許し、その分母は1。導来関係式は後で外積模型に与える。
使われ方：二重・三重に限らない有限 Čech 図式の係数環。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

variable (R : Type u) [CommRing R] {I : Type v} [DecidableEq I]

/-- 概要：固定チャートで有限個の比座標を可逆化するための分母。
方針：有限集合に属する座標の積を取る。
規約：KST §3.1。使われ方：全有限重なりの Away 表示。 -/
def finiteOverlapDenominator (i : I) (T : Finset I) : ChartRing R i :=
  ∏ j ∈ T, chartCoordinate R i j

/-- 概要：固定チャートで T の全座標を可逆化した重なり環。
方針：座標積に関する Away 局所化を使う。
規約：KST §3.1。使われ方：有限 Čech 図式の局所係数環。 -/
abbrev FiniteOverlapRing (i : I) (T : Finset I) :=
  Localization.Away (finiteOverlapDenominator R i T)

/-- 概要：チャートから有限重なりへの構造射。
方針：局所化の係数代数射を使う。
規約：KST Def3.1。使われ方：座標と Koszul 関係式の像。 -/
def finiteOverlapInclusion (i : I) (T : Finset I) :
    ChartRing R i →ₐ[R] FiniteOverlapRing R i T :=
  IsScalarTower.toAlgHom R (ChartRing R i) (FiniteOverlapRing R i T)

/-- 概要：T に属する各比座標は有限重なりで単元となる。
方針：分母の積が単元であることから各因子の単元性を取り出す。
規約：KST §3.1。使われ方：pivot 変更とさらに小さい開集合への制限。 -/
theorem finiteOverlap_coordinate_isUnit (i : I) (T : Finset I) (j : I) (hj : j ∈ T) :
    IsUnit (finiteOverlapInclusion R i T (chartCoordinate R i j)) := by
  have hp := IsLocalization.Away.algebraMap_isUnit (S := FiniteOverlapRing R i T)
    (finiteOverlapDenominator R i T)
  change IsUnit (algebraMap (ChartRing R i) (FiniteOverlapRing R i T)
    (finiteOverlapDenominator R i T)) at hp
  simp only [finiteOverlapDenominator, map_prod] at hp
  exact IsUnit.prod_iff.mp hp j hj

/-- 概要：有限重なり上の指定座標の実際の単元。
方針：証明した単元性から単元を取り出す。
規約：KST §3.1。使われ方：O(m) の推移とチャート基底変換。 -/
def finiteOverlapUnit (i : I) (T : Finset I) (j : I) (hj : j ∈ T) :
    (FiniteOverlapRing R i T)ˣ :=
  (finiteOverlap_coordinate_isUnit R i T j hj).unit

/-- 概要：有限重なりの推移単元の値は座標の像。
方針：IsUnit.unit_spec を使う。
規約：KST Def3.1。使われ方：抽象単元版の規格化公式の適用。 -/
@[simp] theorem finiteOverlapUnit_val (i : I) (T : Finset I) (j : I) (hj : j ∈ T) :
    ↑(finiteOverlapUnit R i T j hj) = finiteOverlapInclusion R i T (chartCoordinate R i j) :=
  (finiteOverlap_coordinate_isUnit R i T j hj).unit_spec

/-- 概要：T⊆U なら T の座標積は U の重なりで単元。
方針：各因子の単元性を積にまとめる。
規約：KST §3.1。使われ方：有限重なりの制限射の局所化延長。 -/
theorem finiteOverlap_denominator_isUnit (i : I) {T U : Finset I} (h : T ⊆ U) :
    IsUnit (finiteOverlapInclusion R i U (finiteOverlapDenominator R i T)) := by
  simp only [finiteOverlapDenominator, map_prod]
  exact IsUnit.prod_iff.mpr (fun j hj => finiteOverlap_coordinate_isUnit R i U j (h hj))

/-- 概要：有限重なりの添字拡大に沿う制限射。
方針：小さい集合の座標積が目標で単元であることを局所化の普遍性へ渡す。
規約：KST §3.1、環射は T から U へ向かう。
使われ方：有限 Čech の係数環図式。 -/
def finiteOverlapRestriction (i : I) {T U : Finset I} (h : T ⊆ U) :
    FiniteOverlapRing R i T →ₐ[R] FiniteOverlapRing R i U :=
  IsLocalization.Away.liftAlgHom (finiteOverlapDenominator R i T)
    (f := finiteOverlapInclusion R i U) (finiteOverlap_denominator_isUnit R i h)

/-- 概要：有限重なりの制限は元のチャート上の構造射と可換。
方針：Away lift の生成元上の公式。
規約：KST §3.1。使われ方：制限射の恒等則と合成則。 -/
@[simp] theorem finiteOverlapRestriction_base (i : I) {T U : Finset I} (h : T ⊆ U)
    (p : ChartRing R i) :
    finiteOverlapRestriction R i h (finiteOverlapInclusion R i T p) =
      finiteOverlapInclusion R i U p :=
  IsLocalization.Away.lift_eq _ (finiteOverlap_denominator_isUnit R i h) p

/-- 概要：同じ有限重なりへの制限は恒等。
方針：局所化の外延性で元のチャート上へ帰着する。
規約：KST §3.1。使われ方：有限重なり環の関手性。 -/
theorem finiteOverlapRestriction_refl (i : I) (T : Finset I) :
    finiteOverlapRestriction R i (T := T) (Finset.Subset.refl T) =
      AlgHom.id R (FiniteOverlapRing R i T) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (finiteOverlapDenominator R i T))
  apply AlgHom.ext
  intro p
  change finiteOverlapRestriction R i (Finset.Subset.refl T)
    (finiteOverlapInclusion R i T p) = finiteOverlapInclusion R i T p
  exact finiteOverlapRestriction_base R i _ p

/-- 概要：有限重なりへの制限は合成を保つ。
方針：局所化の外延性と構造射との可換性を使う。
規約：KST §3.1。使われ方：全有限 Čech の係数環図式の合成律。 -/
theorem finiteOverlapRestriction_comp (i : I) {T U V : Finset I}
    (h : T ⊆ U) (g : U ⊆ V) :
    (finiteOverlapRestriction R i g).comp (finiteOverlapRestriction R i h) =
      finiteOverlapRestriction R i (h.trans g) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (finiteOverlapDenominator R i T))
  apply AlgHom.ext
  intro p
  change finiteOverlapRestriction R i g
      (finiteOverlapRestriction R i h (finiteOverlapInclusion R i T p)) =
    finiteOverlapRestriction R i (h.trans g) (finiteOverlapInclusion R i T p)
  rw [finiteOverlapRestriction_base, finiteOverlapRestriction_base,
    finiteOverlapRestriction_base]

end SerrePositivity.KST.DerivedBlowup
