module

public import SerrePositivity.KST.DerivedBlowup.Charts
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
概要：KST Def3.1・Lemma3.6 のチャート重なりを実際の局所化環として構成する。
方針：S_k^(i) を可逆化し、逆方向の S_i^(k) をその逆単元へ送る。
規約：通常の多項式係数環の重なり。導来 Koszul 商への延長とは区別する。
使われ方：O(1) の推移単元と Koszul cdga の基底変換の係数を供給する。
-/

@[expose] public noncomputable section

universe u v

namespace SerrePositivity.KST.DerivedBlowup

variable (R : Type u) [CommRing R] {I : Type v} [DecidableEq I]

/-- 概要：i チャートの k 座標を可逆化した環。方針：Away 局所化を使う。
規約：KST §3.1 の U_i∩U_k。使われ方：貼り合わせの環射の値域。 -/
abbrev OverlapRing (i k : I) := Localization.Away (chartCoordinate R i k)

/-- 概要：チャート環から重なりへの構造射。方針：局所化の代数構造。
規約：KST Def3.1。使われ方：座標・Koszul 関係式を重なりに移す。 -/
def overlapInclusion (i k : I) : ChartRing R i →ₐ[R] OverlapRing R i k :=
  IsScalarTower.toAlgHom R (ChartRing R i) (OverlapRing R i k)

/-- 概要：可逆化された座標の実際の単元。方針：Away の単元性から取り出す。
規約：KST §3.1、O(1) の推移単元 S_k^(i)。使われ方：逆座標と cocycle。 -/
def overlapUnit (i k : I) : (OverlapRing R i k)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := OverlapRing R i k)
    (chartCoordinate R i k)).unit

/-- 概要：推移単元の値は元の座標の局所化像。方針：IsUnit.unit_spec。
規約：KST Def3.1。使われ方：抽象単元版の座標定理を実際の重なりへ適用する。 -/
@[simp] theorem overlapUnit_val (i k : I) :
    ↑(overlapUnit R i k) = overlapInclusion R i k (chartCoordinate R i k) :=
  (IsLocalization.Away.algebraMap_isUnit (S := OverlapRing R i k)
    (chartCoordinate R i k)).unit_spec

/-- 概要：k チャートから i 側の重なりへの環射。方針：可逆化した k 座標で規格化。
規約：KST §3.1、S_j^(k)=S_j^(i)/S_k^(i)。使われ方：重なり間の局所化環射を延長する。 -/
def overlapTransitionBase (i k : I) : ChartRing R k →ₐ[R] OverlapRing R i k :=
  chartTransition i k (overlapInclusion R i k) (overlapUnit R i k)

/-- 概要：重なり上の環射の座標公式。方針：単元の値を座標に同定する。
規約：KST Def3.1。使われ方：普遍チャートと Koszul 関係式の貼り合わせ。 -/
@[simp] theorem overlapTransitionBase_coordinate (i k j : I) :
    overlapTransitionBase R i k (chartCoordinate R k j) =
      overlapInclusion R i k (chartCoordinate R i j) * ↑(overlapUnit R i k)⁻¹ :=
  chartTransition_coordinate i k j _ _ (overlapUnit_val R i k)

/-- 概要：逆側の pivot 座標は推移単元の逆元になる。方針：元の pivot は1。
規約：KST §3.1、S_i^(k)=1/S_k^(i)。使われ方：反対側の局所化を延長する単元性。 -/
@[simp] theorem overlapTransitionBase_reversePivot (i k : I) :
    overlapTransitionBase R i k (chartCoordinate R k i) = ↑(overlapUnit R i k)⁻¹ := by
  rw [overlapTransitionBase_coordinate, chartCoordinate_self, map_one, one_mul]

/-- 概要：二つの局所化環の間の実際の環射。方針：逆座標の単元性によって延長。
規約：KST §3.1 の標準重なり。使われ方：導来チャートの貼り合わせの係数環。 -/
def overlapMap (i k : I) : OverlapRing R k i →ₐ[R] OverlapRing R i k :=
  IsLocalization.Away.liftAlgHom (chartCoordinate R k i)
    (f := overlapTransitionBase R i k) (by
      rw [overlapTransitionBase_reversePivot]
      exact (overlapUnit R i k)⁻¹.isUnit)

/-- 概要：重なり環射は局所化前のチャート射を延長する。方針：Away の lift_eq。
規約：KST Def3.1。使われ方：局所化環射の逆写像と cocycle の証明。 -/
@[simp] theorem overlapMap_base (i k : I) (p : ChartRing R k) :
    overlapMap R i k (overlapInclusion R k i p) = overlapTransitionBase R i k p := by
  apply IsLocalization.Away.lift_eq
  change IsUnit (overlapTransitionBase R i k (chartCoordinate R k i))
  rw [overlapTransitionBase_reversePivot]
  exact (overlapUnit R i k)⁻¹.isUnit

/-- 概要：重なり環射は反対側の推移単元を逆元へ送る。
方針：単元の値を座標へ戻し lift の生成元計算を使う。
規約：KST §3.1。使われ方：重なりの二つの環射が互いに逆であることの検証。 -/
@[simp] theorem overlapMap_unit (i k : I) :
    overlapMap R i k (↑(overlapUnit R k i)) = ↑(overlapUnit R i k)⁻¹ := by
  rw [overlapUnit_val, overlapMap_base, overlapTransitionBase_reversePivot]

/-- 概要：逆推移単元の像は元の推移単元。方針：環射が逆元律を保つことを使う。
規約：KST §3.1、整域性は不要。使われ方：局所化環射の逆写像の計算。 -/
@[simp] theorem overlapMap_unitInv (i k : I) :
    overlapMap R i k (↑(overlapUnit R k i)⁻¹) = ↑(overlapUnit R i k) := by
  have h := congrArg (overlapMap R i k) (overlapUnit R k i).mul_inv
  rw [map_mul, map_one, overlapMap_unit] at h
  calc
    _ = (↑(overlapUnit R i k) * ↑(overlapUnit R i k)⁻¹) *
        overlapMap R i k (↑(overlapUnit R k i)⁻¹) := by
      rw [(overlapUnit R i k).mul_inv, one_mul]
    _ = _ := by rw [mul_assoc, h, mul_one]

/-- 概要：往復の環射は全てのチャート座標を保つ。
方針：二回の規格化で推移単元とその逆元を消去する。
規約：KST Def3.1。使われ方：局所化の普遍性による重なり同型の証明。 -/
theorem overlapMap_roundtrip_coordinate (i k j : I) :
    overlapMap R i k (overlapMap R k i
      (overlapInclusion R i k (chartCoordinate R i j))) =
        overlapInclusion R i k (chartCoordinate R i j) := by
  rw [overlapMap_base, overlapTransitionBase_coordinate, map_mul,
    overlapMap_base, overlapTransitionBase_coordinate, overlapMap_unitInv]
  rw [mul_assoc, (overlapUnit R i k).inv_mul, mul_one]

/-- 概要：チャート重なり間の環射を往復すると恒等になる。
方針：局所化と多項式環の普遍性で座標の往復公式へ帰着する。
規約：KST Def3.1、零因子のある基底も許す。使われ方：重なり環の代数同型。 -/
theorem overlapMap_comp (i k : I) :
    (overlapMap R i k).comp (overlapMap R k i) = AlgHom.id R (OverlapRing R i k) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (chartCoordinate R i k))
  ext j
  simpa only [chartCoordinate_other, AlgHom.comp_apply, AlgHom.id_apply,
    overlapInclusion, IsScalarTower.toAlgHom, Algebra.algHom] using
    overlapMap_roundtrip_coordinate R i k j.val

/-- 概要：標準チャートの二つの重なり環の同型。
方針：座標規格化とその逆を局所化へ延長した環射を使う。
規約：KST §3.1 の貼り合わせ、導来商への延長は別の段階。
使われ方：Koszul 基底変換を比較する共通係数環の選択。 -/
def overlapEquiv (i k : I) : OverlapRing R k i ≃ₐ[R] OverlapRing R i k :=
  AlgEquiv.ofAlgHom (overlapMap R i k) (overlapMap R k i)
    (overlapMap_comp R i k) (overlapMap_comp R k i)

end SerrePositivity.KST.DerivedBlowup
