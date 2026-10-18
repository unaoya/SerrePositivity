module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapCocycle

/-!
概要：KST §3.1 の有限重なりでの制限射と pivot 変更の可換性。
方針：座標単元とその逆の自然性を計算し、局所化の外延性を使う。
規約：有限集合 T⊆U に沿って比較する。
使われ方：非空有限重なり全体の係数環関手の構成。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

variable (R : Type u) [CommRing R] {I : Type v} [DecidableEq I]

/-- 概要：有限重なりへの制限は座標単元を同じ座標単元へ送る。
方針：単元の値をチャート座標へ戻して構造射の可換性を使う。
規約：KST §3.1。使われ方：制限と規格化の可換性。 -/
theorem finiteOverlapRestriction_unitsMap (i j : I) {T U : Finset I}
    (h : T ⊆ U) (hj : j ∈ T) :
    Units.map (finiteOverlapRestriction R i h).toMonoidHom (finiteOverlapUnit R i T j hj) =
      finiteOverlapUnit R i U j (h hj) := by
  apply Units.ext
  change finiteOverlapRestriction R i h (↑(finiteOverlapUnit R i T j hj)) = _
  rw [finiteOverlapUnit_val, finiteOverlapRestriction_base, finiteOverlapUnit_val]

/-- 概要：有限重なりへの制限は逆座標単元を保つ。
方針：単元写像の逆保存と座標単元の自然性を使う。
規約：KST §3.1。使われ方：制限と pivot 変更の自然性。 -/
theorem finiteOverlapRestriction_unitInv (i j : I) {T U : Finset I}
    (h : T ⊆ U) (hj : j ∈ T) :
    finiteOverlapRestriction R i h (↑(finiteOverlapUnit R i T j hj)⁻¹) =
      ↑(finiteOverlapUnit R i U j (h hj))⁻¹ := by
  change (finiteOverlapRestriction R i h).toMonoidHom
    (↑(finiteOverlapUnit R i T j hj)⁻¹) = _
  rw [← Units.coe_map_inv (finiteOverlapRestriction R i h).toMonoidHom
    (finiteOverlapUnit R i T j hj), finiteOverlapRestriction_unitsMap]

/-- 概要：有限集合の拡大と pivot 変更は座標上で可換。
方針：規格化の積公式と逆座標単元の自然性を使う。
規約：KST §3.1。使われ方：局所化全体の自然性。 -/
theorem finiteOverlapPivotMap_restriction_coordinate (i k : I) {T U : Finset I}
    (h : T ⊆ U) (hk : k ∈ T) (j : I) :
    finiteOverlapRestriction R i h (finiteOverlapPivotMap R i k T hk
      (finiteOverlapInclusion R k T (chartCoordinate R k j))) =
    finiteOverlapPivotMap R i k U (h hk) (finiteOverlapRestriction R k h
      (finiteOverlapInclusion R k T (chartCoordinate R k j))) := by
  rw [finiteOverlapPivotMap_base, finiteOverlapTransitionBase_coordinate, map_mul,
    finiteOverlapRestriction_base, finiteOverlapRestriction_unitInv,
    finiteOverlapRestriction_base, finiteOverlapPivotMap_base,
    finiteOverlapTransitionBase_coordinate]

/-- 概要：有限重なりの制限と pivot 変更は環射として可換。
方針：局所化と多項式環の外延性で座標上の可換性へ帰着する。
規約：KST §3.1。使われ方：全有限重なりの係数環図式の合成。 -/
theorem finiteOverlapPivotMap_restriction (i k : I) {T U : Finset I}
    (h : T ⊆ U) (hk : k ∈ T) :
    (finiteOverlapRestriction R i h).comp (finiteOverlapPivotMap R i k T hk) =
      (finiteOverlapPivotMap R i k U (h hk)).comp (finiteOverlapRestriction R k h) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (finiteOverlapDenominator R k T))
  ext j
  simpa only [chartCoordinate_other, AlgHom.comp_apply,
    finiteOverlapInclusion, IsScalarTower.toAlgHom, Algebra.algHom] using
      finiteOverlapPivotMap_restriction_coordinate R i k h hk j.val

/-- 概要：pivot 自身の座標単元は1。
方針：単元の外延性で pivot 座標の像を計算する。
規約：KST §3.1。使われ方：同じ pivot への変更が恒等であること。 -/
@[simp] theorem finiteOverlapUnit_self (i : I) (T : Finset I) (hi : i ∈ T) :
    finiteOverlapUnit R i T i hi = 1 := by
  apply Units.ext
  simp

/-- 概要：同じ pivot への変更は恒等射。
方針：規格化単元が1なので、局所化の外延性により座標ごとに確認する。
規約：KST §3.1。使われ方：全有限重なりの関手の恒等律。 -/
theorem finiteOverlapPivotMap_self (i : I) (T : Finset I) (hi : i ∈ T) :
    finiteOverlapPivotMap R i i T hi = AlgHom.id R (FiniteOverlapRing R i T) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (finiteOverlapDenominator R i T))
  ext j
  have hc := finiteOverlapPivotMap_base R i i T hi (chartCoordinate R i j.val)
  rw [finiteOverlapTransitionBase_coordinate, finiteOverlapUnit_self] at hc
  simpa only [chartCoordinate_other, AlgHom.comp_apply, AlgHom.id_apply,
    inv_one, Units.val_one, mul_one,
    finiteOverlapInclusion, IsScalarTower.toAlgHom, Algebra.algHom] using hc

end SerrePositivity.KST.DerivedBlowup
