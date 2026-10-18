module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapTransitions

/-!
概要：KST §3.1 の全有限重なりでの pivot 変更の cocycle。
方針：各指定座標の単元の像を求め、二度の規格化を一度にまとめる。
規約：三つの pivot は同じ有限集合に属する。
使われ方：全有限重なりの係数環図式の合成整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

variable (R : Type u) [CommRing R] {I : Type v} [DecidableEq I]

/-- 概要：有限 pivot 変更は各指定座標単元を規格化した単元へ送る。
方針：単元の外延性で値を比較する。
規約：KST §3.1。使われ方：逆単元の像と cocycle の計算。 -/
theorem finiteOverlapPivotMap_unitsMap (i k l : I) (T : Finset I)
    (hk : k ∈ T) (hl : l ∈ T) :
    Units.map (finiteOverlapPivotMap R i k T hk).toMonoidHom
        (finiteOverlapUnit R k T l hl) =
      finiteOverlapUnit R i T l hl * (finiteOverlapUnit R i T k hk)⁻¹ := by
  apply Units.ext
  change finiteOverlapPivotMap R i k T hk (↑(finiteOverlapUnit R k T l hl)) = _
  rw [finiteOverlapUnit_val, finiteOverlapPivotMap_base,
    finiteOverlapTransitionBase_coordinate, Units.val_mul, finiteOverlapUnit_val]

/-- 概要：任意の指定座標の逆単元は規格化単元の逆へ送られる。
方針：単元写像の逆保存と単元の像の公式を使う。
規約：KST §3.1。使われ方：pivot の三重 cocycle。 -/
theorem finiteOverlapPivotMap_general_unitInv (i k l : I) (T : Finset I)
    (hk : k ∈ T) (hl : l ∈ T) :
    finiteOverlapPivotMap R i k T hk (↑(finiteOverlapUnit R k T l hl)⁻¹) =
      ↑(finiteOverlapUnit R i T k hk) * ↑(finiteOverlapUnit R i T l hl)⁻¹ := by
  change (finiteOverlapPivotMap R i k T hk).toMonoidHom
    (↑(finiteOverlapUnit R k T l hl)⁻¹) = _
  rw [← Units.coe_map_inv (finiteOverlapPivotMap R i k T hk).toMonoidHom
    (finiteOverlapUnit R k T l hl), finiteOverlapPivotMap_unitsMap]
  simp only [mul_inv_rev, inv_inv, Units.val_mul]

/-- 概要：有限重なりの二度の pivot 変更は座標上で直接変更に等しい。
方針：座標像を二回代入し、中間 pivot の単元を消去する。
規約：KST §3.1。使われ方：全有限重なりの環射の cocycle。 -/
theorem finiteOverlapPivotMap_cocycle_coordinate (i k l : I) (T : Finset I)
    (hk : k ∈ T) (hl : l ∈ T) (j : I) :
    finiteOverlapPivotMap R i k T hk (finiteOverlapPivotMap R k l T hl
      (finiteOverlapInclusion R l T (chartCoordinate R l j))) =
    finiteOverlapPivotMap R i l T hl (finiteOverlapInclusion R l T (chartCoordinate R l j)) := by
  rw [finiteOverlapPivotMap_base, finiteOverlapTransitionBase_coordinate, map_mul,
    finiteOverlapPivotMap_base, finiteOverlapTransitionBase_coordinate,
    finiteOverlapPivotMap_general_unitInv, finiteOverlapPivotMap_base,
    finiteOverlapTransitionBase_coordinate]
  calc
    _ = finiteOverlapInclusion R i T (chartCoordinate R i j) *
        ((↑(finiteOverlapUnit R i T k hk)⁻¹ * ↑(finiteOverlapUnit R i T k hk)) *
          ↑(finiteOverlapUnit R i T l hl)⁻¹) := by simp only [mul_assoc]
    _ = _ := by rw [(finiteOverlapUnit R i T k hk).inv_mul, one_mul]

/-- 概要：全有限重なり上で pivot 変更射は三重 cocycle を満たす。
方針：局所化と多項式の外延性で座標公式へ帰着する。
規約：KST §3.1。使われ方：全有限 Čech の環図式の合成律。 -/
theorem finiteOverlapPivotMap_cocycle (i k l : I) (T : Finset I)
    (hk : k ∈ T) (hl : l ∈ T) :
    (finiteOverlapPivotMap R i k T hk).comp (finiteOverlapPivotMap R k l T hl) =
      finiteOverlapPivotMap R i l T hl := by
  apply IsLocalization.algHom_ext (Submonoid.powers (finiteOverlapDenominator R l T))
  ext j
  simpa only [chartCoordinate_other, AlgHom.comp_apply,
    finiteOverlapInclusion, IsScalarTower.toAlgHom, Algebra.algHom] using
      finiteOverlapPivotMap_cocycle_coordinate R i k l T hk hl j.val

end SerrePositivity.KST.DerivedBlowup
