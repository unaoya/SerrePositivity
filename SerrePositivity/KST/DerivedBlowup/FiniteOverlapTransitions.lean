module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlaps

/-!
概要：KST §3.1 の任意有限重なりで pivot を変える環射。
方針：新しい pivot 座標で規格化し、全ての指定座標が単元であることから局所化へ延長する。
規約：T の元 k を新しい pivot に使う。逆写像には i∈T も必要。
使われ方：全有限 Čech の異なるチャート表示の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

variable (R : Type u) [CommRing R] {I : Type v} [DecidableEq I]

/-- 概要：k チャートから i 側の有限重なりへの規格化環射。
方針：k 座標の単元を chartTransition へ渡す。
規約：KST §3.1。使われ方：有限重なり間の pivot 変更の基底部分。 -/
def finiteOverlapTransitionBase (i k : I) (T : Finset I) (hk : k ∈ T) :
    ChartRing R k →ₐ[R] FiniteOverlapRing R i T :=
  chartTransition i k (finiteOverlapInclusion R i T) (finiteOverlapUnit R i T k hk)

/-- 概要：有限重なりの pivot 変更は座標を k 座標で割る。
方針：単元の値と chartTransition の座標公式を使う。
規約：KST §3.1。使われ方：局所化延長の単元性と cocycle。 -/
@[simp] theorem finiteOverlapTransitionBase_coordinate (i k : I) (T : Finset I)
    (hk : k ∈ T) (j : I) :
    finiteOverlapTransitionBase R i k T hk (chartCoordinate R k j) =
      finiteOverlapInclusion R i T (chartCoordinate R i j) *
        ↑(finiteOverlapUnit R i T k hk)⁻¹ :=
  chartTransition_coordinate i k j _ _ (finiteOverlapUnit_val R i T k hk)

/-- 概要：有限重なりの pivot 変更は指定座標積を単元へ送る。
方針：各指定座標の像は二つの単元の積になる。
規約：KST §3.1。使われ方：有限重なり環全体への射の延長。 -/
theorem finiteOverlapTransitionBase_denominator_isUnit (i k : I) (T : Finset I)
    (hk : k ∈ T) :
    IsUnit (finiteOverlapTransitionBase R i k T hk (finiteOverlapDenominator R k T)) := by
  simp only [finiteOverlapDenominator, map_prod]
  apply IsUnit.prod_iff.mpr
  intro j hj
  rw [finiteOverlapTransitionBase_coordinate]
  exact (finiteOverlap_coordinate_isUnit R i T j hj).mul
    (finiteOverlapUnit R i T k hk)⁻¹.isUnit

/-- 概要：有限重なりの二つの pivot 表示の間の環射。
方針：規格化環射を座標積の単元性によって局所化へ延長する。
規約：KST §3.1。使われ方：全有限重なりのチャート間比較。 -/
def finiteOverlapPivotMap (i k : I) (T : Finset I) (hk : k ∈ T) :
    FiniteOverlapRing R k T →ₐ[R] FiniteOverlapRing R i T :=
  IsLocalization.Away.liftAlgHom (finiteOverlapDenominator R k T)
    (f := finiteOverlapTransitionBase R i k T hk)
    (finiteOverlapTransitionBase_denominator_isUnit R i k T hk)

/-- 概要：有限 pivot 変更射はチャート上の規格化射を延長する。
方針：Away lift の生成元公式。
規約：KST §3.1。使われ方：有限重なりの比較の逆射と自然性。 -/
@[simp] theorem finiteOverlapPivotMap_base (i k : I) (T : Finset I) (hk : k ∈ T)
    (p : ChartRing R k) :
    finiteOverlapPivotMap R i k T hk (finiteOverlapInclusion R k T p) =
      finiteOverlapTransitionBase R i k T hk p :=
  IsLocalization.Away.lift_eq _
    (finiteOverlapTransitionBase_denominator_isUnit R i k T hk) p

/-- 概要：逆側の pivot 単元の値は元の pivot 単元の逆へ送られる。
方針：単元を座標へ戻し、規格化後の元の pivot は1であることを使う。
規約：KST §3.1。使われ方：pivot 比較が相互逆であることの計算。 -/
@[simp] theorem finiteOverlapPivotMap_unit (i k : I) (T : Finset I)
    (hi : i ∈ T) (hk : k ∈ T) :
    finiteOverlapPivotMap R i k T hk (↑(finiteOverlapUnit R k T i hi)) =
      ↑(finiteOverlapUnit R i T k hk)⁻¹ := by
  rw [finiteOverlapUnit_val, finiteOverlapPivotMap_base,
    finiteOverlapTransitionBase_coordinate, chartCoordinate_self, map_one, one_mul]

/-- 概要：逆側の逆 pivot 単元は元の pivot 単元へ送られる。
方針：環射の積保存と単元の逆元律から求める。
規約：KST §3.1。使われ方：pivot 変更の往復公式。 -/
@[simp] theorem finiteOverlapPivotMap_unitInv (i k : I) (T : Finset I)
    (hi : i ∈ T) (hk : k ∈ T) :
    finiteOverlapPivotMap R i k T hk (↑(finiteOverlapUnit R k T i hi)⁻¹) =
      ↑(finiteOverlapUnit R i T k hk) := by
  have h := congrArg (finiteOverlapPivotMap R i k T hk) (finiteOverlapUnit R k T i hi).mul_inv
  rw [map_mul, map_one, finiteOverlapPivotMap_unit] at h
  calc
    _ = (↑(finiteOverlapUnit R i T k hk) * ↑(finiteOverlapUnit R i T k hk)⁻¹) *
        finiteOverlapPivotMap R i k T hk (↑(finiteOverlapUnit R k T i hi)⁻¹) := by
      rw [(finiteOverlapUnit R i T k hk).mul_inv, one_mul]
    _ = _ := by rw [mul_assoc, h, mul_one]

/-- 概要：有限重なり上で pivot を往復すると全座標を保つ。
方針：規格化を二回展開して互いに逆の単元を消去する。
規約：KST §3.1。使われ方：局所化の外延性による環同型。 -/
theorem finiteOverlapPivotMap_roundtrip_coordinate (i k : I) (T : Finset I)
    (hi : i ∈ T) (hk : k ∈ T) (j : I) :
    finiteOverlapPivotMap R i k T hk (finiteOverlapPivotMap R k i T hi
      (finiteOverlapInclusion R i T (chartCoordinate R i j))) =
        finiteOverlapInclusion R i T (chartCoordinate R i j) := by
  rw [finiteOverlapPivotMap_base, finiteOverlapTransitionBase_coordinate, map_mul,
    finiteOverlapPivotMap_base, finiteOverlapTransitionBase_coordinate,
    finiteOverlapPivotMap_unitInv, mul_assoc, (finiteOverlapUnit R i T k hk).inv_mul, mul_one]

/-- 概要：有限重なり上で二つの pivot 変更射は相互逆。
方針：局所化と多項式環の外延性で座標の往復へ帰着する。
規約：KST §3.1。使われ方：全有限重なりの環同型。 -/
theorem finiteOverlapPivotMap_comp (i k : I) (T : Finset I) (hi : i ∈ T) (hk : k ∈ T) :
    (finiteOverlapPivotMap R i k T hk).comp (finiteOverlapPivotMap R k i T hi) =
      AlgHom.id R (FiniteOverlapRing R i T) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (finiteOverlapDenominator R i T))
  ext j
  simpa only [chartCoordinate_other, AlgHom.comp_apply, AlgHom.id_apply,
    finiteOverlapInclusion, IsScalarTower.toAlgHom, Algebra.algHom] using
      finiteOverlapPivotMap_roundtrip_coordinate R i k T hi hk j.val

/-- 概要：任意有限重なりの二つの pivot 表示の代数同型。
方針：局所化した規格化射とその逆を束ねる。
規約：KST §3.1。使われ方：有限 Čech 図式の pivot の選び方からの独立性。 -/
def finiteOverlapPivotEquiv (i k : I) (T : Finset I) (hi : i ∈ T) (hk : k ∈ T) :
    FiniteOverlapRing R k T ≃ₐ[R] FiniteOverlapRing R i T :=
  AlgEquiv.ofAlgHom (finiteOverlapPivotMap R i k T hk) (finiteOverlapPivotMap R k i T hi)
    (finiteOverlapPivotMap_comp R i k T hi hk) (finiteOverlapPivotMap_comp R k i T hk hi)

end SerrePositivity.KST.DerivedBlowup
