module

public import SerrePositivity.KST.DerivedBlowup.ChartBaseChangeDGFunctor
public import SerrePositivity.KST.DerivedBlowup.OverlapComplexComparison
public import SerrePositivity.KST.DerivedBlowup.ChartDGFunctors

/-!
概要：KST §3.1 の実際の重なり環での dg チャート比較。
方針：環射に沿う Koszul dg 底変更と規格化座標の可逆基底変換を合成する。
規約：二つのチャートの係数変更を共通の外積 dg チャートへ送る準同値を使う。
使われ方：導来 blowup のチャート図式の局所 dg 比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {R : Type u} [CommRing R] {r : ℕ}

/-- 概要：共通重なり環での i チャートの座標。
方針：局所化の構造射で元の座標を送る。
規約：KST §3.1。使われ方：重なりの標準 dg チャート。 -/
abbrev overlapCoordinates (i k : Fin (r + 1)) : Fin (r + 1) → OverlapRing R i k :=
  fun j => overlapInclusion R i k (chartCoordinate R i j)

/-- 概要：共通重なり環での関係式の係数。
方針：基底環の構造射により a_j を送る。
規約：KST §3.1。使われ方：重なりの標準 Koszul 微分。 -/
abbrev overlapCoefficients (a : Fin (r + 1) → R) (i k : Fin (r + 1)) :
    Fin (r + 1) → OverlapRing R i k := fun j => algebraMap R (OverlapRing R i k) (a j)

/-- 概要：重なりの二つの座標表示の同定は生成元の恒等写像で微分を保つ。
方針：遷移環射の座標公式を微分へ適用する。
規約：KST §3.1。使われ方：dg 関手の終域を規格化表示へ合わせる。 -/
theorem overlapCoordinateDifferential_id (a : Fin (r + 1) → R) (i k : Fin (r + 1)) :
    (chartKoszulDifferential (overlapCoefficients a i k)
      (normalizeCoordinates (overlapCoordinates (R := R) i k) (overlapUnit R i k)) k).comp
        LinearMap.id =
      chartKoszulDifferential (overlapCoefficients a i k)
        (fun j => overlapTransitionBase R i k (chartCoordinate R k j)) k := by
  simpa only [LinearMap.comp_id] using
    (congrArg (fun x => chartKoszulDifferential (overlapCoefficients a i k) x k)
      (overlapTransition_coordinates (R := R) i k)).symm

set_option synthInstance.maxHeartbeats 100000 in
-- Away 局所化環上の複体のモノイダル構造の探索に必要。
/-- 概要：k チャートの重なりへの底変更を規格化表示へ送る dg 関手。
方針：一般のチャート底変更に恒等生成元の微分同定を合成する。
規約：KST §3.1。使われ方：可逆基底変換の前段。 -/
def overlapNormalizedDGFunctor (a : Fin (r + 1) → R) (i k : Fin (r + 1)) :
    EnrichedFunctor (DifferentialGraded.Complex (OverlapRing R i k))
      (DifferentialGraded.ScalarExtension.DGBaseChange (overlapTransitionBase R i k).toRingHom
        (DerivedChartObject a k))
      (ExteriorKoszulObject (chartKoszulDifferential (overlapCoefficients a i k)
        (normalizeCoordinates (overlapCoordinates (R := R) i k) (overlapUnit R i k)) k)) :=
  EnrichedFunctor.comp (DifferentialGraded.Complex (OverlapRing R i k))
    (chartBaseChangeDGFunctor a k (overlapTransitionBase R i k))
    (exteriorKoszulDGFunctor LinearMap.id
      (chartKoszulDifferential (overlapCoefficients a i k)
        (fun j => overlapTransitionBase R i k (chartCoordinate R k j)) k)
      (chartKoszulDifferential (overlapCoefficients a i k)
        (normalizeCoordinates (overlapCoordinates (R := R) i k) (overlapUnit R i k)) k)
      (overlapCoordinateDifferential_id a i k))

set_option synthInstance.maxHeartbeats 100000 in
-- Away 局所化環上の複体のモノイダル構造の探索に必要。
/-- 概要：k チャートの底変更を共通重なりの i 側の外積 dg チャートへ送る。
方針：規格化された底変更表示に Koszul の可逆基底変換を合成する。
規約：KST §3.1。使われ方：二つのチャートを共通模型で比較する dg 関手。 -/
def overlapChartDGFunctor (a : Fin (r + 1) → R) (i k : Fin (r + 1)) :
    EnrichedFunctor (DifferentialGraded.Complex (OverlapRing R i k))
      (DifferentialGraded.ScalarExtension.DGBaseChange (overlapTransitionBase R i k).toRingHom
        (DerivedChartObject a k))
      (ExteriorKoszulObject (chartKoszulDifferential (overlapCoefficients a i k)
        (overlapCoordinates (R := R) i k) i)) :=
  EnrichedFunctor.comp (DifferentialGraded.Complex (OverlapRing R i k))
    (overlapNormalizedDGFunctor a i k)
    (chartExteriorDGFunctor (overlapCoefficients a i k) (overlapCoordinates (R := R) i k)
      i k (overlapUnit R i k) (by simp [overlapCoordinates]) (overlapUnit_val R i k))

set_option synthInstance.maxHeartbeats 100000 in
-- 同じ局所化係数環の複体同型の型クラス探索に必要。
/-- 概要：実際の重なりにおけるチャート dg 比較の Hom 写像は複体同型。
方針：チャート底変更と二つの可逆生成元変換の同型を使う。
規約：KST §3.1。使われ方：重なりにおける局所 dg 同値性。 -/
theorem overlapChartDGFunctor_map_isIso (a : Fin (r + 1) → R) (i k : Fin (r + 1)) (x y) :
    IsIso ((overlapChartDGFunctor a i k).map x y) := by
  have := chartBaseChangeDGFunctor_map_isIso a k (overlapTransitionBase R i k) x y
  change IsIso (((chartBaseChangeDGFunctor a k (overlapTransitionBase R i k)).map x y ≫
    (exteriorKoszulCochainIso (LinearEquiv.refl (OverlapRing R i k) _)
      (chartKoszulDifferential (overlapCoefficients a i k)
        (fun j => overlapTransitionBase R i k (chartCoordinate R k j)) k)
      (chartKoszulDifferential (overlapCoefficients a i k)
        (normalizeCoordinates (overlapCoordinates (R := R) i k) (overlapUnit R i k)) k)
      (overlapCoordinateDifferential_id a i k)).hom) ≫
      (chartExteriorCochainIso (overlapCoefficients a i k) (overlapCoordinates (R := R) i k)
        i k (overlapUnit R i k) (by simp [overlapCoordinates]) (overlapUnit_val R i k)).hom)
  infer_instance

set_option synthInstance.maxHeartbeats 100000 in
-- 同じ局所化係数環の豊穣関手の型クラス探索に必要。
/-- 概要：実際の重なりでのチャート dg 比較は準同値。
方針：Hom の複体同型と一対象の H⁰ 上の全射性を使う。
規約：KST §3.1。使われ方：導来チャート図式の局所比較。 -/
theorem overlapChartDGFunctor_quasiEquivalence (a : Fin (r + 1) → R) (i k : Fin (r + 1)) :
    DifferentialGraded.QuasiEquivalence (overlapChartDGFunctor a i k) := by
  constructor
  · intro x y
    have := overlapChartDGFunctor_map_isIso a i k x y
    infer_instance
  · apply Functor.essSurj_of_surj
    rintro ⟨y⟩
    change ExteriorKoszulObject (chartKoszulDifferential (overlapCoefficients a i k)
      (overlapCoordinates (R := R) i k) i) at y
    cases y
    exact ⟨⟨ExteriorKoszulObject.point⟩, rfl⟩

end SerrePositivity.KST.DerivedBlowup
