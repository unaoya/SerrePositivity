module

public import SerrePositivity.KST.DerivedBlowup.ChartSemilinearTransition
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapDiagram

/-!
概要：KST §3.1 の全有限重なりの実際の環射に沿う dg チャート遷移。
方針：有限重なり環射の係数・座標公式を確認し、半線形チャート dg 遷移に適用する。
規約：元・目標の pivot はそれぞれの有限集合に属する。
使われ方：非空有限重なり全体の dg 図式の構成。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded DifferentialGraded.ScalarExtension

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：有限重なり環での比座標。
方針：多項式チャートの座標を局所化の構造射で送る。
規約：KST §3.1。使われ方：局所 dg チャートの微分と遷移。 -/
def finiteOverlapCoordinates (i : I) (T : Finset I) : I → FiniteOverlapRing R i T :=
  fun j => finiteOverlapInclusion R i T (chartCoordinate R i j)

/-- 概要：有限重なり環射は元の比座標を目標の規格化座標へ送る。
方針：制限と pivot 変更の座標公式を合成する。
規約：KST §3.1。使われ方：半線形チャート遷移の座標条件。 -/
theorem finiteOverlapChartMap_coordinates (i k : I) {T U : Finset I}
    (h : T ⊆ U) (hi : i ∈ T) :
    (finiteOverlapChartMap R i k h hi).toRingHom ∘ finiteOverlapCoordinates R i T =
      normalizeCoordinates (finiteOverlapCoordinates R k U) (finiteOverlapUnit R k U i (h hi)) := by
  funext j
  change finiteOverlapPivotMap R k i U (h hi)
    (finiteOverlapRestriction R i h (finiteOverlapInclusion R i T (chartCoordinate R i j))) = _
  rw [finiteOverlapRestriction_base, finiteOverlapPivotMap_base,
    finiteOverlapTransitionBase_coordinate]
  rfl

/-- 概要：有限重なり上の局所 Koszul dg チャート模型。
方針：局所化環の係数と比座標から外積微分を作る。
規約：KST §3.1。使われ方：有限重なり dg 図式の対象。 -/
abbrev FiniteOverlapKoszulObject (a : I → R) (i : I) (T : Finset I) :=
  ExteriorKoszulObject (chartKoszulDifferential
    (fun j => algebraMap R (FiniteOverlapRing R i T) (a j)) (finiteOverlapCoordinates R i T) i)

/-- 概要：有限重なりの拡大と pivot 変更をまとめた実際の dg 遷移。
方針：有限重なり環射が係数を保ち座標を規格化する公式を半線形遷移へ渡す。
規約：KST §3.1、行先は元の重なり環への係数制限。
使われ方：全有限重なりのチャート dg 図式の射。 -/
def finiteOverlapDGTransition (a : I → R) (i k : I) {T U : Finset I}
    (h : T ⊆ U) (hi : i ∈ T) :
    DGFunctor (FiniteOverlapRing R i T) (FiniteOverlapKoszulObject R a i T)
      (DGRestriction (finiteOverlapChartMap R i k h hi).toRingHom
        (FiniteOverlapKoszulObject R a k U)) :=
  chartSemilinearDGFunctor (finiteOverlapChartMap R i k h hi).toRingHom
    (fun j => algebraMap R (FiniteOverlapRing R i T) (a j)) (finiteOverlapCoordinates R i T)
    (fun j => algebraMap R (FiniteOverlapRing R k U) (a j)) (finiteOverlapCoordinates R k U)
    i k (finiteOverlapUnit R k U i (h hi))
    (by funext j; exact (finiteOverlapChartMap R i k h hi).commutes (a j))
    (finiteOverlapChartMap_coordinates R i k h hi)
    (by simp [finiteOverlapCoordinates]) (finiteOverlapUnit_val R k U i (h hi))

set_option maxHeartbeats 800000 in
-- 局所化環上の豊穣 Hom と係数制限の成分の照合に必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環上の豊穣 Hom と係数制限の成分の照合に必要。
/-- 概要：有限重なり dg 遷移の Hom は係数変更と明示基底変換で計算できる。
方針：一般の半線形チャート遷移の包含公式を適用する。
規約：KST §3.1。使われ方：有限重なり dg 遷移の恒等・合成則。 -/
theorem finiteOverlapDGTransition_inclusion (a : I → R) (i k : I) {T U : Finset I}
    (h : T ⊆ U) (hi : i ∈ T) (v w : FiniteOverlapKoszulObject R a i T) (q : ℤ)
    (z : (exteriorKoszulCochain (chartKoszulDifferential
      (fun j => algebraMap R (FiniteOverlapRing R i T) (a j))
      (finiteOverlapCoordinates R i T) i)).X q) :
    exteriorCochainInclusion (chartKoszulDifferential
        (fun j => algebraMap R (FiniteOverlapRing R k U) (a j))
        (finiteOverlapCoordinates R k U) k) q
        (((finiteOverlapDGTransition R a i k h hi).map v w).f q z) =
      ExteriorAlgebra.map (koszulGeneratorMap k i (finiteOverlapCoordinates R k U)
        (finiteOverlapUnit R k U i (h hi)))
        (freeExteriorScalarMap (finiteOverlapChartMap R i k h hi).toRingHom
          (exteriorCochainInclusion (chartKoszulDifferential
            (fun j => algebraMap R (FiniteOverlapRing R i T) (a j))
            (finiteOverlapCoordinates R i T) i) q z)) := by
  exact chartSemilinearDGFunctor_inclusion (finiteOverlapChartMap R i k h hi).toRingHom
    (fun j => algebraMap R (FiniteOverlapRing R i T) (a j)) (finiteOverlapCoordinates R i T)
    (fun j => algebraMap R (FiniteOverlapRing R k U) (a j)) (finiteOverlapCoordinates R k U)
    i k (finiteOverlapUnit R k U i (h hi))
    (by funext j; exact (finiteOverlapChartMap R i k h hi).commutes (a j))
    (finiteOverlapChartMap_coordinates R i k h hi)
    (by simp [finiteOverlapCoordinates]) (finiteOverlapUnit_val R k U i (h hi)) v w q z

end SerrePositivity.KST.DerivedBlowup
