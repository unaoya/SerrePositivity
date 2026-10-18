module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapDGTransition
public import SerrePositivity.KST.DerivedBlowup.ChartSemilinearComposition

/-!
概要：KST §3.1 の有限重なり dg 遷移の係数環と単元の合成データ。
方針：環図式の合成律と座標公式から合成環射と合成単元の等式を取り出す。
規約：有限集合の包含に沿う共変の環図式。
使われ方：実際の有限重なり dg 遷移の合成整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：有限重なりの環射の合成は環準同型としても直接射に等しい。
方針：代数射の合成律から環準同型の成分を取る。
規約：KST §3.1。使われ方：dg 制限の合成の行先の比較。 -/
theorem finiteOverlapChartMap_ringHom_comp (i k l : I) {T U V : Finset I}
    (h : T ⊆ U) (g : U ⊆ V) (hi : i ∈ T) (hk : k ∈ U) :
    (finiteOverlapChartMap R k l g hk).toRingHom.comp
      (finiteOverlapChartMap R i k h hi).toRingHom =
      (finiteOverlapChartMap R i l (h.trans g) hi).toRingHom :=
  congrArg (fun f => f.toRingHom) (finiteOverlapChartMap_comp R i k l h g hi hk)

/-- 概要：有限重なりの合成遷移単元は直接遷移の単元に等しい。
方針：半線形遷移の合成単元の値を座標で計算し、単元の外延性を使う。
規約：KST §3.1。使われ方：有限重なり dg 遷移の基底変換の cocycle。 -/
theorem finiteOverlapDGTransition_unit_comp (i k l : I) {T U V : Finset I}
    (h : T ⊆ U) (g : U ⊆ V) (hi : i ∈ T) (hk : k ∈ U) :
    finiteOverlapUnit R l V k (g hk) *
      Units.map (finiteOverlapChartMap R k l g hk).toRingHom.toMonoidHom
        (finiteOverlapUnit R k U i (h hi)) =
      finiteOverlapUnit R l V i (g (h hi)) := by
  apply Units.ext
  exact (chartSemilinearUnit_comp (finiteOverlapChartMap R k l g hk).toRingHom
    (finiteOverlapCoordinates R k U) (finiteOverlapCoordinates R l V) i
    (finiteOverlapUnit R k U i (h hi)) (finiteOverlapUnit R l V k (g hk))
    (finiteOverlapChartMap_coordinates R k l g hk)
    (finiteOverlapUnit_val R k U i (h hi))).trans (finiteOverlapUnit_val R l V i (g (h hi))).symm

end SerrePositivity.KST.DerivedBlowup
