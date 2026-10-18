module

public import SerrePositivity.KST.DerivedBlowup.ChartBaseChangeComparison
public import SerrePositivity.KST.DerivedBlowup.Overlaps

/-!
概要：KST §3.1 の共通重なり環でチャート Koszul 複体を同定する。
方針：実際の局所化環への係数変更を外積模型へ移し、可逆基底変換を適用する。
規約：複体の項ごとのスカラー拡大の比較。dg 代数の導来底変更との比較は別工程。
使われ方：導来チャート図式の underlying 複体の遷移。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {R : Type u} [CommRing R] {r : ℕ}

/-- 概要：重なりへの遷移後の全座標は可逆座標による規格化に等しい。
方針：実際の局所化環上の座標公式を関数の等式へまとめる。
規約：KST §3.1。使われ方：重なり上の Koszul 基底変換。 -/
theorem overlapTransition_coordinates (i k : Fin (r + 1)) :
    (fun j => overlapTransitionBase R i k (chartCoordinate R k j)) =
      normalizeCoordinates (fun j => overlapInclusion R i k (chartCoordinate R i j))
        (overlapUnit R i k) := by
  funext j
  exact overlapTransitionBase_coordinate R i k j

/-- 概要：共通重なり環での二つの外積チャート模型は複体同型。
方針：座標の規格化を同定し、可逆 Koszul 生成元変換を適用する。
規約：KST §3.1、重なり環は Away 局所化そのもの。
使われ方：元のチャートのスカラー拡大後の比較。 -/
def overlapChartExteriorIso (a : Fin (r + 1) → R) (i k : Fin (r + 1)) :
    chartExteriorCochain (fun j => algebraMap R (OverlapRing R i k) (a j))
        (fun j => overlapTransitionBase R i k (chartCoordinate R k j)) k ≅
      chartExteriorCochain (fun j => algebraMap R (OverlapRing R i k) (a j))
        (fun j => overlapInclusion R i k (chartCoordinate R i j)) i :=
  eqToIso (congrArg
    (fun x => chartExteriorCochain (fun j => algebraMap R (OverlapRing R i k) (a j)) x k)
    (overlapTransition_coordinates (R := R) i k)) ≪≫
      chartExteriorCochainIso (fun j => algebraMap R (OverlapRing R i k) (a j))
        (fun j => overlapInclusion R i k (chartCoordinate R i j)) i k (overlapUnit R i k)
        (by simp) (overlapUnit_val R i k)

/-- 概要：二つのチャートの共通重なり環への底変更複体は同型。
方針：両側を外積模型へ比較し、重なりの基底変換を間に挟む。
規約：KST §3.1、複体レベルのスカラー拡大。
使われ方：チャート図式の underlying 複体の実際の貼り合わせ。 -/
def overlapChartComplexIso (a : Fin (r + 1) → R) (i k : Fin (r + 1)) :
    baseChange (overlapTransitionBase R i k).toRingHom (derivedChartComplex a k) ≅
      baseChange (overlapInclusion R i k).toRingHom (derivedChartComplex a i) :=
  chartBaseChangeExteriorIso a k (overlapTransitionBase R i k) ≪≫
    overlapChartExteriorIso a i k ≪≫
      (chartBaseChangeExteriorIso a i (overlapInclusion R i k)).symm

end SerrePositivity.KST.DerivedBlowup
