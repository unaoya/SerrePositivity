module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FiberwisePullbackConePathCompatibility

/-!
概要：全空間錐の指定 path の元の全座標を回収する。
方針：元の区間円柱を比較で引き戻し、curry の自然性と三座標式を使う。
規約：全単体で一致。使われ方：coherent 余極限の指定 path の保持。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E D H B : SSet.{u}} (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H)

/-- 概要：全空間比較を通る指定 path の円柱。
方針：元の区間円柱への前合成。規約：代表を選び直さない。使われ方：全座標の回収。 -/
def fiberwisePullbackTotalRawPathHomotopy :=
  functorHomotopyPrecomp
    (intervalPullbackPathHomotopy (continuousKanMap f) (continuousKanMap g))
    (show (fiberwisePullbackTotalKanObject p f g).obj ⟶
      (fiberwisePullbackTargetKanObject f g).obj from fiberwisePullbackComparisonKanMap p f g)

/-- 概要：指定円柱の全 path は元の全空間 path の Kan 比較そのもの。
方針：curry の自然性と比較の厳密な path 座標式。
規約：全単体の等式。使われ方：同型の類だけに制限しない指定データの追跡。 -/
lemma fiberwisePullbackTotalRawPathHomotopy_curry :
    curry ((β_ (Δ[1] : SSet.{u}) (fiberwisePullbackTotalKanObject p f g).obj).hom ≫
      (fiberwisePullbackTotalRawPathHomotopy p f g).h) =
        continuousKanReplacement.map (fiberwiseIntervalPullbackPath p f g) ≫
          fiberwiseIntervalKanComparison p := by
  let a : (fiberwisePullbackTotalKanObject p f g).obj ⟶
      (fiberwisePullbackTargetKanObject f g).obj := fiberwisePullbackComparisonKanMap p f g
  have hn :
      (β_ (Δ[1] : SSet.{u}) (fiberwisePullbackTotalKanObject p f g).obj).hom ≫
          (a ▷ (Δ[1] : SSet.{u})) =
        ((Δ[1] : SSet.{u}) ◁ a) ≫
          (β_ (Δ[1] : SSet.{u}) (fiberwisePullbackTargetKanObject f g).obj).hom := rfl
  change curry (_ ≫ (_ ▷ (Δ[1] : SSet.{u})) ≫ _) = _
  rw [← Category.assoc, hn, Category.assoc, curry_natural_left]
  change a ≫ curry ((β_ (Δ[1] : SSet.{u})
    (intervalPullback (continuousKanMap f) (continuousKanMap g))).hom ≫
      (intervalPullbackPathHomotopy (continuousKanMap f) (continuousKanMap g)).h) = _
  rw [intervalPullbackPathHomotopy_curry]
  exact fiberwisePullbackKanComparison_path p f g

/-- 概要：指定 path 同型の輸送前の射は元の全円柱の類。
方針：前合成のホモトピー類と関手同型の作用を照合。
規約：指定された代表。使われ方：正規化した path 同型の元データ。 -/
lemma fiberwisePullbackTotalRawPathIso_hom :
    ((intervalPullbackPathIso (continuousKanMap f) (continuousKanMap g)).precomp
      (show (fiberwisePullbackTotalKanObject p f g).obj ⟶
        (fiberwisePullbackTargetKanObject f g).obj from
          fiberwisePullbackComparisonKanMap p f g)).hom =
      SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (fiberwisePullbackTotalRawPathHomotopy p f g)) := by
  have ht := functorHomotopyPrecomp_hom
    (intervalPullbackPathHomotopy (continuousKanMap f) (continuousKanMap g))
    (show (fiberwisePullbackTotalKanObject p f g).obj ⟶
      (fiberwisePullbackTargetKanObject f g).obj from fiberwisePullbackComparisonKanMap p f g)
  rw [← intervalPullbackPathIso_hom] at ht
  exact ht.symm

end SerrePositivity.InfinityCategories.F2
