module

public import SerrePositivity.InfinityCategories.F2.FiberwisePullbackNativeConeLeg
public import SerrePositivity.InfinityCategories.F2.KanIntervalConeProjections

/-!
概要：全空間の native な引き戻し錐の二脚と元の全空間射影を照合する。
方針：元の比較射での前合成と Kan 写像空間の連結成分の推移性。
規約：元の全空間模型を保持。使われ方：coherent 余極限錐の脚との比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
variable {E D H B : SSet.{u}} [Quasicategory B] [IsFilteredInfinity B]
  (p : H ⟶ B) [LeftFibration p] (f : E ⟶ H) (g : D ⟶ H)
  [LeftFibration (f ≫ p)] [LeftFibration (g ≫ p)]

/-- 概要：全空間の native な左脚は元の第一入力への Kan 射影にホモトピック。
方針：区間錐の左脚の比較を前合成し、比較の厳密な射影式を使う。
規約：同じ頂点。使われ方：引き戻し交換の第一脚。 -/
lemma fiberwisePullbackNativeConeKanLeg_left :
    Nonempty (SSet.Homotopy
      (fiberwisePullbackNativeConeKanLeg p f g (AsSmall.up.obj WalkingCospan.left))
      (continuousKanReplacement.map (fiberwiseIntervalPullbackLeft p f g))) := by
  have ha := fiberwisePullbackNativeConeKanLeg_comparison p f g
    (AsSmall.up.obj WalkingCospan.left)
  obtain ⟨e⟩ := intervalPullbackConeKanLeg_left (continuousKanMap f) (continuousKanMap g)
  have hb := functorHomotopyPrecomp e
    (show (fiberwisePullbackTotalKanObject p f g).obj ⟶
      (fiberwisePullbackTargetKanObject f g).obj from fiberwisePullbackComparisonKanMap p f g)
  have he : fiberwisePullbackComparisonKanMap p f g ≫
      intervalPullbackLeft (continuousKanMap f) (continuousKanMap g) =
      continuousKanReplacement.map (fiberwiseIntervalPullbackLeft p f g) := by
    change fiberwisePullbackKanComparison p f g ≫ _ ≫ _ = _
    exact fiberwisePullbackKanComparison_left p f g
  have hc : SSet.Homotopy
      (fiberwisePullbackComparisonKanMap p f g ≫
        intervalPullbackConeKanLeg (continuousKanMap f) (continuousKanMap g)
          (AsSmall.up.obj WalkingCospan.left))
      (continuousKanReplacement.map (fiberwiseIntervalPullbackLeft p f g)) :=
    { h := hb.h, h₀ := hb.h₀, h₁ := hb.h₁.trans he, rel := hb.rel }
  apply (functorVertex_piZero_eq_iff_homotopy _ _).mp
  exact ((functorVertex_piZero_eq_iff_homotopy _ _).mpr ha).trans
    ((functorVertex_piZero_eq_iff_homotopy _ _).mpr ⟨hc⟩)

/-- 概要：全空間の native な右脚は元の第二入力への Kan 射影にホモトピック。
方針：区間錐の右脚の比較を前合成し、比較の厳密な射影式を使う。
規約：同じ頂点。使われ方：引き戻し交換の第二脚。 -/
lemma fiberwisePullbackNativeConeKanLeg_right :
    Nonempty (SSet.Homotopy
      (fiberwisePullbackNativeConeKanLeg p f g (AsSmall.up.obj WalkingCospan.right))
      (continuousKanReplacement.map (fiberwiseIntervalPullbackRight p f g))) := by
  have ha := fiberwisePullbackNativeConeKanLeg_comparison p f g
    (AsSmall.up.obj WalkingCospan.right)
  obtain ⟨e⟩ := intervalPullbackConeKanLeg_right (continuousKanMap f) (continuousKanMap g)
  have hb := functorHomotopyPrecomp e
    (show (fiberwisePullbackTotalKanObject p f g).obj ⟶
      (fiberwisePullbackTargetKanObject f g).obj from fiberwisePullbackComparisonKanMap p f g)
  have he : fiberwisePullbackComparisonKanMap p f g ≫
      intervalPullbackRight (continuousKanMap f) (continuousKanMap g) =
      continuousKanReplacement.map (fiberwiseIntervalPullbackRight p f g) :=
    fiberwisePullbackKanComparison_right p f g
  have hc : SSet.Homotopy
      (fiberwisePullbackComparisonKanMap p f g ≫
        intervalPullbackConeKanLeg (continuousKanMap f) (continuousKanMap g)
          (AsSmall.up.obj WalkingCospan.right))
      (continuousKanReplacement.map (fiberwiseIntervalPullbackRight p f g)) :=
    { h := hb.h, h₀ := hb.h₀, h₁ := hb.h₁.trans he, rel := hb.rel }
  apply (functorVertex_piZero_eq_iff_homotopy _ _).mp
  exact ((functorVertex_piZero_eq_iff_homotopy _ _).mpr ha).trans
    ((functorVertex_piZero_eq_iff_homotopy _ _).mpr ⟨hc⟩)

end SerrePositivity.InfinityCategories.F2
