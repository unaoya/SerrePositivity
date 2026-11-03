module

public import SerrePositivity.InfinityCategories.Core.IntervalBoundary
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalPullbackMaps
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePullbackKanComparison
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePullbackKanUnit
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePullbackPathPrism
public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.FiberwisePullbackValue
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalPullbackCoordinates
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.PathSquareCurry
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.RelativePathBoundary
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.RelativePathBoundaryTransportHomotopy
public import SerrePositivity.InfinityCategories.F1B.FilteredExchange.RelativePathComparisonFaces
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.RelativePathInputTransportData
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.RelativePathSquareCurry
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.RelativePathTransportTarget

/-!
概要：相対 path 比較から作った Kan 引き戻し円柱の制限を元の境界輸送と同定する。
方針：二入力と全 path の三座標を厳密に照合する。
規約：ホモトピー類でなく全円柱の等式。使われ方：元の境界を持つ相対有限検出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：三座標を保持した比較円柱は、指定部分で元の境界輸送の実際の比較像に一致。
方針：二入力の制限式と全 path の curry の制限式。
規約：全単体で厳密。使われ方：境界を保持する相対比較の結論。 -/
lemma relativePathKanComparison_restrict {K M E D H B : SSet.{u}}
    {p : H ⟶ B} {f : E ⟶ H} {g : D ⟶ H} {A : K.Subcomplex}
    {u : K ⟶ E} {v : K ⟶ D} {a : (A : SSet.{u}) ⟶ fiberwiseIntervalPullback p f g}
    {m : relativePathBoundaryShape A ⟶ M} {q : M ⟶ H}
    (d : RelativePathInputTransportData p f g A u v a m q)
    (hk : (relativePathBoundarySide A ≫ m) ≫ q = fiberwisePullbackPathPrism p f g a)
    (he : (relativePathBoundaryEnds A ≫ m) ≫ q = intervalBoundaryDiagram (u ≫ f) (v ≫ g))
    (F : ((Δ[1] : SSet.{u}) ⊗ K) ⊗ (Δ[1] : SSet.{u}) ⟶ continuousKanReplacement.obj H)
    (hF : (relativePathBoundaryι A ▷ (Δ[1] : SSet.{u})) ≫ F =
      (relativePathBoundaryTransportHomotopy d hk he).h ≫ continuousKanReplacementUnit.app H)
    (L : K ⊗ (Δ[1] : SSet.{u}) ⟶
      intervalPullback (continuousKanReplacement.map f) (continuousKanReplacement.map g))
    (hl : L ≫ intervalPullbackLeft (continuousKanReplacement.map f)
      (continuousKanReplacement.map g) = d.leftHomotopy.h ≫ continuousKanReplacementUnit.app E)
    (hr : L ≫ intervalPullbackRight (continuousKanReplacement.map f)
      (continuousKanReplacement.map g) = d.rightHomotopy.h ≫ continuousKanReplacementUnit.app D)
    (hp : L ≫ intervalPullbackPath (continuousKanReplacement.map f)
      (continuousKanReplacement.map g) = pathSquareCurry
        (((β_ K (Δ[1] : SSet.{u})).hom ▷ (Δ[1] : SSet.{u})) ≫ F)) :
    (A.ι ▷ (Δ[1] : SSet.{u})) ≫ L = d.boundaryHomotopy.h ≫
      continuousKanReplacementUnit.app (fiberwiseIntervalPullback p f g) ≫
        fiberwisePullbackKanComparison p f g := by
  have hul : continuousKanReplacementUnit.app (fiberwiseIntervalPullback p f g) ≫
      fiberwisePullbackKanComparison p f g ≫ intervalPullbackLeft
        (continuousKanReplacement.map f) (continuousKanReplacement.map g) =
      fiberwiseIntervalPullbackLeft p f g ≫ continuousKanReplacementUnit.app E := by
    simpa only [intervalPullbackLeft, Category.assoc] using
      fiberwisePullbackKanComparison_unit_left p f g
  have hur : continuousKanReplacementUnit.app (fiberwiseIntervalPullback p f g) ≫
      fiberwisePullbackKanComparison p f g ≫ intervalPullbackRight
        (continuousKanReplacement.map f) (continuousKanReplacement.map g) =
      fiberwiseIntervalPullbackRight p f g ≫ continuousKanReplacementUnit.app D := by
    simpa only [intervalPullbackRight, Category.assoc] using
      fiberwisePullbackKanComparison_unit_right p f g
  apply intervalPullback_hom_ext
  · simp only [Category.assoc]
    rw [hp]
    exact relativePathSquareCurry_restrict p f g A.ι d.boundaryHomotopy.h F
      (relativePathComparison_side d hk he F hF)
  · change ((A.ι ▷ (Δ[1] : SSet.{u})) ≫ L) ≫ intervalPullbackLeft
      (continuousKanReplacement.map f) (continuousKanReplacement.map g) =
        d.boundaryHomotopy.h ≫ (continuousKanReplacementUnit.app
          (fiberwiseIntervalPullback p f g) ≫ (fiberwisePullbackKanComparison p f g ≫
            intervalPullbackLeft (continuousKanReplacement.map f) (continuousKanReplacement.map g)))
    rw [hul, Category.assoc, hl,
      ← Category.assoc, d.left_restrict, Category.assoc]
  · change ((A.ι ▷ (Δ[1] : SSet.{u})) ≫ L) ≫ intervalPullbackRight
      (continuousKanReplacement.map f) (continuousKanReplacement.map g) =
        d.boundaryHomotopy.h ≫ (continuousKanReplacementUnit.app
          (fiberwiseIntervalPullback p f g) ≫ (fiberwisePullbackKanComparison p f g ≫
            intervalPullbackRight (continuousKanReplacement.map f)
              (continuousKanReplacement.map g)))
    rw [hur, Category.assoc, hr,
      ← Category.assoc, d.right_restrict, Category.assoc]

end SerrePositivity.InfinityCategories.F2
