module
public import SerrePositivity.KST.Fibration.ComposableWeakArrowEndpointPullback
public import SerrePositivity.KST.Fibration.RelativeCofiberBaseChange

/-! # 第二辺の相対 cofiber 補完を全て保持した二辺の object 比較

元の終点への厳密基底変換に相対 K-1 と K-2 を適用する。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 第一 W 辺の終点上で、第二辺の全相対 cofiber 図式を保持する object 単体集合。 -/
def completedTwoObjects {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) : SSet.{u} :=
  pullback
    (objectSConstructionFunctor.map (relativeCofiberSubobject
      (ClosedStablePredicate.top (sInputModel B)) (kernelClosedPredicate q)))
    (objectSConstructionFunctor.map (weakArrowTargetTopExact q))

/-- 補完した二辺から、元の第一辺と第二辺の核値 cofiber を抽出する実際の射対。 -/
def completedTwoObjectComparison {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    completedTwoObjects q ⟶ objectSConstructionFunctor.obj (weakArrowModel q) ⊗
      objectSConstructionFunctor.obj (closedStableModel (kernelClosedPredicate q)) :=
  lift (pullback.snd _ _) (pullback.fst _ _ ≫
    objectSConstructionFunctor.map (relativeCofiberQuotient
      (ClosedStablePredicate.top (sInputModel B)) (kernelClosedPredicate q)))

/-- 同じ元の射対は相対左 fiber の定理の基底変換と Quillen A により局所化同型。 -/
theorem completedTwoObjectComparison_localized_isIso {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    IsIso (AnodyneHomotopy.anodyneQ.map (completedTwoObjectComparison q)) :=
  relativeCofiberBaseChange_localized_isIso (ClosedStablePredicate.top (sInputModel B))
    (kernelClosedPredicate q) (IsPullback.of_hasPullback _ _)

end SerrePositivity.KST.Fibration
