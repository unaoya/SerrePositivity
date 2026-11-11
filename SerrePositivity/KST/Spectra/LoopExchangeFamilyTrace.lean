module

public import SerrePositivity.KST.Spectra.LoopExchangeFamily
public import SerrePositivity.KST.Spectra.DeloopedTracedExchange
public import SerrePositivity.KST.Spectra.PointedTracedPathSquare

/-!
概要：実証済みの交換族を、元の内側の源に対する随伴へ直接移す。
方針：同じ交換区間を二重後合成の写像 path に両端固定で持ち上げる。
規約：元の随伴・普遍区間・全トレースを保持する。使われ方：通常円の元の exchange の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.KST.Spectra.LoopExchangeFamily
open LoopExchangePaths

variable {S Y Z : PointedSimplicialSet.{u}} (I : LoopExchangeFamily S)
  [KanComplex Y.right] [KanComplex Z.right] (a : Y ⟶ PointedObject.basedHom S Z)

omit [KanComplex Y.right] in
/-- 元の随伴の二重後合成へ制限した、同じ普遍交換区間の端点表示。 -/
def targetInterval : PointedMapping.VerticalPath (PointedObject.toPoint
    (doubleLoop (PointedObject.basedHom S Z)))
    (swap Y ≫ doublePost a) (reversal Y ≫ doublePost a) :=
  ((I.interval Z).pre (doublePost a)).changeEndpoints (swap_doublePost a) (reversal_doublePost a)

/-- 元の随伴に沿う、同じ普遍区間全体と両端の定数 path を保つ移送。 -/
def trace (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right) :
    PointedMapping.TracedPathLift (doublePost a) (targetInterval I a) :=
  PointedMapping.TracedPathLift.choose (doublePost a) (doublePost_piIsomorphism a ha)
    (targetInterval I a)

/-- 元の対象自身の交換と反転を結ぶ、同じトレースから回収した実区間。 -/
def exchange (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right) :
    PointedMapping.VerticalPath (PointedObject.toPoint (doubleLoop Y)) (swap Y) (reversal Y) :=
  (trace I a ha).path

/-- 元の随伴の二重後合成での区間の像と、同じ普遍区間を結ぶ実正方形。 -/
def projectionSquare (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right) :
    SSet.Homotopy (((exchange I a ha).basedPost (doublePost a)).path)
      (((I.interval Z).pre (doublePost a)).path) := (trace I a ha).traceSquare

/-- 同じ射影比較の左辺全体は、元の交換作用の像で一定。 -/
lemma projectionSquare_start (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right) :
    SquareAdjustment.leftSide ≫ (projectionSquare I a ha).h =
      SSet.const (PointedMapping.familyVertex (swap Y ≫ doublePost a)) :=
  (trace I a ha).traceSquare_start

/-- 同じ射影比較の右辺全体も、元の反転作用の像で一定。 -/
lemma projectionSquare_finish (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right) :
    SquareAdjustment.rightSide ≫ (projectionSquare I a ha).h =
      SSet.const (PointedMapping.familyVertex (reversal Y ≫ doublePost a)) :=
  (trace I a ha).traceSquare_finish

/-- 写像 path の射影は、選んだ同じ普遍区間全体の入力制限そのもの。 -/
lemma trace_projection (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right) :
    (trace I a ha).trace ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection (PointedObject.basedHomMap (doubleLoop Y) (doublePost a))).right =
        ((I.interval Z).pre (doublePost a)).path := (trace I a ha).projection

/-- 写像 path の源射影も、元の対象へ移送した同じ区間の辺全体。 -/
lemma trace_retraction (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right) :
    (trace I a ha).trace ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction (PointedObject.basedHomMap (doubleLoop Y) (doublePost a))).right =
        (exchange I a ha).path := (trace I a ha).retraction

end SerrePositivity.KST.Spectra.LoopExchangeFamily
