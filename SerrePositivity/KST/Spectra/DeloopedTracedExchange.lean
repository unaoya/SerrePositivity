module

public import SerrePositivity.KST.Spectra.TripleCircleLoopExchangeNaturality
public import SerrePositivity.KST.Spectra.PointedTracedPathLift
public import SerrePositivity.KST.Spectra.KanLoopLift

/-!
概要：一つの三重円の交換区間を、Ω 条件の π 同型に沿って元の対象へ移す。
方針：二重後合成の写像 path に、元の普遍区間と両端の定数 path を保持する。
規約：対象別の成分等式から区間を選ばない。使われ方：単位構造区間の高次自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.LoopExchangePaths

/-- 二つの Kan 円による元の二重後合成。 -/
def doublePost {Y V : PointedSimplicialSet.{u}} (h : Y ⟶ V) :
    doubleLoop Y ⟶ doubleLoop V :=
  PointedObject.basedHomMap CirclePower.space.{u}
    (PointedObject.basedHomMap CirclePower.space.{u} h)

/-- 源の二円の交換は、元の二重後合成と厳密に可換。 -/
lemma swap_doublePost {Y V : PointedSimplicialSet.{u}} (h : Y ⟶ V) :
    swap Y ≫ doublePost h = doublePost h ≫ swap V :=
  (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeTarget.natural_post CirclePower.space.{u} CirclePower.space.{u} h).symm

/-- 源の内側の反転も、元の二重後合成と厳密に可換。 -/
lemma reversal_doublePost {Y V : PointedSimplicialSet.{u}} (h : Y ⟶ V) :
    reversal Y ≫ doublePost h = doublePost h ≫ reversal V := by
  have hn := ((MonoidalClosed.pre (CirclePower.integerPowerMap.{u} (-1))).naturality h).symm
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hn
  change _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} (-1)) Y ≫
      PointedObject.basedHomMap CirclePower.space.{u} h =
    PointedObject.basedHomMap CirclePower.space.{u} h ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} (-1)) V at hn
  have hv := congrArg ((ihom CirclePower.space.{u}).map) hn
  simp only [Functor.map_comp] at hv
  exact hv

/-- Ω 条件の π 同型は元の二重後合成でも全基点 π 同型。 -/
lemma doublePost_piIsomorphism {Y V : PointedSimplicialSet.{u}}
    [KanComplex Y.right] [KanComplex V.right] (h : Y ⟶ V)
    (hh : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism h.right) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (doublePost h).right :=
  PointedMapping.post_piIsomorphism CirclePower.space.{u}
    (PointedObject.basedHomMap CirclePower.space.{u} h)
    (PointedMapping.post_piIsomorphism CirclePower.space.{u} h hh)

variable {Y Z : PointedSimplicialSet.{u}} [KanComplex Y.right] [KanComplex Z.right]
  (h : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z)

omit [KanComplex Y.right] in
/-- 同じ普遍交換区間の像を、元の二つの作用の後合成として端点表示する。 -/
def exchangeTargetInterval :
    PointedMapping.VerticalPath (PointedObject.toPoint
      (doubleLoop (PointedObject.basedHom CirclePower.space.{u} Z)))
      (swap Y ≫ doublePost h) (reversal Y ≫ doublePost h) :=
  ((TripleCircle.loopExchangeInterval Z).pre (doublePost h)).changeEndpoints
    (swap_doublePost h) (reversal_doublePost h)

/-- Ω 対象への交換区間の移送は、同じ普遍区間全体の写像 path トレースを持つ。 -/
def exchangeTrace (hh : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism h.right) :
    PointedMapping.TracedPathLift (doublePost h) (exchangeTargetInterval h) :=
  PointedMapping.TracedPathLift.choose (doublePost h) (doublePost_piIsomorphism h hh)
    (exchangeTargetInterval h)

/-- 元の Ω 対象の二つの作用を結ぶ、トレースを保持した実際の交換区間。 -/
def deloopedExchange (hh : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism h.right) :
    PointedMapping.VerticalPath (PointedObject.toPoint (doubleLoop Y))
      (swap Y) (reversal Y) := (exchangeTrace h hh).path

/-- 写像 path の射影は、選んだ同じ普遍交換区間の入力制限に厳密一致する。 -/
lemma exchangeTrace_projection (hh : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism h.right) :
    (exchangeTrace h hh).trace ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection (PointedObject.basedHomMap (doubleLoop Y) (doublePost h))).right =
        ((TripleCircle.loopExchangeInterval Z).pre (doublePost h)).path :=
  (exchangeTrace h hh).projection

/-- 写像 path の源射影は、移送された交換区間の辺全体そのもの。 -/
lemma exchangeTrace_retraction (hh : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism h.right) :
    (exchangeTrace h hh).trace ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction (PointedObject.basedHomMap (doubleLoop Y) (doublePost h))).right =
        (deloopedExchange h hh).path := (exchangeTrace h hh).retraction

end SerrePositivity.KST.Spectra.LoopExchangePaths
