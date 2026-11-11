module

public import SerrePositivity.KST.Spectra.ParametricLoopExchangeFamily
public import SerrePositivity.KST.Spectra.LoopExchangeFamilyTrace
public import SerrePositivity.KST.Spectra.PointedIntervalIhomSquare

/-!
概要：元の射影比較正方形を全パラメータ内部 Hom へ移し、同じ入力へ制限する。
方針：元の二次元射を ihomAction と前合成へ送り、実辺の厳密可換式を使う。
規約：元の区間と射影比較を選び直さない。使われ方：全族自然性の共通終辺。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.ParametricLoopExchangeFamily
open LoopExchangePaths
variable {S : PointedSimplicialSet.{u}} (I : ParametricLoopExchangeFamily S)
variable {P A Y Z : PointedSimplicialSet.{u}} [KanComplex Y.right] [KanComplex Z.right]
  (a : Y ⟶ PointedObject.basedHom S Z) (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right)
  (b : A ⟶ PointedObject.basedHom P (doubleLoop Y))

/-- 元の同じ射影比較へ内部 Hom を施した実正方形。 -/
def exchangeIhomProjectionSquare :=
  PointedMapping.VerticalPath.basedIhomSquare
    ((LoopExchangeFamily.exchange I.underlying a ha).basedPost (doublePost a))
    ((I.underlying.interval Z).pre (doublePost a))
    (LoopExchangeFamily.projectionSquare I.underlying a ha) P

/-- 全族の射影比較を同じ入力へ制限し、普遍終辺の合成入力と照合する。 -/
def exchangePreProjectionSquare :
    SSet.Homotopy
      (((((LoopExchangeFamily.exchange I.underlying a ha).basedIhomMap P).basedPost
        (PointedObject.basedHomMap P (doublePost a))).pre b).path)
      ((((I.underlying.interval Z).basedIhomMap P).pre
        (b ≫ PointedObject.basedHomMap P (doublePost a))).path) where
  h := (exchangeIhomProjectionSquare I a ha (P := P)).h ≫
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed b
      (PointedObject.basedHom P (doubleLoop (PointedObject.basedHom S Z)))).right
  h₀ := by
    rw [← Category.assoc, (exchangeIhomProjectionSquare I a ha (P := P)).h₀]
    exact congrArg (· ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed b _).right)
      ((LoopExchangeFamily.exchange I.underlying a ha).basedIhomMap_post_path P (doublePost a))
  h₁ := by
    rw [← Category.assoc, (exchangeIhomProjectionSquare I a ha (P := P)).h₁]
    exact (congrArg (· ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed b _).right)
      ((I.underlying.interval Z).basedIhomMap_pre_path_natural P (doublePost a))).trans
      (((I.underlying.interval Z).basedIhomMap P).pre_pre_path
        (PointedObject.basedHomMap P (doublePost a)) b)
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

/-- 同じ射影比較を、等しい指定の合成入力を持つ終辺へ表示する。 -/
def exchangePreProjectionSquareTo
    (c : A ⟶ PointedObject.basedHom P (doubleLoop (PointedObject.basedHom S Z)))
    (hc : b ≫ PointedObject.basedHomMap P (doublePost a) = c) :
    SSet.Homotopy
      (((((LoopExchangeFamily.exchange I.underlying a ha).basedIhomMap P).basedPost
        (PointedObject.basedHomMap P (doublePost a))).pre b).path)
      ((((I.underlying.interval Z).basedIhomMap P).pre c).path) where
  h := (exchangePreProjectionSquare I a ha b).h
  h₀ := (exchangePreProjectionSquare I a ha b).h₀
  h₁ := (exchangePreProjectionSquare I a ha b).h₁.trans
    (congrArg (fun j => (((I.underlying.interval Z).basedIhomMap P).pre j).path) hc)
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

/-- 同じ左境界全体は、元の交換作用の全パラメータ像で一定。 -/
lemma exchangePreProjectionSquare_start :
    SquareAdjustment.leftSide ≫ (exchangePreProjectionSquare I a ha b).h =
      SSet.const (PointedMapping.familyVertex
        (b ≫ PointedObject.basedHomMap P (swap Y ≫ doublePost a))) := by
  change SquareAdjustment.leftSide ≫
    (((LoopExchangeFamily.projectionSquare I.underlying a ha).h ≫
      (PointedMapping.ihomAction P (doubleLoop Y)
        (doubleLoop (PointedObject.basedHom S Z))).right) ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed b _).right) = _
  rw [← Category.assoc, ← Category.assoc,
    LoopExchangeFamily.projectionSquare_start I.underlying,
    SSet.const_comp, PointedMapping.familyVertex_ihomAction,
    SSet.const_comp, PointedMapping.familyVertex_pre]

/-- 同じ右境界全体も、元の反転作用の全パラメータ像で一定。 -/
lemma exchangePreProjectionSquare_finish :
    SquareAdjustment.rightSide ≫ (exchangePreProjectionSquare I a ha b).h =
      SSet.const (PointedMapping.familyVertex
        (b ≫ PointedObject.basedHomMap P (reversal Y ≫ doublePost a))) := by
  change SquareAdjustment.rightSide ≫
    (((LoopExchangeFamily.projectionSquare I.underlying a ha).h ≫
      (PointedMapping.ihomAction P (doubleLoop Y)
        (doubleLoop (PointedObject.basedHom S Z))).right) ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed b _).right) = _
  rw [← Category.assoc, ← Category.assoc,
    LoopExchangeFamily.projectionSquare_finish I.underlying,
    SSet.const_comp, PointedMapping.familyVertex_ihomAction,
    SSet.const_comp, PointedMapping.familyVertex_pre]

end SerrePositivity.KST.Spectra.ParametricLoopExchangeFamily
