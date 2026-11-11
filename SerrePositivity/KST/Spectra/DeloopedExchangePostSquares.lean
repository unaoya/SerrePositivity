module

public import SerrePositivity.KST.Spectra.DeloopedExchangeProjectionSquare
public import SerrePositivity.KST.Spectra.TripleCircleLoopExchangeBoundary

/-!
概要：交換トレースの標的後合成と普遍自然性の入力制限を、同じ共通辺で表示する。
方針：元の二次元射へ内部 Hom の同じ前後合成を作用させる。
規約：区間や正方形を再選択しない。使われ方：交換の自然性の指定境界付き貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.LoopExchangePaths

variable {Y Z Z' : PointedSimplicialSet.{u}} [KanComplex Y.right]
  [KanComplex Z.right] [KanComplex Z'.right]
  (h : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z)
  (hh : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism h.right) (v : Z ⟶ Z')

/-- 同じ射影比較の二次元射を、元の三重 loop の後合成へ写す。 -/
def exchangePostProjectionSquare :
    SSet.Homotopy
      ((((deloopedExchange h hh).basedPost (doublePost h)).basedPost
        (TripleCircle.loopPost v)).path)
      ((((TripleCircle.loopExchangeInterval Z).pre (doublePost h)).basedPost
        (TripleCircle.loopPost v)).path) where
  h := (exchangeProjectionSquare h hh).h ≫
    (PointedObject.basedHomMap (doubleLoop Y) (TripleCircle.loopPost v)).right
  h₀ := by rw [← Category.assoc, (exchangeProjectionSquare h hh).h₀]; rfl
  h₁ := by rw [← Category.assoc, (exchangeProjectionSquare h hh).h₁]; rfl
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

omit [KanComplex Z'.right] in
/-- 標的後合成した射影比較の左辺全体は、同じ交換作用の像で一定。 -/
lemma exchangePostProjectionSquare_start :
    SquareAdjustment.leftSide ≫ (exchangePostProjectionSquare h hh v).h =
      SSet.const (PointedMapping.familyVertex
        ((swap Y ≫ doublePost h) ≫ TripleCircle.loopPost v)) := by
  change SquareAdjustment.leftSide ≫ ((exchangeProjectionSquare h hh).h ≫ _) = _
  rw [← Category.assoc, exchangeProjectionSquare_start, SSet.const_comp,
    PointedMapping.familyVertex_post]

omit [KanComplex Z'.right] in
/-- 標的後合成した射影比較の右辺全体も、同じ反転作用の像で一定。 -/
lemma exchangePostProjectionSquare_finish :
    SquareAdjustment.rightSide ≫ (exchangePostProjectionSquare h hh v).h =
      SSet.const (PointedMapping.familyVertex
        ((reversal Y ≫ doublePost h) ≫ TripleCircle.loopPost v)) := by
  change SquareAdjustment.rightSide ≫ ((exchangeProjectionSquare h hh).h ≫ _) = _
  rw [← Category.assoc, exchangeProjectionSquare_finish, SSet.const_comp,
    PointedMapping.familyVertex_post]

/-- 元の普遍自然性正方形を、同じ Ω 条件の二重後合成へ制限する。 -/
def exchangeRestrictedNaturalitySquare :
    SSet.Homotopy
      ((((TripleCircle.loopExchangeInterval Z).pre (doublePost h)).basedPost
        (TripleCircle.loopPost v)).path)
      (((TripleCircle.loopExchangeInterval Z').pre
        (doublePost h ≫ TripleCircle.loopPost v)).path) where
  h := (TripleCircle.loopExchangeNaturalitySquare v).h ≫
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (doublePost h)
      (doubleLoop (PointedObject.basedHom CirclePower.space.{u} Z'))).right
  h₀ := by
    rw [← Category.assoc, (TripleCircle.loopExchangeNaturalitySquare v).h₀]
    exact (TripleCircle.loopExchangeInterval Z).pre_basedPost_path
      (doublePost h) (TripleCircle.loopPost v)
  h₁ := by
    rw [← Category.assoc, (TripleCircle.loopExchangeNaturalitySquare v).h₁]
    exact (TripleCircle.loopExchangeInterval Z').pre_pre_path
      (TripleCircle.loopPost v) (doublePost h)
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

omit [KanComplex Y.right] [KanComplex Z.right] [KanComplex Z'.right] in
/-- 二つの同じ後合成の間で、元の交換作用の厳密な像を照合する。 -/
lemma doublePost_loopPost_swap :
    (swap Y ≫ doublePost h) ≫ TripleCircle.loopPost v =
      doublePost h ≫ (TripleCircle.loopPost v ≫
        swap (PointedObject.basedHom CirclePower.space.{u} Z')) := by
  have hc := swap_doublePost (PointedObject.basedHomMap CirclePower.space.{u} v)
  change swap (PointedObject.basedHom CirclePower.space.{u} Z) ≫ TripleCircle.loopPost v =
    TripleCircle.loopPost v ≫ swap (PointedObject.basedHom CirclePower.space.{u} Z') at hc
  rw [swap_doublePost h, Category.assoc, hc]

omit [KanComplex Y.right] [KanComplex Z.right] [KanComplex Z'.right] in
/-- 二つの同じ後合成の間で、元の反転作用の厳密な像も照合する。 -/
lemma doublePost_loopPost_reversal :
    (reversal Y ≫ doublePost h) ≫ TripleCircle.loopPost v =
      doublePost h ≫ (TripleCircle.loopPost v ≫
        reversal (PointedObject.basedHom CirclePower.space.{u} Z')) := by
  have hc := reversal_doublePost (PointedObject.basedHomMap CirclePower.space.{u} v)
  change reversal (PointedObject.basedHom CirclePower.space.{u} Z) ≫ TripleCircle.loopPost v =
    TripleCircle.loopPost v ≫ reversal (PointedObject.basedHom CirclePower.space.{u} Z') at hc
  rw [reversal_doublePost h, Category.assoc, hc]

omit [KanComplex Y.right] in
/-- 制限した自然性正方形の左辺は、標的後合成した射影比較と同じ一定境界。 -/
lemma exchangeRestrictedNaturalitySquare_start :
    SquareAdjustment.leftSide ≫ (exchangeRestrictedNaturalitySquare h v).h =
      SSet.const (PointedMapping.familyVertex
        ((swap Y ≫ doublePost h) ≫ TripleCircle.loopPost v)) := by
  change SquareAdjustment.leftSide ≫ ((TripleCircle.loopExchangeNaturalitySquare v).h ≫ _) = _
  rw [← Category.assoc, TripleCircle.loopExchangeNaturalitySquare_start_vertex, SSet.const_comp]
  have hv : (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (doublePost h)
      (doubleLoop (PointedObject.basedHom CirclePower.space.{u} Z'))).right.app _
        (PointedMapping.familyVertex (TripleCircle.loopPost v ≫
          swap (PointedObject.basedHom CirclePower.space.{u} Z'))) =
      PointedMapping.familyVertex (doublePost h ≫ (TripleCircle.loopPost v ≫
        swap (PointedObject.basedHom CirclePower.space.{u} Z'))) :=
    PointedMapping.familyVertex_pre _ _
  rw [hv, ← doublePost_loopPost_swap h v]

omit [KanComplex Y.right] in
/-- 制限した自然性正方形の右辺も、標的後合成した射影比較と同じ一定境界。 -/
lemma exchangeRestrictedNaturalitySquare_finish :
    SquareAdjustment.rightSide ≫ (exchangeRestrictedNaturalitySquare h v).h =
      SSet.const (PointedMapping.familyVertex
        ((reversal Y ≫ doublePost h) ≫ TripleCircle.loopPost v)) := by
  change SquareAdjustment.rightSide ≫ ((TripleCircle.loopExchangeNaturalitySquare v).h ≫ _) = _
  rw [← Category.assoc, TripleCircle.loopExchangeNaturalitySquare_finish_vertex, SSet.const_comp]
  have hv : (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (doublePost h)
      (doubleLoop (PointedObject.basedHom CirclePower.space.{u} Z'))).right.app _
        (PointedMapping.familyVertex (TripleCircle.loopPost v ≫
          reversal (PointedObject.basedHom CirclePower.space.{u} Z'))) =
      PointedMapping.familyVertex (doublePost h ≫ (TripleCircle.loopPost v ≫
        reversal (PointedObject.basedHom CirclePower.space.{u} Z'))) :=
    PointedMapping.familyVertex_pre _ _
  rw [hv, ← doublePost_loopPost_reversal h v]

end SerrePositivity.KST.Spectra.LoopExchangePaths
