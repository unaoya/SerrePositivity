module

public import SerrePositivity.KST.Spectra.LoopExchangeFamilyTrace
public import SerrePositivity.KST.Spectra.ParametricLoopExchangeFamily
public import SerrePositivity.KST.Spectra.DoubleLoopParametricSquare
public import SerrePositivity.KST.Spectra.PointedIntervalNaturality
public import SerrePositivity.KST.Spectra.PointedIntervalInputBoundary

/-!
概要：交換トレースの全族後合成と普遍全族自然性の入力制限を、同じ共通辺で表示する。
方針：元の二次元射へ内部 Hom の同じ前後合成を作用させる。
規約：区間や正方形を再選択しない。使われ方：交換の自然性の指定境界付き貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.ParametricLoopExchangeFamily
open LoopExchangePaths
variable {S : PointedSimplicialSet.{u}} (I : ParametricLoopExchangeFamily S)

variable {P Y Z Z' : PointedSimplicialSet.{u}} [KanComplex Y.right]
  [KanComplex Z.right] [KanComplex Z'.right]
  (h : Y ⟶ PointedObject.basedHom S Z)
  (hh : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism h.right) (v : P ⟶ PointedObject.basedHom Z Z')

/-- 同じ射影比較の二次元射を、同じ内部 Hom の二重 loop の後合成へ写す。 -/
def exchangePostProjectionSquare :
    SSet.Homotopy
      ((((LoopExchangeFamily.exchange I.underlying h hh).basedPost (doublePost h)).basedPost
        (TwoLoopSource.standardParametricPost S v)).path)
      ((((I.underlying.interval Z).pre (doublePost h)).basedPost
        (TwoLoopSource.standardParametricPost S v)).path) where
  h := (LoopExchangeFamily.projectionSquare I.underlying h hh).h ≫
    (PointedObject.basedHomMap (doubleLoop Y) (TwoLoopSource.standardParametricPost S v)).right
  h₀ := by rw [← Category.assoc, (LoopExchangeFamily.projectionSquare I.underlying h hh).h₀]; rfl
  h₁ := by rw [← Category.assoc, (LoopExchangeFamily.projectionSquare I.underlying h hh).h₁]; rfl
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

omit [KanComplex Z'.right] in
/-- 標的後合成した射影比較の左辺全体は、同じ交換作用の像で一定。 -/
lemma exchangePostProjectionSquare_start :
    SquareAdjustment.leftSide ≫ (exchangePostProjectionSquare I h hh v).h =
      SSet.const (PointedMapping.familyVertex
        ((swap Y ≫ doublePost h) ≫ TwoLoopSource.standardParametricPost S v)) := by
  change SquareAdjustment.leftSide ≫
    ((LoopExchangeFamily.projectionSquare I.underlying h hh).h ≫ _) = _
  rw [← Category.assoc, LoopExchangeFamily.projectionSquare_start I.underlying, SSet.const_comp,
    PointedMapping.familyVertex_post]

omit [KanComplex Z'.right] in
/-- 標的後合成した射影比較の右辺全体も、同じ反転作用の像で一定。 -/
lemma exchangePostProjectionSquare_finish :
    SquareAdjustment.rightSide ≫ (exchangePostProjectionSquare I h hh v).h =
      SSet.const (PointedMapping.familyVertex
        ((reversal Y ≫ doublePost h) ≫ TwoLoopSource.standardParametricPost S v)) := by
  change SquareAdjustment.rightSide ≫
    ((LoopExchangeFamily.projectionSquare I.underlying h hh).h ≫ _) = _
  rw [← Category.assoc, LoopExchangeFamily.projectionSquare_finish I.underlying, SSet.const_comp,
    PointedMapping.familyVertex_post]

/-- 元の普遍自然性正方形を、同じ Ω 条件の二重後合成へ制限する。 -/
def exchangeRestrictedNaturalitySquare :
    SSet.Homotopy
      ((((I.underlying.interval Z).pre (doublePost h)).basedPost
        (TwoLoopSource.standardParametricPost S v)).path)
      ((((I.underlying.interval Z').basedIhomMap P).pre
        (doublePost h ≫ TwoLoopSource.standardParametricPost S v)).path) where
  h := (I.naturality v).h ≫
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (doublePost h)
      (PointedObject.basedHom P (doubleLoop (PointedObject.basedHom S Z')))).right
  h₀ := by
    rw [← Category.assoc, (I.naturality v).h₀]
    exact (I.underlying.interval Z).pre_basedPost_path
      (doublePost h) (TwoLoopSource.standardParametricPost S v)
  h₁ := by
    rw [← Category.assoc, (I.naturality v).h₁]
    exact ((I.underlying.interval Z').basedIhomMap P).pre_pre_path
      (TwoLoopSource.standardParametricPost S v) (doublePost h)
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

omit [KanComplex Y.right] [KanComplex Z.right] [KanComplex Z'.right] in
/-- 二つの同じ後合成の間で、元の交換作用の厳密な像を照合する。 -/
lemma doublePost_loopPost_swap :
    (swap Y ≫ doublePost h) ≫ TwoLoopSource.standardParametricPost S v =
      doublePost h ≫ (TwoLoopSource.standardParametricPost S v ≫
        PointedObject.basedHomMap P (swap (PointedObject.basedHom S Z'))) := by
  have hc := swap_doubleParametricPost (v ≫ PointedMapping.ihomAction S Z Z')
  change swap (PointedObject.basedHom S Z) ≫ TwoLoopSource.standardParametricPost S v =
    TwoLoopSource.standardParametricPost S v ≫
      PointedObject.basedHomMap P (swap (PointedObject.basedHom S Z')) at hc
  rw [swap_doublePost h, Category.assoc, hc]

omit [KanComplex Y.right] [KanComplex Z.right] [KanComplex Z'.right] in
/-- 二つの同じ後合成の間で、元の反転作用の厳密な像も照合する。 -/
lemma doublePost_loopPost_reversal :
    (reversal Y ≫ doublePost h) ≫ TwoLoopSource.standardParametricPost S v =
      doublePost h ≫ (TwoLoopSource.standardParametricPost S v ≫
        PointedObject.basedHomMap P (reversal (PointedObject.basedHom S Z'))) := by
  have hc := reversal_doubleParametricPost (v ≫ PointedMapping.ihomAction S Z Z')
  change reversal (PointedObject.basedHom S Z) ≫ TwoLoopSource.standardParametricPost S v =
    TwoLoopSource.standardParametricPost S v ≫
      PointedObject.basedHomMap P (reversal (PointedObject.basedHom S Z')) at hc
  rw [reversal_doublePost h, Category.assoc, hc]

omit [KanComplex Y.right] in
/-- 制限した自然性正方形の左辺は、標的後合成した射影比較と同じ一定境界。 -/
lemma exchangeRestrictedNaturalitySquare_start :
    SquareAdjustment.leftSide ≫ (exchangeRestrictedNaturalitySquare I h v).h =
      SSet.const (PointedMapping.familyVertex
        ((swap Y ≫ doublePost h) ≫ TwoLoopSource.standardParametricPost S v)) := by
  change SquareAdjustment.leftSide ≫ ((I.naturality v).h ≫ _) = _
  rw [← Category.assoc, I.start, SSet.const_comp]
  have hv : (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (doublePost h)
      (PointedObject.basedHom P (doubleLoop (PointedObject.basedHom S Z')))).right.app _
        (PointedMapping.familyVertex (TwoLoopSource.standardParametricPost S v ≫
          PointedObject.basedHomMap P (swap (PointedObject.basedHom S Z')))) =
      PointedMapping.familyVertex (doublePost h ≫ (TwoLoopSource.standardParametricPost S v ≫
        PointedObject.basedHomMap P (swap (PointedObject.basedHom S Z')))) :=
    PointedMapping.familyVertex_pre _ _
  rw [hv, ← doublePost_loopPost_swap h v]

omit [KanComplex Y.right] in
/-- 制限した自然性正方形の右辺も、標的後合成した射影比較と同じ一定境界。 -/
lemma exchangeRestrictedNaturalitySquare_finish :
    SquareAdjustment.rightSide ≫ (exchangeRestrictedNaturalitySquare I h v).h =
      SSet.const (PointedMapping.familyVertex
        ((reversal Y ≫ doublePost h) ≫ TwoLoopSource.standardParametricPost S v)) := by
  change SquareAdjustment.rightSide ≫ ((I.naturality v).h ≫ _) = _
  rw [← Category.assoc, I.finish, SSet.const_comp]
  have hv : (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (doublePost h)
      (PointedObject.basedHom P (doubleLoop (PointedObject.basedHom S Z')))).right.app _
        (PointedMapping.familyVertex (TwoLoopSource.standardParametricPost S v ≫
          PointedObject.basedHomMap P (reversal (PointedObject.basedHom S Z')))) =
      PointedMapping.familyVertex (doublePost h ≫ (TwoLoopSource.standardParametricPost S v ≫
        PointedObject.basedHomMap P (reversal (PointedObject.basedHom S Z')))) :=
    PointedMapping.familyVertex_pre _ _
  rw [hv, ← doublePost_loopPost_reversal h v]

end SerrePositivity.KST.Spectra.ParametricLoopExchangeFamily
