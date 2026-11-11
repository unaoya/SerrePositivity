module

public import SerrePositivity.KST.Spectra.LoopExchangeFamilyTrace
public import SerrePositivity.KST.Spectra.LoopExchangeFamilyNaturalitySides
public import SerrePositivity.KST.Spectra.ConstantBoundarySquareCodifference

/-!
概要：二つの Ω 条件の厳密な可換式から、交換区間の像の四辺固定自然性を構成する。
方針：同じ普遍終辺へ至る二正方形を、指定した定数二単体上の外ホーンで比較する。
規約：元の二正方形と比較三角形を保持する。使われ方：π 同型に沿う upstairs 比較の反映。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.KST.Spectra.LoopExchangeFamily
open LoopExchangePaths
variable {S : PointedSimplicialSet.{u}} (I : LoopExchangeFamily S)

variable {Y Y' Z Z' : PointedSimplicialSet.{u}} [KanComplex Y.right] [KanComplex Y'.right]
  [KanComplex Z.right] [KanComplex Z'.right]
  (h : Y ⟶ PointedObject.basedHom S Z)
  (hh : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism h.right)
  (h' : Y' ⟶ PointedObject.basedHom S Z')
  (hh' : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism h'.right) (v : Y ⟶ Y') (w : Z ⟶ Z')
  (hc : h ≫ PointedObject.basedHomMap S w = v ≫ h')

include hc

/-- 共通の普遍終辺を持つ二つの実正方形を、同じ定数境界上で比較した実三角形。 -/
def exchangeNaturalityImageData :
    SquareAdjustment.ConstantBoundaryCodifference
      (exchangePostComparisonSquare I h hh w) (exchangeAlignedPreSquare I h h' hh' v w hc)
      (PointedMapping.familyVertex ((swap Y ≫ doublePost h) ≫ TwoLoopSource.loopPost S w))
      (PointedMapping.familyVertex ((reversal Y ≫ doublePost h) ≫ TwoLoopSource.loopPost S w)) := by
  let targetKan : KanComplex (PointedObject.basedHom (doubleLoop Y)
      (doubleLoop (PointedObject.basedHom S Z'))).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  exact SquareAdjustment.ConstantBoundaryCodifference.choose _ _ _ _
    (exchangePostComparisonSquare_start I h hh w) (exchangePostComparisonSquare_finish I h hh w)
    (exchangeAlignedPreSquare_start I h h' hh' v w hc)
    (exchangeAlignedPreSquare_finish I h h' hh' v w hc)

omit [KanComplex Y'.right] [KanComplex Z'.right] in
/-- 始辺は、元の交換区間へ源射と標的 Ω 条件を後合成した同じ像。 -/
lemma exchangeNaturalityImage_zero :
    (((exchange I h hh).basedPost (doublePost v)).basedPost (doublePost h')).path =
      (((exchange I h hh).basedPost (doublePost h)).basedPost
        (TwoLoopSource.loopPost S w)).path := by
  rw [PointedMapping.VerticalPath.basedPost_basedPost_path,
    PointedMapping.VerticalPath.basedPost_basedPost_path, doublePost_square h h' v w hc]

/-- 元の交換区間同士の前後合成像を、同じ Ω 条件の射影後で結ぶ実正方形。 -/
def exchangeNaturalityImageSquare :
    SSet.Homotopy
      ((((exchange I h hh).basedPost (doublePost v)).basedPost (doublePost h')).path)
      ((((exchange I h' hh').pre (doublePost v)).basedPost (doublePost h')).path) where
  h := (exchangeNaturalityImageData I h hh h' hh' v w hc).homotopy.h
  h₀ := (exchangeNaturalityImageData I h hh h' hh' v w hc).homotopy.h₀.trans
    (exchangeNaturalityImage_zero I h hh h' v w hc).symm
  h₁ := (exchangeNaturalityImageData I h hh h' hh' v w hc).homotopy.h₁.trans
    ((exchange I h' hh').pre_basedPost_path (doublePost v) (doublePost h'))
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

/-- 像の自然性正方形の左辺全体は、元の交換作用の同じ射影像で一定。 -/
lemma exchangeNaturalityImageSquare_start :
    SquareAdjustment.leftSide ≫ (exchangeNaturalityImageSquare I h hh h' hh' v w hc).h =
      SSet.const (PointedMapping.familyVertex
        ((swap Y ≫ doublePost v) ≫ doublePost h')) := by
  have hb := SquareAdjustment.ConstantBoundaryCodifference.start _ _ _ _
    (exchangeNaturalityImageData I h hh h' hh' v w hc)
  have he : (swap Y ≫ doublePost h) ≫ TwoLoopSource.loopPost S w =
      (swap Y ≫ doublePost v) ≫ doublePost h' := by
    rw [Category.assoc, doublePost_square h h' v w hc, ← Category.assoc]
  exact hb.trans (congrArg (fun f => SSet.const (PointedMapping.familyVertex f)) he)

/-- 右辺全体も、元の反転作用の同じ射影像で一定。 -/
lemma exchangeNaturalityImageSquare_finish :
    SquareAdjustment.rightSide ≫ (exchangeNaturalityImageSquare I h hh h' hh' v w hc).h =
      SSet.const (PointedMapping.familyVertex
        ((reversal Y ≫ doublePost v) ≫ doublePost h')) := by
  have hb := SquareAdjustment.ConstantBoundaryCodifference.finish _ _ _ _
    (exchangeNaturalityImageData I h hh h' hh' v w hc)
  have he : (reversal Y ≫ doublePost h) ≫ TwoLoopSource.loopPost S w =
      (reversal Y ≫ doublePost v) ≫ doublePost h' := by
    rw [Category.assoc, doublePost_square h h' v w hc, ← Category.assoc]
  exact hb.trans (congrArg (fun f => SSet.const (PointedMapping.familyVertex f)) he)

end SerrePositivity.KST.Spectra.LoopExchangeFamily
