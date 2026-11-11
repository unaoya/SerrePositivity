module

public import SerrePositivity.KST.Spectra.LoopExchangeFamilyTrace
public import SerrePositivity.KST.Spectra.LoopExchangeFamilyNaturalityImage
public import SerrePositivity.KST.Spectra.PointedPathSquareEndpointReflection

/-!
概要：厳密な Ω 条件の可換式から、元の交換区間同士の四辺固定自然性を回収する。
方針：同じ射影後の正方形を、内部 Hom の写像 path 分解に両端境界固定で持ち上げる。
規約：元の区間・基底正方形へのトレースを保持する。使われ方：単位構造区間の高次自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
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

/-- 元の二交換区間を結び、指定した射影後の正方形への全トレースを保つ相対反映。 -/
def exchangeNaturalityReflection :=
  PointedMapping.pathEndpointSquareReflection
    ((exchange I h hh).basedPost (doublePost v))
    ((exchange I h' hh').pre (doublePost v))
    (swap_doublePost v) (reversal_doublePost v)
    (doublePost h') (doublePost_piIsomorphism h' hh')
    (exchangeNaturalityImageSquare I h hh h' hh' v w hc)
    (exchangeNaturalityImageSquare_start I h hh h' hh' v w hc)
    (exchangeNaturalityImageSquare_finish I h hh h' hh' v w hc)

/-- 元の交換区間同士の前後合成を、同じ反映データから回収した実自然性正方形。 -/
def exchangeNaturalitySquare :
    SSet.Homotopy (((exchange I h hh).basedPost (doublePost v)).path)
      (((exchange I h' hh').pre (doublePost v)).path) :=
  (exchangeNaturalityReflection I h hh h' hh' v w hc).homotopy

/-- 回収した自然性正方形の全境界は、元の同じ始点・終点で一定。 -/
lemma exchangeNaturalitySquare_boundary :
    (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ (exchangeNaturalitySquare I h hh h' hh' v w hc).h =
      intervalBoundaryFamily
        (SSet.const (PointedMapping.familyVertex (swap Y ≫ doublePost v)))
        (SSet.const (PointedMapping.familyVertex (reversal Y ≫ doublePost v))) := by
  exact PointedMapping.pathEndpointSquareReflection_boundary
    ((exchange I h hh).basedPost (doublePost v))
    ((exchange I h' hh').pre (doublePost v))
    (swap_doublePost v) (reversal_doublePost v)
    (doublePost h') (doublePost_piIsomorphism h' hh')
    (exchangeNaturalityImageSquare I h hh h' hh' v w hc)
    (exchangeNaturalityImageSquare_start I h hh h' hh' v w hc)
    (exchangeNaturalityImageSquare_finish I h hh h' hh' v w hc)

/-- 左辺全体は、元の交換作用の同じ像で一定。 -/
lemma exchangeNaturalitySquare_start :
    SquareAdjustment.leftSide ≫ (exchangeNaturalitySquare I h hh h' hh' v w hc).h =
      SSet.const (PointedMapping.familyVertex (swap Y ≫ doublePost v)) :=
  (SquareAdjustment.sides_of_boundary_restriction _
    (exchangeNaturalitySquare_boundary I h hh h' hh' v w hc)).1

/-- 右辺全体も、元の反転作用の同じ像で一定。 -/
lemma exchangeNaturalitySquare_finish :
    SquareAdjustment.rightSide ≫ (exchangeNaturalitySquare I h hh h' hh' v w hc).h =
      SSet.const (PointedMapping.familyVertex (reversal Y ≫ doublePost v)) :=
  (SquareAdjustment.sides_of_boundary_restriction _
    (exchangeNaturalitySquare_boundary I h hh h' hh' v w hc)).2

end SerrePositivity.KST.Spectra.LoopExchangeFamily
