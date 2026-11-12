module

public import SerrePositivity.KST.Spectra.UniversalLoopExchangePaths
public import SerrePositivity.KST.Spectra.LoopExchangeFamilyNaturality

/-!
概要：元の通常円随伴の厳密可換式から、既存 exchange 自身の境界固定自然性を構成する。
方針：実証済みの通常円交換族の同じ移送・貼り合わせ・反映を具体化する。
規約：元の同じ区間と全トレースを保持する。使われ方：単位構造区間の高次自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.LoopExchangePaths

variable {Y Y' Z Z' : PointedSimplicialSet.{u}} [KanComplex Y.right] [KanComplex Y'.right]
  [KanComplex Z.right] [KanComplex Z'.right]
  (a : Y ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} Z)
  (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right)
  (a' : Y' ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} Z')
  (ha' : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a'.right) (v : Y ⟶ Y') (w : Z ⟶ Z')
  (hc : a ≫ PointedObject.basedHomMap PointedSimplicialSet.circle.{u} w = v ≫ a')

/-- 元の随伴を使った同じ exchange の二辺と、像の正方形への相対反映トレース。 -/
def ordinaryExchangeNaturalityReflection :=
  LoopExchangeFamily.exchangeNaturalityReflection OrdinaryLoopSource.family.{u}
    a ha a' ha' v w hc

/-- 既存の exchange 自身の前後合成を結ぶ、元の通常円随伴からの実自然性正方形。 -/
def ordinaryExchangeNaturalitySquare :
    SSet.Homotopy (((exchange a ha).basedPost (doublePost v)).path)
      (((exchange a' ha').pre (doublePost v)).path) :=
  LoopExchangeFamily.exchangeNaturalitySquare OrdinaryLoopSource.family.{u} a ha a' ha' v w hc

/-- 既存 exchange の自然性正方形の左右全境界は、元の作用の同じ像で一定。 -/
lemma ordinaryExchangeNaturalitySquare_boundary :
    (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫
        (ordinaryExchangeNaturalitySquare a ha a' ha' v w hc).h =
      intervalBoundaryFamily (SSet.const (PointedMapping.familyVertex (swap Y ≫ doublePost v)))
        (SSet.const (PointedMapping.familyVertex (reversal Y ≫ doublePost v))) :=
  LoopExchangeFamily.exchangeNaturalitySquare_boundary OrdinaryLoopSource.family.{u}
    a ha a' ha' v w hc

/-- 左辺全体は、元の交換作用の同じ後合成像で一定。 -/
lemma ordinaryExchangeNaturalitySquare_start :
    SquareAdjustment.leftSide ≫ (ordinaryExchangeNaturalitySquare a ha a' ha' v w hc).h =
      SSet.const (PointedMapping.familyVertex (swap Y ≫ doublePost v)) :=
  LoopExchangeFamily.exchangeNaturalitySquare_start OrdinaryLoopSource.family.{u}
    a ha a' ha' v w hc

/-- 右辺全体も、元の反転作用の同じ後合成像で一定。 -/
lemma ordinaryExchangeNaturalitySquare_finish :
    SquareAdjustment.rightSide ≫ (ordinaryExchangeNaturalitySquare a ha a' ha' v w hc).h =
      SSet.const (PointedMapping.familyVertex (reversal Y ≫ doublePost v)) :=
  LoopExchangeFamily.exchangeNaturalitySquare_finish OrdinaryLoopSource.family.{u}
    a ha a' ha' v w hc

/-- 自然性の二次元射全体は、同じ反映トレースから回収した正方形そのもの。 -/
lemma ordinaryExchangeNaturalitySquare_h :
    (ordinaryExchangeNaturalitySquare a ha a' ha' v w hc).h =
      (ordinaryExchangeNaturalityReflection a ha a' ha' v w hc).homotopy.h := rfl

end SerrePositivity.KST.Spectra.LoopExchangePaths
