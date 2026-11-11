module

public import SerrePositivity.KST.Spectra.UniversalLoopExchangePaths
public import SerrePositivity.KST.Spectra.ParametricExchangeNaturality

/-!
概要：通常円随伴の全族可換式から、既存 exchange の全パラメータ境界固定自然性。
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

variable {P Y Y' Z Z' : PointedSimplicialSet.{u}} [KanComplex Y.right] [KanComplex Y'.right]
  [KanComplex Z.right] [KanComplex Z'.right]
  (a : Y ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} Z)
  (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right)
  (a' : Y' ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} Z')
  (ha' : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a'.right) (v : P ⟶ PointedObject.basedHom Y Y')
  (w : P ⟶ PointedObject.basedHom Z Z')
  (hc : a ≫ PointedMapping.parametricPost PointedSimplicialSet.circle.{u} w =
    PointedMapping.transpose v ≫ PointedObject.basedHomMap P a')

/-- 元の随伴を使った同じ exchange の二辺と、像の正方形への相対反映トレース。 -/
def ordinaryParametricExchangeNaturalityReflection :=
  ParametricLoopExchangeFamily.exchangeNaturalityReflection
    OrdinaryLoopSource.parametricFamily.{u}
    a ha a' ha' v w hc

/-- 既存の exchange 自身の前後合成を結ぶ、元の通常円随伴からの実自然性正方形。 -/
def ordinaryParametricExchangeNaturalitySquare :
    SSet.Homotopy (((exchange a ha).basedPost (doubleParametricPost v)).path)
      ((((exchange a' ha').basedIhomMap P).pre (doubleParametricPost v)).path) :=
  ParametricLoopExchangeFamily.exchangeNaturalitySquare
    OrdinaryLoopSource.parametricFamily.{u} a ha a' ha' v w hc

/-- 既存 exchange の自然性正方形の左右全境界は、元の作用の同じ像で一定。 -/
lemma ordinaryParametricExchangeNaturalitySquare_boundary :
    (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫
        (ordinaryParametricExchangeNaturalitySquare a ha a' ha' v w hc).h =
      intervalBoundaryFamily
        (SSet.const (PointedMapping.familyVertex (swap Y ≫ doubleParametricPost v)))
        (SSet.const (PointedMapping.familyVertex (reversal Y ≫ doubleParametricPost v))) :=
  ParametricLoopExchangeFamily.exchangeNaturalitySquare_boundary
    OrdinaryLoopSource.parametricFamily.{u}
    a ha a' ha' v w hc

/-- 左辺全体は、元の交換作用の同じ後合成像で一定。 -/
lemma ordinaryParametricExchangeNaturalitySquare_start :
    SquareAdjustment.leftSide ≫ (ordinaryParametricExchangeNaturalitySquare a ha a' ha' v w hc).h =
      SSet.const (PointedMapping.familyVertex (swap Y ≫ doubleParametricPost v)) :=
  ParametricLoopExchangeFamily.exchangeNaturalitySquare_start
    OrdinaryLoopSource.parametricFamily.{u}
    a ha a' ha' v w hc

/-- 右辺全体も、元の反転作用の同じ後合成像で一定。 -/
lemma ordinaryParametricExchangeNaturalitySquare_finish :
    SquareAdjustment.rightSide ≫ (ordinaryParametricExchangeNaturalitySquare a ha a' ha' v w hc).h =
      SSet.const (PointedMapping.familyVertex (reversal Y ≫ doubleParametricPost v)) :=
  ParametricLoopExchangeFamily.exchangeNaturalitySquare_finish
    OrdinaryLoopSource.parametricFamily.{u}
    a ha a' ha' v w hc

/-- 自然性の二次元射全体は、同じ反映トレースから回収した正方形そのもの。 -/
lemma ordinaryParametricExchangeNaturalitySquare_h :
    (ordinaryParametricExchangeNaturalitySquare a ha a' ha' v w hc).h =
      (ordinaryParametricExchangeNaturalityReflection a ha a' ha' v w hc).homotopy.h := rfl

end SerrePositivity.KST.Spectra.LoopExchangePaths
