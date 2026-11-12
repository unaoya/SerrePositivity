module

public import SerrePositivity.KST.Spectra.SignedAdjointConstantCoordinates

/-!
概要：同じ実入力比較を左端点の定数区間へ作用させ、第三の自然性正方形を構成する。
方針：元の入力正方形の始辺・終辺を前後合成した左端点へ照合し、共有境界を計算する。
規約：非定値な入力境界を保持。使われ方：元の合成・逆三角形の三辺の高次比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.SignedAdjointPaths
open LoopExchangePaths
variable {A A' Y Y' Z Z' W W' B : PointedSimplicialSet.{u}}
  (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
  (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z)
  (f' : A' ⟶ PointedObject.basedHom CirclePower.space.{u} Y')
  (g' : Y' ⟶ PointedObject.basedHom CirclePower.space.{u} Z')
  (j : A ⟶ A') (v : Z ⟶ Z') {p : doubleLoop Z' ⟶ B}
  (H : PointedMapping.VerticalPath p (input f g ≫ doublePost v) (j ≫ input f' g'))

/-- 元の左端点の像で一定な二辺の間の実自然性。二次元射は同じ実入力正方形。 -/
def constantPathNaturalitySquare :
    SSet.Homotopy (SSet.const (X := (Δ[1] : SSet.{u}))
      (PointedMapping.familyVertex (left f g ≫ targetPost v)))
      (SSet.const (PointedMapping.familyVertex (j ≫ left f' g'))) := by
  let e := (swap Z' ≫ reversal Z') ≫ projection Z'
  let R := PointedMapping.VerticalPath.refl (PointedObject.toPoint (target Z')) e
  let S := PointedMapping.VerticalPath.inputSquare H R
  exact {
    h := S.h
    h₀ := (S.h₀.trans (PointedMapping.VerticalPath.refl_pre_path e
      (input f g ≫ doublePost v))).trans
        (congrArg (fun m => SSet.const (PointedMapping.familyVertex m)) (left_post f g v).symm)
    h₁ := (S.h₁.trans (PointedMapping.VerticalPath.refl_pre_path e (j ≫ input f' g'))).trans
      (congrArg (fun m => SSet.const (PointedMapping.familyVertex m)) (left_pre f' g' j).symm)
    rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim }

/-- 第三正方形の左右境界は、同じ左端点への実入力作用として全区間で一致する。 -/
lemma constantPathNaturalitySquare_sides :
    SquareAdjustment.leftSide ≫ (constantPathNaturalitySquare f g f' g' j v H).h =
      SquareAdjustment.rightSide ≫ (constantPathNaturalitySquare f g f' g' j v H).h := by
  change SquareAdjustment.leftSide ≫ (PointedMapping.VerticalPath.inputSquare H
    (PointedMapping.VerticalPath.refl (PointedObject.toPoint (target Z'))
      ((swap Z' ≫ reversal Z') ≫ projection Z'))).h =
    SquareAdjustment.rightSide ≫ (PointedMapping.VerticalPath.inputSquare H
      (PointedMapping.VerticalPath.refl (PointedObject.toPoint (target Z'))
        ((swap Z' ≫ reversal Z') ≫ projection Z'))).h
  rw [PointedMapping.VerticalPath.inputSquare_left, PointedMapping.VerticalPath.inputSquare_right]

variable [KanComplex Z.right] [KanComplex Z'.right] [KanComplex W.right] [KanComplex W'.right]
  (a : Z ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} W)
  (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right)
  (a' : Z' ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} W')
  (ha' : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a'.right) (w : W ⟶ W')
  (hc : a ≫ PointedObject.basedHomMap PointedSimplicialSet.circle.{u} w = v ≫ a')

/-- 第一辺と第三の定数辺の実自然性正方形は、同じ非定値な始点境界全体を共有する。 -/
lemma firstConstantNaturalitySquare_shared :
    SquareAdjustment.leftSide ≫ (firstPathNaturalitySquare a ha a' ha' v w hc f g f' g' j H).h =
      SquareAdjustment.leftSide ≫ (constantPathNaturalitySquare f g f' g' j v H).h := by
  rw [firstPathNaturalitySquare_left]
  change SquareAdjustment.leftSide ≫ (PointedMapping.VerticalPath.inputSquare H
    ((cancellationFirst a' ha').basedPost (projection Z'))).h =
      SquareAdjustment.leftSide ≫ (PointedMapping.VerticalPath.inputSquare H
        (PointedMapping.VerticalPath.refl (PointedObject.toPoint (target Z'))
          ((swap Z' ≫ reversal Z') ≫ projection Z'))).h
  rw [PointedMapping.VerticalPath.inputSquare_left, PointedMapping.VerticalPath.inputSquare_left]

end SerrePositivity.KST.Spectra.SignedAdjointPaths
