module

public import SerrePositivity.KST.Spectra.SignedAdjointSecondNaturality

/-!
概要：二つの辺へ同じ実入力比較を作用させた正方形の中間境界を全区間で照合する。
方針：入力正方形の左右境界を、元の共通端点への同じ入力作用として計算する。
規約：非定値な入力区間を保持。使われ方：実合成三角形を指定した二辺の貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra
namespace PointedMapping.VerticalPath

/-- 同じ入力比較を共通端点を持つ二辺へ作用させると、中間境界全体が一致する。 -/
lemma inputSquare_shared {A D E B : PointedSimplicialSet.{u}} {p : D ⟶ B}
    {a b : A ⟶ D} (H : VerticalPath p a b) {f g k : D ⟶ E}
    (P : VerticalPath (PointedObject.toPoint E) f g)
    (Q : VerticalPath (PointedObject.toPoint E) g k) :
    SquareAdjustment.rightSide ≫ (inputSquare H P).h =
      SquareAdjustment.leftSide ≫ (inputSquare H Q).h := by
  rw [inputSquare_right, inputSquare_left]

end PointedMapping.VerticalPath
namespace SignedAdjointPaths
open LoopExchangePaths
variable {A A' Y Y' Z Z' W' B : PointedSimplicialSet.{u}}
  [KanComplex Z.right] [KanComplex Z'.right] [KanComplex W'.right]
  (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
  (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z)
  (f' : A' ⟶ PointedObject.basedHom CirclePower.space.{u} Y')
  (g' : Y' ⟶ PointedObject.basedHom CirclePower.space.{u} Z')
  (j : A ⟶ A') (v : Z ⟶ Z') {p : doubleLoop Z' ⟶ B}
  (H : PointedMapping.VerticalPath p (input f g ≫ doublePost v) (j ≫ input f' g'))
  (a' : Z' ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} W')
  (ha' : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a'.right)

/-- 交換符号辺の入力正方形と元の第二辺の自然性正方形の中間境界は同じ実区間。 -/
lemma firstSecondInputSquare_shared :
    SquareAdjustment.rightSide ≫
        (PointedMapping.VerticalPath.inputSquare H
          ((cancellationFirst a' ha').basedPost (projection Z'))).h =
      SquareAdjustment.leftSide ≫ (secondPathNaturalitySquare f g f' g' j v H).h :=
  PointedMapping.VerticalPath.inputSquare_shared H
    ((cancellationFirst a' ha').basedPost (projection Z'))
    ((reversalTwice Z').basedPost (projection Z'))

end SignedAdjointPaths
end SerrePositivity.KST.Spectra
