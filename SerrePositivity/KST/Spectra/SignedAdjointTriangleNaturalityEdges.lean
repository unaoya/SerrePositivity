module

public import SerrePositivity.KST.Spectra.SignedAdjointTrianglePair
public import SerrePositivity.KST.Spectra.SignedAdjointConstantNaturality

/-!
概要：元の三自然性正方形を、保存済みの前後合成した三角形の同じ三面へ照合する。
方針：二次元射をそのまま保ち、元の実三角形の面の厳密等式で端点だけを照合する。
規約：二つの共有境界も全区間で保持。使われ方：選択済み逆区間の高次自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.SignedAdjointPaths
variable {A A' Y Y' Z Z' W W' B : PointedSimplicialSet.{u}}
  [KanComplex Z.right] [KanComplex Z'.right] [KanComplex W.right] [KanComplex W'.right]
  (a : Z ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} W)
  (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right)
  (a' : Z' ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} W')
  (ha' : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a'.right) (v : Z ⟶ Z') (w : W ⟶ W')
  (hc : a ≫ PointedObject.basedHomMap PointedSimplicialSet.circle.{u} w = v ≫ a')
  (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
  (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z)
  (f' : A' ⟶ PointedObject.basedHom CirclePower.space.{u} Y')
  (g' : Y' ⟶ PointedObject.basedHom CirclePower.space.{u} Z')
  (j : A ⟶ A') {p : LoopExchangePaths.doubleLoop Z' ⟶ B}
  (H : PointedMapping.VerticalPath p
    (input f g ≫ LoopExchangePaths.doublePost v) (j ≫ input f' g'))

/-- 第一辺の同じ二次元射を、保存済み二つの合成三角形の第一面へ照合する。 -/
def triangleFirstNaturalitySquare :
    SSet.Homotopy (stdSimplex.δ (2 : Fin 3) ≫ (postTrianglePair a ha f g v).forward)
      (stdSimplex.δ (2 : Fin 3) ≫ (preTrianglePair a' ha' f' g' j).forward) := by
  let S := firstPathNaturalitySquare a ha a' ha' v w hc f g f' g' j H
  exact {
    h := S.h
    h₀ := S.h₀.trans (postTrianglePair_two a ha f g v).symm
    h₁ := S.h₁.trans (preTrianglePair_two a' ha' f' g' j).symm
    rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim }

/-- 第二辺の同じ二次元射を、保存済み二つの合成三角形の第二面へ照合する。 -/
def triangleSecondNaturalitySquare :
    SSet.Homotopy (stdSimplex.δ (0 : Fin 3) ≫ (postTrianglePair a ha f g v).forward)
      (stdSimplex.δ (0 : Fin 3) ≫ (preTrianglePair a' ha' f' g' j).forward) := by
  let S := secondPathNaturalitySquare f g f' g' j v H
  exact {
    h := S.h
    h₀ := S.h₀.trans (postTrianglePair_zero a ha f g v).symm
    h₁ := S.h₁.trans (preTrianglePair_zero a' ha' f' g' j).symm
    rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim }

/-- 第三の同じ二次元射を、保存済み二つの逆三角形の定数面へ照合する。 -/
def triangleConstantNaturalitySquare :
    SSet.Homotopy (stdSimplex.δ (1 : Fin 3) ≫ (postTrianglePair a ha f g v).inverse)
      (stdSimplex.δ (1 : Fin 3) ≫ (preTrianglePair a' ha' f' g' j).inverse) := by
  let S := constantPathNaturalitySquare f g f' g' j v H
  exact {
    h := S.h
    h₀ := S.h₀.trans (postTrianglePair_inverse_one a ha f g v).symm
    h₁ := S.h₁.trans (preTrianglePair_inverse_one a' ha' f' g' j).symm
    rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim }

/-- 第一・第二面の正方形は元の同じ非定値な中間境界を共有する。 -/
lemma triangleFirstSecondNaturalitySquare_shared :
    SquareAdjustment.rightSide ≫
        (triangleFirstNaturalitySquare a ha a' ha' v w hc f g f' g' j H).h =
      SquareAdjustment.leftSide ≫
        (triangleSecondNaturalitySquare a ha a' ha' v f g f' g' j H).h :=
  firstSecondNaturalitySquare_shared a ha a' ha' v w hc f g f' g' j H

/-- 第一・第三面の正方形も元の同じ非定値な始点境界を共有する。 -/
lemma triangleFirstConstantNaturalitySquare_shared :
    SquareAdjustment.leftSide ≫
        (triangleFirstNaturalitySquare a ha a' ha' v w hc f g f' g' j H).h =
      SquareAdjustment.leftSide ≫
        (triangleConstantNaturalitySquare a ha a' ha' v f g f' g' j H).h :=
  firstConstantNaturalitySquare_shared f g f' g' j v H a ha a' ha' w hc

end SerrePositivity.KST.Spectra.SignedAdjointPaths
