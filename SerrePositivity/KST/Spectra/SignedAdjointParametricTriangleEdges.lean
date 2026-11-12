module

public import SerrePositivity.KST.Spectra.SignedAdjointParametricTrianglePair
public import SerrePositivity.KST.Spectra.SignedAdjointParametricConstantNaturality

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
variable {P A A' Y Y' Z Z' W W' B : PointedSimplicialSet.{u}}
  [KanComplex Z.right] [KanComplex Z'.right] [KanComplex W.right] [KanComplex W'.right]
  (a : Z ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} W)
  (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right)
  (a' : Z' ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} W')
  (ha' : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a'.right) (v : P ⟶ PointedObject.basedHom Z Z')
  (w : P ⟶ PointedObject.basedHom W W')
  (hc : a ≫ PointedMapping.parametricPost PointedSimplicialSet.circle.{u} w =
    PointedMapping.transpose v ≫ PointedObject.basedHomMap P a')
  (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
  (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z)
  (f' : A' ⟶ PointedObject.basedHom CirclePower.space.{u} Y')
  (g' : Y' ⟶ PointedObject.basedHom CirclePower.space.{u} Z')
  (j : A ⟶ PointedObject.basedHom P A')
  {p : PointedObject.basedHom P (LoopExchangePaths.doubleLoop Z') ⟶ B}
  (H : PointedMapping.VerticalPath p
    (input f g ≫ LoopExchangePaths.doubleParametricPost v) (j ≫ PointedObject.basedHomMap P
      (input f' g')))

/-- 第一辺の同じ二次元射を、保存済み二つの合成三角形の第一面へ照合する。 -/
def triangleFirstParametricNaturalitySquare :
    SSet.Homotopy (stdSimplex.δ (2 : Fin 3) ≫ (parametricPostTrianglePair a ha f g v).forward)
      (stdSimplex.δ (2 : Fin 3) ≫ (parametricPreTrianglePair a' ha' f' g' j).forward) := by
  let S := firstPathParametricNaturalitySquare a ha a' ha' v w hc f g f' g' j H
  exact {
    h := S.h
    h₀ := S.h₀.trans (parametricPostTrianglePair_two a ha f g v).symm
    h₁ := S.h₁.trans (parametricPreTrianglePair_two a' ha' f' g' j).symm
    rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim }

/-- 第二辺の同じ二次元射を、保存済み二つの合成三角形の第二面へ照合する。 -/
def triangleSecondParametricNaturalitySquare :
    SSet.Homotopy (stdSimplex.δ (0 : Fin 3) ≫ (parametricPostTrianglePair a ha f g v).forward)
      (stdSimplex.δ (0 : Fin 3) ≫ (parametricPreTrianglePair a' ha' f' g' j).forward) := by
  let S := secondPathParametricNaturalitySquare f g f' g' j v H
  exact {
    h := S.h
    h₀ := S.h₀.trans (parametricPostTrianglePair_zero a ha f g v).symm
    h₁ := S.h₁.trans (parametricPreTrianglePair_zero a' ha' f' g' j).symm
    rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim }

/-- 第三の同じ二次元射を、保存済み二つの逆三角形の定数面へ照合する。 -/
def triangleConstantParametricNaturalitySquare :
    SSet.Homotopy (stdSimplex.δ (1 : Fin 3) ≫ (parametricPostTrianglePair a ha f g v).inverse)
      (stdSimplex.δ (1 : Fin 3) ≫ (parametricPreTrianglePair a' ha' f' g' j).inverse) := by
  let S := constantPathParametricNaturalitySquare f g f' g' j v H
  exact {
    h := S.h
    h₀ := S.h₀.trans (parametricPostTrianglePair_inverse_one a ha f g v).symm
    h₁ := S.h₁.trans (parametricPreTrianglePair_inverse_one a' ha' f' g' j).symm
    rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim }

/-- 第一・第二面の正方形は元の同じ非定値な中間境界を共有する。 -/
lemma triangleFirstSecondParametricNaturalitySquare_shared :
    SquareAdjustment.rightSide ≫
        (triangleFirstParametricNaturalitySquare a ha a' ha' v w hc f g f' g' j H).h =
      SquareAdjustment.leftSide ≫
        (triangleSecondParametricNaturalitySquare a ha a' ha' v f g f' g' j H).h := by
  change SquareAdjustment.rightSide ≫
      (firstPathParametricNaturalitySquare a ha a' ha' v w hc f g f' g' j H).h =
    SquareAdjustment.leftSide ≫ (secondPathParametricNaturalitySquare f g f' g' j v H).h
  exact firstSecondParametricNaturalitySquare_shared f g f' g' j v H a ha a' ha' w hc

/-- 第一・第三面の正方形も元の同じ非定値な始点境界を共有する。 -/
lemma triangleFirstConstantParametricNaturalitySquare_shared :
    SquareAdjustment.leftSide ≫
        (triangleFirstParametricNaturalitySquare a ha a' ha' v w hc f g f' g' j H).h =
      SquareAdjustment.leftSide ≫
        (triangleConstantParametricNaturalitySquare a ha a' ha' v f g f' g' j H).h := by
  change SquareAdjustment.leftSide ≫
      (firstPathParametricNaturalitySquare a ha a' ha' v w hc f g f' g' j H).h =
    SquareAdjustment.leftSide ≫ (constantPathParametricNaturalitySquare f g f' g' j v H).h
  exact firstConstantParametricNaturalitySquare_shared f g f' g' j v H a ha a' ha' w hc

end SerrePositivity.KST.Spectra.SignedAdjointPaths
