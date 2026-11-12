module

public import SerrePositivity.KST.Spectra.SignedAdjointTrianglePair
public import SerrePositivity.KST.Spectra.SignedAdjointParametricConstantNaturality
public import SerrePositivity.KST.Spectra.PointedIntervalIhomSquare
public import SerrePositivity.KST.Spectra.SignedAdjointNaturalityCoordinates
public import SerrePositivity.KST.Spectra.TrianglePairComparison

/-!
概要：符号付き随伴比較の保存済み合成・逆三角形を、前後合成する同じ一組へ束ねる。
方針：元の実二単体と共有面の厳密等式を使い、同じ写像空間の射で同時に写す。
規約：元の充填・三辺を選び直さない。使われ方：三つの実自然性正方形から逆辺を比較する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.SignedAdjointPaths
variable {P A A' Y Z Z' W : PointedSimplicialSet.{u}} [KanComplex Z.right] [KanComplex W.right]
  (a : Z ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} W)
  (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right)
  (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
  (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z)

/-- 保存済みの同じ二単体への標的後合成。 -/
def parametricPostTrianglePair (v : P ⟶ PointedObject.basedHom Z Z') :
    SquareAdjustment.TrianglePair (PointedObject.basedHom A (PointedObject.basedHom P (target
      Z'))).right :=
  (trianglePair a ha f g).map (PointedObject.basedHomMap A (targetParametricPost v)).right

/-- 保存済みの同じ二単体への入力制限。 -/
def parametricPreTrianglePair (j : A' ⟶ PointedObject.basedHom P A) :
    SquareAdjustment.TrianglePair (PointedObject.basedHom A' (PointedObject.basedHom P (target
      Z))).right :=
  (trianglePair a ha f g).map
    (PointedMapping.ihomAction P A (target Z) ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j (PointedObject.basedHom P (target Z))).right

/-- 後合成した合成三角形の第一辺は、元の第一辺の同じ後合成。 -/
lemma parametricPostTrianglePair_two (v : P ⟶ PointedObject.basedHom Z Z') :
    stdSimplex.δ (2 : Fin 3) ≫ (parametricPostTrianglePair a ha f g v).forward =
      ((firstPath a ha f g).basedPost (targetParametricPost v)).path := by
  change stdSimplex.δ (2 : Fin 3) ≫ (_ ≫ _) = _
  dsimp only [trianglePair]
  rw [← Category.assoc, forwardComposite_two]
  rfl

/-- 後合成した合成三角形の第二辺も元の第二辺の同じ後合成。 -/
lemma parametricPostTrianglePair_zero (v : P ⟶ PointedObject.basedHom Z Z') :
    stdSimplex.δ (0 : Fin 3) ≫ (parametricPostTrianglePair a ha f g v).forward =
      ((secondPath f g).basedPost (targetParametricPost v)).path := by
  change stdSimplex.δ (0 : Fin 3) ≫ (_ ≫ _) = _
  dsimp only [trianglePair]
  rw [← Category.assoc, forwardComposite_zero]
  rfl

/-- 後合成した逆三角形の対角辺は、元の左端点の後合成で一定。 -/
lemma parametricPostTrianglePair_inverse_one (v : P ⟶ PointedObject.basedHom Z Z') :
    stdSimplex.δ (1 : Fin 3) ≫ (parametricPostTrianglePair a ha f g v).inverse =
      SSet.const (PointedMapping.familyVertex (left f g ≫ targetParametricPost v)) := by
  change stdSimplex.δ (1 : Fin 3) ≫ (_ ≫ _) = _
  dsimp only [trianglePair]
  rw [← Category.assoc, reverseComposite_one, SSet.const_comp, PointedMapping.familyVertex_post]

/-- 後合成した逆三角形の残る辺も、元の逆区間全体の同じ後合成。 -/
lemma parametricPostTrianglePair_inverse_zero (v : P ⟶ PointedObject.basedHom Z Z') :
    stdSimplex.δ (0 : Fin 3) ≫ (parametricPostTrianglePair a ha f g v).inverse =
      (((reverseComposite a ha f g).path).basedPost (targetParametricPost v)).path := by
  change stdSimplex.δ (0 : Fin 3) ≫ (_ ≫ _) = _
  dsimp only [trianglePair]
  rw [← Category.assoc, reverseComposite_zero]
  rfl

/-- 入力制限した合成三角形の第一辺は、元の第一辺の同じ入力制限。 -/
lemma parametricPreTrianglePair_two (j : A' ⟶ PointedObject.basedHom P A) :
    stdSimplex.δ (2 : Fin 3) ≫ (parametricPreTrianglePair a ha f g j).forward =
      (((firstPath a ha f g).basedIhomMap P).pre j).path := by
  change stdSimplex.δ (2 : Fin 3) ≫
      (((trianglePair a ha f g).forward ≫
        (PointedMapping.ihomAction P A (target Z)).right) ≫
          (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j (PointedObject.basedHom P (target Z))).right) =
    ((firstPath a ha f g).basedIhomMap P).path ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j (PointedObject.basedHom P (target Z))).right
  dsimp only [trianglePair]
  rw [← Category.assoc, ← Category.assoc, forwardComposite_two,
    PointedMapping.VerticalPath.basedIhomMap_path]

/-- 入力制限した合成三角形の第二辺も、元の第二辺の同じ入力制限。 -/
lemma parametricPreTrianglePair_zero (j : A' ⟶ PointedObject.basedHom P A) :
    stdSimplex.δ (0 : Fin 3) ≫ (parametricPreTrianglePair a ha f g j).forward =
      (((secondPath f g).basedIhomMap P).pre j).path := by
  change stdSimplex.δ (0 : Fin 3) ≫
      (((trianglePair a ha f g).forward ≫
        (PointedMapping.ihomAction P A (target Z)).right) ≫
          (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j (PointedObject.basedHom P (target Z))).right) =
    ((secondPath f g).basedIhomMap P).path ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j (PointedObject.basedHom P (target Z))).right
  dsimp only [trianglePair]
  rw [← Category.assoc, ← Category.assoc, forwardComposite_zero,
    PointedMapping.VerticalPath.basedIhomMap_path]

/-- 入力制限した逆三角形の対角辺は、元の左端点の同じ入力制限で一定。 -/
lemma parametricPreTrianglePair_inverse_one (j : A' ⟶ PointedObject.basedHom P A) :
    stdSimplex.δ (1 : Fin 3) ≫ (parametricPreTrianglePair a ha f g j).inverse =
      SSet.const (PointedMapping.familyVertex (j ≫ PointedObject.basedHomMap P (left f g))) := by
  change stdSimplex.δ (1 : Fin 3) ≫
      (((trianglePair a ha f g).inverse ≫
        (PointedMapping.ihomAction P A (target Z)).right) ≫
          (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j (PointedObject.basedHom P (target Z))).right) = _
  dsimp only [trianglePair]
  rw [← Category.assoc, ← Category.assoc, reverseComposite_one, SSet.const_comp,
    PointedMapping.familyVertex_ihomAction, SSet.const_comp, PointedMapping.familyVertex_pre]

/-- 入力制限した逆三角形の残る辺も、元の逆区間全体の同じ入力制限。 -/
lemma parametricPreTrianglePair_inverse_zero (j : A' ⟶ PointedObject.basedHom P A) :
    stdSimplex.δ (0 : Fin 3) ≫ (parametricPreTrianglePair a ha f g j).inverse =
      ((((reverseComposite a ha f g).path).basedIhomMap P).pre j).path := by
  change stdSimplex.δ (0 : Fin 3) ≫
      (((trianglePair a ha f g).inverse ≫
        (PointedMapping.ihomAction P A (target Z)).right) ≫
          (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j (PointedObject.basedHom P (target Z))).right) =
    (((reverseComposite a ha f g).path).basedIhomMap P).path ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j (PointedObject.basedHom P (target Z))).right
  dsimp only [trianglePair]
  rw [← Category.assoc, ← Category.assoc, reverseComposite_zero,
    PointedMapping.VerticalPath.basedIhomMap_path]

end SerrePositivity.KST.Spectra.SignedAdjointPaths
