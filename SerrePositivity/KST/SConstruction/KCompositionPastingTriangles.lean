module
public import SerrePositivity.KST.SConstruction.KCompositionPastingSquares
public import SerrePositivity.KST.SConstruction.ThreeSquareTrianglePasting
public import SerrePositivity.KST.SConstruction.KPrismSpecifiedSpanFamilies

/-! # 元の K 合成 prism に指定する三角形
概要：合成射・前の射・後の射の元の外側三角形を同じ Hom に集める。
方針：前の三角形には次段の後合成、後の三角形には suspension の前合成を使う。
規約：指定三角形の全二単体と元の適合辺を保存する。
使われ方：三正方形と指定三角形の同時貼り合わせ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Spectra SerrePositivity.InfinityCategories
open scoped Simplicial
local instance kCompositionPastingTrianglesPointedCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
variable {I : Type u} [SmallCategory I] (r : ℕ) (F : I ⥤ StableModel.{u})

/-- 元の指定外側三角形の、全二単体の実写像。 -/
def kKanOriginalOuterTriangle {x y : I} (f : x ⟶ y) : (Δ[2] : SSet.{u}) ⟶
    kKanOriginalSuspensionMappingTarget r F x y :=
  SSet.yonedaEquiv.symm (kKanOriginalPrismSpecifiedOuterTriangleData r F f).val

/-- 指定三角形の 01 辺は、同じ元の上側復号辺。 -/
lemma kKanOriginalOuterTriangle_upper {x y : I} (f : x ⟶ y) :
    stdSimplex.δ 2 ≫ kKanOriginalOuterTriangle r F f =
      SSet.yonedaEquiv.symm
        (coherentSquareMappingLeftTop (kKanSuspensionMappingTriangles r F f)).edge := by
  rw [kKanOriginalOuterTriangle, stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg SSet.yonedaEquiv.symm
    ((kKanOriginalPrismSpecifiedOuterTriangleData r F f).property.1.trans
      (kKanOriginalPrismUpperCompositeContraction_boundary_leg r F f))

/-- 指定三角形の 02 辺は、同じ元の下側復号辺。 -/
lemma kKanOriginalOuterTriangle_lower {x y : I} (f : x ⟶ y) :
    stdSimplex.δ 1 ≫ kKanOriginalOuterTriangle r F f =
      SSet.yonedaEquiv.symm
        (coherentSquareMappingBottomRight (kKanSuspensionMappingTriangles r F f)).edge := by
  rw [kKanOriginalOuterTriangle, stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg SSet.yonedaEquiv.symm
    ((kKanOriginalPrismSpecifiedOuterTriangleData r F f).property.2.2.trans
      (kKanOriginalPrismLowerCompositeContraction_boundary_leg r F f))

/-- 残る 12 辺は、選び直していない元の適合区間。 -/
lemma kKanOriginalOuterTriangle_compatibility {x y : I} (f : x ⟶ y) :
    stdSimplex.δ 0 ≫ kKanOriginalOuterTriangle r F f =
      SSet.yonedaEquiv.symm (kKanSuspensionCompatibilityEdge r F f).edge := by
  rw [kKanOriginalOuterTriangle, stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg SSet.yonedaEquiv.symm
    (kKanOriginalPrismSpecifiedOuterTriangleData r F f).property.2.1

variable {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の三つの指定三角形を、同じ suspension Hom に集める。 -/
def kKanOriginalCompositionPastingTriangle (e : Fin 3) : (Δ[2] : SSet.{u}) ⟶
    (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj x)).level r).space)
      ((kKanSequence (F.obj z)).level (r + 1)).space).right :=
  ![kKanOriginalOuterTriangle r F (f ≫ g),
    kKanOriginalOuterTriangle r F f ≫
      (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj x)).level r).space)
        (kKanSequenceLevelMap (F.map g) (r + 1))).right,
    kKanOriginalOuterTriangle r F g ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedSimplicialSet.circle.{u} ◁ kKanSequenceLevelMap (F.map f) r)
        ((kKanSequence (F.obj z)).level (r + 1)).space] e

/-- 三つの指定三角形の 01 辺は、貼り合わせた正方形の同じ外側脚。 -/
lemma kKanOriginalCompositionPastingTriangle_upper (e : Fin 3) :
    stdSimplex.δ 2 ≫ kKanOriginalCompositionPastingTriangle r F f g e =
      threeSquareSpanLeft e ≫ kKanOriginalCompositionPastingSquares r F f g := by
  fin_cases e
  · change stdSimplex.δ 2 ≫ (kKanOriginalOuterTriangle r F (f ≫ g)) =
        (pastingSquareHorizontal 0 ≫ threeSquareInclusion 0) ≫
          kKanOriginalCompositionPastingSquares r F f g
    rw [Category.assoc, kKanOriginalCompositionPastingSquares_square]
    rw [kKanOriginalOuterTriangle_upper]
    exact (kKanOriginalCompositionMappingSquare_composite_upper r F f g).symm
  · change stdSimplex.δ 2 ≫ (kKanOriginalOuterTriangle r F f ≫
        (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj x)).level r).space)
          (kKanSequenceLevelMap (F.map g) (r + 1))).right) =
        (pastingSquareHorizontal 1 ≫ threeSquareInclusion 0) ≫
          kKanOriginalCompositionPastingSquares r F f g
    rw [Category.assoc, kKanOriginalCompositionPastingSquares_square]
    rw [← Category.assoc, kKanOriginalOuterTriangle_upper]
    exact (kKanOriginalCompositionMappingSquare_first_upper_post r F f g).symm
  · change stdSimplex.δ 2 ≫ (kKanOriginalOuterTriangle r F g ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre
          (PointedSimplicialSet.circle.{u} ◁ kKanSequenceLevelMap (F.map f) r)
          ((kKanSequence (F.obj z)).level (r + 1)).space) =
        (pastingSquareVertical 1 ≫ threeSquareInclusion 1) ≫
          kKanOriginalCompositionPastingSquares r F f g
    rw [Category.assoc, kKanOriginalCompositionPastingSquares_square]
    rw [← Category.assoc, kKanOriginalOuterTriangle_upper]
    exact (kKanOriginalCompositionMappingSquare_second_upper_pre r F f g).symm

/-- 三つの指定三角形の 02 辺は、貼り合わせた正方形の同じ外側脚。 -/
lemma kKanOriginalCompositionPastingTriangle_lower (e : Fin 3) :
    stdSimplex.δ 1 ≫ kKanOriginalCompositionPastingTriangle r F f g e =
      threeSquareSpanRight e ≫ kKanOriginalCompositionPastingSquares r F f g := by
  fin_cases e
  · change stdSimplex.δ 1 ≫ (kKanOriginalOuterTriangle r F (f ≫ g)) =
        (pastingSquareVertical 0 ≫ threeSquareInclusion 2) ≫
          kKanOriginalCompositionPastingSquares r F f g
    rw [Category.assoc, kKanOriginalCompositionPastingSquares_square]
    rw [kKanOriginalOuterTriangle_lower]
    exact (kKanOriginalCompositionMappingSquare_composite_lower r F f g).symm
  · change stdSimplex.δ 1 ≫ (kKanOriginalOuterTriangle r F f ≫
        (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj x)).level r).space)
          (kKanSequenceLevelMap (F.map g) (r + 1))).right) =
        (pastingSquareHorizontal 1 ≫ threeSquareInclusion 1) ≫
          kKanOriginalCompositionPastingSquares r F f g
    rw [Category.assoc, kKanOriginalCompositionPastingSquares_square]
    rw [← Category.assoc, kKanOriginalOuterTriangle_lower]
    exact (kKanOriginalCompositionMappingSquare_first_lower_post r F f g).symm
  · change stdSimplex.δ 1 ≫ (kKanOriginalOuterTriangle r F g ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre
          (PointedSimplicialSet.circle.{u} ◁ kKanSequenceLevelMap (F.map f) r)
          ((kKanSequence (F.obj z)).level (r + 1)).space) =
        (pastingSquareVertical 1 ≫ threeSquareInclusion 2) ≫
          kKanOriginalCompositionPastingSquares r F f g
    rw [Category.assoc, kKanOriginalCompositionPastingSquares_square]
    rw [← Category.assoc, kKanOriginalOuterTriangle_lower]
    exact (kKanOriginalCompositionMappingSquare_second_lower_pre r F f g).symm

end SerrePositivity.KST.SConstruction
