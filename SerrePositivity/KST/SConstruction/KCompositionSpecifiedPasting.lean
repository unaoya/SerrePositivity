module
public import SerrePositivity.KST.SConstruction.KCompositionPastingTriangles

/-! # 元の三正方形と全指定三角形の同時保持
概要：元の合成 prism と元の三つの外側三角形を、一つの実写像へ貼る。
方針：六脚の厳密な照合を、有限セル複体の pushout に渡す。
規約：三正方形・三角形全体と指定適合区間を選び直さない。
使われ方：二本の入力射の適合区間と合成射の適合区間の実比較の境界。
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
local instance kCompositionSpecifiedPastingPointedCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
variable {I : Type u} [SmallCategory I] (r : ℕ) (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の三正方形と指定した全三角形を同時に保つ実写像。 -/
def kKanOriginalCompositionSpecifiedPasting : threeSquareTrianglePasting ⟶
    (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj x)).level r).space)
      ((kKanSequence (F.obj z)).level (r + 1)).space).right :=
  threeSquareTrianglePastingMap
    (kKanOriginalCompositionMappingSquare r F f g 0)
    (kKanOriginalCompositionMappingSquare r F f g 1)
    (kKanOriginalCompositionMappingSquare r F f g 2)
    (kKanOriginalCompositionMappingSquare_shared_first r F f g)
    (kKanOriginalCompositionMappingSquare_shared_second r F f g)
    (kKanOriginalCompositionPastingTriangle r F f g)
    (kKanOriginalCompositionPastingTriangle_upper r F f g)
    (kKanOriginalCompositionPastingTriangle_lower r F f g)

/-- 元の三正方形の全体を、厳密に回収する。 -/
lemma kKanOriginalCompositionSpecifiedPasting_square (q : Fin 3) :
    threeSquareTriangleSquare q ≫ kKanOriginalCompositionSpecifiedPasting r F f g =
      kKanOriginalCompositionMappingSquare r F f g q := by
  have h := threeSquareTrianglePastingMap_square
    (kKanOriginalCompositionMappingSquare r F f g 0)
    (kKanOriginalCompositionMappingSquare r F f g 1)
    (kKanOriginalCompositionMappingSquare r F f g 2)
    (kKanOriginalCompositionMappingSquare_shared_first r F f g)
    (kKanOriginalCompositionMappingSquare_shared_second r F f g)
    (kKanOriginalCompositionPastingTriangle r F f g)
    (kKanOriginalCompositionPastingTriangle_upper r F f g)
    (kKanOriginalCompositionPastingTriangle_lower r F f g) q
  exact h.trans (by fin_cases q <;> rfl)

/-- 指定した各外側三角形の全体も厳密に回収する。 -/
lemma kKanOriginalCompositionSpecifiedPasting_triangle (e : Fin 3) :
    threeSquareTriangleCell e ≫ kKanOriginalCompositionSpecifiedPasting r F f g =
      kKanOriginalCompositionPastingTriangle r F f g e :=
  threeSquareTrianglePastingMap_triangle _ _ _ _ _ _ _ _ e

/-- 合成射の元の適合区間を、付けた三角形の同じ境界として回収する。 -/
lemma kKanOriginalCompositionSpecifiedPasting_composite_compatibility :
    stdSimplex.δ 0 ≫ threeSquareTriangleCell 0 ≫
      kKanOriginalCompositionSpecifiedPasting r F f g =
      SSet.yonedaEquiv.symm (kKanSuspensionCompatibilityEdge r F (f ≫ g)).edge := by
  rw [kKanOriginalCompositionSpecifiedPasting_triangle]
  exact kKanOriginalOuterTriangle_compatibility r F (f ≫ g)

/-- 前の射の元の適合区間の実後合成を、同じ境界として回収する。 -/
lemma kKanOriginalCompositionSpecifiedPasting_first_compatibility :
    stdSimplex.δ 0 ≫ threeSquareTriangleCell 1 ≫
      kKanOriginalCompositionSpecifiedPasting r F f g =
      SSet.yonedaEquiv.symm (kKanSuspensionCompatibilityEdge r F f).edge ≫
        (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj x)).level r).space)
          (kKanSequenceLevelMap (F.map g) (r + 1))).right := by
  rw [kKanOriginalCompositionSpecifiedPasting_triangle]
  change stdSimplex.δ 0 ≫ (kKanOriginalOuterTriangle r F f ≫ _) = _
  rw [← Category.assoc, kKanOriginalOuterTriangle_compatibility]

/-- 後の射の元の適合区間の実前合成を、同じ境界として回収する。 -/
lemma kKanOriginalCompositionSpecifiedPasting_second_compatibility :
    stdSimplex.δ 0 ≫ threeSquareTriangleCell 2 ≫
      kKanOriginalCompositionSpecifiedPasting r F f g =
      SSet.yonedaEquiv.symm (kKanSuspensionCompatibilityEdge r F g).edge ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedSimplicialSet.circle.{u} ◁ kKanSequenceLevelMap (F.map f) r)
          ((kKanSequence (F.obj z)).level (r + 1)).space := by
  rw [kKanOriginalCompositionSpecifiedPasting_triangle]
  change stdSimplex.δ 0 ≫ (kKanOriginalOuterTriangle r F g ≫ _) = _
  rw [← Category.assoc, kKanOriginalOuterTriangle_compatibility]

/-- 元の最初の定数外側辺も全時刻で保持される。 -/
lemma kKanOriginalCompositionSpecifiedPasting_exterior_upper_constant :
    ∃ v, pastingSquareVertical 1 ≫ threeSquareTriangleSquare 0 ≫
      kKanOriginalCompositionSpecifiedPasting r F f g = SSet.const v := by
  rw [kKanOriginalCompositionSpecifiedPasting_square]
  exact kKanOriginalCompositionMappingSquare_exterior_upper_constant r F f g

/-- 元の最後の定数外側辺も全時刻で保持される。 -/
lemma kKanOriginalCompositionSpecifiedPasting_exterior_lower_constant :
    ∃ v, pastingSquareHorizontal 1 ≫ threeSquareTriangleSquare 2 ≫
      kKanOriginalCompositionSpecifiedPasting r F f g = SSet.const v := by
  rw [kKanOriginalCompositionSpecifiedPasting_square]
  exact kKanOriginalCompositionMappingSquare_exterior_lower_constant r F f g

end SerrePositivity.KST.SConstruction
