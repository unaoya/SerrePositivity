module
public import SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityOfMaps
public import SerrePositivity.KST.SConstruction.KCompositionSpecifiedPasting

/-! # 元の K 合成 prism からの六セル比較データ
概要：元の三正方形・指定三角形・定数外側辺を、そのまま比較入力へ渡す。
方針：既存の六脚の等号と実定数辺から、共有頂点と全境界を内部構成する。
規約：零段を含む全段で、全区間と全指定二単体を保持する。
使われ方：元の三適合区間そのものを三面に持つ実比較三角形。
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
local instance kCompositionCompatibilityDataPointedCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
variable {I : Type u} [SmallCategory I] (r : ℕ) (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の三正方形と三指定三角形の全境界を保つ、無条件の実比較入力。 -/
def kKanOriginalCompositionCompatibilityData : ThreeSquareCompatibilityData
    (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj x)).level r).space)
      ((kKanSequence (F.obj z)).level (r + 1)).space).right :=
  threeSquareCompatibilityDataOfMaps
    (kKanOriginalCompositionMappingSquare r F f g 0)
    (kKanOriginalCompositionMappingSquare r F f g 1)
    (kKanOriginalCompositionMappingSquare r F f g 2)
    (kKanOriginalCompositionMappingSquare_shared_first r F f g)
    (kKanOriginalCompositionMappingSquare_shared_second r F f g)
    (kKanOriginalCompositionMappingSquare_exterior_upper_constant r F f g).choose
    (kKanOriginalCompositionMappingSquare_exterior_lower_constant r F f g).choose
    (kKanOriginalCompositionMappingSquare_exterior_upper_constant r F f g).choose_spec
    (kKanOriginalCompositionMappingSquare_exterior_lower_constant r F f g).choose_spec
    (kKanOriginalCompositionPastingTriangle r F f g 0)
    (kKanOriginalCompositionPastingTriangle r F f g 1)
    (kKanOriginalCompositionPastingTriangle r F f g 2)
    (by
      have h := kKanOriginalCompositionPastingTriangle_upper r F f g 0
      change stdSimplex.δ 2 ≫ kKanOriginalCompositionPastingTriangle r F f g 0 =
        (pastingSquareHorizontal 0 ≫ threeSquareInclusion 0) ≫
          kKanOriginalCompositionPastingSquares r F f g at h
      simpa only [Category.assoc, kKanOriginalCompositionPastingSquares_square] using h)
    (by
      have h := kKanOriginalCompositionPastingTriangle_lower r F f g 0
      change stdSimplex.δ 1 ≫ kKanOriginalCompositionPastingTriangle r F f g 0 =
        (pastingSquareVertical 0 ≫ threeSquareInclusion 2) ≫
          kKanOriginalCompositionPastingSquares r F f g at h
      simpa only [Category.assoc, kKanOriginalCompositionPastingSquares_square] using h)
    (by
      have h := kKanOriginalCompositionPastingTriangle_upper r F f g 1
      change stdSimplex.δ 2 ≫ kKanOriginalCompositionPastingTriangle r F f g 1 =
        (pastingSquareHorizontal 1 ≫ threeSquareInclusion 0) ≫
          kKanOriginalCompositionPastingSquares r F f g at h
      simpa only [Category.assoc, kKanOriginalCompositionPastingSquares_square] using h)
    (by
      have h := kKanOriginalCompositionPastingTriangle_lower r F f g 1
      change stdSimplex.δ 1 ≫ kKanOriginalCompositionPastingTriangle r F f g 1 =
        (pastingSquareHorizontal 1 ≫ threeSquareInclusion 1) ≫
          kKanOriginalCompositionPastingSquares r F f g at h
      simpa only [Category.assoc, kKanOriginalCompositionPastingSquares_square] using h)
    (by
      have h := kKanOriginalCompositionPastingTriangle_upper r F f g 2
      change stdSimplex.δ 2 ≫ kKanOriginalCompositionPastingTriangle r F f g 2 =
        (pastingSquareVertical 1 ≫ threeSquareInclusion 1) ≫
          kKanOriginalCompositionPastingSquares r F f g at h
      simpa only [Category.assoc, kKanOriginalCompositionPastingSquares_square] using h)
    (by
      have h := kKanOriginalCompositionPastingTriangle_lower r F f g 2
      change stdSimplex.δ 1 ≫ kKanOriginalCompositionPastingTriangle r F f g 2 =
        (pastingSquareVertical 1 ≫ threeSquareInclusion 2) ≫
          kKanOriginalCompositionPastingSquares r F f g at h
      simpa only [Category.assoc, kKanOriginalCompositionPastingSquares_square] using h)

/-- 比較入力は元の三正方形全体を保持する。 -/
lemma kKanOriginalCompositionCompatibilityData_squares (q : Fin 3) :
    ![(kKanOriginalCompositionCompatibilityData r F f g).firstSquare.square,
      (kKanOriginalCompositionCompatibilityData r F f g).middleSquare.square,
      (kKanOriginalCompositionCompatibilityData r F f g).lastSquare.square] q =
      kKanOriginalCompositionMappingSquare r F f g q := by
  fin_cases q <;> rfl

/-- 比較入力の三指定三角形も、元の全二単体そのものである。 -/
lemma kKanOriginalCompositionCompatibilityData_triangles (e : Fin 3) :
    ![(kKanOriginalCompositionCompatibilityData r F f g).compositeTriangle.simplex,
      (kKanOriginalCompositionCompatibilityData r F f g).firstTriangle.simplex,
      (kKanOriginalCompositionCompatibilityData r F f g).secondTriangle.simplex] e =
      SSet.yonedaEquiv (kKanOriginalCompositionPastingTriangle r F f g e) := by
  fin_cases e <;> rfl

end SerrePositivity.KST.SConstruction
