module
public import SerrePositivity.KST.SConstruction.KCompositionNativeFamilies
public import SerrePositivity.KST.SConstruction.RelativeSpecifiedTriangleMaps

/-! # 元の全三適合円柱を固定する全精密化の比較三角形
概要：元の三円柱と指定直通列点の全比較三角形を同時に保持して延長する。
方針：直通列点の anodyne 性と、全境界を固定する相対三角形族の構成を使う。
規約：三辺の全時刻と指定点の全二単体を厳密に回収する。零段も含む。
使われ方：元の全パラメータの合成適合比較を全段の補正列へ接続する。
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
local instance kCompositionNativeTrianglesPointedCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
local instance kCompositionNativeTrianglesKan {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (x z : I) :
    KanComplex
      (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj x)).level r).space)
        ((kKanSequence (F.obj z)).level (r + 1)).space).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
variable {I : Type u} [SmallCategory I] (r : ℕ) (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の三円柱と指定した元の比較三角形を保つ、全精密化の実二単体族。 -/
def kKanCompositionNativeTriangle :
    nerve (CompositionStringParameters f g) ⊗ (Δ[2] : SSet.{u}) ⟶
      (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj x)).level r).space)
        ((kKanSequence (F.obj z)).level (r + 1)).space).right :=
  relativeSpecifiedTriangleMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g))
    (kKanCompositionFirstNativeFamily r F f g) (kKanCompositionSecondNativeFamily r F f g)
    (kKanCompositionCompositeNativeFamily r F f g)
    (snd (Δ[0] : SSet.{u}) (Δ[2] : SSet.{u}) ≫
      SSet.yonedaEquiv.symm (kKanOriginalCompositionCompatibilityTriangle r F f g).simplex)
    (by
      rw [← Category.assoc, whiskerLeft_snd, Category.assoc,
        kKanOriginalCompositionCompatibilityTriangle_face_first,
        kKanCompositionFirstNativeFamily_boundary])
    (by
      rw [← Category.assoc, whiskerLeft_snd, Category.assoc,
        kKanOriginalCompositionCompatibilityTriangle_face_second,
        kKanCompositionSecondNativeFamily_boundary])
    (by
      rw [← Category.assoc, whiskerLeft_snd, Category.assoc,
        kKanOriginalCompositionCompatibilityTriangle_face_composite,
        kKanCompositionCompositeNativeFamily_boundary])
    (compositionStringDirect_anodyne f g)

/-- 指定直通列点では、元の六セルから作った同じ全比較三角形を回収する。 -/
lemma kKanCompositionNativeTriangle_boundary :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g) ▷ (Δ[2] : SSet.{u})) ≫
        kKanCompositionNativeTriangle r F f g =
      snd (Δ[0] : SSet.{u}) (Δ[2] : SSet.{u}) ≫
        SSet.yonedaEquiv.symm (kKanOriginalCompositionCompatibilityTriangle r F f g).simplex := by
  rw [kKanCompositionNativeTriangle, relativeSpecifiedTriangleMap_boundary]

/-- 全精密化の 01 面は、前の射の元の全適合円柱の実後合成。 -/
lemma kKanCompositionNativeTriangle_first :
    (nerve (CompositionStringParameters f g) ◁ stdSimplex.δ 2) ≫
      kKanCompositionNativeTriangle r F f g = (kKanCompositionFirstNativeCylinder r F f g).h := by
  rw [kKanCompositionNativeTriangle, relativeSpecifiedTriangleMap_first]
  rfl

/-- 全精密化の 12 面は、後の射の元の全適合円柱の実前合成。 -/
lemma kKanCompositionNativeTriangle_second :
    (nerve (CompositionStringParameters f g) ◁ stdSimplex.δ 0) ≫
      kKanCompositionNativeTriangle r F f g = (kKanCompositionSecondNativeCylinder r F f g).h := by
  rw [kKanCompositionNativeTriangle, relativeSpecifiedTriangleMap_second]
  rfl

/-- 全精密化の 02 面は、合成射の元の全適合円柱そのもの。 -/
lemma kKanCompositionNativeTriangle_composite :
    (nerve (CompositionStringParameters f g) ◁ stdSimplex.δ 1) ≫
      kKanCompositionNativeTriangle r F f g =
        (kKanCompositionCompositeNativeCylinder r F f g).h := by
  rw [kKanCompositionNativeTriangle, relativeSpecifiedTriangleMap_composite]
  rfl

end SerrePositivity.KST.SConstruction
