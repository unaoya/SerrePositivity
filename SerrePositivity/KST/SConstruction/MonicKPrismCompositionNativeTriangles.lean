module
public import SerrePositivity.KST.SConstruction.KCompositionNativeTriangles
public import SerrePositivity.KST.SConstruction.MonicKPrismOriginalCompositionTriangle

/-! # 単射源の全精密化上の実合成比較三角形
概要：元の全精密化の比較三角形族を、全二単体ごと単射源へ前合成する。
方針：元の源の射影を同じ全族に適用し、三面と指定頂点の厳密な回収を使う。
規約：零段を含み、三円柱の全時刻と元の指定比較三角形を保持する。
使われ方：元の全適合族と保存済みの BF 補正列を同じ Hom 内で比較する。
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
local instance monicKPrismCompositionNativeTrianglesPointedCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
variable {I : Type u} [SmallCategory I] (r : ℕ) (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の全三角形族を、単射源からの同じ suspension Hom に表示する。 -/
def monicKPrismCompositionNativeTriangle :
    nerve (CompositionStringParameters f g) ⊗ (Δ[2] : SSet.{u}) ⟶
      (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kOmegaSpectrum (F.obj x)).level r).space)
        ((kKanSequence (F.obj z)).level (r + 1)).space).right :=
  kKanCompositionNativeTriangle r F f g ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre
      (PointedSimplicialSet.circle.{u} ◁ (monicKKanSequenceProjection (F.obj x)).app r)
      ((kKanSequence (F.obj z)).level (r + 1)).space

/-- 指定直通列点では、元の同じ単射源の全比較二単体を厳密に回収する。 -/
lemma monicKPrismCompositionNativeTriangle_boundary :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g) ▷ (Δ[2] : SSet.{u})) ≫
        monicKPrismCompositionNativeTriangle r F f g =
      snd (Δ[0] : SSet.{u}) (Δ[2] : SSet.{u}) ≫
        monicKPrismOriginalCompositionTriangle r F f g := by
  rw [monicKPrismCompositionNativeTriangle, ← Category.assoc,
    kKanCompositionNativeTriangle_boundary, Category.assoc]
  rfl

/-- 第一面は元の前の適合円柱の全精密化と同じ源の射影。 -/
lemma monicKPrismCompositionNativeTriangle_first :
    (nerve (CompositionStringParameters f g) ◁ stdSimplex.δ 2) ≫
        monicKPrismCompositionNativeTriangle r F f g =
      (kKanCompositionFirstNativeCylinder r F f g).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre
          (PointedSimplicialSet.circle.{u} ◁ (monicKKanSequenceProjection (F.obj x)).app r)
          ((kKanSequence (F.obj z)).level (r + 1)).space := by
  rw [monicKPrismCompositionNativeTriangle, ← Category.assoc, kKanCompositionNativeTriangle_first]

/-- 第二面は元の後の適合円柱の全精密化と同じ源の射影。 -/
lemma monicKPrismCompositionNativeTriangle_second :
    (nerve (CompositionStringParameters f g) ◁ stdSimplex.δ 0) ≫
        monicKPrismCompositionNativeTriangle r F f g =
      (kKanCompositionSecondNativeCylinder r F f g).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre
          (PointedSimplicialSet.circle.{u} ◁ (monicKKanSequenceProjection (F.obj x)).app r)
          ((kKanSequence (F.obj z)).level (r + 1)).space := by
  rw [monicKPrismCompositionNativeTriangle, ← Category.assoc, kKanCompositionNativeTriangle_second]

/-- 合成面も元の合成射の全適合円柱と同じ源の射影を保持する。 -/
lemma monicKPrismCompositionNativeTriangle_composite :
    (nerve (CompositionStringParameters f g) ◁ stdSimplex.δ 1) ≫
        monicKPrismCompositionNativeTriangle r F f g =
      (kKanCompositionCompositeNativeCylinder r F f g).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre
          (PointedSimplicialSet.circle.{u} ◁ (monicKKanSequenceProjection (F.obj x)).app r)
          ((kKanSequence (F.obj z)).level (r + 1)).space := by
  rw [monicKPrismCompositionNativeTriangle, ← Category.assoc,
    kKanCompositionNativeTriangle_composite]

end SerrePositivity.KST.SConstruction
