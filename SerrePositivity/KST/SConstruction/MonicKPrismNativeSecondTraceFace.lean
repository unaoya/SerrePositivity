module
public import SerrePositivity.KST.SConstruction.MonicKPrismNativeTraceFaces
public import SerrePositivity.KST.SConstruction.MonicKPrismOriginalCompatibilityCylinder

/-! # 元の全三角形の第二面と二次元補正の元の始点
概要：単射源の全比較三角形の第二面を、元の段族での後続適合円柱へ厳密に照合する。
方針：同じ源の二前合成を合成し、定数段族との実豊穣合成を通常の前合成へ戻す。
規約：元の全時刻と全精密化を保持し、補正後の円柱と同じと仮定しない。
使われ方：保存済みの二次元補正列を、元の全比較三角形へ接続する。
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
local instance nativeSecondTraceFacePointedCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
variable {I : Type u} [SmallCategory I] (r : ℕ) (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の第二円柱の源の制限は、元の定数段族での同じ合成円柱。 -/
lemma monicKPrismCompositionNativeSecondCylinder_trace :
    (kKanCompositionSecondNativeCylinder r F f g).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre
          (PointedSimplicialSet.circle.{u} ◁ (monicKKanSequenceProjection (F.obj x)).app r)
          ((kKanSequence (F.obj z)).level (r + 1)).space =
      (compositionStringPair f g ▷ (Δ[1] : SSet.{u})) ≫
        monicKPrismCompositeCompatibilityAt F f g r (monicKPrismRawLevelFamily r F f) := by
  let p : ((monicKKanSequence (F.obj x)).level r).space ⟶
      ((kKanSequence (F.obj x)).level r).space := (monicKKanSequenceProjection (F.obj x)).app r
  have hs := pointedMapping_pre_suspension_comp
    (Z := ((kKanSequence (F.obj z)).level (r + 1)).space)
    p (kKanSequenceLevelMap (F.map f) r)
  have hh := congrArg (fun h => (nerveMap (compositionStringSecond f g) ▷ (Δ[1] : SSet.{u})) ≫
    (kKanOriginalPrismSpecifiedCompatibilityFamily r F g).h ≫ h) hs
  have ht := congrArg (fun h => (compositionStringPair f g ▷ (Δ[1] : SSet.{u})) ≫ h)
    (monicKPrismCompositeCompatibilityAt_raw F f g r)
  simp only [monicKPrismCompositeCompatibility_h, Category.assoc,
    ← comp_whiskerRight_assoc, compositionStringPair_second] at ht
  have hh' : (kKanCompositionSecondNativeCylinder r F f g).h ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre
        (PointedSimplicialSet.circle.{u} ◁ (monicKKanSequenceProjection (F.obj x)).app r)
        ((kKanSequence (F.obj z)).level (r + 1)).space =
      (nerveMap (compositionStringSecond f g) ▷ (Δ[1] : SSet.{u})) ≫
        (kKanOriginalPrismSpecifiedCompatibilityFamily r F g).h ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre
            (PointedSimplicialSet.circle.{u} ◁ monicKToRawLevelMap (F.map f) r)
            ((kKanSequence (F.obj z)).level (r + 1)).space := by
    simpa only [kKanCompositionSecondNativeCylinder, constantFamilyHomotopyWhisker,
      Category.assoc, p, monicKToRawLevelMap] using hh
  exact hh'.trans ht.symm

/-- 第二面は、保存済み二次元補正の元の定数段族での始点の同じ引き戻し。 -/
lemma monicKPrismCompositionNativeTriangle_second_trace :
    (nerve (CompositionStringParameters f g) ◁ stdSimplex.δ 0) ≫
        monicKPrismCompositionNativeTriangle r F f g =
      (compositionStringPair f g ▷ (Δ[1] : SSet.{u})) ≫
        monicKPrismCompositeCompatibilityAt F f g r (monicKPrismRawLevelFamily r F f) :=
  (monicKPrismCompositionNativeTriangle_second r F f g).trans
    (monicKPrismCompositionNativeSecondCylinder_trace r F f g)

end SerrePositivity.KST.SConstruction
