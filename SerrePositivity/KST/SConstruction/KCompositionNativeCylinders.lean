module
public import SerrePositivity.KST.SConstruction.CompositionStringParameters
public import SerrePositivity.KST.SConstruction.SpecifiedPointConstantHomotopies
public import SerrePositivity.KST.SConstruction.KCompositionCompatibilityTriangle

/-! # 共通精密化パラメータ上の元の三適合円柱
概要：合成射と二入力射の元の全円柱を、三つの合成列圏の積へ移す。
方針：各射影と元の前後合成だけを使い、指定直通列点の全区間を回収する。
規約：元の実円柱と全パラメータを保持し、適合辺を選び直さない。
使われ方：三辺を固定した、全精密化上の実比較三角形の入力。
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
local instance kCompositionNativeCylindersPointedCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
variable {I : Type u} [SmallCategory I] (r : ℕ) (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の前の射の適合円柱を、独立な全精密化の共通パラメータに移す。 -/
def kKanCompositionFirstNativeCylinder :=
  constantFamilyHomotopyWhisker (nerveMap (compositionStringFirst f g))
    ((PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj x)).level r).space)
      (kKanSequenceLevelMap (F.map g) (r + 1))).right)
    (kKanOriginalPrismSpecifiedCompatibilityFamily r F f)

/-- 指定直通列の組では、元の前の射の適合区間の全時刻を厳密に回収する。 -/
lemma kKanCompositionFirstNativeCylinder_boundary :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g) ▷ (Δ[1] : SSet.{u})) ≫
        (kKanCompositionFirstNativeCylinder r F f g).h =
      snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
        SSet.yonedaEquiv.symm (kKanOriginalCompositionCompatibilityData r F f g).first.edge := by
  have h := constantFamilyHomotopyWhisker_boundary
    (nerveMap (compositionStringFirst f g))
    ((PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj x)).level r).space)
      (kKanSequenceLevelMap (F.map g) (r + 1))).right)
    (kKanOriginalPrismSpecifiedCompatibilityFamily r F f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f))
    (SSet.yonedaEquiv.symm (kKanSuspensionCompatibilityEdge r F f).edge)
    (compositionStringFirst_direct f g)
    (kKanOriginalPrismSpecifiedCompatibilityFamily_boundary r F f)
  simpa only [kKanCompositionFirstNativeCylinder,
    kKanOriginalCompositionCompatibilityData_first, Category.assoc] using h

/-- 元の後の射の適合円柱を、独立な全精密化の共通パラメータに移す。 -/
def kKanCompositionSecondNativeCylinder :=
  constantFamilyHomotopyWhisker (nerveMap (compositionStringSecond f g))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre
      (PointedSimplicialSet.circle.{u} ◁ kKanSequenceLevelMap (F.map f) r)
      ((kKanSequence (F.obj z)).level (r + 1)).space)
    (kKanOriginalPrismSpecifiedCompatibilityFamily r F g)

/-- 指定直通列の組では、元の後の射の適合区間の全時刻を厳密に回収する。 -/
lemma kKanCompositionSecondNativeCylinder_boundary :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g) ▷ (Δ[1] : SSet.{u})) ≫
        (kKanCompositionSecondNativeCylinder r F f g).h =
      snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
        SSet.yonedaEquiv.symm (kKanOriginalCompositionCompatibilityData r F f g).second.edge := by
  have h := constantFamilyHomotopyWhisker_boundary
    (nerveMap (compositionStringSecond f g)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre
      (PointedSimplicialSet.circle.{u} ◁ kKanSequenceLevelMap (F.map f) r)
      ((kKanSequence (F.obj z)).level (r + 1)).space)
    (kKanOriginalPrismSpecifiedCompatibilityFamily r F g)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect g))
    (SSet.yonedaEquiv.symm (kKanSuspensionCompatibilityEdge r F g).edge)
    (compositionStringSecond_direct f g)
    (kKanOriginalPrismSpecifiedCompatibilityFamily_boundary r F g)
  simpa only [kKanCompositionSecondNativeCylinder,
    kKanOriginalCompositionCompatibilityData_second, Category.assoc] using h

/-- 元の合成射の適合円柱を、独立な全精密化の共通パラメータに移す。 -/
def kKanCompositionCompositeNativeCylinder :=
  constantFamilyHomotopyWhisker (nerveMap (compositionStringComposite f g))
    (𝟙 (kKanOriginalSuspensionMappingTarget r F x z))
    (kKanOriginalPrismSpecifiedCompatibilityFamily r F (f ≫ g))

/-- 指定直通列の組では、元の合成射の適合区間の全時刻を厳密に回収する。 -/
lemma kKanCompositionCompositeNativeCylinder_boundary :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g) ▷ (Δ[1] : SSet.{u})) ≫
        (kKanCompositionCompositeNativeCylinder r F f g).h =
      snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
        SSet.yonedaEquiv.symm
          (kKanOriginalCompositionCompatibilityData r F f g).composite.edge := by
  rw [kKanOriginalCompositionCompatibilityData_composite]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g) ▷ (Δ[1] : SSet.{u})) ≫
    ((nerveMap (compositionStringComposite f g) ▷ (Δ[1] : SSet.{u})) ≫
      (kKanOriginalPrismSpecifiedCompatibilityFamily r F (f ≫ g)).h ≫ 𝟙 _) = _
  rw [Category.comp_id, ← Category.assoc, ← comp_whiskerRight,
    compositionStringComposite_direct]
  exact kKanOriginalPrismSpecifiedCompatibilityFamily_boundary r F (f ≫ g)

end SerrePositivity.KST.SConstruction
