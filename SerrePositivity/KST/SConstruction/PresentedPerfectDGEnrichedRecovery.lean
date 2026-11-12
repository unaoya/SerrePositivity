module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGEnrichedFunctor
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGFunctor

/-! # 厳密豊穣 Perf 関手の元の通常作用の回収
概要：出力宇宙の通常の入力射から、元の dg Perf 作用と同じ QCat 関手を得る。
方針：元の dg 作用の恒等・合成を使い、豊穣 Hom を含めた単位射の像も回収する。
規約：元の全 Perf 単体の射を保持。使われ方：完全性と元の K への比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 出力宇宙の元の入力射に、同じ native Perf 作用を対応させる通常の関手。 -/
def presentedPerfectDGQCatFunctor :
    PerfDGInput.{u, v} A ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{max (u + 1) v} where
  obj := presentedPerfectDGQCat A
  map F := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGAction A _ _ F.down)
  map_id C := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGAction A C C (DGFunctor.id C)) =
      𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A C))
    rw [presentedPerfectDGAction_id, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_id]
  map_comp {C D E} F G := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGAction A C E (DGFunctor.comp F.down G.down)) = _
    rw [← presentedPerfectDGAction_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp]
    rfl

/-- 元の通常の Perf 関手の対象は、同じラベル付き native Perf 模型。 -/
lemma presentedPerfectDGQCatFunctor_obj (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGQCatFunctor A).obj C = presentedPerfectDGQCat A C := rfl

/-- 元の通常の Perf 関手の射は、同じ厳密 dg 入力による元の native 作用。 -/
lemma presentedPerfectDGQCatFunctor_map {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    (presentedPerfectDGQCatFunctor A).map F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGAction A C D F.down) := rfl

/-- 豊穣射の元の単位射への作用は、包含後に同じ通常の Perf 射の curry を回収する。 -/
lemma presentedPerfectDGEnrichedFunctor_hom_recovery
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    (eHomEquiv SSet.{max (u + 1) v} F ≫ (presentedPerfectDGEnrichedFunctor A).map C D) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A C))).obj
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A D)))).ι =
      curry' (C := SSet.{max (u + 1) v}) ((presentedPerfectDGQCatFunctor A).map F) := by
  change (perfDGInputUnitHomEquiv A C D F ≫ presentedPerfectDGNativeCoreFamilyMap A C D) ≫ _ = _
  rw [Category.assoc, presentedPerfectDGNativeCoreFamilyMap_inclusion,
    perfDGInputUnitHomEquiv_point, presentedPerfectDGNativeFamilyMap_fixed]
  rfl

private lemma qCat_homEquiv_inclusion
    {X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{w}} (f : X ⟶ Y) :
    eHomEquiv SSet.{w} f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom X.obj).obj Y.obj)).ι =
      curry' (C := SSet.{w}) f := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCoreUnitHomEquiv _ (curry' (C := SSet.{w}) f) ≫ _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCoreUnitHomEquiv_eq, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_ι]
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCoreUnit ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (𝟙_ SSet.{w})).ι = 𝟙 _ := rfl
  rw [← Category.assoc, h, Category.id_comp]

/-- 厳密豊穣 Perf 関手は、元の通常の Perf 関手と同じ入力射の像を持つ。 -/
lemma presentedPerfectDGEnrichedFunctor_hom
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    eHomEquiv SSet.{max (u + 1) v} F ≫ (presentedPerfectDGEnrichedFunctor A).map C D =
      eHomEquiv SSet.{max (u + 1) v} ((presentedPerfectDGQCatFunctor A).map F) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A C))).obj
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A D)))).ι).mp
  exact (presentedPerfectDGEnrichedFunctor_hom_recovery A F).trans
    (qCat_homEquiv_inclusion ((presentedPerfectDGQCatFunctor A).map F)).symm

end SerrePositivity.KST.SConstruction
