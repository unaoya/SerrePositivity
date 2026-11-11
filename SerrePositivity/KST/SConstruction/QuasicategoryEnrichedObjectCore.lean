module
public import SerrePositivity.KST.SConstruction.QuasicategoryEnrichedCoreComparison
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedFunctorCategory

/-! # 全高次比較を保つ実対象 core の関手
概要：局所 Kan な入力上の実 Quasi 値図式を、同じ対象 core の図式へ移す。
方針：Kan 値の厳密豊穣関手を Quasi 値へ含め、元の比較の core 射を使う。
規約：全入力 Hom を保持する。使われ方：元の面退化を持つ core S• 図式。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories

/-- 実 Kan 対象を、同じ全内部 Hom を持つ Quasi 対象として含める。 -/
def kanObjectEnrichedInclusion :
    EnrichedFunctor SSet.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u} where
  obj X := ⟨X.obj, inferInstance⟩
  map X Y := 𝟙 ((ihom X.obj).obj Y.obj)
  map_id X := Category.comp_id _
  map_comp X Y Z := by
    change _ ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ _
    simp only [Category.comp_id, tensorHom_id, id_whiskerRight, Category.id_comp]
    rfl

variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 全高次 Kan 比較を、同じ成分の全高次 Quasi 比較として含める。 -/
def kanEnrichedComparisonQuasicategory
    {F G : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} (η : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison F G) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison (F.comp SSet.{u} kanObjectEnrichedInclusion)
      (G.comp SSet.{u} kanObjectEnrichedInclusion) := by
  refine ⟨fun X => (show (F.obj X).obj ⟶ (G.obj X).obj from η.val X), ?_⟩
  intro X Y
  change ((show (F.obj X).obj ⟶ (G.obj X).obj from η.val X) ▷
      (X ⟶[SSet.{u}] Y)) ≫ uncurry (G.map X Y ≫ 𝟙 _) =
    uncurry (F.map X Y ≫ 𝟙 _) ≫
      (show (F.obj Y).obj ⟶ (G.obj Y).obj from η.val Y)
  simpa only [Category.comp_id] using η.property X Y

variable [∀ X Y : C, KanComplex (X ⟶[SSet.{u}] Y)]

/-- 同じ実対象 core と全入力 Hom を保持する、全高次比較の圏上の関手。 -/
def quasicategoryEnrichedObjectCoreFunctor :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedFunctorCategory C ⥤ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedFunctorCategory C where
  obj F := (quasicategoryEnrichedCoreFunctor F).comp SSet.{u} kanObjectEnrichedInclusion
  map η := kanEnrichedComparisonQuasicategory (quasicategoryEnrichedCoreComparison η)
  map_id F := by
    apply Subtype.ext
    funext X
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map_id (F.obj X).obj
  map_comp η θ := by
    apply Subtype.ext
    funext X
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map_comp (η.val X) (θ.val X)

/-- 実対象 core 関手の比較成分は元の同じ成分の core 射。 -/
lemma quasicategoryEnrichedObjectCoreFunctor_map
    {F G : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedFunctorCategory C} (η : F ⟶ G) (X : C) :
    ((quasicategoryEnrichedObjectCoreFunctor.map η).val X) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (η.val X) := rfl

end SerrePositivity.KST.SConstruction
