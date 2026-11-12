module
public import SerrePositivity.KST.SConstruction.QuasicategoryEnrichedCoreFunctor
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedComparisonComposition

/-! # 全高次比較の実 core への自然な持ち上げ
概要：元の全 Hom に自然な比較を、同じ実 core 値の全パラメータ比較に移す。
方針：元の成分の core 射を使い、包含後に全単体の元の自然性を反映する。
規約：比較成分を選び直さない。使われ方：core S• の面退化と全単体的図式。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  [∀ X Y : C, KanComplex (X ⟶[SSet.{u}] Y)]
  {F G : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u}}

/-- 同じ元の全高次比較は、実 core 値への作用とも全単体で厳密に可換する。 -/
lemma quasicategoryEnrichedCoreAction_naturality (η : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison F G)
    (X Y : C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (η.val X) ▷ (X ⟶[SSet.{u}] Y)) ≫
        quasicategoryEnrichedCoreAction G X Y =
      quasicategoryEnrichedCoreAction F X Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (η.val Y) := by
  ext n p
  apply Subtype.ext
  exact congrArg (fun f => f.app n (p.1.val, p.2)) (η.property X Y)

/-- 同じ元の全高次比較を、実 core 値の Kan 比較に移す。 -/
def quasicategoryEnrichedCoreComparison (η : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison F G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison (quasicategoryEnrichedCoreFunctor F)
      (quasicategoryEnrichedCoreFunctor G) := by
  refine ⟨fun X => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (η.val X), ?_⟩
  intro X Y
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (η.val X) ▷ (X ⟶[SSet.{u}] Y)) ≫
    uncurry (curry (quasicategoryEnrichedCoreAction G X Y)) =
      uncurry (curry (quasicategoryEnrichedCoreAction F X Y)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (η.val Y)
  rw [uncurry_curry, uncurry_curry]
  exact quasicategoryEnrichedCoreAction_naturality η X Y

/-- 実 core 比較の各成分は、元の同じ比較成分の core 射である。 -/
lemma quasicategoryEnrichedCoreComparison_app (η : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison F G)
    (X : C) : (quasicategoryEnrichedCoreComparison η).val X =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (η.val X) := rfl

end SerrePositivity.KST.SConstruction
