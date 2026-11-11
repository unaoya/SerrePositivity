module
public import SerrePositivity.KST.SConstruction.MultiSQuasicategoryEnrichedDiagram
public import SerrePositivity.KST.SConstruction.QuasicategoryEnrichedObjectCore
public import SerrePositivity.KST.SConstruction.CoreEnrichedInclusion
public import SerrePositivity.KST.SConstruction.SExactCoreEnrichedFunctor
public import SerrePositivity.KST.SConstruction.MultiRealization

/-! # 全自然同値を保持する安定入力の反復 core S• 図式
概要：完全関手空間の実 core を入力とし、元の全多次数の core S• を保持する。
方針：同じ core 包含で前合成し、既存の実対象 core 関手を適用する。
規約：全高次入力を保持。使われ方：関手同型の全反復実現への移送。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories LocalizingInvariants

/-- 全自然同値を入力とする、元の全多単体 S• 図式。 -/
def stableMultiSEnrichedDiagram (r : ℕ) :
    (Fin r → SimplexCategoryᵒᵖ) ⥤ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedFunctorCategory _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u} :=
  multiSQuasicategoryEnrichedDiagram r ⋙
    quasicategoryEnrichedPrecompositionFunctor (coreEnrichedInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u})

/-- 全自然同値と元の全多次数を保持する、実 core S• 図式。 -/
def stableMultiSCoreEnrichedDiagram (r : ℕ) :
    (Fin r → SimplexCategoryᵒᵖ) ⥤ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedFunctorCategory _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u} :=
  stableMultiSEnrichedDiagram r ⋙ quasicategoryEnrichedObjectCoreFunctor

/-- 同じ全多次数の実値は、元の反復 core S• の値。 -/
lemma stableMultiSCoreEnrichedDiagram_obj (r : ℕ)
    (d : Fin r → SimplexCategoryᵒᵖ) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (((stableMultiSCoreEnrichedDiagram r).obj d).obj C).obj =
      (multiCoreSConstruction r (stableCategoryModel C)).obj d := rfl

/-- 元の通常の完全射では、同じ反復 S の射を回収する。 -/
lemma stableMultiSEnrichedDiagram_hom (r : ℕ)
    (d : Fin r → SimplexCategoryᵒᵖ) {C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (F : C ⟶ D) :
    eHomEquiv SSet.{u} F ≫ ((stableMultiSEnrichedDiagram r).obj d).map C D =
      curry' (C := SSet.{u}) (multiSExactMap r d F).hom := by
  change eHomEquiv SSet.{u} F ≫
    ((coreEnrichedInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}).map C D ≫
      (multiSQuasicategoryEnrichedFunctor r d).map C D) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ (multiSQuasicategoryEnrichedFunctor r d).map C D)
      (stableExactCoreHomEquiv_inclusion F)).trans
        (multiSQuasicategoryEnrichedFunctor_hom r d F))

/-- 元の通常の完全射では、同じ反復 core の射を回収する。 -/
lemma stableMultiSCoreEnrichedDiagram_hom (r : ℕ)
    (d : Fin r → SimplexCategoryᵒᵖ) {C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (F : C ⟶ D) :
    eHomEquiv SSet.{u} F ≫ ((stableMultiSCoreEnrichedDiagram r).obj d).map C D =
      curry' (C := SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (multiSExactMap r d F).hom) := by
  change eHomEquiv SSet.{u} F ≫
    ((quasicategoryEnrichedCoreFunctor ((stableMultiSEnrichedDiagram r).obj d)).map C D ≫
      𝟙 _) = _
  rw [Category.comp_id]
  exact quasicategoryEnrichedCoreFunctor_hom _ F _ (stableMultiSEnrichedDiagram_hom r d F)

end SerrePositivity.KST.SConstruction
