module
public import SerrePositivity.KST.SConstruction.MultiSQuasicategoryEnrichedDiagram
public import SerrePositivity.KST.SConstruction.QuasicategoryEnrichedObjectCore
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGFullEnrichedFunctor
public import SerrePositivity.KST.SConstruction.MultiRealization

/-! # 全厳密 dg 入力を保持する有限反復 core S• 図式
概要：全方向の元の反復 S• と実 core を、全 native Kan 入力に自然な図式にする。
方針：完全 Perf の全 Hom で前合成してから、実対象 core 関手を適用する。
規約：元の多単体図式の値と制限を変えない。使われ方：反復実現と豊穣 BF K の入力。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の全多単体 S• Perf を、全 native Kan dg 入力族に自然な図式として保持する。 -/
def presentedPerfectDGMultiSEnrichedDiagram (r : ℕ) :
    (Fin r → SimplexCategoryᵒᵖ) ⥤
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedFunctorCategory (PerfDGInput.{u, v} A) :=
  multiSQuasicategoryEnrichedDiagram r ⋙
    quasicategoryEnrichedPrecompositionFunctor (presentedPerfectDGFullEnrichedFunctor A)

/-- 元の全多単体 core S• Perf と全入力 Hom を同時に保持する実図式。 -/
def presentedPerfectDGMultiSCoreEnrichedDiagram (r : ℕ) :
    (Fin r → SimplexCategoryᵒᵖ) ⥤
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedFunctorCategory (PerfDGInput.{u, v} A) :=
  presentedPerfectDGMultiSEnrichedDiagram A r ⋙ quasicategoryEnrichedObjectCoreFunctor

/-- 全多次数の実 core 値は、元の同じ反復 core S• の値。 -/
lemma presentedPerfectDGMultiSCoreEnrichedDiagram_obj (r : ℕ)
    (d : Fin r → SimplexCategoryᵒᵖ) (C : PerfDGInput.{u, v} A) :
    (((presentedPerfectDGMultiSCoreEnrichedDiagram A r).obj d).obj C).obj =
      (multiCoreSConstruction r
        (stableCategoryModel (presentedPerfectDGStableCategory A C))).obj d := rfl

/-- 全方向の面退化は、元の同じ反復 core S• の制限射。 -/
lemma presentedPerfectDGMultiSCoreEnrichedDiagram_map (r : ℕ)
    {d e : Fin r → SimplexCategoryᵒᵖ} (θ : d ⟶ e) (C : PerfDGInput.{u, v} A) :
    ((presentedPerfectDGMultiSCoreEnrichedDiagram A r).map θ).val C =
      (multiCoreSConstruction r
        (stableCategoryModel (presentedPerfectDGStableCategory A C))).map θ := rfl

/-- 元の通常 dg 射では、同じ全反復の元の完全射を回収する。 -/
lemma presentedPerfectDGMultiSEnrichedDiagram_hom (r : ℕ)
    (d : Fin r → SimplexCategoryᵒᵖ) {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    eHomEquiv SSet.{max (u + 1) v} F ≫
      ((presentedPerfectDGMultiSEnrichedDiagram A r).obj d).map C D =
        curry' (C := SSet.{max (u + 1) v})
          (multiSExactMap r d (presentedPerfectDGExactMap A F)).hom := by
  change eHomEquiv SSet.{max (u + 1) v} F ≫
    ((presentedPerfectDGFullEnrichedFunctor A).map C D ≫
      (multiSQuasicategoryEnrichedFunctor r d).map _ _) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (multiSQuasicategoryEnrichedFunctor r d).map
      (presentedPerfectDGStableCategory A C) (presentedPerfectDGStableCategory A D))
        (presentedPerfectDGFullEnrichedFunctor_hom A F)).trans
          (multiSQuasicategoryEnrichedFunctor_hom r d (presentedPerfectDGExactMap A F)))

/-- 元の通常 dg 射の実 core 像は、同じ元の全反復 core 射。 -/
lemma presentedPerfectDGMultiSCoreEnrichedDiagram_hom (r : ℕ)
    (d : Fin r → SimplexCategoryᵒᵖ) {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    eHomEquiv SSet.{max (u + 1) v} F ≫
      ((presentedPerfectDGMultiSCoreEnrichedDiagram A r).obj d).map C D =
        curry' (C := SSet.{max (u + 1) v})
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (multiSExactMap r d (presentedPerfectDGExactMap A F)).hom) := by
  change eHomEquiv SSet.{max (u + 1) v} F ≫
    ((quasicategoryEnrichedCoreFunctor
      ((presentedPerfectDGMultiSEnrichedDiagram A r).obj d)).map C D ≫ 𝟙 _) = _
  rw [Category.comp_id]
  exact quasicategoryEnrichedCoreFunctor_hom _ F _
    (presentedPerfectDGMultiSEnrichedDiagram_hom A r d F)

end SerrePositivity.KST.SConstruction
