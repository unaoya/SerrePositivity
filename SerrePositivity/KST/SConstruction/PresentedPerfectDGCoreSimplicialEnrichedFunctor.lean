module
public import SerrePositivity.KST.SConstruction.QuasicategoryEnrichedObjectCore
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGSimplicialEnrichedFunctor
public import SerrePositivity.KST.SConstruction.CoreSimplicial

/-! # 全厳密 dg 入力を保持する実 core S• 図式
概要：元の各 S_n Perf の core と、元の全ての面退化を厳密豊穣図式に束ねる。
方針：実 S• 豊穣図式に、全高次比較を保つ対象 core 関手を後合成する。
規約：入力 Hom を離散化しない。使われ方：core S• 全体と反復・実現への接続。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の全 native Kan dg 入力族に自然な、同じ実 core S• Perf 図式。 -/
def presentedPerfectDGCoreSimplicialEnrichedFunctor :
    SimplicialObject (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedFunctorCategory (PerfDGInput.{u, v} A)) :=
  presentedPerfectDGSimplicialEnrichedFunctor A ⋙ quasicategoryEnrichedObjectCoreFunctor

/-- 実 core 図式の各段は、同じ元の全 gapped S_n Perf の core。 -/
lemma presentedPerfectDGCoreSimplicialEnrichedFunctor_obj
    (C : PerfDGInput.{u, v} A) (n : SimplexCategoryᵒᵖ) :
    (((presentedPerfectDGCoreSimplicialEnrichedFunctor A).obj n).obj C).obj =
      coreSConstruction n.unop.len (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A C)) := rfl

/-- 全ての面退化は、元の同じ添字制限の core 射。 -/
lemma presentedPerfectDGCoreSimplicialEnrichedFunctor_map
    (C : PerfDGInput.{u, v} A) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    ((presentedPerfectDGCoreSimplicialEnrichedFunctor A).map f).val C =
      coreSMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A C)) f.unop.toOrderHom := rfl

/-- 通常の元の dg 入力射では、同じ cofiber 型 S_n 射の core を回収する。 -/
lemma presentedPerfectDGCoreSimplicialEnrichedFunctor_hom (n : SimplexCategoryᵒᵖ)
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    eHomEquiv SSet.{max (u + 1) v} F ≫
      ((presentedPerfectDGCoreSimplicialEnrichedFunctor A).obj n).map C D =
        curry' (C := SSet.{max (u + 1) v})
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (sExactMap n.unop.len (presentedPerfectDGExactMap A F)).hom) := by
  change eHomEquiv SSet.{max (u + 1) v} F ≫
    ((quasicategoryEnrichedCoreFunctor
      ((presentedPerfectDGSimplicialEnrichedFunctor A).obj n)).map C D ≫ 𝟙 _) = _
  rw [Category.comp_id]
  exact quasicategoryEnrichedCoreFunctor_hom _ F _
    (presentedPerfectDGSimplicialEnrichedFunctor_hom A n F)

end SerrePositivity.KST.SConstruction
