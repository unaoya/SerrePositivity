module
public import SerrePositivity.KST.SConstruction.SExactQuasicategoryDiagram
public import SerrePositivity.KST.SConstruction.QuasicategoryEnrichedDiagramPrecomposition
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGFullEnrichedFunctor

/-! # 元の全厳密 dg 入力族に自然な実 S• Perf 図式
概要：元の S• と面退化を、全 native Kan 入力に関して自然な単体的豊穣図式にする。
方針：完全な豊穣 Perf の同じ全 Hom で前合成し、元の各段と添字制限を回収する。
規約：各段だけの関手性に弱めない。使われ方：反復 S•・core・実現の入力。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の全 native Kan dg 入力族を保持する、全高次比較に自然な実 S• Perf 図式。 -/
def presentedPerfectDGSimplicialEnrichedFunctor :
    SimplicialObject (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedFunctorCategory (PerfDGInput.{u, v} A)) :=
  sExactSimplicialEnrichedFunctor ⋙
    quasicategoryEnrichedPrecompositionFunctor (presentedPerfectDGFullEnrichedFunctor A)

/-- 一つの元の dg 圏で評価した、同じ実 S• Perf の単体的図式。 -/
def presentedPerfectDGSimplicialDiagram (C : PerfDGInput.{u, v} A) :
    SimplicialObject _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{max (u + 1) v} :=
  presentedPerfectDGSimplicialEnrichedFunctor A ⋙ quasicategoryEnrichedEvaluationFunctor C

/-- 元の評価図式の各段は、同じラベル付き Perf の全 gapped S_n。 -/
lemma presentedPerfectDGSimplicialDiagram_obj (C : PerfDGInput.{u, v} A)
    (n : SimplexCategoryᵒᵖ) :
    ((presentedPerfectDGSimplicialDiagram A C).obj n).obj =
      sConstruction n.unop.len (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A C)) := rfl

/-- 元の評価図式の全ての面退化は、同じ元の実 S_n 添字制限。 -/
lemma presentedPerfectDGSimplicialDiagram_map (C : PerfDGInput.{u, v} A)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    (presentedPerfectDGSimplicialDiagram A C).map f =
      sMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A C)) f.unop.toOrderHom := rfl

/-- 各段の全 Hom 作用は、元の全完全 Perf 関手族と元の全パラメータ S_n の合成。 -/
lemma presentedPerfectDGSimplicialEnrichedFunctor_map (n : SimplexCategoryᵒᵖ)
    (C D : PerfDGInput.{u, v} A) :
    ((presentedPerfectDGSimplicialEnrichedFunctor A).obj n).map C D =
      (presentedPerfectDGFullEnrichedFunctor A).map C D ≫
        sExactFamilyMap n.unop.len
          (presentedPerfectDGStableCategory A C) (presentedPerfectDGStableCategory A D) := rfl

/-- 元の通常 dg 入力射では、同じ cofiber 型 S_n Perf 射の curry を回収する。 -/
lemma presentedPerfectDGSimplicialEnrichedFunctor_hom (n : SimplexCategoryᵒᵖ)
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    eHomEquiv SSet.{max (u + 1) v} F ≫
      ((presentedPerfectDGSimplicialEnrichedFunctor A).obj n).map C D =
        curry' (C := SSet.{max (u + 1) v}) (sExactMap n.unop.len
          (presentedPerfectDGExactMap A F)).hom := by
  change eHomEquiv SSet.{max (u + 1) v} F ≫
    ((presentedPerfectDGFullEnrichedFunctor A).map C D ≫ sExactFamilyMap n.unop.len
      (presentedPerfectDGStableCategory A C) (presentedPerfectDGStableCategory A D)) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ sExactFamilyMap n.unop.len
      (presentedPerfectDGStableCategory A C) (presentedPerfectDGStableCategory A D))
        (presentedPerfectDGFullEnrichedFunctor_hom A F)).trans
          (sExactFamilyMap_fixed n.unop.len (presentedPerfectDGExactMap A F)))

end SerrePositivity.KST.SConstruction
