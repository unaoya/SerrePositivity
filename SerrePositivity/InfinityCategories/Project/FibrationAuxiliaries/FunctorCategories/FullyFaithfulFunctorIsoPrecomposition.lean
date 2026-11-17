module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningRepresentation
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerHom

/-! 元の指定表現同型の前合成・評価を、同じ構成の法則で照合する。 -/

@[expose] public section
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 同じ指定構成の前合成・評価の法則。 -/
lemma fullyFaithfulPreimageFunctorIso_precomp {A B X : SSet.{u}} [Quasicategory X]
    (i : A ⟶ B) (hi : IsFullyFaithful ((pre i).app X))
    {F G : B ⟶ X} (e : FunctorIso (i ≫ F) (i ≫ G)) :
    FunctorIso.precomp (f := F) (g := G)
      (hi.preimageVertexIso (x := functorVertex F) (y := functorVertex G) e) i = e := by
  apply Iso.ext
  rw [functorIso_precomp_hom]
  exact hi.toHoFullyFaithful.map_preimage
    (X := HomotopyCategory.mk (functorVertex F))
    (Y := HomotopyCategory.mk (functorVertex G)) e.hom

/-- 同じ指定構成の前合成・評価の法則。 -/
lemma fullyFaithfulPreimageFunctorIso_evaluate {A B X : SSet.{u}} [Quasicategory X]
    (i : A ⟶ B) (hi : IsFullyFaithful ((pre i).app X))
    {F G : B ⟶ X} (e : FunctorIso (i ≫ F) (i ≫ G)) (x : A _⦋0⦌) :
    functorHomEvaluate
      (hi.preimageVertexIso (x := functorVertex F) (y := functorVertex G) e).hom
      (i.app (Opposite.op ⦋0⦌) x) = functorHomEvaluate e.hom x := by
  have h := congrArg (fun z : FunctorIso (i ≫ F) (i ≫ G) =>
    functorHomEvaluate z.hom x) (fullyFaithfulPreimageFunctorIso_precomp i hi e)
  rw [functorIso_precomp_hom] at h
  have he := functorHomEvaluate_precomp
    (hi.preimageVertexIso (x := functorVertex F) (y := functorVertex G) e).hom i x
  exact he.symm.trans h

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

end
