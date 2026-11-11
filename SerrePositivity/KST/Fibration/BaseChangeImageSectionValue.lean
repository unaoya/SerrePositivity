module
public import SerrePositivity.KST.Fibration.ScaffoldBaseChangeLeftPoint

/-! # 像の単体への切断点の等式輸送は、元の E 値の切断を保つ -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

private lemma sectionPoint_eq_mp_val {A E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] {a b : A ⟶ B} (hab : a = b)
    (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation (Over.mk a)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf p) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation (Over.mk b)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf p))
    {n : SimplexCategoryᵒᵖ} (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a).obj n) :
    (Eq.mp (congrArg (fun T : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} => T.obj.obj n) h) v).val = v.val := by
  subst b
  have hh : h = rfl := Subsingleton.elim _ _
  rw [hh]
  rfl

variable {E B D : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [Quasicategory B]
  (k : D ⟶ B)

omit [Quasicategory B] in
/-- 像の単体へ輸送した切断点の underlying E 値の族は、元の族と厳密に同じ。 -/
theorem straighteningBaseChangeImageSectionPoint_val (c : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory D)
    (v : (((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor D ⋙ Over.map k)).obj c).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf p)).obj _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.straighteningBaseChangeImageSectionPoint p k c v).val = v.val := by
  exact sectionPoint_eq_mp_val p
    (SSet.yonedaEquiv_symm_comp c.objDown.val k)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening.straighteningBaseChangeLeft_section_eq k (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf p) c) v

end SerrePositivity.KST.Fibration
