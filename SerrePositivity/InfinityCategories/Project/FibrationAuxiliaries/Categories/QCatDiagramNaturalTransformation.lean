module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QCatDiagramPrism
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatInvertible
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise

/-!
概要：対象ごとの同値である自然変換を coherent な Cat∞ 値図式間の同型へ移す。
方針：実際の prism の評価を成分の coherent 辺と照合し、点ごとの可逆性を使う。
規約：同じ自然変換の辺を使い、独立に選んだ各値の同値で代用しない。
使われ方：Cat∞ 値 weighted nerve の strict 図式の復元比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 自然変換の coherent な辺の c での評価は、元の成分の coherent な辺。 -/
lemma qCatDiagramNaturalTransformationEdge_at {C : Type u} [Category.{u} C]
    {F G : C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}} (η : F ⟶ G) (c : C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u}) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))).app _
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramNaturalTransformationEdge η).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (η.app c)).edge := by
  have hd : ((CategoryTheory.Functor.id (Fin 2)).prod'
      ((CategoryTheory.Functor.const (Fin 2)).obj c)) ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramArrow η =
        ComposableArrows.mk₁ (η.app c) := by
    refine CategoryTheory.Functor.ext (fun i => by fin_cases i <;> rfl) ?_
    intro i j f
    fin_cases i <;> fin_cases j
    all_goals first
    | have hf := leOfHom f
      exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) hf)
    | simp [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramArrow, CategoryTheory.Functor.uncurry, ComposableArrows.mk₁]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram
    ((⟨ULift.down, fun _ _ h ↦ h⟩ : ULift.{u} (Fin 2) →o Fin 2).toFunctor ⋙
      (((CategoryTheory.Functor.id (Fin 2)).prod'
        ((CategoryTheory.Functor.const (Fin 2)).obj c)) ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramArrow η)) = _
  rw [hd]
  refine EnrichedFunctor.ext SSet (fun i ↦ ?_) (fun i j ↦ ?_)
  · rcases i with ⟨⟨i⟩⟩
    fin_cases i <;> rfl
  · rcases i with ⟨⟨i⟩⟩
    rcases j with ⟨⟨j⟩⟩
    fin_cases i <;> fin_cases j
    all_goals
      simp only [eqToHom_refl, Category.comp_id]
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro P
      rfl

/-- 成分ごとに同値な自然変換の同じ coherent な辺は可逆。 -/
lemma qCatDiagramNaturalTransformationEdge_isInvertible {C : Type u} [Category.{u} C]
    {F G : C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}} (η : F ⟶ G)
    (hη : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (X := (F.obj c).obj) (Y := (G.obj c).obj) (η.app c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramNaturalTransformationEdge η) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isInvertibleEdge_iff_evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramNaturalTransformationEdge η)).mpr
  rintro ⟨s⟩
  obtain ⟨c, rfl⟩ : ∃ c : C, s = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c := ⟨s.obj 0, ComposableArrows.ext₀ rfl⟩
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (qCatDiagramNaturalTransformationEdge_at η c)).mpr
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.coherentQCatEdge_isInvertible_of_isQCatEquivalence (hη c)

/-- 対象ごとの同値である元の自然変換を、図式全体の coherent な関手同型にする。 -/
def qCatDiagramFunctorIsoOfPointwise {C : Type u} [Category.{u} C]
    {F G : C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}} (η : F ⟶ G)
    (hη : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (X := (F.obj c).obj) (Y := (G.obj c).obj) (η.app c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.qCatDiagramCoherentNerve F) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.qCatDiagramCoherentNerve G) := by
  letI : IsIso (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramNaturalTransformationEdge η)) :=
    qCatDiagramNaturalTransformationEdge_isInvertible η hη
  exact asIso (SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramNaturalTransformationEdge η))

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
