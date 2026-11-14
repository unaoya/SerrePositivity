module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceCalculus
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.KanFibrationTools

/-! 指定された trivial Kan 射影の実切断は、底が Kan なら同じ実ホモトピー同値。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
variable {E B : SSet.{u}} (p : E ⟶ B) [hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p]

include p hp in
lemma dgGluingTrivialKanProjection_kanComplex [KanComplex B] : KanComplex E := by
  let : Fibration p := (SSet.modelCategoryQuillen.fibration_iff _).2 (by
    intro K L i hi
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := p) i (J_le_monomorphisms i hi))
  exact isFibrant_of_fibration p

include hp in
lemma dgGluingTrivialKanSection_equivalence [KanComplex B] (s : B ⟶ E)
    (hs : s ≫ p = 𝟙 B) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence s := by
  let : KanComplex E := dgGluingTrivialKanProjection_kanComplex p
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration p
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence.isSimplicialHomotopyEquivalence
  apply he.cancel_right
  rw [hs]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isSimplicialHomotopyEquivalence_id B).isQCatEquivalence

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
