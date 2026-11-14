module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Cochains.ComplexPullbackDegrees
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedLinearChainMap

/-! 複体の引き戻しに沿い、同じ有限集合ごとの線形成分を一意に持ち上げる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits DifferentialGraded
variable {R : Type u} [CommRing R] {D₀ D₁ D₂ D₃ : Type v}
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D₀] [_root_.SerrePositivity.DifferentialGraded.DGCategory R D₁] [_root_.SerrePositivity.DifferentialGraded.DGCategory R D₂] [_root_.SerrePositivity.DifferentialGraded.DGCategory R D₃]
  {x₀ y₀ : D₀} {x₁ y₁ : D₁} {x₂ y₂ : D₂} {x₃ y₃ : D₃}
  {a : _root_.SerrePositivity.DifferentialGraded.homObject R D₀ x₀ y₀ ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R D₁ x₁ y₁}
  {b : _root_.SerrePositivity.DifferentialGraded.homObject R D₀ x₀ y₀ ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R D₂ x₂ y₂}
  {f : _root_.SerrePositivity.DifferentialGraded.homObject R D₁ x₁ y₁ ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R D₃ x₃ y₃}
  {g : _root_.SerrePositivity.DifferentialGraded.homObject R D₂ x₂ y₂ ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R D₃ x₃ y₃}
  {n : ℕ}

def dgGluingPinchedPullbackData (h : IsPullback a b f g)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x₁ y₁ n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x₂ y₂ n)
    (e : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap f s = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap g t) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x₀ y₀ n := fun i =>
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPullback_exists h i.val.2 (s.val i) (t.val i) (by
    have he := congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x₃ y₃ n => z.val i) e
    exact he))

lemma dgGluingPinchedPullbackData_fst (h : IsPullback a b f g)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x₁ y₁ n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x₂ y₂ n)
    (e : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap f s = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap g t) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearDataMap a (dgGluingPinchedPullbackData h s t e) = s.val := by
  funext i
  exact (Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPullback_exists h i.val.2 (s.val i) (t.val i)
    (congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x₃ y₃ n => z.val i) e))).1

lemma dgGluingPinchedPullbackData_snd (h : IsPullback a b f g)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x₁ y₁ n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x₂ y₂ n)
    (e : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap f s = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap g t) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearDataMap b (dgGluingPinchedPullbackData h s t e) = t.val := by
  funext i
  exact (Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPullback_exists h i.val.2 (s.val i) (t.val i)
    (congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x₃ y₃ n => z.val i) e))).2

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
