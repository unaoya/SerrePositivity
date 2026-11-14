module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.PinchedPullbackData

/-! 引き戻した全成分は、同じ線形微分方程式を満たす単体を一意に定める。 -/
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
  {g : _root_.SerrePositivity.DifferentialGraded.homObject R D₂ x₂ y₂ ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R D₃ x₃ y₃} {n : ℕ}

lemma dgGluingPinchedData_equation_image (z : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x₀ y₀ n)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x₁ y₁ n) (hz : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearDataMap a z = s.val)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    a.f (k + 1) ((_root_.SerrePositivity.DifferentialGraded.homObject R D₀ x₀ y₀).d k (k + 1) (z.component J k hJ hk)) =
      a.f (k + 1) (z.rhs J k hk) := by
  have hc := (ConcreteCategory.congr_hom (a.comm k (k + 1)) (z.component J k hJ hk)).symm
  change a.f (k + 1) ((_root_.SerrePositivity.DifferentialGraded.homObject R D₀ x₀ y₀).d k (k + 1) (z.component J k hJ hk)) =
    (_root_.SerrePositivity.DifferentialGraded.homObject R D₁ x₁ y₁).d k (k + 1)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearDataMap a z).component J k hJ hk) at hc
  rw [hc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearDataMap_rhs]
  rw [hz]
  exact s.equation J k hJ hk

lemma dgGluingPinchedPullbackData_equation (h : IsPullback a b f g)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x₁ y₁ n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x₂ y₂ n)
    (e : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap f s = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap g t)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (_root_.SerrePositivity.DifferentialGraded.homObject R D₀ x₀ y₀).d k (k + 1)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedPullbackData h s t e).component J k hJ hk) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedPullbackData h s t e).rhs J k hk := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPullback_ext h (k + 1)
  · exact dgGluingPinchedData_equation_image _ s
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedPullbackData_fst h s t e) J k hJ hk
  · exact dgGluingPinchedData_equation_image _ t
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedPullbackData_snd h s t e) J k hJ hk

def dgGluingPinchedPullbackSimplex (h : IsPullback a b f g)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x₁ y₁ n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x₂ y₂ n)
    (e : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap f s = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap g t) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x₀ y₀ n :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedPullbackData h s t e,
    dgGluingPinchedPullbackData_equation h s t e⟩

lemma dgGluingPinchedPullbackSimplex_fst (h : IsPullback a b f g)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x₁ y₁ n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x₂ y₂ n)
    (e : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap f s = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap g t) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap a (dgGluingPinchedPullbackSimplex h s t e) = s :=
  Subtype.ext (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedPullbackData_fst h s t e)

lemma dgGluingPinchedPullbackSimplex_snd (h : IsPullback a b f g)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x₁ y₁ n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x₂ y₂ n)
    (e : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap f s = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap g t) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap b (dgGluingPinchedPullbackSimplex h s t e) = t :=
  Subtype.ext (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedPullbackData_snd h s t e)

lemma dgGluingPinchedPullbackSimplex_ext (h : IsPullback a b f g)
    (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x₀ y₀ n)
    (ha : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap a s = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap a t)
    (hb : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap b s = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap b t) : s = t := by
  apply Subtype.ext
  funext i
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPullback_ext h i.val.2
  · exact congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x₁ y₁ n => z.val i) ha
  · exact congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x₂ y₂ n => z.val i) hb

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
