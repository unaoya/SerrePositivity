module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.PinchedPullbackSimplex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedChainMapComposition

/-! 線形持ち上げを実際の pinched 単体へ戻し、全次数の存在と共同単射性を得る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D₀ D₁ D₂ D₃ : Type v}
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D₀] [_root_.SerrePositivity.DifferentialGraded.DGCategory R D₁] [_root_.SerrePositivity.DifferentialGraded.DGCategory R D₂] [_root_.SerrePositivity.DifferentialGraded.DGCategory R D₃]
  {x₀ y₀ : D₀} {x₁ y₁ : D₁} {x₂ y₂ : D₂} {x₃ y₃ : D₃}
  {a : _root_.SerrePositivity.DifferentialGraded.homObject R D₀ x₀ y₀ ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R D₁ x₁ y₁}
  {b : _root_.SerrePositivity.DifferentialGraded.homObject R D₀ x₀ y₀ ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R D₂ x₂ y₂}
  {f : _root_.SerrePositivity.DifferentialGraded.homObject R D₁ x₁ y₁ ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R D₃ x₃ y₃}
  {g : _root_.SerrePositivity.DifferentialGraded.homObject R D₂ x₂ y₂ ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R D₃ x₃ y₃}

lemma dgGluingPinchedPullbackElement_ext (h : IsPullback a b f g) (n : SimplexCategoryᵒᵖ)
    (s t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D₀ x₀ y₀).obj n)
    (ha : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap a).app n s = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap a).app n t)
    (hb : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap b).app n s = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap b).app n t) : s = t := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv x₀ y₀ n.unop.len).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex s = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex t
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex a s = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex a t at ha
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex b s = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex b t at hb
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedPullbackSimplex_ext h
  · have hh := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (A := R) (x := x₁) (y := y₁)) ha
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex_linear] using hh
  · have hh := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (A := R) (x := x₂) (y := y₂)) hb
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex_linear] using hh

lemma dgGluingPinchedPullbackElement_exists (h : IsPullback a b f g) (n : SimplexCategoryᵒᵖ)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D₁ x₁ y₁).obj n)
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D₂ x₂ y₂).obj n)
    (he : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap f).app n s = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap g).app n t) :
    ∃ z : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D₀ x₀ y₀).obj n,
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap a).app n z = s ∧ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap b).app n z = t := by
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex f s = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex g t at he
  have e : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex s) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap g (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex t) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex_linear] using
      congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (A := R) (x := x₃) (y := y₃)) he
  refine ⟨(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedPullbackSimplex h (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex s) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex t) e).toPinched,
    ?_, ?_⟩
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv x₁ y₁ n.unop.len).injective
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex a _) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex s
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex_linear, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedPullbackSimplex_fst h _ _ e
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv x₂ y₂ n.unop.len).injective
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex b _) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex t
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex_linear, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedPullbackSimplex_snd h _ _ e

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
