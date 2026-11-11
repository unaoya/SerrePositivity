module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedHomChainMap

/-! 実 Hom 鎖写像の全 pinched 作用の係数を、同じ鎖写像の次数成分で回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {C D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
  {x y : C} {x' y' : D}

lemma dgGluingPinchedChainMapSimplex_component
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject R C x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R D x' y') {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R C x y) _⦋n⦌)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex φ s)).component J k hJ hk =
      φ.f k ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component J k hJ hk) := by
  exact congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x' y' n => t.val.component J k hJ hk)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex_linear φ s)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
