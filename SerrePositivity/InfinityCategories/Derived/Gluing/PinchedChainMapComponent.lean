module
public import SerrePositivity.InfinityCategories.Derived.PinchedHomChainMap

/-! 実 Hom 鎖写像の全 pinched 作用の係数を、同じ鎖写像の次数成分で回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable {R : Type u} [CommRing R] {C D : Type v} [DGCategory R C] [DGCategory R D]
  {x y : C} {x' y' : D}

lemma dgGluingPinchedChainMapSimplex_component
    (φ : homObject R C x y ⟶ homObject R D x' y') {n : ℕ}
    (s : (DGNerve.pinchedHom R C x y) _⦋n⦌)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (toLinearData (pinchedHomChainMapSimplex φ s)).component J k hJ hk =
      φ.f k ((toLinearData s).component J k hJ hk) := by
  exact congrArg (fun t : LinearSimplex R x' y' n => t.val.component J k hJ hk)
    (pinchedHomChainMapSimplex_linear φ s)

end SerrePositivity.InfinityCategories
