module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.RelativeHornFaces

/-! 次数別全射な鎖写像に沿う相対ホーンの線形持ち上げ。準同型性は要求しない。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D E : Type v}
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] {x y : D} {x' y' : E}

lemma dgGluingRelativeHorn_linear_lift
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject R D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R E x' y')
    (hs : ∀ k : ℤ, Function.Surjective (φ.f k)) {n : ℕ} {i : Fin (n + 2)}
    (b : (Λ[n + 1, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D x y)
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R E x' y') _⦋n + 1⦌)
    (hb : b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap φ = Λ[n + 1, i].ι ≫ SSet.yonedaEquiv.symm t) :
    ∃ s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x y (n + 1),
      (∀ j (hji : j ≠ i), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback j.succAboveOrderEmb.toOrderHom s.val =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.faceData b j hji) ∧ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap φ s = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex t := by
  let q : ∀ k : ℤ, k = 1 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ) →
      GradedHom R x y k := fun k hk =>
    Classical.choose (hs k ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex t).val.component Finset.univ k
      Finset.univ_nonempty hk))
  let s := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHornTopSimplex b q
  have hf : ∀ j (hji : j ≠ i), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback j.succAboveOrderEmb.toOrderHom s.val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.faceData b j hji := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHornTopData_face b q
  refine ⟨s, hf, ?_⟩
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHornSimplex_ext i
  · intro k hk
    change φ.f k ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHornTopData b q).component Finset.univ k
      Finset.univ_nonempty hk) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHornTopData_top]
    exact Classical.choose_spec (hs k ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex t).val.component Finset.univ k
      Finset.univ_nonempty hk))
  · apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHornData_component_eq_of_faces i
    intro j hji
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback j.succAboveOrderEmb.toOrderHom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearDataMap φ s.val) = _
    rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearDataMap_pullback, hf j hji]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRelativeHorn_face_map φ b t hb j hji

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
