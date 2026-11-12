module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HornPrescribedTopSimplex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HornSimplexExt
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedChainMapComposition

/-! 相対ホーンの可換条件を、利用可能な全ての線形面へ移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D E : Type v}
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] {x y : D} {x' y' : E}

lemma dgGluingRelativeHorn_face_map
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject R D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R E x' y') {n : ℕ} {i : Fin (n + 2)}
    (b : (Λ[n + 1, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D x y)
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R E x' y') _⦋n + 1⦌)
    (hb : b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap φ = Λ[n + 1, i].ι ≫ SSet.yonedaEquiv.symm t)
    (j : Fin (n + 2)) (hji : j ≠ i) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearDataMap φ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.faceData b j hji) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback j.succAboveOrderEmb.toOrderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex t).val := by
  have he := congrArg (fun f => f.app _ (SSet.horn.face i j hji)) hb
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex φ (b.app _ (SSet.horn.face i j hji)) =
    t.pullback (SimplexCategory.δ j) at he
  have hh := congrArg (fun s => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex s).val) he
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex_linear, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_pullback] at hh
  exact hh

lemma dgGluingHornTopSimplex_face {n : ℕ} {i : Fin (n + 2)}
    (b : (Λ[n + 1, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D x y)
    (q : ∀ k : ℤ, k = 1 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ) →
      _root_.SerrePositivity.DifferentialGraded.GradedHom R x y k) (j : Fin (n + 2)) (hji : j ≠ i) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D x y).δ j (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHornTopSimplex b q).toPinched =
      b.app _ (SSet.horn.face i j hji) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv x y n).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHornTopSimplex b q).toPinched.pullback
    (SimplexCategory.δ j)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_pullback, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched]
  exact Subtype.ext (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHornTopData_face b q j hji)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
