module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.NativeModels.NativePrismNormalizedLinearData

/-! 元 prism の正規化係数を実 pinched 単体へ再構成し、同じ明示 cochain 族の単体と厳密照合。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)
  {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M} {n : ℕ}
  (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) X Y) _⦋n⦌)

def dgGluingNativePrismNormalizedLinearSimplex (β : (Δ[1] : SSet.{max u v w}) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, max u v w} (M.value X.left Y.right)) R
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget _) n :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePrismNormalizedLinearData R C D M s (SSet.stdSimplex.objEquiv β).toOrderHom, by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePrismNormalizedLinearData_eq]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientAugmentationPrism R C D M X Y).app
      (Opposite.op ⦋n⦌) (β, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso X Y).hom.app (Opposite.op ⦋n⦌) s))).property⟩

def dgGluingNativePrismNormalizedSimplex (β : (Δ[1] : SSet.{max u v w}) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max u v w} (M.value X.left Y.right)) _⦋n⦌ :=
  (dgGluingNativePrismNormalizedLinearSimplex R C D M s β).toPinched

lemma dgGluingNativePrismNormalizedSimplex_eq (β : (Δ[1] : SSet.{max u v w}) _⦋n⦌) :
    dgGluingNativePrismNormalizedSimplex R C D M s β =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientAugmentationPrism R C D M X Y).app (Opposite.op ⦋n⦌)
        (β, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso X Y).hom.app (Opposite.op ⦋n⦌) s) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource (M.value X.left Y.right))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget _) n).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (dgGluingNativePrismNormalizedSimplex R C D M s β) = _
  rw [dgGluingNativePrismNormalizedSimplex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched]
  apply Subtype.ext
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePrismNormalizedLinearData_eq R C D M s β

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
