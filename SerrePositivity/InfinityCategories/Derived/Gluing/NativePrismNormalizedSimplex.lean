module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativePrismNormalizedLinearData

/-! 元 prism の正規化係数を実 pinched 単体へ再構成し、同じ明示 cochain 族の単体と厳密照合。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  {X Y : DGGluingObject R C D M} {n : ℕ}
  (s : (DGNerve.pinchedHom R (DGGluingObject R C D M) X Y) _⦋n⦌)

def dgGluingNativePrismNormalizedLinearSimplex (β : (Δ[1] : SSet.{max u v w}) _⦋n⦌) :
    LinearSimplex (D := DGComplexPinchedModel.{u, max u v w} (M.value X.left Y.right)) R
      (complexPinchedSource _) (complexPinchedTarget _) n :=
  ⟨dgGluingNativePrismNormalizedLinearData R C D M s (SSet.stdSimplex.objEquiv β).toOrderHom, by
    rw [dgGluingNativePrismNormalizedLinearData_eq]
    exact (toLinearSimplex ((dgGluingHomCoefficientAugmentationPrism R C D M X Y).app
      (Opposite.op ⦋n⦌) (β, (pinchedComplexModelIso X Y).hom.app (Opposite.op ⦋n⦌) s))).property⟩

def dgGluingNativePrismNormalizedSimplex (β : (Δ[1] : SSet.{max u v w}) _⦋n⦌) :
    (complexPinchedSpace.{u, max u v w} (M.value X.left Y.right)) _⦋n⦌ :=
  (dgGluingNativePrismNormalizedLinearSimplex R C D M s β).toPinched

lemma dgGluingNativePrismNormalizedSimplex_eq (β : (Δ[1] : SSet.{max u v w}) _⦋n⦌) :
    dgGluingNativePrismNormalizedSimplex R C D M s β =
      (dgGluingHomCoefficientAugmentationPrism R C D M X Y).app (Opposite.op ⦋n⦌)
        (β, (pinchedComplexModelIso X Y).hom.app (Opposite.op ⦋n⦌) s) := by
  apply (linearEquiv (complexPinchedSource (M.value X.left Y.right))
    (complexPinchedTarget _) n).injective
  change toLinearSimplex (dgGluingNativePrismNormalizedSimplex R C D M s β) = _
  rw [dgGluingNativePrismNormalizedSimplex, LinearSimplex.toLinearSimplex_toPinched]
  apply Subtype.ext
  exact dgGluingNativePrismNormalizedLinearData_eq R C D M s β

end SerrePositivity.InfinityCategories
