module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativePrismNormalizedSimplex
public import SerrePositivity.InfinityCategories.Derived.Gluing.SimplicialMapOfPointwise

/-! 元 gluing prism の実正規化係数から全単体的区間族を構成し、同じ明示 cochain prism と照合。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingNativePrismNormalizedFamily (X Y : DGGluingObject R C D M) :
    (Δ[1] : SSet.{max u v w}) ⊗ DGNerve.pinchedHom R (DGGluingObject R C D M) X Y ⟶
      complexPinchedSpace.{u, max u v w} (M.value X.left Y.right) :=
  dgGluingSimplicialMapOfPointwise
    (((Δ[1] : SSet.{max u v w}) ◁ (pinchedComplexModelIso X Y).hom) ≫
      dgGluingHomCoefficientAugmentationPrism R C D M X Y)
    (fun _ z => dgGluingNativePrismNormalizedSimplex R C D M z.2 z.1)
    (by rintro ⟨⟨n⟩⟩ z; exact dgGluingNativePrismNormalizedSimplex_eq R C D M z.2 z.1)

lemma dgGluingNativePrismNormalizedFamily_comparison (X Y : DGGluingObject R C D M) :
    dgGluingNativePrismNormalizedFamily R C D M X Y =
      ((Δ[1] : SSet.{max u v w}) ◁ (pinchedComplexModelIso X Y).hom) ≫
        dgGluingHomCoefficientAugmentationPrism R C D M X Y :=
  dgGluingSimplicialMapOfPointwise_eq _ _ _

lemma dgGluingNativePrismNormalizedFamily_zero (X Y : DGGluingObject R C D M) :
    prismEndpoint 0 _ ≫ dgGluingNativePrismNormalizedFamily R C D M X Y =
      (pinchedComplexModelIso X Y).hom ≫ complexPinchedMap.{u, max u v w}
        (dgGluingLeftHomMap R C D M X Y ≫ dgGluingLeftAction R C D M X Y) := by
  rw [dgGluingNativePrismNormalizedFamily_comparison, ← Category.assoc,
    prismEndpoint_naturality, Category.assoc]
  exact congrArg (fun p => (pinchedComplexModelIso X Y).hom ≫ p)
    (dgGluingHomCoefficientAugmentationPrism_zero R C D M X Y)

lemma dgGluingNativePrismNormalizedFamily_one (X Y : DGGluingObject R C D M) :
    prismEndpoint 1 _ ≫ dgGluingNativePrismNormalizedFamily R C D M X Y =
      (pinchedComplexModelIso X Y).hom ≫ complexPinchedMap.{u, max u v w}
        (dgGluingRightHomMap R C D M X Y ≫ dgGluingRightAction R C D M X Y) := by
  rw [dgGluingNativePrismNormalizedFamily_comparison, ← Category.assoc,
    prismEndpoint_naturality, Category.assoc]
  exact congrArg (fun p => (pinchedComplexModelIso X Y).hom ≫ p)
    (dgGluingHomCoefficientAugmentationPrism_one R C D M X Y)

end SerrePositivity.InfinityCategories
