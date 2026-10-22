module
public import SerrePositivity.InfinityCategories.Derived.Gluing.PrismSliceCube
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugNervePrism

/-! 元 comma augmentation を実 slice 合成三角形へ適用した三次元族と、その全境界。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
local notation "Q" => DGFunctorCommaObject R C E F

def dgGluingCommaAugmentationPrism :
    (Δ[1] : SSet.{max u v w}) ⊗ dgNerve R Q ⟶
      dgNerve R (DGUniverseLift.{w, max u v} E) :=
  (β_ (Δ[1] : SSet.{max u v w}) (dgNerve R Q)).hom ≫
    (dgCommaAugmentationNerveHomotopy R C E F).h

lemma dgGluingCommaAugmentationPrism_zero :
    prismEndpoint 0 _ ≫ dgGluingCommaAugmentationPrism R C E F =
      dgNerve.map (dgCommaAugmentationSourceLift R C E F) := by
  have hi : prismEndpoint 0 (dgNerve R Q) ≫
      (β_ (Δ[1] : SSet.{max u v w}) (dgNerve R Q)).hom = SSet.ι₀ := rfl
  rw [dgGluingCommaAugmentationPrism, ← Category.assoc, hi,
    (dgCommaAugmentationNerveHomotopy R C E F).h₀]

lemma dgGluingCommaAugmentationPrism_one :
    prismEndpoint 1 _ ≫ dgGluingCommaAugmentationPrism R C E F =
      dgNerve.map (dgCommaAugmentationTargetLift R C E F) := by
  have hi : prismEndpoint 1 (dgNerve R Q) ≫
      (β_ (Δ[1] : SSet.{max u v w}) (dgNerve R Q)).hom = SSet.ι₁ := rfl
  rw [dgGluingCommaAugmentationPrism, ← Category.assoc, hi,
    (dgCommaAugmentationNerveHomotopy R C E F).h₁]

variable (Y : DGFunctorCommaObject R C E F) {P : SSet.{max u v w}}
  (W : (Δ[1] : SSet.{max u v w}) ⊗ P ⟶
    sliceOver ((SSet.yonedaEquiv (X := dgNerve R (DGFunctorCommaObject R C E F))).symm
      (Simplex.vertex Y)))

def dgGluingCommaAugmentationSliceCube :=
  dgGluingPrismSliceCube (dgGluingCommaAugmentationPrism R C E F) (Simplex.vertex Y) W

lemma dgGluingCommaAugmentationSliceCube_zero :
    prismEndpoint 0 _ ≫ dgGluingCommaAugmentationSliceCube R C E F Y W =
      slicePrismSquare (Simplex.vertex Y) W ≫
        dgNerve.map (dgCommaAugmentationSourceLift R C E F) :=
  dgGluingPrismSliceCube_outer_face _ _ _ 0 (dgGluingCommaAugmentationPrism_zero R C E F)

lemma dgGluingCommaAugmentationSliceCube_one :
    prismEndpoint 1 _ ≫ dgGluingCommaAugmentationSliceCube R C E F Y W =
      slicePrismSquare (Simplex.vertex Y) W ≫
        dgNerve.map (dgCommaAugmentationTargetLift R C E F) :=
  dgGluingPrismSliceCube_outer_face _ _ _ 1 (dgGluingCommaAugmentationPrism_one R C E F)

lemma dgGluingCommaAugmentationSliceCube_source :
    (Δ[1] ◁ prismEndpoint 0 _) ≫ dgGluingCommaAugmentationSliceCube R C E F Y W =
      (Δ[1] ◁ (W ≫ sliceOverProjection _)) ≫ dgGluingCommaAugmentationPrism R C E F :=
  dgGluingPrismSliceCube_middle_zero _ _ _

lemma dgGluingCommaAugmentationSliceCube_target :
    (Δ[1] ◁ prismEndpoint 1 _) ≫ dgGluingCommaAugmentationSliceCube R C E F Y W =
      (Δ[1] ◁ SSet.const (X := Δ[1] ⊗ P) (Simplex.vertex Y)) ≫
        dgGluingCommaAugmentationPrism R C E F :=
  dgGluingPrismSliceCube_middle_one _ _ _

lemma dgGluingCommaAugmentationSliceCube_inner (i : Fin 2) :
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint i P)) ≫
        dgGluingCommaAugmentationSliceCube R C E F Y W =
      (Δ[1] ◁ (rightMappingSpacePrism P ≫ sliceOverUncurry (prismEndpoint i P ≫ W))) ≫
        dgGluingCommaAugmentationPrism R C E F :=
  dgGluingPrismSliceCube_inner _ _ _ i

end SerrePositivity.InfinityCategories
