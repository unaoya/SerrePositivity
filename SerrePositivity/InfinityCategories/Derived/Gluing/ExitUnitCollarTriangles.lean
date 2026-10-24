module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaProjectionIntervalFamilies
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizationAugmentationCoherence
/-! # 標準終側合成面の元終辺固定補正

概要：同じ四面体の標準終側合成面を補正し、元 Hom の第二三角形を回収する。
方針：元 Hom と標準終閉射の三角形へ augmentation を適用し、終側単位再添字を使う。
規約：元入力・元終辺・元端を保持し、正規化済み入力へ置き換えない。
使われ方：高次貼り合わせの終側を、選択済み第二変形へ相対比較する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type (max u v)) [DGCategory R E]
  (X Y : DGFunctorCommaObject R E E (DGFunctor.id E))
  {K : SSet.{max u v}} (f : K ⟶ DGNerve.pinchedHom R
    (DGFunctorCommaObject R E E (DGFunctor.id E)) X Y)
local notation "Q" => DGFunctorCommaObject R E E (DGFunctor.id E)
def dgGluingExitAugmentationTriangle :=
  (Δ[1] ◁ dgGluingNormalizationExitTriangle R E X Y f) ≫
    dgGluingCommaAugmentationPrism R E E (DGFunctor.id E)
lemma dgGluingExitAugmentationTriangle_side :
    (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ K)) ≫
        dgGluingExitAugmentationTriangle R E X Y f =
      (Δ[1] ◁ intervalMappingUncurry ((SSet.const (X := K)
        (pinchedClosedVertex R Q (dgGluingIdentityCommaNormalizationClosedOut R E Y))) ≫
          pinchedHomToIntervalMappingSpace (X := dgNerve R Q)
            (Simplex.vertex Y) (Simplex.vertex (dgGluingIdentityCommaObject R E Y.source)))) ≫
              dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) := by
  rw [dgGluingExitAugmentationTriangle, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingNormalizationExitTriangle, dgGluingDGCompositionTriangleFamily_zero]
def dgGluingExitUnitCollarTriangleFamily : (Δ[2] : SSet.{max u v}) ⊗ (K ⊗ Δ[1]) ⟶ dgNerve R E :=
  dgGluingTriangleTimeReindex dgGluingLastUnitCollar ≫
    dgGluingExitAugmentationTriangle R E X Y f ≫
      dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)
lemma dgGluingExitUnitCollarSide :
    (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ K)) ≫
      (dgGluingExitAugmentationTriangle R E X Y f ≫
        dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)) =
    (Δ[1] ◁ fst (Δ[1] : SSet.{max u v}) K) ≫ dgGluingSquareUnitCollapse 1 ≫
      SSet.yonedaEquiv.symm (dgClosedEdge R E Y.augmentation).edge := by
  rw [← Category.assoc, dgGluingExitAugmentationTriangle_side,
    Category.assoc, dgGluingClosedAugmentationSquare_constant_family,
    dgGluingNormalizationOutAugmentationSquare_eq]
lemma dgGluingExitUnitCollarTriangleFamily_last :
    (stdSimplex.δ (0 : Fin 3) ▷ (K ⊗ Δ[1])) ≫ dgGluingExitUnitCollarTriangleFamily R E X Y f =
      fst (Δ[1] : SSet.{max u v}) (K ⊗ Δ[1]) ≫
        SSet.yonedaEquiv.symm (dgClosedEdge R E Y.augmentation).edge := by
  exact dgGluingLastUnitCollarFamily_last
    (dgGluingExitAugmentationTriangle R E X Y f ≫
      dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E))
    (SSet.yonedaEquiv.symm (dgClosedEdge R E Y.augmentation).edge)
    (dgGluingExitUnitCollarSide R E X Y f)
lemma dgGluingExitAugmentationTriangle_source_phase :
    prismEndpoint 0 (Δ[2] ⊗ K) ≫ dgGluingExitAugmentationTriangle R E X Y f =
      dgGluingNormalizationExitTriangle R E X Y f ≫
        dgNerve.map (dgCommaAugmentationSourceLift R E E (DGFunctor.id E)) := by
  rw [dgGluingExitAugmentationTriangle, ← Category.assoc,
    prismEndpoint_naturality, Category.assoc, dgGluingCommaAugmentationPrism_zero]
lemma dgGluingExitUnitCollarTriangleFamily_first :
    (stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ Δ[1])) ≫ dgGluingExitUnitCollarTriangleFamily R E X Y f =
      (Δ[1] ◁ fst K (Δ[1] : SSet.{max u v})) ≫
        intervalMappingUncurry (f ≫ pinchedHomToIntervalMappingSpace
          (X := dgNerve R Q) (Simplex.vertex X) (Simplex.vertex Y)) ≫
          dgNerve.map (dgCommaAugmentationSourceLift R E E (DGFunctor.id E)) ≫
            dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E) := by
  have hz : (stdSimplex.δ (2 : Fin 3) ▷ K) ≫
      dgGluingNormalizationExitTriangle R E X Y f =
      intervalMappingUncurry (f ≫ pinchedHomToIntervalMappingSpace
        (X := dgNerve R Q) (Simplex.vertex X) (Simplex.vertex Y)) := by
    rw [dgGluingNormalizationExitTriangle, dgGluingDGCompositionTriangleFamily_two]
  rw [dgGluingExitUnitCollarTriangleFamily, ← Category.assoc, dgGluingLastUnitCollarFamily_first]
  have ht := congrArg (fun g => (Δ[1] ◁ fst K (Δ[1] : SSet.{max u v})) ≫
    (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ g ≫
      dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E))
    (dgGluingExitAugmentationTriangle_source_phase R E X Y f)
  have he := congrArg (fun g => (Δ[1] ◁ fst K (Δ[1] : SSet.{max u v})) ≫ g ≫
    dgNerve.map (dgCommaAugmentationSourceLift R E E (DGFunctor.id E)) ≫
      dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)) hz
  simp only [Category.assoc] at ht he ⊢
  exact ht.trans he

def dgGluingExitReplacementIntervalFamily : K ⟶ intervalMappingSpace (X := dgNerve R E)
    (Simplex.vertex X.replacement) (Simplex.vertex Y.replacement) :=
  (f ≫ pinchedHomToIntervalMappingSpace (X := dgNerve R Q)
    (Simplex.vertex X) (Simplex.vertex Y)) ≫
      intervalMappingPostOfEq
        (dgNerve.map (dgCommaAugmentationSourceLift R E E (DGFunctor.id E)) ≫
          dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E))
        (Simplex.vertex X) (Simplex.vertex Y)
        (by apply Simplex.vertexEquiv.injective; rfl)
        (by apply Simplex.vertexEquiv.injective; rfl)
lemma dgGluingExitUnitCollarTriangleFamily_first_input :
    (stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ Δ[1])) ≫ dgGluingExitUnitCollarTriangleFamily R E X Y f =
      intervalMappingUncurry (fst K (Δ[1] : SSet.{max u v}) ≫
        dgGluingExitReplacementIntervalFamily R E X Y f) := by
  rw [intervalMappingUncurry_precomp, dgGluingExitReplacementIntervalFamily,
    intervalMappingPostOfEq_uncurry]
  exact dgGluingExitUnitCollarTriangleFamily_first R E X Y f


lemma dgGluingExitReplacementIntervalFamily_eq : dgGluingExitReplacementIntervalFamily R E X Y f =
    dgGluingIdentityCommaReplacementIntervalFamily R E X Y f := by
  apply intervalMappingUncurry_injective
  rw [dgGluingExitReplacementIntervalFamily, intervalMappingPostOfEq_uncurry, ← dgNerve.map_comp,
    dgGluingIdentityCommaSourceLift_down, dgGluingIdentityCommaReplacementIntervalFamily]
  exact (dgGluingFunctorPinchedIntervalImage
    (dgFunctorCommaReplacement R E E (DGFunctor.id E)) (f := f)).symm
lemma dgGluingExitAugmentationTriangle_original :
    (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ K)) ≫
      dgGluingExitAugmentationTriangle R E X Y f =
    (Δ[1] ◁ intervalMappingUncurry (f ≫ pinchedHomToIntervalMappingSpace
      (X := dgNerve R Q) (Simplex.vertex X) (Simplex.vertex Y))) ≫
        dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) := by
  rw [dgGluingExitAugmentationTriangle, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingNormalizationExitTriangle, dgGluingDGCompositionTriangleFamily_two]
lemma dgGluingExitUnitCollarTriangleFamily_zero :
    (Δ[2] ◁ (ι₀ : K ⟶ _)) ≫ dgGluingExitUnitCollarTriangleFamily R E X Y f =
    (squareTriangle 0 ▷ K) ≫ (α_ (Δ[1] : SSet.{max u v}) Δ[1] K).hom ≫
      (Δ[1] ◁ intervalMappingUncurry (f ≫ pinchedHomToIntervalMappingSpace
        (X := dgNerve R Q) (Simplex.vertex X) (Simplex.vertex Y))) ≫
        dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) ≫
          dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E) := by
  calc
    _ = (squareTriangle 0 ▷ K) ≫ (α_ (Δ[1] : SSet.{max u v}) Δ[1] K).hom ≫
        ((Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ K)) ≫
          dgGluingExitAugmentationTriangle R E X Y f) ≫
            dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E) := by
      rw [dgGluingExitUnitCollarTriangleFamily, ← Category.assoc, dgGluingLastUnitCollarFamily_zero]
      simp only [Category.assoc]
    _ = _ := by
      rw [dgGluingExitAugmentationTriangle_original]
      simp only [Category.assoc]
lemma dgGluingExitAugmentationTriangle_tetrahedron :
    (Δ[1] ◁ (stdSimplex.δ (0 : Fin 4) ▷ K)) ≫
      dgGluingNormalizationAugmentationTetrahedron R E X Y f =
      dgGluingExitAugmentationTriangle R E X Y f :=
  dgGluingNormalizationAugmentationTetrahedron_zero R E X Y f
lemma dgGluingExitUnitCollarTriangleFamily_first_original :
    (stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
      dgGluingExitUnitCollarTriangleFamily R E X Y f =
      intervalMappingUncurry (fst K (Δ[1] : SSet.{max u v}) ≫
        dgGluingIdentityCommaReplacementIntervalFamily R E X Y f) := by
  rw [dgGluingExitUnitCollarTriangleFamily_first_input,
    dgGluingExitReplacementIntervalFamily_eq]
end SerrePositivity.InfinityCategories
