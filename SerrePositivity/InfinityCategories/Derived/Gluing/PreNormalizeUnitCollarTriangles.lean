module
public import SerrePositivity.InfinityCategories.Derived.Gluing.FirstUnitCollarFamilies
/-! # 元の始辺と Hom 入力を保つ実前正規化族

概要：標準側面を貼った前正規化を、元 augmentation と元第二入力を保つ三角形族へ移す。
方針：実 augmentation prism の側面を単位正方形へ同定し、始側補正の再添字を適用する。
規約：元端の三角形と全パラメーターを回収し、Small 仮定を課さない。
使われ方：正本第一三角形からの実入力固定変形を構成する。
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
def dgGluingPreNormalizeUnitCollarTriangleFamily :
    (Δ[2] : SSet.{max u v}) ⊗ (K ⊗ Δ[1]) ⟶ dgNerve R E :=
  dgGluingTriangleTimeReindex dgGluingFirstUnitCollar ≫
    dgGluingPreNormalizeAugmentationTriangle R E X Y f ≫
      dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)
lemma dgGluingPreNormalizeUnitCollarSide :
    (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ K)) ≫
      (dgGluingPreNormalizeAugmentationTriangle R E X Y f ≫
        dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)) =
    (Δ[1] ◁ fst (Δ[1] : SSet.{max u v}) K) ≫ dgGluingSquareUnitCollapse 0 ≫
      SSet.yonedaEquiv.symm (dgClosedEdge R E X.augmentation).edge := by
  rw [← Category.assoc, dgGluingPreNormalizeAugmentationTriangle_side,
    Category.assoc, dgGluingClosedAugmentationSquare_constant_family,
    dgGluingNormalizationInAugmentationSquare_eq]
lemma dgGluingPreNormalizeUnitCollarTriangleFamily_first :
    (stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
      dgGluingPreNormalizeUnitCollarTriangleFamily R E X Y f =
      fst (Δ[1] : SSet.{max u v}) (K ⊗ Δ[1]) ≫
        SSet.yonedaEquiv.symm (dgClosedEdge R E X.augmentation).edge := by
  exact dgGluingFirstUnitCollarFamily_first
    (dgGluingPreNormalizeAugmentationTriangle R E X Y f ≫
      dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E))
    (SSet.yonedaEquiv.symm (dgClosedEdge R E X.augmentation).edge)
    (dgGluingPreNormalizeUnitCollarSide R E X Y f)


lemma dgGluingPreNormalizeAugmentationTriangle_target_phase :
    prismEndpoint 1 (Δ[2] ⊗ K) ≫ dgGluingPreNormalizeAugmentationTriangle R E X Y f =
      dgGluingSlicePrismTriangle (dgGluingIdentityCommaPreNormalizePrism R E X Y f) ≫
        dgNerve.map (dgCommaAugmentationTargetLift R E E (DGFunctor.id E)) := by
  rw [dgGluingPreNormalizeAugmentationTriangle, ← Category.assoc,
    prismEndpoint_naturality, Category.assoc, dgGluingCommaAugmentationPrism_one]
lemma dgGluingPreNormalizeUnitCollarTriangleFamily_last :
    (stdSimplex.δ (0 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
      dgGluingPreNormalizeUnitCollarTriangleFamily R E X Y f =
      (Δ[1] ◁ fst K (Δ[1] : SSet.{max u v})) ≫
        intervalMappingUncurry (f ≫ pinchedHomToIntervalMappingSpace
          (X := dgNerve R Q) (Simplex.vertex X) (Simplex.vertex Y)) ≫
          dgNerve.map (dgCommaAugmentationTargetLift R E E (DGFunctor.id E)) ≫
            dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E) := by
  have hz : (stdSimplex.δ (0 : Fin 3) ▷ K) ≫
      dgGluingSlicePrismTriangle (dgGluingIdentityCommaPreNormalizePrism R E X Y f) =
      intervalMappingUncurry (f ≫ pinchedHomToIntervalMappingSpace
        (X := dgNerve R Q) (Simplex.vertex X) (Simplex.vertex Y)) := by
    rw [dgGluingSlicePrismTriangle_zero, dgGluingIdentityCommaPreNormalizePrism_one,
      dgGluingPinchedSliceEvaluation]
  rw [dgGluingPreNormalizeUnitCollarTriangleFamily, ← Category.assoc,
    dgGluingFirstUnitCollarFamily_last]
  have ht := congrArg (fun g => (Δ[1] ◁ fst K (Δ[1] : SSet.{max u v})) ≫
    (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ g ≫
      dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E))
    (dgGluingPreNormalizeAugmentationTriangle_target_phase R E X Y f)
  have he := congrArg (fun g => (Δ[1] ◁ fst K (Δ[1] : SSet.{max u v})) ≫ g ≫
    dgNerve.map (dgCommaAugmentationTargetLift R E E (DGFunctor.id E)) ≫
      dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)) hz
  simp only [Category.assoc] at ht he ⊢
  exact ht.trans he

lemma dgGluingPreNormalizeUnitCollarTriangleFamily_one :
    (Δ[2] ◁ (ι₁ : K ⟶ _)) ≫
      dgGluingPreNormalizeUnitCollarTriangleFamily R E X Y f =
      (squareTriangle 1 ▷ K) ≫ (α_ (Δ[1] : SSet.{max u v}) Δ[1] K).hom ≫
        (Δ[1] ◁ intervalMappingUncurry (f ≫ pinchedHomToIntervalMappingSpace
          (X := dgNerve R Q) (Simplex.vertex X) (Simplex.vertex Y))) ≫
          dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) ≫
            dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E) := by
  calc
    _ = (squareTriangle 1 ▷ K) ≫ (α_ (Δ[1] : SSet.{max u v}) Δ[1] K).hom ≫
        ((Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ K)) ≫
          dgGluingPreNormalizeAugmentationTriangle R E X Y f) ≫
            dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E) := by
      rw [dgGluingPreNormalizeUnitCollarTriangleFamily, ← Category.assoc,
        dgGluingFirstUnitCollarFamily_one]
      simp only [Category.assoc]
    _ = _ := by
      rw [dgGluingPreNormalizeAugmentationTriangle_original]
      simp only [Category.assoc]

def dgGluingIdentityCommaSourceIntervalFamily : K ⟶ intervalMappingSpace (X := dgNerve R E)
    (Simplex.vertex X.source) (Simplex.vertex Y.source) :=
  (f ≫ pinchedHomToIntervalMappingSpace (X := dgNerve R Q)
    (Simplex.vertex X) (Simplex.vertex Y)) ≫
      intervalMappingPostOfEq (dgNerve.map (dgCommaAugmentationTargetLift R E E (DGFunctor.id E)) ≫
        dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E))
          (Simplex.vertex X) (Simplex.vertex Y)
          (by apply Simplex.vertexEquiv.injective; rfl)
          (by apply Simplex.vertexEquiv.injective; rfl)
lemma dgGluingPreNormalizeUnitCollarTriangleFamily_last_input :
    (stdSimplex.δ (0 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
      dgGluingPreNormalizeUnitCollarTriangleFamily R E X Y f =
      intervalMappingUncurry (fst K (Δ[1] : SSet.{max u v}) ≫
        dgGluingIdentityCommaSourceIntervalFamily R E X Y f) := by
  rw [intervalMappingUncurry_precomp, dgGluingIdentityCommaSourceIntervalFamily,
    intervalMappingPostOfEq_uncurry]
  exact dgGluingPreNormalizeUnitCollarTriangleFamily_last R E X Y f


end SerrePositivity.InfinityCategories
