module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LastUnitCollarFamilies
/-! # 元の終辺を保つ実後正規化族

概要：後正規化の共有三角形へ終側単位補正を貼り、元 augmentation を終辺に保つ。
方針：実側面を単位正方形へ同定し、全パラメーターの終側再添字を適用する。
規約：共有端・全時間の始辺・元終辺を回収し、Small 仮定を課さない。
使われ方：元終辺の合成対応内で後側の実入力変形を構成する。
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
local notation "NX" => dgGluingIdentityCommaObject R E X.replacement
local notation "fp" => f ≫ pinchedHomChainMap (D := Q) (E := Q)
  (dgGluingIdentityCommaPreNormalizeHom R E X Y)
def dgGluingPostNormalizeUnitCollarTriangleFamily :
    (Δ[2] : SSet.{max u v}) ⊗ (K ⊗ Δ[1]) ⟶ dgNerve R E :=
  dgGluingTriangleTimeReindex dgGluingLastUnitCollar ≫
    dgGluingPostNormalizeAugmentationTriangle R E X Y f ≫
      dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)
lemma dgGluingPostNormalizeUnitCollarSide :
    (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ K)) ≫
      (dgGluingPostNormalizeAugmentationTriangle R E X Y f ≫
        dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)) =
    (Δ[1] ◁ fst (Δ[1] : SSet.{max u v}) K) ≫ dgGluingSquareUnitCollapse 1 ≫
      SSet.yonedaEquiv.symm (dgClosedEdge R E Y.augmentation).edge := by
  rw [← Category.assoc, dgGluingPostNormalizeAugmentationTriangle_side,
    Category.assoc, dgGluingClosedAugmentationSquare_constant_family,
    dgGluingNormalizationOutAugmentationSquare_eq]
lemma dgGluingPostNormalizeUnitCollarTriangleFamily_last :
    (stdSimplex.δ (0 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
      dgGluingPostNormalizeUnitCollarTriangleFamily R E X Y f =
      fst (Δ[1] : SSet.{max u v}) (K ⊗ Δ[1]) ≫
        SSet.yonedaEquiv.symm (dgClosedEdge R E Y.augmentation).edge := by
  exact dgGluingLastUnitCollarFamily_last
    (dgGluingPostNormalizeAugmentationTriangle R E X Y f ≫
      dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E))
    (SSet.yonedaEquiv.symm (dgClosedEdge R E Y.augmentation).edge)
    (dgGluingPostNormalizeUnitCollarSide R E X Y f)
lemma dgGluingPostNormalizeAugmentationTriangle_source_phase :
    prismEndpoint 0 (Δ[2] ⊗ K) ≫ dgGluingPostNormalizeAugmentationTriangle R E X Y f =
      dgGluingSlicePrismTriangle (dgGluingIdentityCommaPostNormalizePrism R E X Y f) ≫
        dgNerve.map (dgCommaAugmentationSourceLift R E E (DGFunctor.id E)) := by
  rw [dgGluingPostNormalizeAugmentationTriangle, ← Category.assoc,
    prismEndpoint_naturality, Category.assoc, dgGluingCommaAugmentationPrism_zero]
lemma dgGluingPostNormalizeUnitCollarTriangleFamily_first :
    (stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
      dgGluingPostNormalizeUnitCollarTriangleFamily R E X Y f =
      (Δ[1] ◁ fst K (Δ[1] : SSet.{max u v})) ≫
        intervalMappingUncurry (fp ≫ pinchedHomToIntervalMappingSpace
          (X := dgNerve R Q) (Simplex.vertex NX) (Simplex.vertex Y)) ≫
          dgNerve.map (dgCommaAugmentationSourceLift R E E (DGFunctor.id E)) ≫
            dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E) := by
  have hz : (stdSimplex.δ (2 : Fin 3) ▷ K) ≫
      dgGluingSlicePrismTriangle (dgGluingIdentityCommaPostNormalizePrism R E X Y f) =
      intervalMappingUncurry (fp ≫ pinchedHomToIntervalMappingSpace
        (X := dgNerve R Q) (Simplex.vertex NX) (Simplex.vertex Y)) := by
    rw [dgGluingSlicePrismTriangle_front, dgGluingIdentityCommaPostNormalizePrism_projection]
  rw [dgGluingPostNormalizeUnitCollarTriangleFamily, ← Category.assoc,
    dgGluingLastUnitCollarFamily_first]
  have ht := congrArg (fun g => (Δ[1] ◁ fst K (Δ[1] : SSet.{max u v})) ≫
    (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ g ≫
      dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E))
    (dgGluingPostNormalizeAugmentationTriangle_source_phase R E X Y f)
  have he := congrArg (fun g => (Δ[1] ◁ fst K (Δ[1] : SSet.{max u v})) ≫ g ≫
    dgNerve.map (dgCommaAugmentationSourceLift R E E (DGFunctor.id E)) ≫
      dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)) hz
  simp only [Category.assoc] at ht he ⊢
  exact ht.trans he

def dgGluingPreNormalizedReplacementIntervalFamily : K ⟶ intervalMappingSpace (X := dgNerve R E)
    (Simplex.vertex X.replacement) (Simplex.vertex Y.replacement) :=
  (fp ≫ pinchedHomToIntervalMappingSpace (X := dgNerve R Q)
    (Simplex.vertex NX) (Simplex.vertex Y)) ≫
      intervalMappingPostOfEq
        (dgNerve.map (dgCommaAugmentationSourceLift R E E (DGFunctor.id E)) ≫
          dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E))
        (Simplex.vertex NX) (Simplex.vertex Y)
        (by apply Simplex.vertexEquiv.injective; rfl)
        (by apply Simplex.vertexEquiv.injective; rfl)
lemma dgGluingPostNormalizeUnitCollarTriangleFamily_first_input :
    (stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ Δ[1])) ≫
      dgGluingPostNormalizeUnitCollarTriangleFamily R E X Y f =
      intervalMappingUncurry (fst K (Δ[1] : SSet.{max u v}) ≫
        dgGluingPreNormalizedReplacementIntervalFamily R E X Y f) := by
  rw [intervalMappingUncurry_precomp, dgGluingPreNormalizedReplacementIntervalFamily,
    intervalMappingPostOfEq_uncurry]
  exact dgGluingPostNormalizeUnitCollarTriangleFamily_first R E X Y f


lemma dgGluingPostNormalizeUnitCollarTriangleFamily_zero :
    (Δ[2] ◁ (ι₀ : K ⟶ _)) ≫
      dgGluingPostNormalizeUnitCollarTriangleFamily R E X Y f =
      (squareTriangle 0 ▷ K) ≫ (α_ (Δ[1] : SSet.{max u v}) Δ[1] K).hom ≫
        (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ K)) ≫
          dgGluingPreNormalizeAugmentationTriangle R E X Y f ≫
            dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E) := by
  rw [dgGluingPostNormalizeUnitCollarTriangleFamily, ← Category.assoc,
    dgGluingLastUnitCollarFamily_zero]
  have h := congrArg (fun t => (squareTriangle 0 ▷ K) ≫
    (α_ (Δ[1] : SSet.{max u v}) Δ[1] K).hom ≫ t ≫
      dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E))
    (dgGluingPostNormalizeAugmentationTriangle_shared R E X Y f)
  simpa only [Category.assoc] using h
end SerrePositivity.InfinityCategories
