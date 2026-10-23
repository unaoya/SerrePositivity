module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeNormalizationRawCubes

/-! native cube の加群側二端面は、元恒等 comma Hom と実正規化 Hom の同じ全区間族。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
local notation "RM" => RightModule R C
local notation "Q" => DGFunctorCommaObject R (RightModule R C) (RightModule R C)
  (DGFunctor.id (RightModule R C))
local notation "IX" => dgGluingNativeIdentityCommaObject R C D M X
local notation "IY" => dgGluingNativeIdentityCommaObject R C D M Y

lemma dgGluingNativePreNormalizeRawCube_original_face :
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 1 (DGNerve.pinchedHom R Q IX IY))) ≫
        dgGluingNativePreNormalizeRawCube R C D M X Y =
      (Δ[1] ◁ intervalMappingUncurry (pinchedHomToIntervalMappingSpace
        (X := dgNerve R Q) (Simplex.vertex IX) (Simplex.vertex IY))) ≫
          dgGluingCommaAugmentationPrism R RM RM (DGFunctor.id RM) ≫
            dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R RM) := by
  rw [dgGluingNativePreNormalizeRawCube, ← Category.assoc,
    dgGluingIdentityCommaPreNormalizeCube_interval_one, Category.id_comp, Category.assoc]

lemma dgGluingNativePostNormalizeRawCube_normalized_face :
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 0 (DGNerve.pinchedHom R Q IX IY))) ≫
        dgGluingNativePostNormalizeRawCube R C D M X Y =
      (Δ[1] ◁ intervalMappingUncurry ((pinchedHomChainMap (D := Q) (E := Q)
        (dgGluingIdentityCommaNormalizeHom R RM IX IY)) ≫
          pinchedHomToIntervalMappingSpace (X := dgNerve R Q)
            (Simplex.vertex (dgGluingIdentityCommaObject R RM (representable R X.left)))
            (Simplex.vertex (dgGluingIdentityCommaObject R RM (M.rightAt Y.right))))) ≫
              dgGluingCommaAugmentationPrism R RM RM (DGFunctor.id RM) ≫
                dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R RM) := by
  rw [dgGluingNativePostNormalizeRawCube, ← Category.assoc,
    dgGluingIdentityCommaPostNormalizeCube_interval_zero, Category.id_comp, Category.assoc]
  rfl

end SerrePositivity.InfinityCategories
