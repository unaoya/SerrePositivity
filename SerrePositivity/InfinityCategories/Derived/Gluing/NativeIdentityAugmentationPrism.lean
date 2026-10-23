module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeIdentityComma
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaImagePrism
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaAugmentationSliceCube
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseAugmentationPrism
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseSimplexFamilies
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseNerveMap

/-! 元 gluing の全 augmentation 族は、一般宇宙の実恒等 comma 関手で引き戻した同じ元の族。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
local notation "RM" => RightModule R C
local notation "Q" => DGFunctorCommaObject R (RightModule R C) (RightModule R C)
  (DGFunctor.id (RightModule R C))

lemma dgGluingNativeIdentityAugmentationSimplex {n : ℕ}
    (s : Simplex R (DGGluingObject R C D M) n) (β : Fin (n + 1) →o Fin 2) :
    dgCommaAugmentationPrismSimplex R RM RM (DGFunctor.id RM)
        (s.map (dgGluingNativeIdentityCommaFunctor R C D M)) β =
      dgCommaAugmentationPrismSimplex R D RM M.toFunctor
        (s.map (dgGluingToComma R C D M)) β := by
  have hs : s.map (dgGluingNativeIdentityCommaFunctor R C D M) =
      (s.map (dgGluingToComma R C D M)).map
        (dgGluingCommaImageFunctor R D RM M.toFunctor) := by
    apply Simplex.ext
    exact SimplexData.map_comp s.toSimplexData _ _
  rw [hs, dgGluingCommaImagePrismSimplex]

omit D M in
def dgGluingModuleIdentityAugmentationPrism :
    (Δ[1] : SSet.{max (u + 1) v}) ⊗ dgNerve R Q ⟶ dgNerve R RM :=
  dgGluingCommaAugmentationPrism R RM RM (DGFunctor.id RM) ≫
    dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R RM)

lemma dgGluingNativeIdentityAugmentationPrism :
    (Δ[1] ◁ dgGluingUniverseNerveMap.{u, max u v w, max (u + 1) v, max (u + 1) v w}
        (dgGluingNativeIdentityCommaFunctor R C D M)) ≫
      dgGluingUliftSimplexFamily.{max (u + 1) v, max (u + 1) v w} 1
        (dgGluingModuleIdentityAugmentationPrism R C) =
      (β_ (Δ[1] : SSet.{max (u + 1) v w})
        ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (dgNerve R (DGGluingObject R C D M)))).hom ≫
            dgGluingUniverseAugmentationPrism R C D M := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  change ((dgCommaAugmentationPrismSimplex R RM RM (DGFunctor.id RM)
      (s.2.down.map (dgGluingNativeIdentityCommaFunctor R C D M))
      (SSet.stdSimplex.objEquiv s.1).toOrderHom).map
        (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R RM)).map
        (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R RM) =
    dgCommaAugmentationPrismSimplex R D RM M.toFunctor
      (s.2.down.map (dgGluingToComma R C D M)) (SSet.stdSimplex.objEquiv s.1).toOrderHom
  rw [dgGluingNativeIdentityAugmentationSimplex]
  apply Simplex.ext
  change ((dgCommaAugmentationPrismSimplex R D RM M.toFunctor
      (s.2.down.map (dgGluingToComma R C D M))
      (SSet.stdSimplex.objEquiv s.1).toOrderHom).toSimplexData.map
        (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R RM)).map
        (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R RM) = _
  rw [← SimplexData.map_comp, dgUniverseLiftUp_comp_down, SimplexData.map_id]

end SerrePositivity.InfinityCategories
