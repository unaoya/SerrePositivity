module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseNerveProjections
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugPrismReindex
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-! 対象宇宙の等しさを仮定せず、元の augmentation 全単体族を共通宇宙へ送る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingUniverseAugmentationPrism :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
      (dgNerve R (DGGluingObject R C D M)) ⊗ (Δ[1] : SSet) ⟶
    (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
      (dgNerve R (RightModule R C)) where
  app _ := ↾fun s => ULift.up (dgCommaAugmentationPrismSimplex R D (RightModule R C)
    M.toFunctor (s.1.down.map (dgGluingToComma R C D M))
      (SSet.stdSimplex.objEquiv s.2).toOrderHom)
  naturality _ _ f := by
    ext s
    apply ULift.ext
    change dgCommaAugmentationPrismSimplex R D (RightModule R C) M.toFunctor
        ((s.1.down.pullback f.unop.toOrderHom).map (dgGluingToComma R C D M))
        ((SSet.stdSimplex.objEquiv s.2).toOrderHom.comp f.unop.toOrderHom) =
      (dgCommaAugmentationPrismSimplex R D (RightModule R C) M.toFunctor
        (s.1.down.map (dgGluingToComma R C D M))
        (SSet.stdSimplex.objEquiv s.2).toOrderHom).pullback f.unop.toOrderHom
    have hx : (s.1.down.pullback f.unop.toOrderHom).map (dgGluingToComma R C D M) =
        (s.1.down.map (dgGluingToComma R C D M)).pullback f.unop.toOrderHom := by
      apply Simplex.ext
      exact SimplexData.map_pullback s.1.down.toSimplexData
        (dgGluingToComma R C D M) f.unop.toOrderHom
    rw [hx, dgCommaAugmentationPrismSimplex_pullback]

lemma dgGluingUniverseAugmentationPrism_zero :
    SSet.ι₀ ≫ dgGluingUniverseAugmentationPrism R C D M =
      dgGluingUniverseLeftNerve R C D M ≫ dgGluingUniverseYoneda.{u, v, w} R C := by
  ext n s
  apply ULift.ext
  change dgCommaAugmentationPrismSimplex R D (RightModule R C) M.toFunctor
      (s.down.map (dgGluingToComma R C D M)) (OrderHom.const _ (0 : Fin 2)) =
    (s.down.map (dgGluingLeft R C D M)).map (dgYoneda R C)
  rw [dgCommaAugmentationPrismSimplex_zero]
  apply Simplex.ext
  change (s.down.toSimplexData.map (dgGluingToComma R C D M)).map
      (dgCommaAugmentationSource R D (RightModule R C) M.toFunctor) =
    (s.down.toSimplexData.map (dgGluingLeft R C D M)).map (dgYoneda R C)
  rw [← SimplexData.map_comp, ← SimplexData.map_comp, dgGluingLeft_comp_yoneda]
  rfl

lemma dgGluingUniverseAugmentationPrism_one :
    SSet.ι₁ ≫ dgGluingUniverseAugmentationPrism R C D M =
      dgGluingUniverseRightNerve R C D M ≫ dgGluingUniverseCoefficient R C D M := by
  ext n s
  apply ULift.ext
  change dgCommaAugmentationPrismSimplex R D (RightModule R C) M.toFunctor
      (s.down.map (dgGluingToComma R C D M)) (OrderHom.const _ (1 : Fin 2)) =
    (s.down.map (dgGluingRight R C D M)).map M.toFunctor
  rw [dgCommaAugmentationPrismSimplex_one]
  apply Simplex.ext
  change (s.down.toSimplexData.map (dgGluingToComma R C D M)).map
      (dgCommaAugmentationTarget R D (RightModule R C) M.toFunctor) =
    (s.down.toSimplexData.map (dgGluingRight R C D M)).map M.toFunctor
  rw [← SimplexData.map_comp, ← SimplexData.map_comp]
  rfl

def dgGluingUniverseAugmentationHomotopy :
    SSet.Homotopy
      (dgGluingUniverseLeftNerve R C D M ≫ dgGluingUniverseYoneda.{u, v, w} R C)
      (dgGluingUniverseRightNerve R C D M ≫ dgGluingUniverseCoefficient R C D M) where
  h := dgGluingUniverseAugmentationPrism R C D M
  h₀ := dgGluingUniverseAugmentationPrism_zero R C D M
  h₁ := dgGluingUniverseAugmentationPrism_one R C D M
  rel := by
    ext n s
    exact False.elim s.1.2

end SerrePositivity.InfinityCategories
