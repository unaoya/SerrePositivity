module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseNerveProjections
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCommaAugPrismReindex
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-! 対象宇宙の等しさを仮定せず、元の augmentation 全単体族を共通宇宙へ送る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)

def dgGluingUniverseAugmentationPrism :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)) ⊗ (Δ[1] : SSet) ⟶
    (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R C)) where
  app _ := ↾fun s => ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R D (RightModule R C)
    M.toFunctor (s.1.down.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M))
      (SSet.stdSimplex.objEquiv s.2).toOrderHom)
  naturality _ _ f := by
    ext s
    apply ULift.ext
    change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R D (RightModule R C) M.toFunctor
        ((s.1.down.pullback f.unop.toOrderHom).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M))
        ((SSet.stdSimplex.objEquiv s.2).toOrderHom.comp f.unop.toOrderHom) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R D (RightModule R C) M.toFunctor
        (s.1.down.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M))
        (SSet.stdSimplex.objEquiv s.2).toOrderHom).pullback f.unop.toOrderHom
    have hx : (s.1.down.pullback f.unop.toOrderHom).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M) =
        (s.1.down.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M)).pullback f.unop.toOrderHom := by
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map_pullback s.1.down.toSimplexData
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M) f.unop.toOrderHom
    rw [hx, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex_pullback]

lemma dgGluingUniverseAugmentationPrism_zero :
    SSet.ι₀ ≫ dgGluingUniverseAugmentationPrism R C D M =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseLeftNerve R C D M ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseYoneda.{u, v, w} R C := by
  ext n s
  apply ULift.ext
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R D (RightModule R C) M.toFunctor
      (s.down.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M)) (OrderHom.const _ (0 : Fin 2)) =
    (s.down.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M)).map (dgYoneda R C)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex_zero]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  change (s.down.toSimplexData.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M)).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R D (RightModule R C) M.toFunctor) =
    (s.down.toSimplexData.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M)).map (dgYoneda R C)
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData.map_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft_comp_yoneda]
  rfl

lemma dgGluingUniverseAugmentationPrism_one :
    SSet.ι₁ ≫ dgGluingUniverseAugmentationPrism R C D M =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseRightNerve R C D M ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseCoefficient R C D M := by
  ext n s
  apply ULift.ext
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R D (RightModule R C) M.toFunctor
      (s.down.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M)) (OrderHom.const _ (1 : Fin 2)) =
    (s.down.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M)).map M.toFunctor
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex_one]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  change (s.down.toSimplexData.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M)).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTarget R D (RightModule R C) M.toFunctor) =
    (s.down.toSimplexData.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M)).map M.toFunctor
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData.map_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData.map_comp]
  rfl

def dgGluingUniverseAugmentationHomotopy :
    SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseLeftNerve R C D M ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseYoneda.{u, v, w} R C)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseRightNerve R C D M ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseCoefficient R C D M) where
  h := dgGluingUniverseAugmentationPrism R C D M
  h₀ := dgGluingUniverseAugmentationPrism_zero R C D M
  h₁ := dgGluingUniverseAugmentationPrism_one R C D M
  rel := by
    ext n s
    exact False.elim s.1.2

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
