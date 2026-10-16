module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.PrecompositionHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanPullbackDeformation

/-! # A vertical retraction homotopy becomes a strong mapping-space deformation retract

The actual precomposition inclusion is fixed on its entire interval.
This supplies the exact hypothesis needed for Kan pullback deformation,
without replacing any mapping space or assuming a value model structure.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.MappingPrecompositionRetraction
variable {E B : SSet.{v}} (p : E ⟶ B) (s : B ⟶ E) (hs : s ≫ p = 𝟙 B)
  (H : SSet.Homotopy (𝟙 E) (p ≫ s))
  (hH : H.h ≫ p = fst E (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ p)

include hs in
lemma retraction (K : SSet.{v}) :
    (MonoidalClosed.pre p).app K ≫ (MonoidalClosed.pre s).app K = 𝟙 _ := by
  rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, hs, MonoidalClosed.pre_id]
  rfl

def homotopy (K : SSet.{v}) :
    SSet.Homotopy (𝟙 ((ihom E).obj K))
      ((MonoidalClosed.pre s).app K ≫ (MonoidalClosed.pre p).app K) :=
  LargeParameterSquare.changeEndpoints (PrecompositionHomotopy.homotopy H K)
    (by rw [MonoidalClosed.pre_id]; rfl)
    (by rw [MonoidalClosed.pre_map]; rfl)

include hH in
lemma fixed (K : SSet.{v}) :
    ((MonoidalClosed.pre p).app K) ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫
      (homotopy p s H K).h =
    fst ((ihom B).obj K) (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫
      (MonoidalClosed.pre p).app K := by
  rw [homotopy, LargeParameterSquare.changeEndpoints_h]
  change _ ≫ PrecompositionHomotopy.interval H K = _
  rw [PrecompositionHomotopy.interval_post]
  exact PrecompositionHomotopy.interval_constant (HomotopyClasses.postHomotopy p H) K p hH

include hs hH in
lemma pullback_localized_isIso (K : SSet.{v}) {Z P : SSet.{v}}
    (q : Z ⟶ (ihom E).obj K) (hq : SSet.modelCategoryQuillen.J.rlp q)
    (j : P ⟶ Z) (k : P ⟶ (ihom B).obj K)
    (sq : IsPullback j k q ((MonoidalClosed.pre p).app K)) :
    IsIso (AnodyneHomotopy.anodyneQ.map j) :=
  KanPullbackDeformation.localized_isIso _ _ (retraction p s hs K)
    (homotopy p s H K) (fixed p s H hH K) q hq j k sq

end SerrePositivity.SimplicialModel.MappingPrecompositionRetraction
