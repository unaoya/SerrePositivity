module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetIdentityFunctor
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetNerveLaxComparison
/-! 恒等二脚への移送は元の augmentation の全 prism と矢印族を保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed SSet DifferentialGraded DGNerve
open KST.SConstruction
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
local notation "M" => dgHomGluingBimodule R C D E p q
local notation "F" => dgGluingHomTargetToIdentity R C D E p q

lemma dgGluingHomTargetToIdentity_prism {n : ℕ}
    (s : Simplex R (DGGluingObject R C D (dgHomGluingBimodule R C D E p q)) n)
    (β : Fin (n + 1) →o Fin 2) :
    dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E)
      ((s.map (F)).map (dgGluingHomTargetToComma R E E E
        (DGFunctor.id E) (DGFunctor.id E))) β =
    dgCommaAugmentationPrismSimplex R D E q
      (s.map (dgGluingHomTargetToComma R C D E p q)) β := by
  have h : (s.map (F)).map (dgGluingHomTargetToComma R E E E
        (DGFunctor.id E) (DGFunctor.id E)) =
      s.map (dgGluingHomTargetIdentityCommaFunctor R C D E p q) := by
    apply Simplex.ext
    change (s.toSimplexData.map (F)).map _ = _
    rw [← SimplexData.map_comp, dgGluingHomTargetToIdentity_comma]
    rfl
  rw [h]
  exact dgGluingHomTargetIdentityCommaFunctor_prism R C D E p q s β

lemma dgGluingHomTargetAugmentationHomotopy_evaluate {n : ℕ}
    (s : Simplex R (DGGluingObject R C D (dgHomGluingBimodule R C D E p q)) n)
    (β : (Δ[1] : SSet) _⦋n⦌) :
    (dgGluingHomTargetAugmentationHomotopy R C D E p q).h.app (Opposite.op ⦋n⦌) (s, β) =
      dgCommaAugmentationPrismSimplex R D E q
        (s.map (dgGluingHomTargetToComma R C D E p q)) (stdSimplex.objEquiv β).toOrderHom := by
  change ((dgCommaAugmentationPrismSimplex R D E q
    (s.map (dgGluingHomTargetToComma R C D E p q)) (stdSimplex.objEquiv β).toOrderHom).map
      (dgUniverseLiftUp R E)).map (dgUniverseLiftDown R E) = _
  apply Simplex.ext
  dsimp only [Simplex.map]
  rw [← SimplexData.map_comp, dgUniverseLiftUp_comp_down, SimplexData.map_id]

lemma dgGluingHomTargetToIdentity_homotopy :
    (dgNerve.map (F) ▷ (Δ[1] : SSet)) ≫
      (dgGluingHomTargetAugmentationHomotopy R E E E (DGFunctor.id E) (DGFunctor.id E)).h =
    (dgGluingHomTargetAugmentationHomotopy R C D E p q).h := by
  ext ⟨⟨n⟩⟩ s
  rcases s with ⟨s, β⟩
  change (dgGluingHomTargetAugmentationHomotopy R E E E
    (DGFunctor.id E) (DGFunctor.id E)).h.app _ (s.map (F), β) =
      (dgGluingHomTargetAugmentationHomotopy R C D E p q).h.app _ (s, β)
  rw [dgGluingHomTargetAugmentationHomotopy_evaluate,
    dgGluingHomTargetAugmentationHomotopy_evaluate]
  exact dgGluingHomTargetToIdentity_prism R C D E p q s _

lemma dgGluingHomTargetToIdentity_arrow :
    dgNerve.map (F) ≫ dgGluingHomTargetAugmentationArrowFamily R E E E
      (DGFunctor.id E) (DGFunctor.id E) =
      dgGluingHomTargetAugmentationArrowFamily R C D E p q := by
  unfold dgGluingHomTargetAugmentationArrowFamily
  rw [← MonoidalClosed.curry_natural_left]
  congr 1
  rw [← Category.assoc, BraidedCategory.braiding_naturality_right,
    Category.assoc, dgGluingHomTargetToIdentity_homotopy]

end SerrePositivity.InfinityCategories
