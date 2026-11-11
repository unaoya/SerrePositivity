module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetIdentityFunctor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetNerveLaxComparison
/-! 恒等二脚への移送は元の augmentation の全 prism と矢印族を保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed SSet DifferentialGraded
open KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (p : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) (q : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E)
local notation "M" => dgHomGluingBimodule R C D E p q
local notation "F" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetToIdentity R C D E p q

lemma dgGluingHomTargetToIdentity_prism {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q)) n)
    (β : Fin (n + 1) →o Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E)
      ((s.map (F)).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetToComma R E E E
        (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id E) (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id E))) β =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R D E q
      (s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetToComma R C D E p q)) β := by
  have h : (s.map (F)).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetToComma R E E E
        (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id E) (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id E)) =
      s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetIdentityCommaFunctor R C D E p q) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
    change (s.toSimplexData.map (F)).map _ = _
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetToIdentity_comma]
    rfl
  rw [h]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetIdentityCommaFunctor_prism R C D E p q s β

lemma dgGluingHomTargetAugmentationHomotopy_evaluate {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q)) n)
    (β : (Δ[1] : SSet) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationHomotopy R C D E p q).h.app (Opposite.op ⦋n⦌) (s, β) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R D E q
        (s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetToComma R C D E p q)) (stdSimplex.objEquiv β).toOrderHom := by
  change ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R D E q
    (s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetToComma R C D E p q)) (stdSimplex.objEquiv β).toOrderHom).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R E)).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown R E) = _
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.map]
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp_comp_down, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData.map_id]

lemma dgGluingHomTargetToIdentity_homotopy :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (F) ▷ (Δ[1] : SSet)) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationHomotopy R E E E (DGFunctor.id E) (DGFunctor.id E)).h =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationHomotopy R C D E p q).h := by
  ext ⟨⟨n⟩⟩ s
  rcases s with ⟨s, β⟩
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationHomotopy R E E E
    (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id E) (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id E)).h.app _ (s.map (F), β) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationHomotopy R C D E p q).h.app _ (s, β)
  rw [dgGluingHomTargetAugmentationHomotopy_evaluate,
    dgGluingHomTargetAugmentationHomotopy_evaluate]
  exact dgGluingHomTargetToIdentity_prism R C D E p q s _

lemma dgGluingHomTargetToIdentity_arrow :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (F) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationArrowFamily R E E E
      (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id E) (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id E) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationArrowFamily R C D E p q := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationArrowFamily
  rw [← MonoidalClosed.curry_natural_left]
  congr 1
  rw [← Category.assoc, BraidedCategory.braiding_naturality_right,
    Category.assoc, dgGluingHomTargetToIdentity_homotopy]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
