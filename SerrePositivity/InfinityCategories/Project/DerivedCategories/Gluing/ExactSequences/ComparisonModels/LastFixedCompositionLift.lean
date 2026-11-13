module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CompositionCorrespondenceDiagonal

/-! 可変第一辺と指定した終辺を持つ実三角形族を、同じ合成対応へ戻す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
variable {X T : SSet.{u}} (x : X _⦋0⦌) {y z : X _⦋0⦌} (g : X.Edge y z)
  (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) (H : (Δ[2] : SSet.{u}) ⊗ T ⟶ X)
  (hfirst : (stdSimplex.δ (2 : Fin 3) ▷ T) ≫ H = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry a)
  (hlast : (stdSimplex.δ (0 : Fin 3) ▷ T) ≫ H =
    fst (Δ[1] : SSet.{u}) T ≫ SSet.yonedaEquiv.symm g.edge)

def dgGluingLastFixedCompositionLift : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondence x g :=
  pullback.lift (curry H) a (by
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry]
    apply (horn₂₁.isPushout.map (tensorRight T)).hom_ext
    · change (horn₂₁.ι₀₁ ▷ T) ≫ (((horn 2 1).ι ▷ T) ≫ H) =
        (horn₂₁.ι₀₁ ▷ T) ≫ uncurry (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.composableHomHornMap x g)
      rw [← Category.assoc, ← comp_whiskerRight, horn.ι_ι,
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.composableHomHornMap_first, hfirst]
    · change (horn₂₁.ι₁₂ ▷ T) ≫ (((horn 2 1).ι ▷ T) ≫ H) =
        (horn₂₁.ι₁₂ ▷ T) ≫ uncurry (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.composableHomHornMap x g)
      rw [← Category.assoc, ← comp_whiskerRight, horn.ι_ι,
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.composableHomHornMap_last, hlast])

lemma dgGluingLastFixedCompositionLift_triangle :
    dgGluingLastFixedCompositionLift x g a H hfirst hlast ≫
      pullback.fst ((pre (horn 2 1).ι).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.composableHomHornMap x g) =
      curry H :=
  pullback.lift_fst _ _ _

lemma dgGluingLastFixedCompositionLift_first :
    dgGluingLastFixedCompositionLift x g a H hfirst hlast ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceFirst x g = a :=
  pullback.lift_snd _ _ _

lemma dgGluingLastFixedCompositionLift_evaluation :
    (Δ[2] ◁ dgGluingLastFixedCompositionLift x g a H hfirst hlast) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceEvaluation x g = H := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceEvaluation, ← uncurry_natural_left,
    dgGluingLastFixedCompositionLift_triangle, uncurry_curry]

lemma dgGluingLastFixedCompositionLift_diagonal :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (dgGluingLastFixedCompositionLift x g a H hfirst hlast ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonal x g) = (stdSimplex.δ (1 : Fin 3) ▷ T) ≫ H := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonal_uncurry]
  change (stdSimplex.δ (1 : Fin 3) ▷ T) ≫
    ((Δ[2] ◁ dgGluingLastFixedCompositionLift x g a H hfirst hlast) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceEvaluation x g) = _
  rw [dgGluingLastFixedCompositionLift_evaluation]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
