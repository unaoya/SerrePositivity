module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.FirstFixedCompositionDiagonal

/-! 指定した始辺と可変第二辺を持つ実三角形族を、同じ合成対応へ戻す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
variable {X T : SSet.{u}} {x y : X _⦋0⦌} (f : X.Edge x y) (z : X _⦋0⦌)
  (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace y z) (H : (Δ[2] : SSet.{u}) ⊗ T ⟶ X)
  (hfirst : (stdSimplex.δ (2 : Fin 3) ▷ T) ≫ H =
    fst (Δ[1] : SSet.{u}) T ≫ SSet.yonedaEquiv.symm f.edge)
  (hlast : (stdSimplex.δ (0 : Fin 3) ▷ T) ≫ H = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry a)

def dgGluingFirstFixedCompositionLift : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionSpace f z :=
  pullback.lift (curry H) a (by
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry]
    apply (horn₂₁.isPushout.map (tensorRight T)).hom_ext
    · change (horn₂₁.ι₀₁ ▷ T) ≫ (((horn 2 1).ι ▷ T) ≫ H) =
        (horn₂₁.ι₀₁ ▷ T) ≫ uncurry (a ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionHornMap f z)
      rw [← Category.assoc, ← comp_whiskerRight, horn.ι_ι,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionHornMap_first, hfirst]
    · change (horn₂₁.ι₁₂ ▷ T) ≫ (((horn 2 1).ι ▷ T) ≫ H) =
        (horn₂₁.ι₁₂ ▷ T) ≫ uncurry (a ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionHornMap f z)
      rw [← Category.assoc, ← comp_whiskerRight, horn.ι_ι,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionHornMap_last, hlast])

lemma dgGluingFirstFixedCompositionLift_triangle :
    dgGluingFirstFixedCompositionLift f z a H hfirst hlast ≫
      pullback.fst ((pre (horn 2 1).ι).app X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionHornMap f z) =
      curry H :=
  pullback.lift_fst _ _ _

lemma dgGluingFirstFixedCompositionLift_second :
    dgGluingFirstFixedCompositionLift f z a H hfirst hlast ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionSecond f z = a :=
  pullback.lift_snd _ _ _

lemma dgGluingFirstFixedCompositionLift_evaluation :
    (Δ[2] ◁ dgGluingFirstFixedCompositionLift f z a H hfirst hlast) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionEvaluation f z = H := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionEvaluation, ← uncurry_natural_left,
    dgGluingFirstFixedCompositionLift_triangle, uncurry_curry]

lemma dgGluingFirstFixedCompositionLift_diagonal :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (dgGluingFirstFixedCompositionLift f z a H hfirst hlast ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionDiagonal f z) = (stdSimplex.δ (1 : Fin 3) ▷ T) ≫ H := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionDiagonal_uncurry]
  change (stdSimplex.δ (1 : Fin 3) ▷ T) ≫
    ((Δ[2] ◁ dgGluingFirstFixedCompositionLift f z a H hfirst hlast) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionEvaluation f z) = _
  rw [dgGluingFirstFixedCompositionLift_evaluation]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
