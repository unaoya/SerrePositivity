module
public import SerrePositivity.InfinityCategories.Derived.Gluing.FirstFixedCompositionDiagonal

/-! 指定した始辺と可変第二辺を持つ実三角形族を、同じ合成対応へ戻す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
variable {X T : SSet.{u}} {x y : X _⦋0⦌} (f : X.Edge x y) (z : X _⦋0⦌)
  (a : T ⟶ intervalMappingSpace y z) (H : (Δ[2] : SSet.{u}) ⊗ T ⟶ X)
  (hfirst : (stdSimplex.δ (2 : Fin 3) ▷ T) ≫ H =
    fst (Δ[1] : SSet.{u}) T ≫ SSet.yonedaEquiv.symm f.edge)
  (hlast : (stdSimplex.δ (0 : Fin 3) ▷ T) ≫ H = intervalMappingUncurry a)

def dgGluingFirstFixedCompositionLift : T ⟶ dgGluingFirstFixedCompositionSpace f z :=
  pullback.lift (curry H) a (by
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry]
    apply (horn₂₁.isPushout.map (tensorRight T)).hom_ext
    · change (horn₂₁.ι₀₁ ▷ T) ≫ (((horn 2 1).ι ▷ T) ≫ H) =
        (horn₂₁.ι₀₁ ▷ T) ≫ uncurry (a ≫ dgGluingFirstFixedCompositionHornMap f z)
      rw [← Category.assoc, ← comp_whiskerRight, horn.ι_ι,
        dgGluingFirstFixedCompositionHornMap_first, hfirst]
    · change (horn₂₁.ι₁₂ ▷ T) ≫ (((horn 2 1).ι ▷ T) ≫ H) =
        (horn₂₁.ι₁₂ ▷ T) ≫ uncurry (a ≫ dgGluingFirstFixedCompositionHornMap f z)
      rw [← Category.assoc, ← comp_whiskerRight, horn.ι_ι,
        dgGluingFirstFixedCompositionHornMap_last, hlast])

lemma dgGluingFirstFixedCompositionLift_triangle :
    dgGluingFirstFixedCompositionLift f z a H hfirst hlast ≫
      pullback.fst ((pre (horn 2 1).ι).app X) (dgGluingFirstFixedCompositionHornMap f z) =
      curry H :=
  pullback.lift_fst _ _ _

lemma dgGluingFirstFixedCompositionLift_second :
    dgGluingFirstFixedCompositionLift f z a H hfirst hlast ≫
      dgGluingFirstFixedCompositionSecond f z = a :=
  pullback.lift_snd _ _ _

lemma dgGluingFirstFixedCompositionLift_evaluation :
    (Δ[2] ◁ dgGluingFirstFixedCompositionLift f z a H hfirst hlast) ≫
      dgGluingFirstFixedCompositionEvaluation f z = H := by
  rw [dgGluingFirstFixedCompositionEvaluation, ← uncurry_natural_left,
    dgGluingFirstFixedCompositionLift_triangle, uncurry_curry]

lemma dgGluingFirstFixedCompositionLift_diagonal :
    intervalMappingUncurry (dgGluingFirstFixedCompositionLift f z a H hfirst hlast ≫
      dgGluingFirstFixedCompositionDiagonal f z) = (stdSimplex.δ (1 : Fin 3) ▷ T) ≫ H := by
  rw [intervalMappingUncurry_precomp, dgGluingFirstFixedCompositionDiagonal_uncurry]
  change (stdSimplex.δ (1 : Fin 3) ▷ T) ≫
    ((Δ[2] ◁ dgGluingFirstFixedCompositionLift f z a H hfirst hlast) ≫
      dgGluingFirstFixedCompositionEvaluation f z) = _
  rw [dgGluingFirstFixedCompositionLift_evaluation]

end SerrePositivity.InfinityCategories
