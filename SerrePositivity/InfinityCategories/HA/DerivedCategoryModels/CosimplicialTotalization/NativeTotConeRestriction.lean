module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotConePointSection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.WeightedSectionParameterNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.UliftPointTensorEvaluation

/-!
概要：元のTot錐全体上の指定された族を制限すると元の豊穣Hom比較になる。
方針：相対uncurryの単射性、点を固定したend作用、ULift評価の同じ射を照合する。
規約：IS-W2 B06。元の頂点・標準脚・全高次単体を保つ。
使われ方：HA 1.2.4、指定族によるnative極限性の判定。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open scoped Simplicial
variable {A : Type u} [CommRing A]

/-- 全Tot錐上の指定族の制限は、同じ豊穣Hom比較と既存native比較の合成。 -/
theorem nativeTotConeFamilyLift_restriction
    (X : CosimplicialObject (Complex A)) (x : ClosedCategory A (Complex A)) :
    nativeTotConeFamilyLift X x ≫
      coneSectionRestriction (nativeCoherentCone X) (coherentNerveVertex x) =
    (SSet.uliftFunctor.{u+1,u}).map
      (reflectedWeightedHomComparison (liftedClosedDiagram X)
        (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
        (liftedEnrichedBousfieldKanCone X) x) ≫
      reflectedHomHolimConeComparison (liftedClosedDiagram X) x := by
  let I := AsSmall.{u} SimplexCategory
  let U := SSet.uliftFunctor.{u+1,u}
  let F := liftedClosedDiagram X
  let z := ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X)
  let H := simplicialHomDiagram F z ⋙ SSet.opFunctor
  let φ := liftedEnrichedBousfieldKanCone X
  let S := (SimplicialCategory.sHom x z).op
  let E := bousfieldKanHolim H
  let p : (Δ[0] : SSet.{u}) ⟶ E := weightedSectionsLift
    (fst (bousfieldKanWeight I) ((Functor.const I).obj (Δ[0] : SSet.{u})) ≫ φ)
  let v := inv (snd (Δ[0] : SSet.{u}) S) ≫ (p ⊗ₘ 𝟙 S)
  have hv : v ≫ weightedConeEndPrecomposition F x z =
      reflectedWeightedHomComparison F z φ x := by
    have h := congrArg (fun h => inv (snd (Δ[0] : SSet.{u}) S) ≫ h)
      (reflectedWeightedHomComparison_point_precomposition F z φ x)
    change (inv (snd (Δ[0] : SSet.{u}) S) ≫ (p ⊗ₘ 𝟙 S)) ≫
        weightedConeEndPrecomposition F x z =
      inv (snd (Δ[0] : SSet.{u}) S) ≫ snd (Δ[0] : SSet.{u}) S ≫
        reflectedWeightedHomComparison F z φ x at h
    simpa only [v, Category.assoc, IsIso.inv_hom_id_assoc] using h
  have he : SSet.yonedaEquiv.symm (ULift.up (SSet.yonedaEquiv p)) =
      (uliftStdSimplexIso.{u,u+1} 0).inv ≫ U.map p := by
    simpa only [Equiv.symm_apply_apply] using
      (uliftYonedaMap.{u,u+1} (SSet.yonedaEquiv p)).symm
  apply relativeFunctorUncurry_injective
    (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
    (strictCoherentDiagram F)
  rw [nativeTotConeFamilyLift_restriction_uncurry]
  change _ = relativeFunctorUncurry
    (U.map (reflectedWeightedHomComparison F z φ x) ≫ reflectedHomHolimConeComparison F x)
  rw [← hv, Functor.map_comp, Category.assoc, relativeFunctorUncurry_parameter,
    reflectedHomHolimConeComparison_precomposition_uncurry,
    weightedCosliceEndPrecompositionEvaluation_eq_family]
  erw [he]
  simpa only [Category.assoc] using congrArg
    (fun h => h ≫ weightedCoslicePrecompositionFamily F x z)
    (uliftPointTensorEvaluation.{u,u+1} (nerve I) E
      _ S p (bousfieldKanWeightedNerveEvaluation H))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
