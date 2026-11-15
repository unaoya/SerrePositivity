module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotConeFamilyLift
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.CoherentConePointSection
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.CoherentConeSourceWeightedRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ReflectedStrictConeEvaluation

/-!
概要：元のTot錐のcoslice切断を、指定weighted点の評価そのものへ戻す。
方針：固定頂点の錐と切断の往復、Yonedaの自然性、既存BK比較の評価則を合成する。
規約：IS-W2 B06の既存構成の単位・評価則。元の点と全高次単体を保持する。
使われ方：HA 1.2.4、全Tot錐上の族の制限の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open scoped Simplicial
variable {A : Type u} [CommRing A]

/-- 同じTot錐の正規化したcoslice切断は、元の切断点の実際の評価。 -/
theorem nativeTotCone_cosliceSection (X : CosimplicialObject (Complex A)) :
    coherentConeCosliceSection (nativeCoherentCone X) ≫
      eqToHom (congrArg (fun w : (SimplicialNerve (ClosedCategory A (Complex A))) _⦋0⦌ =>
        sliceUnder (SSet.yonedaEquiv.symm w)) (nativeCoherentCone_vertex X)) =
    inv (fst ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)))
      (Δ[0] : SSet.{u+1})) ≫ relativeFunctorUncurry
        (SSet.yonedaEquiv.symm (reflectedWeightedConeSectionPoint (liftedClosedDiagram X)
          (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
          (liftedEnrichedBousfieldKanCone X))) :=
  fixedVertexConeSpaceEquiv_cosliceSection _ _ _ (nativeCoherentCone_vertex X)

/-- 元のweighted切断点のYoneda表示は、同じendの点と指定BK比較の合成。 -/
theorem nativeTotCone_point_yoneda (X : CosimplicialObject (Complex A)) :
    let F := liftedClosedDiagram X
    let z := ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X)
    let φ := liftedEnrichedBousfieldKanCone X
    SSet.yonedaEquiv.symm (reflectedWeightedConeSectionPoint F z φ) =
      SSet.yonedaEquiv.symm (ULift.up (SSet.yonedaEquiv (weightedSectionsLift
        (fst (bousfieldKanWeight (AsSmall.{u} SimplexCategory))
          ((Functor.const (AsSmall.{u} SimplexCategory)).obj (Δ[0] : SSet.{u})) ≫ φ)))) ≫
        reflectedHomHolimConeComparison F z := by
  dsimp only [reflectedWeightedConeSectionPoint]
  rw [← SSet.yonedaEquiv_symm_comp]
  rfl

/-- 同じTot錐のcoslice切断は、指定end点のweighted評価と既存coslice比較の合成。 -/
theorem nativeTotCone_cosliceSection_weighted (X : CosimplicialObject (Complex A)) :
    let I := AsSmall.{u} SimplexCategory
    let F := liftedClosedDiagram X
    let z := ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X)
    let H := simplicialHomDiagram F z ⋙ SSet.opFunctor
    let φ := liftedEnrichedBousfieldKanCone X
    let e : (Δ[0] : SSet.{u+1}) ⟶
        (SSet.uliftFunctor.{u+1,u}).obj (bousfieldKanHolim H) :=
      SSet.yonedaEquiv.symm (ULift.up (SSet.yonedaEquiv (weightedSectionsLift
      (fst (bousfieldKanWeight I) ((Functor.const I).obj (Δ[0] : SSet.{u})) ≫ φ))))
    let s := inv (fst ((SSet.uliftFunctor.{u+1,u}).obj (nerve I)) (Δ[0] : SSet.{u+1})) ≫
      (((SSet.uliftFunctor.{u+1,u}).obj (nerve I)) ◁ e) ≫
        (uliftTensorIso (nerve I) (bousfieldKanHolim H)).inv ≫
          (SSet.uliftFunctor.{u+1,u}).map (bousfieldKanWeightedNerveEvaluation H)
    coherentConeCosliceSection (nativeCoherentCone X) ≫
      eqToHom (congrArg (fun w : (SimplicialNerve (ClosedCategory A (Complex A))) _⦋0⦌ =>
        sliceUnder (SSet.yonedaEquiv.symm w)) (nativeCoherentCone_vertex X)) =
    s ≫ weightedCosliceComparison F z := by
  dsimp only
  erw [nativeTotCone_cosliceSection, nativeTotCone_point_yoneda,
    relativeFunctorUncurry_parameter, reflectedHomHolimConeComparison_uncurry]
  rfl

/-- 元のTot錐全体上の族の制限は、同じweighted切断のcoslice前合成を返す。 -/
theorem nativeTotConeFamilyLift_restriction_uncurry
    (X : CosimplicialObject (Complex A)) (x : ClosedCategory A (Complex A)) :
    let I := AsSmall.{u} SimplexCategory
    let F := liftedClosedDiagram X
    let z := ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X)
    let H := simplicialHomDiagram F z ⋙ SSet.opFunctor
    let φ := liftedEnrichedBousfieldKanCone X
    let e : (Δ[0] : SSet.{u+1}) ⟶
        (SSet.uliftFunctor.{u+1,u}).obj (bousfieldKanHolim H) :=
      SSet.yonedaEquiv.symm (ULift.up (SSet.yonedaEquiv (weightedSectionsLift
      (fst (bousfieldKanWeight I) ((Functor.const I).obj (Δ[0] : SSet.{u})) ≫ φ))))
    let s := inv (fst ((SSet.uliftFunctor.{u+1,u}).obj (nerve I)) (Δ[0] : SSet.{u+1})) ≫
      (((SSet.uliftFunctor.{u+1,u}).obj (nerve I)) ◁ e) ≫
        (uliftTensorIso (nerve I) (bousfieldKanHolim H)).inv ≫
          (SSet.uliftFunctor.{u+1,u}).map (bousfieldKanWeightedNerveEvaluation H)
    relativeFunctorUncurry (nativeTotConeFamilyLift X x ≫
      coneSectionRestriction (nativeCoherentCone X) (coherentNerveVertex x)) =
    (s ▷ (SSet.uliftFunctor.{u+1,u}).obj (SimplicialCategory.sHom x z).op) ≫
      weightedCoslicePrecompositionFamily F x z := by
  dsimp only
  let I := AsSmall.{u} SimplexCategory
  let F := liftedClosedDiagram X
  let z := ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X)
  let H := simplicialHomDiagram F z ⋙ SSet.opFunctor
  let φ := liftedEnrichedBousfieldKanCone X
  let e : (Δ[0] : SSet.{u+1}) ⟶
      (SSet.uliftFunctor.{u+1,u}).obj (bousfieldKanHolim H) :=
    SSet.yonedaEquiv.symm (ULift.up (SSet.yonedaEquiv (weightedSectionsLift
    (fst (bousfieldKanWeight I) ((Functor.const I).obj (Δ[0] : SSet.{u})) ≫ φ))))
  let s := inv (fst ((SSet.uliftFunctor.{u+1,u}).obj (nerve I)) (Δ[0] : SSet.{u+1})) ≫
    (((SSet.uliftFunctor.{u+1,u}).obj (nerve I)) ◁ e) ≫
      (uliftTensorIso (nerve I) (bousfieldKanHolim H)).inv ≫
        (SSet.uliftFunctor.{u+1,u}).map (bousfieldKanWeightedNerveEvaluation H)
  exact coherentConeSourceFamily_restriction_weighted F (nativeCoherentCone X) z
    (nativeCoherentCone_vertex X) s (nativeTotCone_cosliceSection_weighted X) x

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
