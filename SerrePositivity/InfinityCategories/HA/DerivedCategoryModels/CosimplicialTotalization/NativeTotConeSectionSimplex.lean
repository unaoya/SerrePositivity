module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotConePointSection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.UliftPointSimplexEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedSectionParameter

/-!
概要：元のTot錐のcoslice切断の全単体は、同じ反転BK入力の実weighted評価。
方針：同じend点のYoneda表示、ULiftの任意次数の同じ点評価、切断随伴の余単位則を合成する。
規約：IS-W2 D01の既存構成の評価・単位則。元の全高次単体を保持する。
使われ方：HA 1.2.4、native錐の元の全セルとの照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped Simplicial
variable {A : Type u} [CommRing A]

/-- 指定Tot錐の切断の各単体は、同じweighted入力から作るcosliceの頂点そのもの。 -/
theorem nativeTotCone_cosliceSection_simplex (X : CosimplicialObject (Complex A)) {n : ℕ}
    (σ : (nerve (AsSmall.{u} SimplexCategory)) _⦋n⦌)
    (a₀ : (Δ[0] : SSet.{u}) _⦋n⦌) :
    let I := AsSmall.{u} SimplexCategory
    let F := liftedClosedDiagram X
    let z := ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X)
    let φ := liftedEnrichedBousfieldKanCone X
    ((coherentConeCosliceSection (nativeCoherentCone X) ≫ eqToHom (congrArg
      (fun w : (SimplicialNerve (ClosedCategory A (Complex A))) _⦋0⦌ =>
        sliceUnder (SSet.yonedaEquiv.symm w)) (nativeCoherentCone_vertex X))).app
          (Opposite.op ⦋n⦌) (ULift.up σ)) =
    weightedCosliceSimplex F z
      ((weightedNerveSectionFromTransform
        (fst (bousfieldKanWeight I) ((Functor.const I).obj (Δ[0] : SSet.{u})) ≫ φ)).app
          (Opposite.op ⦋n⦌) (σ, a₀)) := by
  let I := AsSmall.{u} SimplexCategory
  let F := liftedClosedDiagram X
  let z := ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X)
  let H := simplicialHomDiagram F z ⋙ SSet.opFunctor
  let φ := liftedEnrichedBousfieldKanCone X
  let η := fst (bousfieldKanWeight I) ((Functor.const I).obj (Δ[0] : SSet.{u})) ≫ φ
  let p := weightedSectionsLift η
  have he : SSet.yonedaEquiv.symm (ULift.up (SSet.yonedaEquiv p)) =
      (uliftStdSimplexIso.{u,u+1} 0).inv ≫ (SSet.uliftFunctor.{u+1,u}).map p := by
    simpa only [Equiv.symm_apply_apply] using
      (uliftYonedaMap.{u,u+1} (SSet.yonedaEquiv p)).symm
  have ht := bousfieldKanSectionHomEquiv_apply H p
  change weightedNerveSectionFromTransform (weightedSectionsUncurry p) =
    (nerve I ◁ p) ≫ bousfieldKanWeightedNerveEvaluation H at ht
  change weightedNerveSectionFromTransform (weightedSectionsUncurry (weightedSectionsLift η)) =
    (nerve I ◁ p) ≫ bousfieldKanWeightedNerveEvaluation H at ht
  rw [weightedSectionsUncurry_lift] at ht
  let t : (nerve I ⊗ (Δ[0] : SSet.{u})) _⦋n⦌ :=
    (σ, a₀)
  have hv := ConcreteCategory.congr_hom (NatTrans.congr_app ht (Opposite.op ⦋n⦌))
    t
  erw [nativeTotCone_cosliceSection_weighted, he]
  change (weightedCosliceComparison F z).app (Opposite.op ⦋n⦌)
    ((inv (fst ((SSet.uliftFunctor.{u+1,u}).obj (nerve I)) (Δ[0] : SSet.{u+1})) ≫
      ((SSet.uliftFunctor.{u+1,u}).obj (nerve I) ◁
        ((uliftStdSimplexIso.{u,u+1} 0).inv ≫ (SSet.uliftFunctor.{u+1,u}).map p)) ≫
      (uliftTensorIso (nerve I) (bousfieldKanHolim H)).inv ≫
      (SSet.uliftFunctor.{u+1,u}).map (bousfieldKanWeightedNerveEvaluation H)).app
        (Opposite.op ⦋n⦌) (ULift.up σ)) = _
  erw [uliftPointSimplexEvaluation (nerve I) (bousfieldKanHolim H) _ p
    (bousfieldKanWeightedNerveEvaluation H) σ a₀]
  change weightedCosliceSimplex F z _ = weightedCosliceSimplex F z _
  congr 1
  exact hv.symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
