module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotConeSectionVertex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.JoinConeSectionLeg

/-!
概要：元のTot錐のdg nerveの実際の脚を、同じweighted入力の実一次単体で読む。
方針：join脚とcoslice切断の評価、元の切断の頂点、比較写像の後合成を照合する。
規約：IS-W2 C01の証明分割。辺の同型類ではなく同じ一次単体を保持する。
使われ方：HA 1.2.4、標準脚の最終等式。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped Simplicial
variable {A : Type u} [CommRing A]

/-- 元のdg錐の脚は、指定weighted入力の同じ第0単体からの実一次単体。 -/
theorem nativeDGCone_leg_weighted (X : CosimplicialObject (Complex A))
    (σ : (nerve (AsSmall.{u} SimplexCategory)) _⦋0⦌) :
    let I := AsSmall.{u} SimplexCategory
    let F := liftedClosedDiagram X
    let z := ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X)
    let φ := liftedEnrichedBousfieldKanCone X
    (derivedConeLeg (nativeDGCone X) (ULift.up σ)).edge =
    (coherentComparison (R := A) (D := Complex A)).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
        (weightedCosliceSimplex F z
          ((weightedNerveSectionFromTransform
            (CartesianMonoidalCategory.fst (bousfieldKanWeight I)
              ((Functor.const I).obj (Δ[0] : SSet.{u})) ≫ φ)).app
                (Opposite.op ⦋0⦌)
                (σ, SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))))).val)) := by
  have h := joinCone_section_leg (nativeCoherentCone X) (ULift.up σ)
    (coherentNerveVertex (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X)))
    (nativeCoherentCone_vertex X)
  erw [nativeTotCone_cosliceSection_vertex] at h
  have hm : (derivedConeLeg (nativeDGCone X) (ULift.up σ)).edge =
      (coherentComparison (R := A) (D := Complex A)).app (Opposite.op ⦋1⦌)
        (derivedConeLeg (nativeCoherentCone X) (ULift.up σ)).edge := by
    change SSet.yonedaEquiv (_ ≫ _ ≫ ((nativeCoherentCone X).val ≫
      coherentComparison (R := A) (D := Complex A))) = _
    rw [← Category.assoc, ← Category.assoc, SSet.yonedaEquiv_comp]
    rfl
  exact hm.trans (congrArg
    (fun e => (coherentComparison (R := A) (D := Complex A)).app (Opposite.op ⦋1⦌) e) h)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
