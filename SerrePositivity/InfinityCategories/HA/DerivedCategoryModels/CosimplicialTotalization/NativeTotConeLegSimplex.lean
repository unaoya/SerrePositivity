module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotConeLegEvaluation

/-!
概要：元のTot錐の指定脚は、同じweighted係数からの一次coherent単体の比較像。
方針：点と点のjoin同型の両逆則を使い、余分な標準単体の輸送を消す。
規約：IS-W2 C01の既存構成の単位・評価則。一次単体の厳密等式。
使われ方：HA 1.2.4、標準脚の閉零射との最終照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open scoped Simplicial
variable {A : Type u} [CommRing A]

/-- 元のdg錐の脚を、同じweighted第0単体のcoherent一単体で読む。 -/
theorem nativeDGCone_leg_simplex (X : CosimplicialObject (Complex A))
    (σ : (nerve (AsSmall.{u} SimplexCategory)) _⦋0⦌) :
    let I := AsSmall.{u} SimplexCategory
    let F := liftedClosedDiagram X
    let z := ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X)
    let φ := liftedEnrichedBousfieldKanCone X
    let s := (weightedNerveSectionFromTransform
      (CartesianMonoidalCategory.fst (bousfieldKanWeight I)
        ((Functor.const I).obj (Δ[0] : SSet.{u})) ≫ φ)).app (Opposite.op ⦋0⦌)
          (σ, SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))
    (derivedConeLeg (nativeDGCone X) (ULift.up σ)).edge =
      (coherentComparison (R := A) (D := Complex A)).app (Opposite.op ⦋1⦌)
        (weightedConeSimplex F z s.2) := by
  erw [nativeDGCone_leg_weighted]
  congr 1
  change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
    ((leftPointStdSimplexIso 0).hom ≫ SSet.yonedaEquiv.symm _)) = _
  change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
    (((joinStdSimplexIso 0 0).hom ≫ 𝟙 _) ≫ SSet.yonedaEquiv.symm _)) = _
  rw [Category.comp_id, Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
