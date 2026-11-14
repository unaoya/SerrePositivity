module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotWeightedApexFamily
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotWeightedCellNaturality
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotWeightedCellIdentification
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSimplexEvaluationAtParameter

/-!
概要：元のweighted Totセルの全図式射・全高次単体の評価族。
方針：既存StrictSimplexCategoryと全評価を、元の指定セルと厳密写像へ適用。
規約：IS-W2 D01の既存構成の組み立て・表示則。同じ元の全joinセルへ戻す。
使われ方：HA 1.2.4、全錐族の局所セルの貼り合わせ。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory SSet MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 元の全Tot頂点関手を固定した、同じweightedセルのcoslice単体。 -/
def nativeTotFunctorCosliceSimplex {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    (sliceUnder (curry (nativeTotApexFamily A))) _⦋n⦌ := by
  refine ⟨curry (nativeTotWeightedCellFamily A σ), ?_⟩
  change joinInl (Δ[0] : SSet.{u+1}) (Δ[n] : SSet.{u+1}) ≫
      curry (nativeTotWeightedCellFamily A σ) = curry (nativeTotApexFamily A)
  rw [← curry_natural_left, nativeTotWeightedCellFamily_apex]

/-- 元の全セル族を、既存cosliceの切断として貼り合わせる。 -/
def nativeTotFunctorCosliceSection :
    (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)) ⟶
      sliceUnder (curry (nativeTotApexFamily A)) where
  app n := ↾fun s => nativeTotFunctorCosliceSimplex A (n := n.unop.len) s.down
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    exact (congrArg curry (nativeTotWeightedCellFamily_reindex A α.unop s.down)).trans
      (curry_natural_left _ _)

/-- 元の指定Tot錐の全図式射・全高次単体を同時に評価する全join族。 -/
def nativeTotJoinFamily :
    nerve (CosimplicialObject (Complex A)) ⊗
      join (Δ[0] : SSet.{u+1})
        ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory))) ⟶
          dgNerve A (Complex A) :=
  uncurry (sliceUnderUncurry (nativeTotFunctorCosliceSection A))

/-- 全join族の初点は同じ元の全Tot頂点関手。 -/
theorem nativeTotJoinFamily_apex :
    (nerve (CosimplicialObject (Complex A)) ◁
      joinInl (Δ[0] : SSet.{u+1})
        ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)))) ≫
      nativeTotJoinFamily A = nativeTotApexFamily A := by
  rw [nativeTotJoinFamily, ← uncurry_natural_left, sliceUnderUncurry_fixed]
  exact uncurry_curry _

/-- 全join族の各cosliceセルは元の同じ全パラメータセル族。 -/
theorem nativeTotJoinFamily_cell {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    (nerve (CosimplicialObject (Complex A)) ◁
      joinMap (𝟙 (Δ[0] : SSet.{u+1}))
        (SSet.yonedaEquiv.symm (ULift.up σ))) ≫ nativeTotJoinFamily A =
      nativeTotWeightedCellFamily A σ := by
  have h := sliceUnderCurry_uncurry (nativeTotFunctorCosliceSection A)
  have hc := congrArg (fun f => (f.app (Opposite.op ⦋n⦌) (ULift.up σ)).val) h
  change joinMap (𝟙 (Δ[0] : SSet.{u+1})) (SSet.yonedaEquiv.symm (ULift.up σ)) ≫
      sliceUnderUncurry (nativeTotFunctorCosliceSection A) =
        curry (nativeTotWeightedCellFamily A σ) at hc
  rw [nativeTotJoinFamily, ← uncurry_natural_left, hc, uncurry_curry]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
