module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotWeightedSimplexComposition
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
open CategoryTheory SSet MonoidalCategory CartesianMonoidalCategory
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 元の同じweighted単体と全厳密HA写像を全図式の通常関手にする。 -/
def nativeTotWeightedCellFunctor {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    CosimplicialObject (Complex A) ⥤ StrictSimplexCategory A (Complex A) (n+1) where
  obj X := ⟨coherentSimplex (weightedConeSimplex (liftedClosedDiagram X)
    (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
      (nativeTotWeightedPrefix X σ))⟩
  map f := nativeTotWeightedSimplexMap f σ
  map_id X := nativeTotWeightedSimplexMap_id X σ
  map_comp f g := nativeTotWeightedSimplexMap_comp f g σ

/-- 元の同じweightedセルの、全図式射・全高次単体の同時評価。 -/
def nativeTotWeightedCellFamily {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    nerve (CosimplicialObject (Complex A)) ⊗
      join (Δ[0] : SSet.{u+1}) (Δ[n] : SSet.{u+1}) ⟶ dgNerve A (Complex A) :=
  (nerve (CosimplicialObject (Complex A)) ◁ (leftPointStdSimplexIso n).hom) ≫
    strictSimplexFunctorEvaluation A (Complex A) (nativeTotWeightedCellFunctor A σ)

/-- 同じ全図式パラメータ族の固定Xでの値は、元の同じweightedセルの全射。 -/
theorem nativeTotWeightedCellFamily_at {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) (X : CosimplicialObject (Complex A)) :
    lift (SSet.const (ComposableArrows.mk₀ X))
        (𝟙 (join (Δ[0] : SSet.{u+1}) (Δ[n] : SSet.{u+1}))) ≫
      nativeTotWeightedCellFamily A σ =
    (leftPointStdSimplexIso n).hom ≫
      SSet.yonedaEquiv.symm (nativeTotWeightedCellFunctor A σ |>.obj X |>.val) := by
  unfold nativeTotWeightedCellFamily
  have hshape :
      lift (SSet.const (ComposableArrows.mk₀ X))
          (𝟙 (join (Δ[0] : SSet.{u+1}) (Δ[n] : SSet.{u+1}))) ≫
          (nerve (CosimplicialObject (Complex A)) ◁ (leftPointStdSimplexIso n).hom) =
        (leftPointStdSimplexIso n).hom ≫
          lift (SSet.const (ComposableArrows.mk₀ X))
            (𝟙 (Δ[n+1] : SSet.{u+1})) := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro τ
    rfl
  rw [← Category.assoc, hshape, Category.assoc]
  exact congrArg ((leftPointStdSimplexIso n).hom ≫ ·)
    (strictSimplexFunctorEvaluation_atParameter A (Complex A)
      (nativeTotWeightedCellFunctor A σ) X)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
