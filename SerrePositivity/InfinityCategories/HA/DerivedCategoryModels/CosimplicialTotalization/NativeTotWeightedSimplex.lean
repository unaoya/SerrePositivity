module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.LiftedBKConeNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.WeightedConeComparisonStrictMap
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PrefixOverWeight

/-!
概要：元のnative Tot錐の指定入力の各射列でのweighted単体と厳密な全HA写像。
方針：指定prefixOverWeightに元のBK入力を合成し、同じ双方向自然性を適用。
規約：IS-W2 D01の既存構成の制限・自然性・貼り合わせ則。元の単体を選び直さない。
使われ方：HA 1.2.4、同じnative錐の各セルから全StrictCoherentFamilyへの接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
variable {A : Type u} [CommRing A]

/-- 元の図式射を、同じAsSmall添字の閉零図式の射へ送る。 -/
def liftedClosedDiagramMap {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    liftedClosedDiagram X ⟶ liftedClosedDiagram Y :=
  Functor.whiskerRight (Functor.whiskerLeft AsSmall.down f) (complexToClosed A)

/-- 同じ指定BK入力を、元の射列の初区間へ制限する。 -/
def nativeTotWeightedPrefix (X : CosimplicialObject (Complex A)) {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    simplexPrefixWeight n ⟶ σ ⋙
      simplicialHomDiagram (liftedClosedDiagram X)
        (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X)) ⋙ SSet.opFunctor :=
  prefixOverWeight σ ≫ Functor.whiskerLeft σ (liftedEnrichedBousfieldKanCone X)

/-- 同じ射列上の元のBK錐のcoherent比較の全HAデータ。 -/
def nativeTotWeightedSimplexData (X : CosimplicialObject (Complex A)) {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) : SimplexData A (Complex A) (n+1) :=
  coherentSimplexData (weightedConeSimplex (liftedClosedDiagram X)
    (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
    (nativeTotWeightedPrefix X σ))

/-- 元の射列への制限でも、指定BK入力の全自然性を保つ。 -/
theorem nativeTotWeightedPrefix_dinaturality
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    nativeTotWeightedPrefix X σ ≫ Functor.whiskerLeft σ
        (Functor.whiskerRight
          (weightedConeHomTargetMap (liftedClosedDiagramMap f)
            (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))) SSet.opFunctor) =
      nativeTotWeightedPrefix Y σ ≫ Functor.whiskerLeft σ
        (Functor.whiskerRight
          (weightedConeHomSourceMap ((complexToClosed A).map ((productTotalFunctor A).map f))
            (liftedClosedDiagram Y)) SSet.opFunctor) := by
  have h := congrArg (fun η => prefixOverWeight σ ≫ Functor.whiskerLeft σ η)
    (liftedEnrichedBousfieldKanCone_dinaturality f)
  simp only [Functor.whiskerLeft_comp, Category.assoc] at h
  exact h

/-- 同じ図式射のTot成分と各次数の成分は、元のweightedセルの全HA成分に可換する。 -/
def nativeTotWeightedSimplexMap
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    StrictSimplexMap A (Complex A) (nativeTotWeightedSimplexData X σ)
      (nativeTotWeightedSimplexData Y σ) :=
  weightedConeComparisonStrictMap (liftedClosedDiagramMap f)
    ((complexToClosed A).map ((productTotalFunctor A).map f))
    (nativeTotWeightedPrefix X σ) (nativeTotWeightedPrefix Y σ)
    (nativeTotWeightedPrefix_dinaturality f σ)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
