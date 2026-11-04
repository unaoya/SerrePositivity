module
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.FractionFamilyCoslice
public import SerrePositivity.KST.Fibration.PointSourceFatRestriction
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.FractionMappingComparison
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.LeftIntervalEquivalence

/-! # 同じ全族の coslice 制限と、既存の両端固定分数評価の実ホモトピー -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {X Q : SSet.{u}} [Quasicategory Q] (F : X ⟶ Q)
  (W : Set (X _⦋1⦌)) (hF : InvertsEdges F W) (x y : X _⦋0⦌)

/-- 元の全分数矢印族を両端固定の部分族へ制限すると、既存の同じ分数評価を厳密に回収する。 -/
theorem fractionFamilyFatDiagram_fixed_recover :
    leftIntervalFatPrism (fixedMarkedSpans X W x y) ≫
      (fatJoinMap (𝟙 (Δ[0] : SSet.{u})) (fixedMarkedSpanToFamily X W x y) ≫
        fractionFamilyFatDiagram F W hF x) = intervalMappingUncurry
          (fixedFractionEvaluation F W hF x y) := by
  rw [fractionFamilyFatDiagram, pointSourceFatDiagram_restrict_recover,
    fractionFamilyArrow, ← Category.assoc, fixedMarkedSpanToFamily_inclusion]
  exact (congrArg uncurry (fixedFractionEvaluation_inclusion F W hF x y)).symm

/-- 同じ全 coslice 関手の固定終点 fiber での評価は、既存の分数評価と実ホモトピーで一致する。 -/
def fixedFractionCosliceComparisonHomotopy :
    SSet.Homotopy
      (fixedFractionCosliceEvaluation F W hF x y ≫
        cosliceFiberToIntervalMappingSpace (F.app (Opposite.op ⦋0⦌) x)
          (F.app (Opposite.op ⦋0⦌) y)) (fixedFractionEvaluation F W hF x y) :=
  (fractionFamilyCosliceData F W hF x).toFiberIntervalHomotopy
    (fixedMarkedSpanToFamily X W x y) (fixedMarkedSpanToFamily_target F W x y)
    (fixedFractionEvaluation F W hF x y) (fractionFamilyFatDiagram_fixed_recover F W hF x y)

/-- 比較は同じ写像空間への全関手 ∞ 圏内の同型としても保持する。 -/
def fixedFractionCosliceComparisonIso :
    FunctorIso
      (fixedFractionCosliceEvaluation F W hF x y ≫
        cosliceFiberToIntervalMappingSpace (F.app (Opposite.op ⦋0⦌) x)
          (F.app (Opposite.op ⦋0⦌) y)) (fixedFractionEvaluation F W hF x y) :=
  functorIsoOfSimplicialHomotopy (fixedFractionCosliceComparisonHomotopy F W hF x y)

end SerrePositivity.KST.Fibration
