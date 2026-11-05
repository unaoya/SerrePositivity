module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.Fibration
variable {X Q : SSet.{u}} [Quasicategory Q] (F : X ⟶ Q)
  (W : Set (X _⦋1⦌)) (hF : InvertsEdges F W) (x y : X _⦋0⦌)

/-- 元の全分数矢印族を両端固定の部分族へ制限すると、既存の同じ分数評価を厳密に回収する。 -/
theorem fractionFamilyFatDiagram_fixed_recover :
    leftIntervalFatPrism (fixedMarkedSpans X W x y) ≫
      (fatJoinMap (𝟙 (Δ[0] : SSet.{u})) (fixedMarkedSpanToFamily X W x y) ≫
        _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionFamilyFatDiagram F W hF x) = intervalMappingUncurry
          (fixedFractionEvaluation F W hF x y) := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionFamilyFatDiagram, pointSourceFatDiagram_restrict_recover,
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionFamilyArrow, ← Category.assoc, fixedMarkedSpanToFamily_inclusion]
  exact (congrArg uncurry (fixedFractionEvaluation_inclusion F W hF x y)).symm

/-- 同じ全 coslice 関手の固定終点 fiber での評価は、既存の分数評価と実ホモトピーで一致する。 -/
def fixedFractionCosliceComparisonHomotopy :
    SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceEvaluation F W hF x y ≫
        cosliceFiberToIntervalMappingSpace (F.app (Opposite.op ⦋0⦌) x)
          (F.app (Opposite.op ⦋0⦌) y)) (fixedFractionEvaluation F W hF x y) :=
  (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionFamilyCosliceData F W hF x).toFiberIntervalHomotopy
    (fixedMarkedSpanToFamily X W x y) (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedMarkedSpanToFamily_target F W x y)
    (fixedFractionEvaluation F W hF x y) (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionFamilyFatDiagram_fixed_recover F W hF x y)

/-- 比較は同じ写像空間への全関手 ∞ 圏内の同型としても保持する。 -/
def fixedFractionCosliceComparisonIso :
    FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceEvaluation F W hF x y ≫
        cosliceFiberToIntervalMappingSpace (F.app (Opposite.op ⦋0⦌) x)
          (F.app (Opposite.op ⦋0⦌) y)) (fixedFractionEvaluation F W hF x y) :=
  functorIsoOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceComparisonHomotopy F W hF x y)

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceComparisonHomotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fixedFractionCosliceComparisonHomotopy := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceComparisonHomotopy

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceComparisonIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fixedFractionCosliceComparisonIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceComparisonIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionFamilyFatDiagram_fixed_recover := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionFamilyFatDiagram_fixed_recover

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fixedFractionCosliceComparisonIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceComparisonIso._proof_1
