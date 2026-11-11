module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.RepresentationFamilyWitness
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorParameterizedPrismNaturality

/-!
概要：一般の表現間の相対射の実現をパラメーターで制限する。
方針：同じ制限射を prism の三条件へ同時に前合成する。
規約：相対射や変換の族を別々に選び直さない。
使われ方：普遍的な写像空間の族を任意の入力族へ戻す。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：実現の証拠は任意のパラメーター制限を厳密に保つ。
方針：始点・終点・底に同じ制限射を前合成する。
規約：制限射の単射性や同値性を要求しない。
使われ方：写像空間全体の比較を各族へ制限する。 -/
def TransportRepresentationFamilyWitness.comp {E F B K L : SSet.{u + 1}}
    {p : E ⟶ B} {q : F ⟶ B} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    {R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p} {S : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation q}
    {t : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace R.diagram S.diagram} {f : E ⊗ K ⟶ F}
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportRepresentationFamilyWitness R S t f) (i : L ⟶ K) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportRepresentationFamilyWitness R S (i ≫ t) ((E ◁ i) ≫ f) where
  prism := ((Δ[1] ⊗ E) ◁ i) ≫ w.prism
  source := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismEndpoint_parameter_naturality, Category.assoc, w.source,
      ← Category.assoc, whiskerLeft_fst]
  target := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismEndpoint_parameter_naturality, Category.assoc, w.target,
      ← Category.assoc]
  projection := by
    rw [Category.assoc, w.projection, ← Category.assoc]
    have hn : ((Δ[1] ⊗ E) ◁ i) ≫ ((Δ[1] ◁ p) ▷ K) =
        ((Δ[1] ◁ p) ▷ L) ≫ ((Δ[1] ⊗ B) ◁ i) := by
      apply SSet.hom_ext; intro n; rfl
    rw [hn, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism_parameter,
      ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportRepresentationFamilyWitness export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportRepresentationFamilyWitness (comp)


end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
