module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.NativeFilteredPreservation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.Definition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：小さい κ-compact な全部分生成圏によって κ-accessible ∞ 圏を定義する。
方針：元の各対象を頂点とする単一の小さい κ-filtered 余極限表示を要求する。
規約：κ と生成圏と添字は u、標的は u+1。同値や Kan 拡張の結論は仮定しない。
使われ方：HTT 5.4.2、Indκ との比較および presentable ∞ 圏。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 指定した小さい生成圏の像から、同じ対象を頂点とする κ-filtered 表示を持つこと。 -/
def HasKappaFilteredGeneratorPresentation (κ : Cardinal.{u})
    {A : SSet.{u}} {C : SSet.{u + 1}}
    (i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C) (x : C _⦋0⦌) : Prop :=
  ∃ (I : SSet.{u}) (hI : Quasicategory I),
    letI := hI
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ I ∧
    ∃ a : I ⟶ A, ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map a ≫ i),
      c.vertex = x ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c

/-- 小さい全部分圏の像が κ-compact であり、各対象を単一 κ-filtered 余極限で生成する。 -/
structure IsKappaCompactGenerating (κ : Cardinal.{u})
    {A : SSet.{u}} [Quasicategory A] {C : SSet.{u + 1}} [Quasicategory C]
    (i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C) : Prop where
  fullyFaithful : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful i
  compact : ∀ a : A _⦋0⦌,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (i.app (Opposite.op ⦋0⦌) (ULift.up a))
  presentation : ∀ x, HasKappaFilteredGeneratorPresentation κ i x

/-- 正則 κ、κ-filtered 余極限の存在、小さい κ-compact 生成圏による accessibility。 -/
@[kerodon 06K6]
def IsKappaAccessible (κ : Cardinal.{u}) (C : SSet.{u + 1}) [Quasicategory C] : Prop :=
  κ.IsRegular ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ C ∧
    ∃ (A : SSet.{u}) (hA : Quasicategory A),
      letI := hA
      ∃ i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C, IsKappaCompactGenerating κ i

/-- ある宇宙 u の正則濃度について κ-accessible な宇宙 u+1 の ∞ 圏。 -/
@[kerodon 06KF]
def IsAccessible (C : SSet.{u + 1}) [Quasicategory C] : Prop :=
  ∃ κ : Cardinal.{u}, IsKappaAccessible κ C

lemma IsKappaAccessible.isAccessible {κ : Cardinal.{u}} {C : SSet.{u + 1}}
    [Quasicategory C] (h : IsKappaAccessible κ C) : IsAccessible C := ⟨κ, h⟩

lemma IsKappaAccessible.hasSmallKappaFilteredColimits {κ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] (h : IsKappaAccessible κ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ C := h.2.1

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
