module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndCardinalChange
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleFunctor
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafPointwiseColimits
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafAllSmallLimits
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：元の全図式の小余極限の存在と accessibility によって presentable ∞ 圏を定義する。
方針：添字を宇宙 u、標的を u+1 に固定し、全ての小さい単体集合形状を量化する。
規約：余極限の存在・保存は追加の instance とせず、指定された全余錐の性質で扱う。
使われ方：HTT 5.5.1 の前層・Ind の presentable 性、極限と随伴関手定理。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
open _root_.SerrePositivity.InfinityCategories

/-- 宇宙 u の任意の全図式の native な余極限が、元の宇宙 u+1 の標的に存在する。 -/
@[kerodon 06B7]
def HasSmallColimits (C : SSet.{u + 1}) : Prop :=
  ∀ (K : SSet.{u}) (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit D

/-- 宇宙 u の任意の全図式の native な極限が、元の宇宙 u+1 の標的に存在する。 -/
@[kerodon 06B7]
def HasSmallLimits (C : SSet.{u + 1}) : Prop :=
  ∀ (K : SSet.{u}) (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit D

/-- 指定された元の任意の小さい全余極限余錐を、同じ全関手で保存すること。 -/
@[kerodon 06BA]
def PreservesSmallColimits {C E : SSet.{u + 1}} (F : C ⟶ E) : Prop :=
  ∀ (K : SSet.{u}) (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone F c)

/-- presentable は、同じ宇宙に関して accessible で、全ての小余極限を持つこと。 -/
@[kerodon 06ND]
def IsPresentable (C : SSet.{u + 1}) [Quasicategory C] : Prop :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible C ∧ HasSmallColimits C

lemma IsPresentable.isAccessible {C : SSet.{u + 1}} [Quasicategory C]
    (h : IsPresentable C) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible C := h.1

lemma IsPresentable.hasSmallColimits {C : SSet.{u + 1}} [Quasicategory C]
    (h : IsPresentable C) : HasSmallColimits C := h.2

/-- 小余極限は、同じ任意の濃度に対する小さい filtered 余極限の存在を含む。 -/
lemma HasSmallColimits.hasSmallKappaFilteredColimits {C : SSet.{u + 1}}
    (h : HasSmallColimits C) (κ : Cardinal.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ C := by
  intro K hK hκ D
  exact h K D

/-- 全小余極限を保つ元の関手は、全ての濃度について filtered 余極限を保つ。 -/
lemma PreservesSmallColimits.isKappaAccessibleFunctor {C E : SSet.{u + 1}}
    {F : C ⟶ E} (h : PreservesSmallColimits F) (κ : Cardinal.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ F := by
  intro K hK hκ D c hc
  exact h K D c hc

/-- 小余極限を保つ元の関手は accessible。 -/
@[kerodon 06LC]
lemma PreservesSmallColimits.isAccessibleFunctor {C E : SSet.{u + 1}}
    {F : C ⟶ E} (h : PreservesSmallColimits F) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor F :=
  ⟨Cardinal.aleph0, Cardinal.isRegular_aleph0, h.isKappaAccessibleFunctor _⟩

/-- 元の前層 ∞ 圏は、任意の小さい底に対して全ての小余極限を持つ。 -/
lemma presheaf_hasSmallColimits (A : SSet.{u}) : HasSmallColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A) := by
  intro K D
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinity_hasColimit D

/-- 元の前層 ∞ 圏は、任意の小さい底に対して全ての小極限を持つ。 -/
lemma presheaf_hasSmallLimits (A : SSet.{u}) : HasSmallLimits (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A) := by
  intro K D
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinity_hasLimit D

/-- 元の空間 ∞ 圏は、全ての小余極限を持つ。 -/
lemma space_hasSmallColimits : HasSmallColimits _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} := by
  intro K D
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.hasColimit_coherentSpaceDiagram D

/-- 元の空間 ∞ 圏は、全ての小極限を持つ。 -/
@[kerodon 05QQ]
lemma space_hasSmallLimits : HasSmallLimits _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} := by
  intro K D
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.hasLimit_coherentSpaceDiagram D

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
