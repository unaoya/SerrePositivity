module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndCorepresentability
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CorepresentabilityEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleIndRepresentation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndCardinalChange
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.EquivalenceSmallLimits

/-!
概要：小極限を持つ accessible 圏の accessible な極限保存関手の余表現可能性。
方針：関手と圏の濃度をそろえ、Ind 模型上の全自然な retract を分裂して元へ移す。
規約：余表現対象と比較同型の存在を追加仮定にしない。
使われ方：HTT 5.5.2.7 と presentable 圏の随伴関手定理。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：accessible な小極限保存関手は元の accessible かつ完備な圏の対象で余表現可能。
方針：同じ濃度の Ind 模型へ引き戻し、構成した余表現対象を全同値で送る。
規約：小極限の存在と保存は元の宇宙の全錐について要求する。
使われ方：左随伴の存在に必要な空間値関手の余表現可能性。 -/
lemma accessible_preservesLimits_isCorepresentable
    {C : SSet.{u + 1}} [Quasicategory C] (F : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (hCa : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible C) (hCl : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallLimits C)
    (hFa : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor F) (hFl : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallLimits F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsCorepresentableSmallSpaceFunctor F := by
  obtain ⟨μ, _, hμF⟩ := hFa
  obtain ⟨κ, hμκ, hκC⟩ := hCa.exists_larger μ
  have : Fact κ.IsRegular := ⟨hκC.1⟩
  obtain ⟨A, hA, i, e, _, he, _⟩ := hκC.exists_indRepresentation
  have := hA
  have hκF : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ F := hμF.of_le hμκ.le
  have hF' : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (e.hom ≫ F) := he.comp hκF
  have hC' : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallLimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A) := hCl.of_equivalence e.symm
  have hl' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallLimits (e.hom ≫ F) := by
    intro K D c hc
    have h := hFl K (D ≫ e.hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone e.hom c) ((e.isLimitCone_iff c).mp hc)
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_iff_of_cone_val_eq
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (e.hom ≫ F) c) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone F (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone e.hom c))
      (Category.assoc c.val e.hom F).symm).mpr h
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.isCorepresentable_of_equivalence_restriction e F
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ind_corepresentable_of_continuous_preservesLimits κ A hC' (e.hom ≫ F) hF' hl')

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.5.2.7"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.accessible_preservesLimits_isCorepresentable
