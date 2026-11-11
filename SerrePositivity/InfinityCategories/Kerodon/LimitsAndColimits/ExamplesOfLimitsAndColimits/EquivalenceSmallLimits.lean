module

public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalenceAllLimits
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitDiagramIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.AdjunctionLimits
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：元の全図式の小極限の保存と全同値による存在の輸送。
方針：任意小形状の指定全錐を保存し、逆関手の全図式を自然同型で回収する。
規約：小形状は u、標的は u+1。存在と保存を instance にしない。
使われ方：presentable 圏への完備性の輸送。

対応節は Kerodon 7.6（Tag 03E8）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits

/-- 概要：全小極限を元の全錐で保存すること。
方針：小形状とその持ち上げた全図式を量化する。
規約：任意の単体集合形状を扱う。
使われ方：右随伴と反映包含の保存性。 -/
@[kerodon 06BA]
def PreservesSmallLimits {C E : SSet.{u + 1}} (F : C ⟶ E) : Prop :=
  ∀ (K : SSet.{u}) (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone D), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone F c)

/-- 概要：右随伴は全小極限を保存する。
方針：任意形状の右随伴保存定理を元の小形状へ適用する。
規約：極限の存在は入力に追加しない。
使われ方：反映包含の各点計算。 -/
lemma adjunction_preservesSmallLimits {C E : SSet.{u + 1}}
    [Quasicategory C] [Quasicategory E] {L : C ⟶ E} {R : E ⟶ C}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R) : PreservesSmallLimits R := by
  intro K D c hc
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.mapJoinCone_isLimit_of_adjunction a c hc

/-- 概要：全小極限の存在は全同値で移る。
方針：逆像の図式の極限を順射で写し、元の図式を全自然同型で回収する。
規約：元の任意小図式を結論に保持する。
使われ方：Ind 反映模型からの完備性。 -/
lemma HasSmallLimits.of_equivalence {C E : SSet.{u + 1}}
    [Quasicategory C] [Quasicategory E] (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallLimits C)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence C E) : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallLimits E := by
  intro K D
  obtain ⟨c, hc⟩ := hC K (D ≫ e.inv)
  have ed : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((D ≫ e.inv) ≫ e.hom) D := by
    simpa only [Category.assoc, Category.comp_id] using e.invHomIso.precomp D
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasLimit_iff_of_functorIso ed).mp
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone e.hom c, (e.isLimitCone_iff c).mp hc⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallLimits export _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallLimits (of_equivalence)


end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits
