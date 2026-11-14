module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftUnitInvertible
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftCanonical
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeColimitFunctorIso

/-!
概要：可逆な相対左 Kan 単位から元の関手の標準局所条件を得る。
方針：局所輸送の可逆性と余錐全体の同型による相対余極限の保存を使う。
規約：元の標準余錐と任意の inner U を扱う。
使われ方：相対左 Kan 関手の全部分圏内での厳密化。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：可逆な相対左 Kan 単位を持つ関手は標準局所条件を満たす。
方針：局所輸送の同型で U 余極限性を標準余錐へ戻す。
規約：包含の充満忠実性は不要で、指定単位の可逆性を入力する。
使われ方：指定変換の模型から元の関手の頂点条件へ移る。 -/
lemma kanRelativeLeftKanExtension_canonical_of_unit_isIso {K C D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) [InnerFibration U]
    (δ : K ⟶ C) {F₀ : K ⟶ D} {F : C ⟶ D} (β : SSet.Homotopy F₀ (δ ≫ F))
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtension U δ F₀ F β)
    (hi : IsIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtendedFrom U δ F := by
  intro c
  obtain ⟨t, ht⟩ := hβ c
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftTransport_isIso_of_unit_isIso t hi
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_of_functorIso U ht
    (asIso (SSet.Truncated.HomotopyCategory.homMk t.edge))

/-- 概要：関手圏の同型は元の標準相対左 Kan 条件を保つ。
方針：標準局所余錐の射への前合成で全余錐の同型を作る。
規約：図式の各点の同型を独立に選ばない。
使われ方：元と像を固定した同値による図式の厳密化。 -/
lemma kanIsRelativeLeftKanExtendedFrom_of_functorIso {K C D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) [InnerFibration U]
    (δ : K ⟶ C) {F G : C ⟶ D} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtendedFrom U δ F) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtendedFrom U δ G := by
  intro c
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_of_functorIso U (hF c)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonicalCoconeMap δ c))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "4.3.2.6" (partial := component) "仮定：内ファイブレーションと関手準圏で同型な二関手（HTT の (1) と一致）。結論：関手同型とその逆に適用すると相対左 Kan 条件が同値（結論 (1) が一致。図式全体の圏同値での移送 (2) は含まない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsRelativeLeftKanExtendedFrom_of_functorIso
