module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredHomotopyRetracts
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredInfinity
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：filtered 性と κ-filtered 性は ∞ 圏の同値で不変。
方針：指定した同値の両合成をホモトピー retract の輸送に使う。
規約：κ の正則性を輸送の条件に加えない。
使われ方：Kerodon 9.1.1.19（Tag 02PK）、filtered な添字の表示の変更。

対応節は Kerodon 9.1（Tag 05WY）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories

/-- 概要：同値な ∞ 圏は filtered 性を共有する。
方針：同値の両合成を coherent なホモトピー retract として使う。
規約：同型に限定しない。使われ方：filtered な添字の同値による変更。 -/
@[kerodon 02PK]
lemma isFilteredInfinity_iff_of_equivalence {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence C D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity C ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity D := by
  constructor
  · intro _
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isFilteredInfinity_of_homotopyRetract e.inv e.hom e.invHomIso
  · intro _
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isFilteredInfinity_of_homotopyRetract e.hom e.inv e.homInvIso

/-- 概要：同値な ∞ 圏は任意の同じ κ に対して κ-filtered 性を共有する。
方針：κ-small な形状を保つホモトピー retract の両向きの輸送。
規約：κ の正則性は不要。使われ方：Indκ の添字の同値による変更。 -/
@[kerodon 02PK]
lemma isKappaFiltered_iff_of_equivalence {κ : Cardinal.{u}} {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence C D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ C ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ D := by
  constructor
  · intro _
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_of_homotopyRetract e.inv e.hom e.invHomIso
  · intro _
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_of_homotopyRetract e.hom e.inv e.homInvIso

/-- 概要：指定した関手が同値なら filtered 性を保ち反映する。
方針：同値の逆データを選んで同値不変性に渡す。
規約：追加の保存性を仮定しない。使われ方：比較関手への適用。 -/
lemma isFilteredInfinity_iff_of_isQCatEquivalence {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] {f : C ⟶ D} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity C ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity D := isFilteredInfinity_iff_of_equivalence hf.choose

/-- 概要：指定した関手が同値なら κ-filtered 性を保ち反映する。
方針：選んだ逆データに関する不変性を使う。
規約：元の κ を保つ。使われ方：κ 版の比較関手への適用。 -/
@[kerodon 02PK]
lemma isKappaFiltered_iff_of_isQCatEquivalence {κ : Cardinal.{u}} {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] {f : C ⟶ D} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ C ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ D := isKappaFiltered_iff_of_equivalence hf.choose

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.3.1.11"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_iff_of_isQCatEquivalence
