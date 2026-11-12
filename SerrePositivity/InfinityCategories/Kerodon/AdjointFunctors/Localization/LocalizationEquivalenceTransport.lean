module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Localization
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorComposition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceCalculus

/-!
# 標的の実 ∞ 圏同値に沿う局所化の普遍性の移送

概要：同じ反転関手全部分圏への実際の前合成を同値に沿って比較する。
方針：全部分圏の包含で厳密な合成を回収し、元の前合成同値を消去する。
規約：元の指定辺集合・元の射と可逆二胞体を保持する。
使われ方：実 hammock nerve と既存 localizationNerve の普遍性の同値。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory MonoidalClosed _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable {X D Q : SSet.{u}} [SSet.Quasicategory D] [SSet.Quasicategory Q]
  (q : X ⟶ D) (W : Set (X _⦋1⦌)) (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges q W) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence D Q)

lemma localizationPrecomposition_comp_equivalence (E : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition (q ≫ e.hom) W (hq.comp e.hom) E =
      (pre e.hom).app E ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition q W hq E := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X E W).ι).mp
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition_ι, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition_ι,
    pre_map, NatTrans.comp_app]

include hq in
lemma isLocalization_comp_equivalence_iff :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (q ≫ e.hom) W ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization q W := by
  constructor
  · rintro ⟨hcomp, h⟩
    refine ⟨hq, fun E _ => ?_⟩
    have hh : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition (q ≫ e.hom) W (hq.comp e.hom) E) := h E
    rw [localizationPrecomposition_comp_equivalence q W hq e E] at hh
    exact (e.precompose E).isQCatEquivalence.cancel_left hh
  · rintro ⟨hq', h⟩
    refine ⟨hq.comp e.hom, fun E _ => ?_⟩
    rw [localizationPrecomposition_comp_equivalence q W hq e E]
    exact (e.precompose E).isQCatEquivalence.comp (h E)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
