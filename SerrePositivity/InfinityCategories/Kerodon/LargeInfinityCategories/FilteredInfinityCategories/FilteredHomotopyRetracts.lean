module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeExistenceTransport
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredInfinity
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.SmallSimplicialShapes

/-!
概要：filtered 性と κ-filtered 性は ∞ 圏のホモトピー retract で保たれる。
方針：図式の余錐を送って戻した後、合成と恒等の関手同型で制限を厳密化する。
規約：単なる頂点ごとの同型の族ではなく coherent な関手同型を使う。
使われ方：filtered な添字 ∞ 圏の同値不変性。

対応節は Kerodon 9.1（Tag 05WY）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories

/-- 概要：filtered ∞ 圏のホモトピー retract は filtered。
方針：図式を包含し、余錐を戻してから元の図式への関手同型を延長する。
規約：retract の合成に厳密な恒等の等式を要求しない。
使われ方：Kerodon 9.1.1.19（Tag 02PK） の同値による輸送。 -/
lemma isFilteredInfinity_of_homotopyRetract {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity C]
    (i : D ⟶ C) (r : C ⟶ D) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (i ≫ r) (𝟙 D)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity D where
  cocone_nonempty f := by
    obtain ⟨c⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity.cocone_nonempty (f ≫ i)
    have hc : Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ r))) := ⟨⟨c.val ≫ r, by
      rw [← Category.assoc, c.property, Category.assoc]⟩⟩
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f ≫ (i ≫ r)) f := by
      simpa only [Category.comp_id] using _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e f
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nonempty_joinCocone_of_functorIso he hc

/-- 概要：κ-filtered ∞ 圏のホモトピー retract は κ-filtered。
方針：κ-small な形状を保ち、戻した余錐の制限を元の図式へ厳密化する。
規約：κ の正則性は不要。使われ方：κ-filtered 性の同値不変性。 -/
lemma isKappaFiltered_of_homotopyRetract {κ : Cardinal.{u}} {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ C]
    (i : D ⟶ C) (r : C ⟶ D) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (i ≫ r) (𝟙 D)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ D where
  cocone_nonempty hK f := by
    obtain ⟨c⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered.cocone_nonempty hK (f ≫ i)
    have hc : Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ r))) := ⟨⟨c.val ≫ r, by
      rw [← Category.assoc, c.property, Category.assoc]⟩⟩
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f ≫ (i ≫ r)) f := by
      simpa only [Category.comp_id] using _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e f
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nonempty_joinCocone_of_functorIso he hc

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
