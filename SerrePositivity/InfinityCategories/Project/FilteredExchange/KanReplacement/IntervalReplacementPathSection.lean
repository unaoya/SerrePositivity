module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathReplacement
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalReplacementKanComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalReplacementPathIso
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalReplacementSection

/-!
概要：元の置換 path の切断上での全円柱を定値円柱へ厳密に同定する。
方針：元の定値 path 座標と curry の往復。
規約：全時刻・全単体を保持。使われ方：指定同型の切断上での簡約。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {X Y : SSet.{u}} [KanComplex Y] (f : X ⟶ Y)

/-- 概要：切断上の元の全 path 座標は元の射の像の定値 path。
方針：標準比較同型と可逆 path の定値切断。規約：射の等式。使われ方：円柱の簡約。 -/
lemma intervalReplacementSection_path :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementSection f ≫ pullback.fst ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app Y) f =
      f ≫ curry (snd (Δ[1] : SSet.{u}) Y) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementSection, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.equivalenceIntervalReplacementIso_fst,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection, pullback.lift_fst,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.equivalencePathRefl_ι]

/-- 概要：元の置換円柱は切断上で全時刻定値。
方針：元の path 座標の等式を uncurry。規約：厳密な円柱。使われ方：指定値の簡約。 -/
lemma intervalReplacementCanonicalPathHomotopy_section :
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementSection f ▷ (Δ[1] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementCanonicalPathHomotopy f).h = fst X (Δ[1] : SSet.{u}) ≫ f := by
  have hswap : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementSection f ▷ (Δ[1] : SSet.{u})) ≫
      (β_ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacement f) (Δ[1] : SSet.{u})).hom =
    (β_ X (Δ[1] : SSet.{u})).hom ≫ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementSection f) := rfl
  change (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementSection f ▷ (Δ[1] : SSet.{u})) ≫
    (β_ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacement f) (Δ[1] : SSet.{u})).hom ≫ uncurry (pullback.fst _ f) = _
  rw [← Category.assoc, hswap, Category.assoc, ← uncurry_natural_left,
    intervalReplacementSection_path, uncurry_natural_left, uncurry_curry]
  rfl

/-- 概要：任意の前合成でも切断上の元の円柱は定値。
方針：円柱の前合成と元の全時刻の式。規約：指定射を保持。使われ方：左脚への制限。 -/
lemma intervalReplacementCanonicalPathHomotopy_section_precomp {A : SSet.{u}} (a : A ⟶ X) :
    ((a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementSection f) ▷ (Δ[1] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementCanonicalPathHomotopy f).h = fst A (Δ[1] : SSet.{u}) ≫ a ≫ f := by
  rw [comp_whiskerRight, Category.assoc, intervalReplacementCanonicalPathHomotopy_section]
  rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange
