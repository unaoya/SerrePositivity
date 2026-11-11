module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseInitialTerminal
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseSlices
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeOpposite

/-! # 普遍錐の宇宙比較

概要：図式と錐の ULift は極限性・余極限性を保ち反映する。
方針：実 slice/coslice の同型と、始・終対象性の境界充填の比較を使う。
規約：quasicategory 性は不要。使われ方：安定性の宇宙降下。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 同型は実終対象性を保ち反映する。 -/
lemma isTerminalVertex_iff_of_isIso {X Y : SSet.{u}} (q : X ⟶ Y) [IsIso q]
    (x : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (q.app (Opposite.op ⦋0⦌) x) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsTerminalVertex.map_of_isIso q, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_of_trivialKanFibration q⟩

/-- 図式上の実錐を持ち上げる。 -/
def JoinCone.ulift {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone ((SSet.uliftFunctor.{v, u}).map p) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSliceOverSimplexEquiv p 0 c

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone export _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone (ulift)


/-- 図式下の実余錐を持ち上げる。 -/
def JoinCocone.ulift {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone ((SSet.uliftFunctor.{v, u}).map p) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSliceUnderSimplexEquiv p 0 c

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone export _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone (ulift)


/-- 持ち上げた錐の頂点は元の実頂点の持ち上げである。 -/
lemma JoinCone.ulift_vertex {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    (JoinCone.ulift.{u, v} c).vertex = ULift.up c.vertex := by
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone export _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone (ulift_vertex)


/-- 持ち上げた余錐の頂点も元の実頂点の持ち上げである。 -/
lemma JoinCocone.ulift_vertex {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    (JoinCocone.ulift.{u, v} c).vertex = ULift.up c.vertex := by
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone export _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone (ulift_vertex)


/-- 同じ錐の持ち上げは極限性を保ち反映する。 -/
lemma isLimitCone_iff_ulift {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (JoinCone.ulift.{u, v} c) :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isTerminalVertex_iff_ulift.{u, v} (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) c).trans
    (isTerminalVertex_iff_of_isIso (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSliceOverIso.{u, v} p).hom (ULift.up c))

/-- 同じ余錐の持ち上げは余極限性を保ち反映する。 -/
lemma isColimitCone_iff_ulift {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (JoinCocone.ulift.{u, v} c) :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isInitialVertex_iff_ulift.{u, v} (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) c).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isInitialVertex_iff_of_isIso (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSliceUnderIso.{u, v} p).hom (ULift.up c))

/-- 持ち上げた図式の全ての錐は小さい錐の持ち上げである。 -/
lemma JoinCone.ulift_surjective {K X : SSet.{u}} (p : K ⟶ X) :
    Function.Surjective (JoinCone.ulift.{u, v} (p := p)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSliceOverSimplexEquiv p 0).surjective

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone export _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone (ulift_surjective)


/-- 持ち上げた図式の全ての余錐は小さい余錐の持ち上げである。 -/
lemma JoinCocone.ulift_surjective {K X : SSet.{u}} (p : K ⟶ X) :
    Function.Surjective (JoinCocone.ulift.{u, v} (p := p)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSliceUnderSimplexEquiv p 0).surjective

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone export _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone (ulift_surjective)


/-- 極限の存在は持ち上げた図式で保ち反映される。 -/
lemma hasLimit_iff_ulift {K X : SSet.{u}} (p : K ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit p ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit ((SSet.uliftFunctor.{v, u}).map p) := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c.ulift, (isLimitCone_iff_ulift c).1 hc⟩
  · rintro ⟨c, hc⟩
    obtain ⟨d, rfl⟩ := JoinCone.ulift_surjective p c
    exact ⟨d, (isLimitCone_iff_ulift d).2 hc⟩

/-- 余極限の存在は持ち上げた図式で保ち反映される。 -/
lemma hasColimit_iff_ulift {K X : SSet.{u}} (p : K ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit ((SSet.uliftFunctor.{v, u}).map p) := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c.ulift, (isColimitCone_iff_ulift c).1 hc⟩
  · rintro ⟨c, hc⟩
    obtain ⟨d, rfl⟩ := JoinCocone.ulift_surjective p c
    exact ⟨d, (isColimitCone_iff_ulift d).2 hc⟩

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
