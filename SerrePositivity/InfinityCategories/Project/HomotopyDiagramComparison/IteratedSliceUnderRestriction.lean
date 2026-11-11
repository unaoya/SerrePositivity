module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.IteratedSliceUnderIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialRestrictionBaseEvaluation

/-!
概要：展開した図式から元の左因子への制限を反復 coslice の射影に同定する。
方針：元の固定図式と可変終点を同じ join の再結合で保持する。
規約：充填条件を追加仮定しない。使われ方：HTT 5.5.4 の局所同値の pushout 保存。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
variable {K L X A A' : SSet.{u}} {p : K ⟶ X} (q : L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p)

/-- 元の左因子へ制限し、固定条件で終域を元の coslice に移す。 -/
def uncurriedSliceUnderRestriction : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry q) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry q) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K L) ≫
    eqToHom (congrArg (fun f : K ⟶ X ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed q))

/-- 元の図式への制限は左因子の包含への前合成として展開される。 -/
lemma uncurriedSliceUnderRestriction_uncurry (s : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry q)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (s ≫ uncurriedSliceUnderRestriction q) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K L) (𝟙 A) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry s := by
  rw [uncurriedSliceUnderRestriction, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceUnderUncurry_eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed q),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_restrict]

/-- 順方向の族の制限は元の反復 coslice の射影。 -/
lemma iteratedSliceUnderForwardFamily_restriction (s : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder q) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.iteratedSliceUnderForwardFamily q s ≫ uncurriedSliceUnderRestriction q =
      s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection q := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_injective p
  rw [uncurriedSliceUnderRestriction_uncurry, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.iteratedSliceUnderForwardFamily_uncurry,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinAssociator_outerPair, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection]

/-- 反復 coslice の同型は元の図式への制限と射影を対応させる。 -/
lemma iteratedSliceUnderIso_restriction :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.iteratedSliceUnderIso q).hom ≫ uncurriedSliceUnderRestriction q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection q := by
  simpa only [Category.id_comp, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.iteratedSliceUnderIso, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.iteratedSliceUnderMap] using
    iteratedSliceUnderForwardFamily_restriction q (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder q))

/-- 元の左因子への制限は可変終点の射影を保つ。 -/
lemma uncurriedSliceUnderRestriction_projection :
    uncurriedSliceUnderRestriction q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry q) := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.iteratedSliceUnderIso q).hom).1
  rw [← Category.assoc, iteratedSliceUnderIso_restriction]
  exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.iteratedSliceUnderIso_projection q).symm

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
