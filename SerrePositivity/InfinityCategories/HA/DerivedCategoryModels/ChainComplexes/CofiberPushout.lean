module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.CofiberBoundaryJoinFaces

/-! # 標準 cofiber 余錐の普遍性

概要：複体の dg nerve における標準 cofiber 正方形が押し出しであることを証明する。
方針：指定余錐を最初の頂点に持つ全ての coslice 境界を、二セルの明示解で直接充填する。
規約：HTT §1.2.13、HA Proposition 1.3.1.10。使われ方：D(S) の cofiber と安定性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes
open _root_.CategoryTheory _root_.SerrePositivity.DifferentialGraded
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] {A B C : _root_.SerrePositivity.DifferentialGraded.Complex S}

/-- 標準 cofiber 余錐は coslice の始対象である。 -/
lemma standardCofiberCocone_isColimit (f : A ⟶ B) (g : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberCocone f g) := by
  intro n b hb
  let F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryJoinFiller f g b hb
  have hfaces := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryJoinFiller_faces f g b hb
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cosliceJoinBoundaryFaces_fixed _ b F hfaces), ?_⟩
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceUnderCurry_boundary_of_joinFaces _ b F hfaces

/-- 標準 mapping cone による cofiber 正方形は実際の ∞ 押し出しである。 -/
lemma standardCofiberSquare_isPushout (f : A ⟶ B) (g : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare f g) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberCocone_isColimit f g

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.3.2.17" (partial := component) "仮定：可換環上の複体の二射（Lean が強い：任意の加法圏ではない）。結論：mapping cone を頂点とする dg nerve の押し出しで、片側が零なら対応する cofiber を表す（Lean が弱い：HA の E(1) テンソルによる通常の押し出しとの比較はない）。"] _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare_isPushout
