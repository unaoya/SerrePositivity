module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FunctorLoopSection
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopEquivalenceCofiberExists
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorComposition

/-!
概要：元の loop 同値を全関手圏へ移し、全 cofiber を構成する。
方針：同じ実切断の評価式と、同値の内部 Hom 後合成への保存を使う。
規約：一般安定性や有限余極限は仮定しない。
使われ方：一般零角の図式の比較と、その回転の全単体族。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：関手圏へ移した loop 族も同じ終点の厳密切断である。
方針：元の切断等式を内部 Hom の後合成で写す。
規約：端点を同型に置き換えない。使われ方：関手圏の native loop 入力。 -/
lemma functorLoopSection_target {K X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X] (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X)
    (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorLoopSection K s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation ((ihom K).obj X) 1 1 =
      𝟙 ((ihom K).obj X) := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorLoopSection_evaluation, hs, CategoryTheory.Functor.map_id]

/-- 概要：関手圏の同じ実 loop 関手も同値である。
方針：厳密な評価式で元の loop 関手の後合成に同定する。
規約：始域 K は任意。使われ方：関手区間での切除と回転。 -/
lemma functorLoopSection_loop_isQCatEquivalence {K X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X] (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorLoopSection K s ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation ((ihom K).obj X) 0 0) := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorLoopSection_evaluation]
  exact hΩ.postcompose K

/-- 概要：任意の関手圏の全辺が同じ指定辺の cofiber 四角形を持つ。
方針：pointed 性・有限極限・実 loop 同値を全関手圏へ移して適用する。
規約：点ごとの cofiber の任意選択を自然な族と見なさない。
使われ方：一般零角の比較に対する cofiber と回転の自然な族。 -/
lemma functorCofiberSquare_nonempty_of_loopEquivalence (K : SSet.{u}) {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X]
    (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0))
    {x y : ((ihom K).obj X) _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj ((ihom K).obj X)) x y) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare f) := by
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasZeroVertex_functorCategory K X
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteLimits_functorCategory K X
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSquare_nonempty_of_loopEquivalence (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorLoopSection K s)
    (functorLoopSection_target s hs) (functorLoopSection_loop_isQCatEquivalence s hΩ) f

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
