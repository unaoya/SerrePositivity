module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSourceUniversalUnit

/-!
概要：固定始域 comma の実矢印と始対象性、指定 loop 単位の可逆性。
方針：実ホモトピーの Ho 自然性と left fibration の可逆性反映を使う。
規約：生の関手値の端点を保つ。使われ方：元の loop 四角形の押し出し性の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 同じ comma の実矢印と始対象性の比較。 -/
lemma QCatEquivalence.toAdjunction_unitHom_isIso {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) :
    IsIso e.toAdjunction.unitHom := by
  change IsIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor X X).map e.adjointEquivalence.unit.hom)
  infer_instance

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.QCatEquivalence (toAdjunction_unitHom_isIso)


/-- 同じ comma の実矢印と始対象性の比較。 -/
lemma loopSourceUnit_isIso {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X]
    (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)) :
    IsIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopSourceUnit s hs hΩ) :=
  QCatEquivalence.toAdjunction_unitHom_isIso _
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
