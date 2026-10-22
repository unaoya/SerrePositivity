module
public import SerrePositivity.InfinityCategories.Stable.LoopSourceUniversalUnit

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
namespace SerrePositivity.InfinityCategories

/-- 同じ comma の実矢印と始対象性の比較。 -/
lemma QCatEquivalence.toAdjunction_unitHom_isIso {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y) :
    IsIso e.toAdjunction.unitHom := by
  change IsIso ((qcatHomFunctor X X).map e.adjointEquivalence.unit.hom)
  infer_instance

/-- 同じ comma の実矢印と始対象性の比較。 -/
lemma loopSourceUnit_isIso {X : SSet.{u}} [Quasicategory X] [HasZeroVertex X]
    (s : X ⟶ loopDiagrams X) (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0)) :
    IsIso (loopSourceUnit s hs hΩ) :=
  QCatEquivalence.toAdjunction_unitHom_isIso _
end SerrePositivity.InfinityCategories
