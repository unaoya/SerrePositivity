module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeInitialSimplex

/-!
概要：始点を取り替えた coherent simplex の構成を、全ての面・退化と整合させる。
方針：最小点の全パラメータ座標の自然性と元の simplex の前合成を使う。
規約：添字変換は始点を固定する prependOrderHom によるもの。
使われ方：HTT 4.2.4.1 の錐全体の単体的な族への組立て。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 初点から出る新しい Hom は、元の simplex とパラメータの同時の制限に自然。 -/
lemma coneInitialHead_reindex (x : C) {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (T : (SimplicialNerve C) _⦋n + 1⦌)
    (p : Δ[n] ⟶ (SimplicialCategory.sHom x (T.obj ⟨ULift.up 0⟩)).op)
    (j : Fin (m + 1)) :
    nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstReindexFunctor α.toOrderHom j) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneInitialHead x T p (α.toOrderHom j) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneInitialHead x
        ((SimplicialThickening.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom α.toOrderHom).uliftMap).comp SSet T)
        (stdSimplex.map α ≫ p) j := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneInitialHead
  erw [comp_lift_assoc]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pathFirstParameterMap_reindex, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap_pre]
  rfl

/-- 始点を取り替える操作は、始点固定の全ての面・退化と厳密に可換。 -/
lemma coneInitialSimplex_reindex (x : C) {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (T : (SimplicialNerve C) _⦋n + 1⦌)
    (p : Δ[n] ⟶ (SimplicialCategory.sHom x (T.obj ⟨ULift.up 0⟩)).op) :
    (SimplicialThickening.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom α.toOrderHom).uliftMap).comp SSet
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneInitialSimplex x T p) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneInitialSimplex x
        ((SimplicialThickening.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom α.toOrderHom).uliftMap).comp SSet T)
        (stdSimplex.map α ≫ p) := by
  refine EnrichedFunctor.ext SSet (fun i ↦ ?_) (fun i j ↦ ?_)
  · rcases i with ⟨⟨i⟩⟩
    induction i using Fin.cases <;> rfl
  · rcases i with ⟨⟨i⟩⟩
    rcases j with ⟨⟨j⟩⟩
    induction i using Fin.cases <;> induction j using Fin.cases
    all_goals simp only [eqToHom_refl, Category.comp_id]
    case zero.zero =>
      change (_ ≫ toUnit _) ≫ eId SSet x = toUnit _ ≫ eId SSet x
      rw [comp_toUnit]
    case zero.succ j =>
      change nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstReindexFunctor α.toOrderHom j) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneInitialHead x T p (α.toOrderHom j) = _
      exact coneInitialHead_reindex x α T p j
    case succ.zero i =>
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro P
      have h := Path.le (P.obj 0)
      change i.succ ≤ 0 at h
      simp at h
    case succ.succ i j => rfl

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
