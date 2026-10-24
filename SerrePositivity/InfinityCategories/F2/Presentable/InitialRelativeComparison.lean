module

public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationInitialEvaluation
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence
public import SerrePositivity.InfinityCategories.Core.FullyFaithful

/-!
概要：始対象で一致する左ファイブレーション上の持ち上げを相対関手空間で比較する。
方針：始対象での評価の自明 Kan 性から、そのホモトピー圏の充満忠実性を使う。
規約：比較は底を固定した相対関手空間内の同型。
使われ方：全解錐から作る輸送比較の分裂三角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：始対象で同じ点を持つ二つの全持ち上げは相対関手空間で同型。
方針：始対象評価の自明 Kan fibration の充満忠実性で同じ評価点の恒等同型を戻す。
規約：元の底の図式 a と始対象 v を固定する。
使われ方：coslice の恒等点で一致する輸送と射影の全自然な比較。 -/
def relativeFunctorIso_of_initial_evaluation_eq
    {A E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    (a : A ⟶ B) (v : A _⦋0⦌) (hv : IsInitialVertex v)
    (W V : A ⟶ E) (hW : W ≫ p = a) (hV : V ≫ p = a)
    (he : W.app (Opposite.op ⦋0⦌) v = V.app (Opposite.op ⦋0⦌) v) :
    VertexIso (relativeFunctorVertex p a W hW) (relativeFunctorVertex p a V hV) := by
  let e := relativeFunctorEvaluate p a v
  have : TrivialKanFibration e := relativeFunctorEvaluate_initial_trivialKanFibration p a v hv
  have h : e.app (Opposite.op ⦋0⦌) (relativeFunctorVertex p a W hW) =
      e.app (Opposite.op ⦋0⦌) (relativeFunctorVertex p a V hV) := by
    apply Subtype.ext
    change (evaluateFunctorAt v).app (Opposite.op ⦋0⦌) (functorVertex W) =
      (evaluateFunctorAt v).app (Opposite.op ⦋0⦌) (functorVertex V)
    rw [evaluateFunctorAt_functorVertex, evaluateFunctorAt_functorVertex]
    exact he
  exact (isFullyFaithful_of_trivialKanFibration e).toHoFullyFaithful.preimageIso
    (eqToIso (congrArg HomotopyCategory.mk h))

end SerrePositivity.InfinityCategories.F2.Presentable
