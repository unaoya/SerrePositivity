module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativePointFunctorIso
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorAnodyneRestriction
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.PreFiberKan

/-!
概要：left anodyne な点包含での相対関手評価の全境界持ち上げ。
方針：点への相対制限と一点上の評価同型を合成する。
規約：評価点の像を別の表示で指定する場合も、fiber の包含後の式で移送する。
使われ方：Kerodon §5.3.1、strict transport の始対象での評価の同値性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：点包含で相対制限して評価すると、その点の像での元の相対評価となる。
方針：fiber の包含後に前合成と頂点評価の自然性を使う。
規約：点包含 i は任意で、充填性は不要。
使われ方：Kerodon §5.3.1、点への相対制限を元の fiber への評価として読む式。 -/
lemma relativeFunctorPre_point_evaluate {A E B : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (i : (Δ[0] : SSet.{u}) ⟶ A) :
    relativeFunctorPre p a i ≫ (relativePointFunctorIso p (i ≫ a)).hom =
      relativeFunctorEvaluate p a (i.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)) := by
  apply vertexFiber_hom_ext p
    (a.app (Opposite.op ⦋0⦌) (i.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)))
  change (vertexFiberι ((ihom A).map p) (functorVertex a) ≫ (pre i).app E) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) =
    vertexFiberι ((ihom A).map p) (functorVertex a) ≫
      evaluateFunctorAt (i.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0))
  rw [Category.assoc, evaluateFunctorAt_pre]

/-- 概要：left anodyne な点包含での相対評価は trivial Kan fibration。
方針：相対制限の全境界持ち上げに続けて、一点上の評価の同型を合成する。
規約：底の quasicategory 性は要求しない。
使われ方：Kerodon §5.3.1、始対象を持つ通常の圏上の相対関手の評価。 -/
lemma relativeFunctorEvaluate_trivialKanFibration_of_pointMap {A E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (a : A ⟶ B)
    (i : (Δ[0] : SSet.{u}) ⟶ A) (hi : leftAnodyneExtensions i) :
    TrivialKanFibration (relativeFunctorEvaluate p a
      (i.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0))) := by
  rw [← relativeFunctorPre_point_evaluate p a i]
  exact ⟨trivialKanFibrations.comp_mem _ _
    (relativeFunctorPre_trivialKanFibration p a i hi).mem
    (TrivialKanFibration.mem (p := (relativePointFunctorIso p (i ≫ a)).hom))⟩

/-- 概要：底の頂点の表示を同定した相対評価も全境界を持ち上げる。
方針：底の頂点の等式を消去し、fiber の包含後の式から元の評価射と一致させる。
規約：f の定義に使われる固定条件の証明の選択には依存しない。
使われ方：Kerodon §5.3.1、strict transport の評価の底を元の対象の頂点で表す。 -/
lemma relativeFunctorEvaluate_trivialKanFibration_of_identification {A E B : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (v : A _⦋0⦌) (b : B _⦋0⦌)
    (hb : a.app (Opposite.op ⦋0⦌) v = b)
    (f : relativeFunctorSpace p a ⟶ vertexFiber p b)
    (hf : f ≫ vertexFiberι p b =
      vertexFiberι ((ihom A).map p) (functorVertex a) ≫ evaluateFunctorAt v)
    (he : TrivialKanFibration (relativeFunctorEvaluate p a v)) : TrivialKanFibration f := by
  subst b
  have h : f = relativeFunctorEvaluate p a v :=
    vertexFiber_hom_ext _ _ (hf.trans (relativeFunctorEvaluate_ι p a v).symm)
  rw [h]
  exact he

end SerrePositivity.InfinityCategories
