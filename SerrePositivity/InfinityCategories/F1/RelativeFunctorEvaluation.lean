module

public import SerrePositivity.InfinityCategories.F1.RelativeFunctorSpace

/-!
概要：相対関手単体集合の指定した頂点での fiber 内の評価。
方針：内部 Hom の評価を fiber の固定条件に沿って元の射の fiber へ持ち上げる。
規約：底の頂点は指定図式 a による評価点の像。
使われ方：Kerodon §5.3.1、strict transport と元の fibration の fiber の比較射。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：相対関手を A の頂点 v で評価すると、a(v) 上の fiber に値を持つ。
方針：評価の後合成自然性と fiber の定値条件を使って持ち上げる。
規約：p や a に充填性は要求しない。
使われ方：Kerodon §5.3.1、undercategory の恒等射での strict transport の評価。 -/
def relativeFunctorEvaluate {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) (v : A _⦋0⦌) :
    relativeFunctorSpace p a ⟶ vertexFiber p (a.app (Opposite.op ⦋0⦌) v) :=
  vertexFiberLift _ _
    (vertexFiberι ((ihom A).map p) (functorVertex a) ≫ evaluateFunctorAt v) (by
      have he : evaluateFunctorAt (Y := E) v ≫ p =
          (ihom A).map p ≫ evaluateFunctorAt v := rfl
      rw [Category.assoc, he, ← Category.assoc, vertexFiberι_comp, SSet.const_comp]
      rw [evaluateFunctorAt_functorVertex])

/-- 概要：fiber 内の相対評価を元の全空間に含めると通常の関手評価となる。
方針：fiber への持ち上げの包含後の式を使う。
規約：評価点 v と底の図式 a は任意。
使われ方：Kerodon §5.3.1、strict transport の評価の計算則。 -/
lemma relativeFunctorEvaluate_ι {A E B : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (v : A _⦋0⦌) :
    relativeFunctorEvaluate p a v ≫ vertexFiberι p (a.app (Opposite.op ⦋0⦌) v) =
      vertexFiberι ((ihom A).map p) (functorVertex a) ≫ evaluateFunctorAt v := rfl

end SerrePositivity.InfinityCategories
