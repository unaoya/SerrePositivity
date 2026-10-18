module

public import SerrePositivity.InfinityCategories.F1.LeftStrictTransport
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorEvaluation

/-!
概要：strict transport を undercategory の恒等射で評価する比較射。
方針：恒等射の nerve の頂点で相対関手を評価し、元の fibration の fiber に持ち上げる。
規約：ここでは比較射を構成し、その同値性は別に証明する。
使われ方：Kerodon §5.3.1、strict transport 表現から元の fiber への比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：c/C の恒等射 id_c が表す nerve の頂点。
方針：under の対象 Under.mk id_c を nerve の零単体にする。
規約：底の対象 c は通常の圏の対象。
使われ方：Kerodon §5.3.1、strict transport の元の fiber への評価点。 -/
def strictTransportUnderIdentityVertex {C : Type u} [Category.{u} C] (c : C) :
    (nerve (Under c)) _⦋0⦌ :=
  (nerveEquiv (C := Under c)).symm (Under.mk (𝟙 c))

/-- 概要：under の恒等射の頂点は底で c の頂点に写る。
方針：nerve の零単体上の関手の作用を計算する。
規約：底の頂点は nerveEquiv による標準表示。
使われ方：Kerodon §5.3.1、strict transport の評価の fiber の固定。 -/
lemma strictTransportUnderIdentityVertex_projection {C : Type u} [Category.{u} C] (c : C) :
    (nerveMap (Under.forget c)).app (Opposite.op ⦋0⦌) (strictTransportUnderIdentityVertex c) =
      (nerveEquiv (C := C)).symm c := by
  change (nerveMap (Under.forget c)).app (Opposite.op ⦋0⦌)
    (ComposableArrows.mk₀ (Under.mk (𝟙 c))) = ComposableArrows.mk₀ c
  rw [nerveMap_app_mk₀]
  rfl

/-- 概要：strict transport を恒等射で評価すると元の fibration の c 上の fiber を得る。
方針：相対関手の評価の底を恒等射の射影の式で同定し、fiber へ持ち上げる。
規約：比較射の構成には p の left fibration 性は不要。
使われ方：Kerodon §5.3.1、strict transport の fiber 比較射。 -/
def leftStrictTransportEvaluate {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) (c : C) :
    leftStrictTransport p c ⟶ vertexFiber p ((nerveEquiv (C := C)).symm c) :=
  vertexFiberLift p _
    (vertexFiberι ((ihom (nerve (Under c))).map p)
      (functorVertex (nerveMap (Under.forget c))) ≫
        evaluateFunctorAt (strictTransportUnderIdentityVertex c)) (by
      rw [← relativeFunctorEvaluate_ι, Category.assoc, vertexFiberι_comp,
        SSet.comp_const, strictTransportUnderIdentityVertex_projection])

/-- 概要：strict transport の fiber 内評価を全空間へ含めると通常の関手評価。
方針：fiber への持ち上げの包含後の計算則を使う。
規約：評価点は undercategory の恒等射。
使われ方：Kerodon §5.3.1、strict transport と元の fiber の比較の計算。 -/
lemma leftStrictTransportEvaluate_ι {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) (c : C) :
    leftStrictTransportEvaluate p c ≫ vertexFiberι p ((nerveEquiv (C := C)).symm c) =
      vertexFiberι ((ihom (nerve (Under c))).map p)
        (functorVertex (nerveMap (Under.forget c))) ≫
          evaluateFunctorAt (strictTransportUnderIdentityVertex c) := rfl

end SerrePositivity.InfinityCategories
