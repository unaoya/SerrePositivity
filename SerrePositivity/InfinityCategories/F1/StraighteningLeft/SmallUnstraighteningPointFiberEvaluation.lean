module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallUnstraighteningFiberHomNaturality
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorPointFiberEvaluation

/-!
概要：小さい unstraightening の同じ指定点での評価を、元の大きい fiber の評価へ移す。
方針：全 Hom の可換式に評価を続け、同型の往復と宇宙移送の評価公式を消去する。
規約：評価点は同じ fiber の縮小同型の像そのもの。別の点を選び直さない。
使われ方：全体からの Yoneda 恒等点評価を、c1 の実際の普遍輸送の評価に戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ頂点での評価は、値の後合成と厳密に可換。 -/
lemma evaluateFunctorAt_post {A X Y : SSet.{u}} (f : X ⟶ Y) (a : A _⦋0⦌) :
    (ihom A).map f ≫ evaluateFunctorAt a = evaluateFunctorAt a ≫ f := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro F
  rfl

/-- 内部 Hom の宇宙移送は、同じ持ち上げた頂点での評価を厳密に保つ。 -/
lemma uliftFunctorSpaceIso_evaluate {A X : SSet.{u}} (a : A _⦋0⦌) :
    (uliftFunctorSpaceIso.{u, v} A X).hom ≫ evaluateFunctorAt (ULift.up a) =
      (SSet.uliftFunctor.{v, u}).map (evaluateFunctorAt (Y := X) a) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro F
  rfl

/-- 相対 Hom の縮小同型は、同じ fiber の指定点での評価を全パラメーターで保つ。 -/
lemma smallLeftUnstraighteningRelativeFunctorIso_pointEvaluation {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌)
    (v : (vertexFiber (smallLeftUnstraighteningProjection F) b) _⦋0⦌) :
    (smallLeftUnstraighteningRelativeFunctorIso F G).hom ≫
      relativeFunctorFiberHom (leftUnstraighteningProjection F)
        (leftUnstraighteningProjection G) (ULift.up b) ≫
      evaluateFunctorAt ((smallLeftUnstraighteningFiberIso F b).hom.app
        (Opposite.op ⦋0⦌) (ULift.up v)) =
    (SSet.uliftFunctor.{u + 1, u}).map
        (relativeFunctorFiberHom (smallLeftUnstraighteningProjection F)
          (smallLeftUnstraighteningProjection G) b ≫ evaluateFunctorAt v) ≫
      (smallLeftUnstraighteningFiberIso G b).hom := by
  let w := (smallLeftUnstraighteningFiberIso F b).hom.app (Opposite.op ⦋0⦌) (ULift.up v)
  have hw : (smallLeftUnstraighteningFiberIso F b).inv.app (Opposite.op ⦋0⦌) w =
      ULift.up v :=
    congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) (ULift.up v))
      (smallLeftUnstraighteningFiberIso F b).hom_inv_id
  rw [← Category.assoc, smallLeftUnstraighteningRelativeFunctorIso_fiberHom]
  simp only [Category.assoc]
  rw [evaluateFunctorAt_post]
  rw [← Category.assoc _ (evaluateFunctorAt w) (smallLeftUnstraighteningFiberIso G b).hom,
    evaluateFunctorAt_pre, hw]
  have hEval := uliftFunctorSpaceIso_evaluate.{u, u + 1}
    (X := vertexFiber (smallLeftUnstraighteningProjection G) b) v
  have hComp := congrArg (fun f ↦
    (SSet.uliftFunctor.{u + 1, u}).map
      (relativeFunctorFiberHom (smallLeftUnstraighteningProjection F)
        (smallLeftUnstraighteningProjection G) b) ≫ f ≫
      (smallLeftUnstraighteningFiberIso G b).hom) hEval
  simpa only [Functor.map_comp, Category.assoc] using hComp

end SerrePositivity.InfinityCategories
