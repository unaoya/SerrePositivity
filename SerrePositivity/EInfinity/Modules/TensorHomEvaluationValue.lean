module
public import SerrePositivity.EInfinity.Modules.TensorHomEvaluation

/-!
概要：元の全 frame Hom 評価の値を符号付き交換で明示する。
方針：実 Hom 同値の転置を戻し、左右のテンソル順序を同定する。
規約：HA 1.3.1.13、符号付き braiding を保持する。
使われ方：M10 の同じ全三相データを各対象で評価した係数の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory Opposite MonoidalCategory
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 概要：全単体の評価は元の加群射の評価の前に符号付き交換を置いた射。
方針：元の二つの転置の両逆を戻す。
規約：HA 1.3.1.13、実射の等式。使われ方：全要素図式の評価。 -/
lemma moduleTensorEvaluationHomMap_app (P Q : ModuleCategory A D) (x : D)
    (n : SimplexCategory)
    (f : ((moduleTensorSimplicesFunctor A D).obj P).obj n ⟶ Q) :
    (moduleTensorEvaluationHomMap A D P Q x).app (op n) f =
      (signedSwap ((moduleEvaluation A D x).obj P)
        ((BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj n))).hom ≫
          (moduleEvaluation A D x).map f := by
  let e := tensorHomEquiv ((moduleEvaluation A D x).obj P)
    ((BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj n))
    ((moduleEvaluation A D x).obj Q)
  have ht : e ((moduleTensorEvaluationHomMap A D P Q x).app (op n) f) =
      curryRight ((moduleEvaluation A D x).map f) :=
    (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A _ n).injective
      (moduleTensorEvaluationHomMap_transpose A D P Q x n f)
  calc
    _ = e.symm (curryRight ((moduleEvaluation A D x).map f)) :=
      (e.symm_apply_apply _).symm.trans (congrArg e.symm ht)
    _ = _ := by
      dsimp only [e]
      rw [tensorHomEquiv_uncurryRight, uncurryRight_curryRight]

end SerrePositivity.EInfinity.Modules
