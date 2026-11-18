module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementParameterEvaluation

/-!
概要：元の大域 pinched 評価の全単体は、同じ終端普遍単体の実評価像である。
方針：終端の普遍評価式を恒等単体で評価し、元のパラメータ射の直接値へ戻す。
規約：元の大域写像・全単体列・同じ終端評価射を保持する。
使われ方：大域 prism の評価端点を元の実 pinched 族へ同定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorElementPinchedMap_app {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋n⦌) c =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := Complex A) (E := Complex A) (x := X) (x' := X)
      (homPostcompose X
        ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluation A X Y).app (c.obj (Fin.last n))))).app
          (Opposite.op ⦋n⦌) (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalSimplex A X Y c) := by
  have he := _root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalFamily_evaluation A X Y c
  rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorHomPinchedSimplex_reindex] at he
  have h := congrArg (fun f : SSet.uliftFunctor.{u + 1, u}.obj (Δ[n] : SSet.{u}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (Complex A) X Y =>
      f.app (Opposite.op ⦋n⦌) (ULift.up (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)))) he
  rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorHomPinchedSimplex_id_eval] at h
  exact (congrArg ((_root_.SerrePositivity.ComplexLimits.normalizedTensorPinchedIso A X Y).hom.app (Opposite.op ⦋n⦌))
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementParameterMap_app A X Y c)).trans h.symm

end SerrePositivity.ComplexLimits
