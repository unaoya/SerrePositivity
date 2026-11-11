module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementParameterEvaluation

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorElementPinchedMap_app {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    (normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋n⦌) c =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := Complex A) (E := Complex A) (x := X) (x' := X)
      (homPostcompose X
        ((normalizedTensorElementEvaluation A X Y).app (c.obj (Fin.last n))))).app
          (Opposite.op ⦋n⦌) (normalizedTensorElementUniversalSimplex A X Y c) := by
  have he := normalizedTensorElementUniversalFamily_evaluation A X Y c
  rw [normalizedTensorHomPinchedSimplex_reindex] at he
  have h := congrArg (fun f : SSet.uliftFunctor.{u + 1, u}.obj (Δ[n] : SSet.{u}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (Complex A) X Y =>
      f.app (Opposite.op ⦋n⦌) (ULift.up (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)))) he
  rw [normalizedTensorHomPinchedSimplex_id_eval] at h
  exact (congrArg ((normalizedTensorPinchedIso A X Y).hom.app (Opposite.op ⦋n⦌))
    (normalizedTensorElementParameterMap_app A X Y c)).trans h.symm

end SerrePositivity.EInfinity.ComplexLimits
