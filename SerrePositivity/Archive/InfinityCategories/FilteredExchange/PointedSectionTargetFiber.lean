module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentFiberPointedSourceIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorInitialEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.VertexFiberNervePullback
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeCospanSectionFibrations

/-!
概要：辺上の pointed 切断を、明示した終点の元の小さい fiber へ写す Kan fibration。
方針：終点評価、頂点等式による fiber の輸送、元の終点族の同型の逆を合成する。
規約：頂点等式を入力に保持。使われ方：二辺の切断模型を実際の fiber 二脚へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌)
  (e : (Δ[1] : SSet.{u + 1}) ⟶ SpaceInfinity.{u})
  (hv : e.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1) =
    G.app (Opposite.op ⦋0⦌) (ULift.up b))

local instance : KanComplex (vertexFiber (smallLeftUnstraighteningProjection G) b) :=
  vertexFiber_kanComplex_of_leftFibration _ _

/-- 明示した元の終点の小さい fiber へ、同じ終点評価を戻す。 -/
def pointedSectionTargetFiber : relativeFunctorSpace pointedSpaceProjection e ⟶
    coherentNativeTriangleFiberParameters G b :=
  relativeFunctorEvaluate pointedSpaceProjection e (stdSimplex.obj₀Equiv.symm 1) ≫
    eqToHom (congrArg (vertexFiber pointedSpaceProjection) hv) ≫
      (coherentFiberPointedSourceIso G b).inv

/-- 元の小さい fiber への写像の一致は、同じ終点評価の厳密な包含式から導ける。 -/
lemma pointedSectionTargetFiber_eq_of_evaluate_ι {A : SSet.{u + 1}}
    (W : A ⟶ relativeFunctorSpace pointedSpaceProjection e)
    (w : A ⟶ coherentNativeTriangleFiberParameters G b)
    (h : W ≫ relativeFunctorEvaluate pointedSpaceProjection e (stdSimplex.obj₀Equiv.symm 1) ≫
      vertexFiberι pointedSpaceProjection
        (e.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1)) =
      w ≫ coherentCospanFiberPointedSource G b) :
    W ≫ pointedSectionTargetFiber G b e hv = w := by
  have he : W ≫ relativeFunctorEvaluate pointedSpaceProjection e (stdSimplex.obj₀Equiv.symm 1) ≫
      eqToHom (congrArg (vertexFiber pointedSpaceProjection) hv) =
      w ≫ (coherentFiberPointedSourceIso G b).hom := by
    apply vertexFiber_hom_ext pointedSpaceProjection (G.app (Opposite.op ⦋0⦌) (ULift.up b))
    simp only [Category.assoc, vertexFiberTransport_ι pointedSpaceProjection hv,
      coherentFiberPointedSourceIso_hom_ι]
    exact h
  unfold pointedSectionTargetFiber
  have hc := congrArg (fun k => k ≫ (coherentFiberPointedSourceIso G b).inv) he
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hc

/-- 元の終点へ戻す評価写像は Kan fibration。 -/
lemma pointedSectionTargetFiber_fibration :
    Fibration (pointedSectionTargetFiber G b e hv) := by
  have : Fibration (relativeFunctorPre pointedSpaceProjection e (stdSimplex.δ (0 : Fin 2))) :=
    relativeFunctorPre_fibration _ _ _
  have he := relativeFunctorPre_point_evaluate pointedSpaceProjection e
    (stdSimplex.δ (0 : Fin 2))
  have hp : (stdSimplex.δ (0 : Fin 2) :
      (Δ[0] : SSet.{u + 1}) ⟶ Δ[1]).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm 0) = stdSimplex.obj₀Equiv.symm (1 : Fin 2) := by decide
  have ht : Fibration (relativeFunctorEvaluate pointedSpaceProjection e
      ((stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u + 1}) ⟶ Δ[1]).app
        (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0))) := by
    rw [← he]
    infer_instance
  have : Fibration
      (relativeFunctorEvaluate pointedSpaceProjection e (stdSimplex.obj₀Equiv.symm 1)) := by
    rw [hp] at ht
    exact ht
  unfold pointedSectionTargetFiber
  infer_instance

end SerrePositivity.InfinityCategories.F2
