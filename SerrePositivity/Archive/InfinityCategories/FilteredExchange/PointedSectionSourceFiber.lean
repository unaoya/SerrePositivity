module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentFiberPointedSourceIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorInitialEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.VertexFiberNervePullback
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeCospanSectionFibrations

/-!
概要：辺上の pointed 切断を、明示した始点の元の小さい fiber へ写す同値。
方針：始点評価、頂点等式による fiber の輸送、元の始点族の同型の逆を合成する。
規約：頂点等式を入力に保持。使われ方：二辺の切断模型を実際の fiber 二脚へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌)
  (e : (Δ[1] : SSet.{u + 1}) ⟶ SpaceInfinity.{u})
  (hv : e.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0) =
    G.app (Opposite.op ⦋0⦌) (ULift.up b))

local instance : KanComplex (vertexFiber (smallLeftUnstraighteningProjection G) b) :=
  vertexFiber_kanComplex_of_leftFibration _ _

/-- 明示した元の始点の小さい fiber へ、同じ始点評価を戻す。 -/
def pointedSectionSourceFiber : relativeFunctorSpace pointedSpaceProjection e ⟶
    coherentNativeTriangleFiberParameters G b :=
  relativeFunctorEvaluate pointedSpaceProjection e (stdSimplex.obj₀Equiv.symm 0) ≫
    eqToHom (congrArg (vertexFiber pointedSpaceProjection) hv) ≫
      (coherentFiberPointedSourceIso G b).inv

/-- 元の小さい fiber への写像の一致は、同じ始点評価の厳密な包含式から導ける。 -/
lemma pointedSectionSourceFiber_eq_of_evaluate_ι {A : SSet.{u + 1}}
    (W : A ⟶ relativeFunctorSpace pointedSpaceProjection e)
    (w : A ⟶ coherentNativeTriangleFiberParameters G b)
    (h : W ≫ relativeFunctorEvaluate pointedSpaceProjection e (stdSimplex.obj₀Equiv.symm 0) ≫
      vertexFiberι pointedSpaceProjection
        (e.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)) =
      w ≫ coherentCospanFiberPointedSource G b) :
    W ≫ pointedSectionSourceFiber G b e hv = w := by
  have he : W ≫ relativeFunctorEvaluate pointedSpaceProjection e (stdSimplex.obj₀Equiv.symm 0) ≫
      eqToHom (congrArg (vertexFiber pointedSpaceProjection) hv) =
      w ≫ (coherentFiberPointedSourceIso G b).hom := by
    apply vertexFiber_hom_ext pointedSpaceProjection (G.app (Opposite.op ⦋0⦌) (ULift.up b))
    simp only [Category.assoc, vertexFiberTransport_ι pointedSpaceProjection hv,
      coherentFiberPointedSourceIso_hom_ι]
    exact h
  unfold pointedSectionSourceFiber
  have hc := congrArg (fun k => k ≫ (coherentFiberPointedSourceIso G b).inv) he
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hc

/-- 始点を明示して元の小さい fiber へ戻す写像は同値。 -/
lemma pointedSectionSourceFiber_isQCatEquivalence :
    IsQCatEquivalence (pointedSectionSourceFiber G b e hv) := by
  have hi : leftAnodyneExtensions
      (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u + 1}) ⟶ Δ[1]) := by
    have hd : scaffoldFirstVertex.{u + 1} 1 = stdSimplex.δ (1 : Fin 2) := by
      apply SSet.yonedaEquiv.injective
      decide
    rw [← hd]
    exact scaffoldFirstVertex_leftAnodyne 1
  have ht := relativeFunctorEvaluate_trivialKanFibration_of_pointMap
    pointedSpaceProjection e (stdSimplex.δ (1 : Fin 2)) hi
  have hp : (stdSimplex.δ (1 : Fin 2) :
      (Δ[0] : SSet.{u + 1}) ⟶ Δ[1]).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm 0) = stdSimplex.obj₀Equiv.symm (0 : Fin 2) := by decide
  rw [hp] at ht
  have := ht
  have he := isQCatEquivalence_of_trivialKanFibration
    (relativeFunctorEvaluate pointedSpaceProjection e (stdSimplex.obj₀Equiv.symm 0))
  exact he.comp ((qCatEquivalenceOfIso
    (eqToIso (congrArg (vertexFiber pointedSpaceProjection) hv))).isQCatEquivalence.comp
      (qCatEquivalenceOfIso (coherentFiberPointedSourceIso G b).symm).isQCatEquivalence)

end SerrePositivity.InfinityCategories.F2
