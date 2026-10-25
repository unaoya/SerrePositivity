module

public import SerrePositivity.InfinityCategories.F2.Presentable.Supply.LeftClassificationHomLifting
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorPullbackVertices
public import SerrePositivity.InfinityCategories.F1.Coherent.NerveHomEdgeNaturality
public import SerrePositivity.InfinityCategories.F1.Fibrations.FiberComparisonBaseChange

/-!
概要：left fibration の実底変換が、元の比較辺とその類に与える作用を固定する。
方針：元の豊穣 Hom の零次の底変換則を、coherent nerve の実辺の式へ移す。
規約：実際の fiberComparisonBaseChange を使う。
使われ方：P-12 の指定された分類 Hom と底変換の可換正方形への入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

local instance supplyLeftClassificationBaseChangeEdges_pullbackLeftFibration
    {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

/-- 概要：底変換後の元の coherent な辺は、実際の引き戻し比較の辺そのもの。
方針：元の相対 Hom の頂点の底変換則を豊穣単位からの射として読む。
規約：両端の辺の一次単体の厳密な等式。
使われ方：分類の底変換同型の自然性を元の実比較へ移す。 -/
lemma leftFibrationBaseChange_edge
    {E H B D : SSet.{u}} (p : E ⟶ B) (q : H ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ H) (hf : f ≫ q = p) (k : D ⟶ B) :
    (leftFibrationInfinityBaseChange k).app (Opposite.op ⦋1⦌)
      (leftFibrationInfinityEdge p q f hf).edge =
    (leftFibrationInfinityEdge (pullback.snd p k) (pullback.snd q k)
      (fiberComparisonBaseChange p q f hf k)
      (fiberComparisonBaseChange_projection p q f hf k)).edge := by
  apply coherentNerveMap_edge_of_homEquiv (leftFibrationBaseChangeEnriched k)
    (show leftFibrationObjectOf p ⟶ leftFibrationObjectOf q from Over.homMk f hf)
    (show leftFibrationBaseChangeObject k (leftFibrationObjectOf p) ⟶
      leftFibrationBaseChangeObject k (leftFibrationObjectOf q) from
      Over.homMk (fiberComparisonBaseChange p q f hf k)
        (fiberComparisonBaseChange_projection p q f hf k))
  apply (SSet.unitHomEquiv _).injective
  change (relativeFunctorPullback p q k).app (Opposite.op ⦋0⦌)
      (relativeFunctorVertex q p f hf) =
    relativeFunctorVertex (pullback.snd q k) (pullback.snd p k)
      (fiberComparisonBaseChange p q f hf k) (fiberComparisonBaseChange_projection p q f hf k)
  exact relativeFunctorPullback_vertex p q k f hf

/-- 概要：底変換の Hom 作用を元の引き戻しの頂点へ正規化すると実比較の辺の類となる。
方針：元の辺の底変換式を端点の指定等式で移し、ホモトピー圏へ送る。
規約：実比較と指定頂点等式を保持する。
使われ方：全分類同型の自然性を元の分類 Hom の等式へ戻す。 -/
lemma leftFibrationBaseChange_normalizedHom
    {E H B D : SSet.{u}} (p : E ⟶ B) (q : H ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ H) (hf : f ≫ q = p) (k : D ⟶ B) :
    normalizedVertexHomMap (leftFibrationInfinityBaseChange k)
      (x := leftFibrationInfinityVertex p) (y := leftFibrationInfinityVertex q)
      (leftFibrationInfinityBaseChange_vertex k (leftFibrationObjectOf p)).symm
      (leftFibrationInfinityBaseChange_vertex k (leftFibrationObjectOf q)).symm
      (Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q f hf).toTruncated) =
    Truncated.HomotopyCategory.homMk
      (leftFibrationInfinityEdge (pullback.snd p k) (pullback.snd q k)
        (fiberComparisonBaseChange p q f hf k)
        (fiberComparisonBaseChange_projection p q f hf k)).toTruncated := by
  have h : ((leftFibrationInfinityEdge p q f hf).map (leftFibrationInfinityBaseChange k)).ofEq
      (leftFibrationInfinityBaseChange_vertex k (leftFibrationObjectOf p))
      (leftFibrationInfinityBaseChange_vertex k (leftFibrationObjectOf q)) =
      leftFibrationInfinityEdge (pullback.snd p k) (pullback.snd q k)
        (fiberComparisonBaseChange p q f hf k)
        (fiberComparisonBaseChange_projection p q f hf k) := by
    apply SSet.Edge.ext
    exact leftFibrationBaseChange_edge p q f hf k
  have he := congrArg (fun e ↦ Truncated.HomotopyCategory.homMk e.toTruncated) h
  rw [homMk_edge_ofEq] at he
  exact he

end SerrePositivity.InfinityCategories.F2.Presentable
