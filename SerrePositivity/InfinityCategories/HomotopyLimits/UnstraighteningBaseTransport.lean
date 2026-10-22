module

public import SerrePositivity.InfinityCategories.HomotopyLimits.DiagonalEvaluationTransport

/-!
概要：元の全変換の点評価は、元の底辺による両図式の標準輸送と両立する。
方針：四辺を保持した元の正方形の全輸送比較を、同じ元の評価作用へ移す。
規約：全変換空間を一つのパラメータとして扱い、点ごとの自然性を仮定しない。
使われ方：Yoneda 評価の第一変数自然性の、反変輸送側との接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の変換族と底辺から、元の四辺を保持した輸送正方形を構成する。 -/
def unstraighteningTransportSquare {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) {a b : B _⦋0⦌} (e : SSet.Edge a b) :
    TransportIntervalSquare (leftUnstraighteningTransformationSpace F G)
      (F.app _ a) (F.app _ b) (G.app _ a) (G.app _ b) where
  bottom := SSet.const (intervalMappingVertexOfEdge (e.map F))
  top := SSet.const (intervalMappingVertexOfEdge (e.map G))
  left := unstraighteningEvaluationInterval F G a
  right := unstraighteningEvaluationInterval F G b
  square := unstraighteningBaseSquare F G e
  zero := unstraighteningBaseSquare_zero F G e
  one := unstraighteningBaseSquare_one F G e
  inner_zero := unstraighteningBaseSquare_inner_zero F G e
  inner_one := unstraighteningBaseSquare_inner_one F G e

/-- 元の全 fiber Hom の評価は、同じ元の底辺に沿う両端の標準輸送と関手同型まで可換。 -/
def unstraighteningFiberEvaluation_baseTransportIso {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) {a b : B _⦋0⦌} (e : SSet.Edge a b)
    (v : (vertexFiber pointedSpaceProjection (F.app (Opposite.op ⦋0⦌) a)) _⦋0⦌) :
    FunctorIso
      (leftUnstraighteningMappingFiberHom F G b ≫ evaluateFunctorAt
        ((edgeTransport pointedSpaceProjection (e.map F)).app (Opposite.op ⦋0⦌) v))
      (leftUnstraighteningMappingFiberHom F G a ≫ evaluateFunctorAt v ≫
        edgeTransport pointedSpaceProjection (e.map G)) := by
  let p := pointedSpaceProjection
  let s := unstraighteningTransportSquare F G e
  have hb : FunctorIso (diagonalFiberTransport p (SSet.const v) s.bottom)
      (SSet.const ((edgeTransport p (e.map F)).app (Opposite.op ⦋0⦌) v)) := by
    have h := diagonalFiberTransport_edgeIso p (e.map F)
      (SSet.const (X := leftUnstraighteningTransformationSpace F G) v)
    simp only [SSet.const_comp] at h
    exact h
  have ha := unstraighteningFiberEvaluation_diagonalIso F G a v
  have hc := unstraighteningFiberEvaluation_diagonalIso F G b
    ((edgeTransport p (e.map F)).app (Opposite.op ⦋0⦌) v)
  have h₂ := diagonalFiberTransport_sourceIso p hb s.right
  have h₃ := diagonalFiberTransport_edgeIso p (e.map G)
    (diagonalFiberTransport p (SSet.const v) s.left)
  have h₄ := ha.postcomp (edgeTransport p (e.map G))
  have h := hc ≪≫ h₂.symm ≪≫ s.transportIso p (SSet.const v) ≪≫ h₃ ≪≫ h₄.symm
  simp only [Category.assoc] at h
  exact h

end SerrePositivity.InfinityCategories.HomotopyLimits
