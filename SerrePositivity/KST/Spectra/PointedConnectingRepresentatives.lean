module

public import SerrePositivity.KST.Spectra.PointedFibrationBoundary

/-!
概要：標準基点での連結準同型の値を任意の相対ホーン充填の最後の面で代表する。
方針：fiber の基点を明示して移し、公開連結射の基点比較の順逆を消す。
規約：底の代表の基点は全空間の基点の像。標準基点への移送を式に残す。
使われ方：Goerss–Jardine I §8、VIII §1。セル境界の局所的な連結射の実計算。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace BoundaryLift

variable {E B : PointedSimplicialSet.{u}} {p : E ⟶ B} {n : ℕ}
  {s : B.right.PtSimplex (n + 1) (p.right.app _ E.basepoint)}

/-- 概要：相対ホーン充填の最後の面を標準基点の pointed fiber の単体へ戻す。
方針：基礎の単体の射を保ち、ofVertex の基点の等式で境界条件だけを移す。
規約：選んだ充填の最後の面そのものを使用する。
使われ方：Kerodon §3.2.5、Goerss–Jardine I §8。公開連結射の代表。 -/
def pointedBoundary (L : BoundaryLift p.right E.basepoint s) :
    (pointedFiber p).right.PtSimplex n (pointedFiber p).basepoint where
  map := L.boundary.map
  comm := by
    have h : (pointedFiber p).basepoint = fiberPoint p.right E.basepoint :=
      PointedSimplicialSet.basepoint_ofVertex _ _
    rw [h]
    exact L.boundary.comm

@[reassoc (attr := simp)]
lemma pointedBoundary_ι (L : BoundaryLift p.right E.basepoint s) :
    L.pointedBoundary.map ≫ (pointedFiberι p).right =
      stdSimplex.δ (Fin.last (n + 1)) ≫ L.map := L.boundary_ι

variable [Fibration p.right]

/-- 概要：標準基点の fiber の代表を既存の fiberPoint の群表示へ戻す。
方針：恒等射による基点移送は単体の射を変えない。
規約：正次数の代表の実際の次元は r+1。
使われ方：Goerss–Jardine I §8。連結準同型の基点正規化。 -/
lemma pointedFiberGroupEquiv_mk {r : ℕ}
    {t : B.right.PtSimplex (r + 2) (p.right.app _ E.basepoint)}
    (L : BoundaryLift p.right E.basepoint t) :
    pointedFiberGroupEquiv p r (KanHomotopyGroup.mk L.pointedBoundary) =
      KanHomotopyGroup.mk L.boundary := by
  change KanHomotopyGroup.map (𝟙 _) _ (KanHomotopyGroup.mk L.pointedBoundary) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map_mk]
  congr 1

end BoundaryLift

/-- 概要：公開連結準同型は任意の相対ホーン充填の最後の面の類で計算できる。
方針：底の基点移送の逆を打ち消し、充填の選択独立性と fiber の基点比較を使う。
規約：群の値そのものの等式。符号の補正や存在の仮定を新しく入れない。
使われ方：Goerss–Jardine I §8、VIII §1。セル境界の連結射の代表公式。 -/
theorem pointedConnectingHom_boundaryLift {E B : PointedSimplicialSet.{u}}
    (p : E ⟶ B) [Fibration p.right] [KanComplex E.right] [KanComplex B.right]
    (r : ℕ) {s : B.right.PtSimplex (r + 2) (p.right.app _ E.basepoint)}
    (L : BoundaryLift p.right E.basepoint s) :
    pointedConnectingHom p r
        (KanHomotopyGroup.equivOfIso (r + 1) (Iso.refl B.right)
          (OmegaSpectrum.pointedMap_basepoint p) (KanHomotopyGroup.mk s)) =
      KanHomotopyGroup.mk L.pointedBoundary := by
  apply (pointedFiberGroupEquiv p r).injective
  rw [pointedConnectingHom_compute, MulEquiv.symm_apply_apply,
    BoundaryLift.pointedFiberGroupEquiv_mk, _root_.SerrePositivity.InfinityCategories.Kan.connectingHom_apply,
    _root_.SerrePositivity.InfinityCategories.Kan.connecting_eq p.right E.basepoint L]
  rfl

end
end SerrePositivity.KST.Spectra
