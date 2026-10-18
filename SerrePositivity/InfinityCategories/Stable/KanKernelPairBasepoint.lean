module
public import SerrePositivity.InfinityCategories.Stable.KernelPairFiberTransportHom
public import SerrePositivity.InfinityCategories.Stable.KanKernelPairLoops

/-! # 自己引き戻しのループ表示の基点変更

概要：基点間の辺の底への像は、二つのループ表示を可換に結ぶ。
方針：第二射影の fiber を基点間の辺に沿って動かし、第一成分の Hom 表示の輸送と始対象変更を合成する。
規約：共役を可逆射との可換式で述べる。使われ方：ループ積の基点からの独立性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：基点の辺を底へ送った射は、同じ成分の異なる基点のループ表示を可換に結ぶ。
方針：固定 fiber で成分を代表し、第二射影の輸送の Hom 公式と始対象変更の公式を使う。
規約：r は Kan fibration、E は可縮な Kan、B も Kan。使われ方：共役の合成保存による積の独立性。 -/
lemma kanKernelPairPiZeroLoopEquiv_basepoint {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (r : E ⟶ B) [Fibration r] (hE : IsContractibleKan E) {e d : E _⦋0⦌}
    (a : SSet.Truncated.Edge (X := (truncation 2).obj E) e d)
    (c : SSet.π₀ (pullback r r)) :
    kanKernelPairPiZeroLoopEquiv r hE e c ≫
      SSet.Truncated.HomotopyCategory.homMk (a.map ((truncation 2).map r)) =
    SSet.Truncated.HomotopyCategory.homMk (a.map ((truncation 2).map r)) ≫
      kanKernelPairPiZeroLoopEquiv r hE d c := by
  obtain ⟨T⟩ := nonempty_leftFibrationFiberTransport (pullback.snd r r) a
  obtain ⟨b, rfl⟩ := (vertexFiberι_homotopyEquivalence_of_contractible_base
    (pullback.snd r r) hE e).mapPiZero_bijective.surjective c
  have Htrans := kernelPairFiberTransport_hom r e (hE.isInitialVertex e) a T b
  have Hchange := leftFibrationInitialFiberPiZeroEquiv_change_initial r e d
    (hE.isInitialVertex e) (hE.isInitialVertex d) (r.app (Opposite.op ⦋0⦌) d)
    (SSet.mapπ₀ (vertexFiberPullbackIso r r d).hom (SSet.mapπ₀ T.map b))
  have hinit : (hoFunctor.map r).toFunctor.map
      (initialVertexIso (hE.isInitialVertex e) (hE.isInitialVertex d)).hom =
      SSet.Truncated.HomotopyCategory.homMk (a.map ((truncation 2).map r)) := by
    have h := (hE.isInitialVertex e).isInitialHo.hom_ext
      (initialVertexIso (hE.isInitialVertex e) (hE.isInitialVertex d)).hom
      (SSet.Truncated.HomotopyCategory.homMk a)
    rw [h]
    rfl
  rw [hinit] at Hchange
  rw [kanKernelPairPiZeroLoopEquiv_fiber r hE e b]
  rw [T.piZero_inclusion b, kanKernelPairPiZeroLoopEquiv_fiber]
  exact Htrans.symm.trans Hchange.symm

end SerrePositivity.InfinityCategories
