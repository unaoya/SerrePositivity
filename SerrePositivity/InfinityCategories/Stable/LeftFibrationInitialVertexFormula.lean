module
public import SerrePositivity.InfinityCategories.F1.PinchedLeftPiZeroVertex
public import SerrePositivity.InfinityCategories.Core.ZeroHomotopy
public import SerrePositivity.InfinityCategories.Core.CoconeFactorization

/-! # 始対象からの fiber の Hom 表示の代表元

概要：fiber の Hom 表示は始対象から終点への一意の射を底へ送った射である。
方針：中間空間の頂点を辺として読み、左模型の零単体の計算と始対象からの射の一意性を使う。
規約：終点の等号輸送を明示する。使われ方：始対象・余極限余錐の選択変更。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：固定図式を等号で変えても coslice fiber の元の錐は変わらない。
方針：図式の等号を消す。
規約：零単体の錐そのものの等号。使われ方：左模型の座標の計算。 -/
lemma stableCosliceFiberChange_vertex_val {K B : SSet.{u}} {a b : K ⟶ B}
    (h : a = b) (y : B _⦋0⦌) (s : (vertexFiber (sliceUnderProjection a) y) _⦋0⦌) :
    ((eqToHom (congrArg (fun t => vertexFiber (sliceUnderProjection t) y) h)).app
      (Opposite.op ⦋0⦌) s).val.val = s.val.val := by
  subst b
  rfl

/-- 概要：比較の中間空間の頂点は底の指定した二端点間の辺を与える。
方針：始点下の辺を底へ送り、fiber の条件で終点を揃える。
規約：底の辺は二切断で指定する。使われ方：表現可能な Hom の代表元。 -/
def leftFibrationInitialTotalVertexEdge {E B : SSet.{u}} (p : E ⟶ B)
    (c : E _⦋0⦌) (y : B _⦋0⦌) (s : (leftFibrationInitialTotal p c y) _⦋0⦌) :
    SSet.Truncated.Edge (X := (truncation 2).obj B) (p.app (Opposite.op ⦋0⦌) c) y where
  edge := p.app (Opposite.op ⦋1⦌) (sliceUnderVertexEdge c s.val).edge
  src_eq := ((sliceUnderVertexEdge c s.val).map ((truncation 2).map p)).src_eq
  tgt_eq := ((sliceUnderVertexEdge c s.val).map ((truncation 2).map p)).tgt_eq.trans
    (s.property.trans (pinchedConstant_zero y))

/-- 概要：Hom 表示を中間空間の頂点に適用すると、その底の辺の類を得る。
方針：比較 span の計算則を使い、図式の表示変更を除いて左模型の零単体を読む。
規約：底は quasicategory、p は left fibration、始点は始対象。
使われ方：Hom 表示の選択変更の計算。 -/
lemma leftFibrationInitialFiberPiZeroEquiv_total_vertex {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] (c : E _⦋0⦌) (hc : IsInitialVertex c) (y : B _⦋0⦌)
    (s : (leftFibrationInitialTotal p c y) _⦋0⦌) :
    leftFibrationInitialFiberPiZeroEquiv p c hc y
      (SSet.π₀.mk ((leftFibrationInitialEvaluation p c y).app (Opposite.op ⦋0⦌) s)) =
    SSet.Truncated.HomotopyCategory.homMk (leftFibrationInitialTotalVertexEdge p c y s) := by
  have h := leftFibrationInitialFiberPiZeroEquiv_evaluation p c hc y (SSet.π₀.mk s)
  change leftFibrationInitialFiberPiZeroEquiv p c hc y
    (SSet.π₀.mk ((leftFibrationInitialEvaluation p c y).app (Opposite.op ⦋0⦌) s)) = _ at h
  rw [h]
  change pinchedHomLeftPiZeroEquiv _ y (SSet.mapπ₀
    (pinchedLeftCosliceFiberIso _ y).inv (SSet.π₀.mk
      ((eqToHom (congrArg (fun t => vertexFiber (sliceUnderProjection t) y)
        (SSet.yonedaEquiv_symm_comp c p))).app (Opposite.op ⦋0⦌)
        ((leftFibrationInitialProjection p c y).app (Opposite.op ⦋0⦌) s)))) = _
  rw [stableCosliceFiberPiZeroEquiv_mk]
  apply congrArg SSet.Truncated.HomotopyCategory.homMk
  apply SSet.Truncated.Edge.ext
  change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫ _) =
    p.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫ s.val.val))
  rw [stableCosliceFiberChange_vertex_val (SSet.yonedaEquiv_symm_comp c p)]
  change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫ (s.val.val ≫ p)) = _
  rw [← Category.assoc, SSet.yonedaEquiv_comp]

/-- 概要：Hom 表示は始対象から終点への一意の射を底へ送ったもの。
方針：辺による代表元を底へ送った射と照合し、始対象からの射の一意性を使う。
規約：中間空間の頂点で述べ、終点を fiber の等号で輸送する。
使われ方：二つの始対象を用いた Hom 表示の比較。 -/
lemma leftFibrationInitialFiberPiZeroEquiv_total_initialHom
    {E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] (c : E _⦋0⦌) (hc : IsInitialVertex c) (y : B _⦋0⦌)
    (s : (leftFibrationInitialTotal p c y) _⦋0⦌) :
    leftFibrationInitialFiberPiZeroEquiv p c hc y
      (SSet.π₀.mk ((leftFibrationInitialEvaluation p c y).app (Opposite.op ⦋0⦌) s)) =
    (hoFunctor.map p).toFunctor.map (hc.isInitialHo.to (SSet.HomotopyCategory.mk
      ((sliceUnderProjection (SSet.yonedaEquiv.symm c)).app (Opposite.op ⦋0⦌) s.val))) ≫
        eqToHom (congrArg (fun x => (SSet.HomotopyCategory.mk x : hoFunctor.obj B))
          (s.property.trans (pinchedConstant_zero y))) := by
  rw [leftFibrationInitialFiberPiZeroEquiv_total_vertex]
  have h := hc.isInitialHo.hom_ext
    (hc.isInitialHo.to (SSet.HomotopyCategory.mk
      ((sliceUnderProjection (SSet.yonedaEquiv.symm c)).app (Opposite.op ⦋0⦌) s.val)))
    (SSet.Truncated.HomotopyCategory.homMk (sliceUnderVertexEdge c s.val))
  rw [h]
  exact (homMk_comp_eqToHom_of_edge_eq
    ((sliceUnderVertexEdge c s.val).map ((truncation 2).map p))
    (leftFibrationInitialTotalVertexEdge p c y s)
    (s.property.trans (pinchedConstant_zero y)) rfl).symm

end SerrePositivity.InfinityCategories
