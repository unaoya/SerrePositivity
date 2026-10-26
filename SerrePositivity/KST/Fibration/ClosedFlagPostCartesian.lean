module
public import SerrePositivity.KST.Fibration.ClosedKernelInitialPullback
public import SerrePositivity.KST.Fibration.SimplicialInitialPullback
public import SerrePositivity.KST.Fibration.CoreSinglePullbackTransfer
public import SerrePositivity.KST.SConstruction.MultiStageConnected

/-!
概要：元の P 全旗包含の全単体的実自然性四角形は homotopy pullback。
方針：同じ実初期評価の引き戻しを共通単体計算へ渡し、単回座標同型で元の F へ戻す。
規約：B と P のみ。Cofinality・NonConnective・商比較を依存に持たない。
使われ方：K-B2-S1 の元の全自然性条件を実定理で放電する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.KST.LocalizingInvariants SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Comparison
namespace SerrePositivity.KST.Fibration
open Relative
variable {B : StableModel.{u}} (P : ClosedStablePredicate B)

/-- 概要：元の P 全旗包含を全反復の実単体的自然変換に束ねる。
方針：元の実完全射の厳密再添字へ同じ反復実現関手を適用する。
規約：元の全旗を保持。使われ方：全正反復の自然性引き戻し。 -/
def closedKernelMultiPostcomp (r : ℕ) :
    weakStringMultiRealization (closedKernelZeroMap P) r ⟶
      closedFlagSimplicial P ⋙ multiRealizationFunctor r where
  app n := (multiRealizationFunctor r).map (closedKernelFlagPost P n.unop)
  naturality {_ _} θ := by
    change (multiRealizationFunctor r).map (weakStringExactMap (closedKernelZeroMap P) θ.unop) ≫
      (multiRealizationFunctor r).map (closedKernelFlagPost P _) =
        (multiRealizationFunctor r).map (closedKernelFlagPost P _) ≫
          (multiRealizationFunctor r).map (closedFlagMap P θ.unop)
    rw [← Functor.map_comp, ← Functor.map_comp, closedKernelFlagPost_reindex]

/-- 概要：元の P 全旗包含の先頭を保つ自然性四角形は全正反復で引き戻し。
方針：同じ初期評価四角形と厳密再添字を共通の水平消去計算へ渡す。
規約：元の自然性四角形そのもの。使われ方：全生成面・退化の検出。 -/
theorem closedKernelMultiPostcomp_head_homotopyPullback (r : ℕ)
    {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (hθ : θ.toOrderHom 0 = 0) :
    IsHomotopyPullback (CommSq.mk ((closedKernelMultiPostcomp P (r + 1)).naturality θ.op)) := by
  apply simplicialInitialComparison_head_homotopyPullback (closedKernelMultiPostcomp P (r + 1))
    ((multiRealizationFunctor (r + 1)).map (closedStableInclusion P))
    (fun n => (multiRealizationFunctor (r + 1)).map (closedKernelInitialExact P n))
    (fun n => (multiRealizationFunctor (r + 1)).map (closedFlagVertex P n 0))
    (fun n => closedKernelInitialPostSquare P n (r + 1))
    (fun n => closedKernelInitialPostSquare_homotopyPullback P n.len r) θ
  · change (multiRealizationFunctor (r + 1)).map (weakStringExactMap (closedKernelZeroMap P) θ) ≫
      (multiRealizationFunctor (r + 1)).map (closedKernelInitialExact P ⦋m⦌) = _
    rw [← Functor.map_comp]
    apply congrArg (multiRealizationFunctor (r + 1)).map
    unfold closedKernelInitialExact
    rw [← Category.assoc, weakStringVertexTopExact_reindex, hθ]
  · change (multiRealizationFunctor (r + 1)).map (closedFlagMap P θ) ≫
      (multiRealizationFunctor (r + 1)).map (closedFlagVertex P ⦋m⦌ 0) = _
    rw [← Functor.map_comp, closedFlagVertex_reindex, hθ]

/-- 概要：元の P 全旗包含の全単体作用素の実自然性四角形は全正反復で引き戻し。
方針：同じ初期評価の引き戻しと行の連結性を共通の全生成計算へ渡す。
規約：追加の存在仮定なし。使われ方：元の単回 F への座標輸送。 -/
theorem closedKernelMultiPostcomp_homotopyPullback (r : ℕ)
    {m n : SimplexCategory} (θ : m ⟶ n) :
    IsHomotopyPullback (CommSq.mk ((closedKernelMultiPostcomp P (r + 1)).naturality θ.op)) := by
  letI : ∀ n, SSet.IsConnected ((closedFlagSimplicial P ⋙
      multiRealizationFunctor (r + 1)).obj (Opposite.op n)) :=
    fun n => multiDiagonalCoreSConstruction_isConnected r (closedFlagModel P n)
  exact simplicialNaturality_homotopyPullback_of_head (closedKernelMultiPostcomp P (r + 1))
    (fun θ hθ => closedKernelMultiPostcomp_head_homotopyPullback P r θ hθ) θ

/-- 概要：元の F 値全 P 旗包含の全自然性四角形は実 homotopy pullback。
方針：同じ一回反復の実定理を元の単回 F の四隅の厳密座標同型へ輸送する。
規約：B と P のみ。元の包含を保持し、商・Verdier 列・共終性を仮定しない。
使われ方：K-B2-S1 の閉じた安定部分圏版有限旗自然性の公開供給。 -/
theorem closedStableFlagPost_homotopyPullback {m n : SimplexCategory} (θ : m ⟶ n) :
    IsHomotopyPullback (CommSq.mk ((closedStableFlagPost P).naturality θ.op)) := by
  let sq : CommSq (weakStringExactMap (closedKernelZeroMap P) θ)
      (closedKernelFlagPost P n) (closedKernelFlagPost P m) (closedFlagMap P θ) :=
    ⟨closedKernelFlagPost_reindex P θ⟩
  exact coreSingleRealization_homotopyPullback_of_multi sq
    (closedKernelMultiPostcomp_homotopyPullback P 0 θ)

/-- 概要：元の明示有限旗自然性条件を B・P のみから放電する。
方針：同じ公開全自然性定理を条件の全作用素へ代入する。
規約：条件の存在を仮定しない。使われ方：K-B2 の既存の実 fiber 定理への代入。 -/
theorem closedStableFlagPostPullback : ClosedStableFlagPostPullback P :=
  fun θ => closedStableFlagPost_homotopyPullback P θ

end SerrePositivity.KST.Fibration
