module
public import SerrePositivity.KST.Fibration.ClosedFlagFiniteComparison
public import SerrePositivity.KST.Fibration.WeakStringFiniteRecursion

/-!
概要：閉じた部分圏 P の元の全有限旗比較を、先行旗と最後の cofiber へ厳密に分解する。
方針：元の全座標の再添字を共通の有限積分解補題へ渡す。
規約：P を商の核へ置換せず、既存 q 版と同じ帰納計算を共有する。
使われ方：K-B2 の相対加法性から全長比較の同値性を導く。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration
open Relative

/-- 概要：先行旗の比較は元の初期評価と全先行 cofiber を厳密に回収する。
方針：同じ最後の面射への制限を元の全座標の再添字公式へ代入する。
規約：同じ有限添字と実補完。使われ方：共通帰納分解の前提。 -/
theorem closedFlagFiniteComparison_prefix {B : StableModel.{u}}
    (P : ClosedStablePredicate B) (n r : ℕ) :
    (multiRealizationFunctor r).map (closedFlagMap P (SimplexCategory.δ (Fin.last (n + 2)))) ≫
      closedFlagFiniteComparison P (n + 1) r =
        lift ((multiRealizationFunctor r).map (closedFlagVertex P ⦋n + 2⦌ 0))
          (Pi.lift (fun i : Fin (n + 1) => (multiRealizationFunctor r).map
            (closedFlagCofiber P (consecutiveWeakStringEdge (n + 2) i.castSucc)))) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, closedFlagFiniteComparison_reindex_initial, lift_fst]
    rfl
  · apply Pi.hom_ext
    intro i
    rw [Category.assoc, Category.assoc, closedFlagFiniteComparison_reindex_cofiber,
      lift_snd, Pi.lift_comp_π, consecutiveWeakStringEdge_lastFace]

/-- 概要：元の先行旗と最後の P 値 cofiber を保つ実比較段。
方針：元の実制限と共通補完の実現を束ねる。
規約：相対加法性との照合は別工程。使われ方：共通帰納の実一段写像。 -/
def closedFlagTailMultiStep {B : StableModel.{u}} (P : ClosedStablePredicate B) (n r : ℕ) :
    (multiRealizationFunctor r).obj (closedFlagModel P ⦋n + 2⦌) ⟶
      (multiRealizationFunctor r).obj (closedFlagModel P ⦋n + 1⦌) ⊗
        (multiRealizationFunctor r).obj (closedStableModel P) :=
  lift ((multiRealizationFunctor r).map (closedFlagMap P (SimplexCategory.δ (Fin.last (n + 2)))))
    ((multiRealizationFunctor r).map
      (closedFlagCofiber P (consecutiveWeakStringEdge (n + 2) (Fin.last (n + 1)))))

/-- 概要：P 版の同じ全有限比較は共通の有限積帰納分解を満たす。
方針：元の先行旗座標を汎用の同じ分解補題へ代入する。
規約：既存 q 版の長い帰納証明を複製しない。
使われ方：実相対加法性を共通の局所化同型帰納へ渡す。 -/
theorem closedFlagFiniteComparison_factor {B : StableModel.{u}}
    (P : ClosedStablePredicate B) (n r : ℕ) :
    closedFlagTailMultiStep P n r ≫ (closedFlagFiniteComparison P (n + 1) r ⊗ₘ 𝟙 _) ≫
      (α_ _ _ _).hom = closedFlagFiniteComparison P (n + 2) r ≫
        (𝟙 _ ⊗ₘ (finSnocProductIso ((multiRealizationFunctor r).obj
          (closedStableModel P)) (n + 1)).hom) :=
  finiteFlagComparison_factor (n + 1)
    ((multiRealizationFunctor r).map (closedFlagMap P (SimplexCategory.δ (Fin.last (n + 2)))))
    (closedFlagFiniteComparison P (n + 1) r)
    ((multiRealizationFunctor r).map (closedFlagVertex P ⦋n + 2⦌ 0))
    (fun i => (multiRealizationFunctor r).map
      (closedFlagCofiber P (consecutiveWeakStringEdge (n + 2) i)))
    (closedFlagFiniteComparison_prefix P n r)

end SerrePositivity.KST.Fibration
