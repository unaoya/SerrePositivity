module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.ResolutionStepFunctor
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# 本体の同じ半自由分解列の関手性

## 概要
元の自由 disk 被覆から始まる同じ可算 kernel cell 列を、実際の射について写す。

## 方針
本体の増大を保つ arrow の射を段階で再帰し、同じ可算列の余極限へ渡す。

## 規約
候補の対象・増大・半自由性・擬同型性は本体のものを再利用する。関手の加法性は要求しない。

## 使われ方
BS 著者版 Lemma 4.22 の厳密な余単体的入力の解消。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DifferentialGraded

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonResolution
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 一般の arrow の射について、同じ遷移包含を保つ法則。 -/
@[reassoc] theorem kernelStepArrowMap_ι {F G : Arrow (ModuleCategory R D)} (s : F ⟶ G) :
    moduleKernelCellStepι R D F.hom ≫ ((kernelStepArrowFunctor R D).map s).left =
      s.left ≫ moduleKernelCellStepι R D G.hom := kernelStepMap_ι R D s

/-- 本体の同じ各段階の増大の、実際の射での像。 -/
def stageArrowMap {M N : ModuleCategory R D} (g : M ⟶ N) :
    ∀ k : ℕ, Arrow.mk (moduleResolutionStage R D M k).hom ⟶
      Arrow.mk (moduleResolutionStage R D N k).hom
  | 0 => (diskCoverArrowFunctor R D).map g
  | k+1 => by
    change (kernelStepArrowFunctor R D).obj (Arrow.mk (moduleResolutionStage R D M k).hom) ⟶
      (kernelStepArrowFunctor R D).obj (Arrow.mk (moduleResolutionStage R D N k).hom)
    exact (kernelStepArrowFunctor R D).map (stageArrowMap g k)

/-- 段階の射は元の増大の値域の射を保つ。 -/
@[simp] theorem stageArrowMap_right {M N : ModuleCategory R D} (g : M ⟶ N) (k : ℕ) :
    (stageArrowMap R D g k).right = g := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

/-- 同じ各段階の恒等射の法則。 -/
@[simp] theorem stageArrowMap_id (M : ModuleCategory R D) (k : ℕ) :
    stageArrowMap R D (𝟙 M) k = 𝟙 (Arrow.mk (moduleResolutionStage R D M k).hom) := by
  induction k with
  | zero => exact (diskCoverArrowFunctor R D).map_id M
  | succ k ih =>
    exact (congrArg (fun h => (kernelStepArrowFunctor R D).map h) ih).trans
      ((kernelStepArrowFunctor R D).map_id _)

/-- 同じ各段階の合成の法則。 -/
@[simp] theorem stageArrowMap_comp {M N P : ModuleCategory R D} (g : M ⟶ N) (h : N ⟶ P) (k : ℕ) :
    stageArrowMap R D (g ≫ h) k = stageArrowMap R D g k ≫ stageArrowMap R D h k := by
  induction k with
  | zero => exact (diskCoverArrowFunctor R D).map_comp g h
  | succ k ih =>
    exact (congrArg (fun s => (kernelStepArrowFunctor R D).map s) ih).trans
      ((kernelStepArrowFunctor R D).map_comp (stageArrowMap R D g k) (stageArrowMap R D h k))

set_option maxHeartbeats 800000 in
-- 元の DG 写像錐の対象の型照合を、この法則だけに局所化する。
/-- 同じ段階の射は、本体の同じ遷移包含を保つ。 -/
@[reassoc] theorem stageArrowMap_transition {M N : ModuleCategory R D} (g : M ⟶ N) (k : ℕ) :
    (moduleResolutionTransition R D M k).left ≫ (stageArrowMap R D g (k+1)).left =
      (stageArrowMap R D g k).left ≫ (moduleResolutionTransition R D N k).left := by
  change moduleKernelCellStepι R D (moduleResolutionStage R D M k).hom ≫
      ((kernelStepArrowFunctor R D).map (stageArrowMap R D g k)).left =
    (stageArrowMap R D g k).left ≫ moduleKernelCellStepι R D (moduleResolutionStage R D N k).hom
  exact kernelStepArrowMap_ι R D (stageArrowMap R D g k)

/-- 元の同じ可算分解列を写す自然変換。 -/
def resolutionDiagramMap {M N : ModuleCategory R D} (g : M ⟶ N) :
    moduleResolutionDiagram R D M ⟶ moduleResolutionDiagram R D N :=
  NatTrans.ofSequence (fun k => (stageArrowMap R D g k).left) (by
    intro k
    simpa only [moduleResolutionDiagram, Functor.comp_map, Over.forget_map,
      moduleResolutionOverDiagram, Functor.ofSequence_map_homOfLE_succ] using
      stageArrowMap_transition R D g k)


end SerrePositivity.BhattScholze.Prismatic.HTComparisonResolution
