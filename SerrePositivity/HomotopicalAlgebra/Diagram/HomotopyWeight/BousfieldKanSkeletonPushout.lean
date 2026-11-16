module
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.BousfieldKanCellEvaluation
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.BousfieldKanCellReindex

/-!
概要：元のBK重みの連続する骨格は、同じ自由境界細胞を付着する押し出し。
方針：各評価の相対細胞の押し出しを指定余積同型で輸送し、評価で反映する。
規約：IS-W2 R03aの細胞分解の証明分割。重みの置換は行わない。
使われ方：BK重み全体の射影cofibrancy。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.SSet
open _root_.SerrePositivity.DiagramModel.BousfieldKanCells
open _root_.SerrePositivity.DiagramModel.SimplicialDiagramSkeleton
open _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped _root_.Simplicial
variable (I : Type u) [SmallCategory I]

/-- 空の部分複体に関する相対骨格を、元の同じ骨格へ同定する。 -/
def bkSkeletonInitialIso (n : ℕ) (i : I) :
    (skeletonOfMono ((⊥ : (nerve (Over i)).Subcomplex).ι) n : SSet.{u}) ≅
      ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkSkeleton I).obj n).obj i :=
  Subcomplex.eqToIso (by
    simp [skeletonOfMono, bousfieldKanWeight]
    rfl)

/-- 相対骨格の同型は、同じ元の重みへの包含を保つ。 -/
@[reassoc] theorem bkSkeletonInitialIso_ι (n : ℕ) (i : I) :
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkSkeletonInitialIso I n i).hom ≫ ((nerve (Over i)).skeleton n).ι =
      (skeletonOfMono ((⊥ : (nerve (Over i)).Subcomplex).ι) n).ι := rfl

/-- 各評価で、元の自由境界の四角形は同じ骨格を作る押し出し。 -/
theorem bkCellAttachment_isPushout_app (n : ℕ) (i : I) :
    IsPushout ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellBoundary I n).app i) (((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellTensor I n).map ∂Δ[n].ι).app i)
      (((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkSkeleton I).map (homOfLE (Nat.le_succ n))).app i) ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellTop I n).app i) := by
  let z := ((⊥ : (nerve (Over i)).Subcomplex).ι)
  let e := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkInitialCellEquiv I n i
  refine (relativeCellComplexOfMono.isPushout z n).of_iso
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellReindexIso I e (∂Δ[n] : SSet.{u})) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkSkeletonInitialIso I n i)
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellReindexIso I e Δ[n]) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkSkeletonInitialIso I (n+1) i) ?_ ?_ ?_ ?_
  · apply Sigma.hom_ext
    intro c
    apply (cancel_mono ((nerve (Over i)).skeleton n).ι).mp
    simp only [Category.assoc, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkSkeletonInitialIso_ι, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellReindexIso_ι_assoc,
      _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellComponent_boundary_ι, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkInitialCellEquiv_simplex]
    change _ = _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellComponentInclusion I (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkInitialCellEquiv I n i c) (∂Δ[n] : SSet.{u}) ≫
      (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellBoundary I n).app i ≫ (((bousfieldKanWeight I).obj i).skeleton n).ι
    rw [_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellComponent_boundary_ι, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkInitialCellEquiv_simplex]
    dsimp only [relativeCellComplexOfMono.t]
    rw [← Category.assoc, Sigma.ι_comp_desc]
    rfl
  · apply Sigma.hom_ext
    intro c
    simp only [relativeCellComplexOfMono.Cell.ι_l_assoc, Category.assoc,
      _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellReindexIso_ι, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellReindexIso_ι_assoc, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellComponentInclusion_map]
  · apply (cancel_mono ((nerve (Over i)).skeleton (n+1)).ι).mp
    rfl
  · apply Sigma.hom_ext
    intro c
    apply (cancel_mono ((nerve (Over i)).skeleton (n+1)).ι).mp
    simp only [Category.assoc, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkSkeletonInitialIso_ι, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellReindexIso_ι_assoc,
      _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellComponent_top_ι, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkInitialCellEquiv_simplex]
    change _ = _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellComponentInclusion I (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkInitialCellEquiv I n i c) Δ[n] ≫
      (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellTop I n).app i ≫ (((bousfieldKanWeight I).obj i).skeleton (n+1)).ι
    rw [_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellComponent_top_ι, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkInitialCellEquiv_simplex]
    exact c.ι_b_ι

/-- 元の自由境界の図式全体の四角形は、同じ次の骨格を作る押し出し。 -/
theorem bkCellAttachment_isPushout (n : ℕ) :
    IsPushout (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellBoundary I n) ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellTensor I n).map ∂Δ[n].ι)
      ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkSkeleton I).map (homOfLE (Nat.le_succ n))) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellTop I n) where
  w := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellAttachment_comm I n
  isColimit' := ⟨evaluationJointlyReflectsColimits _ (fun i =>
    (isColimitMapCoconePushoutCoconeEquiv _ _).2
      (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellAttachment_isPushout_app I n i).isColimit)⟩

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
