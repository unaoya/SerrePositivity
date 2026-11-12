module

public import SerrePositivity.KST.Comparison.HatGLShiftedStabilization
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyConstant

/-!
# 高次の係数表示と rank の安定化の可換性

概要：有限 rank の ĜL の高次の係数表示は、係数群の行列の安定化と可換する。
方針：各係数の標準写像を合成し、既存の係数と新しい零の定数写像を分けて計算する。
規約：KST Lemma 2.13 の安定 rank の高次公式へ渡す自然性。
使われ方：rank の群の図式の自然同型の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite SSet
open scoped Simplicial

/--
概要：有限 rank の高次の係数表示は rank の安定化と可換する。
方針：各成分を標準係数写像の誘導写像として計算し、新しい係数は定数射が単位へ送ることを使う。
規約：新しい行・列は係数群の単位、加法記法では零で埋める。
使われ方：KST Lemma 2.13 の高次の行列公式の自然同型。
-/
theorem hatGLCoefficientHomotopy_stabilization (A : SimplicialObject RingCat.{u}) (r n : ℕ)
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (hatGLSpace A r) n (1 : hatGLSubmonoid A r 0)) :
    simplicialRingHatGLCoefficientHomotopyMulEquiv A (r + 1) n
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (hatGLSpaceStabilization A r)
          (hatGLSpaceStabilization_unit A r) x) =
      coefficientMatrixStabilization
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (ringSpace A) n (0 : A.obj (op ⦋0⦌))) r
          (simplicialRingHatGLCoefficientHomotopyMulEquiv A r n x) := by
  have heq (f g : hatGLSpace A r ⟶ ringSpace A)
      (hf : f.app (op ⦋0⦌) (1 : hatGLSubmonoid A r 0) = (0 : A.obj (op ⦋0⦌)))
      (hg : g.app (op ⦋0⦌) (1 : hatGLSubmonoid A r 0) = (0 : A.obj (op ⦋0⦌)))
      (h : f = g) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map f hf x =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map g hg x := by
    subst g
    rfl
  have hz : (SSet.const (X := hatGLSpace A r) (Y := ringSpace A) (0 : A.obj (op ⦋0⦌))).app (op ⦋0⦌)
      (1 : hatGLSubmonoid A r 0) = (0 : A.obj (op ⦋0⦌)) := by
    change (A.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op).hom 0 = 0
    exact map_zero _
  funext i' j'
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i'
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j'
  rw [hatGLCoefficientHomotopyMulEquiv_entry, coefficientMatrixStabilization_apply_sum]
  let s := hatGLShiftedEntryMap A (r + 1) (finSumFinEquiv i) (finSumFinEquiv j)
  have hs : s.app (op ⦋0⦌) (1 : hatGLSubmonoid A (r + 1) 0) =
      (0 : A.obj (op ⦋0⦌)) := hatGLShiftedEntryMap_basepoint A (r + 1) _ _
  have hc : (hatGLSpaceStabilization A r ≫ s).app (op ⦋0⦌)
      (1 : hatGLSubmonoid A r 0) = (0 : A.obj (op ⦋0⦌)) := by
    change s.app (op ⦋0⦌) ((hatGLSpaceStabilization A r).app (op ⦋0⦌)
      (1 : hatGLSubmonoid A r 0)) = _
    rw [hatGLSpaceStabilization_unit]
    exact hs
  have hmap := DFunLike.congr_fun (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_comp (n := n)
    (hatGLSpaceStabilization A r) (hatGLSpaceStabilization_unit A r) s hs hc) x
  refine hmap.symm.trans ?_
  have hNat := hatGLShiftedEntryMap_stabilization A r i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      exact (heq _ _ hc (hatGLShiftedEntryMap_basepoint A r i j) hNat).trans
        (hatGLCoefficientHomotopyMulEquiv_entry A r n x i j).symm
    | inr j =>
      exact (heq _ _ hc hz hNat).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.map_const (n + 1) hz x)
  | inr i =>
    cases j with
    | inl j =>
      exact (heq _ _ hc hz hNat).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.map_const (n + 1) hz x)
    | inr j =>
      exact (heq _ _ hc hz hNat).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.map_const (n + 1) hz x)

end SerrePositivity.KST.Comparison
