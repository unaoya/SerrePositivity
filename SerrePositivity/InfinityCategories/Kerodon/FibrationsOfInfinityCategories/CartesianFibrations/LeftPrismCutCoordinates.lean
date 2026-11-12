module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PrismCutCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinReverseCuts
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CosliceFiberCoordinates

/-!
概要：左 Hom の区間比較の切断と、右 Hom の切断の反転の一致。
方針：零の時刻では追加した始点、一の時刻では元の頂点の後続を取る。
規約：単体の次数と時刻のパラメーターをともに任意に保つ。
使われ方：移送した豊穣 Hom の辺の族と左 Hom の区間比較の照合。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 左の区間比較では零ラベルを最初の頂点、一ラベルを元の頂点の後続に送る。 -/
def coherentLeftPrismCut {n : ℕ} (t : Fin (n + 1) →o Fin 2) :
    Fin (n + 1) →o Fin (n + 2) where
  toFun i := if t i = 0 then 0 else i.succ
  monotone' := by
    intro i j hij
    by_cases hi : t i = 0 <;> by_cases hj : t j = 0
    · simp only [hi, hj, ite_true, le_refl]
    · simp only [hi, hj, ite_true, ite_false, Fin.zero_le]
    · have h := t.monotone hij
      rw [hj] at h
      exact False.elim (hi (le_antisymm h (Fin.zero_le _)))
    · simpa only [hi, hj, ite_false, Fin.succ_le_succ_iff] using hij

/-- 左の切断は、時刻を反転した右の切断をさらに反転したもの。 -/
lemma coherentLeftPrismCut_eq_reverse {n : ℕ} (t : Fin (n + 1) →o Fin 2) :
    SimplexCategory.mkHom (coherentLeftPrismCut t) =
      SimplexCategory.rev.map
        (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableReverseOrderHom t))) := by
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro i
  change (if t i = 0 then 0 else i.succ) =
    (if _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableReverseOrderHom t i.rev = 0 then i.rev.castSucc else Fin.last (n + 1)).rev
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableReverseOrderHom t i.rev = (t i).rev := by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableReverseOrderHom, OrderHom.coe_mk]
    rw [Fin.rev_rev]
  rw [ht]
  by_cases hi : t i = 0
  · rw [hi]
    rw [ite_eq_left rfl, ite_eq_right (by decide : (0 : Fin 2).rev ≠ 0), Fin.rev_last]
  · have hi' : t i = 1 := Fin.ext (by have h := (t i).isLt; omega)
    rw [hi']
    rw [ite_eq_right (by decide : (1 : Fin 2) ≠ 0),
      ite_eq_left (by decide : (1 : Fin 2).rev = 0), Fin.rev_castSucc, Fin.rev_rev]

/-- 左 prism の標準単体表示は、追加した始点を使う切断写像を表す。 -/
lemma leftMappingSpacePrism_stdSimplex_cut (n : ℕ)
    (t : (Δ[1] : SSet.{u}) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftPointStdSimplexIso n).hom.app (Opposite.op ⦋n⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingSpacePrism Δ[n]).app (Opposite.op ⦋n⦌)
        (t, SSet.yonedaEquiv (𝟙 Δ[n]))) =
      stdSimplex.objEquiv.symm
        (SimplexCategory.mkHom (coherentLeftPrismCut (stdSimplex.objEquiv t).toOrderHom)) := by
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  let a : (Δ[0] : SSet.{u}) _⦋n⦌ := stdSimplex.objEquiv.symm
    (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0)
  change (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.simplexCastIso (show 0 + n + 1 = n + 1 by omega)).hom.app _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 n).hom.app _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap Δ[0] Δ[n]).app _ ((a, t), SSet.yonedaEquiv (𝟙 Δ[n]))))) i).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.simplexCastIso_hom_app_val, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_stdSimplex_val]
  change (if (t i).val = 0 then 0 else 0 + 1 + i.val) =
    (if (stdSimplex.objEquiv t).toOrderHom i = 0 then 0 else i.succ).val
  by_cases h : (stdSimplex.objEquiv t).toOrderHom i = 0
  · have h' : (t i).val = 0 := congrArg Fin.val h
    simp only [h, h', ite_true, Fin.val_zero]
  · have h' : (t i).val ≠ 0 := fun he ↦ h (Fin.ext he)
    simp only [h, h', ite_false, Fin.val_succ]
    omega

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
