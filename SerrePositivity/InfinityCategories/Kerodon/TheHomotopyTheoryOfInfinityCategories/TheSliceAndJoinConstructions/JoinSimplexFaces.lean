module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinSimplexInclusions

/-! # cospan の join の標準セルの面

概要：可変因子の面を標準 join の大きい単体の同じ番号の面へ移す。
方針：左右の包含で比較し、有限順序集合への頂点の二通りの挿入を同定する。
規約：HTT §1.2.8・§1.2.13。使われ方：N7c の既知境界面からの成分回収。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

open CategoryTheory Opposite
open scoped _root_.Simplicial

/-- 概要：末尾の二点を固定して先頭の面を取ると、先頭で面を取ってから二点を加えることと一致。
方針：飛ばす点より前か後かで場合分けする。
規約：HTT §1.2.8。使われ方：join の左側の面の頂点写像。 -/
lemma succAbove_castAdd_two {n : ℕ} (j : Fin (n + 2)) (i : Fin (n + 1)) :
    (j.castAdd 2).succAbove (i.castAdd 2) = (j.succAbove i).castAdd 2 := by
  by_cases h : i.castSucc < j
  · rw [Fin.succAbove_of_castSucc_lt j i h,
      Fin.succAbove_of_castSucc_lt (j.castAdd 2) (i.castAdd 2) (by exact h)]
    rfl
  · have hle : j ≤ i.castSucc := le_of_not_gt h
    rw [Fin.succAbove_of_le_castSucc j i hle,
      Fin.succAbove_of_le_castSucc (j.castAdd 2) (i.castAdd 2) (by exact hle)]
    rfl

/-- 概要：左因子の一面の join は大きい標準単体の対応する先頭の面。
方針：左包含では二点追加と面の可換性、右包含では全ての点が一つ後ろへ移ることを使う。
規約：HTT §1.2.8・§1.2.13。使われ方：slice 境界から標準セルの既知の面への制限。 -/
lemma joinStdSimplexIso_left_face (n : ℕ) (j : Fin (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.δ j) (𝟙 (Δ[1] : SSet.{u})) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso (n + 1) 1).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1).hom ≫ SSet.stdSimplex.δ (j.castAdd 2) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join_hom_to_stdSimplex_ext
  · calc
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[n] Δ[1] ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.δ j) (𝟙 Δ[1]) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso (n + 1) 1).hom) =
        SSet.stdSimplex.δ j ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[n + 1] Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso (n + 1) 1).hom) := by
          rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc]
      _ = SSet.stdSimplex.δ j ≫ SSet.stdSimplex.map
          (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinLeftOrderHom (n + 1) 1)) := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_inl]
      _ = SSet.stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinLeftOrderHom n 1)) ≫
          SSet.stdSimplex.δ (j.castAdd 2) := by
        change SSet.stdSimplex.map (SimplexCategory.δ j) ≫ SSet.stdSimplex.map _ =
          SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map (SimplexCategory.δ (j.castAdd 2))
        rw [← Functor.map_comp, ← Functor.map_comp]
        apply congrArg SSet.stdSimplex.map
        apply SimplexCategory.Hom.ext
        apply DFunLike.ext
        intro i
        exact (succAbove_castAdd_two j i).symm
      _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[n] Δ[1] ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1).hom ≫
          SSet.stdSimplex.δ (j.castAdd 2)) := by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_inl]
  · calc
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[n] Δ[1] ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.δ j) (𝟙 Δ[1]) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso (n + 1) 1).hom) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[n + 1] Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso (n + 1) 1).hom := by
          rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp]
      _ = SSet.stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightOrderHom (n + 1) 1)) :=
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_inr _ _
      _ = SSet.stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightOrderHom n 1)) ≫
          SSet.stdSimplex.δ (j.castAdd 2) := by
        change SSet.stdSimplex.map _ = SSet.stdSimplex.map _ ≫
          SSet.stdSimplex.map (SimplexCategory.δ (j.castAdd 2))
        rw [← Functor.map_comp]
        apply congrArg SSet.stdSimplex.map
        apply SimplexCategory.Hom.ext
        apply DFunLike.ext
        intro i
        have hle : j.castAdd 2 ≤ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightOrderHom n 1 i).castSucc := by
          change j.val ≤ n + 1 + i.val
          have := j.isLt
          omega
        change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightOrderHom (n + 1) 1 i = (j.castAdd 2).succAbove (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightOrderHom n 1 i)
        rw [Fin.succAbove_of_le_castSucc _ _ hle]
        apply Fin.ext
        change n + 1 + 1 + i.val = n + 1 + i.val + 1
        omega
      _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[n] Δ[1] ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1).hom ≫
          SSet.stdSimplex.δ (j.castAdd 2)) := by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_inr]

/-- 概要：右因子の最後の頂点との join は、右の最初の頂点を除く面。
方針：左右の包含で比較し、面の挿入写像を有限順序集合で計算する。
規約：HTT §1.2.8・§1.2.13。使われ方：cospan の二つの標準セルの共通面。 -/
lemma joinStdSimplexIso_right_last (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[n] : SSet.{u})) (SSet.stdSimplex.δ (0 : Fin 2)) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫
        SSet.stdSimplex.δ ((Fin.last (n + 1)).castSucc) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join_hom_to_stdSimplex_ext
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_inl, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_inl]
    change SSet.stdSimplex.map _ = SSet.stdSimplex.map _ ≫
      SSet.stdSimplex.map (SimplexCategory.δ ((Fin.last (n + 1)).castSucc))
    rw [← Functor.map_comp]
    apply congrArg SSet.stdSimplex.map
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinLeftOrderHom n 1 i =
      ((Fin.last (n + 1)).castSucc).succAbove (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinLeftOrderHom n 0 i)
    rw [Fin.succAbove_of_castSucc_lt _ _ (by
      change i.val < n + 1
      exact i.isLt)]
    rfl
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_inr, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_inr]
    change SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫
      SSet.stdSimplex.map _ = SSet.stdSimplex.map _ ≫
        SSet.stdSimplex.map (SimplexCategory.δ ((Fin.last (n + 1)).castSucc))
    rw [← Functor.map_comp, ← Functor.map_comp]
    apply congrArg SSet.stdSimplex.map
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    have hi : i = 0 := by
      exact Fin.eq_zero (show Fin 1 from i)
    subst i
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightOrderHom n 1 1 =
      ((Fin.last (n + 1)).castSucc).succAbove (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightOrderHom n 0 0)
    rw [Fin.succAbove_of_le_castSucc _ _ (by rfl)]
    apply Fin.ext
    change n + 1 + 1 = n + 1 + 0 + 1
    omega

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
