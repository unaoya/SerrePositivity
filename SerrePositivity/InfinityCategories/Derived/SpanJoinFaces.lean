module
public import SerrePositivity.InfinityCategories.Derived.SpanJoinCells

/-! # span の join の可変因子の面

概要：coslice の可変単体の面は二つの固定頂点の後ろの同じ面となる。
方針：正規化した標準 join 同型の左右包含で頂点写像を比較する。
規約：可変因子の添字 j は大きいセルの j.succ.succ に移る。
使われ方：D7 の cofiber の coslice 境界から既知成分を取り出す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DGNerve
open scoped Simplicial

/-- 概要：右因子の一面の join は先頭二頂点を固定した大きい単体の面。
方針：左の二頂点は面で固定され、右の添字では succAbove が二回の succ と可換である。
規約：正規化した標準 join 同型。使われ方：coslice の二セルの境界の計算。 -/
lemma cofiberJoinStdSimplexIso_right_face (n : ℕ) (j : Fin (n + 2)) :
    joinMap (𝟙 (Δ[1] : SSet.{u})) (SSet.stdSimplex.δ j) ≫
        (cofiberJoinStdSimplexIso 1 (n + 1) (n + 3) (by omega)).hom =
      (cofiberJoinStdSimplexIso 1 n (n + 2) (by omega)).hom ≫
        SSet.stdSimplex.δ j.succ.succ := by
  apply join_hom_to_stdSimplex_ext
  · rw [← Category.assoc, joinInl_joinMap, Category.id_comp,
      cofiberJoinStdSimplexIso_inl, ← Category.assoc, cofiberJoinStdSimplexIso_inl]
    change SSet.stdSimplex.map _ = SSet.stdSimplex.map _ ≫
      SSet.stdSimplex.map (SimplexCategory.δ j.succ.succ)
    rw [← CategoryTheory.Functor.map_comp]
    apply congrArg SSet.stdSimplex.map
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    change cofiberJoinLeftOrderHom 1 (n + 1) (n + 3) (by omega) i =
      j.succ.succ.succAbove (cofiberJoinLeftOrderHom 1 n (n + 2) (by omega) i)
    rw [Fin.succAbove_of_castSucc_lt _ _ (by
      change i.val < j.val + 1 + 1
      have hi : i.val < 2 := i.isLt
      omega)]
    rfl
  · rw [← Category.assoc, joinInr_joinMap, Category.assoc,
      cofiberJoinStdSimplexIso_inr, ← Category.assoc, cofiberJoinStdSimplexIso_inr]
    change SSet.stdSimplex.map (SimplexCategory.δ j) ≫ SSet.stdSimplex.map _ =
      SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map (SimplexCategory.δ j.succ.succ)
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    apply congrArg SSet.stdSimplex.map
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    change cofiberJoinRightOrderHom 1 (n + 1) (n + 3) (by omega) (j.succAbove i) =
      j.succ.succ.succAbove (cofiberJoinRightOrderHom 1 n (n + 2) (by omega) i)
    have hi : cofiberJoinRightOrderHom 1 n (n + 2) (by omega) i = i.succ.succ := by
      apply Fin.ext
      change 1 + 1 + i.val = i.val + 1 + 1
      omega
    rw [hi, Fin.succ_succAbove_succ, Fin.succ_succAbove_succ]
    apply Fin.ext
    change 1 + 1 + (j.succAbove i).val = (j.succAbove i).val + 1 + 1
    omega

/-- 概要：左セルの可変頂点の面は、小さい左セルへ同じ面を後合成したもの。
方針：標準 join 同型の面の式を逆向きに使い、joinMap の合成則で整理する。
規約：固定の A,B は変えない。使われ方：左の dg nerve 単体の既知の面。 -/
lemma spanJoinLeft_face (n : ℕ) (j : Fin (n + 2)) :
    SSet.stdSimplex.δ j.succ.succ ≫ spanJoinLeft.{u} (n + 1) =
      spanJoinLeft n ≫ joinMap (𝟙 (SSet.horn 2 0 : SSet.{u})) (SSet.stdSimplex.δ j) := by
  have hi : SSet.stdSimplex.δ j.succ.succ ≫
      (cofiberJoinStdSimplexIso 1 (n + 1) (n + 3) (by omega)).inv =
      (cofiberJoinStdSimplexIso 1 n (n + 2) (by omega)).inv ≫
        joinMap (𝟙 (Δ[1] : SSet.{u})) (SSet.stdSimplex.δ j) := by
    apply (cancel_mono (cofiberJoinStdSimplexIso 1 (n + 1) (n + 3) (by omega)).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [cofiberJoinStdSimplexIso_right_face, Iso.inv_hom_id_assoc]
  simp only [spanJoinLeft, ← Category.assoc]
  rw [hi]
  simp only [Category.assoc]
  congr 1
  rw [← joinMap_comp, ← joinMap_comp]
  simp only [Category.id_comp, Category.comp_id]

/-- 概要：右セルの可変頂点の面は、小さい右セルへ同じ面を後合成したもの。
方針：標準 join 同型の面の式と joinMap の合成則を使う。
規約：固定の A,C は変えない。使われ方：右の dg nerve 単体の既知の面。 -/
lemma spanJoinRight_face (n : ℕ) (j : Fin (n + 2)) :
    SSet.stdSimplex.δ j.succ.succ ≫ spanJoinRight.{u} (n + 1) =
      spanJoinRight n ≫ joinMap (𝟙 (SSet.horn 2 0 : SSet.{u})) (SSet.stdSimplex.δ j) := by
  have hi : SSet.stdSimplex.δ j.succ.succ ≫
      (cofiberJoinStdSimplexIso 1 (n + 1) (n + 3) (by omega)).inv =
      (cofiberJoinStdSimplexIso 1 n (n + 2) (by omega)).inv ≫
        joinMap (𝟙 (Δ[1] : SSet.{u})) (SSet.stdSimplex.δ j) := by
    apply (cancel_mono (cofiberJoinStdSimplexIso 1 (n + 1) (n + 3) (by omega)).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [cofiberJoinStdSimplexIso_right_face, Iso.inv_hom_id_assoc]
  simp only [spanJoinRight, ← Category.assoc]
  rw [hi]
  simp only [Category.assoc]
  congr 1
  rw [← joinMap_comp, ← joinMap_comp]
  simp only [Category.id_comp, Category.comp_id]

end SerrePositivity.InfinityCategories
