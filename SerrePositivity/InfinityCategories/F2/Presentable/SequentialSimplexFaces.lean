module

public import SerrePositivity.InfinityCategories.Core.PinchedSlice

/-!
概要：右因子の最初の頂点の包含と標準単体の join 表示を比較する。
方針：各単体の切断の左右で連結順序写像の値を計算する。
規約：全 join 図式についての厳密な等式。
使われ方：指定辺を付け加えた有限図式が前段階を保つことの確認。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：右の辺の始点への制限は、結合した標準単体の最終頂点を除く面。
方針：左右の区間の連結順序写像の値を比較する。
規約：元の左単体を変更しない。
使われ方：余錐圏の指定辺から有限図式を延長する。 -/
lemma joinStdSimplexIso_rightEdge_zero (n : ℕ) :
    joinMap (𝟙 (Δ[n] : SSet.{u})) (SSet.stdSimplex.δ (1 : Fin 2)) ≫
      (joinStdSimplexIso n 1).hom =
    (joinStdSimplexIso n 0).hom ≫ SSet.stdSimplex.map (PinchedHom.front (n + 1)) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  change Join.Simplex (Δ[n] : SSet.{u}) Δ[0] d at s
  apply SSet.stdSimplex.ext
  intro i
  apply Fin.ext
  change (Join.concat s.1.val (Nat.le_of_lt_succ s.1.isLt)
    (Join.stdAugEquiv n _ (Join.augHom (𝟙 Δ[n]) _ s.2.1))
    (Join.stdAugEquiv 1 _ (Join.augHom
      (SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2))) _ s.2.2)) i).val =
    (Join.concat s.1.val (Nat.le_of_lt_succ s.1.isLt)
      (Join.stdAugEquiv n _ s.2.1) (Join.stdAugEquiv 0 _ s.2.2) i).val
  rw [Join.augHom_id, Join.stdAugEquiv_augHom]
  by_cases hi : i.val < s.1.val
  · rw [Join.concat_of_lt _ _ _ _ _ hi, Join.concat_of_lt _ _ _ _ _ hi]
  · rw [Join.concat_of_ge _ _ _ _ _ (Nat.le_of_not_gt hi),
      Join.concat_of_ge _ _ _ _ _ (Nat.le_of_not_gt hi)]
    have hδ (t : Fin 1) :
        ((SimplexCategory.δ (1 : Fin 2)).toOrderHom t).val = t.val := by
      fin_cases t
      rfl
    exact congrArg (fun k : ℕ ↦ n + 1 + k) (hδ _)

end SerrePositivity.InfinityCategories.F2.Presentable
