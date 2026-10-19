module

public import SerrePositivity.EInfinity.Surjection.CompositionPathRows
public import SerrePositivity.EInfinity.Surjection.ComponentWalkVertices

/-!
# 元の融合格子列と成分次数歩行の一致

概要：Berger–Fresse §1.5.7 の元の境界行番号から作る融合格子列を成分次数の歩行へ同定する。
方針：未消費の成分次数対を一つずつ取り出し、元の両座標の更新式へ合わせる。
規約：最後の水平成分まで同じ自然数座標で比較する。
使われ方：実際の compositionPath の全座標列との一般の一致を閉じる。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.Surjection.TableCompositionData

/-- 概要：未消費の成分次数対の先頭は同じ垂直と次の水平次数（BF §1.5.7）。
方針：有限列の指定位置と残りの drop を分離する。
規約：出現番号を一つ進める。
使われ方：融合格子列の帰納と既存の成分次数列を揃える。 -/
lemma degreePairs_drop_step {m n d e : ℕ} (c : TableCompositionData m n d e)
    (i : Fin c.count) :
    (compositionDegreePairs c.outerWord c.innerWord c.slot c.cuts).drop i.val =
      (segmentDegree c.innerWord.val c.cuts i,
        outerSegmentDegree c.outerWord.val c.slot (i.val + 1)) ::
          (compositionDegreePairs c.outerWord c.innerWord c.slot c.cuts).drop (i.val + 1) := by
  have hp : i.val < (compositionDegreePairs c.outerWord c.innerWord c.slot c.cuts).length := by
    simpa only [compositionDegreePairs, List.length_ofFn] using i.isLt
  have h := List.getElem_cons_drop hp
  simpa only [compositionDegreePairs, List.getElem_ofFn] using h.symm

/-- 概要：全成分消費後の成分次数列は空（BF §1.5.7）。
方針：元の有限成分列の個数を使う。
規約：最後の水平成分はこの列の外側に保持する。
使われ方：融合格子列の帰納の終端。 -/
lemma degreePairs_drop_last {m n d e : ℕ} (c : TableCompositionData m n d e) :
    (compositionDegreePairs c.outerWord c.innerWord c.slot c.cuts).drop c.count = [] := by
  apply List.drop_eq_nil_of_le
  simp only [compositionDegreePairs, List.length_ofFn, Nat.le_refl]

/-- 概要：元の全後続融合格子列は元の境界からの成分次数歩行（BF §1.5.7）。
方針：未消費成分の列を分離し、水平・垂直の実際の所属行更新で帰納する。
規約：次数零の成分も同じ再帰。
使われ方：第零境界で実際の compositionPath の座標列へ戻す。 -/
lemma fusedGrid_eq_walk {m n d e : ℕ} (c : TableCompositionData m n d e)
    (i : ℕ) (hi : i ≤ c.count) : c.fusedGridVertices i =
      DegreePath.walkVertices (c.outerGrid i) (c.innerGrid i)
        (outerSegmentDegree c.outerWord.val c.slot i)
        ((compositionDegreePairs c.outerWord c.innerWord c.slot c.cuts).drop i) := by
  by_cases hlt : i < c.count
  · conv_lhs => rw [fusedGridVertices, dite_eq_left hlt]
    conv_rhs =>
      rw [c.degreePairs_drop_step ⟨i, hlt⟩, DegreePath.walkVertices,
        c.outerGrid_step i, c.innerGrid_step ⟨i, hlt⟩]
    rw [c.fusedGrid_eq_walk (i + 1) (by omega)]
    rfl
  · have he : i = c.count := by omega
    subst i
    rw [fusedGridVertices, dite_eq_right (Nat.lt_irrefl _), c.degreePairs_drop_last,
      DegreePath.walkVertices]
    rfl
termination_by c.count - i
decreasing_by omega

/-- 概要：元の融合格子列の始点は第零格子点（BF §1.5.7）。
方針：元の出現境界と内側分割境界が零であることを行番号へ移す。
規約：指定値が全射語に一回以上現れることを使う。
使われ方：実際の経路の零始点と一致させる。 -/
lemma grid_zero {m n d e : ℕ} (c : TableCompositionData m n d e) :
    c.outerGrid 0 = 0 ∧ c.innerGrid 0 = 0 := by
  have hz := c.cuts.boundaryPosition_zero c.inner_positive
    (occurrenceCount_pos c.outerWord c.slot)
  change c.cuts.boundary 0 = 0 at hz
  simp only [outerGrid, innerGrid, occurrenceBoundary_zero, hz, lineRank_zero, and_self]

/-- 概要：実際の compositionPath の全座標列は元の全融合格子列に一致（BF §1.5.7）。
方針：両方を同じ零始点の成分次数歩行へ戻す。
規約：元の二表の成功と分割以外の座標一致を仮定しない。
使われ方：実際の経路表の一般の合成語抽出成功を構成する。 -/
lemma compositionPath_vertices_eq_grid {m n d e : ℕ} (c : TableCompositionData m n d e) :
    DegreePath.vertices (compositionPath c.outerWord c.innerWord c.slot c.cuts) =
      c.fusedGridVertices 0 := by
  rw [c.fusedGrid_eq_walk 0 (Nat.zero_le _), List.drop_zero,
    c.grid_zero.1, c.grid_zero.2, DegreePath.walkVertices_eq_blocks]
  rw [compositionPath_vertices]
  have hs : DegreePath.shift (outerSegmentDegree c.outerWord.val c.slot 0) 0 =
      (fun z : ℕ × ℕ => (outerSegmentDegree c.outerWord.val c.slot 0 + z.1, z.2)) := by
    funext z
    simp only [DegreePath.shift, Nat.zero_add]
  simp only [DegreePath.horizontalAt, hs, Nat.zero_add]

end SerrePositivity.EInfinity.Surjection.TableCompositionData
