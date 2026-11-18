module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionBlocks
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.IntervalVertexCoordinates

/-!
模型。文献の定義との比較は後で
# 全合成表のブロック境界での実際の共有行

概要：Berger–Fresse §1.5.7 の交互の水平・垂直成分が同じ置換行で接続することを示す。
方針：元の成分の始終置換を所属行で評価し、同じ部分合成へ移す。
規約：行長はまだ融合せず、行自体の一致を示す。
使われ方：全表の成功を共有行の融合で実際の合成経路へ移す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：水平合成行の第一射影は元の置換列への行表示（BF §1.5.7）。
方針：二つの map の合成を各頂点で比較する。
規約：選択長さは射影で忘れる。
使われ方：元の成分端点を実際の合成行へ移す。 -/
lemma fixedInnerRows_fst {m n : ℕ} (τ : Equiv.Perm (Fin n)) (k : Fin (m + 1))
    (vs : List (Equiv.Perm (Fin (m + 1)) × ℕ)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedInnerRows τ k vs).map Prod.fst =
      (vs.map Prod.fst).map (fun σ => List.ofFn (permutationComposition m n k σ τ).symm) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedInnerRows, List.map_map, Function.comp_def]

/-- 概要：垂直合成行の第一射影は元の置換列への行表示（BF §1.5.7）。
方針：二つの map の合成を各頂点で比較する。
規約：選択長さは射影で忘れる。
使われ方：元の成分端点を実際の合成行へ移す。 -/
lemma fixedOuterRows_fst {m n : ℕ} (σ : Equiv.Perm (Fin (m + 1))) (k : Fin (m + 1))
    (vs : List (Equiv.Perm (Fin n) × ℕ)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedOuterRows σ k vs).map Prod.fst =
      (vs.map Prod.fst).map (fun τ => List.ofFn (permutationComposition m n k σ τ).symm) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedOuterRows, List.map_map, Function.comp_def]

namespace TableCompositionData

/-- 概要：水平ブロックの実際の行数は水平次数＋1（BF §1.5.7）。
方針：置換行表示と重み付き頂点の長さを元の成分の行数へ戻す。
規約：次数零では一行。
使われ方：共有行融合後の経路の頂点数の照合。 -/
lemma horizontalRows_length {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) (i : ℕ) :
    (c.horizontalRows i).length = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerSegmentDegree c.outerWord.val c.slot i + 1 := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.horizontalRows, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedInnerRows, List.length_map,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReductionInterval.weightedVertices_length, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerComponentExtraction_length]

/-- 概要：垂直ブロックの実際の行数は垂直次数＋1（BF §1.5.7）。
方針：置換行表示と重み付き頂点の長さを元の成分の行数へ戻す。
規約：一文字成分も同じ式。
使われ方：共有行融合後の経路の頂点数の照合。 -/
lemma verticalRows_length {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) (i : Fin c.count) :
    (c.verticalRows i).length = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.segmentDegree c.innerWord.val c.cuts i + 1 := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.verticalRows, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedOuterRows, List.length_map,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReductionInterval.weightedVertices_length, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.componentExtraction_length]

/-- 概要：水平ブロックの各実際の行には重複文字がない（BF §1.5.7）。
方針：行を実際の合成置換の逆像列に戻す。
規約：選択長さには依存しない。
使われ方：共有行融合の非重複条件を元の表から供給する。 -/
lemma horizontalRows_nodup {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (i : ℕ) (row : List (Fin (m + n))) (hr : row ∈ (c.horizontalRows i).map Prod.fst) :
    row.Nodup := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.horizontalRows, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedInnerRows, List.map_map, List.mem_map] at hr
  obtain ⟨p, _, hp⟩ := hr
  subst row
  exact List.nodup_ofFn_ofInjective (permutationComposition m n c.slot p.1
    (c.inner (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow c.inner c.innerSchedule c.innerWord.val c.inner_success
      (c.innerPosition i)))).symm.injective

/-- 概要：垂直ブロックの各実際の行には重複文字がない（BF §1.5.7）。
方針：行を実際の合成置換の逆像列に戻す。
規約：選択長さには依存しない。
使われ方：共有行融合の非重複条件を元の表から供給する。 -/
lemma verticalRows_nodup {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (i : Fin c.count) (row : List (Fin (m + n)))
    (hr : row ∈ (c.verticalRows i).map Prod.fst) : row.Nodup := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.verticalRows, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedOuterRows, List.map_map, List.mem_map] at hr
  obtain ⟨p, _, hp⟩ := hr
  subst row
  exact List.nodup_ofFn_ofInjective (permutationComposition m n c.slot
    (c.outer (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow c.outer c.outerSchedule c.outerWord.val c.outer_success
      (c.outerPosition (i.val + 1)))) p.1).symm.injective

/-- 概要：水平末尾と直後の垂直先頭は同じ実際の行（BF §1.5.7）。
方針：外側終点と内側始点の元の置換を同じ有限境界で評価する。
規約：次数零の成分も含む。
使われ方：水平から垂直の共有二行を融合する。 -/
lemma horizontal_vertical_join {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (i : Fin c.count) :
    ((c.horizontalRows i.val).map Prod.fst).getLast? =
      ((c.verticalRows i).map Prod.fst).head? := by
  have hh := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerComponentExtraction c.outer c.outerSchedule c.outerWord c.outer_success
    c.slot (by omega) i.val).weightedVertices_last
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundaryPosition_mono c.outerWord.val c.slot (by omega) (by omega))
  have hv := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.componentExtraction c.inner c.innerSchedule c.innerWord c.inner_success c.cuts
    c.inner_positive i).weightedVertices_head
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.horizontalRows, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedInnerRows_fst, List.getLast?_map, hh,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.verticalRows, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedOuterRows_fst, List.head?_map, hv]
  simp only [Option.map_some, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.outerPosition, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.innerPosition, c.cuts.boundaryPosition_at]

/-- 概要：垂直末尾と次の水平先頭は同じ実際の行（BF §1.5.7）。
方針：内側終点を次の分割境界に戻し、外側固定行と次の始行を一致させる。
規約：最後の水平への接続も含む。
使われ方：垂直から水平の共有二行を融合する。 -/
lemma vertical_horizontal_join {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (i : Fin c.count) :
    ((c.verticalRows i).map Prod.fst).getLast? =
      ((c.horizontalRows (i.val + 1)).map Prod.fst).head? := by
  have hv := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.componentExtraction c.inner c.innerSchedule c.innerWord c.inner_success c.cuts
    c.inner_positive i).weightedVertices_last (c.cuts.startPosition_le_endPosition _ i)
  have hh := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerComponentExtraction c.outer c.outerSchedule c.outerWord c.outer_success
    c.slot (by omega) (i.val + 1)).weightedVertices_head
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.verticalRows, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedOuterRows_fst, List.getLast?_map, hv,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.horizontalRows, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedInnerRows_fst, List.head?_map, hh]
  simp only [Option.map_some, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.outerPosition, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.innerPosition, c.cuts.boundaryPosition_next]

end TableCompositionData

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
