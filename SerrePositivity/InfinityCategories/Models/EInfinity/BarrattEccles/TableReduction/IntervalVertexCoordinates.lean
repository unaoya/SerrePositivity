module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.IntervalVertices

/-!
模型。文献の定義との比較は後で
# 成分区間の実際の置換頂点の座標

概要：Berger–Fresse §1.5.7 の成分の頂点列が元の連続する頂点列であることを公開する。
方針：元の行表示の一致から zip の長さを揃え、第一射影を復元する。
規約：端点を重ねた閉区間の全頂点を保持する。
使われ方：水平・垂直の接続点の置換の一致と共有行の融合。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReductionInterval

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：成分の置換・長さ列の長さは元の成分行数（BF §1.5.7）。
方針：元の成分行列への復元に長さを適用する。
規約：各行に置換一つ。
使われ方：成分次数と実際のブロック長の照合。 -/
lemma weightedVertices_length {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}
    {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d} {v : Fin (n + d) → Fin n}
    {h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some (List.ofFn v)} {p q : Fin (n + d)}
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReductionInterval w r v h p q) : c.weightedVertices.length = c.part.length := by
  have he := congrArg List.length c.permutationRows_eq
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationRows, List.length_map] using he

/-- 概要：成分の置換列は元の連続する頂点列そのもの（BF §1.5.7）。
方針：元の行列表示の長さの一致で zip の第一射影を復元する。
規約：新たな置換を選ばない。
使われ方：隣接するブロックの共有置換の同定。 -/
lemma weightedVertices_fst {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}
    {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d} {v : Fin (n + d) → Fin n}
    {h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some (List.ofFn v)} {p q : Fin (n + d)}
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReductionInterval w r v h p q) :
    c.weightedVertices.map Prod.fst = ((List.ofFn w).drop (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v p.val)).take
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v q.val - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v p.val + 1) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReductionInterval.weightedVertices
  apply List.map_fst_zip
  have hs := congrArg List.length c.source
  simp only [List.length_map, List.length_take, List.length_drop, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.length_ofFn] at hs ⊢
  omega

/-- 概要：成分の各頂点は元の開始行からの連続した座標を持つ（BF §1.5.7）。
方針：第一射影の閉区間表示を有限添字で評価する。
規約：元の行数内の座標を使う。
使われ方：接続点と経路上の全頂点の照合。 -/
lemma weightedVertices_vertex {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}
    {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d} {v : Fin (n + d) → Fin n}
    {h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some (List.ofFn v)} {p q : Fin (n + d)}
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReductionInterval w r v h p q) (j : ℕ)
    (hj : j < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v q.val - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v p.val + 1)
    (hb : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v p.val + j < d + 1) :
    (c.weightedVertices.map Prod.fst)[j]? = some (w ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v p.val + j, hb⟩) := by
  rw [c.weightedVertices_fst, List.getElem?_take_of_lt hj, List.getElem?_drop,
    List.getElem?_ofFn, dite_eq_left hb]

/-- 概要：成分の先頭置換は元の始点の所属行の置換（BF §1.5.7）。
方針：第零頂点の座標を評価する。
規約：成分が次数零でも同じ式。
使われ方：前のブロックの終点との共有置換の同定。 -/
lemma weightedVertices_head {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}
    {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d} {v : Fin (n + d) → Fin n}
    {h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some (List.ofFn v)} {p q : Fin (n + d)}
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReductionInterval w r v h p q) :
    (c.weightedVertices.map Prod.fst).head? = some (w (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow w r v h p)) := by
  rw [List.head?_eq_getElem?]
  exact c.weightedVertices_vertex 0 (by omega) (by
    simpa only [Nat.add_zero, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow] using (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow w r v h p).isLt)

/-- 概要：成分の末尾置換は元の終点の所属行の置換（BF §1.5.7）。
方針：元の成分長と行番号の単調性で最終頂点の座標を評価する。
規約：元の語の始点は終点以前。
使われ方：次のブロックの先頭との共有置換の同定。 -/
lemma weightedVertices_last {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}
    {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d} {v : Fin (n + d) → Fin n}
    {h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some (List.ofFn v)} {p q : Fin (n + d)}
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReductionInterval w r v h p q) (hpq : p ≤ q) :
    (c.weightedVertices.map Prod.fst).getLast? = some (w (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow w r v h q)) := by
  have hmono := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank_mono v hpq
  have he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v p.val + (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v q.val - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v p.val) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v q.val := by omega
  rw [List.getLast?_eq_getElem?, List.length_map, c.weightedVertices_length, c.length]
  simp only [Nat.add_sub_cancel]
  have hb : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v p.val + (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v q.val - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v p.val) < d + 1 := by
    rw [he]
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow w r v h q).isLt
  have hv := c.weightedVertices_vertex (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v q.val - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v p.val) (by omega) hb
  simpa only [he, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow] using hv

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReductionInterval
