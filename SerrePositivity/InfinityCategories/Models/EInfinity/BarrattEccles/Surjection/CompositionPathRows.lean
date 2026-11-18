module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.FusedGridRows
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleComponent

/-!
模型。文献の定義との比較は後で
# 実際の compositionPath 上の元の置換列と行列

概要：Berger–Fresse §1.5.7 の実際の shuffle 合成の置換列を格子座標の行表示へ戻す。
方針：元の有限頂点評価と範囲内の rowAtGrid の一致を使う。
規約：全融合表との一致は座標列の等式を明示した条件として分離する。
使われ方：残る座標列の純粋な一致から実際の table reduction の成功を導く。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：実際の compositionPath に沿う元の置換部分合成列（BF §1.5.7）。
方針：経路の二座標で元の二つの置換列を評価する。
規約：既存の shuffleSimplex の頂点公式と同じ列。
使われ方：実際の TR の Schedule を評価する入力。 -/
noncomputable def pathSequence {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (k : Fin (d + e + 1)) : Equiv.Perm (Fin (m + n)) :=
  permutationComposition m n c.slot
    (c.outer ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionPath c.outerWord c.innerWord c.slot c.cuts).horizontal k))
    (c.inner ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionPath c.outerWord c.innerWord c.slot c.cuts).vertical k))

/-- 概要：実際の経路置換列の行列は全経路座標への rowAtGrid（BF §1.5.7）。
方針：各頂点の有限二座標で範囲内の評価を同定する。
規約：行長は元の融合表から構成済みの fusedSchedule を使う。
使われ方：座標列の等式を実際の表の行列等式へ移す。 -/
lemma pathSequence_rows_grid {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows c.pathSequence c.fusedSchedule).map Prod.fst =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertices (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionPath c.outerWord c.innerWord c.slot c.cuts)).map
        c.rowAtGrid := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.map_ofFn, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertices, Function.comp_def]
  apply congrArg List.ofFn
  funext k
  exact (c.rowAtGrid_valid
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionPath c.outerWord c.innerWord c.slot c.cuts).horizontal k)
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionPath c.outerWord c.innerWord c.slot c.cuts).vertical k)).symm

/-- 概要：経路の座標列が元の融合格子座標と一致すれば実際の全表も一致（BF §1.5.7）。
方針：両方の行列を同じ rowAtGrid の map とし、実際の行長で復元する。
規約：座標列の全体一致は明示した未解決の入力。
使われ方：次に座標列を同定したとき実際の経路表を直ちに得る。 -/
lemma rows_pathSequence_of_vertices {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (hv : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertices (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionPath c.outerWord c.innerWord c.slot c.cuts) =
      c.fusedGridVertices 0) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows c.pathSequence c.fusedSchedule = c.fusedRows 0 := by
  apply c.rows_fusedSchedule_of_fst
  rw [c.pathSequence_rows_grid, hv, ← c.fusedRows_eq_grid 0 (Nat.zero_le _)]

/-- 概要：座標列の全体一致から実際の経路表の合成語抽出成功（BF §1.5.7）。
方針：実際の経路表を元の成功済み融合表へ戻す。
規約：一般の座標列一致の証明は後続で必要。
使われ方：TR 合成保存の正方向の経路上の成功。 -/
lemma pathSequence_success_of_vertices {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (hv : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertices (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionPath c.outerWord c.innerWord c.slot c.cuts) =
      c.fusedGridVertices 0) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows c.pathSequence c.fusedSchedule) [] =
        some (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord c.outerWord c.innerWord c.slot c.cuts) := by
  rw [c.rows_pathSequence_of_vertices hv]
  exact c.fused_success_compositeWord

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData
