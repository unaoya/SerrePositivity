module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowEndPositions
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CaesuraRanks

/-!
模型。文献の定義との比較は後で
# 行末の順序と区切りの番号の一致

概要：Berger–Fresse §1.4.4 の行番号と語の区切り番号を同定する。
方針：非空行の末尾の位置は狭義単調で、同じ位置集合を持つ昇順の列は等しい。
規約：非退化な全射語の caesuraList と比較する。
使われ方：各非最終行末の削除符号が行番号の交代符号になることを示す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：非空行の末尾の位置は狭義単調（BF §1.4.4）。
方針：後続の位置には現在行の正の長さが加わる。
規約：全ての行が非空であれば分離条件は不要。
使われ方：行末の順序を区切りの昇順の列と比較する。 -/
lemma rowEndPositions_sortedLT {α : Type*} (picked : List (List α)) :
    (∀ row ∈ picked, row ≠ []) → (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions picked).SortedLT := by
  induction picked with
  | nil => intro _; simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions, List.sortedLT_iff_pairwise]
  | cons row rest ih =>
    intro hn
    have hr : 0 < row.length := List.length_pos_iff.mpr (hn row (List.mem_cons_self ..))
    have hnrest : ∀ r ∈ rest, r ≠ [] := fun r hm => hn r (List.mem_cons_of_mem _ hm)
    cases rest with
    | nil => simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions, List.sortedLT_iff_pairwise]
    | cons next rest =>
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions, List.sortedLT_cons]
      constructor
      · intro b hb
        obtain ⟨k, _, rfl⟩ := List.mem_map.mp hb
        omega
      · rw [List.sortedLT_iff_pairwise, List.pairwise_map]
        apply List.Pairwise.imp _ (ih hnrest).pairwise
        intro a b hab
        omega

/-- 概要：基底語の区切り列の自然数位置は狭義単調（BF §1.2.2）。
方針：Fin の狭義順序を自然数値の順序へ移す。
規約：位置の順序だけを使う。
使われ方：table の行末の列との等式を証明する。 -/
lemma caesuraList_val_sortedLT {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraList v).map (fun i => i.val)).SortedLT := by
  rw [List.sortedLT_iff_pairwise, List.pairwise_map]
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraList_sortedLT v).pairwise.imp (fun h => h)

/-- 概要：区切りの昇順の列は行末位置の列そのもの（BF §1.4.4）。
方針：再出現位置を共有する二つの狭義単調列の所属を比較する。
規約：出力は非退化な全射語として指定する。
使われ方：第 i 行末を第 i 区切り位置と同定する。 -/
lemma caesuraList_val_eq_rowEnds {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d)
    (picked : List (List (Fin n))) (hn : ∀ row ∈ picked, row ≠ [])
    (he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.repeatPositions (List.ofFn v.val) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions picked) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraList v).map (fun i => i.val) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions picked := by
  apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.caesuraList_val_sortedLT v).eq_of_mem_iff (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions_sortedLT picked hn)
  intro k
  rw [← he]
  constructor
  · intro hk
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hk
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesura_iff_mem_repeatPositions v.val i).mp ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.mem_caesuraList v i).mp hi)
  · intro hk
    obtain ⟨hb, _⟩ := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.mem_repeatPositions (List.ofFn v.val) k).mp hk
    have hb' : k < n + d := by simpa only [List.length_ofFn] using hb
    let i : Fin (n + d) := ⟨k, hb'⟩
    refine List.mem_map.mpr ⟨i, ?_, rfl⟩
    apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.mem_caesuraList v i).mpr
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesura_iff_mem_repeatPositions v.val i).mpr hk

/-- 概要：区切りの有限添字の評価は同じ番号の行末の位置（BF §1.4.4）。
方針：二つのリストの等式を添字で評価する。
規約：行末の番号は Fin d。
使われ方：実際の語の削除係数を行番号の符号へ移す。 -/
lemma caesuraAt_val_eq_rowEnd {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d)
    (picked : List (List (Fin n))) (hn : ∀ row ∈ picked, row ≠ [])
    (he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.repeatPositions (List.ofFn v.val) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions picked) (i : Fin d) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i).val = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions picked).get
      ⟨i.val, by rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.caesuraList_val_eq_rowEnds v picked hn he, List.length_map,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraList_length]; exact i.isLt⟩ := by
  have hlist := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.caesuraList_val_eq_rowEnds v picked hn he
  have hl : i.val < ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraList v).map (fun k => k.val)).length := by
    rw [List.length_map, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraList_length]
    exact i.isLt
  have hr : i.val < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions picked).length := by rw [← hlist]; exact hl
  have hlookup := congrArg (fun xs : List ℕ => xs[i.val]?) hlist
  rw [List.getElem?_eq_getElem hl, List.getElem?_eq_getElem hr] at hlookup
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt, List.get_eq_getElem, List.getElem_map] using Option.some.inj hlookup

/-- 概要：第 i 非最終行末の削除係数は (−1)^i（BF §1.4.4）。
方針：行末の添字評価を同じ番号の区切りへ移し、区切り順位の符号を使う。
規約：有効な行末位置を Option の評価で指定する。
使われ方：一文字行の削除項を頂点境界の符号に対応させる。 -/
lemma deletionCoefficient_rowEnd {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d)
    (picked : List (List (Fin n))) (hn : ∀ row ∈ picked, row ≠ [])
    (he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.repeatPositions (List.ofFn v.val) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions picked)
    (i : Fin d) (k : Fin (n + d))
    (hk : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions picked)[i.val]? = some k.val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient v.val k = (-1 : ℤ) ^ i.val := by
  have hlist := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.caesuraList_val_eq_rowEnds v picked hn he
  have hb : i.val < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions picked).length := by
    rw [← hlist, List.length_map, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraList_length]
    exact i.isLt
  have hlookup : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions picked)[i.val]? = some (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i).val := by
    rw [List.getElem?_eq_getElem hb]
    exact congrArg some (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.caesuraAt_val_eq_rowEnd v picked hn he i).symm
  have hki : k = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i := Fin.ext (Option.some.inj (hk.symm.trans hlookup))
  rw [hki, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient_caesuraAt]

/-- 概要：成功した非退化 TR 項の全行末と削除符号の証明書（BF §1.4.4）。
方針：実際の行の分割・区切り列の一致・各区切りの順位をまとめる。
規約：Table の全行長は入力の Schedule と同じ順で保持する。
使われ方：微分保存の一文字行と一般の相殺対の符号の計算に適用する。 -/
lemma rowEndSigns_of_reduction {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some (List.ofFn v.val)) :
    ∃ picked, picked.flatten = List.ofFn v.val ∧ (∀ row ∈ picked, row ≠ []) ∧
      picked.length = d + 1 ∧ picked.map List.length = List.ofFn (fun i => (r.val i).val) ∧
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraList v).map (fun k => k.val) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions picked ∧
      ∀ (i : Fin d) (k : Fin (n + d)), (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions picked)[i.val]? = some k.val →
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient v.val k = (-1 : ℤ) ^ i.val := by
  obtain ⟨picked, he, hn, hl, hlengths, hp⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEnds_of_reduction w r _ h
  refine ⟨picked, he, hn, hl, hlengths, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.caesuraList_val_eq_rowEnds v picked hn hp, ?_⟩
  intro i k hk
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionCoefficient_rowEnd v picked hn hp i k hk

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
