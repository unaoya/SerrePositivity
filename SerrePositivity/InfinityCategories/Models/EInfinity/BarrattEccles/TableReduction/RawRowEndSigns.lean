module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowEndOrder
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.RawCaesuraOrder

/-!
模型。文献の定義との比較は後で
# 退化出力を含む table の行末の削除符号

概要：Berger–Fresse §1.4.4 の相殺計算で必要な全ての成功 table の行末符号を与える。
方針：基底語の条件を使わず、再出現列と行末の昇順の列を比較する。
規約：退化・非全射の判定をする前の出力を扱う。
使われ方：零に正規化される table も含め、削除項の相殺と頂点境界を対応させる。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：任意の語の区切り列は同じ再出現列を持つ行末列と一致（BF §1.4.4）。
方針：狭義単調な位置の列の所属を比較する。
規約：全射性や非退化性を要求しない。
使われ方：退化した table で区切り番号を行番号に直す。 -/
lemma rawCaesuraList_val_eq_rowEnds {n l : ℕ} (v : Fin l → Fin n)
    (picked : List (List (Fin n))) (hn : ∀ row ∈ picked, row ≠ [])
    (he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.repeatPositions (List.ofFn v) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions picked) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawCaesuraList v).map (fun k => k.val) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions picked := by
  have hs : ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawCaesuraList v).map (fun k => k.val)).SortedLT := by
    rw [List.sortedLT_iff_pairwise, List.pairwise_map]
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawCaesuraList_sortedLT v).pairwise.imp (fun h => h)
  apply hs.eq_of_mem_iff (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions_sortedLT picked hn)
  intro k
  rw [← he]
  constructor
  · intro hk
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hk
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesura_iff_mem_repeatPositions v i).mp ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.mem_rawCaesuraList v i).mp hi)
  · intro hk
    obtain ⟨hb, _⟩ := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.mem_repeatPositions (List.ofFn v) k).mp hk
    have hb' : k < l := by simpa only [List.length_ofFn] using hb
    let i : Fin l := ⟨k, hb'⟩
    refine List.mem_map.mpr ⟨i, ?_, rfl⟩
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.mem_rawCaesuraList v i).mpr ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesura_iff_mem_repeatPositions v i).mpr hk)

/-- 概要：任意の語の第 i 行末の削除係数は (−1)^i（BF §1.4.4）。
方針：行末の Option 評価を区切りリストの評価に移す。
規約：退化した table 出力にも適用する。
使われ方：一文字行の削除符号を退化項も含めて頂点境界へ移す。 -/
lemma deletionCoefficient_raw_rowEnd {n l : ℕ} (v : Fin l → Fin n)
    (picked : List (List (Fin n))) (hn : ∀ row ∈ picked, row ≠ [])
    (he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.repeatPositions (List.ofFn v) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions picked) (i : ℕ) (k : Fin l)
    (hk : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions picked)[i]? = some k.val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient v k = (-1 : ℤ) ^ i := by
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rawCaesuraList_val_eq_rowEnds v picked hn he, List.getElem?_map] at hk
  cases hraw : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawCaesuraList v)[i]? with
  | none => simp only [hraw, Option.map_none, reduceCtorEq] at hk
  | some cut =>
    obtain ⟨hi, hcut⟩ := List.getElem?_eq_some_iff.mp hraw
    have hval : cut.val = k.val := by
      simpa only [hraw, Option.map_some, Option.some.injEq] using hk
    have hkc : k = cut := Fin.ext hval.symm
    subst k
    have hc := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient_raw_get v ⟨i, hi⟩
    have hget : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawCaesuraList v).get ⟨i, hi⟩ = cut := hcut
    rw [hget] at hc
    exact hc

/-- 概要：全ての成功した TR 項の行末と削除符号の証明書（BF §1.4.4）。
方針：行の分割と再出現列の一致を、出力の有限語へ直接適用する。
規約：出力に隣接重複があっても成立する。
使われ方：退化項を途中で捨てずに全 table の削除対を相殺する。 -/
lemma rawRowEndSigns_of_reduction {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (out : List (Fin n)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out) :
    ∃ picked, picked.flatten = out ∧ (∀ row ∈ picked, row ≠ []) ∧ picked.length = d + 1 ∧
      picked.map List.length = List.ofFn (fun i => (r.val i).val) ∧
      ∀ (i : Fin d) (k : Fin out.length), (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions picked)[i.val]? = some k.val →
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient (fun j : Fin out.length => out[j.val]) k = (-1 : ℤ) ^ i.val := by
  obtain ⟨picked, he, hn, hl, hlengths, hp⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEnds_of_reduction w r out h
  refine ⟨picked, he, hn, hl, hlengths, ?_⟩
  intro i k hk
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionCoefficient_raw_rowEnd _ picked hn _ i.val k hk
  simpa only [List.ofFn_getElem] using hp

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
