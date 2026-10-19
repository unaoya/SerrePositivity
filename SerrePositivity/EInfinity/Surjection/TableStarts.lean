module

public import SerrePositivity.EInfinity.Surjection.Caesuras
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.FinRange

/-!
# 区切り位置から得られる table の行の開始位置

概要：Berger–Fresse §1.2.2・§1.4.2 の d+1 個の行の開始位置を構成する。
方針：区切り位置を昇順に列挙し、その直後の位置の前に零を加える。
規約：開始位置は元の語の自然数添字。空語は零だけの列を持つ。
使われ方：全射語の各 table 行で復元する BE の頂点置換を指定する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.Surjection

/-- 概要：全射語の区切り位置の昇順のリスト（BF §1.2.2）。
方針：位置を昇順に列挙して区切りだけを残す。
規約：最終出現は含めない。
使われ方：行の順序と開始位置を固定する。 -/
def caesuraList {n d : ℕ} (v : BasisWord n d) : List (Fin (n + d)) :=
  (List.finRange (n + d)).filter (fun i => Caesura v.val i)

/-- 概要：区切り位置の列は狭義単調（BF §1.2.2）。
方針：昇順の位置リストの部分列であることを使う。
規約：有限の所属判定だけで列挙する。
使われ方：行の開始位置の正しい順序を保証する。 -/
lemma caesuraList_sortedLT {n d : ℕ} (v : BasisWord n d) : (caesuraList v).SortedLT := by
  rw [List.sortedLT_iff_pairwise]
  exact (List.sortedLT_finRange (n + d)).pairwise.filter _

/-- 概要：区切り位置の列は有限集合のソートと一致する（BF §1.2.2）。
方針：狭義単調な二列の所属集合を比較する。
規約：実装には構造的な有限列挙を使う。
使われ方：区切りの濃度をリストの長さへ移す。 -/
lemma caesuraList_eq_sort {n d : ℕ} (v : BasisWord n d) :
    caesuraList v = (Finset.univ.filter (Caesura v.val)).sort (· ≤ ·) := by
  apply (caesuraList_sortedLT v).eq_of_mem_iff (Finset.sortedLT_sort _)
  intro a
  simp [caesuraList]

/-- 概要：区切り位置のリストの長さは次数 d（BF §1.2.2）。
方針：sort の長さと区切りの濃度の公式を使う。
規約：零 arity・次数零も含む。
使われ方：開始位置を Fin(d+1) で添字づける。 -/
@[simp] lemma caesuraList_length {n d : ℕ} (v : BasisWord n d) :
    (caesuraList v).length = d := by
  rw [caesuraList_eq_sort, Finset.length_sort]
  simpa only [Fintype.card_subtype] using card_caesuras_basisWord v

/-- 概要：区切り位置の列の所属は元の区切り条件（BF §1.2.2）。
方針：sort と filter の所属判定を使う。
規約：語の位置自体を保つ。
使われ方：各行の開始位置が語の範囲内にあることを示す。 -/
@[simp] lemma mem_caesuraList {n d : ℕ} (v : BasisWord n d) (i : Fin (n + d)) :
    i ∈ caesuraList v ↔ Caesura v.val i := by simp [caesuraList]

/-- 概要：table の行の開始位置を昇順に並べる（BF §1.4.2）。
方針：各区切りの直後に開始位置を置き、最初に零を置く。
規約：語の位置を零から数える。
使われ方：復元する置換列の各頂点の引数となる。 -/
def rowStarts {n d : ℕ} (v : BasisWord n d) : List ℕ :=
  0 :: (caesuraList v).map (fun i => i.val + 1)

/-- 概要：table の行数は d+1（BF §1.2.2）。
方針：区切りの個数に最初の行を加える。
規約：空語でも最初の行の開始位置零を残す。
使われ方：開始位置を有限添字で評価する。 -/
@[simp] lemma rowStarts_length {n d : ℕ} (v : BasisWord n d) :
    (rowStarts v).length = d + 1 := by simp only [rowStarts, List.length_cons,
      List.length_map, caesuraList_length]

/-- 概要：全射語の指定した行の開始位置（BF §1.4.2）。
方針：開始位置のリストを有限添字で評価する。
規約：i=0 は最初の行。
使われ方：canonicalPermutation の評価位置を与える。 -/
def rowStart {n d : ℕ} (v : BasisWord n d) (i : Fin (d + 1)) : ℕ :=
  (rowStarts v).get ⟨i.val, by rw [rowStarts_length]; exact i.isLt⟩

/-- 概要：最初の行は語の先頭から始まる（BF §1.4.2）。
方針：開始位置のリストの先頭を評価する。
規約：空語でも成立する。
使われ方：最初の頂点置換を簡約する。 -/
@[simp] lemma rowStart_zero {n d : ℕ} (v : BasisWord n d) : rowStart v 0 = 0 := rfl

/-- 概要：次の行は対応する区切りの直後から始まる（BF §1.4.2）。
方針：開始位置のリストの後続部分を評価する。
規約：区切りは昇順で番号づける。
使われ方：隣接頂点の移動する文字の位置を指定する。 -/
lemma rowStart_succ {n d : ℕ} (v : BasisWord n d) (i : Fin d) :
    rowStart v i.succ =
      ((caesuraList v).get ⟨i.val, by rw [caesuraList_length]; exact i.isLt⟩).val + 1 := by
  simp only [rowStart, rowStarts, List.get_eq_getElem, Fin.val_succ,
    List.getElem_cons_succ, List.getElem_map]

/-- 概要：開始位置は語の長さを超えない（BF §1.4.2）。
方針：先頭は零、残りは実際の区切り位置の次である。
規約：空語を含むため不等式は弱い形で述べる。
使われ方：復元される行の先頭部分と尾部を正しく分割する。 -/
lemma rowStart_le_length {n d : ℕ} (v : BasisWord n d) (i : Fin (d + 1)) :
    rowStart v i ≤ n + d := by
  obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ i
  · simp only [rowStart_zero, Nat.zero_le]
  · rw [rowStart_succ]
    exact ((caesuraList v).get _).isLt

/-- 概要：行の開始位置は狭義単調に並ぶ（BF §1.2.2）。
方針：区切り位置のソートと正の後続位置の列から導く。
規約：最初の零は全ての区切りの直後より小さい。
使われ方：隣接する開始位置の差が正の行長となることを示す。 -/
lemma rowStarts_sortedLT {n d : ℕ} (v : BasisWord n d) : (rowStarts v).SortedLT := by
  rw [rowStarts, List.sortedLT_cons]
  constructor
  · intro b hb
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hb
    omega
  · rw [List.sortedLT_iff_pairwise, List.pairwise_map]
    apply List.Pairwise.imp _ (List.sortedLT_iff_pairwise.mp (caesuraList_sortedLT v))
    intro a b hab
    exact Nat.succ_lt_succ hab

/-- 概要：有限添字で評価する行の開始位置も狭義単調（BF §1.2.2）。
方針：ソートされた開始位置のリストの評価の単調性を使う。
規約：添字は Fin(d+1)。
使われ方：復元する table の各行長の正値性を導く。 -/
lemma rowStart_strictMono {n d : ℕ} (v : BasisWord n d) : StrictMono (rowStart v) := by
  intro i j hij
  change (rowStarts v).get _ < (rowStarts v).get _
  apply (rowStarts_sortedLT v).strictMono_get
  exact hij

/-- 概要：正の arity で各行の開始位置は終端より真に前（BF §1.2.2）。
方針：区切りは後に同値が現れるので最終位置にはならない。
規約：空語は除き、非空語で主張する。
使われ方：最後の行の長さが正になることを示す。 -/
lemma rowStart_lt_length {n d : ℕ} (v : BasisWord n d) (hn : 0 < n)
    (i : Fin (d + 1)) : rowStart v i < n + d := by
  obtain rfl | ⟨k, rfl⟩ := Fin.eq_zero_or_eq_succ i
  · rw [rowStart_zero]
    omega
  · rw [rowStart_succ]
    let p : Fin d := k
    let cut := (caesuraList v).get ⟨p.val, by rw [caesuraList_length]; exact p.isLt⟩
    have hc : Caesura v.val cut :=
      (mem_caesuraList v cut).mp (List.get_mem (caesuraList v) _)
    obtain ⟨j, hj, _⟩ := hc
    have hval : cut.val < j.val := hj
    have hb := j.isLt
    change cut.val + 1 < n + d
    omega

end SerrePositivity.EInfinity.Surjection
