module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableStarts

/-!
模型。文献の定義との比較は後で
# 隣接する区切りの間に区切りがないこと

概要：Berger–Fresse §1.4.2 の各 table 行の内部は最終出現だけからなる。
方針：昇順の区切りリストの添字の単調性を使う。
規約：行の開始位置を含み、行末の区切り位置を除く区間を考える。
使われ方：復元行の区間不変性を実際の標準頂点列に適用する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：指定した番号の区切り位置（BF §1.2.2）。
方針：昇順の区切りリストを Fin d で評価する。
規約：次数 d で区切りは d 個。
使われ方：隣接する標準頂点の間の移動する文字を指定する。 -/
def caesuraAt {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (i : Fin d) : Fin (n + d) :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraList v).get ⟨i.val, by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraList_length]; exact i.isLt⟩

/-- 概要：列挙された区切りは実際に再出現を持つ（BF §1.2.2）。
方針：リストの所属を区切り条件へ戻す。
規約：番号は範囲内。
使われ方：一文字の非自明な移動を適用する。 -/
lemma caesuraAt_caesura {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (i : Fin d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i) :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.mem_caesuraList v _).mp (List.get_mem _ _)

/-- 概要：次の行は指定した区切りの直後に始まる（BF §1.2.2）。
方針：開始位置の後続添字の式を使う。
規約：区切りを Fin d、行を Fin(d+1) で数える。
使われ方：移動後の復元行を次の標準頂点と同定する。 -/
lemma rowStart_succ_eq_caesuraAt {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (i : Fin d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.succ = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i).val + 1 := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart_succ v i

/-- 概要：行の開始位置から区切りまでには別の区切りがない（BF §1.4.2）。
方針：仮の区切りの添字は指定添字より小さく、前の区切り以下となって矛盾する。
規約：指定した区切り自体を区間に含めない。
使われ方：行内部で canonicalRow が不変であることを導く。 -/
lemma not_caesura_between_start_and_cut {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (i : Fin d)
    (k : Fin (n + d)) (hstart : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc ≤ k.val)
    (hcut : k.val < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i).val) : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v.val k := by
  intro hk
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.mem_caesuraList v k).mpr hk)
  have hij : j.val < i.val := by
    have hlt : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraList v).get j <
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraList v).get ⟨i.val, by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraList_length]; exact i.isLt⟩ := by
      rw [hj]
      exact hcut
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraList_sortedLT v).strictMono_get.lt_iff_lt.mp hlt
  have hipos : 0 < i.val := by omega
  let prev : Fin d := ⟨i.val - 1, by omega⟩
  have hsuc : prev.succ = i.castSucc := by
    apply Fin.ext
    change (i.val - 1) + 1 = i.val
    omega
  have hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v prev).val + 1 := by
    rw [← hsuc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart_succ_eq_caesuraAt]
  have hle : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraList v).get j ≤ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v prev := by
    apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraList_sortedLT v).strictMono_get.monotone
    change j.val ≤ i.val - 1
    omega
  rw [hj] at hle
  change k.val ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v prev).val at hle
  omega

/-- 概要：各行の開始位置はその末尾の区切り以下（BF §1.2.2）。
方針：次の行の開始位置の式と開始位置の狭義単調性を使う。
規約：最後の行を除く d 個の行について主張する。
使われ方：行内部の復元行の不変区間の両端を指定する。 -/
lemma rowStart_le_caesuraAt {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (i : Fin d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i).val := by
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart_strictMono v i.castSucc_lt_succ
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart_succ_eq_caesuraAt] at hs
  omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
