module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CaesuraGaps
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OccurrenceSuffixes

/-!
模型。文献の定義との比較は後で
# 最後の行の後続語の重複のなさ

概要：Berger–Fresse §1.4.2–3 の最後の行は全て最終出現からなる。
方針：最後の開始位置より後に区切りがあると、最大の区切り位置以下であることに反する。
規約：次数零の区切りがない場合も含める。
使われ方：標準 table の最後の行が残りの語全体を抽出することを示す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：最後の行の開始以後に区切りはない（BF §1.4.2）。
方針：仮の区切りは列挙された最大の区切り以下で、開始位置より前となる。
規約：次数零では区切りリストが空なので矛盾する。
使われ方：最後の行の尾部には全ての値が一度だけ現れる。 -/
lemma not_caesura_after_last_start {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (k : Fin (n + d))
    (hstart : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v (Fin.last d) ≤ k.val) : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v.val k := by
  intro hk
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.mem_caesuraList v k).mpr hk)
  have hjbound : j.val < d := by simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraList_length] using j.isLt
  have hd : 0 < d := by omega
  let lastCut : Fin d := ⟨d - 1, by omega⟩
  have hsuc : lastCut.succ = Fin.last d := by
    apply Fin.ext
    change (d - 1) + 1 = d
    omega
  have hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v (Fin.last d) = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v lastCut).val + 1 := by
    rw [← hsuc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart_succ_eq_caesuraAt]
  have hle : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraList v).get j ≤ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v lastCut := by
    apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraList_sortedLT v).strictMono_get.monotone
    change j.val ≤ d - 1
    omega
  rw [hj] at hle
  change k.val ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v lastCut).val at hle
  omega

/-- 概要：区切りのない尾部には重複がない（BF §1.4.2）。
方針：異なる二位置の同値から小さい方の位置が区切りであることを導く。
規約：開始位置は自然数で、終端以後の空尾部も含む。
使われ方：最初の出現の選択が最後の行では恒等であることを示す。 -/
lemma suffix_nodup_of_no_caesura {n l : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word n l) (p : ℕ)
    (h : ∀ i : Fin l, p ≤ i.val → ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v.val i) :
    ((List.ofFn v.val).drop p).Nodup := by
  apply List.nodup_iff_injective_getElem.mpr
  intro i j he
  have hi : p + i.val < l := by
    have hi := i.isLt
    simp only [List.length_drop, List.length_ofFn] at hi
    omega
  have hj : p + j.val < l := by
    have hj := j.isLt
    simp only [List.length_drop, List.length_ofFn] at hj
    omega
  have hv : v.val ⟨p + i.val, hi⟩ = v.val ⟨p + j.val, hj⟩ := by
    simpa only [List.getElem_drop, List.getElem_ofFn] using he
  apply Fin.ext
  rcases lt_trichotomy i.val j.val with hij | hij | hij
  · exact False.elim (h ⟨p + i.val, hi⟩ (by change p ≤ p + i.val; omega)
      ⟨⟨p + j.val, hj⟩, by change p + i.val < p + j.val; omega, hv.symm⟩)
  · exact hij
  · exact False.elim (h ⟨p + j.val, hj⟩ (by change p ≤ p + j.val; omega)
      ⟨⟨p + i.val, hi⟩, by change p + j.val < p + i.val; omega, hv⟩)

/-- 概要：最後の行の尾部は重複しない（BF §1.4.2–3）。
方針：最後の開始位置以後の区切りの不在を尾部の一般補題へ適用する。
規約：空語も含む。
使われ方：標準 table の最後の行の抽出を簡約する。 -/
lemma last_suffix_nodup {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) :
    ((List.ofFn v.val).drop (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v (Fin.last d))).Nodup :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.suffix_nodup_of_no_caesura v _ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.not_caesura_after_last_start v)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
