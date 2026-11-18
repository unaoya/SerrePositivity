module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.OutputOccurrences

/-!
模型。文献の定義との比較は後で
# 語の隙間による出力と切断点色の端点

概要：Berger–Fresse §2.2.7 の切断点色の端点置換を、重複のない隙間切断で表示する。
方針：隙間の前の文字へ零頂点、後の文字へ一頂点を割り当てる。
規約：隙間は先頭前と末尾後も含み、各文字はちょうど一つの側へ入る。
使われ方：隣接する非零切断の始点・終点置換が同じ出力族になることを示す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：隙間で二分した語の各色の出力頂点集合（BF §2.2.7）。
方針：隙間より前なら零、隙間以後なら一を対応させる。
規約：隙間は文字を重複させない。
使われ方：切断点色を頂点へ置換した出力を共通表示する。 -/
def gapOutputVertices {n l : ℕ} (u : Fin l → Fin n) (q : Fin (l + 1)) (k : Fin n) :
    Finset (Fin 2) :=
  (Finset.univ.filter (fun i => u i = k)).image (fun i => if i.val < q.val then 0 else 1)

/-- 概要：隙間出力の頂点所属は前後の同色出現で決まる（BF §2.2.7）。
方針：有限集合の像を展開し、隙間より前か後かを分ける。
規約：左は厳密不等号、右は広義不等号。
使われ方：切断端点の頂点集合との比較。 -/
lemma gapOutputVertices_mem_iff {n l : ℕ} (u : Fin l → Fin n) (q : Fin (l + 1))
    (k : Fin n) (b : Fin 2) : b ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapOutputVertices u q k ↔
      (b = 0 ∧ ∃ i, i.val < q.val ∧ u i = k) ∨
      (b = 1 ∧ ∃ i, q.val ≤ i.val ∧ u i = k) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapOutputVertices, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, hb⟩
    by_cases hq : i.val < q.val
    · exact Or.inl ⟨by simpa only [ite_eq_left hq] using hb.symm, i, hq, hi⟩
    · exact Or.inr ⟨by simpa only [ite_eq_right hq] using hb.symm, i, le_of_not_gt hq, hi⟩
  · rintro (⟨rfl, i, hi, hu⟩ | ⟨rfl, i, hi, hu⟩)
    · exact ⟨i, hu, ite_eq_left hi⟩
    · exact ⟨i, hu, ite_eq_right (not_lt_of_ge hi)⟩

/-- 概要：全射語の隙間出力は各色で非空（BF §2.2.7）。
方針：その色の任意の出現を前後のいずれかへ送る。
規約：先頭前・末尾後の隙間も含む。
使われ方：隙間出力を実際の区間単体にする。 -/
lemma gapOutputVertices_nonempty {n l : ℕ} (u : Fin l → Fin n) (hu : Function.Surjective u)
    (q : Fin (l + 1)) (k : Fin n) : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapOutputVertices u q k).Nonempty := by
  obtain ⟨i, hi⟩ := hu k
  exact Finset.Nonempty.image ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩ _

/-- 概要：全射語の隙間切断の出力単体族（BF §2.2.7）。
方針：非空な頂点集合を区間の単体として持ち上げる。
規約：語の次数による型変換を追加しない。
使われ方：端点項の望遠和の共通値。 -/
def gapOutput {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (q : Fin (n + d + 1)) (k : Fin n) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex :=
  ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapOutputVertices u.val q k, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapOutputVertices_nonempty u.val u.surjective q k⟩

/-- 概要：非零切断の切断点色を終点にすると直前の隙間出力（BF §2.2.7）。
方針：切断点色の唯一性でその色を一頂点へ固定し、他色は厳密な左側へ移す。
規約：終点は一頂点。
使われ方：隣接切断の境界値を同じ隙間出力へ同定する。 -/
lemma edgeOutput_pivot_endpoint_one {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (p : Fin (n + d))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p) :
    Function.update (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p) (u.val p) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex 1) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapOutput u p.castSucc := by
  funext k
  apply Subtype.ext
  apply Finset.ext
  intro b
  by_cases hk : k = u.val p
  · subst k
    rw [Function.update_self]
    change b ∈ ({1} : Finset (Fin 2)) ↔ b ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapOutputVertices u.val p.castSucc (u.val p)
    rw [Finset.mem_singleton, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapOutputVertices_mem_iff]
    simp only [Fin.val_castSucc]
    constructor
    · intro hb
      exact Or.inr ⟨hb, p, le_rfl, rfl⟩
    · rintro (⟨_, i, hi, hu⟩ | ⟨hb, _⟩)
      · have he := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivot_unique h i hu
        subst i
        exact False.elim ((lt_irrefl _) hi)
      · exact hb
  · rw [Function.update_of_ne hk]
    change b ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices u.val p k ↔ b ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapOutputVertices u.val p.castSucc k
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices_mem_iff, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapOutputVertices_mem_iff]
    simp only [Fin.val_castSucc]
    have hl : (∃ i, i ≤ p ∧ u.val i = k) ↔ ∃ i, i.val < p.val ∧ u.val i = k := by
      constructor
      · rintro ⟨i, hi, hu⟩
        refine ⟨i, ?_, hu⟩
        exact lt_of_le_of_ne hi (fun he => hk (hu.symm.trans (congrArg u.val (Fin.ext he))))
      · rintro ⟨i, hi, hu⟩
        exact ⟨i, le_of_lt hi, hu⟩
    rw [hl]
    rfl

/-- 概要：非零切断の切断点色を始点にすると直後の隙間出力（BF §2.2.7）。
方針：切断点色の唯一性でその色を零頂点へ固定し、他色は厳密な右側へ移す。
規約：始点は零頂点。
使われ方：隣接切断の境界値を同じ隙間出力へ同定する。 -/
lemma edgeOutput_pivot_endpoint_zero {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (p : Fin (n + d))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p) :
    Function.update (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p) (u.val p) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex 0) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapOutput u p.succ := by
  funext k
  apply Subtype.ext
  apply Finset.ext
  intro b
  by_cases hk : k = u.val p
  · subst k
    rw [Function.update_self]
    change b ∈ ({0} : Finset (Fin 2)) ↔ b ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapOutputVertices u.val p.succ (u.val p)
    rw [Finset.mem_singleton, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapOutputVertices_mem_iff]
    simp only [Fin.val_succ]
    constructor
    · intro hb
      exact Or.inl ⟨hb, p, by omega, rfl⟩
    · rintro (⟨hb, _⟩ | ⟨_, i, hi, hu⟩)
      · exact hb
      · have he := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivot_unique h i hu
        subst i
        omega
  · rw [Function.update_of_ne hk]
    change b ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices u.val p k ↔ b ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapOutputVertices u.val p.succ k
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices_mem_iff, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapOutputVertices_mem_iff]
    simp only [Fin.val_succ]
    have hl : (∃ i, i ≤ p ∧ u.val i = k) ↔ ∃ i, i.val < p.val + 1 ∧ u.val i = k := by
      constructor <;> rintro ⟨i, hi, hu⟩ <;> exact ⟨i, by omega, hu⟩
    have hr : (∃ i, p ≤ i ∧ u.val i = k) ↔ ∃ i, p.val + 1 ≤ i.val ∧ u.val i = k := by
      constructor
      · rintro ⟨i, hi, hu⟩
        refine ⟨i, ?_, hu⟩
        have hne : i ≠ p := fun he => hk (hu.symm.trans (congrArg u.val he))
        have hv : i.val ≠ p.val := fun he => hne (Fin.ext he)
        omega
      · rintro ⟨i, hi, hu⟩
        exact ⟨i, by change p.val ≤ i.val; omega, hu⟩
    rw [hl, hr]

/-- 概要：先頭前の隙間では全出力が一頂点（BF §2.2.7）。
方針：全出現が右側へ入ることと全射性を使う。
規約：空語の空出力族も含む。
使われ方：次数零の望遠和の入力辺の終点。 -/
lemma gapOutput_first {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapOutput u 0 = fun _ => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex 1 := by
  funext k
  apply Subtype.ext
  apply Finset.ext
  intro b
  change b ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapOutputVertices u.val 0 k ↔ b ∈ ({1} : Finset (Fin 2))
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapOutputVertices_mem_iff, Finset.mem_singleton]
  simp only [Fin.val_zero, Nat.not_lt_zero, false_and, exists_false, and_false,
    zero_le, true_and, false_or]
  exact and_iff_left (u.surjective k)

/-- 概要：末尾後の隙間では全出力が零頂点（BF §2.2.7）。
方針：全出現が左側へ入ることと全射性を使う。
規約：空語の空出力族も含む。
使われ方：次数零の望遠和の入力辺の始点。 -/
lemma gapOutput_last {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapOutput u (Fin.last (n + d)) = fun _ => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex 0 := by
  funext k
  apply Subtype.ext
  apply Finset.ext
  intro b
  change b ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapOutputVertices u.val (Fin.last (n + d)) k ↔ b ∈ ({0} : Finset (Fin 2))
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapOutputVertices_mem_iff, Finset.mem_singleton]
  simp only [Fin.val_last, Fin.is_lt, true_and, Nat.not_le_of_lt (Fin.is_lt _),
    false_and, exists_false, and_false, or_false]
  exact and_iff_left (u.surjective k)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
