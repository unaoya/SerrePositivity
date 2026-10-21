module
public import SerrePositivity.KST.SConstruction.SimplexHAOrderAppendLast

/-! # 元の右側頂点列を加えた有界昇順列
概要：元の頂点列に、それより右の有限昇順列を全頂点を保って追加する。
方針：右側列の最後を上界とする前段を再帰し、その最後の頂点を一点追加する。
規約：元の順序埋め込みを保持。使われ方：右側全辺添字を元の頂点集合へ読み替える。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の列と右側有限列を連結し、指定上界より左の最後の頂点を保つ元の昇順列。 -/
def simplexHATailPrefix {n : ℕ} (m : ℕ) (v : Fin (m + 1) ↪o Fin (n + 1)) :
    (t : ℕ) → (w : Fin t ↪o Fin (n + 1)) → (∀ j, v (Fin.last m) < w j) →
    (b : Fin (n + 1)) → v (Fin.last m) < b → (∀ j, w j < b) →
      {u : Fin (m + t + 1) ↪o Fin (n + 1) // u (Fin.last (m + t)) < b}
  | 0, _, _, _, hv, _ => ⟨v, hv⟩
  | t + 1, w, hsep, _, _, hw =>
    let r := w (Fin.last t)
    let u := simplexHATailPrefix m v t (Fin.castSuccOrderEmb.trans w)
      (fun j => hsep j.castSucc) r (hsep (Fin.last t))
      (fun j => w.strictMono (Fin.castSucc_lt_last j))
    ⟨simplexHAOrderAppendLast (m + t) u.val r u.property, by
      exact lt_of_eq_of_lt (simplexHAOrderAppendLast_last (m + t) u.val r u.property)
        (hw (Fin.last t))⟩

/-- 元の右側列が空なら、元の同じ頂点列を回収する。 -/
lemma simplexHATailPrefix_zero {n : ℕ} (m : ℕ) (v : Fin (m + 1) ↪o Fin (n + 1))
    (w : Fin 0 ↪o Fin (n + 1)) (hs : ∀ j, v (Fin.last m) < w j)
    (b : Fin (n + 1)) (hv : v (Fin.last m) < b) (hw : ∀ j, w j < b) :
    (simplexHATailPrefix m v 0 w hs b hv hw).val = v := rfl

/-- 元の連結列の頂点は、外側の上界の選択によらない。 -/
lemma simplexHATailPrefix_bound_irrel {n : ℕ} (m : ℕ) (v : Fin (m + 1) ↪o Fin (n + 1))
    (t : ℕ) (w : Fin t ↪o Fin (n + 1)) (hs : ∀ j, v (Fin.last m) < w j)
    (b b' : Fin (n + 1)) (hv : v (Fin.last m) < b) (hw : ∀ j, w j < b)
    (hv' : v (Fin.last m) < b') (hw' : ∀ j, w j < b') :
    (simplexHATailPrefix m v t w hs b hv hw).val =
      (simplexHATailPrefix m v t w hs b' hv' hw').val := by
  cases t <;> rfl

/-- 元の右側列を連結しても、元の始頂点を保持する。 -/
lemma simplexHATailPrefix_first {n : ℕ} (m : ℕ) (v : Fin (m + 1) ↪o Fin (n + 1))
    (t : ℕ) (w : Fin t ↪o Fin (n + 1)) (hs : ∀ j, v (Fin.last m) < w j)
    (b : Fin (n + 1)) (hv : v (Fin.last m) < b) (hw : ∀ j, w j < b) :
    (simplexHATailPrefix m v t w hs b hv hw).val 0 = v 0 := by
  induction t generalizing b with
  | zero => rfl
  | succ t ih =>
    let u := simplexHATailPrefix m v t (Fin.castSuccOrderEmb.trans w)
      (fun j => hs j.castSucc) (w (Fin.last t)) (hs (Fin.last t))
      (fun j => w.strictMono (Fin.castSucc_lt_last j))
    exact (simplexHAOrderAppendLast_first (m + t) u.val (w (Fin.last t)) u.property).trans
      (ih (Fin.castSuccOrderEmb.trans w) (fun j => hs j.castSucc) _ (hs (Fin.last t))
        (fun j => w.strictMono (Fin.castSucc_lt_last j)))

/-- 元の連結列の全頂点の像は、元の両列の像の和そのもの。 -/
lemma simplexHATailPrefix_range {n : ℕ} (m : ℕ) (v : Fin (m + 1) ↪o Fin (n + 1))
    (t : ℕ) (w : Fin t ↪o Fin (n + 1)) (hs : ∀ j, v (Fin.last m) < w j)
    (b : Fin (n + 1)) (hv : v (Fin.last m) < b) (hw : ∀ j, w j < b) :
    Finset.univ.map (simplexHATailPrefix m v t w hs b hv hw).val.toEmbedding =
      Finset.univ.map v.toEmbedding ∪ Finset.univ.map w.toEmbedding := by
  induction t generalizing b with
  | zero => simp only [simplexHATailPrefix, Finset.univ_eq_empty, Finset.map_empty,
      Finset.union_empty]
  | succ t ih =>
    let u := simplexHATailPrefix m v t (Fin.castSuccOrderEmb.trans w)
      (fun j => hs j.castSucc) (w (Fin.last t)) (hs (Fin.last t))
      (fun j => w.strictMono (Fin.castSucc_lt_last j))
    change Finset.univ.map
      (simplexHAOrderAppendLast (m + t) u.val (w (Fin.last t)) u.property).toEmbedding = _
    rw [simplexHAOrderAppendLast_range]
    rw [show Finset.univ.map u.val.toEmbedding = _ from
      ih (Fin.castSuccOrderEmb.trans w) (fun j => hs j.castSucc) _ (hs (Fin.last t))
        (fun j => w.strictMono (Fin.castSucc_lt_last j)), simplexHAOrderRange_succ w]
    simp only [Finset.union_insert]

end SerrePositivity.KST.SConstruction
