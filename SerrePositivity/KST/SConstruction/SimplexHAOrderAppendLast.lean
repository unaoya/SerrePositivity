module
public import SerrePositivity.KST.SConstruction.SimplexHADecodeBounds

/-! # 元の HA 頂点列の右端への一点追加
概要：元の昇順頂点列より右の頂点を、同じ全頂点を保った昇順列の最後へ加える。
方針：元の Fin.lastCases と狭義単調性で順序埋め込みを作る。
規約：元の頂点順を保持。使われ方：右側集合の昇順列挙と右側全辺添字の比較。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の頂点列の右端に、それより右の一点を加えた同じ昇順列。 -/
def simplexHAOrderAppendLast {n : ℕ} (m : ℕ) (v : Fin (m + 1) ↪o Fin (n + 1))
    (r : Fin (n + 1)) (hr : v (Fin.last m) < r) : Fin (m + 2) ↪o Fin (n + 1) :=
  OrderEmbedding.ofStrictMono (fun i => Fin.lastCases r v i) (by
    intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i
    · intro hij
      exact False.elim ((not_lt_of_ge (Fin.le_last j)) hij)
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · intro _
        simpa only [Fin.lastCases_castSucc, Fin.lastCases_last] using
          (v.monotone (Fin.le_last i)).trans_lt hr
      · intro hij
        simpa only [Fin.lastCases_castSucc] using v.strictMono
          (Fin.castSucc_lt_castSucc_iff.mp hij))

/-- 元の追加列の前段頂点は、同じ元の頂点そのもの。 -/
lemma simplexHAOrderAppendLast_castSucc {n : ℕ} (m : ℕ)
    (v : Fin (m + 1) ↪o Fin (n + 1)) (r : Fin (n + 1)) (hr : v (Fin.last m) < r)
    (i : Fin (m + 1)) : simplexHAOrderAppendLast m v r hr i.castSucc = v i := by
  change Fin.lastCases r (fun j => v j) i.castSucc = v i
  exact Fin.lastCases_castSucc i

/-- 元の追加列の最後は、元の追加した頂点。 -/
lemma simplexHAOrderAppendLast_last {n : ℕ} (m : ℕ)
    (v : Fin (m + 1) ↪o Fin (n + 1)) (r : Fin (n + 1)) (hr : v (Fin.last m) < r) :
    simplexHAOrderAppendLast m v r hr (Fin.last (m + 1)) = r := by
  change Fin.lastCases r (fun j => v j) (Fin.last (m + 1)) = r
  exact Fin.lastCases_last

/-- 元の追加列の左部分は、元の前段の列と順序埋め込みとして厳密に一致する。 -/
lemma simplexHAOrderAppendLast_prefix {n : ℕ} (m : ℕ)
    (v : Fin (m + 1) ↪o Fin (n + 1)) (r : Fin (n + 1)) (hr : v (Fin.last m) < r) :
    Fin.castSuccOrderEmb.trans (simplexHAOrderAppendLast m v r hr) = v := by
  ext i
  exact congrArg Fin.val (simplexHAOrderAppendLast_castSucc m v r hr i)

/-- 元の追加列の最初は、元の前段の列の最初。 -/
lemma simplexHAOrderAppendLast_first {n : ℕ} (m : ℕ)
    (v : Fin (m + 1) ↪o Fin (n + 1)) (r : Fin (n + 1)) (hr : v (Fin.last m) < r) :
    simplexHAOrderAppendLast m v r hr 0 = v 0 :=
  simplexHAOrderAppendLast_castSucc m v r hr 0

/-- 元の有限昇順列の像は、最後の頂点と元の左部分の像の和。 -/
lemma simplexHAOrderRange_succ {n t : ℕ} (w : Fin (t + 1) ↪o Fin (n + 1)) :
    Finset.univ.map w.toEmbedding = insert (w (Fin.last t))
      (Finset.univ.map (Fin.castSuccOrderEmb.trans w).toEmbedding) := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_map, Finset.mem_univ, true_and,
    RelEmbedding.coe_toEmbedding]
  change (∃ j, w j = x) ↔ x = w (Fin.last t) ∨ ∃ j : Fin t, w j.castSucc = x
  constructor
  · rintro ⟨j, rfl⟩
    refine Fin.lastCases ?_ (fun j => ?_) j
    · exact Or.inl rfl
    · exact Or.inr ⟨j, rfl⟩
  · rintro (rfl | ⟨j, hj⟩)
    · exact ⟨Fin.last t, rfl⟩
    · exact ⟨j.castSucc, hj⟩

/-- 元の一点追加列の像は、元の前段の像に同じ最後の頂点を加えた集合。 -/
lemma simplexHAOrderAppendLast_range {n : ℕ} (m : ℕ)
    (v : Fin (m + 1) ↪o Fin (n + 1)) (r : Fin (n + 1)) (hr : v (Fin.last m) < r) :
    Finset.univ.map (simplexHAOrderAppendLast m v r hr).toEmbedding =
      insert r (Finset.univ.map v.toEmbedding) := by
  rw [simplexHAOrderRange_succ, simplexHAOrderAppendLast_last, simplexHAOrderAppendLast_prefix]

end SerrePositivity.KST.SConstruction
