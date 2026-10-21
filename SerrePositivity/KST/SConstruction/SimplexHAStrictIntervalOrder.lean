module
public import SerrePositivity.KST.SConstruction.SimplexHADecodeSubset

/-! # 元の厳密区間の HA 復元用の頂点列
概要：a<b の元の区間の終点を除く全頂点を、元の同じ標準単体内で昇順に列挙する。
方針：元の始点番号へ局所番号を加え、像を元の半開区間と照合する。
規約：元の両端点と全内部頂点を保持。使われ方：Λ の全昇順 Hom の逆鎖射。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の厳密区間 [a,b) の全頂点を、元の頂点番号のまま列挙する。 -/
def simplexHAStrictIntervalOrder {N : ℕ} (a b : Fin (N + 1)) (hab : a < b) :
    Fin (b.val - a.val - 1 + 1) ↪o Fin (N + 1) :=
  OrderEmbedding.ofStrictMono (fun j => ⟨a.val + j.val, by
    have ha : a.val < b.val := hab
    have hj := j.isLt
    have hN := b.isLt
    omega⟩) (fun i j h => by
      change a.val + i.val < a.val + j.val
      exact Nat.add_lt_add_left h _)

/-- 元の厳密区間の列の始点は、元の同じ a。 -/
lemma simplexHAStrictIntervalOrder_first {N : ℕ} (a b : Fin (N + 1)) (hab : a < b) :
    simplexHAStrictIntervalOrder a b hab 0 = a := rfl

/-- 元の厳密区間の列の最後は、元の同じ終点 b より厳密に左。 -/
lemma simplexHAStrictIntervalOrder_last_lt {N : ℕ} (a b : Fin (N + 1)) (hab : a < b) :
    simplexHAStrictIntervalOrder a b hab (Fin.last (b.val - a.val - 1)) < b := by
  change a.val + (b.val - a.val - 1) < b.val
  have ha : a.val < b.val := hab
  omega

/-- 元の厳密区間の頂点列の像は、元の同じ半開区間そのもの。 -/
lemma simplexHAStrictIntervalOrder_range {N : ℕ} (a b : Fin (N + 1)) (hab : a < b) :
    Finset.univ.map (simplexHAStrictIntervalOrder a b hab).toEmbedding = Finset.Ico a b := by
  ext x
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_Ico,
    RelEmbedding.coe_toEmbedding]
  constructor
  · rintro ⟨j, rfl⟩
    constructor
    · change a.val ≤ a.val + j.val
      omega
    · change a.val + j.val < b.val
      have hj := j.isLt
      have ha : a.val < b.val := hab
      omega
  · rintro ⟨hax, hxb⟩
    have ha : a.val < b.val := hab
    have hax' : a.val ≤ x.val := hax
    have hxb' : x.val < b.val := hxb
    refine ⟨⟨x.val - a.val, by omega⟩, ?_⟩
    apply Fin.ext
    change a.val + (x.val - a.val) = x.val
    omega

/-- 元の厳密区間列に同じ終点を加えた読み替え部分集合は、元の閉区間そのもの。 -/
lemma simplexHAStrictIntervalOrder_subset {N : ℕ} (a b : Fin (N + 1)) (hab : a < b) :
    simplexHADecodeSubset (b.val - a.val - 1) (simplexHAStrictIntervalOrder a b hab) {b} =
      Finset.Icc a b := by
  rw [simplexHADecodeSubset, simplexHAStrictIntervalOrder_range]
  ext x
  simp only [Finset.mem_union, Finset.mem_Ico, Finset.mem_singleton, Finset.mem_Icc]
  constructor
  · rintro (⟨hax, hxb⟩ | rfl)
    · exact ⟨hax, hxb.le⟩
    · exact ⟨hab.le, le_rfl⟩
  · rintro ⟨hax, hxb⟩
    by_cases h : x = b
    · exact Or.inr h
    · exact Or.inl ⟨hax, lt_of_le_of_ne hxb h⟩

end SerrePositivity.KST.SConstruction
