module
public import SerrePositivity.KST.SConstruction.SimplexHAFaceVertexCount
public import SerrePositivity.KST.SConstruction.SimplexSubsetInteriorCoordinates

/-! # 元の読み替え面座標と HA 内部頂点の同値
概要：右側一点の元の頂点集合の内部頂点を、元の全ての面座標で一意に表示する。
方針：面頂点番号の単射性と、元の列の像・右端一点の所属表示から全射性を示す。
規約：元の頂点をそのまま保持。使われ方：HA 右辺の内部頂点和を元の全面和へ移す。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction

/-- 元の全ての面座標と、同じ頂点集合の元の所属内部頂点の実際の同値。 -/
def simplexHAFaceInteriorEquiv {n : ℕ} (m : ℕ)
    (v : Fin (m + 2) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last (m + 1)) < b) : Fin (m + 1) ≃
      SimplexSubsetInterior (simplexHADecodeSubset (m + 1) v {b})
        (simplexHADecodeSubset_two (m + 1) v {b} (Finset.singleton_nonempty b)
          (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb)) := by
  let htail : ∀ t ∈ ({b} : Finset (Fin (n + 1))), v (Fin.last (m + 1)) < t :=
    fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb
  let f (i : Fin (m + 1)) :
      SimplexSubsetInterior (simplexHADecodeSubset (m + 1) v {b})
        (simplexHADecodeSubset_two (m + 1) v {b} (Finset.singleton_nonempty b) htail) :=
    ⟨v (simplexHAFaceVertex m i), simplexHAFaceVertex_mem m v {b} i, by
      rw [simplexHADecodeSubset_min (m + 1) v {b} htail]
      exact simplexHAFaceVertex_first_lt m v i, by
      rw [simplexHADecodeSubset_max (m + 1) v {b} (Finset.singleton_nonempty b) htail]
      exact simplexHAFaceVertex_tail_lt m v {b} i htail b (Finset.mem_singleton_self b)⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro i j hij
    exact simplexHAFaceVertex_injective m (v.injective (congrArg Subtype.val hij))
  · intro j
    have hj0 : v 0 < j.val :=
      (simplexHADecodeSubset_min (m + 1) v {b} htail).symm.trans_lt j.property.2.1
    have hjb : j.val < b := j.property.2.2.trans_eq
      (simplexHADecodeSubset_max (m + 1) v {b} (Finset.singleton_nonempty b) htail)
    rcases (simplexHADecodeSubset_mem (m + 1) v {b} j.val).mp j.property.1 with ⟨p, hp⟩ | hj
    · have hp0 : 0 < p.val := by
        by_contra h
        have he : p = 0 := Fin.ext (by change p.val = 0; omega)
        rw [he] at hp
        exact (ne_of_lt hj0) hp
      let i : Fin (m + 1) := ⟨m + 1 - p.val, by have h := p.isLt; omega⟩
      refine ⟨i, Subtype.ext ?_⟩
      have he : simplexHAFaceVertex m i = p := by
        apply Fin.ext
        change m + 1 - (m + 1 - p.val) = p.val
        have h := p.isLt
        omega
      exact (congrArg v he).trans hp
    · have he : j.val = b := Finset.mem_singleton.mp hj
      exact False.elim ((not_lt_of_ge he.ge) hjb)

/-- 元の面座標からの内部頂点は、元の昇順列の同じ番号の頂点そのもの。 -/
lemma simplexHAFaceInteriorEquiv_val {n : ℕ} (m : ℕ)
    (v : Fin (m + 2) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hb : v (Fin.last (m + 1)) < b) (i : Fin (m + 1)) :
    (simplexHAFaceInteriorEquiv m v b hb i).val = v (simplexHAFaceVertex m i) := rfl

end SerrePositivity.KST.SConstruction
