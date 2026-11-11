module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialSpine

/-!
概要：可算 spine の外の有限頂点集合を、最小頂点の次の番号の挿入・削除で対にする。
方針：最小頂点と少なくとも二つ大きい頂点を保つため、挿入点は常に内部にある。
規約：単体的 pairing とその整礎性は後続で接続する。
使われ方：P-11 の可算 spine の inner anodyne 性の組合せ論。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：spine の外の頂点集合には番号差が二以上の二頂点がある。
方針：全称的な spine 条件を否定して証人を取り出す。
規約：空集合は spine 内である。
使われ方：挿入点の両側の頂点を確保する。 -/
lemma not_sequentialSpineSupport_iff (S : Finset ℕ) :
    ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialSpineSupport S ↔ ∃ a ∈ S, ∃ b ∈ S, a + 1 < b := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialSpineSupport, not_forall, not_le, exists_prop]

/-- 概要：spine の外の有限頂点集合は非空。
方針：番号差を持つ二頂点の最初のものを取る。
規約：元の有限集合の所属証人を返す。
使われ方：最小頂点の選択。 -/
lemma sequentialSpineOutside_nonempty {S : Finset ℕ} (hS : ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialSpineSupport S) :
    S.Nonempty := by
  obtain ⟨a, ha, _, _, _⟩ := (not_sequentialSpineSupport_iff S).mp hS
  exact ⟨a, ha⟩

/-- 概要：有限頂点集合の最小番号の直後を挿入点として選ぶ。
方針：非空なら最小値に一を足し、空集合には既定値を置く。
規約：実際の pairing では spine 外の非空な集合だけを使う。
使われ方：隣接辺以外の単体の対を定める。 -/
def sequentialSpinePivot (S : Finset ℕ) : ℕ :=
  if hS : S.Nonempty then S.min' hS + 1 else 0

/-- 概要：非空な集合の挿入点はその最小番号の直後。
方針：定義の非空分岐を展開する。
規約：非空性の証明の選び方に依存しない。
使われ方：挿入・削除に関する最小値の比較。 -/
lemma sequentialSpinePivot_eq {S : Finset ℕ} (hS : S.Nonempty) :
    sequentialSpinePivot S = S.min' hS + 1 := by
  simp only [sequentialSpinePivot, dite_eq_left hS]

/-- 概要：挿入点の挿入では、元の最小頂点は変わらない。
方針：最小頂点は既に存在し、新しい頂点はそれより大きい。
規約：挿入点が既にある場合も含む。
使われ方：pairing の逆操作が同じ挿入点を使うことの確認。 -/
lemma sequentialSpinePivot_insert {S : Finset ℕ} (hS : S.Nonempty) :
    sequentialSpinePivot (insert (sequentialSpinePivot S) S) = sequentialSpinePivot S := by
  rw [sequentialSpinePivot_eq (Finset.insert_nonempty _ _), sequentialSpinePivot_eq hS,
    Finset.min'_insert _ S hS]
  omega

/-- 概要：挿入点の削除後も元の最小頂点が残る。
方針：挿入点は最小頂点より一つ大きい。
規約：spine の外という仮定は不要。
使われ方：削除後の非空性と最小値の保持。 -/
lemma sequentialSpinePivot_erase_nonempty {S : Finset ℕ} (hS : S.Nonempty) :
    (S.erase (sequentialSpinePivot S)).Nonempty := by
  refine ⟨S.min' hS, Finset.mem_erase.mpr ⟨?_, Finset.min'_mem S hS⟩⟩
  rw [sequentialSpinePivot_eq hS]
  omega

/-- 概要：挿入点を削除しても、次に選ぶ挿入点は同じ。
方針：削除後に残る元の最小値の最小性を確認する。
規約：挿入点が元の集合に無くてもよい。
使われ方：挿入・削除の全単射の整合性。 -/
lemma sequentialSpinePivot_erase {S : Finset ℕ} (hS : S.Nonempty) :
    sequentialSpinePivot (S.erase (sequentialSpinePivot S)) = sequentialSpinePivot S := by
  rw [sequentialSpinePivot_eq (sequentialSpinePivot_erase_nonempty hS)]
  conv_rhs => rw [sequentialSpinePivot_eq hS]
  congr 1
  apply (Finset.min'_eq_iff _ _ _).mpr
  refine ⟨Finset.mem_erase.mpr ⟨?_, Finset.min'_mem S hS⟩, ?_⟩
  · rw [sequentialSpinePivot_eq hS]
    omega
  · intro b hb
    exact Finset.min'_le S b (Finset.mem_of_mem_erase hb)

/-- 概要：spine の外の集合への頂点の挿入は、依然 spine の外。
方針：元の番号差を持つ二頂点を保つ。
規約：任意の番号の挿入に使える。
使われ方：pairing の大きい方の単体の領域外性。 -/
lemma sequentialSpineOutside_insert {S : Finset ℕ} (hS : ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialSpineSupport S) (p : ℕ) :
    ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialSpineSupport (insert p S) := by
  obtain ⟨a, ha, b, hb, hab⟩ := (not_sequentialSpineSupport_iff S).mp hS
  exact (not_sequentialSpineSupport_iff _).mpr
    ⟨a, Finset.mem_insert_of_mem ha, b, Finset.mem_insert_of_mem hb, hab⟩

/-- 概要：spine の外の集合から挿入点を削除しても、依然 spine の外。
方針：元の最小頂点とそれより二以上大きい頂点を残す。
規約：削除する点は最小値の直後に固定する。
使われ方：pairing の小さい方の単体の領域外性。 -/
lemma sequentialSpineOutside_erase {S : Finset ℕ} (hS : ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialSpineSupport S) :
    ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialSpineSupport (S.erase (sequentialSpinePivot S)) := by
  let hs := sequentialSpineOutside_nonempty hS
  obtain ⟨a, ha, b, hb, hab⟩ := (not_sequentialSpineSupport_iff S).mp hS
  have hma := Finset.min'_le S a ha
  apply (not_sequentialSpineSupport_iff _).mpr
  refine ⟨S.min' hs, Finset.mem_erase.mpr ⟨?_, Finset.min'_mem S hs⟩,
    b, Finset.mem_erase.mpr ⟨?_, hb⟩, ?_⟩
  · rw [sequentialSpinePivot_eq hs]
    omega
  · rw [sequentialSpinePivot_eq hs]
    omega
  · omega

/-- 概要：spine の外の集合の、挿入点を欠くものと含むものの全単射。
方針：同じ最小頂点の直後を挿入・削除し、領域外性と挿入点の不変性を使う。
規約：実際の有限頂点集合を保持する。
使われ方：可算 spine の非退化単体の pairing。 -/
def sequentialSpineSupportPairEquiv :
    {S : Finset ℕ // ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialSpineSupport S ∧ sequentialSpinePivot S ∉ S} ≃
      {S : Finset ℕ // ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialSpineSupport S ∧ sequentialSpinePivot S ∈ S} where
  toFun S := ⟨insert (sequentialSpinePivot S.val) S.val,
    sequentialSpineOutside_insert S.property.1 _, by
      rw [sequentialSpinePivot_insert (sequentialSpineOutside_nonempty S.property.1)]
      exact Finset.mem_insert_self _ _⟩
  invFun S := ⟨S.val.erase (sequentialSpinePivot S.val),
    sequentialSpineOutside_erase S.property.1, by
      rw [sequentialSpinePivot_erase (sequentialSpineOutside_nonempty S.property.1)]
      exact Finset.notMem_erase _ _⟩
  left_inv S := by
    apply Subtype.ext
    change (insert (sequentialSpinePivot S.val) S.val).erase
      (sequentialSpinePivot (insert (sequentialSpinePivot S.val) S.val)) = S.val
    rw [sequentialSpinePivot_insert (sequentialSpineOutside_nonempty S.property.1),
      Finset.erase_insert S.property.2]
  right_inv S := by
    apply Subtype.ext
    change insert (sequentialSpinePivot (S.val.erase (sequentialSpinePivot S.val)))
      (S.val.erase (sequentialSpinePivot S.val)) = S.val
    rw [sequentialSpinePivot_erase (sequentialSpineOutside_nonempty S.property.1),
      Finset.insert_erase S.property.2]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
