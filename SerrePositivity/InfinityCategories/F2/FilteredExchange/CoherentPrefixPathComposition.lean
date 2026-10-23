module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentPrefixPathDeformation

/-!
概要：prefix 変形は和集合による path の合成を保持する。
方針：追加区間を接合点の前後で分け、時刻の単調性で接合点を時刻零に保つ。
規約：二つの元の path と同じ接合点を保持する。
使われ方：固定始点の比較を実際の豊穣関手へ組み立てる。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SimplicialThickening SSet
namespace SerrePositivity.InfinityCategories.F2

/-- prefix 変形は path の合成と厳密に可換。 -/
lemma coherentPrefixPathDeformation_comp {J K : Type u} [LinearOrder J] [LinearOrder K]
    (A : J →o K) (t : J →o Fin 2) {i j k : J} (P : Path i j) (Q : Path j k) :
    coherentPrefixPathDeformation A t
      (show (⟨i⟩ : SimplicialThickening J) ⟶ ⟨k⟩ from P ≫ Q) =
    (show (⟨A i⟩ : SimplicialThickening K) ⟶ ⟨A k⟩ from
      coherentPrefixPathDeformation A t P ≫ coherentPrefixPathDeformation A t Q) := by
  apply SimplicialThickening.Path.ext
  ext z
  change (z ∈ A '' (P.I ∪ Q.I) ∨
    ∃ l ∈ P.I ∪ Q.I, t l = 0 ∧ A i ≤ z ∧ z ≤ A l) ↔
    (z ∈ (coherentPrefixPathDeformation A t P).I ∨
      z ∈ (coherentPrefixPathDeformation A t Q).I)
  constructor
  · rintro (⟨l, hl | hl, rfl⟩ | ⟨l, hl | hl, ht, hiz, hzl⟩)
    · exact Or.inl (Or.inl ⟨l, hl, rfl⟩)
    · exact Or.inr (Or.inl ⟨l, hl, rfl⟩)
    · exact Or.inl (Or.inr ⟨l, hl, ht, hiz, hzl⟩)
    · by_cases hzj : z ≤ A j
      · have htj : t j = 0 := by
          apply Fin.ext
          have h := t.monotone (Q.left_le l hl)
          rw [ht] at h
          change (t j).val ≤ (0 : Fin 2).val at h
          omega
        exact Or.inl (Or.inr ⟨j, P.right, htj, hiz, hzj⟩)
      · exact Or.inr (Or.inr ⟨l, hl, ht, le_of_not_ge hzj, hzl⟩)
  · rintro ((⟨l, hl, rfl⟩ | ⟨l, hl, ht, hiz, hzl⟩) |
      (⟨l, hl, rfl⟩ | ⟨l, hl, ht, hjz, hzl⟩))
    · exact Or.inl ⟨l, Or.inl hl, rfl⟩
    · exact Or.inr ⟨l, Or.inl hl, ht, hiz, hzl⟩
    · exact Or.inl ⟨l, Or.inr hl, rfl⟩
    · exact Or.inr ⟨l, Or.inr hl, ht, (A.monotone P.le).trans hjz, hzl⟩

end SerrePositivity.InfinityCategories.F2
