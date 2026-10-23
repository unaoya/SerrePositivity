module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentPrefixPathDeformation

/-!
概要：prefix 変形の添字変換と両端の座標。
方針：像の証人を対応させ、時刻零で終点を区間の証人として使う。
規約：元の path と固定した両端を保持する。
使われ方：固定始点の coslice の実比較とその端点。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SimplicialThickening SSet
namespace SerrePositivity.InfinityCategories.F2

/-- prefix 変形は始域の単調写像による添字変換と可換。 -/
lemma coherentPrefixPathDeformation_reindex {I J K : Type u}
    [LinearOrder I] [LinearOrder J] [LinearOrder K]
    (g : I →o J) (A : J →o K) (t : J →o Fin 2) {i j : I} (P : Path i j) :
    coherentPrefixPathDeformation (A.comp g) (t.comp g) P =
      coherentPrefixPathDeformation A t
        ((SimplicialThickening.functorMap g ⟨i⟩ ⟨j⟩).obj P) := by
  apply SimplicialThickening.Path.ext
  ext z
  change (z ∈ (A.comp g) '' P.I ∨
    ∃ k ∈ P.I, t (g k) = 0 ∧ A (g i) ≤ z ∧ z ≤ A (g k)) ↔
    (z ∈ A '' (g '' P.I) ∨
      ∃ k ∈ g '' P.I, t k = 0 ∧ A (g i) ≤ z ∧ z ≤ A k)
  constructor
  · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, ht, hiz, hzk⟩)
    · exact Or.inl ⟨g k, ⟨k, hk, rfl⟩, rfl⟩
    · exact Or.inr ⟨g k, ⟨k, hk, rfl⟩, ht, hiz, hzk⟩
  · rintro (⟨_, ⟨k, hk, rfl⟩, rfl⟩ | ⟨_, ⟨k, hk, rfl⟩, ht, hiz, hzk⟩)
    · exact Or.inl ⟨k, hk, rfl⟩
    · exact Or.inr ⟨k, hk, ht, hiz, hzk⟩

/-- 時刻一では追加区間がなく元の path の像を回収する。 -/
lemma coherentPrefixPathDeformation_one {J K : Type u} [LinearOrder J] [LinearOrder K]
    (A : J →o K) {i j : J} (P : Path i j) :
    coherentPrefixPathDeformation A (OrderHom.const J 1) P =
      (SimplicialThickening.functorMap A ⟨i⟩ ⟨j⟩).obj P := by
  apply SimplicialThickening.Path.ext
  ext z
  simp [coherentPrefixPathDeformation]

/-- 時刻零では同じ二端点の全区間を回収する。 -/
lemma coherentPrefixPathDeformation_zero {J K : Type u} [LinearOrder J] [LinearOrder K]
    (A : J →o K) {i j : J} (P : Path i j) :
    (coherentPrefixPathDeformation A (OrderHom.const J 0) P).I =
      Set.Icc (A i) (A j) := by
  ext z
  constructor
  · intro hz
    exact ⟨Path.left_le _ z hz, Path.le_right _ z hz⟩
  · rintro ⟨hiz, hzj⟩
    exact Or.inr ⟨j, P.right, rfl, hiz, hzj⟩

/-- 対象写像が定値なら任意の時刻でも恒等 path を回収する。 -/
lemma coherentPrefixPathDeformation_constant {J K : Type u} [LinearOrder J] [LinearOrder K]
    (a : K) (t : J →o Fin 2) {i j : J} (P : Path i j) :
    coherentPrefixPathDeformation (OrderHom.const J a) t P =
      𝟙 (⟨a⟩ : SimplicialThickening K) := by
  apply SimplicialThickening.Path.ext
  ext z
  change z ∈ (coherentPrefixPathDeformation (OrderHom.const J a) t P).I ↔ z = a
  constructor
  · intro hz
    exact le_antisymm (Path.le_right _ z hz) (Path.left_le _ z hz)
  · rintro rfl
    exact Path.left _

end SerrePositivity.InfinityCategories.F2
