module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathDeformation

/-!
概要：始点を固定する coslice の比較に使う、prefix を埋める path 変形。
方針：時刻零の頂点までの区間を元の path の像に加える。
規約：対象写像と時刻写像は単調、path の精密化の向きを保持する。
使われ方：最大化した全族から元の零面の全族への実比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SimplicialThickening SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 時刻零の頂点までの prefix 区間を埋めた path。 -/
def coherentPrefixPathDeformation {J K : Type u} [LinearOrder J] [LinearOrder K]
    (A : J →o K) (t : J →o Fin 2) {i j : J} (P : Path i j) : Path (A i) (A j) where
  I := A '' P.I ∪ {z | ∃ k ∈ P.I, t k = 0 ∧ A i ≤ z ∧ z ≤ A k}
  left := Or.inl ⟨i, P.left, rfl⟩
  right := Or.inl ⟨j, P.right, rfl⟩
  left_le z hz := by
    rcases hz with ⟨k, hk, rfl⟩ | ⟨_, _, _, hiz, _⟩
    · exact A.monotone (P.left_le k hk)
    · exact hiz
  le_right z hz := by
    rcases hz with ⟨k, hk, rfl⟩ | ⟨k, hk, _, _, hzk⟩
    · exact A.monotone (P.le_right k hk)
    · exact hzk.trans (A.monotone (P.le_right k hk))

/-- prefix 変形は元の精密化の包含を保持する。 -/
lemma coherentPrefixPathDeformation_mono {J K : Type u} [LinearOrder J] [LinearOrder K]
    (A : J →o K) (t : J →o Fin 2) {i j : J} {P Q : Path i j} (h : P.I ⊆ Q.I) :
    (coherentPrefixPathDeformation A t P).I ⊆ (coherentPrefixPathDeformation A t Q).I := by
  rintro z (⟨k, hk, rfl⟩ | ⟨k, hk, ht, hiz, hzk⟩)
  · exact Or.inl ⟨k, h hk, rfl⟩
  · exact Or.inr ⟨k, h hk, ht, hiz, hzk⟩

/-- prefix 変形は恒等 path を保持する。 -/
lemma coherentPrefixPathDeformation_id {J K : Type u} [LinearOrder J] [LinearOrder K]
    (A : J →o K) (t : J →o Fin 2) (i : J) :
    coherentPrefixPathDeformation A t (𝟙 (⟨i⟩ : SimplicialThickening J)) =
      𝟙 (⟨A i⟩ : SimplicialThickening K) := by
  apply SimplicialThickening.Path.ext
  ext z
  change z ∈ (coherentPrefixPathDeformation A t (𝟙 (⟨i⟩ : SimplicialThickening J))).I ↔
    z = A i
  constructor
  · intro hz
    exact le_antisymm (Path.le_right _ z hz) (Path.left_le _ z hz)
  · rintro rfl
    exact Path.left _

end SerrePositivity.InfinityCategories.F2
