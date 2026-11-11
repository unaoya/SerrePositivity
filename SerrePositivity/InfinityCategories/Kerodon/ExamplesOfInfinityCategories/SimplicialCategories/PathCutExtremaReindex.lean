module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathCutExtremaComposition

/-!
概要：左右の切断座標は、面・退化を含む任意の単調な添字変換と可換。
方針：path の頂点集合の像を取り、最小・最大元の像をそれぞれ比較する。
規約：添字写像の単射性や全射性を要求しない。
使われ方：混合 prism の全単体での自然性。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SimplicialThickening SSet
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 単調な添字写像で path の頂点集合を写す。 -/
def pathCutImage {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) {i j : Fin (m + 1)}
    (P : Path (ULift.up i : ULift.{u} (Fin (m + 1))) (ULift.up j)) :
    Path (ULift.up (α i) : ULift.{u} (Fin (n + 1))) (ULift.up (α j)) where
  I := (fun k : ULift.{u} (Fin (m + 1)) => ULift.up (α k.down)) '' P.I
  left := ⟨ULift.up i, P.left, rfl⟩
  right := ⟨ULift.up j, P.right, rfl⟩
  left_le k hk := by
    obtain ⟨l, hl, rfl⟩ := hk
    exact α.monotone (P.left_le l hl)
  le_right k hk := by
    obtain ⟨l, hl, rfl⟩ := hk
    exact α.monotone (P.le_right l hl)

/-- 最後の零頂点は、任意の添字写像による path の像と可換。 -/
lemma pathCutLastZero_image {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (t : Fin (n + 1) →o Fin 2) {i j : Fin (m + 1)} (hi : t (α i) = 0)
    (P : Path (ULift.up i : ULift.{u} (Fin (m + 1))) (ULift.up j)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero t hi (pathCutImage α P) = α (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero (t.comp α) hi P) := by
  apply le_antisymm
  · obtain ⟨⟨k⟩, hk, he⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero_spec t hi (pathCutImage α P)).2
    have he' : α k = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero t hi (pathCutImage α P) := congrArg ULift.down he
    have ht : (t.comp α) k = 0 := by
      change t (α k) = 0
      rw [he']
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero_spec t hi (pathCutImage α P)).1
    rw [← he']
    exact α.monotone (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.le_pathCutLastZero (t.comp α) hi P k ht hk)
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.le_pathCutLastZero t hi (pathCutImage α P)
    · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero_spec (t.comp α) hi P).1
    · exact ⟨ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero (t.comp α) hi P),
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero_spec (t.comp α) hi P).2, rfl⟩

/-- 最初の一頂点も、任意の添字写像による path の像と可換。 -/
lemma pathCutFirstOne_image {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (t : Fin (n + 1) →o Fin 2) {i j : Fin (m + 1)} (hj : t (α j) = 1)
    (P : Path (ULift.up i : ULift.{u} (Fin (m + 1))) (ULift.up j)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne t hj (pathCutImage α P) = α (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne (t.comp α) hj P) := by
  apply le_antisymm
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne_le t hj (pathCutImage α P)
    · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne_spec (t.comp α) hj P).1
    · exact ⟨ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne (t.comp α) hj P),
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne_spec (t.comp α) hj P).2, rfl⟩
  · obtain ⟨⟨k⟩, hk, he⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne_spec t hj (pathCutImage α P)).2
    have he' : α k = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne t hj (pathCutImage α P) := congrArg ULift.down he
    have ht : (t.comp α) k = 1 := by
      change t (α k) = 1
      rw [he']
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne_spec t hj (pathCutImage α P)).1
    rw [← he']
    exact α.monotone (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne_le (t.comp α) hj P k ht hk)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
