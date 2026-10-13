module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # 中間体の有向合併への段写像

指定体への代数写像の値が中間体Lに入ることを確認して、終域をLへ制限する。
各段の像が有向な中間体F_i全体なら、制限した段写像はその合併L全体を覆う。
局所性・Noether性・平坦性を使わない、体側の共通API。
-/

@[expose] public section
namespace SerrePositivity
variable {B k K : Type*} [CommRing B] [Field k] [Field K]
variable [Algebra B k] [Algebra k K] [Algebra B K] [IsScalarTower B k K]
variable {S : Type*} [CommRing S] [Algebra B S]

/-- 指定体への写像を、値の入る中間体へ制限する。係数構造はMathlibから継承する。 -/
def algHomToIntermediateField (L : IntermediateField k K) (g : S →ₐ[B] K)
    (h : ∀ x, g x ∈ L) : S →ₐ[B] L :=
  g.codRestrict (L.toSubalgebra.restrictScalars B) h

@[simp] theorem algHomToIntermediateField_coe (L : IntermediateField k K) (g : S →ₐ[B] K)
    (h : ∀ x, g x ∈ L) (x : S) : (algHomToIntermediateField L g h x : K) = g x := rfl

section System
variable {ι : Type*} (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra B (S i)]
variable (L : IntermediateField k K) (g : ∀ i, S i →ₐ[B] K)
variable (hmem : ∀ i x, g i x ∈ L)

/-- 指定体への両立する写像は、共通の中間体へ制限しても両立する。 -/
theorem algHomToIntermediateField_compatible [Preorder ι]
    (f : ∀ i j, i ≤ j → S i →ₐ[B] S j)
    (hg : ∀ i j h x, g j (f i j h x) = g i x) :
    ∀ i j h x, algHomToIntermediateField L (g j) (hmem j) (f i j h x) =
      algHomToIntermediateField L (g i) (hmem i) x := by
  intro i j h x
  apply Subtype.ext
  exact hg i j h x

/-- 各段の像が有向な中間体全体なら、制限した写像の像は合併全体を覆う。 -/
theorem algHomToIntermediateField_cover_of_iSup [Nonempty ι]
    (F : ι → IntermediateField k K) (hF : Directed (· ≤ ·) F) (hL : L = ⨆ i, F i)
    (hrange : ∀ i, Set.range (g i) = (F i : Set K)) :
    ∀ x : L, ∃ i, ∃ y : S i, algHomToIntermediateField L (g i) (hmem i) y = x := by
  intro x
  have hx : x.val ∈ (⨆ i, F i : IntermediateField k K) := hL ▸ x.property
  rw [← SetLike.mem_coe, IntermediateField.coe_iSup_of_directed hF] at hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  rw [← hrange i] at hi
  obtain ⟨y, hy⟩ := hi
  exact ⟨i, y, Subtype.ext hy⟩

end System
end SerrePositivity
