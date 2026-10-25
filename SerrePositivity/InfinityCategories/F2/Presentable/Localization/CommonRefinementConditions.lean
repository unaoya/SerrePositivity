module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.FilteredPieceSequenceUnion

/-!
概要：可算増大和で閉じた二つの上方共終な細分条件は、任意の開始部分集合の上で同時に満たせる。
方針：交互列の同じ和に両条件を移す。
規約：条件の上方閉性は仮定しない。使われ方：三角形の二辺の同時細分の添字側。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
local instance : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩
variable {μ : Cardinal.{u}} [Fact μ.IsRegular] {J : Type u} [PartialOrder J]

/-- 増大列の和を、元の同じ小さい filtered 部分集合族の要素として読む。 -/
def filteredPieceSequenceUnionPiece (hμ : Cardinal.aleph0 < μ)
    (A : ℕ → SmallFilteredPieces Cardinal.aleph0 μ J) (hA : Monotone A) :
    SmallFilteredPieces Cardinal.aleph0 μ J :=
  ⟨filteredPieceSequenceUnion A,
    (isCardinalFiltered_aleph0_iff _).mpr (filteredPieceSequenceUnion_isFiltered A hA),
    filteredPieceSequenceUnion_hasCardinalLT hμ A⟩

/-- 交互に含み合う二列は、同じ実部分集合の要素として同じ和を持つ。 -/
lemma filteredPieceSequenceUnionPiece_eq_of_interleaved (hμ : Cardinal.aleph0 < μ)
    (L R : ℕ → SmallFilteredPieces Cardinal.aleph0 μ J) (hL : Monotone L) (hR : Monotone R)
    (hLR : ∀ n, L n ≤ R n) (hRL : ∀ n, R n ≤ L (n + 1)) :
    filteredPieceSequenceUnionPiece hμ L hL = filteredPieceSequenceUnionPiece hμ R hR :=
  Subtype.ext (filteredPieceSequenceUnion_eq_of_interleaved L R hLR hRL)

/-- 二つの上方共終な条件が増大可算和で閉じれば、同じ開始部分集合の上で同時に成立する。 -/
lemma exists_commonRefinementConditions (hμ : Cardinal.aleph0 < μ)
    (Q₀ Q₁ : SmallFilteredPieces Cardinal.aleph0 μ J → Prop)
    (h₀ : ∀ A, ∃ B, A ≤ B ∧ Q₀ B) (h₁ : ∀ A, ∃ B, A ≤ B ∧ Q₁ B)
    (hc₀ : ∀ (A : ℕ → SmallFilteredPieces Cardinal.aleph0 μ J) (hA : Monotone A),
      (∀ n, Q₀ (A n)) → Q₀ (filteredPieceSequenceUnionPiece hμ A hA))
    (hc₁ : ∀ (A : ℕ → SmallFilteredPieces Cardinal.aleph0 μ J) (hA : Monotone A),
      (∀ n, Q₁ (A n)) → Q₁ (filteredPieceSequenceUnionPiece hμ A hA))
    (A : SmallFilteredPieces Cardinal.aleph0 μ J) :
    ∃ B, A ≤ B ∧ Q₀ B ∧ Q₁ B := by
  obtain ⟨L, R, hL, hR, hAL, h⟩ := exists_interleavedRefinementSequence Q₀ Q₁ h₀ h₁ A
  have hsame := filteredPieceSequenceUnionPiece_eq_of_interleaved hμ L R hL hR
    (fun n ↦ (h n).2.2.1) (fun n ↦ (h n).2.2.2)
  refine ⟨filteredPieceSequenceUnionPiece hμ L hL,
    hAL.trans (filteredPieceSequence_subset_union L 0),
    hc₀ L hL (fun n ↦ (h n).1), ?_⟩
  rw [hsame]
  exact hc₁ R hR (fun n ↦ (h n).2.1)

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
