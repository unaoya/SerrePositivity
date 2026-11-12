module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.InterleavedRefinementSequence

/-!
概要：増大する小さい filtered 部分 poset の可算和も、同じ濃度未満の filtered 部分 poset。
方針：二対象を一つの段へ入れて上界を取り、正則性で可算和の小ささを保つ。
規約：和は元の添字 poset 内で取る。使われ方：二辺の交互細分の共通部分表示。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FilteredPieceSequenceUnion
local instance : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩
variable {μ : Cardinal.{u}} {J : Type u} [PartialOrder J]

/-- 同じ元の添字内で、部分 poset 列の和を取る。 -/
def filteredPieceSequenceUnion (A : ℕ → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J) : Set J :=
  ⋃ n, (A n).val

/-- 各実部分集合は同じ和の中に入る。 -/
lemma filteredPieceSequence_subset_union (A : ℕ → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J)
    (n : ℕ) : (A n).val ⊆ filteredPieceSequenceUnion A := by
  change (A n).val ⊆ ⋃ m, (A m).val
  exact Set.subset_iUnion (fun m ↦ (A m).val) n

/-- 増大する filtered 部分 poset の和は filtered。 -/
lemma filteredPieceSequenceUnion_isFiltered
    (A : ℕ → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J) (hA : Monotone A) :
    IsFiltered (filteredPieceSequenceUnion A) := by
  have hF (n : ℕ) : IsFiltered (A n).val :=
    (isCardinalFiltered_aleph0_iff (A n).val).mp (A n).property.1
  have : Nonempty (filteredPieceSequenceUnion A) := by
    have := hF 0
    obtain ⟨x⟩ := (IsFiltered.nonempty : Nonempty (A 0).val)
    exact ⟨⟨x.val, filteredPieceSequence_subset_union A 0 x.property⟩⟩
  have : IsDirectedOrder (filteredPieceSequenceUnion A) := by
    constructor
    intro x y
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp x.property
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp y.property
    let k := max m n
    let x' : (A k).val := ⟨x.val, hA (le_max_left m n) hm⟩
    let y' : (A k).val := ⟨y.val, hA (le_max_right m n) hn⟩
    have := hF k
    have := IsFiltered.isDirectedOrder (A k).val
    obtain ⟨z, hxz, hyz⟩ := exists_ge_ge x' y'
    exact ⟨⟨z.val, filteredPieceSequence_subset_union A k z.property⟩, hxz, hyz⟩
  infer_instance

/-- 非可算正則 μ 未満の部分集合列の和は同じ μ 未満。 -/
lemma filteredPieceSequenceUnion_hasCardinalLT [Fact μ.IsRegular]
    (hμ : Cardinal.aleph0 < μ) (A : ℕ → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J) :
    HasCardinalLT (filteredPieceSequenceUnion A) μ := by
  have hU : HasCardinalLT (ULift.{u} ℕ) μ := by
    rw [hasCardinalLT_iff_cardinal_mk_lt]
    simpa only [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0] using hμ
  have hN : HasCardinalLT ℕ μ :=
    hU.of_surjective ULift.down (fun n ↦ ⟨ULift.up n, rfl⟩)
  exact hasCardinalLT_iUnion _ hN (fun n ↦ (A n).property.2)

/-- 交互に含み合う二列の和は、元の同じ部分集合である。 -/
lemma filteredPieceSequenceUnion_eq_of_interleaved
    (L R : ℕ → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J)
    (hLR : ∀ n, L n ≤ R n) (hRL : ∀ n, R n ≤ L (n + 1)) :
    filteredPieceSequenceUnion L = filteredPieceSequenceUnion R := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨n, hLR n hn⟩
  · intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨n + 1, hRL n hn⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FilteredPieceSequenceUnion
