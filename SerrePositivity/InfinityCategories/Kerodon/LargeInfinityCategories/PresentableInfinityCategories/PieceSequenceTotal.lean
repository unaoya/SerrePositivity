module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FilteredPieceSequenceUnion
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.MonotoneNerveCofinality

/-!
概要：増大部分 poset 列の全空間と、和への元の値射影を構成する。
方針：段番号と実対象の対に積順序を入れ、同じ段内の上界を使う。
規約：元の添字 poset の射を保持。使われ方：部分余極限列から和の余極限への比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal
local instance : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩
variable {μ : Cardinal.{u}} {J : Type u} [PartialOrder J]

/-- 段番号と、その同じ段に属する元の実対象の対。 -/
def PieceSequenceTotal (A : ℕ → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J) :=
  {x : ULift.{u} ℕ × J // x.2 ∈ (A x.1.down).val}

instance pieceSequenceTotal_partialOrder (A : ℕ → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J) :
    PartialOrder (PieceSequenceTotal A) := inferInstanceAs
  (PartialOrder {x : ULift.{u} ℕ × J // x.2 ∈ (A x.1.down).val})

/-- 同じ実対象を、元の部分集合列の和の中へ送る単調写像。 -/
def pieceSequenceTotalValueMonotone (A : ℕ → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J) :
    Monotone (fun x : PieceSequenceTotal A ↦
      (⟨x.val.2, Set.mem_iUnion.mpr ⟨x.val.1.down, x.property⟩⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FilteredPieceSequenceUnion.filteredPieceSequenceUnion A)) :=
  fun _ _ h ↦ h.2

/-- 元の段番号への射影関手。 -/
def pieceSequenceTotalIndex (A : ℕ → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J) :
    PieceSequenceTotal A ⥤ ULift.{u} ℕ where
  obj x := x.val.1
  map f := homOfLE (leOfHom f).1

/-- 指定段の元の部分 poset を、同じ全空間の fiber へ入れる。 -/
def pieceSequenceTotalFiber (A : ℕ → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J) (n : ℕ) :
    (A n).val ⥤ PieceSequenceTotal A where
  obj x := ⟨(ULift.up n, x.val), x.property⟩
  map f := homOfLE ⟨le_refl _, leOfHom f⟩

/-- 増大する filtered 部分 poset 列の全空間の順序は directed。 -/
lemma pieceSequenceTotal_isDirectedOrder
    (A : ℕ → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J) (hA : Monotone A) :
    IsDirectedOrder (PieceSequenceTotal A) := by
  constructor
  intro x y
  let n := max x.val.1.down y.val.1.down
  let x' : (A n).val := ⟨x.val.2, hA (le_max_left _ _) x.property⟩
  let y' : (A n).val := ⟨y.val.2, hA (le_max_right _ _) y.property⟩
  have : IsFiltered (A n).val :=
    (isCardinalFiltered_aleph0_iff (A n).val).mp (A n).property.1
  have := IsFiltered.isDirectedOrder (A n).val
  obtain ⟨z, hx, hy⟩ := exists_ge_ge x' y'
  exact ⟨⟨(ULift.up n, z.val), z.property⟩, ⟨le_max_left _ _, hx⟩, ⟨le_max_right _ _, hy⟩⟩

/-- 同じ全空間の値射影は、和の元の nerve へ right cofinal。 -/
lemma pieceSequenceTotalValue_nerve_isRightCofinal
    (A : ℕ → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J) (hA : Monotone A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (nerveMap (pieceSequenceTotalValueMonotone A).functor) := by
  have := pieceSequenceTotal_isDirectedOrder A hA
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.monotone_nerveMap_isRightCofinal (pieceSequenceTotalValueMonotone A)
  intro x
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp x.property
  exact ⟨⟨(ULift.up n, x.val), hn⟩, le_refl _⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal
