module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallDiagramFactorization

/-!
概要：小さい filtered 部分添字の全空間と、指定対象より上にある部分の filtered 性。
方針：部分集合族を一つの小さい filtered 部分集合に収め、その内部で対象の上界を取る。
規約：全空間の順序は部分集合の包含と元の対象の順序を同時に保持する。
使われ方：元の添字への同じ値射影の cofinal 性。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 部分添字と、その部分添字に属する元の対象の組。 -/
def SmallFilteredTotal (κ μ : Cardinal.{u}) [Fact κ.IsRegular] (I : Type u) [PartialOrder I] :=
  {x : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces κ μ I × I // x.2 ∈ x.1.val}

instance smallFilteredTotal_partialOrder (κ μ : Cardinal.{u}) [Fact κ.IsRegular]
    (I : Type u) [PartialOrder I] : PartialOrder (SmallFilteredTotal κ μ I) :=
  inferInstanceAs (PartialOrder {x : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces κ μ I × I // x.2 ∈ x.1.val})

variable {κ μ : Cardinal.{u}} [Fact κ.IsRegular] {I : Type u} [PartialOrder I]

/-- 元の対象を保持する全空間の値射影。 -/
def smallFilteredTotalValue : SmallFilteredTotal κ μ I ⥤ I where
  obj x := x.val.2
  map f := homOfLE (leOfHom f).2

/-- 元の部分添字を保持する全空間の射影。 -/
def smallFilteredTotalPiece : SmallFilteredTotal κ μ I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces κ μ I where
  obj x := x.val.1
  map f := homOfLE (leOfHom f).1

/-- 指定対象 i より上にある、同じ全空間の部分 poset。 -/
def SmallFilteredTotalAbove (κ μ : Cardinal.{u}) [Fact κ.IsRegular]
    {I : Type u} [PartialOrder I] (i : I) :=
  {x : SmallFilteredTotal κ μ I // i ≤ x.val.2}

instance smallFilteredTotalAbove_partialOrder (κ μ : Cardinal.{u}) [Fact κ.IsRegular]
    {I : Type u} [PartialOrder I] (i : I) : PartialOrder (SmallFilteredTotalAbove κ μ i) :=
  inferInstanceAs (PartialOrder {x : SmallFilteredTotal κ μ I // i ≤ x.val.2})

/-- 値射影の各上方 comma の対象 poset は、同じ κ に対して filtered。 -/
lemma smallFilteredTotalAbove_isCardinalFiltered [Fact μ.IsRegular]
    [IsCardinalFiltered I κ] (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ) (i : I) :
    IsCardinalFiltered (SmallFilteredTotalAbove κ μ i) κ := by
  apply isCardinalFiltered_preorder
  intro K s hK
  have hKκ : HasCardinalLT K κ := (hasCardinalLT_iff_cardinal_mk_lt _ _).mpr hK
  have hKμ : HasCardinalLT K μ := hKκ.of_le h.le
  have hU : HasCardinalLT (⋃ k, (s k).val.val.1.val) μ :=
    hasCardinalLT_iUnion _ hKμ (fun k ↦ (s k).val.val.1.property.2)
  have hi : HasCardinalLT ({i} : Set I) μ :=
    hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le (Fact.out : μ.IsRegular))
  have hUnion : HasCardinalLT (((⋃ k, (s k).val.val.1.val) ∪ {i}) : Set I) μ :=
    hasCardinalLT_union (Cardinal.IsRegular.aleph0_le (Fact.out : μ.IsRegular)) hU hi
  obtain ⟨B, hB⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.exists_smallFilteredPiece_containing h _ hUnion
  have hBi : i ∈ B.val := hB (Set.mem_union_right _ (Set.mem_singleton i))
  have hBs (k : K) : (s k).val.val.1.val ⊆ B.val :=
    fun x hx ↦ hB (Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨k, hx⟩))
  let f : Option K → B.val := fun k ↦ match k with
    | none => ⟨i, hBi⟩
    | some k => ⟨(s k).val.val.2, hBs k (s k).val.property⟩
  have hOption : HasCardinalLT (Option K) κ :=
    (hasCardinalLT_option_iff _ _ (Cardinal.IsRegular.aleph0_le (Fact.out : κ.IsRegular))).mpr hKκ
  have := B.property.1
  obtain ⟨j, ⟨hj⟩⟩ := IsCardinalFiltered.exists_max (κ := κ) f hOption
  refine ⟨⟨⟨⟨B, j.val⟩, j.property⟩, leOfHom (hj none)⟩, fun k ↦ ?_⟩
  exact ⟨hBs k, leOfHom (hj (some k))⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
