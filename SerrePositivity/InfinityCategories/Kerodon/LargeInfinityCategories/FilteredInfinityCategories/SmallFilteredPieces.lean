module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CardinalChangeBound
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredPosetNerve

/-!
概要：κ-filtered poset を、μ-small な κ-filtered 部分集合の μ-filtered な族で被覆する。
方針：明示的な冪の評価から小さい filtered 拡大を得て、和集合に上界を作る。
規約：通常の poset は元の coherent 図式の添字としてだけ使用。圏の濃度変更は未結論。
使われ方：HTT 5.4.2.8〜9 の部分表示の添字。

対応節は Kerodon 9.1（Tag 05WY）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories

/-- 元の poset 内の、κ-filtered かつ濃度 μ 未満の部分集合の包含順。 -/
def SmallFilteredPieces (κ μ : Cardinal.{u}) [Fact κ.IsRegular] (I : Type u) [PartialOrder I] :=
  {A : Set I // IsCardinalFiltered A κ ∧ HasCardinalLT A μ}

instance smallFilteredPieces_partialOrder (κ μ : Cardinal.{u}) [Fact κ.IsRegular]
    (I : Type u) [PartialOrder I] :
    PartialOrder (SmallFilteredPieces κ μ I) := inferInstanceAs
  (PartialOrder {A : Set I // IsCardinalFiltered A κ ∧ HasCardinalLT A μ})

variable {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
  (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ) {I : Type u} [PartialOrder I] [IsCardinalFiltered I κ]
include h

/-- 元の μ-small な部分集合は、同じ I 内の μ-small κ-filtered 部分集合へ拡大できる。 -/
lemma exists_smallFilteredPiece_containing (A : Set I) (hA : HasCardinalLT A μ) :
    ∃ B : SmallFilteredPieces κ μ I, A ⊆ B.val := by
  obtain ⟨B, hAB, hB, hBμ⟩ := Cardinal.SharplyLT.exists_isCardinalFiltered_set
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound.sharplyLT h) A hA
  exact ⟨⟨B, hB, hBμ⟩, hAB⟩

/-- 同じ小さい filtered 部分集合の包含順は μ-filtered。 -/
lemma smallFilteredPieces_isCardinalFiltered :
    IsCardinalFiltered (SmallFilteredPieces κ μ I) μ := by
  apply isCardinalFiltered_preorder
  intro K f hK
  have hK' : HasCardinalLT K μ := (hasCardinalLT_iff_cardinal_mk_lt K μ).mpr hK
  have hA : HasCardinalLT (⋃ k, (f k).val) μ :=
    hasCardinalLT_iUnion _ hK' (fun k ↦ (f k).property.2)
  obtain ⟨B, hB⟩ := exists_smallFilteredPiece_containing h (⋃ k, (f k).val) hA
  exact ⟨B, fun k ↦ (Set.subset_iUnion _ k).trans hB⟩

/-- 元の I の全対象が、同じ小さい filtered 部分集合のどれかに実際に属する。 -/
lemma smallFilteredPieces_cover (i : I) : ∃ A : SmallFilteredPieces κ μ I, i ∈ A.val := by
  have hs : HasCardinalLT ({i} : Set I) μ :=
    hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le (Fact.out : μ.IsRegular))
  obtain ⟨A, hA⟩ := exists_smallFilteredPiece_containing h {i} hs
  exact ⟨A, hA (Set.mem_singleton i)⟩

/-- 同じ部分集合族の nerve は、全 coherent μ-small 図式に対して μ-filtered。 -/
lemma smallFilteredPieces_nerve_isKappaFiltered :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ (nerve (SmallFilteredPieces κ μ I)) := by
  have := smallFilteredPieces_isCardinalFiltered h (I := I)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_nerve_of_cardinalFiltered _

omit h [IsCardinalFiltered I κ] [Fact μ.IsRegular] in
/-- 元の各部分集合の nerve は、全 coherent κ-small 図式に対して κ-filtered。 -/
lemma smallFilteredPiece_nerve_isKappaFiltered (A : SmallFilteredPieces κ μ I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ (nerve A.val) := by
  have := A.property.1
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_nerve_of_cardinalFiltered _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
