module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces

/-!
概要：表示添字内の κ₀-filtered な小部分を長さ κ₀ の増大列で合併する。
方針：κ₀ 個未満の対象の所属段を一つの段へ集め、その段の filtered 性を使う。
規約：同じ元の表示添字内の部分集合を保ち、μ-small 性も同時に保持する。
使われ方：相対交互構成の最終段と極限段の表示部分。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：κ-filtered な段添字上の増大する κ-filtered 部分の合併も κ-filtered。
方針：小さい対象族の所属段を一段へまとめて上界を取る。
規約：元の表示 poset の対象と順序を保持する。
使われ方：長い相対交互構成で得られる合併部分。 -/
lemma chainUnion_isCardinalFiltered {κ μ : Cardinal.{u}} [Fact κ.IsRegular]
    {I T : Type u} [PartialOrder I] [Preorder T] [IsCardinalFiltered T κ]
    (A : T → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces κ μ I) (hA : Monotone A) :
    IsCardinalFiltered (⋃ t, (A t).val) κ := by
  apply isCardinalFiltered_preorder
  intro K f hK
  have hK' : HasCardinalLT K κ := (hasCardinalLT_iff_cardinal_mk_lt _ _).mpr hK
  have hm : ∀ k, ∃ t, (f k).val ∈ (A t).val :=
    fun k ↦ Set.mem_iUnion.mp (f k).property
  choose t ht using hm
  obtain ⟨s, ⟨hs⟩⟩ := IsCardinalFiltered.exists_max (κ := κ) t hK'
  have : IsCardinalFiltered (A s).val κ := (A s).property.1
  let g : K → (A s).val := fun k ↦ ⟨(f k).val, hA (leOfHom (hs k)) (ht k)⟩
  obtain ⟨z, ⟨hz⟩⟩ := IsCardinalFiltered.exists_max (κ := κ) g hK'
  exact ⟨⟨z.val, Set.mem_iUnion.mpr ⟨s, z.property⟩⟩, fun k ↦ leOfHom (hz k)⟩

/-- 概要：μ-small な filtered 段族の増大合併は同じ小さい filtered 部分として保持できる。
方針：元の合併の filtered 性と正則 μ による小ささを組み合わせる。
規約：合併部分そのものを返す。
使われ方：表示添字内の相対構成の全小生成情報。 -/
def chainUnionPiece {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    {I T : Type u} [PartialOrder I] [Preorder T] [IsCardinalFiltered T κ]
    (A : T → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces κ μ I) (hA : Monotone A) (hT : HasCardinalLT T μ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces κ μ I :=
  ⟨⋃ t, (A t).val, chainUnion_isCardinalFiltered A hA,
    hasCardinalLT_iUnion _ hT (fun t ↦ (A t).property.2)⟩

/-- 概要：長さ κ の正則順序添字は元の全 κ-small coherent 図式について filtered。
方針：正則順序の通常の filtered 性を既存の nerve 判定へ渡す。
規約：κ と同じ宇宙の全単体を使う。
使われ方：交互構成の最終余極限が存在する形状。 -/
lemma ordinalNerve_isKappaFiltered (κ : Cardinal.{u}) [Fact κ.IsRegular] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ (nerve κ.ord.ToType) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_nerve_of_cardinalFiltered _

/-- 概要：長さ κ の増大列の最終合併は μ-small な κ-filtered 表示部分。
方針：正則順序の段数 κ が μ より小さいことを合併構成へ渡す。
規約：元の表示添字を変更しない。
使われ方：長さ κ₀ の相対交互構成の最終段。 -/
def ordinalChainUnionPiece {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (hκμ : κ < μ) {I : Type u} [PartialOrder I]
    (A : κ.ord.ToType → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces κ μ I) (hA : Monotone A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces κ μ I :=
  chainUnionPiece A hA (by simpa [hasCardinalLT_iff_cardinal_mk_lt] using hκμ)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
