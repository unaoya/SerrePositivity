module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.CofinalFilteredPoset

/-!
概要：通常の κ-filtered poset の nerve は、元の全 κ-small 図式について κ-filtered。
方針：元の図式の頂点の共通上界を取り、同じ上界を頂点とする nerve 余錐を使う。
規約：F2 の IsKappaFiltered を再利用し、試験図式を通常の nerve に制限しない。
使われ方：cofinal poset 上の図式にも元の κ-filtered 余極限の閉包を適用する。

対応節は Kerodon 9.1（Tag 05WY）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories

/-- 通常の κ-filtered poset の nerve は全 κ-small 図式に対して κ-filtered。 -/
lemma isKappaFiltered_nerve_of_cardinalFiltered {κ : Cardinal.{u}} [Fact κ.IsRegular]
    (I : Type u) [Preorder I] [IsCardinalFiltered I κ] : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ (nerve I) where
  cocone_nonempty {K} hK a := by
    have hcard : HasCardinalLT (K _⦋0⦌) κ :=
      (hasCardinalLT_iff_cardinal_mk_lt _ _).mpr (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.cardinal_vertices_lt_of_isKappaSmall hK)
    obtain ⟨i, ⟨hi⟩⟩ := IsCardinalFiltered.exists_max
      (κ := κ) (fun v : K _⦋0⦌ => (a.app _ v).obj 0) hcard
    obtain ⟨c, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_nerve_joinCocone_at_bound a i (fun v => leOfHom (hi v))
    exact ⟨c⟩

/-- 同じ cofinal poset は通常の κ-filtered 性と元の nerve の κ-filtered 性を両方持つ。 -/
lemma exists_cofinal_kappaFiltered_poset {κ : Cardinal.{u}} [Fact κ.IsRegular]
    (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ C] :
    ∃ (I : Type u) (o : PartialOrder I),
      letI := o
      ∃ f : nerve I ⟶ C,
        IsCardinalFiltered I κ ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ (nerve I) ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal f := by
  obtain ⟨I, o, f, hI, hf⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.exists_cofinal_cardinalFiltered_poset (κ := κ) C
  letI := o
  have := hI
  exact ⟨I, o, f, hI, isKappaFiltered_nerve_of_cardinalFiltered I, hf⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.3.1.18"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.exists_cofinal_kappaFiltered_poset
attribute [cite HTT "5.3.1.8" (partial := direction) "仮定：正則 κ と半順序 A の全 κ-small 部分集合に上界が存在する（HTT の一方の条件と一致）。結論：N(A) が全 κ-small 単体図式について κ-filtered（Lean が弱い：上界条件⇒神経の κ-filtered 性の向き）。Mathlib の任意の小さい族への共通上界から IsCardinalFiltered を得る型と、その神経への宣言を合成する。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_nerve_of_cardinalFiltered
