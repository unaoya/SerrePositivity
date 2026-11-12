module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.CodiscreteFreshCocone
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.CodiscreteConeCut
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ConeSimplexPrefix

/-!
概要：元の部分複体の包含に未使用ラベルの頂点を加えた同じ錐写像は単射。
方針：ラベルで左右の切断を回収し、先頭区間の制限と元の包含の単射性で左単体を回収する。
規約：単射性は元の全次数で証明し、追加仮定にしない。
使われ方：小さい部分複体から同じラベル付き積内への単射な錐の拡大。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {K C : SSet.{u}} {T : Type u}

/-- 同じ新しいラベルを持つ錐の元の写像は、元の底の包含が単射なら単射。 -/
lemma codiscreteProductCocone_mono (p : K ⟶ C ⊗ nerve (Codiscrete T)) [Mono p]
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (p ≫ fst C (nerve (Codiscrete T)))) (a : T)
    (ha : ∀ x : K _⦋0⦌, (nerveEquiv ((p ≫ snd C (nerve (Codiscrete T))).app _ x)).as ≠ a) :
    Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.codiscreteProductCocone p c a).val := by
  let d := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.codiscreteProductCocone p c a
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨n⟩⟩
  rw [mono_iff_injective]
  intro s t h
  have hlabel := congrArg (fun z => (snd C (nerve (Codiscrete T))).app _ z) h
  change ((d.val ≫ snd C (nerve (Codiscrete T))).app _ s) =
    ((d.val ≫ snd C (nerve (Codiscrete T))).app _ t) at hlabel
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.codiscreteProductCocone_snd] at hlabel
  have hcut := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.codiscreteConeLabelMap_cut _ a ha hlabel
  rcases s with ⟨⟨l, hl⟩, x, y⟩
  rcases t with ⟨i, x', y'⟩
  cases hcut
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ (Fin.ext rfl) ?_ ?_
  · change x = x'
    cases l with
    | zero => exact @Subsingleton.elim PUnit inferInstance x x'
    | succ l =>
      apply (mono_iff_injective (p.app (Opposite.op ⦋l⦌))).mp inferInstance
      have hlen : l + 1 ≤ n + 1 := by
        have hbound : l + 1 < n + 2 := hl
        omega
      let α : ⦋l⦌ ⟶ ⦋n⦌ := SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.prefixIncl (n + 1) (l + 1) hlen)
      have hh := congrArg ((C ⊗ nerve (Codiscrete T)).map α.op) h
      have hs := ConcreteCategory.congr_hom (d.val.naturality α.op) ⟨⟨l + 1, hl⟩, x, y⟩
      have ht := ConcreteCategory.congr_hom (d.val.naturality α.op) ⟨⟨l + 1, hl⟩, x', y'⟩
      have he := hs.trans (hh.trans ht.symm)
      change d.val.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0]).map α.op _) =
        d.val.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0]).map α.op _) at he
      dsimp only [α] at he
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneSimplex_prefix, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneSimplex_prefix] at he
      change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0] ≫ d.val).app _ x) =
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0] ≫ d.val).app _ x') at he
      rw [d.property] at he
      exact he
  · exact Subsingleton.elim _ _

/-- 同じ小さい単射な図式は、新しい頂点を持つ同じ積内の単射な錐へ拡大できる。 -/
lemma exists_mono_fresh_codiscreteProductCocone {κ : Cardinal.{u}} [Quasicategory C]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ C] (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ K) (hT : κ ≤ Cardinal.mk T)
    (p : K ⟶ C ⊗ nerve (Codiscrete T)) [Mono p] :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p, Mono d.val ∧ ∀ x : K _⦋0⦌, p.app _ x ≠ d.vertex := by
  obtain ⟨c⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered.cocone_nonempty hK (p ≫ fst C (nerve (Codiscrete T)))
  obtain ⟨a, ha⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_fresh_vertex_label hK hT
    (fun x => (nerveEquiv ((p ≫ snd C (nerve (Codiscrete T))).app _ x)).as)
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.codiscreteProductCocone p c a, codiscreteProductCocone_mono p c a ha,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.codiscreteProductCocone_fresh p c a ha⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
