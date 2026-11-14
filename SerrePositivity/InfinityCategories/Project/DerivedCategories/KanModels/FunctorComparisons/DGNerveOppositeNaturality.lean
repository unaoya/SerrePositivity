module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveOppositeSimplex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveOppositeReindex
/-!
概要：符号付き頂点反転と、任意の単調写像による実単体データの引き戻しの自然性。
方針：局所単射・潰れた二点・高次零の三分岐を、反転した実添字で照合する。
規約：全順序写像を扱う。使われ方：dg 反対模型と単体的反対圏の同型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGNerveOppositeIndex
variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {m n : ℕ}
/-- 符号付き実反転は、全単調写像に沿う実成分の引き戻しと可換。 -/
lemma op_pullback (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n) (α : Fin (m + 1) →o Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.op (s.pullback α) = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.op s).pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.reverseOrderHom α) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · funext i
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.op, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.reverseOrderHom_apply, Fin.rev_rev]
  · apply Function.hfunext rfl
    intro I I' h
    cases h
    apply Function.hfunext rfl
    intro a a' h
    cases h
    apply Function.hfunext rfl
    intro b b' h
    cases h
    apply Function.hfunext rfl
    intro k k' h
    cases h
    apply Function.hfunext rfl
    intro hI hI' h
    cases h
    apply Function.hfunext rfl
    intro ha ha' h
    cases h
    apply Function.hfunext rfl
    intro hb hb' h
    cases h
    apply Function.hfunext rfl
    intro hk hk' h
    cases h
    change HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign I.card • (s.pullback α).hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I) b.rev a.rev k
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.two_le_card_reverse hI) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_min hI hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_max hI ha)
      (by simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.card_reverse] using hk))
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.op s).pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.reverseOrderHom α)).hom I a b k hI ha hb hk)
    have hX : s.obj (α b.rev) = s.obj ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.reverseOrderHom α b).rev) := by simp
    have hY : s.obj (α a.rev) = s.obj ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.reverseOrderHom α a).rev) := by simp
    by_cases hi : Set.InjOn α (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I : Set (Fin (m + 1)))
    · have hi' := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.reverseOrderHom_injOn_iff α I).mpr hi
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi,
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi']
      dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.op]
      simp only [id_eq, Finset.card_image_of_injOn hi']
      apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.gradedHom_units_smul_heq (R := R) (D := D) hX hY rfl
      have he : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse (I.image (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.reverseOrderHom α)) = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I).image α := by
        rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.reverse_image, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.reverseOrderHom_reverse]
      exact s.hom_heq_of_indices_degree he.symm (by simp) (by simp) rfl
    · have hi' := mt (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.reverseOrderHom_injOn_iff α I).mp hi
      by_cases hc : I.card = 2
      · have hc' : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I).card = 2 := by simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.card_reverse] using hc
        have hk0 : k = 0 := by omega
        subst hk0
        have hs : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign I.card = 1 := (congrArg _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign hc).trans _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign_two
        rw [hs, one_smul]
        have hL := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_collapsed_pair s α (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I) b.rev a.rev 0
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.two_le_card_reverse hI) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_min hI hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_max hI ha)
          (by simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.card_reverse] using hk) hi hc'
        have hR := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_collapsed_pair (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.op s) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.reverseOrderHom α)
          I a b 0 hI ha hb hk hi' hc
        refine hL.trans (HEq.trans ?_ hR.symm)
        change HEq (_root_.SerrePositivity.DifferentialGraded.unitElement R (s.obj (α a.rev))).val
          (_root_.SerrePositivity.DifferentialGraded.unitElement R (s.obj ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.reverseOrderHom α b).rev))).val
        have hab := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.collapse_two (a := b.rev) (b := a.rev) hi hc'
          (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_min hI hb]; exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I).isLeast_min' _)
          (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_max hI ha]; exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I).isGreatest_max' _)
        have he : α a.rev = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.reverseOrderHom α b).rev := by simpa using hab.symm
        rw [he]
      · have hc' : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I).card ≠ 2 := by simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.card_reverse] using hc
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ hi hc',
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ hi' hc, smul_zero]
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq hX hY rfl
/-- 全微分式を持つ実単体の反転も、任意の単調写像の引き戻しと可換。 -/
lemma opSimplex_pullback (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D n) (α : Fin (m + 1) →o Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.opSimplex (s.pullback α) = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.opSimplex s).pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.reverseOrderHom α) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact op_pullback s.toSimplexData α
end SerrePositivity.InfinityCategories.Project.DerivedCategories
