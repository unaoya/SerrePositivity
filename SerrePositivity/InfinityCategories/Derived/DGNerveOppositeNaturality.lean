module
public import SerrePositivity.InfinityCategories.Derived.DGNerveOppositeSimplex
public import SerrePositivity.InfinityCategories.Derived.DGNerveOppositeReindex
/-!
概要：符号付き頂点反転と、任意の単調写像による実単体データの引き戻しの自然性。
方針：局所単射・潰れた二点・高次零の三分岐を、反転した実添字で照合する。
規約：全順序写像を扱う。使われ方：dg 反対模型と単体的反対圏の同型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DGNerveOppositeData
open CategoryTheory DifferentialGraded DGNerve DGNerveOppositeIndex DGNerveOppositeSigns
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D] {m n : ℕ}
/-- 符号付き実反転は、全単調写像に沿う実成分の引き戻しと可換。 -/
lemma op_pullback (s : SimplexData R D n) (α : Fin (m + 1) →o Fin (n + 1)) :
    op (s.pullback α) = (op s).pullback (reverseOrderHom α) := by
  apply SimplexData.ext
  · funext i
    simp only [op, SimplexData.pullback, reverseOrderHom_apply, Fin.rev_rev]
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
    change HEq (sign I.card • (s.pullback α).hom (reverse I) b.rev a.rev k
      (two_le_card_reverse hI) (reverse_min hI hb) (reverse_max hI ha)
      (by simpa only [card_reverse] using hk))
      (((op s).pullback (reverseOrderHom α)).hom I a b k hI ha hb hk)
    have hX : s.obj (α b.rev) = s.obj ((reverseOrderHom α b).rev) := by simp
    have hY : s.obj (α a.rev) = s.obj ((reverseOrderHom α a).rev) := by simp
    by_cases hi : Set.InjOn α (reverse I : Set (Fin (m + 1)))
    · have hi' := (reverseOrderHom_injOn_iff α I).mpr hi
      rw [SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi,
        SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi']
      dsimp only [op]
      simp only [id_eq, Finset.card_image_of_injOn hi']
      apply gradedHom_units_smul_heq (R := R) (D := D) hX hY rfl
      have he : reverse (I.image (reverseOrderHom α)) = (reverse I).image α := by
        rw [reverse_image, reverseOrderHom_reverse]
      exact s.hom_heq_of_indices_degree he.symm (by simp) (by simp) rfl
    · have hi' := mt (reverseOrderHom_injOn_iff α I).mp hi
      by_cases hc : I.card = 2
      · have hc' : (reverse I).card = 2 := by simpa only [card_reverse] using hc
        have hk0 : k = 0 := by omega
        subst hk0
        have hs : sign I.card = 1 := (congrArg sign hc).trans sign_two
        rw [hs, one_smul]
        have hL := SimplexData.pullback_hom_of_collapsed_pair s α (reverse I) b.rev a.rev 0
          (two_le_card_reverse hI) (reverse_min hI hb) (reverse_max hI ha)
          (by simpa only [card_reverse] using hk) hi hc'
        have hR := SimplexData.pullback_hom_of_collapsed_pair (op s) (reverseOrderHom α)
          I a b 0 hI ha hb hk hi' hc
        refine hL.trans (HEq.trans ?_ hR.symm)
        change HEq (unitElement R (s.obj (α a.rev))).val
          (unitElement R (s.obj ((reverseOrderHom α b).rev))).val
        have hab := Index.collapse_two (a := b.rev) (b := a.rev) hi hc'
          (by rw [reverse_min hI hb]; exact (reverse I).isLeast_min' _)
          (by rw [reverse_max hI ha]; exact (reverse I).isGreatest_max' _)
        have he : α a.rev = (reverseOrderHom α b).rev := by simpa using hab.symm
        rw [he]
      · have hc' : (reverse I).card ≠ 2 := by simpa only [card_reverse] using hc
        rw [SimplexData.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ hi hc',
          SimplexData.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ hi' hc, smul_zero]
        exact gradedHom_zero_heq hX hY rfl
/-- 全微分式を持つ実単体の反転も、任意の単調写像の引き戻しと可換。 -/
lemma opSimplex_pullback (s : Simplex R D n) (α : Fin (m + 1) →o Fin (n + 1)) :
    opSimplex (s.pullback α) = (opSimplex s).pullback (reverseOrderHom α) := by
  apply Simplex.ext
  exact op_pullback s.toSimplexData α
end SerrePositivity.InfinityCategories.DGNerveOppositeData
