module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewisePairingProper

/-!
概要：edgewise の単体的 pairing の正則性。
方針：頂点集合の順位を非退化単体へ引き戻し、祖先関係で厳密に下がることを示す。
規約：順位は反転した最小左添字と頂点数の辞書式順序。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、ホーン接合による Kan 延長の停止性。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：edgewise の pairing の祖先関係は頂点集合の辞書式順位を下げる。
方針：別の対の大きい単体の面である条件を頂点包含へ移し、既存の有限集合の順位の補題を使う。
規約：祖先関係は型 II の非退化単体の間で定義される。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、単体的な pairing の正則性の判定。 -/
lemma edgewiseExtensionPairing_ancestral_rank_lt (n : ℕ)
    (s t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseExtensionPairing.{u} n).II)
    (hst : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseExtensionPairing n).AncestralRel s t) :
    Prod.Lex (· < ·) (· < ·)
      (n - (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSupportPivot (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport s.val.toN)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseOutsideSimplexEquiv n s.val).property).val,
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport s.val.toN).card)
      (n - (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSupportPivot (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport t.val.toN)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseOutsideSimplexEquiv n t.val).property).val,
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport t.val.toN).card) := by
  have hsub := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport_subset_iff s.val.toN
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseExtensionPairing n).p t).val.toN).2 hst.2.le
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseExtensionPairing_support] at hsub
  have hne : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport s.val.toN ≠
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport t.val.toN := by
    intro h
    apply hst.1
    apply Subtype.ext
    apply (Subcomplex.N.ext_iff _ _).2
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport_injective _ h
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSupport_rank_lt _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseOutsideSimplexEquiv n s.val).property
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseOutsideSimplexEquiv n t.val).property hsub s.property hne

/-- 概要：edgewise の非退化単体の pairing は正則。
方針：proper 性に加え、自然数二成分の well-founded な辞書式順位を祖先関係へ引き戻す。
規約：well-founded 性は有限集合の順位の減少から得て、選択した接合順序には依存しない。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、延長領域の包含のホーンセル分解。 -/
instance edgewiseExtensionPairing_isRegular (n : ℕ) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseExtensionPairing.{u} n).IsRegular where
  isUniquelyCodimOneFace := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseExtensionPairing_isProper n).isUniquelyCodimOneFace
  wf := by
    let r : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseExtensionPairing.{u} n).II → ℕ × ℕ := fun s ↦
      (n - (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSupportPivot (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport s.val.toN)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseOutsideSimplexEquiv n s.val).property).val,
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport s.val.toN).card)
    have h : WellFounded (Prod.Lex (α := ℕ) (β := ℕ) (· < ·) (· < ·)) :=
      Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf
    refine (InvImage.wf r h).mono ?_
    intro s t hst
    exact edgewiseExtensionPairing_ancestral_rank_lt n s t hst

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
