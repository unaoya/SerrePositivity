module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.SimplexPairing
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.SupportRank
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewisePairingProper

/-!
概要：twisted arrow の延長領域の単体的 pairing の正則性。
方針：頂点の挿入から一意な余次元一の面を得て、辞書式順位を祖先関係へ移す。
規約：inner 条件は内部点の前後の頂点の存在から別に示す。
使われ方：inner horn による延長領域のセル分解。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- pairing の小さい方は大きい方の面。 -/
lemma twistedArrowExtensionPairing_le {n : ℕ} (i : Fin (n + 1))
    (hi : i < Fin.last n) (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowExtensionPairing.{u} i hi).II) :
    s.val ≤ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowExtensionPairing i hi).p s).val := by
  apply (Subcomplex.N.le_iff).mpr
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport_subset_iff _ _).mp
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowExtensionPairing_support]
  exact Finset.subset_insert _ _

/-- pairing は新しい頂点を一つ挿入するので、次元を一つ増やす。 -/
lemma twistedArrowExtensionPairing_dim {n : ℕ} (i : Fin (n + 1))
    (hi : i < Fin.last n) (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowExtensionPairing.{u} i hi).II) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowExtensionPairing i hi).p s).val.dim = s.val.dim + 1 := by
  have h := congrArg Finset.card (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowExtensionPairing_support i hi s)
  have hs := s.property
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport s.val.toN) ∉
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport s.val.toN at hs
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport_card] at h
  erw [Finset.card_insert_of_notMem hs] at h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport_card] at h
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowExtensionPairing i hi).p s).val.dim + 1 = s.val.dim + 1 + 1 at h
  omega

/-- pairing の各対は一意な余次元一の面。 -/
instance twistedArrowExtensionPairing_isProper {n : ℕ} (i : Fin (n + 1))
    (hi : i < Fin.last n) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowExtensionPairing.{u} i hi).IsProper where
  isUniquelyCodimOneFace s := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.uniquelyCodimOneFace_of_nonsingular_le s.val.toN
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowExtensionPairing i hi).p s).val.toN
    (twistedArrowExtensionPairing_le i hi s) (twistedArrowExtensionPairing_dim i hi s)

/-- 単体の祖先関係では、有限頂点集合の辞書式順位が下がる。 -/
lemma twistedArrowExtensionPairing_ancestral_rank_lt {n : ℕ} (i : Fin (n + 1))
    (hi : i < Fin.last n) (s t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowExtensionPairing.{u} i hi).II)
    (hst : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowExtensionPairing i hi).AncestralRel s t) :
    Prod.Lex (· < ·) (· < ·)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportRank i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport s.val.toN))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportRank i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport t.val.toN)) := by
  have hsub := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport_subset_iff s.val.toN
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowExtensionPairing i hi).p t).val.toN).mpr hst.2.le
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowExtensionPairing_support] at hsub
  have hne : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport s.val.toN ≠
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport t.val.toN := by
    intro h
    apply hst.1
    apply Subtype.ext
    apply (Subcomplex.N.ext_iff _ _).mpr
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport_injective _ h
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportRank_lt i _ _ hsub s.property hne

/-- twisted arrow の延長領域の pairing は正則。 -/
instance twistedArrowExtensionPairing_isRegular {n : ℕ} (i : Fin (n + 1))
    (hi : i < Fin.last n) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowExtensionPairing.{u} i hi).IsRegular where
  isUniquelyCodimOneFace :=
    (twistedArrowExtensionPairing_isProper i hi).isUniquelyCodimOneFace
  wf := by
    let r : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowExtensionPairing.{u} i hi).II → ℕ × ℕ := fun s ↦
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportRank i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport s.val.toN)
    have h : WellFounded (Prod.Lex (α := ℕ) (β := ℕ) (· < ·) (· < ·)) :=
      Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf
    refine (InvImage.wf r h).mono ?_
    intro s t hst
    exact twistedArrowExtensionPairing_ancestral_rank_lt i hi s t hst

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
