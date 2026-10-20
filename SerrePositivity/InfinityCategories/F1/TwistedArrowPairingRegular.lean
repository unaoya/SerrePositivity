module

public import SerrePositivity.InfinityCategories.F1.TwistedArrowSimplexPairing
public import SerrePositivity.InfinityCategories.F1.TwistedArrowSupportRank
public import SerrePositivity.InfinityCategories.F1.EdgewisePairingProper

/-!
概要：twisted arrow の延長領域の単体的 pairing の正則性。
方針：頂点の挿入から一意な余次元一の面を得て、辞書式順位を祖先関係へ移す。
規約：inner 条件は内部点の前後の頂点の存在から別に示す。
使われ方：inner horn による延長領域のセル分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- pairing の小さい方は大きい方の面。 -/
lemma twistedArrowExtensionPairing_le {n : ℕ} (i : Fin (n + 1))
    (hi : i < Fin.last n) (s : (twistedArrowExtensionPairing.{u} i hi).II) :
    s.val ≤ ((twistedArrowExtensionPairing i hi).p s).val := by
  apply (Subcomplex.N.le_iff).mpr
  apply (stdSimplexNondegenerateSupport_subset_iff _ _).mp
  rw [twistedArrowExtensionPairing_support]
  exact Finset.subset_insert _ _

/-- pairing は新しい頂点を一つ挿入するので、次元を一つ増やす。 -/
lemma twistedArrowExtensionPairing_dim {n : ℕ} (i : Fin (n + 1))
    (hi : i < Fin.last n) (s : (twistedArrowExtensionPairing.{u} i hi).II) :
    ((twistedArrowExtensionPairing i hi).p s).val.dim = s.val.dim + 1 := by
  have h := congrArg Finset.card (twistedArrowExtensionPairing_support i hi s)
  have hs := s.property
  change twistedArrowSupportPivot i (stdSimplexNondegenerateSupport s.val.toN) ∉
    stdSimplexNondegenerateSupport s.val.toN at hs
  rw [stdSimplexNondegenerateSupport_card] at h
  erw [Finset.card_insert_of_notMem hs] at h
  rw [stdSimplexNondegenerateSupport_card] at h
  change ((twistedArrowExtensionPairing i hi).p s).val.dim + 1 = s.val.dim + 1 + 1 at h
  omega

/-- pairing の各対は一意な余次元一の面。 -/
instance twistedArrowExtensionPairing_isProper {n : ℕ} (i : Fin (n + 1))
    (hi : i < Fin.last n) : (twistedArrowExtensionPairing.{u} i hi).IsProper where
  isUniquelyCodimOneFace s := uniquelyCodimOneFace_of_nonsingular_le s.val.toN
    ((twistedArrowExtensionPairing i hi).p s).val.toN
    (twistedArrowExtensionPairing_le i hi s) (twistedArrowExtensionPairing_dim i hi s)

/-- 単体の祖先関係では、有限頂点集合の辞書式順位が下がる。 -/
lemma twistedArrowExtensionPairing_ancestral_rank_lt {n : ℕ} (i : Fin (n + 1))
    (hi : i < Fin.last n) (s t : (twistedArrowExtensionPairing.{u} i hi).II)
    (hst : (twistedArrowExtensionPairing i hi).AncestralRel s t) :
    Prod.Lex (· < ·) (· < ·)
      (twistedArrowSupportRank i (stdSimplexNondegenerateSupport s.val.toN))
      (twistedArrowSupportRank i (stdSimplexNondegenerateSupport t.val.toN)) := by
  have hsub := (stdSimplexNondegenerateSupport_subset_iff s.val.toN
    ((twistedArrowExtensionPairing i hi).p t).val.toN).mpr hst.2.le
  rw [twistedArrowExtensionPairing_support] at hsub
  have hne : stdSimplexNondegenerateSupport s.val.toN ≠
      stdSimplexNondegenerateSupport t.val.toN := by
    intro h
    apply hst.1
    apply Subtype.ext
    apply (Subcomplex.N.ext_iff _ _).mpr
    exact stdSimplexNondegenerateSupport_injective _ h
  exact twistedArrowSupportRank_lt i _ _ hsub s.property hne

/-- twisted arrow の延長領域の pairing は正則。 -/
instance twistedArrowExtensionPairing_isRegular {n : ℕ} (i : Fin (n + 1))
    (hi : i < Fin.last n) : (twistedArrowExtensionPairing.{u} i hi).IsRegular where
  isUniquelyCodimOneFace :=
    (twistedArrowExtensionPairing_isProper i hi).isUniquelyCodimOneFace
  wf := by
    let r : (twistedArrowExtensionPairing.{u} i hi).II → ℕ × ℕ := fun s ↦
      twistedArrowSupportRank i (stdSimplexNondegenerateSupport s.val.toN)
    have h : WellFounded (Prod.Lex (α := ℕ) (β := ℕ) (· < ·) (· < ·)) :=
      Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf
    refine (InvImage.wf r h).mono ?_
    intro s t hst
    exact twistedArrowExtensionPairing_ancestral_rank_lt i hi s t hst

end SerrePositivity.InfinityCategories
