module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseSimplexPairing

/-!
概要：edgewise の pairing の各対は一意な余次元一の面になる。
方針：頂点の挿入による包含と濃度の増加を確認し、非特異な単体集合の面の一意性を使う。
規約：標準単体は非特異なので同じ面を異なる番号で取ることはない。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、ホーンを接合する pairing の proper 性。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：非特異な単体集合で次元差一の非退化な面は一意な余次元一の面。
方針：面を取る単射を選び、標的の非退化単体の Yoneda 射の単射性で一意性を示す。
規約：両方の非退化単体は型 N で指定する。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、頂点集合の対からホーンの欠ける面の一意性を得る。 -/
lemma uniquelyCodimOneFace_of_nonsingular_le {X : SSet.{u}} [X.Nonsingular]
    (x y : X.N) (hxy : x ≤ y) (hd : y.dim = x.dim + 1) :
    x.toS.IsUniquelyCodimOneFace y.toS := by
  refine ⟨hd, ?_⟩
  obtain ⟨f, hf, hfx⟩ := SSet.N.le_iff_exists_mono.mp hxy
  refine ⟨f, ⟨hf, hfx⟩, ?_⟩
  intro g hg
  exact SSet.Nonsingular.injective_map y.simplex y.nonDegenerate (hg.2.trans hfx.symm)

/-- 概要：pairing の小さい非退化単体は大きい方の面。
方針：頂点集合の像が一頂点の挿入である式から包含を得る。
規約：面の余次元はこの補題ではまだ指定しない。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、pairing の proper 性の面の条件。 -/
lemma edgewiseExtensionPairing_le (n : ℕ) (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseExtensionPairing.{u} n).II) :
    s.val ≤ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseExtensionPairing n).p s).val := by
  apply (Subcomplex.N.le_iff).2
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport_subset_iff _ _).1
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseExtensionPairing_support]
  exact Finset.subset_insert _ _

/-- 概要：pairing の大きい非退化単体の次元は小さい方より一つ大きい。
方針：存在しない右頂点を挿入する濃度の式と、非退化単体の頂点数の式を使う。
規約：型 II の不在条件により挿入は真に新しい頂点を加える。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、対の余次元一の条件。 -/
lemma edgewiseExtensionPairing_dim (n : ℕ) (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseExtensionPairing.{u} n).II) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseExtensionPairing n).p s).val.dim = s.val.dim + 1 := by
  have h := congrArg Finset.card (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseExtensionPairing_support n s)
  have hs := s.property
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSupportPivot
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport s.val.toN)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseOutsideSimplexEquiv n s.val).property) ∉
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport s.val.toN at hs
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport_card] at h
  erw [Finset.card_insert_of_notMem hs] at h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport_card] at h
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseExtensionPairing n).p s).val.dim + 1 = s.val.dim + 1 + 1 at h
  omega

/-- 概要：edgewise の非退化単体の pairing は proper。
方針：面の包含、次元差一、標準単体の非特異性を組み合わせる。
規約：この段階では正則性の well-founded 条件とは区別する。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、ホーン接合の正則 pairing の一方の条件。 -/
instance edgewiseExtensionPairing_isProper (n : ℕ) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseExtensionPairing.{u} n).IsProper where
  isUniquelyCodimOneFace s := uniquelyCodimOneFace_of_nonsingular_le s.val.toN
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseExtensionPairing n).p s).val.toN
    (edgewiseExtensionPairing_le n s) (edgewiseExtensionPairing_dim n s)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
