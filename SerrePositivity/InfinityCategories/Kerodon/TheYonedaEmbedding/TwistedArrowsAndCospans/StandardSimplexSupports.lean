module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseExtensionDomain
public import Mathlib.AlgebraicTopology.SimplicialSet.Nonsingular

/-!
概要：標準単体の全ての非退化単体を非空な有限頂点集合で表示する。
方針：Mathlib の次数ごとの頂点集合との同値を、次元を含む非退化単体の型へまとめる。
規約：宇宙の持ち上げは行わない。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、edgewise の頂点集合の pairing を単体へ移す。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：標準単体の非退化単体の頂点集合。
方針：次元を取り出し、その次数の Mathlib の頂点集合の同値を適用する。
規約：s は次元を含む型 N の要素。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、頂点集合の pairing と非退化単体の対応。 -/
noncomputable def stdSimplexNondegenerateSupport {n : ℕ} (s : (Δ[n] : SSet.{u}).N) :
    Finset (Fin (n + 1)) :=
  (stdSimplex.nonDegenerateEquiv' ⟨s.simplex, s.nonDegenerate⟩).val

/-- 概要：非退化単体の頂点集合の濃度は次元に一を加えたもの。
方針：次数ごとの同値の標的の部分型の条件を使う。
規約：退化単体には主張しない。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、頂点の挿入による余次元一の確認。 -/
lemma stdSimplexNondegenerateSupport_card {n : ℕ} (s : (Δ[n] : SSet.{u}).N) :
    (stdSimplexNondegenerateSupport s).card = s.dim + 1 :=
  (stdSimplex.nonDegenerateEquiv' ⟨s.simplex, s.nonDegenerate⟩).property

/-- 概要：非退化単体の頂点集合は非空。
方針：濃度が正であることを次元の式から示す。
規約：零次元の単体も含む。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、非空な頂点集合の型への移送。 -/
lemma stdSimplexNondegenerateSupport_nonempty {n : ℕ} (s : (Δ[n] : SSet.{u}).N) :
    (stdSimplexNondegenerateSupport s).Nonempty := by
  rw [← Finset.card_pos, stdSimplexNondegenerateSupport_card]
  omega

/-- 概要：標準単体の非退化単体は頂点集合によって一意に決まる。
方針：濃度から次元を揃え、次数ごとの同値の単射性を使う。
規約：異なる次元の単体も比較できる。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、pairing の型の相異性と一意性の移送。 -/
lemma stdSimplexNondegenerateSupport_injective (n : ℕ) :
    Function.Injective (stdSimplexNondegenerateSupport.{u} (n := n)) := by
  intro s t h
  obtain ⟨d, x, rfl⟩ := s.mk_surjective
  obtain ⟨e, y, rfl⟩ := t.mk_surjective
  have hcard := congrArg Finset.card h
  rw [stdSimplexNondegenerateSupport_card, stdSimplexNondegenerateSupport_card] at hcard
  change d + 1 = e + 1 at hcard
  have hd : d = e := by omega
  subst e
  have hxy : x = y := stdSimplex.nonDegenerateEquiv'.injective (Subtype.ext h)
  subst y
  rfl

/-- 概要：標準単体の全非退化単体と非空な有限頂点集合の全単射。
方針：単射性には頂点集合の一意性を使い、逆方向には濃度から次元を定める。
規約：次元は頂点数から一を引いたもの。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、有限集合の対を単体的 pairing にするための同値。 -/
noncomputable def stdSimplexNondegenerateSupportEquiv (n : ℕ) :
    (Δ[n] : SSet.{u}).N ≃ {S : Finset (Fin (n + 1)) // S.Nonempty} :=
  Equiv.ofBijective (fun s ↦ ⟨stdSimplexNondegenerateSupport s,
    stdSimplexNondegenerateSupport_nonempty s⟩) (by
      constructor
      · intro s t h
        exact stdSimplexNondegenerateSupport_injective n (congrArg Subtype.val h)
      · intro S
        let d := S.val.card - 1
        have hc : S.val.card = d + 1 := by
          have hp := Finset.card_pos.mpr S.property
          dsimp [d]
          omega
        let x : (Δ[n] : SSet.{u}).nonDegenerate d :=
          stdSimplex.nonDegenerateEquiv'.symm ⟨S.val, hc⟩
        refine ⟨SSet.N.mk x.val x.property, ?_⟩
        apply Subtype.ext
        change (stdSimplex.nonDegenerateEquiv' x).val = S.val
        exact congrArg Subtype.val (stdSimplex.nonDegenerateEquiv'.apply_symm_apply ⟨S.val, hc⟩))

/-- 概要：標準単体の非退化単体の面関係は頂点集合の包含と一致する。
方針：各単体が生成する部分複体を頂点集合の面と同定し、面の順序埋め込みを使う。
規約：s≤t は s が t の任意の余次元の面であること。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、頂点集合の順位の減少を単体の面関係へ移す。 -/
lemma stdSimplexNondegenerateSupport_subset_iff {n : ℕ} (s t : (Δ[n] : SSet.{u}).N) :
    stdSimplexNondegenerateSupport s ⊆ stdSimplexNondegenerateSupport t ↔ s ≤ t := by
  rw [← stdSimplex.face_le_face_iff]
  change stdSimplex.face (stdSimplex.nonDegenerateEquiv' ⟨s.simplex, s.nonDegenerate⟩).val ≤
    stdSimplex.face (stdSimplex.nonDegenerateEquiv' ⟨t.simplex, t.nonDegenerate⟩).val ↔ _
  rw [stdSimplex.face_nonDegenerateEquiv', stdSimplex.face_nonDegenerateEquiv']
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
