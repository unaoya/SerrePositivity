module

public import SerrePositivity.BhattScholze.Semiperfectoid.Lci.LciEnvelope
public import SerrePositivity.BhattScholze.Prismatic.Envelopes.CompletedFreeDeltaFlat

/-!
# 関係列による自由変数包絡の特殊化

## 概要
分類射により自由変数の包絡を指定した関係の族へ特殊化する。

## 方針
延長イデアルの生成元を計算して完備テンソル積の普遍性を適用する。

## 規約
BS 著者版 Example 7.9。分類基底は明示する。

## 使われ方
Koszul 正則な関係列に対する台環の計算と包絡の普遍性をつなぐ。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime] {A₀ A : Type u} [CommRing A₀] [CommRing A]
variable (P₀ : OrientedPrism p A₀) (P : OrientedPrism p A)
variable {S : Type u} (f : S → A)

/-- 基底の向きと指定の関係が生成するイデアル。 -/
abbrev _root_.SerrePositivity.BhattScholze.Semiperfectoid.lciRelationIdeal : Ideal A := P.ideal ⊔ Ideal.span (Set.range f)

/-- 概要：指定の関係を分類する完備自由 δ 射は一意に存在する。
方針：完備自由 δ 環の普遍性に基底射と変数の像を与える。
規約：BS 著者版 Example 7.9 の分類射。係数射は向きを保つ。
使われ方：変数包絡を関係の族に特殊化する。 -/
theorem _root_.SerrePositivity.BhattScholze.Semiperfectoid.existsUnique_lciClassifier (g : _root_.SerrePositivity.BhattScholze.OrientedPrism.Hom P₀ P)
    (hd : g.toRingHom P₀.generator = P.generator) :
    ∃! c : _root_.SerrePositivity.BhattScholze.Prismatic.completedFreeDelta P₀ S →+* A,
      (_root_.SerrePositivity.BhattScholze.Prismatic.completedFreeDeltaStructure P₀ S).IsDeltaHom P.deltaStructure c ∧
      c.comp (_root_.SerrePositivity.BhattScholze.Prismatic.completedFreeDeltaBase P₀ S) = g.toRingHom ∧
      ∀ s, c (_root_.SerrePositivity.BhattScholze.Prismatic.completedFreeDeltaVariable P₀ S s) = f s :=
  _root_.SerrePositivity.BhattScholze.Prismatic.existsUnique_completedFreeDeltaHom P₀ S P.deltaStructure g.toRingHom
    g.map_delta P.complete_p (hd ▸ P.complete_generator) f

/-- 概要：分類射で変数イデアルは向きと指定した関係のイデアルへ写る。
方針：生成元の像を計算する。
規約：全初期変数に沿う変数包絡。
使われ方：BS 著者版 Example 7.9 の特殊化。 -/
theorem _root_.SerrePositivity.BhattScholze.Semiperfectoid.variableIdeal_map_lciRelationIdeal (c : _root_.SerrePositivity.BhattScholze.Prismatic.completedFreeDelta P₀ S →+* A)
    (hd : c (_root_.SerrePositivity.BhattScholze.Prismatic.completedFreeDeltaBase P₀ S P₀.generator) = P.generator)
    (hf : ∀ s, c (_root_.SerrePositivity.BhattScholze.Prismatic.completedFreeDeltaVariable P₀ S s) = f s) :
    (_root_.SerrePositivity.BhattScholze.Prismatic.variableIdeal P₀ S Set.univ).map c = _root_.SerrePositivity.BhattScholze.Semiperfectoid.lciRelationIdeal P f := by
  rw [_root_.SerrePositivity.BhattScholze.Prismatic.variableIdeal, Ideal.map_span]
  change Ideal.span _ = Ideal.span {P.generator} ⊔ Ideal.span (Set.range f)
  rw [← Ideal.span_union]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with rfl | ⟨s, rfl⟩
    · exact Or.inl (Set.mem_singleton_iff.mpr hd)
    · change c (_root_.SerrePositivity.BhattScholze.Prismatic.completedFreeDeltaVariable P₀ S s) ∈ {P.generator} ∪ Set.range f
      rw [hf]
      exact Or.inr ⟨s, rfl⟩
  · rintro (hx | ⟨s, rfl⟩)
    · obtain rfl := Set.mem_singleton_iff.mp hx
      exact ⟨_, Set.mem_insert _ _, hd⟩
    · exact ⟨_root_.SerrePositivity.BhattScholze.Prismatic.completedFreeDeltaVariable P₀ S s,
        Set.mem_insert_of_mem _ ⟨⟨s, Set.mem_univ _⟩, rfl⟩, hf s⟩

/-- 基底 prism の関係イデアルの包絡という性質。 -/
abbrev _root_.SerrePositivity.BhattScholze.Semiperfectoid.IsLciRelationEnvelope {B : Type u} [CommRing B] (Q : _root_.SerrePositivity.BhattScholze.OrientedPrism p B) (η : A →+* B) :=
  _root_.SerrePositivity.BhattScholze.Prismatic.IsPrismaticEnvelope P P.deltaStructure (RingHom.id A) P.deltaStructure.isDeltaHom_id
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.lciRelationIdeal P f)
    (show P.generator ∈ _root_.SerrePositivity.BhattScholze.Semiperfectoid.lciRelationIdeal P f from
      (show P.ideal ≤ P.ideal ⊔ Ideal.span (Set.range f) from le_sup_left)
        (Ideal.subset_span (Set.mem_singleton _))) Q η

/-- 概要：自由変数包絡の完備底変換は、正則性の仮定の下で関係の包絡となる。
方針：イデアルの像を計算し、完備テンソル積の普遍性を適用する。
規約：BS 著者版 Example 7.9 の環の段階。テンソル積では基底を左に並べる。
使われ方：関係列の台環の正則性を包絡の存在へつなぐ。 -/
theorem _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_lciRelationEnvelope_of_regular (hP₀ : _root_.SerrePositivity.BhattScholze.Prismatic.IsBoundedPrism P₀)
    (g : _root_.SerrePositivity.BhattScholze.OrientedPrism.Hom P₀ P) (hd : g.toRingHom P₀.generator = P.generator)
    (c : _root_.SerrePositivity.BhattScholze.Prismatic.completedFreeDelta P₀ S →+* A)
    (hc : (_root_.SerrePositivity.BhattScholze.Prismatic.completedFreeDeltaStructure P₀ S).IsDeltaHom P.deltaStructure c)
    (hg : c.comp (_root_.SerrePositivity.BhattScholze.Prismatic.completedFreeDeltaBase P₀ S) = g.toRingHom)
    (hf : ∀ s, c (_root_.SerrePositivity.BhattScholze.Prismatic.completedFreeDeltaVariable P₀ S s) = f s)
    (hreg : letI := c.toAlgebra
      letI := (_root_.SerrePositivity.BhattScholze.Prismatic.variableEnvelopeSubstitution P₀ S Set.univ).toAlgebra
      IsRegular ((_root_.SerrePositivity.BhattScholze.prismCompletedTensorLeft (A := _root_.SerrePositivity.BhattScholze.Prismatic.completedFreeDelta P₀ S)
        (C := _root_.SerrePositivity.BhattScholze.Prismatic.completedFreeDelta P₀ S) P) P.generator)) :
    letI := c.toAlgebra
    letI := (_root_.SerrePositivity.BhattScholze.Prismatic.variableEnvelopeSubstitution P₀ S Set.univ).toAlgebra
    ∃ Q : _root_.SerrePositivity.BhattScholze.OrientedPrism p
        (_root_.SerrePositivity.BhattScholze.PrismCompletedTensor (A := _root_.SerrePositivity.BhattScholze.Prismatic.completedFreeDelta P₀ S) (C := _root_.SerrePositivity.BhattScholze.Prismatic.completedFreeDelta P₀ S) P),
      _root_.SerrePositivity.BhattScholze.Semiperfectoid.IsLciRelationEnvelope P f Q (_root_.SerrePositivity.BhattScholze.prismCompletedTensorLeft P) := by
  let η := _root_.SerrePositivity.BhattScholze.Prismatic.variableEnvelopeSubstitution P₀ S Set.univ
  let := c.toAlgebra
  let := η.toAlgebra
  let Q := _root_.SerrePositivity.BhattScholze.Prismatic.completedFreeDeltaPrism P₀ S (_root_.SerrePositivity.BhattScholze.Prismatic.completedFreeDelta_generator_regular P₀ hP₀ S)
  have hE := _root_.SerrePositivity.BhattScholze.Prismatic.isPrismaticEnvelope_variableSubstitution P₀ S Set.univ
    (_root_.SerrePositivity.BhattScholze.Prismatic.completedFreeDelta_generator_regular P₀ hP₀ S)
  obtain ⟨T, _, hT⟩ := _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_envelope_of_classified_ideal_of_regular P₀ P
    (_root_.SerrePositivity.BhattScholze.Prismatic.completedFreeDeltaStructure P₀ S) (_root_.SerrePositivity.BhattScholze.Prismatic.completedFreeDeltaBase P₀ S)
    (_root_.SerrePositivity.BhattScholze.Prismatic.completedFreeDeltaBase_isDeltaHom P₀ S) (_root_.SerrePositivity.BhattScholze.Prismatic.variableIdeal P₀ S Set.univ)
    (Ideal.subset_span (Set.mem_insert _ _)) Q η hE c hc g hg hd hreg
  have hi := _root_.SerrePositivity.BhattScholze.Semiperfectoid.variableIdeal_map_lciRelationIdeal P₀ P f c
    ((RingHom.congr_fun hg _).trans hd) hf
  refine ⟨T, ?_⟩
  simpa only [_root_.SerrePositivity.BhattScholze.Semiperfectoid.IsLciRelationEnvelope, hi] using hT

end SerrePositivity.BhattScholze.Prismatic
