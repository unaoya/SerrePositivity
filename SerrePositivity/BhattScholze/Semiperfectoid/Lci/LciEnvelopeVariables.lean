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
BS 著者版 Example 7.9。分類基底は明示する（D4-02）。

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
abbrev lciRelationIdeal : Ideal A := P.ideal ⊔ Ideal.span (Set.range f)

/-- 概要：指定の関係を分類する完備自由 δ 射は一意に存在する。
方針：完備自由 δ 環の普遍性に基底射と変数の像を与える。
規約：BS 著者版 Example 7.9 の分類射。係数射は向きを保つ。
使われ方：変数包絡を関係の族に特殊化する。 -/
theorem existsUnique_lciClassifier (g : OrientedPrism.Hom P₀ P)
    (hd : g.toRingHom P₀.generator = P.generator) :
    ∃! c : completedFreeDelta P₀ S →+* A,
      (completedFreeDeltaStructure P₀ S).IsDeltaHom P.deltaStructure c ∧
      c.comp (completedFreeDeltaBase P₀ S) = g.toRingHom ∧
      ∀ s, c (completedFreeDeltaVariable P₀ S s) = f s :=
  existsUnique_completedFreeDeltaHom P₀ S P.deltaStructure g.toRingHom
    g.map_delta P.complete_p (hd ▸ P.complete_generator) f

/-- 概要：分類射で変数イデアルは向きと指定した関係のイデアルへ写る。
方針：生成元の像を計算する。
規約：全初期変数に沿う変数包絡。
使われ方：BS 著者版 Example 7.9 の特殊化。 -/
theorem variableIdeal_map_lciRelationIdeal (c : completedFreeDelta P₀ S →+* A)
    (hd : c (completedFreeDeltaBase P₀ S P₀.generator) = P.generator)
    (hf : ∀ s, c (completedFreeDeltaVariable P₀ S s) = f s) :
    (variableIdeal P₀ S Set.univ).map c = lciRelationIdeal P f := by
  rw [variableIdeal, Ideal.map_span]
  change Ideal.span _ = Ideal.span {P.generator} ⊔ Ideal.span (Set.range f)
  rw [← Ideal.span_union]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with rfl | ⟨s, rfl⟩
    · exact Or.inl (Set.mem_singleton_iff.mpr hd)
    · change c (completedFreeDeltaVariable P₀ S s) ∈ {P.generator} ∪ Set.range f
      rw [hf]
      exact Or.inr ⟨s, rfl⟩
  · rintro (hx | ⟨s, rfl⟩)
    · obtain rfl := Set.mem_singleton_iff.mp hx
      exact ⟨_, Set.mem_insert _ _, hd⟩
    · exact ⟨completedFreeDeltaVariable P₀ S s,
        Set.mem_insert_of_mem _ ⟨⟨s, Set.mem_univ _⟩, rfl⟩, hf s⟩

/-- 基底 prism の関係イデアルの包絡という性質。 -/
abbrev IsLciRelationEnvelope {B : Type u} [CommRing B] (Q : OrientedPrism p B) (η : A →+* B) :=
  IsPrismaticEnvelope P P.deltaStructure (RingHom.id A) P.deltaStructure.isDeltaHom_id
    (lciRelationIdeal P f)
    (show P.generator ∈ lciRelationIdeal P f from
      (show P.ideal ≤ P.ideal ⊔ Ideal.span (Set.range f) from le_sup_left)
        (Ideal.subset_span (Set.mem_singleton _))) Q η

/-- 概要：自由変数包絡の完備底変換は、正則性の仮定の下で関係の包絡となる。
方針：イデアルの像を計算し、完備テンソル積の普遍性を適用する。
規約：BS 著者版 Example 7.9 の環の段階。テンソル積では基底を左に並べる。
使われ方：関係列の台環の正則性を包絡の存在へつなぐ。 -/
theorem exists_lciRelationEnvelope_of_regular (hP₀ : IsBoundedPrism P₀)
    (g : OrientedPrism.Hom P₀ P) (hd : g.toRingHom P₀.generator = P.generator)
    (c : completedFreeDelta P₀ S →+* A)
    (hc : (completedFreeDeltaStructure P₀ S).IsDeltaHom P.deltaStructure c)
    (hg : c.comp (completedFreeDeltaBase P₀ S) = g.toRingHom)
    (hf : ∀ s, c (completedFreeDeltaVariable P₀ S s) = f s)
    (hreg : letI := c.toAlgebra
      letI := (variableEnvelopeSubstitution P₀ S Set.univ).toAlgebra
      IsRegular ((prismCompletedTensorLeft (A := completedFreeDelta P₀ S)
        (C := completedFreeDelta P₀ S) P) P.generator)) :
    letI := c.toAlgebra
    letI := (variableEnvelopeSubstitution P₀ S Set.univ).toAlgebra
    ∃ Q : OrientedPrism p
        (PrismCompletedTensor (A := completedFreeDelta P₀ S) (C := completedFreeDelta P₀ S) P),
      IsLciRelationEnvelope P f Q (prismCompletedTensorLeft P) := by
  let η := variableEnvelopeSubstitution P₀ S Set.univ
  let := c.toAlgebra
  let := η.toAlgebra
  let Q := completedFreeDeltaPrism P₀ S (completedFreeDelta_generator_regular P₀ hP₀ S)
  have hE := isPrismaticEnvelope_variableSubstitution P₀ S Set.univ
    (completedFreeDelta_generator_regular P₀ hP₀ S)
  obtain ⟨T, _, hT⟩ := exists_envelope_of_classified_ideal_of_regular P₀ P
    (completedFreeDeltaStructure P₀ S) (completedFreeDeltaBase P₀ S)
    (completedFreeDeltaBase_isDeltaHom P₀ S) (variableIdeal P₀ S Set.univ)
    (Ideal.subset_span (Set.mem_insert _ _)) Q η hE c hc g hg hd hreg
  have hi := variableIdeal_map_lciRelationIdeal P₀ P f c
    ((RingHom.congr_fun hg _).trans hd) hf
  refine ⟨T, ?_⟩
  simpa only [IsLciRelationEnvelope, hi] using hT

end SerrePositivity.BhattScholze.Prismatic
