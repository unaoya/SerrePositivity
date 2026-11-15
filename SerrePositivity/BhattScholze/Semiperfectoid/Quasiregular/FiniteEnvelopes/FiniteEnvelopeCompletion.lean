module

public import SerrePositivity.BhattScholze.Semiperfectoid.Lci.PDCompletionPrism
public import SerrePositivity.BhattScholze.Semiperfectoid.Quasiregular.FiniteEnvelopes.FiniteEnvelopeRawColimit

/-!
# 有限包絡の有界な実完備余極限

## 概要
生の包絡余極限の実完備化を全関係の有界包絡へ仕上げ、相対普遍性を示す。
## 方針
既存の環・加群・実完備化の普遍性と有限段の一意性を使い、単位を保つ比較を構成する。
## 規約
BS 著者版 Proposition 7.10。生の余極限と実完備化を区別し、零環を含む。
## 使われ方
S′ の有界包絡、全有界試験 prism への始性と Corollary 7.3 の比較。
-/

/-! ## FiniteEnvelopeCompletedUniversal -/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Prismatic
open _root_.CategoryTheory _root_.SerrePositivity.DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {p : ℕ} [Fact p.Prime] {A J B : Type u} [CommRing A] [CommRing B]
variable (P : OrientedPrism p A) (w : J → A)
variable (C : Finset J → CommRingCat.{u}) (Q : ∀ F, OrientedPrism p (C F))
variable (η : ∀ F, A →+* C F)
variable (hE : ∀ F, IsPrismaticEnvelope P P.deltaStructure (RingHom.id A)
  P.deltaStructure.isDeltaHom_id (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal P w F)
  (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal_generator P w F) (Q F) (η F))
local notation "L" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.FiniteEnvelopeRawColimit P w C Q η hE
local notation "D" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitDelta P w C Q η hE
local notation "b" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitBase P w C Q η hE
local notation "d" => b P.generator

/-- 概要：全関係をイデアルへ送る相対 δ 射は、実完備化した余極限から一意に延長。
方針：生の余極限と実 (p,d) 完備化の二つの一意性を順に使う。
規約：BS 著者版 Proposition 7.10。標的 prism には追加条件を課さない。
使われ方：S′ の完備包絡の始性。 -/
theorem _root_.SerrePositivity.BhattScholze.Semiperfectoid.existsUnique_finiteEnvelopeCompletedHom (Y : _root_.SerrePositivity.BhattScholze.OrientedPrism p B)
    (f : A →+* B) (hf : P.deltaStructure.IsDeltaHom Y.deltaStructure f)
    (hbase : P.ideal ≤ Y.ideal.comap f)
    (hmap : (P.ideal ⊔ Ideal.span (Set.range w)).map f ≤ Y.ideal) :
    letI := pdCompletionCommRing L p d
    ∃! g : PDCompletionH0 L p d →+* B,
      (_root_.SerrePositivity.BhattScholze.deltaPDCompletionStructure D d).IsDeltaHom Y.deltaStructure g ∧
        g.comp ((pdCompletionUnit L p d).comp b) = f := by
  letI := pdCompletionCommRing L p d
  obtain ⟨a, ha, hau⟩ := _root_.SerrePositivity.BhattScholze.Semiperfectoid.existsUnique_finiteEnvelopeRawColimitHom P w C Q η hE Y f hf hbase hmap
  have hd : (D).IsDistinguished d :=
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitBase_isDeltaHom P w C Q η hE).map_isDistinguished P.isDistinguished_generator
  have had : a d ∈ Y.ideal := by
    change (a.comp b) P.generator ∈ Y.ideal
    rw [ha.2]
    exact hbase (Ideal.subset_span (Set.mem_singleton _))
  obtain ⟨g, hg, hgu⟩ := _root_.SerrePositivity.BhattScholze.Semiperfectoid.existsUnique_pdCompletionPrismExtension D d hd Y a ha.1 had
  refine ⟨g, ⟨hg.1, ?_⟩, ?_⟩
  · rw [← RingHom.comp_assoc, hg.2, ha.2]
  · intro k hk
    apply hgu
    refine ⟨hk.1, ?_⟩
    apply hau
    refine ⟨hk.1.comp (_root_.SerrePositivity.BhattScholze.pdCompletionUnit_isDeltaHom D d), ?_⟩
    simpa only [RingHom.comp_assoc] using hk.2

end SerrePositivity.BhattScholze.Prismatic

end

/-! ## FiniteEnvelopeCompletion -/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Prismatic
open _root_.CategoryTheory _root_.SerrePositivity.DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {p : ℕ} [Fact p.Prime] {A J : Type u} [CommRing A]
variable (P : OrientedPrism p A) (w : J → A)
variable (C : Finset J → CommRingCat.{u}) (Q : ∀ F, OrientedPrism p (C F))
variable (η : ∀ F, A →+* C F)
variable (hE : ∀ F, IsPrismaticEnvelope P P.deltaStructure (RingHom.id A)
  P.deltaStructure.isDeltaHom_id (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal P w F)
  (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal_generator P w F) (Q F) (η F))
local notation "L" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.FiniteEnvelopeRawColimit P w C Q η hE
local notation "D" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitDelta P w C Q η hE
local notation "b" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitBase P w C Q η hE
local notation "d" => b P.generator

/-- 概要：有限包絡の実完備余極限は、全関係の有界な包絡。
方針：共通ねじれ指数で完備化後の正則性と有界性を得て、標的への一意延長を使う。
規約：BS 著者版 Proposition 7.10。N は全有限段に共通。
使われ方：S′ の完備包絡の実構成。 -/
theorem _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_boundedFiniteEnvelopeCompletion (N : ℕ)
    (hN : ∀ F n, ∀ x : C F ⧸ (Q F).ideal,
      (p : C F ⧸ (Q F).ideal) ^n * x = 0 → (p : C F ⧸ (Q F).ideal) ^N * x = 0) :
    letI := pdCompletionCommRing L p d
    ∃ V : _root_.SerrePositivity.BhattScholze.OrientedPrism p (PDCompletionH0 L p d),
      _root_.SerrePositivity.BhattScholze.Prismatic.IsBoundedPrism V ∧ _root_.SerrePositivity.BhattScholze.Prismatic.IsPrismaticEnvelope P P.deltaStructure (RingHom.id A)
        P.deltaStructure.isDeltaHom_id (P.ideal ⊔ Ideal.span (Set.range w))
        ((show P.ideal ≤ P.ideal ⊔ Ideal.span (Set.range w) from le_sup_left)
          (Ideal.subset_span (Set.mem_singleton _))) V ((pdCompletionUnit L p d).comp b) := by
  letI := pdCompletionCommRing L p d
  let H := PDCompletionH0 L p d
  let j := pdCompletionUnit L p d
  let φ := j.comp b
  have hb : ∃ M : ℕ, ∀ (n : ℕ) (x : L ⧸ Ideal.span {d}),
      (p : L ⧸ Ideal.span {d}) ^n * x = 0 → (p : L ⧸ Ideal.span {d}) ^M * x = 0 :=
    ⟨N, _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimit_residue_uniform_torsion_bound P w C Q η hE N hN⟩
  have hr := _root_.SerrePositivity.BhattScholze.Semiperfectoid.pdCompletion_generator_regular_of_bounded_quotient L p d
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimit_generator_mul_injective P w C Q η hE) hb
  have hd : (D).IsDistinguished d :=
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitBase_isDeltaHom P w C Q η hE).map_isDistinguished P.isDistinguished_generator
  obtain ⟨V, hδ, hv, hV⟩ := _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_boundedPrism_on_pdCompletion D d hd hr.1 hb
  have hφ : P.deltaStructure.IsDeltaHom V.deltaStructure φ := by
    rw [hδ]
    exact (_root_.SerrePositivity.BhattScholze.pdCompletionUnit_isDeltaHom D d).comp (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitBase_isDeltaHom P w C Q η hE)
  have hi : V.ideal = Ideal.span {φ P.generator} := by
    change Ideal.span {V.generator} = _
    rw [hv]
    rfl
  have hbase : P.ideal ≤ V.ideal.comap φ := by
    rw [_root_.SerrePositivity.BhattScholze.OrientedPrism.ideal, Ideal.span_singleton_le_iff_mem]
    change φ P.generator ∈ V.ideal
    rw [hi]
    exact Ideal.mem_span_singleton_self _
  have hmap : (P.ideal ⊔ Ideal.span (Set.range w)).map φ ≤ V.ideal := by
    apply Ideal.map_le_iff_le_comap.mpr
    apply sup_le hbase
    rw [Ideal.span_le]
    rintro _ ⟨x, rfl⟩
    classical
    let F : Finset J := {x}
    have hx : w x ∈ _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal P w F :=
      (show _root_.SerrePositivity.finiteRelationIdeal w F ≤ _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal P w F from le_sup_right)
        (Ideal.subset_span ⟨x, by simp [F], rfl⟩)
    have hxQ := (hE F).map_le (Ideal.mem_map_of_mem (η F) hx)
    have hxQ' : η F (w x) ∈ Ideal.span {η F P.generator} := by
      simpa only [(hE F).ideal_eq, RingHom.id_apply] using hxQ
    let ofF := _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitOf P w C Q η hE F
    have hxL := Ideal.mem_map_of_mem ofF hxQ'
    rw [Ideal.map_span, Set.image_singleton] at hxL
    have hF := _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitBase_eq_stage P w C Q η hE F
    have hdF : ofF (η F P.generator) = d := (RingHom.congr_fun hF P.generator).symm
    have hxF : ofF (η F (w x)) = b (w x) := (RingHom.congr_fun hF (w x)).symm
    rw [hdF, hxF] at hxL
    have hxH := Ideal.mem_map_of_mem j hxL
    rw [Ideal.map_span, Set.image_singleton] at hxH
    change φ (w x) ∈ V.ideal
    rw [hi]
    exact hxH
  refine ⟨V, hV, ⟨hφ, by simpa only [RingHom.comp_id] using hbase, hi, hmap, ?_⟩⟩
  intro B _ Y f hf hfb hfm
  rw [RingHom.comp_id] at hfb
  simpa only [hδ] using _root_.SerrePositivity.BhattScholze.Semiperfectoid.existsUnique_finiteEnvelopeCompletedHom P w C Q η hE Y f hf hfb hfm

end SerrePositivity.BhattScholze.Prismatic

end
