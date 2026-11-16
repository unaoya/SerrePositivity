module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Data.Fintype.EquivFin
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaColimit
public import SerrePositivity.BhattScholze.Prismatic.Envelopes.Envelope
public import SerrePositivity.BhattScholze.Semiperfectoid.Lci.LciEnvelopeFaithful
public import SerrePositivity.CommutativeAlgebra.DirectLimitRelations

/-!
# 固定基底上の有限包絡の図式

## 概要
K5 から有限段を作り、包絡の一意性による遷移と生の δ 環余極限を組み立てる。
## 方針
既存の環・加群・実完備化の普遍性と有限段の一意性を使い、単位を保つ比較を構成する。
## 規約
BS 著者版 Proposition 7.10。生の余極限と実完備化を区別し、零環を含む。
## 使われ方
S′ の有界包絡、全有界試験 prism への始性と Corollary 7.3 の比較。
-/

/-! ## EnvelopeTransition -/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Prismatic
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {P : OrientedPrism p A}
variable {B : Type u} [CommRing B] {D : DeltaStructure p B}
variable {ι : A →+* B} {hι : P.deltaStructure.IsDeltaHom D ι}
variable {I J K : Ideal B} {hI : ι P.generator ∈ I} {hJ : ι P.generator ∈ J} {hK : ι P.generator ∈ K}
variable {C E F : Type u} [CommRing C] [CommRing E] [CommRing F]
variable {Q : OrientedPrism p C} {V : OrientedPrism p E} {W : OrientedPrism p F}
variable {η : B →+* C} {ν : B →+* E} {ω : B →+* F}
variable (hQ : IsPrismaticEnvelope P D ι hι I hI Q η)
variable (hV : IsPrismaticEnvelope P D ι hι J hJ V ν)
variable (hW : IsPrismaticEnvelope P D ι hι K hK W ω)

include hQ hV

/-- 概要：関係の包含から包絡の間の単位を保つ一意な prism 射がある。
方針：標的包絡の関係を使い、源包絡の一意延長を適用する。
規約：BS 著者版 Proposition 3.13。相対基底射と δ 構造を保存。
使われ方：S′ の有限包絡の遷移。 -/
theorem IsPrismaticEnvelope.existsUnique_transition (h : I ≤ J) :
    ∃! f : OrientedPrism.Hom Q V, f.toRingHom.comp η = ν := by
  obtain ⟨f, hf, hfu⟩ := hQ.lift V ν hV.isDeltaHom hV.base_hom
    ((Ideal.map_mono h).trans hV.map_le)
  let g : OrientedPrism.Hom Q V := ⟨f, hf.1, by
    rw [hQ.ideal_eq, Ideal.span_singleton_le_iff_mem]
    change (f.comp η) (ι P.generator) ∈ V.ideal
    rw [hf.2]
    exact hV.map_le (Ideal.mem_map_of_mem ν (h hI))⟩
  refine ⟨g, hf.2, ?_⟩
  intro k hk
  apply OrientedPrism.Hom.ext
  exact hfu k.toRingHom ⟨k.map_delta, hk⟩

/-- 関係の包含による標準遷移射。 -/
def IsPrismaticEnvelope.transition (h : I ≤ J) : OrientedPrism.Hom Q V :=
  (hQ.existsUnique_transition hV h).choose

/-- 標準遷移射は基底からの単位を保つ。 -/
theorem IsPrismaticEnvelope.transition_comp (h : I ≤ J) :
    (hQ.transition hV h).toRingHom.comp η = ν :=
  (hQ.existsUnique_transition hV h).choose_spec.1

omit hV in
/-- 同じ包絡への標準遷移は恒等射。 -/
theorem IsPrismaticEnvelope.transition_self : hQ.transition hQ le_rfl = OrientedPrism.Hom.id Q := by
  apply (hQ.existsUnique_transition hQ le_rfl).unique
  · exact hQ.transition_comp hQ le_rfl
  · exact RingHom.id_comp η

include hW

/-- 標準遷移射は関係イデアルの包含の合成を保つ。 -/
theorem IsPrismaticEnvelope.transition_trans (h : I ≤ J) (k : J ≤ K) :
    (hV.transition hW k).comp (hQ.transition hV h) = hQ.transition hW (h.trans k) := by
  apply (hQ.existsUnique_transition hW (h.trans k)).unique
  · change ((hV.transition hW k).toRingHom.comp (hQ.transition hV h).toRingHom).comp η = ω
    rw [RingHom.comp_assoc, hQ.transition_comp hV h, hV.transition_comp hW k]
  · exact hQ.transition_comp hW (h.trans k)

end SerrePositivity.BhattScholze.Prismatic

end

/-! ## FiniteEnvelopeDiagram -/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Prismatic
open _root_.CategoryTheory
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {A J : Type u} [CommRing A]
variable (P : OrientedPrism p A) (w : J → A)

/-- 向きのイデアルと有限個の関係を合わせたイデアル。 -/
def _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal (F : Finset J) : Ideal A := P.ideal ⊔ _root_.SerrePositivity.finiteRelationIdeal w F

/-- 向きの生成元は各有限段の関係イデアルに属する。 -/
theorem _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal_generator (F : Finset J) : P.generator ∈ _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal P w F :=
  (show P.ideal ≤ _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal P w F from le_sup_left)
    (Ideal.subset_span (Set.mem_singleton _))

/-- 有限段の関係イデアルは部分族について単調。 -/
theorem _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal_mono {F G : Finset J} (h : F ⊆ G) :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal P w F ≤ _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal P w G :=
  sup_le_sup_left (_root_.SerrePositivity.finiteRelationIdeal_mono w h) _

variable (C : Finset J → CommRingCat.{u}) (Q : ∀ F, OrientedPrism p (C F))
variable (η : ∀ F, A →+* C F)
variable (hE : ∀ F, IsPrismaticEnvelope P P.deltaStructure (RingHom.id A)
  P.deltaStructure.isDeltaHom_id (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal P w F)
  (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal_generator P w F) (Q F) (η F))

/-- 有限部分族間の、一意な単位を保つ prism 遷移射。 -/
def _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeTransition {F G : Finset J} (h : F ⊆ G) : _root_.SerrePositivity.BhattScholze.OrientedPrism.Hom (Q F) (Q G) :=
  (hE F).transition (hE G) (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal_mono P w h)

include hE

/-- 遷移射は固定基底上の係数射を保つ。 -/
theorem _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeTransition_base {F G : Finset J} (h : F ⊆ G) :
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeTransition P w C Q η hE h).toRingHom.comp (η F) = η G :=
  (hE F).transition_comp (hE G) (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal_mono P w h)

/-- 同じ有限段への遷移は恒等射。 -/
theorem _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeTransition_self (F : Finset J) :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeTransition P w C Q η hE (show F ⊆ F from le_rfl) = _root_.SerrePositivity.BhattScholze.OrientedPrism.Hom.id (Q F) :=
  (hE F).transition_self

/-- 有限包絡の遷移は部分族の包含の合成を保つ。 -/
theorem _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeTransition_trans {F G H : Finset J} (h : F ⊆ G) (k : G ⊆ H) :
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeTransition P w C Q η hE k).comp (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeTransition P w C Q η hE h) =
      _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeTransition P w C Q η hE (h.trans k) :=
  (hE F).transition_trans (hE G) (hE H)
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal_mono P w h) (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal_mono P w k)

/-- 有限包絡の台環は Mathlib の有向系を成す。 -/
instance _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeDirectedSystem :
    DirectedSystem (fun F => C F)
      (fun _ _ h => (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeTransition P w C Q η hE h).toRingHom) where
  map_self {i} x := by rw [_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeTransition_self]; rfl
  map_map {k j i} h k' x :=
    RingHom.congr_fun (congrArg _root_.SerrePositivity.BhattScholze.OrientedPrism.Hom.toRingHom
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeTransition_trans P w C Q η hE h k')) x

/-- 有限包絡の生の環余極限。 -/
abbrev _root_.SerrePositivity.BhattScholze.Semiperfectoid.FiniteEnvelopeRawColimit := Ring.DirectLimit (fun F => C F)
  (fun _ _ h => (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeTransition P w C Q η hE h).toRingHom)

/-- 生の余極限に備わる標準 δ 構造。 -/
def _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitDelta : _root_.SerrePositivity.BhattScholze.DeltaStructure p (_root_.SerrePositivity.BhattScholze.Semiperfectoid.FiniteEnvelopeRawColimit P w C Q η hE) :=
  _root_.SerrePositivity.BhattScholze.deltaDirectLimitStructure (fun F => C F)
    (fun _ _ h => (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeTransition P w C Q η hE h).toRingHom)
    (fun F => (Q F).deltaStructure)
    (fun _ _ h => (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeTransition P w C Q η hE h).map_delta)

/-- 各有限包絡から生の環余極限への射。 -/
def _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitOf (F : Finset J) : C F →+* _root_.SerrePositivity.BhattScholze.Semiperfectoid.FiniteEnvelopeRawColimit P w C Q η hE :=
  Ring.DirectLimit.of (fun F => C F)
    (fun _ _ h => (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeTransition P w C Q η hE h).toRingHom) F

/-- 各段からの標準射は δ 射。 -/
theorem _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitOf_isDeltaHom (F : Finset J) :
    (Q F).deltaStructure.IsDeltaHom (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitDelta P w C Q η hE)
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitOf P w C Q η hE F) :=
  _root_.SerrePositivity.BhattScholze.deltaDirectLimitOf_isDeltaHom (fun F => C F)
    (fun _ _ h => (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeTransition P w C Q η hE h).toRingHom)
    (fun F => (Q F).deltaStructure)
    (fun _ _ h => (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeTransition P w C Q η hE h).map_delta) F

/-- 生の包絡余極限への係数射は空関係の段から定める。 -/
def _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitBase : A →+* _root_.SerrePositivity.BhattScholze.Semiperfectoid.FiniteEnvelopeRawColimit P w C Q η hE :=
  (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitOf P w C Q η hE ∅).comp (η ∅)

/-- 生の余極限への係数射はどの有限段でも同じ。 -/
theorem _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitBase_eq_stage (F : Finset J) :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitBase P w C Q η hE =
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitOf P w C Q η hE F).comp (η F) := by
  apply RingHom.ext
  intro x
  have h := Ring.DirectLimit.of_f (G := fun F => C F)
    (f := fun _ _ h => (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeTransition P w C Q η hE h).toRingHom)
    (Finset.empty_subset F) (η ∅ x)
  have he := RingHom.congr_fun (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeTransition_base P w C Q η hE (Finset.empty_subset F)) x
  exact h.symm.trans (congrArg (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitOf P w C Q η hE F) he)

/-- 生の包絡余極限への係数射は δ 構造を保つ。 -/
theorem _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitBase_isDeltaHom :
    P.deltaStructure.IsDeltaHom (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitDelta P w C Q η hE)
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitBase P w C Q η hE) :=
  (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitOf_isDeltaHom P w C Q η hE ∅).comp (hE ∅).isDeltaHom

end SerrePositivity.BhattScholze.Prismatic

end

/-! ## FiniteEnvelopeExistence -/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Prismatic
open _root_.CategoryTheory
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {A J : Type u} [CommRing A]
variable (P : OrientedPrism p A) (w : J → A)

/-- 有限部分集合の添字を Fin に並べる同値。 -/
def _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeEnumeration (F : Finset J) : Fin (Fintype.card F) ≃ F :=
  (Fintype.equivFin F).symm

/-- Fin に並べた有限部分族の関係列。 -/
def _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRelations (F : Finset J) : Fin (Fintype.card F) → A :=
  fun i => w (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeEnumeration F i)

/-- 並べた関係列の生成イデアルは、有限部分族の関係イデアル。 -/
theorem _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRelations_ideal (F : Finset J) :
    Ideal.span (Set.range (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRelations w F)) = _root_.SerrePositivity.finiteRelationIdeal w F := by
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeEnumeration F i, (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeEnumeration F i).property, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨(_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeEnumeration F).symm ⟨j, hj⟩,
      congrArg (fun y : F => w y) ((_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeEnumeration F).apply_symm_apply ⟨j, hj⟩)⟩

/-- 概要：全有限部分族に対する有界な実包絡と忠実平坦な剰余単位が存在。
方針：有限列の K5 を適用し、生成イデアルの比較で同じ固定基底上へそろえる。
規約：BS 著者版 Example 7.9・Proposition 7.10。正則性と有界ねじれのみを入力する。
使われ方：有限包絡の遷移射と完備余極限の構成。 -/
theorem _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_finiteEnvelopeDiagram
    (hreg : ∀ F : Finset J, _root_.SerrePositivity.IsKoszulResolution
      (fun i => Ideal.Quotient.mk P.ideal (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRelations w F i)))
    (hbound : ∀ F : Finset J, ∃ N : ℕ, ∀ (n : ℕ) (x : A ⧸ _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal P w F),
      (p : A ⧸ _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal P w F) ^n * x = 0 →
        (p : A ⧸ _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal P w F) ^N * x = 0) :
    ∃ (C : Finset J → CommRingCat.{u}) (Q : ∀ F, _root_.SerrePositivity.BhattScholze.OrientedPrism p (C F))
      (η : ∀ F, A →+* C F),
      ∀ F, ∃ hE : _root_.SerrePositivity.BhattScholze.Prismatic.IsPrismaticEnvelope P P.deltaStructure (RingHom.id A)
        P.deltaStructure.isDeltaHom_id (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal P w F)
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal_generator P w F) (Q F) (η F),
        _root_.SerrePositivity.BhattScholze.Prismatic.IsBoundedPrism (Q F) ∧
          (letI := (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectEnvelopeResidueUnit
            (show P.ideal ≤ _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal P w F from le_sup_left) hE).toAlgebra
           _root_.SerrePositivity.IsCompletelyFaithfullyFlat (Ideal.span {(p : A ⧸ _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal P w F)})
             (C F ⧸ (Q F).ideal)) := by
  have h (F : Finset J) : ∃ (B : CommRingCat.{u}) (V : _root_.SerrePositivity.BhattScholze.OrientedPrism p B) (ν : A →+* B),
      ∃ hE : _root_.SerrePositivity.BhattScholze.Prismatic.IsPrismaticEnvelope P P.deltaStructure (RingHom.id A)
        P.deltaStructure.isDeltaHom_id (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal P w F)
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal_generator P w F) V ν,
        _root_.SerrePositivity.BhattScholze.Prismatic.IsBoundedPrism V ∧
          (letI := (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectEnvelopeResidueUnit
            (show P.ideal ≤ _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal P w F from le_sup_left) hE).toAlgebra
           _root_.SerrePositivity.IsCompletelyFaithfullyFlat (Ideal.span {(p : A ⧸ _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal P w F)})
             (B ⧸ V.ideal)) := by
    have he : P.ideal ⊔ Ideal.span (Set.range (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRelations w F)) =
        _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal P w F := by rw [_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRelations_ideal]; rfl
    have hb := hbound F
    rw [← he] at hb
    obtain ⟨B, V, ν, hE, hV, hFF⟩ := _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_bounded_lciRelationEnvelope_faithful P
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRelations w F) (fun n => (hreg F).isZero _ (by omega)) hb
    let Good (I : Ideal A) : Prop :=
      ∃ hI : P.generator ∈ I, ∃ (D : CommRingCat.{u}) (W : _root_.SerrePositivity.BhattScholze.OrientedPrism p D) (μ : A →+* D),
        ∃ hW : _root_.SerrePositivity.BhattScholze.Prismatic.IsPrismaticEnvelope P P.deltaStructure (RingHom.id A)
          P.deltaStructure.isDeltaHom_id I hI W μ,
          _root_.SerrePositivity.BhattScholze.Prismatic.IsBoundedPrism W ∧
            (letI := (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectEnvelopeResidueUnit
              (show P.ideal ≤ I from (Ideal.span_singleton_le_iff_mem I).mpr hI) hW).toAlgebra
             _root_.SerrePositivity.IsCompletelyFaithfullyFlat (Ideal.span {(p : A ⧸ I)}) (D ⧸ W.ideal))
    have hg : Good (P.ideal ⊔ Ideal.span (Set.range (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRelations w F))) :=
      ⟨(show P.ideal ≤ P.ideal ⊔ Ideal.span (Set.range (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRelations w F)) from le_sup_left)
        (Ideal.subset_span (Set.mem_singleton _)), B, V, ν, hE, hV, hFF⟩
    have hg' : Good (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal P w F) := he ▸ hg
    obtain ⟨hI, B, V, ν, hE, hV, hFF⟩ := hg'
    exact ⟨B, V, ν, hE, hV, hFF⟩
  choose C Q η hC using h
  exact ⟨C, Q, η, hC⟩

end SerrePositivity.BhattScholze.Prismatic

end
