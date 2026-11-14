module

public import SerrePositivity.BhattScholze.Prism.Basic.Rigidity
public import SerrePositivity.BhattScholze.Semiperfectoid.Quasiregular.FiniteEnvelopes.FiniteEnvelopeDiagram
public import SerrePositivity.CommutativeAlgebra.DirectLimitRelations

/-!
# 有限包絡の生の余極限の正則性と普遍性

## 概要
生の余極限の Cartier 元・剰余の共通指数・全試験 prism への相対一意延長を与える。
## 方針
既存の環・加群・実完備化の普遍性と有限段の一意性を使い、単位を保つ比較を構成する。
## 規約
BS 著者版 Proposition 7.10。生の余極限と実完備化を区別し、零環を含む。
## 使われ方
S′ の有界包絡、全有界試験 prism への始性と Corollary 7.3 の比較。
-/

/-! ## FiniteEnvelopeRawRegular -/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Prismatic
open _root_.CategoryTheory
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {A J : Type u} [CommRing A]
variable (P : OrientedPrism p A) (w : J → A)
variable (C : Finset J → CommRingCat.{u}) (Q : ∀ F, OrientedPrism p (C F))
variable (η : ∀ F, A →+* C F)
variable (hE : ∀ F, IsPrismaticEnvelope P P.deltaStructure (RingHom.id A)
  P.deltaStructure.isDeltaHom_id (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal P w F)
  (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal_generator P w F) (Q F) (η F))

include hE

/-- 概要：基底の Cartier 生成元の像は、生の有限包絡余極限でも非零因子。
方針：各段での生成元の像の正則性と、環余極限の正則性補題を使う。
規約：BS 著者版 Proposition 7.10。全ての段と零環の枝を含む。
使われ方：生の δ 余極限を実 (p,d) 完備化する入力。 -/
theorem _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimit_generator_mul_injective :
    Function.Injective (fun x : _root_.SerrePositivity.BhattScholze.Semiperfectoid.FiniteEnvelopeRawColimit P w C Q η hE =>
      _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitBase P w C Q η hE P.generator * x) := by
  apply _root_.SerrePositivity.ringDirectLimit_element_mul_injective (fun F => C F)
    (fun _ _ h => (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeTransition P w C Q η hE h).toRingHom)
    (fun F => η F P.generator)
  · intro F
    exact (RingHom.congr_fun (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitBase_eq_stage P w C Q η hE F)
      P.generator).symm
  · intro F G h
    exact RingHom.congr_fun (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeTransition_base P w C Q η hE h) P.generator
  · intro F
    let f : _root_.SerrePositivity.BhattScholze.OrientedPrism.Hom P (Q F) := ⟨η F, (hE F).isDeltaHom, by
      simpa only [RingHom.comp_id] using (hE F).base_hom⟩
    exact f.map_generator_mul_injective

end SerrePositivity.BhattScholze.Prismatic

end

/-! ## FiniteEnvelopeRawBound -/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Prismatic
open _root_.CategoryTheory
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {A J : Type u} [CommRing A]
variable (P : OrientedPrism p A) (w : J → A)
variable (C : Finset J → CommRingCat.{u}) (Q : ∀ F, OrientedPrism p (C F))
variable (η : ∀ F, A →+* C F)
variable (hE : ∀ F, IsPrismaticEnvelope P P.deltaStructure (RingHom.id A)
  P.deltaStructure.isDeltaHom_id (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal P w F)
  (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal_generator P w F) (Q F) (η F))
local notation "L" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.FiniteEnvelopeRawColimit P w C Q η hE
local notation "d" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitBase P w C Q η hE P.generator

/-- 概要：全有限包絡の剰余に共通の指数 N は生の余極限の生成元剰余にも有効。
方針：段のイデアルを生成元の像にそろえ、通常剰余の環余極限同型を使う。
規約：BS 著者版 Proposition 7.10。N の一様性は明示的な仮定。
使われ方：有界な完備包絡の構成。 -/
theorem _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimit_residue_uniform_torsion_bound (N : ℕ)
    (hN : ∀ F n, ∀ x : C F ⧸ (Q F).ideal,
      (p : C F ⧸ (Q F).ideal) ^n * x = 0 → (p : C F ⧸ (Q F).ideal) ^N * x = 0)
    (n : ℕ) (x : L ⧸ Ideal.span {d}) (hx : (p : L ⧸ Ideal.span {d}) ^n * x = 0) :
    (p : L ⧸ Ideal.span {d}) ^N * x = 0 := by
  let f : ∀ F G : Finset J, F ⊆ G → C F →+* C G := fun F G h => (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeTransition P w C Q η hE h).toRingHom
  let t := fun F => η F P.generator
  have hc : ∀ F G h, f F G h (t F) = t G := by
    intro F G h
    exact RingHom.congr_fun (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeTransition_base P w C Q η hE h) P.generator
  have ht : ∀ F, Ring.DirectLimit.of (fun F => C F) (fun F G h => f F G h) F (t F) = d := by
    intro F
    exact (RingHom.congr_fun (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitBase_eq_stage P w C Q η hE F)
      P.generator).symm
  obtain ⟨e, _⟩ := _root_.SerrePositivity.exists_ringDirectLimit_principalQuotient_equiv (fun F => C F) f t hc d ht
  have hs (F : Finset J) (k : ℕ) (y : _root_.SerrePositivity.PrincipalQuotientStage (fun F => C F) t F)
      (hy : (p : _root_.SerrePositivity.PrincipalQuotientStage (fun F => C F) t F) ^k * y = 0) :
      (p : _root_.SerrePositivity.PrincipalQuotientStage (fun F => C F) t F) ^N * y = 0 := by
    let b : _root_.SerrePositivity.BhattScholze.OrientedPrism.Hom P (Q F) := ⟨η F, (hE F).isDeltaHom, by
      simpa only [RingHom.comp_id] using (hE F).base_hom⟩
    let eF := Ideal.quotEquivOfEq b.span_map_generator
    apply eF.injective
    have hy' : (p : C F ⧸ (Q F).ideal) ^k * eF y = 0 := by
      simpa only [map_mul, map_pow, map_natCast, map_zero] using congrArg eF hy
    simpa only [map_mul, map_pow, map_natCast, map_zero] using hN F k (eF y) hy'
  apply e.injective
  have hx' : (p : _) ^n * e x = 0 := by
    simpa only [map_mul, map_pow, map_natCast, map_zero] using congrArg e hx
  have h := _root_.SerrePositivity.ringDirectLimit_uniform_torsion_bound (_root_.SerrePositivity.PrincipalQuotientStage (fun F => C F) t)
    (fun _ _ h => _root_.SerrePositivity.principalQuotientStageMap (fun F => C F) f t hc h) p N hs n (e x) hx'
  simpa only [map_mul, map_pow, map_natCast, map_zero] using h

end SerrePositivity.BhattScholze.Prismatic

end

/-! ## FiniteEnvelopeRawUniversal -/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Prismatic
open _root_.CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {p : ℕ} [Fact p.Prime] {A J B : Type u} [CommRing A] [CommRing B]
variable (P : OrientedPrism p A) (w : J → A)
variable (C : Finset J → CommRingCat.{u}) (Q : ∀ F, OrientedPrism p (C F))
variable (η : ∀ F, A →+* C F)
variable (hE : ∀ F, IsPrismaticEnvelope P P.deltaStructure (RingHom.id A)
  P.deltaStructure.isDeltaHom_id (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal P w F)
  (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal_generator P w F) (Q F) (η F))

/-- 有限関係のイデアルは全関係のイデアルに含まれる。 -/
theorem _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal_le_full (F : Finset J) :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal P w F ≤ P.ideal ⊔ Ideal.span (Set.range w) := by
  apply sup_le_sup_left
  apply Ideal.span_mono
  rintro _ ⟨j, _, rfl⟩
  exact ⟨j, rfl⟩

/-- 概要：全関係を殺す相対 δ 射は生の包絡余極限から一意に延長する。
方針：有限包絡の一意性で遷移との両立を示し、δ 余極限の普遍性を使う。
規約：BS 著者版 Proposition 7.10。全 prism が標的。
使われ方：完備包絡の相対普遍性。 -/
theorem _root_.SerrePositivity.BhattScholze.Semiperfectoid.existsUnique_finiteEnvelopeRawColimitHom (Y : _root_.SerrePositivity.BhattScholze.OrientedPrism p B)
    (f : A →+* B) (hf : P.deltaStructure.IsDeltaHom Y.deltaStructure f)
    (hbase : P.ideal ≤ Y.ideal.comap f)
    (hmap : (P.ideal ⊔ Ideal.span (Set.range w)).map f ≤ Y.ideal) :
    ∃! g : _root_.SerrePositivity.BhattScholze.Semiperfectoid.FiniteEnvelopeRawColimit P w C Q η hE →+* B,
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitDelta P w C Q η hE).IsDeltaHom Y.deltaStructure g ∧
        g.comp (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitBase P w C Q η hE) = f := by
  have hF (F : Finset J) : ∃! g : C F →+* B,
      (Q F).deltaStructure.IsDeltaHom Y.deltaStructure g ∧ g.comp (η F) = f :=
    (hE F).lift Y f hf (by simpa only [RingHom.comp_id] using hbase)
      ((Ideal.map_mono (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal_le_full P w F)).trans hmap)
  choose g hg hgu using hF
  have hcomp (F G : Finset J) (h : F ⊆ G) :
      (g G).comp (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeTransition P w C Q η hE h).toRingHom = g F := by
    apply hgu F
    refine ⟨(hg G).1.comp (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeTransition P w C Q η hE h).map_delta, ?_⟩
    rw [RingHom.comp_assoc, _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeTransition_base, (hg G).2]
  let a : _root_.SerrePositivity.BhattScholze.Semiperfectoid.FiniteEnvelopeRawColimit P w C Q η hE →+* B := Ring.DirectLimit.lift
    (fun F => C F) (fun _ _ h => (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeTransition P w C Q η hE h).toRingHom) B g
    (fun F G h x => RingHom.congr_fun (hcomp F G h) x)
  have ha (F : Finset J) (x : C F) : a (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitOf P w C Q η hE F x) = g F x :=
    Ring.DirectLimit.lift_of (G := fun F => C F)
      (f := fun _ _ h => (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeTransition P w C Q η hE h).toRingHom)
      B g (fun F G h x => RingHom.congr_fun (hcomp F G h) x) F x
  have hδ : (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitDelta P w C Q η hE).IsDeltaHom Y.deltaStructure a :=
    _root_.SerrePositivity.BhattScholze.deltaDirectLimitLift_isDeltaHom (fun F => C F)
      (fun _ _ h => (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeTransition P w C Q η hE h).toRingHom)
      (fun F => (Q F).deltaStructure)
      (fun _ _ h => (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeTransition P w C Q η hE h).map_delta)
      Y.deltaStructure g (fun F G h x => RingHom.congr_fun (hcomp F G h) x) (fun F => (hg F).1)
  refine ⟨a, ⟨hδ, ?_⟩, ?_⟩
  · apply RingHom.ext
    intro x
    exact (ha ∅ (η ∅ x)).trans (RingHom.congr_fun (hg ∅).2 x)
  · intro k hk
    apply Ring.DirectLimit.hom_ext
    intro F
    trans g F
    · apply hgu F
      refine ⟨hk.1.comp (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitOf_isDeltaHom P w C Q η hE F), ?_⟩
      rw [RingHom.comp_assoc]
      change k.comp ((_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitOf P w C Q η hE F).comp (η F)) = f
      rw [← _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRawColimitBase_eq_stage, hk.2]
    · apply RingHom.ext
      intro x
      exact (ha F x).symm

end SerrePositivity.BhattScholze.Prismatic

end
