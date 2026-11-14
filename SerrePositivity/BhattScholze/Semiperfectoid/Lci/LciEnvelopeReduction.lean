module

public import SerrePositivity.BhattScholze.Semiperfectoid.Lci.LciEnvelopeCompletedResidue
public import SerrePositivity.BhattScholze.Semiperfectoid.Lci.LciEnvelopeKoszul
public import SerrePositivity.BhattScholze.Semiperfectoid.RawVariableEnvelope
public import SerrePositivity.BhattScholze.Semiperfectoid.Lci.LciEnvelopeVariables
public import SerrePositivity.HomologicalAlgebra.TorAlgebraAcyclicBaseChange

/-!
# lci 分類射の生成元剰余

## 概要
普遍自由変数の生成元剰余を、指定の正則列の商への完全平坦な底変換に使う。
通常の商の p 冪ねじれの上界も、反復した商へ移す。

## 方針
初期変数の商と二重商の標準同型を使い、既存の普遍剰余の完全平坦性を移す。

## 規約
BS 著者版 Example 7.9 と D76。変数の有限個の添字を濃度の宇宙の型と同定する。

## 使われ方
一般の正則列に対する包絡候補の離散性と有界性。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward false

universe u

namespace SerrePositivity.BhattScholze.Prismatic

open CategoryTheory DerivedCompletion

variable {p : ℕ} [Fact p.Prime] {A₀ A S : Type u} [CommRing A₀] [CommRing A]
variable (P₀ : OrientedPrism p A₀) (P : OrientedPrism p A) {r : ℕ} (f : Fin r → A)
variable (index : Fin r ≃ S)
variable (g : OrientedPrism.Hom P₀ P)

local notation "U" => RelativeFreeDeltaRing («R» := A₀) S
local notation "C" => (MvPolynomial.C : A₀ →+* U)
local notation "a" => C P₀.generator
local notation "I" => (Ideal.span {a} : Ideal U)
local notation "q" => Ideal.Quotient.mk I
local notation "c" => relativeFreeDeltaEval P.deltaStructure g.toRingHom (fun s : S => f (index.symm s))
local notation "A₁" => A ⧸ Ideal.map c I
local notation "c₀" => Ideal.quotientMap («I» := I) (Ideal.map c I) c (Ideal.le_comap_map («I» := I) (f := c))
local notation "z" => (fun i : Fin r => q (MvPolynomial.X (index i, 0)))
local notation "J" => Ideal.span (Set.range z)
local notation "T" => (U ⧸ I) ⧸ J
local notation "qz" => Ideal.Quotient.mk J
local notation "R" => A₁ ⧸ Ideal.map c₀ J
local notation "E" => completedFreeDelta P₀ S
local notation "j" => pdCompletionUnit U p a
local notation "d" => j a
local notation "L" => (Ideal.span {d} : Ideal E)
local notation "qE" => Ideal.Quotient.mk L
local notation "α" => rawVariableEnvelopeMap P₀ S

set_option maxHeartbeats 800000 in
/-- 概要：分類射の生成元剰余は、正則列の商を経由する完全平坦な射を持つ。
方針：初期変数の二重商を未完備源の商に同定し、普遍剰余の完全平坦性を合成する。
規約：BS 著者版 Example 7.9。R の有界性は反復した関係商にも同じ指数で通る。
使われ方：一般の lci 商への完備導来底変換。 -/
theorem exists_lciRelation_generatorReduction
    (hd : g.toRingHom P₀.generator = P.generator)
    (hp₀ : Function.Injective (fun x : A₀ => (p : A₀) * x))
    (hpd₀ : Function.Injective (fun x : A₀ ⧸ P₀.ideal => (p : A₀ ⧸ P₀.ideal) * x))
    (hf : IsKoszulResolution (fun i => Ideal.Quotient.mk P.ideal (f i)))
    (hR : ∃ N : ℕ, ∀ (n : ℕ) (x : A ⧸ (P.ideal ⊔ Ideal.span (Set.range f))),
      (p : A ⧸ (P.ideal ⊔ Ideal.span (Set.range f))) ^ n * x = 0 →
        (p : A ⧸ (P.ideal ⊔ Ideal.span (Set.range f))) ^ N * x = 0) :
    ∃ b : T →+* E ⧸ L,
      (qE).comp α = ((b).comp qz).comp q ∧
      IsCompletelyFlat (Ideal.span {(p : T)}) (baseChangeScalarModule b) ∧
      IsKoszulResolution z ∧ IsKoszulResolution (c₀ ∘ z) ∧
      ∃ N : ℕ, ∀ (n : ℕ) (x : R), (p : R) ^ n * x = 0 → (p : R) ^ N * x = 0 := by
  let := pdCompletionCommRing U p a
  let K : Ideal U := Ideal.span (Set.range fun s : S => MvPolynomial.X (s, 0))
  have hJ : J = K.map q := by
    change Ideal.span (Set.range z) = K.map q
    rw [Ideal.map_span]
    apply congrArg Ideal.span
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, ⟨index i, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
      exact ⟨index.symm s, by dsimp; rw [index.apply_symm_apply]⟩
  let eT : T ≃+* U ⧸ (I ⊔ K) :=
    (Ideal.quotEquivOfEq hJ).trans (DoubleQuot.quotQuotEquivQuotSup I K)
  have heT (x : U) : eT (qz (q x)) = Ideal.Quotient.mk (I ⊔ K) x := by
    change DoubleQuot.quotQuotEquivQuotSup I K
      ((Ideal.quotEquivOfEq hJ) (qz (q x))) = _
    rw [Ideal.quotEquivOfEq_mk]
    exact DoubleQuot.quotQuotEquivQuotSup_quotQuotMk I K x
  have hunit : IsUnit (P₀.deltaStructure.delta P₀.generator) := P₀.isDistinguished_generator
  obtain ⟨b₀, hb₀, hflat₀⟩ :=
    exists_completedFreeVariable_generatorResidue_completelyFlat (S := S)
      P₀.deltaStructure P₀.generator hp₀ hpd₀ hunit.unit hunit.unit_spec
  change (U ⧸ (I ⊔ K)) →+* (E ⧸ L) at b₀
  let b : T →+* E ⧸ L := b₀.comp eT.toRingHom
  have hsq : (qE).comp α = ((b).comp qz).comp q := by
    apply RingHom.ext
    intro x
    change qE (α x) = b₀ (eT (qz (q x)))
    rw [heT]
    exact (hb₀ x).symm
  have hflat : IsCompletelyFlat (Ideal.span {(p : T)}) (baseChangeScalarModule b) := by
    have hT : letI := eT.toRingHom.toAlgebra
        IsCompletelyFlat (Ideal.span {(p : T)} : Ideal T) (U ⧸ (I ⊔ K)) := by
      let := eT.toRingHom.toAlgebra
      let : Module.Flat T (U ⧸ (I ⊔ K)) :=
        RingHom.flat_algebraMap_iff.mp (RingHom.Flat.of_bijective eT.bijective)
      intro M _ _ _
      apply (isConcentratedInDegreeZero_derivedTensor_iff (U ⧸ (I ⊔ K)) M).mpr
      intro n hn
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
      exact torModule_subsingleton_of_flat (U ⧸ (I ⊔ K)) M k
    letI : Algebra (U ⧸ (I ⊔ K)) (E ⧸ L) := b₀.toAlgebra
    have hE : IsCompletelyFlat ((Ideal.span {(p : T)}).map eT.toRingHom) (E ⧸ L) := by
      rw [Ideal.map_span, Set.image_singleton, map_natCast]
      exact hflat₀
    have hc := Andre.Transfinite.isCompletelyFlat_comp eT.toRingHom b₀ _ hT hE
    let := b.toAlgebra
    let eM := baseChangeScalarAlgebraEquiv («R» := T) (B := E ⧸ L)
    exact isCompletelyFlat_of_linearEquiv _ eM.symm hc
  have hz : IsKoszulResolution z :=
    freeDelta_initialVariables_modGenerator_isKoszulResolution P₀.generator
      index index.injective
  have hca : c a = P.generator := by
    rw [relativeFreeDeltaEval_C, hd]
  have hIA : Ideal.map c I = P.ideal := by
    rw [Ideal.map_span, Set.image_singleton, hca]
    rfl
  have hc₀ (i : Fin r) : c₀ (z i) = Ideal.Quotient.mk (Ideal.map c I) (f i) := by
    change Ideal.Quotient.mk (Ideal.map c I) (c (MvPolynomial.X (index i, 0))) = _
    rw [relativeFreeDeltaEval_X, Function.iterate_zero_apply, index.symm_apply_apply]
  have hfun : c₀ ∘ z = fun i => Ideal.Quotient.mk (Ideal.map c I) (f i) := funext hc₀
  have hf₀ : IsKoszulResolution (c₀ ∘ z) := by
    rw [hfun]
    let e : (A ⧸ Ideal.map c I) ≃+* A ⧸ P.ideal := Ideal.quotEquivOfEq hIA
    apply isKoszulResolution_of_ringEquiv e
    have he : e.toRingHom ∘ (fun i => Ideal.Quotient.mk (Ideal.map c I) (f i)) =
        (fun i => Ideal.Quotient.mk P.ideal (f i)) := by
      funext i
      exact Ideal.quotEquivOfEq_mk hIA (f i)
    rw [he]
    exact hf
  let F : Ideal A := Ideal.span (Set.range f)
  have hF : Ideal.map c₀ J = F.map (Ideal.Quotient.mk (Ideal.map c I)) := by
    calc
      Ideal.map c₀ J = Ideal.span (c₀ '' Set.range z) := Ideal.map_span c₀ _
      _ = Ideal.span (Set.range (c₀ ∘ z)) := congrArg Ideal.span (Set.range_comp c₀ z).symm
      _ = Ideal.span (Set.range (fun i => Ideal.Quotient.mk (Ideal.map c I) (f i))) :=
        congrArg Ideal.span (congrArg Set.range hfun)
      _ = F.map (Ideal.Quotient.mk (Ideal.map c I)) := by
        exact (congrArg Ideal.span (Set.range_comp _ f)).trans
          (Ideal.map_span _ _).symm
  let eR : R ≃+* A ⧸ (P.ideal ⊔ Ideal.span (Set.range f)) :=
    ((Ideal.quotEquivOfEq hF).trans
      (DoubleQuot.quotQuotEquivQuotSup (Ideal.map c I) F)).trans
      (Ideal.quotEquivOfEq (congrArg (fun H : Ideal A => H ⊔ F) hIA))
  refine ⟨b, hsq, hflat, hz, hf₀, ?_⟩
  obtain ⟨N, hN⟩ := hR
  refine ⟨N, fun n x hx => ?_⟩
  apply eR.injective
  have hx' : (p : A ⧸ (P.ideal ⊔ Ideal.span (Set.range f))) ^ n * eR x = 0 := by
    simpa only [map_mul, map_pow, map_natCast, map_zero] using congrArg eR hx
  have h := hN n (eR x) hx'
  simpa only [map_mul, map_pow, map_natCast, map_zero] using h

end SerrePositivity.BhattScholze.Prismatic
