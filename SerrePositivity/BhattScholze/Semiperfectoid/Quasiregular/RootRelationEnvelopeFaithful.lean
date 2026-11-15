module

public import SerrePositivity.BhattScholze.Semiperfectoid.Quasiregular.RootRelationCoordinates
public import SerrePositivity.BhattScholze.Semiperfectoid.Quasiregular.RootFamilyPerfectoid
public import SerrePositivity.BhattScholze.Semiperfectoid.Quasiregular.PerfectoidRelationEnvelopeFaithful
public import SerrePositivity.BhattScholze.Semiperfectoid.Quasiregular.PrismInitialTransport

/-!
# 有限 T の完全忠実平坦な包絡単位と始性

## 概要
perfectoid 係数から作る有限根関係商に、有界な実包絡と指定された単位を作る。
## 方針
証明済みの Koszul 正則性・有界ねじれを K5 の存在定理へ渡す。
## 規約
BS 著者版 Proposition 7.10。Δ との同一視は含めない。
## 使われ方
有限 T の古典的な prismatic 模型。
-/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open _root_.CategoryTheory _root_.SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] {r : ℕ} (f : Fin r → R)
local notation "Base" => rootFamilyBase p R (Fin r)
local notation "T" => rootRelationQuotient p R f

/-- 概要：有限根関係商に対し、有界な実包絡と全有界試験 prism への始性を作る。
方針：完全な剰余表示に Xi−fi を持ち上げ、既存の有限 lci 包絡を使う。
規約：BS 著者版 Proposition 7.10。零環も含み、標的の p 正則性は仮定しない。
使われ方：prismatic な包絡の比較 の Δ 比較に先立つ有限 T の古典的な始対象。 -/
theorem exists_rootRelationEnvelope_faithful (hR : IsIntegralPerfectoid R p) :
    ∃ (A : CommRingCat.{u}) (P : OrientedPrism p A) (e : A ⧸ P.ideal ≃+* Base)
      (w : Fin r → A),
      (∀ i, e (Ideal.Quotient.mk P.ideal (w i)) = rootRelationSequence p R f i) ∧
      P.deltaStructure.IsPerfect ∧
      ∃ (B : CommRingCat.{u}) (Q : OrientedPrism p B) (η : A →+* B),
        _root_.SerrePositivity.BhattScholze.Semiperfectoid.IsFiniteLciRelationEnvelope P w Q η ∧ IsBoundedPrism Q ∧
        ∃ v : T →+* B ⧸ Q.ideal,
          (∀ x : A, v (rootRelationQuotientUnit p R f (e (Ideal.Quotient.mk P.ideal x))) =
            Ideal.Quotient.mk Q.ideal (η x)) ∧
          (letI := v.toAlgebra
           IsCompletelyFaithfullyFlat (Ideal.span {(p : T)}) (B ⧸ Q.ideal)) ∧
          ∀ (C : Type u) [CommRing C] (Y : OrientedPrism p C) (hY : IsBoundedPrism Y)
            (s : T →+* C ⧸ Y.ideal),
            ∃! g : OrientedPrism.Hom Q Y, g.quotientMap.comp v = s := by
  let z := rootRelationSequence p R f
  have hb : ∃ N : ℕ, ∀ (n : ℕ) (x : Base ⧸ Ideal.span (Set.range z)),
      (p : Base ⧸ Ideal.span (Set.range z))^n * x = 0 →
        (p : Base ⧸ Ideal.span (Set.range z))^N * x = 0 := by
    have h := rootRelationQuotient_bounded p R f hR
    change ∃ N : ℕ, ∀ (n : ℕ) (x : Base ⧸ rootRelationBaseIdeal p R f),
      (p : Base ⧸ rootRelationBaseIdeal p R f)^n * x = 0 →
        (p : Base ⧸ rootRelationBaseIdeal p R f)^N * x = 0 at h
    rwa [rootRelationBaseIdeal_eq] at h
  obtain ⟨A, P, e, w, hw, hP, B, Q, η, hE, hQ, v, hv, hFF, hinit⟩ :=
    exists_perfectoidRelationEnvelope_faithful p Base
      (rootFamilyBase_isIntegralPerfectoid p R (Fin r) hR) z
      (rootRelationSequence_isKoszulResolution p R f) hb
  let eT : T ≃+* Base ⧸ Ideal.span (Set.range z) :=
    Ideal.quotEquivOfEq (rootRelationBaseIdeal_eq p R f)
  let v' := v.comp eT.toRingHom
  refine ⟨A, P, e, w, hw, hP, B, Q, η, hE, hQ, v', ?_, ?_, ?_⟩
  · intro x
    change v (eT (Ideal.Quotient.mk _ (e (Ideal.Quotient.mk P.ideal x)))) = _
    rw [Ideal.quotEquivOfEq_mk]
    exact hv x
  · have hsrc : letI := eT.toRingHom.toAlgebra
        IsCompletelyFaithfullyFlat (Ideal.span {(p : T)}) (Base ⧸ Ideal.span (Set.range z)) := by
      letI := eT.toRingHom.toAlgebra
      letI : Module.FaithfullyFlat T (Base ⧸ Ideal.span (Set.range z)) := by
        apply RingHom.faithfullyFlat_algebraMap_iff.mp
        exact RingHom.FaithfullyFlat.of_bijective eT.bijective
      exact isCompletelyFaithfullyFlat_of_faithfullyFlat _
    exact Andre.Transfinite.isCompletelyFaithfullyFlat_comp eT.toRingHom v _ hsrc (by
      simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using hFF)
  · intro C _ Y hY s
    exact existsUnique_prismHom_of_source_equiv Q Y v eT (hinit C Y hY) s

end SerrePositivity.BhattScholze.Semiperfectoid
