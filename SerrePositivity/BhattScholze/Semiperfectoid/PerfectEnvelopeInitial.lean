module

public import SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelopeInitial
public import SerrePositivity.BhattScholze.Prism.PerfectPrismHomLift
import all SerrePositivity.BhattScholze.Prismatic.Envelope

/-!
# 完全基底上の包絡の全有界試験 prism への始性

## 概要
完全な基底 prism 上の包絡は、剰余の単位を指定した全有界試験 prism に対して始。
## 方針
既存の Lemma 4.8 の一意持ち上げで基底射を供給し、包絡の一意延長へ渡す。
## 規約
BS 著者版 Lemma 4.8・Example 7.9・Proposition 7.10。標的の p 正則性を仮定しない。
## 使われ方
有限 T の相対包絡から絶対的な有界試験対象への始性を得る。
-/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open Prismatic
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B} {J : Ideal A}
variable (hJ : P.ideal ≤ J) {η : A →+* B}
variable (hE : IsPrismaticEnvelope P P.deltaStructure (RingHom.id A)
  P.deltaStructure.isDeltaHom_id J (hJ (Ideal.subset_span (Set.mem_singleton P.generator))) Q η)

include hJ in
/-- 包絡の剰余へ向かう基底の関係商の単位。 -/
@[expose] def perfectEnvelopeResidueUnit : A ⧸ J →+* B ⧸ Q.ideal :=
  Ideal.quotientMap Q.ideal η (Ideal.map_le_iff_le_comap.mp hE.map_le)

/-- 概要：完全基底上の包絡から任意の有界試験 prism への射は剰余単位で一意に決まる。
方針：完全基底の一意持ち上げと包絡の一意延長を順に使う。
規約：BS 著者版 Proposition 7.10 の古典的な始性。p 正則な標的に制限しない。
使われ方：有限 T と S′ の実包絡の絶対始性。 -/
theorem existsUnique_perfectEnvelopeHom (hP : P.deltaStructure.IsPerfect)
    {C : Type u} [CommRing C] (Y : OrientedPrism p C) (hY : IsBoundedPrism Y)
    (z : A ⧸ J →+* C ⧸ Y.ideal) :
    ∃! g : OrientedPrism.Hom Q Y,
      g.quotientMap.comp (perfectEnvelopeResidueUnit hJ hE) = z := by
  let a : A ⧸ P.ideal →+* A ⧸ J := Ideal.Quotient.factor hJ
  obtain ⟨u, hu, huu⟩ := Andre.existsUnique_perfectPrismHomLift_to_bounded P hP Y hY (z.comp a)
  have hmap : J.map u.toRingHom ≤ Y.ideal := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change u.toRingHom x ∈ Y.ideal
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change u.quotientMap (Ideal.Quotient.mk P.ideal x) = 0
    rw [hu]
    change z (Ideal.Quotient.mk J x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  obtain ⟨f, hf, hfu⟩ := hE.lift Y u.toRingHom u.map_delta (by simpa using u.ideal_le) hmap
  let g : OrientedPrism.Hom Q Y := ⟨f, hf.1, by
    rw [hE.ideal_eq, Ideal.span_singleton_le_iff_mem]
    change (f.comp η) P.generator ∈ Y.ideal
    rw [hf.2]
    exact u.map_generator_mem⟩
  have hg : g.quotientMap.comp (perfectEnvelopeResidueUnit hJ hE) = z := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro x
    change Ideal.Quotient.mk Y.ideal ((f.comp η) x) = z (Ideal.Quotient.mk J x)
    rw [hf.2]
    change u.quotientMap (Ideal.Quotient.mk P.ideal x) = _
    rw [hu]
    rfl
  refine ⟨g, hg, ?_⟩
  intro g' hg'
  let b : OrientedPrism.Hom P Q := ⟨η, hE.isDeltaHom, by simpa using hE.base_hom⟩
  have hbase : g'.comp b = u := by
    apply huu
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro x
    exact RingHom.congr_fun hg' (Ideal.Quotient.mk J x)
  apply OrientedPrism.Hom.ext
  apply hfu
  refine ⟨g'.map_delta, ?_⟩
  exact congrArg OrientedPrism.Hom.toRingHom hbase

end SerrePositivity.BhattScholze.Semiperfectoid
