module

public import SerrePositivity.BhattScholze.Prism.Perfectoid.WittQuotientHomLift
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismWittPresentation
public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrismHom

/-! # 一般の完全prism商の射の一意持上げ

F4のWitt復元と一般Witt商の持上げを合成する。商のp正則性は要求しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]

/-- pが非可逆な商を持つ完全prism間では、任意の商射は唯一のprism射に持ち上がる。 -/
theorem existsUnique_perfectPrismHomLift
    (P : OrientedPrism p A) (Q : OrientedPrism p B)
    (hP : P.deltaStructure.IsPerfect) (hQ : Q.deltaStructure.IsPerfect)
    [Fact (¬ IsUnit (p : A ⧸ P.ideal))] [Fact (¬ IsUnit (p : B ⧸ Q.ideal))]
    (g : A ⧸ P.ideal →+* B ⧸ Q.ideal) :
    ∃! f : OrientedPrism.Hom P Q, f.quotientMap = g := by
  let : Fact (¬ IsUnit (p : A)) :=
    ⟨fun h ↦ (Fact.out : ¬ IsUnit (p : A ⧸ P.ideal))
    (by simpa only [map_natCast] using h.map (Ideal.Quotient.mk P.ideal))⟩
  let : Fact (¬ IsUnit (p : B)) :=
    ⟨fun h ↦ (Fact.out : ¬ IsUnit (p : B ⧸ Q.ideal))
    (by simpa only [map_natCast] using h.map (Ideal.Quotient.mk Q.ideal))⟩
  let := hP.perfectRing_mod_p
  let := hQ.perfectRing_mod_p
  let k := ModP A p
  let l := ModP B p
  let ea := perfectPrismWittRecoveryEquiv P hP
  let eb := perfectPrismWittRecoveryEquiv Q hQ
  let d := perfectPrismWittGenerator P hP
  let e := perfectPrismWittGenerator Q hQ
  have hd := perfectPrismWittGenerator_isDistinguished P hP
  have he := perfectPrismWittGenerator_isDistinguished Q hQ
  let : IsAdicComplete (Ideal.span {d}) (WittVector p k) :=
    perfectPrismWitt_isAdicComplete_generator P hP
  let : IsAdicComplete (Ideal.span {e}) (WittVector p l) :=
    perfectPrismWitt_isAdicComplete_generator Q hQ
  let qa : WittVector p k ⧸ Ideal.span {d} ≃+* A ⧸ P.ideal :=
    perfectPrismWittQuotientEquiv P hP
  let qb : WittVector p l ⧸ Ideal.span {e} ≃+* B ⧸ Q.ideal :=
    perfectPrismWittQuotientEquiv Q hQ
  let : Fact (¬ IsUnit (p : WittVector p k ⧸ Ideal.span {d})) :=
    ⟨fun h ↦ (Fact.out : ¬ IsUnit (p : A ⧸ P.ideal))
    (by simpa only [map_natCast] using h.map qa.toRingHom)⟩
  let : Fact (¬ IsUnit (p : WittVector p l ⧸ Ideal.span {e})) :=
    ⟨fun h ↦ (Fact.out : ¬ IsUnit (p : B ⧸ Q.ideal))
    (by simpa only [map_natCast] using h.map qb.toRingHom)⟩
  let gg := qb.symm.toRingHom.comp (g.comp qa.toRingHom)
  obtain ⟨F, hF, _⟩ := existsUnique_wittQuotientHomLift p d e hd he gg
  let f := eb.toRingHom.comp (F.comp ea.symm.toRingHom)
  have hfg : (Ideal.Quotient.mk Q.ideal).comp f =
      g.comp (Ideal.Quotient.mk P.ideal) := by
    apply RingHom.ext
    intro a
    obtain ⟨x, rfl⟩ := ea.surjective a
    have hh := congrArg qb (RingHom.congr_fun hF.2 x)
    change qb (Ideal.Quotient.mk _ (F x)) =
      qb (qb.symm (g (qa (Ideal.Quotient.mk _ x)))) at hh
    rw [qb.apply_symm_apply] at hh
    change Ideal.Quotient.mk Q.ideal (eb (F (ea.symm (ea x)))) =
      g (Ideal.Quotient.mk P.ideal (ea x))
    rw [ea.symm_apply_apply]
    exact hh
  have hdelta : P.deltaStructure.IsDeltaHom Q.deltaStructure f :=
    (perfectPrismWittRecoveryEquiv_isDeltaHom Q hQ).comp
      (hF.1.comp (perfectPrismWittRecoveryEquiv_symm_isDeltaHom P hP))
  have hI : P.ideal ≤ Q.ideal.comap f := by
    intro x hx
    change f x ∈ Q.ideal
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hh := RingHom.congr_fun hfg x
    change Ideal.Quotient.mk Q.ideal (f x) = g (Ideal.Quotient.mk P.ideal x) at hh
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero] at hh
    exact hh
  let H : OrientedPrism.Hom P Q := { f with map_delta := hdelta, ideal_le := hI }
  have hHg : H.quotientMap = g := by
    apply Ideal.Quotient.ringHom_ext
    exact hfg
  refine ⟨H, hHg, ?_⟩
  intro K hK
  apply OrientedPrism.Hom.ext
  have heq : (Ideal.Quotient.mk Q.ideal).comp K.toRingHom =
      (Ideal.Quotient.mk Q.ideal).comp H.toRingHom := by
    rw [← OrientedPrism.Hom.quotientMap_comp_mk, ← OrientedPrism.Hom.quotientMap_comp_mk,
      hK, hHg]
  have hw : eb.symm.toRingHom.comp (K.toRingHom.comp ea.toRingHom) =
      eb.symm.toRingHom.comp (H.toRingHom.comp ea.toRingHom) := by
    apply wittQuotientHom_ext p e he
    apply RingHom.ext
    intro x
    have hh := RingHom.congr_fun heq (ea x)
    have h := congrArg qb.symm hh
    change Ideal.Quotient.mk _ (eb.symm (K.toRingHom (ea x))) =
      Ideal.Quotient.mk _ (eb.symm (H.toRingHom (ea x)))
    exact (perfectPrismWittQuotientEquiv_symm_mk Q hQ (K.toRingHom (ea x))).symm.trans
      (h.trans (perfectPrismWittQuotientEquiv_symm_mk Q hQ (H.toRingHom (ea x))))
  apply RingHom.ext
  intro a
  obtain ⟨x, rfl⟩ := ea.surjective a
  apply eb.symm.injective
  exact RingHom.congr_fun hw x

end SerrePositivity.BhattScholze
