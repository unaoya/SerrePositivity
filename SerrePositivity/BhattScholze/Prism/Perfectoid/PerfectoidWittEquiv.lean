module
public meta import SerrePositivity.Util.Citation

public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectoidPrismPresentation
import all SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid

/-!
# 剰余表示から固定した Fontaine Witt 環への比較

## 概要
完全 prism の剰余が R であるとき、元の prism を W(R♭) と θ を保って比較する。
## 方針
既存の Witt 復元・完備 Witt 商の Fontaine 同型・θ の自然性を合成する。
## 規約
BS 著者版 Theorem 3.10・Proposition 7.10 の非零の枝。
## 使われ方
drafts の固定した A_inf の δ・θ と、有限 T の実包絡の表示の照合。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (p : ℕ) [Fact p.Prime]

/-- 環同型に沿う標準 tilt 射の環同型。 -/
def preTiltEquivOfRingEquiv {R S : Type u} [CommRing R] [CommRing S]
    [Fact (¬ IsUnit (p : R))] [Fact (¬ IsUnit (p : S))] (e : R ≃+* S) :
    PreTilt R p ≃+* PreTilt S p := by
  let em : ModP R p ≃+* ModP S p := Ideal.quotientEquiv _ _ e
    (by simp only [Ideal.map_span, Set.image_singleton, map_natCast])
  let t := Perfection.map p (modPMap p e.toRingHom)
  apply RingEquiv.ofBijective t
  constructor
  · intro x y h
    apply Perfection.ext
    intro n
    apply em.injective
    have hh := congrArg (Perfection.coeff (ModP S p) p n) h
    exact hh
  · intro y
    refine ⟨Perfection.map p em.symm.toRingHom y, ?_⟩
    apply Perfection.ext
    intro n
    exact em.apply_symm_apply _

/-- 環同型から得られる、標準 Witt–tilt 射そのものの環同型。 -/
def wittPreTiltEquivOfRingEquiv {R S : Type u} [CommRing R] [CommRing S]
    [Fact (¬ IsUnit (p : R))] [Fact (¬ IsUnit (p : S))] (e : R ≃+* S) :
    WittVector p (PreTilt R p) ≃+* WittVector p (PreTilt S p) :=
  RingEquiv.ofBijective (WittVector.map (preTiltEquivOfRingEquiv p e).toRingHom)
    ⟨WittVector.map_injective _ (preTiltEquivOfRingEquiv p e).injective,
      WittVector.map_surjective _ (preTiltEquivOfRingEquiv p e).surjective⟩

/-- Witt–tilt の環同型は標準 δ 構造を保つ。 -/
theorem wittPreTiltEquivOfRingEquiv_isDeltaHom {R S : Type u} [CommRing R] [CommRing S]
    [Fact (¬ IsUnit (p : R))] [Fact (¬ IsUnit (p : S))]
    (e : R ≃+* S) : (wittDeltaStructure p (PreTilt R p)).IsDeltaHom
      (wittDeltaStructure p (PreTilt S p)) (wittPreTiltEquivOfRingEquiv p e).toRingHom :=
  wittDeltaStructure_map_isDeltaHom p _ _

/-- Witt–tilt の環同型は、標準 Fontaine 射を保つ。 -/
theorem wittPreTiltEquivOfRingEquiv_fontaine {R S : Type u} [CommRing R] [CommRing S]
    [Fact (¬ IsUnit (p : R))] [Fact (¬ IsUnit (p : S))]
    [IsAdicComplete (Ideal.span {(p : R)}) R] [IsAdicComplete (Ideal.span {(p : S)}) S]
    (e : R ≃+* S) : (WittVector.fontaineTheta S p).comp
      (wittPreTiltEquivOfRingEquiv p e).toRingHom = e.toRingHom.comp (WittVector.fontaineTheta R p) :=
  fontaineTheta_natural p e.toRingHom

/-- 完全 prism の剰余表示は、固定した W(R♭) と δ・θ を保って比較できる。 -/
theorem exists_fontaineCompatibleWittEquiv {R A : Type u} [CommRing R] [CommRing A]
    [Fact (¬ IsUnit (p : R))] [IsAdicComplete (Ideal.span {(p : R)}) R]
    (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (e : A ⧸ P.ideal ≃+* R) :
    ∃ ρ : WittVector p (PreTilt R p) ≃+* A,
      (wittDeltaStructure p (PreTilt R p)).IsDeltaHom P.deltaStructure ρ.toRingHom ∧
      (e.toRingHom.comp (Ideal.Quotient.mk P.ideal)).comp ρ.toRingHom = WittVector.fontaineTheta R p := by
  let qA := e.toRingHom.comp (Ideal.Quotient.mk P.ideal)
  letI : Fact (¬ IsUnit (p : A)) := ⟨fun h => (Fact.out : ¬ IsUnit (p : R))
    (by simpa only [map_natCast] using h.map qA)⟩
  letI := hP.perfectRing_mod_p
  let k := ModP A p
  let d := perfectPrismWittGenerator P hP
  have hd : (wittDeltaStructure p k).IsDistinguished d := perfectPrismWittGenerator_isDistinguished P hP
  letI : IsAdicComplete (Ideal.span {d}) (WittVector p k) :=
    perfectPrismWitt_isAdicComplete_generator P hP
  let S := WittVector p k ⧸ Ideal.span {d}
  let eR : S ≃+* R := (perfectPrismWittQuotientEquiv P hP).trans e
  letI : Fact (¬ IsUnit (p : S)) := ⟨fun h => (Fact.out : ¬ IsUnit (p : R))
    (by simpa only [map_natCast] using h.map eR.toRingHom)⟩
  letI : IsAdicComplete (Ideal.span {(p : S)}) S := by
    have h := (IsAdicComplete.congr_ringEquiv (Ideal.span {(p : R)}) eR.symm).mpr
      (inferInstance : IsAdicComplete (Ideal.span {(p : R)}) R)
    simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using h
  let e0 := RingEquiv.ofBijective (wittQuotientFontaineMap p k d)
    (wittCompleteQuotientFontaineMap_bijective p k d hd)
  let e1 := wittPreTiltEquivOfRingEquiv p eR
  let Φ := e0.trans e1
  let ρ := Φ.symm.trans (perfectPrismWittRecoveryEquiv P hP)
  have hΦ : (wittDeltaStructure p k).IsDeltaHom (wittDeltaStructure p (PreTilt R p)) Φ.toRingHom :=
    (wittPreTiltEquivOfRingEquiv_isDeltaHom p eR).comp (wittQuotientFontaineMap_isDeltaHom p k d)
  refine ⟨ρ, (perfectPrismWittRecoveryEquiv_isDeltaHom P hP).comp hΦ.symm, ?_⟩
  have hθ : (WittVector.fontaineTheta R p).comp Φ.toRingHom =
      eR.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {d})) := by
    change (WittVector.fontaineTheta R p).comp (e1.toRingHom.comp e0.toRingHom) = _
    rw [← RingHom.comp_assoc, wittPreTiltEquivOfRingEquiv_fontaine, RingHom.comp_assoc]
    congr 1
    change (WittVector.fontaineTheta S p).comp (wittQuotientFontaineMap p k d) = _
    exact wittQuotientFontaineMap_comp_fontaineTheta p k d
  apply RingHom.ext
  intro x
  have hh := RingHom.congr_fun hθ (Φ.symm x)
  change eR (Ideal.Quotient.mk (Ideal.span {d}) (Φ.symm x)) = WittVector.fontaineTheta R p x
  change WittVector.fontaineTheta R p (Φ (Φ.symm x)) =
    eR (Ideal.Quotient.mk (Ideal.span {d}) (Φ.symm x)) at hh
  rw [Φ.apply_symm_apply] at hh
  exact hh.symm

end SerrePositivity.BhattScholze.Semiperfectoid

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Thm 3.10" (partial := special) "圏同値ではなく三つの事実（商の perfectoid 性・perfectoid 環の prism 表示・射の持ち上げ）で（D8）。絶対の圏同値は本体にも drafts にもない（drafts/A5 の perfectSiteEquivPerfectoidUnder は固定基底の上の相対版、Lemma 4.8 の系） ／ DOC1 照合：ok 4 件 ／ 11-12 夜更新（§3 の見直し）"] _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_fontaineCompatibleWittEquiv
