module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Delta.Perfect.DeltaPerfection
public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import SerrePositivity.BhattScholze.Delta.Perfect.DistinguishedRegular
public import SerrePositivity.BhattScholze.Delta.Extension.DeltaPDCompletion
public import SerrePositivity.BhattScholze.Prism.Perfection.PCompletedPerfection
public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDelta

/-!
# prism の完全化：完全化から導来 (p,d) 完備化へ（BS 著者版 Lemma 3.9）

## 概要
完全 δ 環と distinguished 元の導来 (p,d) 完備化 H⁰ は完全 prism で、完全試験 prism への普遍性を持つ。
任意の δ 環から完全化を挟んだ普遍性と、完全化と PD 完備化の順序の比較。
完備化と完全化の順序を比較し、BS 著者版 Lemma 3.9 の普遍性に向けた構成を整理する。

## 方針
完全化の普遍性（BS 著者版 Remark 2.27）と導来完備化の普遍性を合成する。

## 規約
原典の形（prism の完全化が普遍な完全 prism）の一つの定理にはまとめていない（BS 著者版 Lemma 3.9 の普遍性）。

## 使われ方
BS 著者版 Corollary 7.3 の構成、Theorem 3.10 の perfectoid 環の prism 表示、André。
PD 完備化の比較は旧 `Andre/RootedExtension` から移した。
-/

universe u

/-! ## 完全δ環のdistinguished元による実完備化の完全prism

実H⁰の完全δ性からp正則性を供給し、導来/古典的比較とBS 著者版 Lemma 2.34で
生成元の正則性を証明する。F5で商のp完備性も供給する。
-/

@[expose] public noncomputable section PerfectDeltaPDPrism

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 完全δ環とdistinguished元から、実PD完備化H⁰上の具体的な完全prismを構成する。 -/
def perfectDeltaPDPrism (D : DeltaStructure p A) (hD : D.IsPerfect) (d : A)
    (hd : D.IsDistinguished d) :
    letI := pdCompletionCommRing A p d
    OrientedPrism p (PDCompletionH0 A p d) := by
  letI := pdCompletionCommRing A p d
  let H := PDCompletionH0 A p d
  let DH := deltaPDCompletionStructure D d
  let j := pdCompletionUnit A p d
  have hH := deltaPDCompletionStructure_isPerfect D hD d
  have hpH := pdCompletionH0_self_complete_p A p d
  have hdH := pdCompletionH0_self_complete_d A p d
  letI : IsAdicComplete (Ideal.span {(p : H)}) H :=
    (isRingModuleComplete_iff_isAdicComplete_natCast H p hH.p_mul_injective).mp hpH
  have hdist : DH.IsDistinguished (j d) := (pdCompletionUnit_isDeltaHom D d).map_isDistinguished hd
  exact OrientedPrism.ofDistinguished DH (j d) hdist (hH.distinguished_mul_injective hdist) hpH hdH

/-- 完全prismのδ構造は、実H⁰への一意延長δ構造そのもの。 -/
@[simp] theorem perfectDeltaPDPrism_deltaStructure
    (D : DeltaStructure p A) (hD : D.IsPerfect) (d : A) (hd : D.IsDistinguished d) :
    letI := pdCompletionCommRing A p d
    (perfectDeltaPDPrism D hD d hd).deltaStructure = deltaPDCompletionStructure D d := rfl

/-- 完全prismの選択生成元は元のdのKoszul標準像。 -/
@[simp] theorem perfectDeltaPDPrism_generator
    (D : DeltaStructure p A) (hD : D.IsPerfect) (d : A) (hd : D.IsDistinguished d) :
    letI := pdCompletionCommRing A p d
    (perfectDeltaPDPrism D hD d hd).generator = pdCompletionUnit A p d d := rfl

/-- 構成したprismのδ構造は完全。 -/
theorem perfectDeltaPDPrism_isPerfect
    (D : DeltaStructure p A) (hD : D.IsPerfect) (d : A) (hd : D.IsDistinguished d) :
    letI := pdCompletionCommRing A p d
    (perfectDeltaPDPrism D hD d hd).deltaStructure.IsPerfect :=
  deltaPDCompletionStructure_isPerfect D hD d

/-- 構成したprismの標準商は、pねじれを許して古典的p進完備。 -/
theorem perfectDeltaPDPrism_quotient_isAdicComplete
    (D : DeltaStructure p A) (hD : D.IsPerfect) (d : A) (hd : D.IsDistinguished d) :
    letI := pdCompletionCommRing A p d
    IsAdicComplete (Ideal.span {(p : PDCompletionH0 A p d ⧸
      Ideal.span {pdCompletionUnit A p d d})})
      (PDCompletionH0 A p d ⧸ Ideal.span {pdCompletionUnit A p d d}) := by
  let := pdCompletionCommRing A p d
  let P := perfectDeltaPDPrism D hD d hd
  have hP := perfectDeltaPDPrism_isPerfect D hD d hd
  let := P.isAdicComplete_p_of_perfect hP
  exact hP.distinguished_quotient_isAdicComplete
    ((pdCompletionUnit_isDeltaHom D d).map_isDistinguished hd)

end SerrePositivity.BhattScholze

end PerfectDeltaPDPrism

/-! ## 完全δ環の実PD完備化prismの普遍性

完全試験prismへの基底δ射でdがprismイデアルへ入る場合、唯一のprism射を得る。
生成元の一致ではなく、イデアルの保存を用いる。
-/

@[expose] public noncomputable section PerfectDeltaPDPrismUniversal

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A T : Type u} [CommRing A] [CommRing T]

/-- d を完全試験 prism のイデアルに送る基底 δ 射は、実完備化 prism へ一意に延長する
（BS 著者版 Lemma 3.9 の完全 δ 環と distinguished 元からの完備化の延長）。 -/
theorem existsUnique_perfectDeltaPDPrismHom
    (D : DeltaStructure p A) (hD : D.IsPerfect) (d : A) (hd : D.IsDistinguished d)
    (Q : OrientedPrism p T) (hQ : Q.deltaStructure.IsPerfect)
    (f : A →+* T) (hf : D.IsDeltaHom Q.deltaStructure f) (hdf : f d ∈ Q.ideal) :
    letI := pdCompletionCommRing A p d
    ∃! g : OrientedPrism.Hom (perfectDeltaPDPrism D hD d hd) Q,
      g.toRingHom.comp (pdCompletionUnit A p d) = f := by
  let := pdCompletionCommRing A p d
  let P := perfectDeltaPDPrism D hD d hd
  let j := pdCompletionUnit A p d
  let := Q.isAdicComplete_generator
  let := Q.isAdicComplete_p_of_perfect hQ
  have hspan : Ideal.span {f d} = Q.ideal := by
    have h := hf.map_span_eq_of_distinguished_of_mem_span hd hdf
      (IsAdicComplete.le_jacobson_bot (Ideal.span {Q.generator}) (Ideal.subset_span (by simp)))
      (IsAdicComplete.le_jacobson_bot (Ideal.span {(p : T)}) (Ideal.subset_span (by simp)))
    simpa only [Ideal.map_span, Set.image_singleton, OrientedPrism.ideal] using h
  let : IsAdicComplete (Ideal.span {f d}) T := by
    rw [hspan]
    exact Q.isAdicComplete_generator
  have hdT : IsModuleComplete T (f d) (ModuleCat.of T T) :=
    isModuleComplete_of_isAdicComplete T (f d) (ModuleCat.of T T)
  obtain ⟨g, hg, hu⟩ := existsUnique_deltaPDCompletionHom D d Q.deltaStructure f hf Q.complete_p hdT
  have hideal : P.ideal ≤ Q.ideal.comap g := by
    change Ideal.span {j d} ≤ Q.ideal.comap g
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    change g (j d) ∈ Q.ideal
    have he : g (j d) = f d := RingHom.congr_fun hg.2 d
    rw [he]
    exact hdf
  let G : OrientedPrism.Hom P Q := ⟨g, hg.1, hideal⟩
  refine ⟨G, hg.2, ?_⟩
  intro k hk
  apply OrientedPrism.Hom.ext
  exact hu k.toRingHom ⟨k.map_delta, hk⟩

end SerrePositivity.BhattScholze

end PerfectDeltaPDPrismUniversal

/-! ## 完全δ環の実PD完備化と完備なdistinguished商の比較

標準商がp進完備なら、実完備化後の商と標準商は同型。
古典的完備化への置換ではなく、実H⁰の環普遍性で比較する。
-/

@[expose] public noncomputable section PerfectDeltaPDQuotientEquiv

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A T : Type u} [CommRing A] [CommRing T]

/-- 完全δ環のdistinguished商の具体的p完備表示は、実PD完備化後の商と同型。 -/
theorem exists_perfectDeltaPDQuotientEquiv
    (D : DeltaStructure p A) (hD : D.IsPerfect) (d : A) (hd : D.IsDistinguished d)
    (f : A →+* T) (hf : Function.Surjective f) (hk : RingHom.ker f = Ideal.span {d})
    [IsAdicComplete (Ideal.span {(p : T)}) T] :
    letI := pdCompletionCommRing A p d
    ∃ e : PDCompletionH0 A p d ⧸ Ideal.span {pdCompletionUnit A p d d} ≃+* T,
      e.toRingHom.comp ((Ideal.Quotient.mk _).comp (pdCompletionUnit A p d)) = f := by
  let := pdCompletionCommRing A p d
  let H := PDCompletionH0 A p d
  let j := pdCompletionUnit A p d
  let Q := H ⧸ Ideal.span {j d}
  let q := Ideal.Quotient.mk (Ideal.span {j d})
  have hfd : f d = 0 := by
    apply RingHom.mem_ker.mp
    rw [hk]
    exact Ideal.mem_span_singleton_self _
  have hpT := isModuleComplete_of_isAdicComplete T (p : T) (ModuleCat.of T T)
  have hz (B : Type u) [CommRing B] : IsModuleComplete B (0 : B) (ModuleCat.of B B) :=
    isModuleComplete_of_pow_smul_zero B 0 _ 1 (by simp)
  have hdT : IsModuleComplete T (f d) (ModuleCat.of T T) := hfd ▸ hz T
  obtain ⟨g, hg, _⟩ := existsUnique_pdCompletionRingHom A p d T f hpT hdT
  have hgd : g (j d) = 0 := by
    have he : g (j d) = f d := RingHom.congr_fun hg d
    exact he.trans hfd
  let b : Q →+* T := Ideal.Quotient.lift _ g (by
    change Ideal.span {j d} ≤ RingHom.ker g
    rw [Ideal.span_singleton_le_iff_mem]
    exact hgd)
  have hb : b.comp q = g := Ideal.Quotient.lift_comp_mk _ _ _
  have hqjd : q (j d) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hi : RingHom.ker f ≤ RingHom.ker (q.comp j) := by
    rw [hk, Ideal.span_singleton_le_iff_mem]
    exact hqjd
  let i : T →+* Q := f.liftOfSurjective hf ⟨q.comp j, hi⟩
  have hij : i.comp f = q.comp j := f.liftOfSurjective_comp hf _
  have hbi : b.comp i = RingHom.id T := by
    apply (RingHom.cancel_right hf).mp
    rw [RingHom.comp_assoc, hij, ← RingHom.comp_assoc, hb, hg, RingHom.id_comp]
  let : IsAdicComplete (Ideal.span {(p : Q)}) Q :=
    perfectDeltaPDPrism_quotient_isAdicComplete D hD d hd
  have hpQ := isModuleComplete_of_isAdicComplete Q (p : Q) (ModuleCat.of Q Q)
  have hdQ : IsModuleComplete Q ((q.comp j) d) (ModuleCat.of Q Q) := hqjd ▸ hz Q
  have hib : i.comp b = RingHom.id Q := by
    apply Ideal.Quotient.ringHom_ext
    have he : (i.comp g) = q := by
      apply pdCompletionRingHom_ext A p d Q (q.comp j) hpQ hdQ
      · rw [RingHom.comp_assoc, hg, hij]
      · rfl
    change (i.comp b).comp q = (RingHom.id Q).comp q
    rw [RingHom.comp_assoc, hb, he, RingHom.id_comp]
  let e : Q ≃+* T :=
    { b with
      invFun := i
      left_inv := RingHom.congr_fun hib
      right_inv := RingHom.congr_fun hbi }
  refine ⟨e, ?_⟩
  change b.comp (q.comp j) = f
  rw [← RingHom.comp_assoc, hb, hg]

end SerrePositivity.BhattScholze

end PerfectDeltaPDQuotientEquiv

/-! ## 二つの実δ完全化PD完備化環の、同じ完全試験環への普遍性 -/

@[expose] public noncomputable section DeltaPerfectionPDCompletionUniversal

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {B T : Type u} [CommRing B] [CommRing T]
variable (E : DeltaStructure p B) (b : B)
variable (F : DeltaStructure p T) (hF : F.IsPerfect) (f : B →+* T) (hf : E.IsDeltaHom F f)
variable (hp : IsModuleComplete T (p : T) (ModuleCat.of T T))
variable (hd : IsModuleComplete T (f b) (ModuleCat.of T T))
include hF hf hp hd

/-- δ完全化の直接PD完備化から、同じ完全なp,f(b)完備δ試験環への一意延長（BS 著者版 Lemma 3.9 の完全化と導来完備化を通る δ 射）。 -/
theorem existsUnique_deltaPerfectionPDCompletionHom :
    letI := pdCompletionCommRing (DeltaPerfection E) p (deltaPerfectionOf E 0 b)
    ∃! g : PDCompletionH0 (DeltaPerfection E) p (deltaPerfectionOf E 0 b) →+* T,
      (deltaPDCompletionStructure (deltaPerfectionStructure E) (deltaPerfectionOf E 0 b)).IsDeltaHom
        F g ∧
      g.comp ((pdCompletionUnit (DeltaPerfection E) p (deltaPerfectionOf E 0 b)).comp
        (deltaPerfectionOf E 0)) = f := by
  let := pdCompletionCommRing (DeltaPerfection E) p (deltaPerfectionOf E 0 b)
  obtain ⟨k, hk, _⟩ := existsUnique_deltaPerfectionHom E F hF f hf
  have hkb : k (deltaPerfectionOf E 0 b) = f b := RingHom.congr_fun hk.2 b
  have hdk : IsModuleComplete T (k (deltaPerfectionOf E 0 b)) (ModuleCat.of T T) := by
    rw [hkb]
    exact hd
  obtain ⟨g, hg, hgu⟩ := existsUnique_deltaPDCompletionHom
    (deltaPerfectionStructure E) (deltaPerfectionOf E 0 b) F k hk.1 hp hdk
  refine ⟨g, ⟨hg.1, ?_⟩, ?_⟩
  · rw [← RingHom.comp_assoc, hg.2, hk.2]
  · intro l hl
    have hlk : l.comp (pdCompletionUnit (DeltaPerfection E) p (deltaPerfectionOf E 0 b)) = k := by
      apply deltaPerfectionHom_ext E F hF _ _
        (hl.1.comp (pdCompletionUnit_isDeltaHom _ _)) hk.1
      simpa only [RingHom.comp_assoc, hk.2] using hl.2
    exact hgu l ⟨hl.1, hlk⟩

/-- p完備化を先に施す既存候補も、同じ完全なp,f(b)完備δ試験環への普遍性を持つ。 -/
theorem existsUnique_pCompletedDeltaPerfectionPDCompletionHom :
    letI := pdCompletionCommRing (PCompletedDeltaPerfection E) p (pCompletedDeltaPerfectionMap E b)
    ∃! g : PDCompletionH0 (PCompletedDeltaPerfection E) p (pCompletedDeltaPerfectionMap E b) →+* T,
      (deltaPDCompletionStructure (pCompletedDeltaPerfectionStructure E)
        (pCompletedDeltaPerfectionMap E b)).IsDeltaHom F g ∧
      g.comp ((pdCompletionUnit (PCompletedDeltaPerfection E) p
        (pCompletedDeltaPerfectionMap E b)).comp (pCompletedDeltaPerfectionMap E)) = f := by
  let := pdCompletionCommRing (PCompletedDeltaPerfection E) p (pCompletedDeltaPerfectionMap E b)
  let : IsAdicComplete (Ideal.span {(p : T)}) T :=
    (isRingModuleComplete_iff_isAdicComplete_natCast T p hF.p_mul_injective).mp hp
  obtain ⟨k, hk, hku⟩ := existsUnique_pCompletedDeltaPerfectionHom E F hF f hf
  have hkb : k (pCompletedDeltaPerfectionMap E b) = f b := RingHom.congr_fun hk.2 b
  have hdk : IsModuleComplete T (k (pCompletedDeltaPerfectionMap E b)) (ModuleCat.of T T) := by
    rw [hkb]
    exact hd
  obtain ⟨g, hg, hgu⟩ := existsUnique_deltaPDCompletionHom
    (pCompletedDeltaPerfectionStructure E) (pCompletedDeltaPerfectionMap E b) F k hk.1 hp hdk
  refine ⟨g, ⟨hg.1, ?_⟩, ?_⟩
  · rw [← RingHom.comp_assoc, hg.2, hk.2]
  · intro l hl
    have hlk : l.comp
        (pdCompletionUnit (PCompletedDeltaPerfection E) p
          (pCompletedDeltaPerfectionMap E b)) = k := by
      apply hku
      exact ⟨hl.1.comp (pdCompletionUnit_isDeltaHom _ _),
        by simpa only [RingHom.comp_assoc] using hl.2⟩
    exact hgu l ⟨hl.1, hlk⟩

/-- 直接PD完備化からのδ射は、元の環からの合成標準単位上で決まる。 -/
theorem deltaPerfectionPDCompletionHom_ext :
    letI := pdCompletionCommRing (DeltaPerfection E) p (deltaPerfectionOf E 0 b)
    ∀ g k : PDCompletionH0 (DeltaPerfection E) p (deltaPerfectionOf E 0 b) →+* T,
      (deltaPDCompletionStructure (deltaPerfectionStructure E) (deltaPerfectionOf E 0 b)).IsDeltaHom
        F g →
      (deltaPDCompletionStructure (deltaPerfectionStructure E) (deltaPerfectionOf E 0 b)).IsDeltaHom
        F k →
      g.comp ((pdCompletionUnit (DeltaPerfection E) p (deltaPerfectionOf E 0 b)).comp
        (deltaPerfectionOf E 0)) = f →
      k.comp ((pdCompletionUnit (DeltaPerfection E) p (deltaPerfectionOf E 0 b)).comp
        (deltaPerfectionOf E 0)) = f → g = k := by
  let := pdCompletionCommRing (DeltaPerfection E) p (deltaPerfectionOf E 0 b)
  obtain ⟨_, _, hu⟩ := existsUnique_deltaPerfectionPDCompletionHom E b F hF f hf hp hd
  intro g k hg hk hgf hkf
  exact (hu g ⟨hg, hgf⟩).trans (hu k ⟨hk, hkf⟩).symm

/-- p先行PD完備化からのδ射も、元の環からの合成標準単位上で決まる。 -/
theorem pCompletedDeltaPerfectionPDCompletionHom_ext :
    letI := pdCompletionCommRing (PCompletedDeltaPerfection E) p (pCompletedDeltaPerfectionMap E b)
    ∀ g k : PDCompletionH0 (PCompletedDeltaPerfection E) p (pCompletedDeltaPerfectionMap E b) →+* T,
      (deltaPDCompletionStructure (pCompletedDeltaPerfectionStructure E)
        (pCompletedDeltaPerfectionMap E b)).IsDeltaHom F g →
      (deltaPDCompletionStructure (pCompletedDeltaPerfectionStructure E)
        (pCompletedDeltaPerfectionMap E b)).IsDeltaHom F k →
      g.comp ((pdCompletionUnit (PCompletedDeltaPerfection E) p
        (pCompletedDeltaPerfectionMap E b)).comp (pCompletedDeltaPerfectionMap E)) = f →
      k.comp ((pdCompletionUnit (PCompletedDeltaPerfection E) p
        (pCompletedDeltaPerfectionMap E b)).comp (pCompletedDeltaPerfectionMap E)) = f → g = k := by
  let := pdCompletionCommRing (PCompletedDeltaPerfection E) p (pCompletedDeltaPerfectionMap E b)
  obtain ⟨_, _, hu⟩ := existsUnique_pCompletedDeltaPerfectionPDCompletionHom E b F hF f hf hp hd
  intro g k hg hk hgf hkf
  exact (hu g ⟨hg, hgf⟩).trans (hu k ⟨hk, hkf⟩).symm

end SerrePositivity.BhattScholze

end DeltaPerfectionPDCompletionUniversal

/-! ## PD完備化を先に挟んだδ完全化の同じ試験環への普遍性 -/

@[expose] public noncomputable section DeltaPDCompletionPerfectionUniversal

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {B T : Type u} [CommRing B] [CommRing T]
variable (E : DeltaStructure p B) (b : B)
variable (F : DeltaStructure p T) (hF : F.IsPerfect) (f : B →+* T) (hf : E.IsDeltaHom F f)
variable (hp : IsModuleComplete T (p : T) (ModuleCat.of T T))
variable (hd : IsModuleComplete T (f b) (ModuleCat.of T T))
local notation "S" => PDCompletionH0 B p b
local notation "G" => deltaPDCompletionStructure E b
local notation "v" => pdCompletionUnit B p b
local notation "C" => DeltaPerfection G
local notation "x" => deltaPerfectionOf G 0 (v b)
local notation "r" => RingHom.comp (pdCompletionUnit C p x) (deltaPerfectionOf G 0)
include hF hf hp hd

/-- 実PD完備化を先に挟んでも、元Bから同じ完全p,f(b)完備δ試験環への一意延長を得る。 -/
theorem existsUnique_deltaPDCompletionPerfectionPDHom :
    letI := pdCompletionCommRing B p b
    letI := pdCompletionCommRing C p x
    ∃! g : PDCompletionH0 C p x →+* T,
      (deltaPDCompletionStructure (deltaPerfectionStructure G) x).IsDeltaHom F g ∧
        g.comp ((r).comp v) = f := by
  let := pdCompletionCommRing B p b
  let := pdCompletionCommRing C p x
  obtain ⟨k, hk, hku⟩ := existsUnique_deltaPDCompletionHom E b F f hf hp hd
  have hkb : k (v b) = f b := RingHom.congr_fun hk.2 b
  have hdk : IsModuleComplete T (k (v b)) (ModuleCat.of T T) := by
    rw [hkb]
    exact hd
  obtain ⟨g, hg, hgu⟩ := existsUnique_deltaPerfectionPDCompletionHom G (v b) F hF k hk.1 hp hdk
  refine ⟨g, ⟨hg.1, ?_⟩, ?_⟩
  · rw [← RingHom.comp_assoc, hg.2, hk.2]
  · intro l hl
    have hlk : l.comp r = k := by
      apply hku
      refine ⟨hl.1.comp ?_, ?_⟩
      · exact (pdCompletionUnit_isDeltaHom _ _).comp (deltaPerfectionOf_isDeltaHom G 0)
      · simpa only [RingHom.comp_assoc] using hl.2
    exact hgu l ⟨hl.1, hlk⟩

end SerrePositivity.BhattScholze

end DeltaPDCompletionPerfectionUniversal

/-! ## δ完全化の直接PD完備化と既存p先行候補の標準環同型 -/

@[expose] public noncomputable section DeltaPerfectionPDCompletionComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
variable (E : DeltaStructure p B) (b : B)
local notation "C" => DeltaPerfection E
local notation "P" => PCompletedDeltaPerfection E
local notation "x" => deltaPerfectionOf E 0 b
local notation "y" => pCompletedDeltaPerfectionMap E b
local notation "H₀" => PDCompletionH0 C p x
local notation "H₁" => PDCompletionH0 P p y
local notation "D₀" => deltaPDCompletionStructure (deltaPerfectionStructure E) x
local notation "D₁" => deltaPDCompletionStructure (pCompletedDeltaPerfectionStructure E) y
local notation "r₀" => RingHom.comp (pdCompletionUnit C p x) (deltaPerfectionOf E 0)
local notation "r₁" => RingHom.comp (pdCompletionUnit P p y) (pCompletedDeltaPerfectionMap E)

/-- 直接PD完備化から、既存のp先行PD完備化への標準δ射。 -/
def deltaPerfectionPDCompletionComparison :
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing P p y
    H₀ →+* H₁ := by
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing P p y
  exact (existsUnique_deltaPerfectionPDCompletionHom E b D₁
    (deltaPDCompletionStructure_isPerfect _ (pCompletedDeltaPerfection_isPerfect E) y)
    r₁ ((pdCompletionUnit_isDeltaHom _ _).comp (pCompletedDeltaPerfectionMap_isDeltaHom E))
    (pdCompletionH0_self_complete_p P p y) (pdCompletionH0_self_complete_d P p y)).choose

/-- 標準比較はδ射であり、元Bからの標準射を保つ。 -/
theorem deltaPerfectionPDCompletionComparison_spec :
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing P p y
    (D₀).IsDeltaHom D₁ (deltaPerfectionPDCompletionComparison E b) ∧
      (deltaPerfectionPDCompletionComparison E b).comp r₀ = r₁ := by
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing P p y
  exact (existsUnique_deltaPerfectionPDCompletionHom E b D₁
    (deltaPDCompletionStructure_isPerfect _ (pCompletedDeltaPerfection_isPerfect E) y)
    r₁ ((pdCompletionUnit_isDeltaHom _ _).comp (pCompletedDeltaPerfectionMap_isDeltaHom E))
    (pdCompletionH0_self_complete_p P p y) (pdCompletionH0_self_complete_d P p y)).choose_spec.1

/-- 既存のp先行候補から直接PD完備化へ戻る標準δ射。 -/
def deltaPerfectionPDCompletionInverse :
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing P p y
    H₁ →+* H₀ := by
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing P p y
  exact (existsUnique_pCompletedDeltaPerfectionPDCompletionHom E b D₀
    (deltaPDCompletionStructure_isPerfect _ (deltaPerfection_isPerfect E) x)
    r₀ ((pdCompletionUnit_isDeltaHom _ _).comp (deltaPerfectionOf_isDeltaHom E 0))
    (pdCompletionH0_self_complete_p C p x) (pdCompletionH0_self_complete_d C p x)).choose

/-- 逆方向の標準射もδ射であり、同じ元Bの標準射を保つ。 -/
theorem deltaPerfectionPDCompletionInverse_spec :
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing P p y
    (D₁).IsDeltaHom D₀ (deltaPerfectionPDCompletionInverse E b) ∧
      (deltaPerfectionPDCompletionInverse E b).comp r₁ = r₀ := by
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing P p y
  exact (existsUnique_pCompletedDeltaPerfectionPDCompletionHom E b D₀
    (deltaPDCompletionStructure_isPerfect _ (deltaPerfection_isPerfect E) x)
    r₀ ((pdCompletionUnit_isDeltaHom _ _).comp (deltaPerfectionOf_isDeltaHom E 0))
    (pdCompletionH0_self_complete_p C p x) (pdCompletionH0_self_complete_d C p x)).choose_spec.1

/-- 直接PD完備化と既存p先行候補は、具体的な両標準δ射により環同型。 -/
def deltaPerfectionPDCompletionEquiv :
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing P p y
    H₀ ≃+* H₁ := by
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing P p y
  let f := deltaPerfectionPDCompletionComparison E b
  let g := deltaPerfectionPDCompletionInverse E b
  have hf := deltaPerfectionPDCompletionComparison_spec E b
  have hg := deltaPerfectionPDCompletionInverse_spec E b
  have hgf : g.comp f = RingHom.id H₀ := by
    apply deltaPerfectionPDCompletionHom_ext E b D₀
      (deltaPDCompletionStructure_isPerfect _ (deltaPerfection_isPerfect E) x)
      r₀ ((pdCompletionUnit_isDeltaHom _ _).comp (deltaPerfectionOf_isDeltaHom E 0))
      (pdCompletionH0_self_complete_p C p x) (pdCompletionH0_self_complete_d C p x)
      (g.comp f) (RingHom.id H₀) (hg.1.comp hf.1) (D₀).isDeltaHom_id ?_ (RingHom.id_comp r₀)
    rw [RingHom.comp_assoc, hf.2, hg.2]
  have hfg : f.comp g = RingHom.id H₁ := by
    apply pCompletedDeltaPerfectionPDCompletionHom_ext E b D₁
      (deltaPDCompletionStructure_isPerfect _ (pCompletedDeltaPerfection_isPerfect E) y)
      r₁ ((pdCompletionUnit_isDeltaHom _ _).comp (pCompletedDeltaPerfectionMap_isDeltaHom E))
      (pdCompletionH0_self_complete_p P p y) (pdCompletionH0_self_complete_d P p y)
      (f.comp g) (RingHom.id H₁) (hf.1.comp hg.1) (D₁).isDeltaHom_id ?_ (RingHom.id_comp r₁)
    rw [RingHom.comp_assoc, hg.2, hf.2]
  exact RingEquiv.ofRingHom f g hfg hgf

/-- この環同型の両方向はδ射であり、元の標準raw射を保つ。 -/
theorem deltaPerfectionPDCompletionEquiv_spec :
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing P p y
    (D₀).IsDeltaHom D₁ (deltaPerfectionPDCompletionEquiv E b).toRingHom ∧
      (D₁).IsDeltaHom D₀ (deltaPerfectionPDCompletionEquiv E b).symm.toRingHom ∧
      (deltaPerfectionPDCompletionEquiv E b).toRingHom.comp r₀ = r₁ := by
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing P p y
  exact ⟨(deltaPerfectionPDCompletionComparison_spec E b).1,
    (deltaPerfectionPDCompletionInverse_spec E b).1,
    (deltaPerfectionPDCompletionComparison_spec E b).2⟩

end SerrePositivity.BhattScholze

end DeltaPerfectionPDCompletionComparison

/-! ## PD完備化をδ完全化の前へ挟む手順との標準環同型 -/

@[expose] public noncomputable section DeltaPDCompletionPerfectionComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
variable (E : DeltaStructure p B) (b : B)
local notation "C" => DeltaPerfection E
local notation "S" => PDCompletionH0 B p b
local notation "G" => deltaPDCompletionStructure E b
local notation "v" => pdCompletionUnit B p b
local notation "P" => DeltaPerfection G
local notation "x" => deltaPerfectionOf E 0 b
local notation "y" => deltaPerfectionOf G 0 (v b)
local notation "H₀" => PDCompletionH0 C p x
local notation "H₁" => PDCompletionH0 P p y
local notation "D₀" => deltaPDCompletionStructure (deltaPerfectionStructure E) x
local notation "D₁" => deltaPDCompletionStructure (deltaPerfectionStructure G) y
local notation "r₀" => RingHom.comp (pdCompletionUnit C p x) (deltaPerfectionOf E 0)
local notation "r₁" => RingHom.comp
  (RingHom.comp (pdCompletionUnit P p y) (deltaPerfectionOf G 0)) v

/-- 直接PD完備化から、PD先行δ完全化後のPD完備化への標準δ射。 -/
def deltaPDCompletionPerfectionComparison :
    letI := pdCompletionCommRing B p b
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing P p y
    H₀ →+* H₁ := by
  let := pdCompletionCommRing B p b
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing P p y
  exact (existsUnique_deltaPerfectionPDCompletionHom E b D₁
    (deltaPDCompletionStructure_isPerfect _ (deltaPerfection_isPerfect G) y)
    r₁ (((pdCompletionUnit_isDeltaHom _ _).comp (deltaPerfectionOf_isDeltaHom G 0)).comp
      (pdCompletionUnit_isDeltaHom E b))
    (pdCompletionH0_self_complete_p P p y) (pdCompletionH0_self_complete_d P p y)).choose

/-- 標準比較はδ射であり、元Bからの標準射を保つ。 -/
theorem deltaPDCompletionPerfectionComparison_spec :
    letI := pdCompletionCommRing B p b
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing P p y
    (D₀).IsDeltaHom D₁ (deltaPDCompletionPerfectionComparison E b) ∧
      (deltaPDCompletionPerfectionComparison E b).comp r₀ = r₁ := by
  let := pdCompletionCommRing B p b
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing P p y
  exact (existsUnique_deltaPerfectionPDCompletionHom E b D₁
    (deltaPDCompletionStructure_isPerfect _ (deltaPerfection_isPerfect G) y)
    r₁ (((pdCompletionUnit_isDeltaHom _ _).comp (deltaPerfectionOf_isDeltaHom G 0)).comp
      (pdCompletionUnit_isDeltaHom E b))
    (pdCompletionH0_self_complete_p P p y) (pdCompletionH0_self_complete_d P p y)).choose_spec.1

/-- PD先行δ完全化後の候補から直接PD完備化へ戻る標準δ射。 -/
def deltaPDCompletionPerfectionInverse :
    letI := pdCompletionCommRing B p b
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing P p y
    H₁ →+* H₀ := by
  let := pdCompletionCommRing B p b
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing P p y
  exact (existsUnique_deltaPDCompletionPerfectionPDHom E b D₀
    (deltaPDCompletionStructure_isPerfect _ (deltaPerfection_isPerfect E) x)
    r₀ ((pdCompletionUnit_isDeltaHom _ _).comp (deltaPerfectionOf_isDeltaHom E 0))
    (pdCompletionH0_self_complete_p C p x) (pdCompletionH0_self_complete_d C p x)).choose

/-- 逆方向の標準射もδ射であり、同じ元Bの標準射を保つ。 -/
theorem deltaPDCompletionPerfectionInverse_spec :
    letI := pdCompletionCommRing B p b
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing P p y
    (D₁).IsDeltaHom D₀ (deltaPDCompletionPerfectionInverse E b) ∧
      (deltaPDCompletionPerfectionInverse E b).comp r₁ = r₀ := by
  let := pdCompletionCommRing B p b
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing P p y
  exact (existsUnique_deltaPDCompletionPerfectionPDHom E b D₀
    (deltaPDCompletionStructure_isPerfect _ (deltaPerfection_isPerfect E) x)
    r₀ ((pdCompletionUnit_isDeltaHom _ _).comp (deltaPerfectionOf_isDeltaHom E 0))
    (pdCompletionH0_self_complete_p C p x) (pdCompletionH0_self_complete_d C p x)).choose_spec.1

/-- 直接PD完備化とPD先行δ完全化後の候補は、具体的な両標準δ射により環同型。 -/
def deltaPDCompletionPerfectionEquiv :
    letI := pdCompletionCommRing B p b
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing P p y
    H₀ ≃+* H₁ := by
  let := pdCompletionCommRing B p b
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing P p y
  let f := deltaPDCompletionPerfectionComparison E b
  let g := deltaPDCompletionPerfectionInverse E b
  have hf := deltaPDCompletionPerfectionComparison_spec E b
  have hg := deltaPDCompletionPerfectionInverse_spec E b
  have hgf : g.comp f = RingHom.id H₀ := by
    obtain ⟨_, _, hu₀⟩ := existsUnique_deltaPerfectionPDCompletionHom E b D₀
      (deltaPDCompletionStructure_isPerfect _ (deltaPerfection_isPerfect E) x)
      r₀ ((pdCompletionUnit_isDeltaHom _ _).comp (deltaPerfectionOf_isDeltaHom E 0))
      (pdCompletionH0_self_complete_p C p x) (pdCompletionH0_self_complete_d C p x)
    apply (hu₀ (g.comp f) ⟨hg.1.comp hf.1, ?_⟩).trans
      (hu₀ (RingHom.id H₀) ⟨(D₀).isDeltaHom_id, RingHom.id_comp r₀⟩).symm
    rw [RingHom.comp_assoc, hf.2, hg.2]
  have hfg : f.comp g = RingHom.id H₁ := by
    obtain ⟨_, _, hu₁⟩ := existsUnique_deltaPDCompletionPerfectionPDHom E b D₁
      (deltaPDCompletionStructure_isPerfect _ (deltaPerfection_isPerfect G) y)
      r₁ (((pdCompletionUnit_isDeltaHom _ _).comp (deltaPerfectionOf_isDeltaHom G 0)).comp
        (pdCompletionUnit_isDeltaHom E b))
      (pdCompletionH0_self_complete_p P p y) (pdCompletionH0_self_complete_d P p y)
    apply (hu₁ (f.comp g) ⟨hf.1.comp hg.1, ?_⟩).trans
      (hu₁ (RingHom.id H₁) ⟨(D₁).isDeltaHom_id, RingHom.id_comp r₁⟩).symm
    rw [RingHom.comp_assoc, hg.2, hf.2]
  exact RingEquiv.ofRingHom f g hfg hgf

/-- この環同型の両方向はδ射であり、元の標準raw射を保つ。 -/
theorem deltaPDCompletionPerfectionEquiv_spec :
    letI := pdCompletionCommRing B p b
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing P p y
    (D₀).IsDeltaHom D₁ (deltaPDCompletionPerfectionEquiv E b).toRingHom ∧
      (D₁).IsDeltaHom D₀ (deltaPDCompletionPerfectionEquiv E b).symm.toRingHom ∧
      (deltaPDCompletionPerfectionEquiv E b).toRingHom.comp r₀ = r₁ := by
  let := pdCompletionCommRing B p b
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing P p y
  exact ⟨(deltaPDCompletionPerfectionComparison_spec E b).1,
    (deltaPDCompletionPerfectionInverse_spec E b).1,
    (deltaPDCompletionPerfectionComparison_spec E b).2⟩

/-- 同じ標準環同型は、元の元bの両完備化後の像を保つ。 -/
theorem deltaPDCompletionPerfectionEquiv_generator :
    letI := pdCompletionCommRing B p b
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing P p y
    deltaPDCompletionPerfectionEquiv E b (pdCompletionUnit C p x x) =
      pdCompletionUnit P p y y := by
  let := pdCompletionCommRing B p b
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing P p y
  exact RingHom.congr_fun (deltaPDCompletionPerfectionEquiv_spec E b).2.2 b

/-- 両手順の同じ標準生成元商も、元の標準環同型により同型。 -/
def deltaPDCompletionPerfectionQuotientEquiv :
    letI := pdCompletionCommRing B p b
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing P p y
    (H₀ ⧸ Ideal.span {(pdCompletionUnit C p x x)}) ≃+*
      (H₁ ⧸ Ideal.span {(pdCompletionUnit P p y y)}) := by
  let := pdCompletionCommRing B p b
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing P p y
  exact Ideal.quotientEquiv _ _ (deltaPDCompletionPerfectionEquiv E b) (by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {(pdCompletionUnit P p y y)} =
      Ideal.span {(deltaPDCompletionPerfectionEquiv E b (pdCompletionUnit C p x x))}
    rw [deltaPDCompletionPerfectionEquiv_generator])

/-- 商環同型は、各代表元に両手順の標準環同型を適用する。 -/
theorem deltaPDCompletionPerfectionQuotientEquiv_mk :
    letI := pdCompletionCommRing B p b
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing P p y
    ∀ h : H₀, deltaPDCompletionPerfectionQuotientEquiv E b (Ideal.Quotient.mk _ h) =
      Ideal.Quotient.mk _ (deltaPDCompletionPerfectionEquiv E b h) := by
  let := pdCompletionCommRing B p b
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing P p y
  intro h
  rfl

/-- 商比較も、元Bからの両標準係数射を保つ。 -/
theorem deltaPDCompletionPerfectionQuotientEquiv_comp_raw :
    letI := pdCompletionCommRing B p b
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing P p y
    (deltaPDCompletionPerfectionQuotientEquiv E b).toRingHom.comp
        ((Ideal.Quotient.mk (Ideal.span {(pdCompletionUnit C p x x)})).comp r₀) =
      (Ideal.Quotient.mk (Ideal.span {(pdCompletionUnit P p y y)})).comp r₁ := by
  let := pdCompletionCommRing B p b
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing P p y
  apply RingHom.ext
  intro a
  change Ideal.Quotient.mk (Ideal.span {(pdCompletionUnit P p y y)})
    (deltaPDCompletionPerfectionEquiv E b (r₀ a)) =
      Ideal.Quotient.mk (Ideal.span {(pdCompletionUnit P p y y)}) (r₁ a)
  exact congrArg (Ideal.Quotient.mk (Ideal.span {(pdCompletionUnit P p y y)}))
    (RingHom.congr_fun (deltaPDCompletionPerfectionEquiv_spec E b).2.2 a)

end SerrePositivity.BhattScholze

end DeltaPDCompletionPerfectionComparison

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Lemma 3.9" (partial := special) "向き付き prism の場合に原典の形の定理がある（BS-W17）：classicalPrismPerfection（δ 完全化の (p,d) 完備化 H⁰、完全・有界）と、完全 prism への射についての普遍性 existsUnique_classicalPrismPerfectionHom。源の完全性は仮定しない。部品（完全δ環＋distinguished 元の PD 完備化が完全 prism で普遍、完全化と完備化の順序比較）も本体。付随の主張は一つの定理には入っていない。p 進完備化した段での正則性などは PCompletedPerfection:124–145 に別の定理としてある。未完備の A_perf についての主張と、導来と古典的完備化の一致は本体にない。PCompleted 版は d 進完備性を仮定。A3/A5 の始完全 prism で使う ／ DOC1 照合（11-07、Codex が型で確認）：項目そのものではないので宣言の列から外したもの：deltaPDCompletionPerfectionEquiv（原文の古典完備化との一致や普遍性とは別の比較同型。module docstring の関連を残す。） ／ DOC1 照合：ok 3 件 ／ 11-12 夜更新 ／ 11-12 夜更新（§3 の見直し）"] _root_.SerrePositivity.BhattScholze.existsUnique_deltaPerfectionPDCompletionHom
attribute [cite BS19 "Lemma 3.9" (partial := special) "向き付き prism の場合に原典の形の定理がある（BS-W17）：classicalPrismPerfection（δ 完全化の (p,d) 完備化 H⁰、完全・有界）と、完全 prism への射についての普遍性 existsUnique_classicalPrismPerfectionHom。源の完全性は仮定しない。部品（完全δ環＋distinguished 元の PD 完備化が完全 prism で普遍、完全化と完備化の順序比較）も本体。付随の主張は一つの定理には入っていない。p 進完備化した段での正則性などは PCompletedPerfection:124–145 に別の定理としてある。未完備の A_perf についての主張と、導来と古典的完備化の一致は本体にない。PCompleted 版は d 進完備性を仮定。A3/A5 の始完全 prism で使う ／ DOC1 照合（11-07、Codex が型で確認）：項目そのものではないので宣言の列から外したもの：deltaPDCompletionPerfectionEquiv（原文の古典完備化との一致や普遍性とは別の比較同型。module docstring の関連を残す。） ／ DOC1 照合：ok 3 件 ／ 11-12 夜更新 ／ 11-12 夜更新（§3 の見直し）"] _root_.SerrePositivity.BhattScholze.existsUnique_perfectDeltaPDPrismHom
