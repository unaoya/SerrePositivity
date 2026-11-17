module

public import SerrePositivity.AlgebraicGeometry.ArcRouteB.BaseChangeComparison
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.CoverLaws
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.UniversalCech
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalSpectrum

/-!
概要：良い区間の部分区間への制限と、rank≤1の区間での普遍Čech完全性。
方針：同じ係数射の合成をL01で比較し、rank≤1では付値拡大上の切断から忠実平坦反映する。
規約：元の区間・底変換・付値拡大の階数を保つ。非平坦な制限でも普遍版を使う。
使われ方：2iのO08・I08、BM18 Lemma 4.7のsub法則・Proposition 4.8(2)。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory
open SerrePositivity
namespace SerrePositivity.AlgebraicGeometry.ArcRouteB

set_option backward.isDefEq.respectTransparency false

/-- 計画O08：同じ区間の普遍Čech完全性の局所法則。 -/
theorem goodArcInterval_sub (p : ℕ) {V B : Type u} [CommRing V] [CommRing B]
    (f : V →+* B) {a b c d : PrimeSpectrum V}
    (h : GoodArcInterval p f a b) (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    [PerfectRing (ValuationIntervalRing hcd) p] : GoodArcInterval p f c d := by
  intro h' T _ _ k
  let hab := hac.trans (hcd.trans hdb)
  let g1 := algebraMap V (ValuationIntervalRing hab)
  let g2 := algebraMap V (ValuationIntervalRing h')
  let r := intervalRingMap hab h' hac hdb
  have hr : r.comp g1 = g2 := RingHom.ext (intervalRingMap_algebraMap hab h' hac hdb)
  have hc : (k.comp r).comp g1 = k.comp g2 := by rw [RingHom.comp_assoc, hr]
  let e1 := arcBaseChangeTransIso f g1 (k.comp r) (k.comp g2) hc
  let e2 := arcBaseChangeTransIso f g2 k (k.comp g2) rfl
  have hR : Cech.IsCechExact (Arrow.mk (CommRingCat.ofHom
      (arcBaseChangeHom (arcBaseChangeHom f g1) (k.comp r)))) := h hab T (k.comp r)
  have hdirect := (Cech.ringCechExact_iff_of_iso
    (CosimplicialObject.augmentedCechConerve.mapIso e1)).mpr hR
  exact (Cech.ringCechExact_iff_of_iso
    (CosimplicialObject.augmentedCechConerve.mapIso e2)).mp hdirect

/-- 計画I08：同じ区間の普遍Čech完全性の局所法則。 -/
theorem goodArcInterval_of_rank_le_one (p : ℕ) [Fact p.Prime]
    {V B : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
    [CommRing B] [PerfectRing V p] [PerfectRing B p] (hp : (p : V) = 0)
    (f : V →+* B) (hf : IsArcHom f) {a b : PrimeSpectrum V} (h : a ≤ b)
    (hdim : ringKrullDim (ValuationIntervalRing h) ≤ 1) : GoodArcInterval p f a b := by
  intro h'
  let I := ValuationIntervalRing h'
  letI : ValuationRing I := valuationRing_interval h'
  have hd : ringKrullDim I ≤ 1 := hdim
  let q := arcBaseChangeHom f (algebraMap V I)
  have hq : IsArcHom q := isArcHom_baseChange f (algebraMap V I) hf
  obtain ⟨W, hW, hval, hdimW, e, l, he, hl⟩ :=
    hq (CommRingCat.of I) hd (RingHom.id I)
  exact perfectRingCechUniversalExact_of_flat_factor p q e l he
    (by simpa only [RingHom.comp_id] using hl)

end SerrePositivity.AlgebraicGeometry.ArcRouteB
