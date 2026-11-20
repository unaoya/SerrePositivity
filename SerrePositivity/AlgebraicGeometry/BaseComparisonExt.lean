module

public import SerrePositivity.AlgebraicGeometry.BaseChangeChartCover
public import SerrePositivity.AlgebraicGeometry.ChartGluing

/-!
概要：KST §5 の係数環を変えたアフィン blowup からの比較射の一意性。
方針：元の中心元の像によるチャート被覆と非零因子局所化で一致を検出する。
規約：標的は元の基底上で分離かつ中心の外で同型。
使われ方：冪比較同型とアフィン開包含の比較との自然性。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
variable {R S : Type u} [CommRing R] [CommRing S] (I : Ideal R) (f : R →+* S)

set_option backward.isDefEq.respectTransparency false in
/--
概要：像中心の blowup から、元の基底上で中心外同型な分離標的への射は基底上で一意。
方針：元の中心元の像のチャートを非零因子で局所化し、その零核で一致を検出する。
規約：KST §5、係数環準同型の平坦性や全射性は不要。
使われ方：正の冪の blowup 同型の自然性と大域化。
-/
theorem affineBlowupBase_hom_ext {Y : Scheme.{u}} (s : Y ⟶ Spec (.of R))
    [IsSeparated s] (hs : ∀ a : I, IsIso (s ∣_ PrimeSpectrum.basicOpen a.1))
    {g h : affineBlowup (I.map f) ⟶ Y}
    (hg : g ≫ s = affineBlowupπ (I.map f) ≫ Spec.map (CommRingCat.ofHom f))
    (hh : h ≫ s = affineBlowupπ (I.map f) ≫ Spec.map (CommRingCat.ofHom f)) : g = h := by
  apply (affineBlowupImageChartCover I f).openCover.hom_ext
  intro a
  let b := centerImageElement I (I.map f) f le_rfl a
  change affineBlowupChartι (I.map f) b ≫ g = affineBlowupChartι (I.map f) b ≫ h
  have := hs a
  apply hom_ext_of_ker_eq_bot_of_separated s
    (by simp only [Category.assoc, hg, hh]) (chartLocalizationι (I.map f) b)
    (chartLocalizationι_ker_eq_bot (I.map f) b)
  apply hom_ext_of_isIso_restrict s (PrimeSpectrum.basicOpen a.1)
  · simp only [Category.assoc, hg, hh]
  · simp only [Category.assoc, hg]
    rintro _ ⟨x, rfl⟩
    exact chartLocalizationι_range_base (I.map f) b ⟨x, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/--
概要：像中心を別のイデアルとして同定した blowup からの基底上の比較射も一意。
方針：中心の等式で像中心の一意性へ移送する。
規約：KST §5、中心を別表示のイデアルとして保持する。
使われ方：冪比較同型とイデアル層の制限写像の自然性。
-/
theorem affineBlowupCenter_hom_ext (J : Ideal S) (hJ : I.map f = J)
    {Y : Scheme.{u}} (s : Y ⟶ Spec (.of R)) [IsSeparated s]
    (hs : ∀ a : I, IsIso (s ∣_ PrimeSpectrum.basicOpen a.1))
    {g h : affineBlowup J ⟶ Y}
    (hg : g ≫ s = affineBlowupπ J ≫ Spec.map (CommRingCat.ofHom f))
    (hh : h ≫ s = affineBlowupπ J ≫ Spec.map (CommRingCat.ofHom f)) : g = h := by
  subst J
  exact affineBlowupBase_hom_ext I f s hs hg hh

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
