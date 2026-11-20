module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.ChartGluing
public import SerrePositivity.AlgebraicGeometry.IdealComplementPullback
public import SerrePositivity.AlgebraicGeometry.SchemeBlowupProper

/-!
概要：KST §5、Stacks 080Y の一般スキーム上の blowup を標的とするアフィン blowup からの射の一意性。
方針：標準チャートの正則局所化で零核を検出し、中心外の同型と分離性を使う。
規約：基底へ向かう局所射の開埋め込み性は不要。
使われ方：一般の開埋め込みによる blowup 比較射の大域構成。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/--
概要：逆像中心に沿うアフィン blowup から一般 blowup への射は基底上で一意。
方針：各標準チャートで正則な中心元を可逆化し、一般基底の中心外へ入ることを使う。
規約：KST §5、Stacks 080Y、逆像中心の環イデアルの等式を明示する。
使われ方：局所 blowup 比較射の包含に関する自然性。
-/
theorem affineBlowup_over_scheme_hom_ext {X : Scheme.{u}} {A : CommRingCat.{u}}
    (K : X.IdealSheafData) (j : Spec A ⟶ X) (I : Ideal A)
    (hI : specIdealEquiv A (K.comap j) = I) {g h : affineBlowup I ⟶ blowup K}
    (hg : g ≫ blowupπ K = affineBlowupπ I ≫ j)
    (hh : h ≫ blowupπ K = affineBlowupπ I ≫ j) : g = h := by
  have hC : affineCenterComplement I = j ⁻¹ᵁ centerComplement K := by
    rw [affine_preimage_centerComplement, hI]
  apply (affineBlowupChartCover I).openCover.hom_ext
  intro a
  change affineBlowupChartι I a ≫ g = affineBlowupChartι I a ≫ h
  apply hom_ext_of_ker_eq_bot_of_separated (blowupπ K)
    (by simp only [Category.assoc, hg, hh]) (chartLocalizationι I a)
    (chartLocalizationι_ker_eq_bot I a)
  have := blowupπ_restrict_complement_isIso K
  apply hom_ext_of_isIso_restrict (blowupπ K) (centerComplement K)
  · simp only [Category.assoc, hg, hh]
  · simp only [Category.assoc, hg]
    rintro _ ⟨x, rfl⟩
    have hx := chartLocalizationι_range_base I a ⟨x, rfl⟩
    have hxC : (chartLocalizationι I a ≫ affineBlowupChartι I a ≫ affineBlowupπ I) x ∈
        affineCenterComplement I :=
      (le_iSup (fun a : I => PrimeSpectrum.basicOpen a.1) a) hx
    rw [hC] at hxC
    exact hxC

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
