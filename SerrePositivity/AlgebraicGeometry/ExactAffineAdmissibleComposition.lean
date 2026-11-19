module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.AffineAdmissibleComposition

/-!
概要：KST §5、Stacks 080Y の二段 blowup を、中心外が指定の基本開に一致する一つの blowup で支配する。
方針：既証の admissible な合成支配の中心へ単項イデアルを掛け、左比較射を合成する。
規約：中心外の一致は元の Spec 上で述べ、第二段の対象を保持する。
使われ方：一般階数を分離した二段の自由化中心を元の基礎環上で支配する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/--
概要：単項中心の補開集合は生成元の基本開集合。
方針：素イデアルへの単項イデアルの包含を生成元の所属で判定する。
規約：KST §5、Stacks 080Y、生成元の正則性は不要。
使われ方：admissible な中心の補開集合を指定の基本開へ揃える。
-/
theorem affineCenterComplement_span_singleton {R : Type u} [CommRing R] (f : R) :
    affineCenterComplement (Ideal.span {f}) = PrimeSpectrum.basicOpen f := by
  ext x
  change (x : PrimeSpectrum R) ∈ affineCenterComplement (Ideal.span {f}) ↔
    x ∈ PrimeSpectrum.basicOpen f
  rw [mem_affineCenterComplement]
  change (¬ Ideal.span {f} ≤ x.asIdeal) ↔ f ∉ x.asIdeal
  rw [Ideal.span_le, Set.singleton_subset_iff]
  rfl

/--
概要：D(f) 上の二段の admissible blowup は中心外がちょうど D(f) の一つの blowup で支配される。
方針：合成支配で得た中心に (f) を掛け、積中心からの左比較射を使う。
規約：KST §5、Stacks 080Y、基底環は Noether、可換式は元の基底上で述べる。
使われ方：二段自由化中心への支配射を元の基礎環上に構成する。
-/
theorem exists_affine_exact_admissible_composition_domination
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (L : (affineBlowup I).IdealSheafData) (f : R)
    (hI : PrimeSpectrum.basicOpen f ≤ affineCenterComplement I)
    (hL : affineBlowupπ I ⁻¹ᵁ PrimeSpectrum.basicOpen f ≤ centerComplement L) :
    ∃ K : Ideal R, K.FG ∧ affineCenterComplement K = PrimeSpectrum.basicOpen f ∧
      ∃ g : affineBlowup K ⟶ blowup L,
        g ≫ blowupπ L ≫ affineBlowupπ I = affineBlowupπ K := by
  obtain ⟨K, hfg, hKU, g, hg⟩ :=
    exists_affine_admissible_composition_domination I L (PrimeSpectrum.basicOpen f) hI hL
  refine ⟨K * Ideal.span {f}, Ideal.fg_of_isNoetherianRing _, ?_,
    affineBlowupProductLeftMap K (Ideal.span {f}) ≫ g, ?_⟩
  · rw [affineCenterComplement_mul, affineCenterComplement_span_singleton, inf_eq_right.mpr hKU]
  · rw [Category.assoc, hg, affineBlowupProductLeftMap_base]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
