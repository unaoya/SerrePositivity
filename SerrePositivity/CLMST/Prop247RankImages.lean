module

public import SerrePositivity.CLMST.Prop247RankLoci
public import SerrePositivity.CommutativeAlgebra.ReducedSpectrum
public import Mathlib.RingTheory.Finiteness.Basic

/-! # Prop 2.4.7：rank 別開集合の切断への元の像と閉包

原典の Ri を、元の R→Γ(Ui,O) の像として固定する。
その有限性と閉包を表すことは perfectoid 化や Cor 8.12 を使わない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open TopologicalSpace Opposite AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 原典の R→Γ(U,O) の像の環。 -/
abbrev prop247_openSectionImage (R : Type u) [CommRing R] (U : Opens (PrimeSpectrum R)) : Type u :=
  (Algebra.ofId R ((Spec.structureSheaf R).obj.obj (op U))).range

/-- 切断への元の写像を像に制限した実環写像。 -/
abbrev prop247_toOpenSectionImage (R : Type u) [CommRing R] (U : Opens (PrimeSpectrum R)) :
    R →ₐ[R] prop247_openSectionImage R U :=
  (Algebra.ofId R ((Spec.structureSheaf R).obj.obj (op U))).rangeRestrict

theorem prop247_toOpenSectionImage_surjective
    (R : Type u) [CommRing R] (U : Opens (PrimeSpectrum R)) :
    Function.Surjective (prop247_toOpenSectionImage R U) :=
  AlgHom.rangeRestrict_surjective _

/-- 原典の像の環は R の商であり、R 上有限である。 -/
theorem prop247_openSectionImage_finite
    (R : Type u) [CommRing R] (U : Opens (PrimeSpectrum R)) :
    Module.Finite R (prop247_openSectionImage R U) :=
  Module.Finite.of_surjective (prop247_toOpenSectionImage R U).toLinearMap
    (prop247_toOpenSectionImage_surjective R U)

/-- 被約な基底では、像への元の写像の核は開集合の消滅イデアルである。 -/
theorem prop247_toOpenSectionImage_ker
    (R : Type u) [CommRing R] [IsReduced R] (U : Opens (PrimeSpectrum R)) :
    RingHom.ker (prop247_toOpenSectionImage R U).toRingHom =
      PrimeSpectrum.vanishingIdeal (U : Set (PrimeSpectrum R)) :=
  (AlgHom.ker_rangeRestrict (Algebra.ofId R ((Spec.structureSheaf R).obj.obj (op U)))).trans
    (ker_algebraMap_sections_eq_vanishingIdeal R U)

/-- 閉包の消滅イデアルによる商と、原典の切断への像との同型。 -/
def prop247_openSectionImageQuotientEquiv
    (R : Type u) [CommRing R] [IsReduced R] (U : Opens (PrimeSpectrum R)) :
    (R ⧸ PrimeSpectrum.vanishingIdeal (U : Set (PrimeSpectrum R))) ≃ₐ[R]
      prop247_openSectionImage R U :=
  (Ideal.quotientEquivAlgOfEq R (ker_algebraMap_sections_eq_vanishingIdeal R U).symm).trans
    (Ideal.quotientKerEquivRange (Algebra.ofId R ((Spec.structureSheaf R).obj.obj (op U))))

/-- 同型は元の R の各元を元の像の元に送る。 -/
@[simp] theorem prop247_openSectionImageQuotientEquiv_mk
    (R : Type u) [CommRing R] [IsReduced R] (U : Opens (PrimeSpectrum R)) (r : R) :
    prop247_openSectionImageQuotientEquiv R U (Ideal.Quotient.mk _ r) =
      prop247_toOpenSectionImage R U r :=
  (prop247_openSectionImageQuotientEquiv R U).commutes r

/-- 原典の像の環の Spec の像は、実開集合 U の閉包である。 -/
theorem prop247_openSectionImage_spectrum_range
    (R : Type u) [CommRing R] [IsReduced R] (U : Opens (PrimeSpectrum R)) :
    Set.range (PrimeSpectrum.comap (prop247_toOpenSectionImage R U).toRingHom) =
      closure (U : Set (PrimeSpectrum R)) := by
  rw [range_comap_of_surjective _ _ (prop247_toOpenSectionImage_surjective R U),
    prop247_toOpenSectionImage_ker, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]

/-- rank 別の相対開閉部分を、Spec R の実開集合として固定する。 -/
def prop247_rankOpen
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S] (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)))
    (n : ℕ) : Opens (PrimeSpectrum R) :=
  ⟨Subtype.val '' {x | prop247_awayRank R S g x = n},
    (PrimeSpectrum.isOpen_basicOpen (a := g)).isOpenMap_subtype_val _
      ((prop247_awayRank_isLocallyConstant R S g hetale).isOpen_fiber n)⟩

/-- rank 部分の閉包を D(g) に戻すと、元の rank 部分に一致する。 -/
theorem prop247_rankOpen_closure_on_away
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S] (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g))) (n : ℕ) :
    (Subtype.val : (PrimeSpectrum.basicOpen g) → PrimeSpectrum R) ⁻¹'
      closure (prop247_rankOpen R S g hetale n : Set (PrimeSpectrum R)) =
      {x | prop247_awayRank R S g x = n} :=
  (PrimeSpectrum.isOpen_basicOpen (a := g)).isOpenMap_subtype_val.preimage_closure_image
    Subtype.val_injective continuous_subtype_val _
    ((prop247_awayRank_isLocallyConstant R S g hetale).isClosed_fiber n)

/-- 原典の Ri=im(R→Γ(Ui,O)) の Spec は、g の外で元の rank 部分をちょうど表す。 -/
theorem prop247_rankSectionImage_spectrum_on_away
    (R S : Type u) [CommRing R] [IsReduced R] [CommRing S] [Algebra R S]
    [Module.Finite R S] (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g))) (n : ℕ) :
    (Subtype.val : (PrimeSpectrum.basicOpen g) → PrimeSpectrum R) ⁻¹'
      Set.range (PrimeSpectrum.comap
        (prop247_toOpenSectionImage R (prop247_rankOpen R S g hetale n)).toRingHom) =
      {x | prop247_awayRank R S g x = n} := by
  rw [prop247_openSectionImage_spectrum_range, prop247_rankOpen_closure_on_away]

end SerrePositivity.CLMST
