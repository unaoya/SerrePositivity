module

public import SerrePositivity.AlgebraicGeometry.SpecIdeal
public import SerrePositivity.AlgebraicGeometry.PureTransformModule
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
概要：アフィンスキームの主開のスキーム論的閉包と、境界ねじれで割った純変換を比較する。
方針：主局所化の核をイデアル層へ移し、閉包含を商環の Spec と同定する。
規約：主開を定める元は基礎環から来る。正則性や Noether 性は仮定しない。
使われ方：Stacks 0815 で、純変換の加群としての平坦性を幾何学的な平坦性に移す。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory

private theorem specIdealEquiv_ker_specMap {B C : CommRingCat.{u}} (φ : B ⟶ C) :
    specIdealEquiv B (Spec.map φ).ker = RingHom.ker φ.hom := by
  rw [← Scheme.IdealSheafData.map_bot, specIdealEquiv_map, OrderIso.map_bot, RingHom.ker]

private theorem localization_ker_restrictScalars
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (r : A) :
    ((RingHom.ker (algebraMap B (Localization.Away (algebraMap A B r)))) :
      Submodule B B).restrictScalars A = boundaryTorsion r B := by
  ext x
  change algebraMap B (Localization.Away (algebraMap A B r)) x = 0 ↔
    x ∈ boundaryTorsion r B
  rw [IsLocalization.map_eq_zero_iff (.powers (algebraMap A B r)), mem_boundaryTorsion_iff]
  simp [Submonoid.mem_powers_iff, Algebra.smul_def]

set_option backward.isDefEq.respectTransparency false in
private theorem flat_image_comp_specMap_iff_of_ker {A B : CommRingCat.{u}} [Algebra A B]
    {X : Scheme.{u}} (f : X ⟶ Spec B) (I : Ideal B)
    (hI : specIdealEquiv B f.ker = I) :
    Flat (f.imageι ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) ↔
      Module.Flat A (B ⧸ I) := by
  let j := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have hker : f.imageι.ker = j.ker := by
    apply (specIdealEquiv B).injective
    rw [Scheme.IdealSheafData.ker_subschemeι, hI, specIdealEquiv_ker_specMap]
    exact Ideal.mk_ker.symm
  let q := IsClosedImmersion.lift j f.imageι hker.ge
  have : IsIso q := IsClosedImmersion.isIso_lift j f.imageι hker.symm
  have hfac : q ≫ j = f.imageι := IsClosedImmersion.lift_fac _ _ _
  rw [← hfac, Category.assoc, MorphismProperty.cancel_left_of_respectsIso @Flat]
  rw [← Spec.map_comp, Flat.SpecMap_iff]
  exact RingHom.flat_algebraMap_iff

set_option backward.isDefEq.respectTransparency false in
/--
概要：主開の閉包から基礎アフィンスキームへの射は、対応する純変換加群が平坦であるとき、
かつそのときに限り平坦。
方針：局所化写像の核と境界ねじれを同定し、商環の Spec に対する平坦性判定を使う。
規約：閉包は点集合の閉包でなく、開包含のスキーム論的像。
使われ方：ブローアップのアフィンチャート上の環論的平坦化から、狭義変換の平坦性を導く。
-/
theorem flat_basicOpen_image_comp_specMap_iff (A B : CommRingCat.{u}) [Algebra A B] (r : A)
    (V : (Spec B).Opens) (hV : V = PrimeSpectrum.basicOpen (algebraMap A B r)) :
    Flat (V.ι.imageι ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) ↔
      Module.Flat A (modulePureTransform r B) := by
  let b := algebraMap A B r
  let φ := CommRingCat.ofHom (algebraMap B (Localization.Away b))
  let I := RingHom.ker φ.hom
  let g := Spec.map φ
  have hrange : Set.range g = Set.range V.ι := by
    rw [Scheme.Opens.range_ι, hV]
    exact PrimeSpectrum.localization_away_comap_range _ b
  let e := IsOpenImmersion.isoOfRangeEq g V.ι hrange
  have hI : specIdealEquiv B V.ι.ker = I := by
    rw [← Scheme.Hom.ker_comp_of_isIso e.hom,
      IsOpenImmersion.isoOfRangeEq_hom_fac g V.ι hrange, specIdealEquiv_ker_specMap]
  refine (flat_image_comp_specMap_iff_of_ker (A := A) V.ι I hI).trans ?_
  change Module.Flat A (B ⧸ I.restrictScalars A) ↔ Module.Flat A (modulePureTransform r B)
  exact Module.Flat.equiv_iff
    (Submodule.quotEquivOfEq _ _ (localization_ker_restrictScalars A B r))

end SerrePositivity.AlgebraicGeometry
