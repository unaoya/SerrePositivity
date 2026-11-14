module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedBaseChange
public import SerrePositivity.HomologicalAlgebra.BoundedAboveExactDerived
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.PowerTorsion
public import Mathlib.Algebra.Category.ModuleCat.Descent

/-! # Faithfully flat detection of homology maps

Flat scalar extension commutes with all homology groups of arbitrary derived objects.
Faithfulness reflects zero maps on those groups. No bound or finite generation is required.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S]

/-- Faithfully flat scalar extension reflects zero module morphisms. -/
lemma faithfullyFlat_extendScalars_map_eq_zero_iff (φ : R →+* S) (hφ : φ.FaithfullyFlat)
    {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (ModuleCat.extendScalars φ).map f = 0 ↔ f = 0 := by
  constructor
  · intro h
    algebraize [φ]
    have hz : LinearMap.lTensor S f.hom = 0 := by
      apply LinearMap.ext
      intro x
      exact congrArg (fun k => k.hom x) h
    apply ModuleCat.hom_ext
    exact (Module.FaithfullyFlat.zero_iff_lTensor_zero R S f.hom).mpr hz
  · rintro rfl
    exact Functor.map_zero _ _ _

/-- Scalar extension on all derived objects along a flat ring map. -/
def flatDerivedBaseChange (φ : R →+* S) (hφ : φ.Flat) :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S) := by
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
  exact (ModuleCat.extendScalars φ).mapDerivedCategory

/-- The projective-model base change agrees naturally with flat base change on actual objects. -/
def boundedAboveFlatDerivedBaseChangeIso (φ : R →+* S) (hφ : φ.Flat) :
    boundedAboveDerivedBaseChange φ ⋙ DerivedCategory.Minus.ι ≅
      DerivedCategory.Minus.ι ⋙ flatDerivedBaseChange φ hφ := by
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
  exact Functor.isoWhiskerRight (boundedAboveLeftDerivedExactIso (ModuleCat.extendScalars φ))
    DerivedCategory.Minus.ι

/-- Flat base change commutes with every homology functor, naturally in all derived morphisms. -/
def flatDerivedBaseChangeHomologyNatIso (φ : R →+* S) (hφ : φ.Flat) (n : ℤ) :
    flatDerivedBaseChange φ hφ ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} S) n ≅
      DerivedCategory.homologyFunctor (ModuleCat.{u} R) n ⋙ ModuleCat.extendScalars φ := by
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
  exact exactDerivedHomologyNatIso (ModuleCat.extendScalars φ) n

/-- Naturality of the flat homology comparison detects zero maps in every degree. -/
lemma flatDerivedHomology_map_eq_zero_iff (φ : R →+* S) (hφ : φ.Flat)
    (n : ℤ) {X Y : DerivedCategory (ModuleCat.{u} R)} (f : X ⟶ Y) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} S) n).map
        ((flatDerivedBaseChange φ hφ).map f) = 0 ↔
      (ModuleCat.extendScalars φ).map
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map f) = 0 := by
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
  let e := flatDerivedBaseChangeHomologyNatIso φ hφ n
  have hn := e.hom.naturality f
  change (DerivedCategory.homologyFunctor (ModuleCat.{u} S) n).map
      ((flatDerivedBaseChange φ hφ).map f) ≫ (e.app Y).hom =
    (e.app X).hom ≫ (ModuleCat.extendScalars φ).map
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map f) at hn
  constructor
  · intro h
    apply (cancel_epi (e.app X).hom).mp
    simpa only [h, zero_comp, comp_zero] using hn.symm
  · intro h
    apply (cancel_mono (e.app Y).hom).mp
    simpa only [h, zero_comp, comp_zero] using hn

/-- A faithfully flat scalar extension detects every homology map, with no boundedness condition. -/
lemma faithfullyFlatDerivedHomology_map_eq_zero_iff (φ : R →+* S)
    (hφ : φ.FaithfullyFlat) (n : ℤ) {X Y : DerivedCategory (ModuleCat.{u} R)} (f : X ⟶ Y) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} S) n).map
        ((flatDerivedBaseChange φ hφ.flat).map f) = 0 ↔
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map f = 0 := by
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ.flat
  exact (flatDerivedHomology_map_eq_zero_iff φ hφ.flat n f).trans
    (faithfullyFlat_extendScalars_map_eq_zero_iff φ hφ _)

/-- In particular, the homology action of any scalar power is reflected faithfully. -/
lemma faithfullyFlatDerivedHomology_scalar_eq_zero_iff (φ : R →+* S)
    (hφ : φ.FaithfullyFlat) (n : ℤ) (X : DerivedCategory (ModuleCat.{u} R)) (g : R) (N : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} S) n).map
        ((flatDerivedBaseChange φ hφ.flat).map (g ^ N • 𝟙 X)) = 0 ↔
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map (g ^ N • 𝟙 X) = 0 :=
  faithfullyFlatDerivedHomology_map_eq_zero_iff φ hφ n _

end SerrePositivity

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "7.2.2.13" (partial := stronger-hyp) "仮定：通常可換環の平坦な準同型 R→S と任意の通常の導来 R 加群（Lean が強い：平坦因子を離散可換 R 代数 S とする場合）。結論：平坦な導来スカラー拡大後の全 Hⁿ を Hⁿ の通常のスカラー拡大と自然に同定する（この平坦因子の場合の結論に一致）。任意の flat 環スペクトル加群とその π の比較は含まれない。"] _root_.SerrePositivity.flatDerivedBaseChangeHomologyNatIso
