module
public import SerrePositivity.PerfectComplex.TensorEnlarge
public import SerrePositivity.HomologicalAlgebra.CochainTensorBaseChange
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Base change of the standard cochain tensor product -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
open Functor.Monoidal Functor.OplaxMonoidal
variable {R S : Type u} [CommRing R] [CommRing S]
variable (φ : R →+* S) (P Q : CochainComplex (ModuleCat.{u} R) ℤ)

/-- Pullback of an intersection lies in an intersection of larger target supports. -/
lemma supportPullback_inf_le {Y Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    {W V : TopologicalSpace.Closeds (PrimeSpectrum S)}
    (hY : supportPullback φ Y ≤ W) (hZ : supportPullback φ Z ≤ V) :
    supportPullback φ (Y ⊓ Z) ≤ W ⊓ V := by
  intro p hp
  exact ⟨hY hp.1, hZ hp.2⟩

namespace K0WithSupport
/-- Cup products commute with ring change, even when the target supports are enlarged. -/
lemma cup_map {Y Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    {W V : TopologicalSpace.Closeds (PrimeSpectrum S)}
    (hY : supportPullback φ Y ≤ W) (hZ : supportPullback φ Z ≤ V)
    (x : K0WithSupport Y) (y : K0WithSupport Z) :
    map φ (Y ⊓ Z) (W ⊓ V) (supportPullback_inf_le φ hY hZ) (cup x y) =
      cup (map φ Y W hY x) (map φ Z V hZ y) := by
  have he :
      (cup (Y := Y) (Z := Z)).compr₂
        (map φ (Y ⊓ Z) (W ⊓ V) (supportPullback_inf_le φ hY hZ)) =
      ((cup (Y := W) (Z := V)).compl₂ (map φ Z V hZ)).comp (map φ Y W hY) := by
    apply cupPairing_hom_ext
    intro X Q
    change map φ (Y ⊓ Z) (W ⊓ V) (supportPullback_inf_le φ hY hZ)
        (cup (mk Y X) (mk Z Q)) = cup (map φ Y W hY (mk Y X)) (map φ Z V hZ (mk Z Q))
    simp only [cup_mk_mk, tensorClass, map_mk]
    exact mk_iso _ (ObjectProperty.isoMk _ (ObjectProperty.isoMk _
      ((homotopyQuot S).mapIso (cochainTensorBaseChangeIso φ
        (supportedPerfectRepresentative X) (supportedPerfectRepresentative Q)))))
  exact DFunLike.congr_fun (DFunLike.congr_fun he x) y
end K0WithSupport
end SerrePositivity
