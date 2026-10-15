module

public import SerrePositivity.PerfectComplex.BiproductPerfect
public import SerrePositivity.PerfectComplex.TensorK0

/-! # Concrete binary-sum and tensor formulas in closed-support K₀ -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
variable {R : Type u} [CommRing R]
namespace K0WithSupport

lemma mk_biprod (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q)
    (hsP : HasHomologySupportOn Z P) (hsQ : HasHomologySupportOn Z Q) :
    mk Z (supportedPerfectOnObj Z (P ⊞ Q) (strictlyPerfectComplex_biprod hp hq)
      (hsP.biprod hsQ)) =
    mk Z (supportedPerfectOnObj Z P hp hsP) + mk Z (supportedPerfectOnObj Z Q hq hsQ) := by
  let S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
    ShortComplex.mk (biprod.inl : P ⟶ P ⊞ Q) biprod.snd (by simp)
  let spl : S.Splitting := ShortComplex.Splitting.ofHasBinaryBiproduct P Q
  exact mk_shortExact Z S spl.shortExact hp (strictlyPerfectComplex_biprod hp hq) hq
    hsP (hsP.biprod hsQ) hsQ

lemma mk_tensor {Y Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q)
    (hsP : HasHomologySupportOn Y P) (hsQ : HasHomologySupportOn Z Q) :
    mk (Y ⊓ Z) (supportedPerfectOnObj (Y ⊓ Z) (cochainTensor P Q)
      (strictlyPerfectComplex_cochainTensor P Q hp hq) (hsP.cochainTensor hsQ hp hq)) =
    cup (mk Y (supportedPerfectOnObj Y P hp hsP)) (mk Z (supportedPerfectOnObj Z Q hq hsQ)) :=
  (cup_mk_mk (supportedPerfectOnObj Y P hp hsP) (supportedPerfectOnObj Z Q hq hsQ)).symm

end K0WithSupport
end SerrePositivity
