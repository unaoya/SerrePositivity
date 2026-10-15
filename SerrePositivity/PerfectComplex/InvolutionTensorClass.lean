module

public import SerrePositivity.PerfectComplex.InvolutionTensor
public import SerrePositivity.PerfectComplex.InvolutionClass
public import SerrePositivity.PerfectComplex.ClosedSupportBiproduct

/-! # Multiplicativity of the difference of involution eigenspace classes -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
variable {R : Type u} [CommRing R] [Invertible (2 : R)]
namespace CochainInvolution
variable {P Q : CochainComplex (ModuleCat.{u} R) ℤ}

def positiveClass (t : CochainInvolution P) (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R P) (hs : HasHomologySupportOn Z P) : K0WithSupport Z :=
  t.positive.k0Class Z hp hs

def negativeClass (t : CochainInvolution P) (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R P) (hs : HasHomologySupportOn Z P) : K0WithSupport Z :=
  t.negative.k0Class Z hp hs

lemma positive_tensor_class (t : CochainInvolution P) (s : CochainInvolution Q)
    {Y Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q)
    (hsP : HasHomologySupportOn Y P) (hsQ : HasHomologySupportOn Z Q) :
    (t.tensor s).positiveClass (Y ⊓ Z) (strictlyPerfectComplex_cochainTensor P Q hp hq)
      (hsP.cochainTensor hsQ hp hq) =
    K0WithSupport.cup (t.positiveClass Y hp hsP) (s.positiveClass Z hq hsQ) +
      K0WithSupport.cup (t.negativeClass Y hp hsP) (s.negativeClass Z hq hsQ) := by
  let ha := t.positive.image_strictlyPerfect hp
  let hb := s.positive.image_strictlyPerfect hq
  let hc := t.negative.image_strictlyPerfect hp
  let hd := s.negative.image_strictlyPerfect hq
  let sa := t.positive.image_support hsP
  let sb := s.positive.image_support hsQ
  let sc := t.negative.image_support hsP
  let sd := s.negative.image_support hsQ
  let hAB := strictlyPerfectComplex_cochainTensor _ _ ha hb
  let hCD := strictlyPerfectComplex_cochainTensor _ _ hc hd
  let sAB := sa.cochainTensor sb ha hb
  let sCD := sc.cochainTensor sd hc hd
  have he := K0WithSupport.mk_eq_of_quasiIso (Y ⊓ Z)
    (cochainTensor t.positive.image s.positive.image ⊞
      cochainTensor t.negative.image s.negative.image)
    (t.tensor s).positive.image
    (strictlyPerfectComplex_biprod hAB hCD)
    ((t.tensor s).positive.image_strictlyPerfect (strictlyPerfectComplex_cochainTensor P Q hp hq))
    (sAB.biprod sCD) ((t.tensor s).positive.image_support (hsP.cochainTensor hsQ hp hq))
    (positiveTensorIso t s).hom
  have hsum := K0WithSupport.mk_biprod (Y ⊓ Z)
    (cochainTensor t.positive.image s.positive.image)
    (cochainTensor t.negative.image s.negative.image)
    hAB hCD sAB sCD
  have hcups := congrArg₂ (fun x y : K0WithSupport (Y ⊓ Z) => x + y)
    (K0WithSupport.mk_tensor t.positive.image s.positive.image ha hb sa sb)
    (K0WithSupport.mk_tensor t.negative.image s.negative.image hc hd sc sd)
  exact he.symm.trans (hsum.trans hcups)

lemma negative_tensor_class (t : CochainInvolution P) (s : CochainInvolution Q)
    {Y Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q)
    (hsP : HasHomologySupportOn Y P) (hsQ : HasHomologySupportOn Z Q) :
    (t.tensor s).negativeClass (Y ⊓ Z) (strictlyPerfectComplex_cochainTensor P Q hp hq)
      (hsP.cochainTensor hsQ hp hq) =
    K0WithSupport.cup (t.positiveClass Y hp hsP) (s.negativeClass Z hq hsQ) +
      K0WithSupport.cup (t.negativeClass Y hp hsP) (s.positiveClass Z hq hsQ) := by
  let ha := t.positive.image_strictlyPerfect hp
  let hb := s.negative.image_strictlyPerfect hq
  let hc := t.negative.image_strictlyPerfect hp
  let hd := s.positive.image_strictlyPerfect hq
  let sa := t.positive.image_support hsP
  let sb := s.negative.image_support hsQ
  let sc := t.negative.image_support hsP
  let sd := s.positive.image_support hsQ
  let hAB := strictlyPerfectComplex_cochainTensor _ _ ha hb
  let hCD := strictlyPerfectComplex_cochainTensor _ _ hc hd
  let sAB := sa.cochainTensor sb ha hb
  let sCD := sc.cochainTensor sd hc hd
  have he := K0WithSupport.mk_eq_of_quasiIso (Y ⊓ Z)
    (cochainTensor t.positive.image s.negative.image ⊞
      cochainTensor t.negative.image s.positive.image)
    (t.tensor s).negative.image
    (strictlyPerfectComplex_biprod hAB hCD)
    ((t.tensor s).negative.image_strictlyPerfect (strictlyPerfectComplex_cochainTensor P Q hp hq))
    (sAB.biprod sCD) ((t.tensor s).negative.image_support (hsP.cochainTensor hsQ hp hq))
    (negativeTensorIso t s).hom
  have hsum := K0WithSupport.mk_biprod (Y ⊓ Z)
    (cochainTensor t.positive.image s.negative.image)
    (cochainTensor t.negative.image s.positive.image)
    hAB hCD sAB sCD
  have hcups := congrArg₂ (fun x y : K0WithSupport (Y ⊓ Z) => x + y)
    (K0WithSupport.mk_tensor t.positive.image s.negative.image ha hb sa sb)
    (K0WithSupport.mk_tensor t.negative.image s.positive.image hc hd sc sd)
  exact he.symm.trans (hsum.trans hcups)

lemma k0Class_tensor (t : CochainInvolution P) (s : CochainInvolution Q)
    {Y Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q)
    (hsP : HasHomologySupportOn Y P) (hsQ : HasHomologySupportOn Z Q) :
    (t.tensor s).k0Class (Y ⊓ Z) (strictlyPerfectComplex_cochainTensor P Q hp hq)
      (hsP.cochainTensor hsQ hp hq) =
    K0WithSupport.cup (t.k0Class Y hp hsP) (s.k0Class Z hq hsQ) := by
  let hT := strictlyPerfectComplex_cochainTensor P Q hp hq
  let sT := hsP.cochainTensor hsQ hp hq
  change (t.tensor s).positiveClass (Y ⊓ Z) hT sT - (t.tensor s).negativeClass (Y ⊓ Z) hT sT =
    K0WithSupport.cup (t.positiveClass Y hp hsP - t.negativeClass Y hp hsP)
      (s.positiveClass Z hq hsQ - s.negativeClass Z hq hsQ)
  rw [positive_tensor_class t s hp hq hsP hsQ, negative_tensor_class t s hp hq hsP hsQ]
  simp only [map_sub, AddMonoidHom.sub_apply]
  abel

end CochainInvolution
end SerrePositivity
