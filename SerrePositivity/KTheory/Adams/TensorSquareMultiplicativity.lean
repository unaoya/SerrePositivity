module

public import SerrePositivity.KTheory.Adams.TensorSquareShuffle
public import SerrePositivity.KTheory.Adams.CyclicTwo
public import SerrePositivity.PerfectComplex.Eigen.InvolutionTensor

/-! # Multiplicativity of the cyclic Adams operation of degree two -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
variable {R : Type u} [CommRing R] [Invertible (2 : R)]
namespace Adams

lemma tensorSquareClass_tensor (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    {Y Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q)
    (hsP : HasHomologySupportOn Y P) (hsQ : HasHomologySupportOn Z Q) :
    tensorSquareClass (cochainTensor P Q) (Y ⊓ Z)
      (strictlyPerfectComplex_cochainTensor P Q hp hq) (hsP.cochainTensor hsQ hp hq) =
    K0WithSupport.cup (tensorSquareClass P Y hp hsP) (tensorSquareClass Q Z hq hsQ) := by
  let hT := strictlyPerfectComplex_cochainTensor P Q hp hq
  let sT := hsP.cochainTensor hsQ hp hq
  let hP := tensorSquare_perfect P hp
  let hQ := tensorSquare_perfect Q hq
  let sP := tensorSquare_support hp hsP
  let sQ := tensorSquare_support hq hsQ
  let t := (tensorSquareInvolution P).tensor (tensorSquareInvolution Q)
  have hpos := K0WithSupport.mk_eq_of_quasiIso (Y ⊓ Z)
    (tensorSquarePositive (cochainTensor P Q)) t.positive.image
    (tensorSquarePositive_perfect _ hT)
    (t.positive.image_strictlyPerfect (strictlyPerfectComplex_cochainTensor _ _ hP hQ))
    (tensorSquarePositive_support hT sT) (t.positive.image_support (sP.cochainTensor sQ hP hQ))
    (tensorSquareTensorPositiveIso P Q).hom
  have hneg := K0WithSupport.mk_eq_of_quasiIso (Y ⊓ Z)
    (tensorSquareNegative (cochainTensor P Q)) t.negative.image
    (tensorSquareNegative_perfect _ hT)
    (t.negative.image_strictlyPerfect (strictlyPerfectComplex_cochainTensor _ _ hP hQ))
    (tensorSquareNegative_support hT sT) (t.negative.image_support (sP.cochainTensor sQ hP hQ))
    (tensorSquareTensorNegativeIso P Q).hom
  have he := congrArg₂ (fun x y : K0WithSupport (Y ⊓ Z) => x - y) hpos hneg
  exact he.trans (CochainInvolution.k0Class_tensor (tensorSquareInvolution P)
    (tensorSquareInvolution Q) hP hQ sP sQ)

/-- Axiom A2 for arbitrary classes in closed-support K₀. -/
lemma cyclicTwo_cup {Y Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (x : K0WithSupport Y) (y : K0WithSupport Z) :
    cyclicTwo (Y ⊓ Z) (K0WithSupport.cup x y) =
      K0WithSupport.cup (cyclicTwo Y x) (cyclicTwo Z y) := by
  have hx : ∀ (X : SupportedPerfectHomotopyOn Y) (y : K0WithSupport Z),
      cyclicTwo (Y ⊓ Z) (K0WithSupport.cup (K0WithSupport.mk Y X) y) =
      K0WithSupport.cup (cyclicTwo Y (K0WithSupport.mk Y X)) (cyclicTwo Z y) := by
    intro X
    have he : (cyclicTwo (Y ⊓ Z)).comp (K0WithSupport.cup (K0WithSupport.mk Y X)) =
        (K0WithSupport.cup (cyclicTwo Y (K0WithSupport.mk Y X))).comp (cyclicTwo Z) := by
      apply K0WithSupport.hom_ext
      intro Q
      change cyclicTwo (Y ⊓ Z) (K0WithSupport.cup (K0WithSupport.mk Y X) (K0WithSupport.mk Z Q)) =
        K0WithSupport.cup (cyclicTwo Y (K0WithSupport.mk Y X)) (cyclicTwo Z (K0WithSupport.mk Z Q))
      rw [K0WithSupport.cup_mk_mk]
      change cyclicTwo (Y ⊓ Z) (K0WithSupport.mk (Y ⊓ Z) (supportedPerfectTensorObj X Q)) = _
      rw [cyclicTwo_mk, cyclicTwo_mk, cyclicTwo_mk]
      exact tensorSquareClass_tensor (supportedPerfectRepresentative X)
        (supportedPerfectRepresentative Q)
        (supportedPerfectRepresentative_perfect X) (supportedPerfectRepresentative_perfect Q)
        (supportedPerfectRepresentative_support X) (supportedPerfectRepresentative_support Q)
    intro y
    exact DFunLike.congr_fun he y
  have he : (cyclicTwo (Y ⊓ Z)).comp (K0WithSupport.cup.flip y) =
      (K0WithSupport.cup.flip (cyclicTwo Z y)).comp (cyclicTwo Y) := by
    apply K0WithSupport.hom_ext
    intro X
    exact hx X y
  exact DFunLike.congr_fun he x

end Adams
end SerrePositivity
