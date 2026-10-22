module

public import SerrePositivity.KST.LocalizingInvariants.CochainKernelHomology

/-!
概要：上に有界な実複体からの全射は、上端の元のホモロジー射でも全射である。
方針：実 kernel の同じ上界と短完全列の長完全列を使う。
規約：元のホモロジー射への Epi。使われ方：集中した係数像のホモロジー表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R] {P T : Complex R} (f : P ⟶ T)

lemma cochainKernel_upperBound (k : ℤ) [P.IsStrictlyLE k] :
    (kernel f).IsStrictlyLE k := by
  apply (CochainComplex.isStrictlyLE_iff _ _).2
  intro j hj
  exact IsZero.of_mono ((kernel.ι f).f j) (P.isZero_of_isStrictlyLE k j hj)

lemma cochainEpi_homologyMap_epi [Epi f] (k : ℤ) [P.IsStrictlyLE k] :
    Epi (homologyMap f k) := by
  have : (kernel f).IsStrictlyLE k := cochainKernel_upperBound f k
  have hz := (kernel f).isZero_of_isLE k (k + 1) (by omega)
  exact ((cochainKernelSequence_shortExact f).homology_exact₃ k (k + 1)
    (by change k + 1 = k + 1; rfl)).epi_f (hz.eq_of_tgt _ _)

end SerrePositivity.KST.LocalizingInvariants
