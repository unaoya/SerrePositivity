module

public import SerrePositivity.AlgebraicGeometry.HomogeneousDegreeOneQuotientAlgebra
public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
概要：次数一の標準開と任意の係数移送の比較。
方針：脱斉次化の商の同型と、テンソル積と商の既存の同型を合成する。
規約：係数移送に flat 性・Noether 性を仮定しない。
使われ方：Proj の任意のアフィン底変換の標準開の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]
variable (G : ℕ → Submodule R A) [GradedRing G] {f : A} (hf : f ∈ G 1)
local instance degreeOneBaseChangeSourceAlgebra : Algebra R (HomogeneousLocalization.Away G f) :=
  projectiveHomogeneousAwayAlgebra G f
local instance degreeOneBaseChangeTargetAlgebra : Algebra B (HomogeneousLocalization.Away (fun n ↦ (G n).baseChange B)
    ((1 : B) ⊗ₜ[R] f)) :=
  projectiveHomogeneousAwayAlgebra (fun n ↦ (G n).baseChange B) _

/-- 延長した脱斉次化のイデアルは、移した分母を 1 とするイデアル。 -/
theorem degreeOneDehomogenizationIdeal_baseChange :
    (Ideal.span ({f - 1} : Set A)).map
        (Algebra.TensorProduct.includeRight : A →ₐ[R] B ⊗[R] A) =
      Ideal.span ({(1 : B) ⊗ₜ[R] f - 1} : Set (B ⊗[R] A)) := by
  simp only [Ideal.map_span, Set.image_singleton, map_sub, map_one,
    Algebra.TensorProduct.includeRight_apply]

/-- 次数一の標準開は任意の係数移送と可換。 -/
def homogeneousDegreeOneBaseChangeEquiv :
    B ⊗[R] (HomogeneousLocalization.Away G f) ≃ₐ[B]
      HomogeneousLocalization.Away (fun n ↦ (G n).baseChange B) ((1 : B) ⊗ₜ[R] f) :=
  (Algebra.TensorProduct.congr (R := R) (AlgEquiv.refl : B ≃ₐ[B] B)
      (homogeneousDegreeOneQuotientAlgEquiv G hf).symm).trans
    ((Algebra.TensorProduct.tensorQuotientEquiv (R := R) B A B
      (Ideal.span ({f - 1} : Set A))).trans
      ((Ideal.quotientEquivAlgOfEq B (degreeOneDehomogenizationIdeal_baseChange (R := R) (B := B)
        (f := f))).trans
        (homogeneousDegreeOneQuotientAlgEquiv (fun n ↦ (G n).baseChange B)
          (Submodule.tmul_mem_baseChange_of_mem (1 : B) hf))))

end SerrePositivity.AlgebraicGeometry
