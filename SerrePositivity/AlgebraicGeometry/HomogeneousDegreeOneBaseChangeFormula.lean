module

public import SerrePositivity.AlgebraicGeometry.HomogeneousDegreeOneBaseChange

/-!
概要：係数移送の標準開の同型における、正規化した純テンソルの像。
方針：脱斉次化の商の同型と、テンソル積と商の同型の元上の式を使う。
規約：flat 性・Noether 性を仮定しない。
使われ方：Proj の係数移送の標準開の射の自然性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]
variable (G : ℕ → Submodule R A) [GradedRing G] {f : A} (hf : f ∈ G 1)
local instance degreeOneBaseFormulaSourceAlgebra : Algebra R (HomogeneousLocalization.Away G f) :=
  projectiveHomogeneousAwayAlgebra G f
local instance degreeOneBaseFormulaTargetAlgebra :
    Algebra B (HomogeneousLocalization.Away (fun n ↦ (G n).baseChange B) ((1 : B) ⊗ₜ[R] f)) :=
  projectiveHomogeneousAwayAlgebra (fun n ↦ (G n).baseChange B) _

/-- 係数移送の同型は、正規化した純テンソルを同じ元の正規化へ送る。 -/
theorem homogeneousDegreeOneBaseChangeEquiv_tmul_normalize (b : B) (x : A) :
    homogeneousDegreeOneBaseChangeEquiv (B := B) G hf
      (b ⊗ₜ[R] homogeneousDegreeOneNormalize G hf x) =
      homogeneousDegreeOneNormalize (fun n ↦ (G n).baseChange B)
        (Submodule.tmul_mem_baseChange_of_mem (1 : B) hf) (b ⊗ₜ[R] x) := by
  have hq : (homogeneousDegreeOneQuotientAlgEquiv G hf).symm
      (homogeneousDegreeOneNormalize G hf x) =
      Ideal.Quotient.mk (Ideal.span ({f - 1} : Set A)) x := by
    rw [show homogeneousDegreeOneNormalize G hf x =
      homogeneousDegreeOneQuotientAlgEquiv G hf (Ideal.Quotient.mk _ x) from rfl,
      AlgEquiv.symm_apply_apply]
  simp only [homogeneousDegreeOneBaseChangeEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    AlgEquiv.coe_toAlgHom, AlgEquiv.coe_refl, id_eq, hq,
    Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul, Ideal.quotientEquivAlgOfEq_mk]
  rfl

end SerrePositivity.AlgebraicGeometry
