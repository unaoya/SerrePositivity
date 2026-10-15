module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nonsingular
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits
public import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-! # Coproducts of nonsingular simplicial sets

Every simplex of a coproduct lies in a summand. Coproduct injections are
degreewise injective, so nondegeneracy and the representing monomorphism
reduce to that summand. No finiteness is needed for nonsingularity.
-/

@[expose] public section
universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.HomotopyFunctionComplex.SimplicialCoproduct
variable {ι : Type v} (X : ι → SSet.{v})

lemma mono_ι (i : ι) : Mono (Sigma.ι X i) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  exact (mono_iff_injective _).mpr
    (Cofan.inj_injective_of_isColimit
      (isColimitCofanMkObjOfIsColimit ((evaluation _ _).obj n) _ _
        (coproductIsCoproduct X)) i)

instance nonsingular [∀ i, (X i).Nonsingular] : (∐ X).Nonsingular where
  mono {n} x := by
    obtain ⟨i, y, hy⟩ := Cofan.inj_jointly_surjective_of_isColimit
      (isColimitCofanMkObjOfIsColimit ((evaluation _ _).obj (Opposite.op (SimplexCategory.mk n)))
        _ _ (coproductIsCoproduct X)) x.val
    have : Mono (Sigma.ι X i) := mono_ι X i
    have hnd : y ∈ (X i).nonDegenerate n :=
      (SSet.nonDegenerate_iff_of_mono (Sigma.ι X i) y).mp (hy.symm ▸ x.property)
    have : Mono ((SSet.yonedaEquiv (X := X i)).symm y) := SSet.Nonsingular.mono' y hnd
    have he : (SSet.yonedaEquiv (X := X i)).symm y ≫ Sigma.ι X i =
        (SSet.yonedaEquiv (X := ∐ X)).symm x.val :=
      (SSet.yonedaEquiv_symm_comp y (Sigma.ι X i)).trans
        (congrArg (SSet.yonedaEquiv (X := ∐ X)).symm hy)
    exact he ▸ inferInstanceAs (Mono ((SSet.yonedaEquiv (X := X i)).symm y ≫ Sigma.ι X i))

end SerrePositivity.HomotopyFunctionComplex.SimplicialCoproduct
