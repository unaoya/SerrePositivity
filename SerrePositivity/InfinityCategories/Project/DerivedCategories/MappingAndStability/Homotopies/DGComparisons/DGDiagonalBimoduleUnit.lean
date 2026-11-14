module
public import SerrePositivity.DifferentialGraded.Tensor.Triple

public import SerrePositivity.DifferentialGraded.Module.ConeConstruction
public import SerrePositivity.DifferentialGraded.Tensor.Associator.Restriction
/-!
概要：対角双加群の二つの単位子を同じ閉零同型として同定する。
方針：全次数の実 tensor 成分の左右作用と Koszul 符号を比較する。
規約：原 Hom の平坦性は不要。使われ方：graph と cell の単位比較。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
lemma dgDiagonal_leftAction_eq_rightAction (b x c : D) :
    BalancedTensor.leftAction R D ((Bimodule.diagonal R D).leftAt b) x c =
      BalancedTensor.rightAction R D (representable R c) b x := by
  apply tensorHom_ext
  intro p q n hn
  subst n
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f h
  change GradedHom R b x q at h
  change (BalancedTensor.leftAction R D ((Bimodule.diagonal R D).leftAt b) x c).f (p + q)
      (HomologicalComplex.ιTensorObj (x ⟶[Complex R] c) (b ⟶[Complex R] x)
        p q (p + q) rfl (f ⊗ₜ[R] h)) =
    (BalancedTensor.rightAction R D (representable R c) b x).f (p + q)
      (HomologicalComplex.ιTensorObj (x ⟶[Complex R] c) (b ⟶[Complex R] x)
        p q (p + q) rfl (f ⊗ₜ[R] h))
  have hl := BalancedTensor.leftAction_apply R D ((Bimodule.diagonal R D).leftAt b)
    x c p q (p + q) rfl f h
  have hr := BalancedTensor.rightAction_apply R D (representable R c)
    b x p q (p + q) rfl f h
  have hv : DifferentialGraded.leftAction R ((Bimodule.diagonal R D).leftAt b) f h
      (show q + p = p + q by omega) =
      (p * q).negOnePow • moduleAction R (representable R c) h f rfl := by
    change (((moduleHomπ R D (representable R x) (representable R c) b).f p
      ((yonedaHom R D x c).f p f)).v q (p + q) (by omega)) h = _
    rw [yonedaHom_element, representable_action]
  exact hl.trans (hv.trans hr.symm)
lemma dgDiagonalBimoduleUnitIso_eq :
    BimoduleTensor.rightBimoduleUnitIso R D D (Bimodule.diagonal R D) =
      BimoduleTensor.leftBimoduleUnitIso R D D (Bimodule.diagonal R D) := by
  apply Iso.ext
  apply BimoduleCategory.value_hom_ext R D D
  intro b c
  calc
    _ = (BimoduleTensor.rightUnitValueIso R D D (Bimodule.diagonal R D) b c).hom :=
      BimoduleTensor.rightBimoduleUnitIso_hom_value R D D (Bimodule.diagonal R D) b c
    _ = (BimoduleTensor.leftUnitValueIso R D D (Bimodule.diagonal R D) b c).hom := by
      apply BalancedTensor.hom_ext
      intro x
      exact (BalancedTensor.ι_yonedaEvaluation R D c
        ((Bimodule.diagonal R D).leftAt b) x).trans
          ((dgDiagonal_leftAction_eq_rightAction R D b x c).trans
            (BimoduleTensor.ι_leftUnitValueIso_hom R D D (Bimodule.diagonal R D) b x c).symm)
    _ = _ := (BimoduleTensor.leftBimoduleUnitIso_hom_value R D D
      (Bimodule.diagonal R D) b c).symm
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
