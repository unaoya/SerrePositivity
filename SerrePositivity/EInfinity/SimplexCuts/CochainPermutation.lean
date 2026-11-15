module

public import SerrePositivity.EInfinity.SimplexCuts.CochainNaturality
public import SerrePositivity.EInfinity.SimplexCuts.CutSumPermutation
public import SerrePositivity.EInfinity.IntervalCuts.InputPermutation

/-!
# BF切断余作用の全複体射の対称群同変性

Berger–Fresse §1.2.1・§2.2.6、M14 L17、報告 §392。
元の語のrenameと全Cut和のKoszul置換を、全係数・全単体へ延長する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 元の語基底の整数次数におけるrenameの値（BF §1.2.1）。 -/
lemma complexRename_basis_inv {n d : ℕ}
    (σ : Equiv.Perm (Fin n)) (v : Surjection.BasisWord n d) :
    (Surjection.complexRename A n σ).f (-(d : ℤ))
      ((Surjection.complexXIso A n d).inv (Surjection.basis A n d (ULift.up v))) =
        (Surjection.complexXIso A n d).inv
          (Surjection.basis A n d (ULift.up (Surjection.Word.rename σ v))) := by
  apply (Surjection.complexXIso A n d).toLinearEquiv.injective
  change (Surjection.complexXIso A n d).hom
      ((Surjection.complexRename A n σ).f (-(d : ℤ))
        ((Surjection.complexXIso A n d).inv (Surjection.basis A n d (ULift.up v)))) =
    (Surjection.complexXIso A n d).hom ((Surjection.complexXIso A n d).inv
      (Surjection.basis A n d (ULift.up (Surjection.Word.rename σ v))))
  rw [IntervalCuts.complexRename_neg_hom_apply, ModuleCat.hom_inv_apply,
    Surjection.renameLinear_basis, ModuleCat.hom_inv_apply]

/-- L17：同じ全arityのBF複体射のKoszul置換との同変性（BF §2.2.6）。 -/
lemma cochainAction_permutation (S : SSet.{0}) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (Surjection.complexRename A n σ ▷ chains A S) ≫ cochainAction A S n =
      cochainAction A S n ≫ (permutationAction (chains A S) n σ).asIso.hom := by
  cases n with
  | zero =>
    have hσ : σ = 1 := Subsingleton.elim _ _
    subst σ
    rw [Surjection.complexRename_one, id_whiskerRight, Category.id_comp,
      permutationAction_one, Category.comp_id]
  | succ n =>
    apply coefficient_simplex_pair_hom_ext A S (n + 1)
    intro d q v x
    simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
    rw [SerrePositivity.DifferentialGraded.whiskerRight_apply, complexRename_basis_inv,
      cochainAction_basis_generator, cochainAction_basis_generator]
    exact cutSum_permutation A S v σ x

/-- 元の対称列の指定置換についての同じ等式（BF §2.2.6）。 -/
lemma cochainAction_equivariance (S : SSet.{0}) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ((Surjection.sequence A).map (FiniteBijection.permutation n σ) ▷ chains A S) ≫
        cochainAction A S n =
      cochainAction A S n ≫ (permutationAction (chains A S) n σ).asIso.hom := by
  rw [Surjection.sequence_map_permutation]
  exact cochainAction_permutation A S n σ

end SerrePositivity.EInfinity.SimplexCuts
