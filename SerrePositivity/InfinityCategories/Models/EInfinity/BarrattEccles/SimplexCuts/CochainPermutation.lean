module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CochainNaturality
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CutSumPermutation
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.InputPermutation

/-!
模型。文献の定義との比較は後で
# BF切断余作用の全複体射の対称群同変性

Berger–Fresse §1.2.1・§2.2.6、M14 L17、報告 §392。
元の語のrenameと全Cut和のKoszul置換を、全係数・全単体へ延長する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- 元の語基底の整数次数におけるrenameの値（BF §1.2.1）。 -/
lemma complexRename_basis_inv {n d : ℕ}
    (σ : Equiv.Perm (Fin n)) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexRename A n σ).f (-(d : ℤ))
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n d).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d (ULift.up v))) =
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n d).inv
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d (ULift.up (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.rename σ v))) := by
  apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n d).toLinearEquiv.injective
  change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n d).hom
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexRename A n σ).f (-(d : ℤ))
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n d).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d (ULift.up v)))) =
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n d).hom ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n d).inv
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d (ULift.up (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word.rename σ v))))
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.complexRename_neg_hom_apply, ModuleCat.hom_inv_apply,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.renameLinear_basis, ModuleCat.hom_inv_apply]

/-- L17：同じ全arityのBF複体射のKoszul置換との同変性（BF §2.2.6）。 -/
lemma cochainAction_permutation (S : SSet.{0}) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexRename A n σ ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction A S n =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction A S n ≫ (permutationAction (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) n σ).asIso.hom := by
  cases n with
  | zero =>
    have hσ : σ = 1 := Subsingleton.elim _ _
    subst σ
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexRename_one, id_whiskerRight, Category.id_comp,
      permutationAction_one, Category.comp_id]
  | succ n =>
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coefficient_simplex_pair_hom_ext A S (n + 1)
    intro d q v x
    simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
    rw [SerrePositivity.DifferentialGraded.whiskerRight_apply, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.complexRename_basis_inv,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction_basis_generator, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction_basis_generator]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSum_permutation A S v σ x

/-- 元の対称列の指定置換についての同じ等式（BF §2.2.6）。 -/
lemma cochainAction_equivariance (S : SSet.{0}) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.sequence A).map (_root_.SerrePositivity.FiniteBijection.permutation n σ) ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction A S n =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction A S n ≫ (permutationAction (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) n σ).asIso.hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.sequence_map_permutation]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction_permutation A S n σ

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
