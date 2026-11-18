module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryZeroOutputValue

/-!
模型。文献の定義との比較は後で
# 零出力arityの空語合成の全次数の一致

Berger–Fresse §1.2.4・§2.2.6、M14 L12a、報告 §366。
元の零単体の値とsingle複体の零対象性を使い、全入力次数を保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial

/-- 零出力arityの実際の空語合成則は全次数で一致（BF §2.2.6）。 -/
lemma cochainAction_composition_nullary_zero_output_eq_iterated
    (A : Type u) [CommRing A] (S : SSet.{0}) {d q : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 1 d) (ν : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 0 0) (k : Fin 1)
    (x : S _⦋q⦌) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction A S 0).f (-(d : ℤ) + -(q : ℤ))
      (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A 0) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S)
        (-(d : ℤ)) (-(q : ℤ)) (-(d : ℤ) + -(q : ℤ)) rfl
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A 0 d).inv
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionOnWords A u ν k) ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S q x)) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.iteratedCochainAction A S 0 0 k).f (-(d : ℤ) + -(q : ℤ))
        (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A 1 ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A 0) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S)
          (-(d : ℤ) + -(0 : ℤ)) (-(q : ℤ)) (-(d : ℤ) + -(q : ℤ)) (by omega)
          (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A 0)
            (-(d : ℤ)) (-(0 : ℤ)) (-(d : ℤ) + -(0 : ℤ)) rfl
            ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A 1 d).inv
              (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A 1 d (ULift.up u)) ⊗ₜ[A]
              (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A 0 0).inv
                (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A 0 0 (ULift.up ν))) ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S q x)) := by
  cases d with
  | succ d => exact isEmptyElim u
  | zero =>
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    cases q with
    | zero => exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction_composition_nullary_output_zero_degree_zero A S u ν x
    | succ q =>
      let _ : Subsingleton ((power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) 0).X (-(0 : ℤ) + -((q + 1 : ℕ) : ℤ))) := by
        change Subsingleton (((single (ModuleCat A) (.up ℤ) 0).obj
          (𝟙_ (ModuleCat A))).X (-(0 : ℤ) + -((q + 1 : ℕ) : ℤ)))
        exact ModuleCat.isZero_iff_subsingleton.mp
          (isZero_single_obj_X (.up ℤ) 0 (𝟙_ (ModuleCat A)) _ (by omega))
      exact Subsingleton.elim _ _

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
