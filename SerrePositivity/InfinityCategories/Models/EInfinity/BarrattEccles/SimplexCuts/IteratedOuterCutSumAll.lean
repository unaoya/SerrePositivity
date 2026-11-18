module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.IteratedCochainAction

/-!
模型。文献の定義との比較は後で
# 内側の全arityの元の二段余作用の全外側切断和

Berger–Fresse §2.2.6・§3.1、M14 L12a の既存構成の法則、報告 §342。
同じ複体射・整数係数・全切断を保って展開する。
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

/-- 実際の二段余作用の外側を、元の全切断和へ展開する（BF §2.2.6・§3.1）。 -/
lemma iteratedCochainAction_basis_outer_cut_sum_all (S : SSet.{0}) {m n d e q : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e)
    (k : Fin (m + 1)) (x : S _⦋q⦌) (z : ℤ)
    (hz : -(d : ℤ) + -(e : ℤ) + -(q : ℤ) = z) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.iteratedCochainAction A S m n k).f z
      (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + 1) ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S)
        (-(d : ℤ) + -(e : ℤ)) (-(q : ℤ)) z hz
        (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + 1)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n)
          (-(d : ℤ)) (-(e : ℤ)) (-(d : ℤ) + -(e : ℤ)) rfl
          ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A (m + 1) d).inv
            (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A (m + 1) d (ULift.up u)) ⊗ₜ[A]
            (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n e).inv
              (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n e (ULift.up v))) ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S q x)) =
      (-(d : ℤ) * -(e : ℤ)).negOnePow •
        ∑ s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + d) q, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSign s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u).val •
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorCoInsertionAction (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n) m n k
            (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction A S n)).f z
            (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n) (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (m + 1))
              (-(e : ℤ)) (-(d : ℤ) + -(q : ℤ)) z (by omega)
              ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n e).inv
                (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n e (ULift.up v)) ⊗ₜ[A]
                _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (m + 1)
                  (fun a => ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u) a,
                    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u) a)
                      (S.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.face s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u) a).op x)⟩)
                  (-(d : ℤ) + -(q : ℤ))
                  (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum_eq_sum, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree_sum]
                      have hnat : m + d + q + 1 - (m + 1) = d + q := by omega
                      rw [hnat]; omega))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.iteratedCochainAction_apply, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction_basis_cut_sum A S u x _ rfl]
  simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul, map_sum, map_zsmul]


end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
