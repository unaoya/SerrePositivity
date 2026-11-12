module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CubeOuterSigns

/-!
# 最大旗の外側境界の座標面への移送

概要：全最大旗の最初と最後の面の符号付き和は、座標1面−座標0面の符号付き和である。
方針：置換を固定座標と残りの置換に分解し、外側の面の等式と符号の式を適用する。
規約：評価値は任意の可換加法群でよい。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の基本鎖の境界公式。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory
open scoped _root_.Simplicial

/-- 概要：全最大旗の最初の面の和は全座標1面の最大旗の和である。
方針：最初の座標による置換の分解を有限和へ適用する。
規約：係数は固定座標の番号による (−1)^i。
使われ方：HA 1.3.1.16 の立方体の1面の境界。 -/
lemma cubeFlag_first_sum {T : Type u} {n : ℕ} (e : Fin (n + 2) ≃ T)
    {M : Type*} [AddCommGroup M] (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T) _⦋n + 1⦌ → M) :
    (∑ τ : Equiv.Perm (Fin (n + 2)), (Equiv.Perm.sign τ : ℤ) •
      F ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T).δ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (τ.trans e)))) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        ∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) •
          F ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceMap e i true).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (σ.trans Equiv.ulift.symm))) := by
  let H (τ : Equiv.Perm (Fin (n + 2))) := (Equiv.Perm.sign τ : ℤ) •
    F ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T).δ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (τ.trans e)))
  change (∑ τ, H τ) = _
  rw [← Fintype.sum_equiv Equiv.Perm.decomposeFin'.symm
    (H ∘ Equiv.Perm.decomposeFin'.symm) H (fun _ ↦ rfl), Fintype.sum_prod_type]
  simp only [Function.comp_apply, Equiv.Perm.decomposeFin'_symm, H]
  simp_rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFirstPermutation_sign, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag_face_first, mul_smul]
  simp only [Finset.smul_sum]

/-- 概要：全最大旗の最後の面の境界和は全座標0面の最大旗の和の負である。
方針：末尾指定の置換の同値で添字を移し、最後の面の符号を吸収する。
規約：最後の単体境界係数 (−1)^(n+2) を左辺に含む。
使われ方：HA 1.3.1.16 の立方体の0面の境界。 -/
lemma cubeFlag_last_sum {T : Type u} {n : ℕ} (e : Fin (n + 2) ≃ T)
    {M : Type*} [AddCommGroup M] (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T) _⦋n + 1⦌ → M) :
    (∑ τ : Equiv.Perm (Fin (n + 2)),
      ((-1 : ℤ) ^ (n + 2) * (Equiv.Perm.sign τ : ℤ)) •
        F ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T).δ (Fin.last (n + 2)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (τ.trans e)))) =
      -(∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        ∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) •
          F ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceMap e i false).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (σ.trans Equiv.ulift.symm)))) := by
  let H (τ : Equiv.Perm (Fin (n + 2))) :=
    ((-1 : ℤ) ^ (n + 2) * (Equiv.Perm.sign τ : ℤ)) •
      F ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T).δ (Fin.last (n + 2)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (τ.trans e)))
  change (∑ τ, H τ) = _
  rw [← Fintype.sum_equiv _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeLastPermutationEquiv
    (H ∘ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeLastPermutationEquiv) H (fun _ ↦ rfl), Fintype.sum_prod_type]
  simp only [Function.comp_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeLastPermutationEquiv_apply, H]
  simp_rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeLastBoundary_sign, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag_face_last, neg_smul, mul_smul]
  simp only [Finset.smul_sum, Finset.sum_neg_distrib]

/-- 概要：最大旗の二つの外側境界和は座標1面−座標0面の境界和に等しい。
方針：最初と最後の面の和の式を合わせて有限和とスカラー倍を分配する。
規約：内部面を除いた境界についての式。
使われ方：Kerodon 2.5.9（Tag 00SC） の基本鎖の立方体境界。 -/
lemma cubeFlag_outer_boundary_sum {T : Type u} {n : ℕ} (e : Fin (n + 2) ≃ T)
    {M : Type*} [AddCommGroup M] (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T) _⦋n + 1⦌ → M) :
    (∑ τ : Equiv.Perm (Fin (n + 2)), (Equiv.Perm.sign τ : ℤ) •
      F ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T).δ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (τ.trans e)))) +
      (∑ τ : Equiv.Perm (Fin (n + 2)),
        ((-1 : ℤ) ^ (n + 2) * (Equiv.Perm.sign τ : ℤ)) •
          F ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T).δ (Fin.last (n + 2)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (τ.trans e)))) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        ((∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) •
          F ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceMap e i true).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (σ.trans Equiv.ulift.symm)))) -
        (∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) •
          F ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceMap e i false).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (σ.trans Equiv.ulift.symm))))) := by
  rw [cubeFlag_first_sum, cubeFlag_last_sum, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact (smul_sub _ _ _).symm

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
