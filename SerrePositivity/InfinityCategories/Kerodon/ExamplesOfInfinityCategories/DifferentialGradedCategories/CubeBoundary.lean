module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CubeOuterBoundary

/-!
# 最大旗の基本鎖の立方体境界公式

概要：全最大旗の交代境界の符号付き和は、各座標の1面−0面の符号付き和である。
方針：単体の境界和を両端と内部に分け、内部面を相殺し、両端を座標面へ移す。
規約：ここでは任意の可換加法群で評価する鎖の等式を証明する。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の dg 単体の方程式の境界計算。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory
open scoped _root_.Simplicial

/-- 概要：最大旗の全ての内部境界項の符号付き二重和は零である。
方針：和の順序を交換し、各内部面の対合による相殺を使う。
規約：単体の面の係数と置換の係数の両方を含める。
使われ方：Kerodon 2.5.9（Tag 00SC） の基本鎖の内部境界の消去。 -/
lemma cubeFlag_all_internal_sum_eq_zero {T : Type u} {n : ℕ} (e : Fin (n + 2) ≃ T)
    {M : Type*} [AddCommGroup M] (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T) _⦋n + 1⦌ → M) :
    (∑ σ : Equiv.Perm (Fin (n + 2)), ∑ r : Fin (n + 1), (Equiv.Perm.sign σ : ℤ) •
      ((-1 : ℤ) ^ (r.val + 1)) •
        F ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T).δ r.succ.castSucc (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (σ.trans e)))) = 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro r _
  have he : (∑ σ : Equiv.Perm (Fin (n + 2)), (Equiv.Perm.sign σ : ℤ) •
      ((-1 : ℤ) ^ (r.val + 1)) •
        F ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T).δ r.succ.castSucc (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (σ.trans e)))) =
      ((-1 : ℤ) ^ (r.val + 1)) •
        ∑ σ : Equiv.Perm (Fin (n + 2)), (Equiv.Perm.sign σ : ℤ) •
          F ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T).δ r.succ.castSucc (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (σ.trans e))) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    exact smul_comm _ _ _
  rw [he, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag_internal_sum_eq_zero, smul_zero]

/-- 概要：最大旗の全境界和は内部面を除いた最初と最後の面の和に等しい。
方針：面の和の先頭と末尾を分け、内部境界の二重和を零にする。
規約：最後の面の係数は (−1)^(n+2)。
使われ方：HA 1.3.1.16 の基本鎖の境界の外側への還元。 -/
lemma cubeFlag_boundary_eq_outer_sum {T : Type u} {n : ℕ} (e : Fin (n + 2) ≃ T)
    {M : Type*} [AddCommGroup M] (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T) _⦋n + 1⦌ → M) :
    (∑ σ : Equiv.Perm (Fin (n + 2)), (Equiv.Perm.sign σ : ℤ) •
      ∑ j : Fin (n + 3), (-1 : ℤ) ^ j.val •
        F ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T).δ j (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (σ.trans e)))) =
      (∑ σ : Equiv.Perm (Fin (n + 2)), (Equiv.Perm.sign σ : ℤ) •
        F ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T).δ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (σ.trans e)))) +
      (∑ σ : Equiv.Perm (Fin (n + 2)),
        ((-1 : ℤ) ^ (n + 2) * (Equiv.Perm.sign σ : ℤ)) •
          F ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T).δ (Fin.last (n + 2)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (σ.trans e)))) := by
  let B (σ : Equiv.Perm (Fin (n + 2))) (j : Fin (n + 3)) :=
    (-1 : ℤ) ^ j.val • F ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T).δ j (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (σ.trans e)))
  have hb (σ : Equiv.Perm (Fin (n + 2))) : (∑ j, B σ j) =
      B σ 0 + (∑ r : Fin (n + 1), B σ r.succ.castSucc) + B σ (Fin.last (n + 2)) := by
    rw [Fin.sum_univ_succ (B σ),
      Fin.sum_univ_castSucc (fun j : Fin (n + 2) ↦ B σ j.succ)]
    exact (add_assoc (B σ 0) (∑ r : Fin (n + 1), B σ r.succ.castSucc)
      (B σ (Fin.last (n + 2)))).symm
  change (∑ σ, (Equiv.Perm.sign σ : ℤ) • ∑ j, B σ j) = _
  simp_rw [hb, smul_add, Finset.smul_sum]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hi : (∑ σ : Equiv.Perm (Fin (n + 2)), ∑ r : Fin (n + 1),
      (Equiv.Perm.sign σ : ℤ) • B σ r.succ.castSucc) = 0 :=
    cubeFlag_all_internal_sum_eq_zero e F
  rw [hi, add_zero]
  simp only [B, Fin.val_zero, pow_zero, one_smul, Fin.val_last]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  rw [← mul_smul, mul_comm]

/-- 概要：全最大旗の交代境界の符号付き和は立方体の座標境界に等しい。
方針：内部境界を消し、外側の面の座標面への式を適用する。
規約：座標 i の係数は (−1)^i、座標1面から座標0面を引く。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の比較写像の基本鎖の境界公式。 -/
lemma cubeFlag_boundary_sum {T : Type u} {n : ℕ} (e : Fin (n + 2) ≃ T)
    {M : Type*} [AddCommGroup M] (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T) _⦋n + 1⦌ → M) :
    (∑ σ : Equiv.Perm (Fin (n + 2)), (Equiv.Perm.sign σ : ℤ) •
      ∑ j : Fin (n + 3), (-1 : ℤ) ^ j.val •
        F ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T).δ j (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (σ.trans e)))) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        ((∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) •
          F ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceMap e i true).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (σ.trans Equiv.ulift.symm)))) -
        (∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) •
          F ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceMap e i false).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (σ.trans Equiv.ulift.symm))))) :=
  (cubeFlag_boundary_eq_outer_sum e F).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag_outer_boundary_sum e F)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
