module

public import SerrePositivity.InfinityCategories.DoldKanComparison.StandardTopBoundary

/-!
# 立方体評価の微分と座標境界

概要：立方体評価の微分は各座標の1面と0面の評価の差の交代和である。
方針：最上位成分の微分を単体境界へ移し、最大旗の境界公式を使う。
規約：座標の番号付けが向きを固定する。ここでは次元二以上を扱う。
使われ方：HA 1.3.1.16、Kerodon 2.5.9 の比較写像の dg 方程式の境界側。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DoldKanComparison
open CategoryTheory DifferentialGraded DGNerve.PinchedHom
open scoped Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D] {x y : D}

/-- 概要：立方体の旗の評価の微分は、その旗の各面の評価の交代和である。
方針：標準 Hom の微分公式を適用し、単体集合の射の自然性で面を移す。
規約：次元 n+1 の旗から次数 −n の成分を得る。
使われ方：HA 1.3.1.16 の基本鎖の評価の微分を各旗で計算する。 -/
lemma cubeFlagEvaluation_d {T : Type u} {n : ℕ} (e : Fin (n + 1) ≃ T)
    (φ : Coherent.cube T ⟶ standardHomSpace (R := R) x y) :
    (homObject R D x y).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (cubeFlagEvaluation e φ) =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • standardTopEval (R := R) x y n
        (φ.app _ ((Coherent.cube T).δ j (cubeFlag e))) := by
  rw [cubeFlagEvaluation, standardTopEval_d]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact congrArg (standardTopEval (R := R) x y n)
    (φ.naturality_apply (SimplexCategory.δ j).op (cubeFlag e)).symm

/-- 概要：立方体の基本鎖の評価の微分は座標境界の評価の交代和である。
方針：線形性で旗ごとの微分へ移し、内部面を相殺した境界公式を適用する。
規約：次数 −(n+2) から −(n+1) の微分で、座標1面から0面を引く。
使われ方：HA 1.3.1.16 の比較写像の成分の微分公式。 -/
lemma cubeEvaluation_d {T : Type u} {n : ℕ} (e : Fin (n + 2) ≃ T)
    (φ : Coherent.cube T ⟶ standardHomSpace (R := R) x y) :
    (homObject R D x y).d (-((n + 2 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ)) (cubeEvaluation e φ) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        (cubeEvaluation (Equiv.ulift.symm : Fin (n + 1) ≃ ULift.{u} (Fin (n + 1)))
          (cubeFaceMap e i true ≫ φ) -
        cubeEvaluation (Equiv.ulift.symm : Fin (n + 1) ≃ ULift.{u} (Fin (n + 1)))
          (cubeFaceMap e i false ≫ φ)) := by
  change ((homObject R D x y).d (-((n + 2 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ))).hom
    (∑ σ : Equiv.Perm (Fin (n + 2)), (Equiv.Perm.sign σ : ℤ) •
      cubeFlagEvaluation (σ.trans e) φ) = _
  rw [map_sum]
  simp_rw [map_zsmul]
  refine (Finset.sum_congr rfl (fun σ _ ↦ ?_)).trans
    (cubeFlag_boundary_sum e
      (fun a ↦ standardTopEval (R := R) x y (n + 1) (φ.app _ a)))
  congr 1
  exact cubeFlagEvaluation_d (σ.trans e) φ

end SerrePositivity.InfinityCategories.DoldKanComparison
