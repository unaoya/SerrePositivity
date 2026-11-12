module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardTopBoundary

/-!
# 立方体評価の微分と座標境界

概要：立方体評価の微分は各座標の1面と0面の評価の差の交代和である。
方針：最上位成分の微分を単体境界へ移し、最大旗の境界公式を使う。
規約：座標の番号付けが向きを固定する。ここでは次元二以上を扱う。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の比較写像の dg 方程式の境界側。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y : D}

/-- 概要：立方体の旗の評価の微分は、その旗の各面の評価の交代和である。
方針：標準 Hom の微分公式を適用し、単体集合の射の自然性で面を移す。
規約：次元 n+1 の旗から次数 −n の成分を得る。
使われ方：HA 1.3.1.16 の基本鎖の評価の微分を各旗で計算する。 -/
lemma cubeFlagEvaluation_d {T : Type u} {n : ℕ} (e : Fin (n + 1) ≃ T)
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y) :
    (homObject R D x y).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlagEvaluation e φ) =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := R) x y n
        (φ.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T).δ j (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlagEvaluation, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval_d]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := R) x y n)
    (φ.naturality_apply (SimplexCategory.δ j).op (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e)).symm

/-- 概要：立方体の基本鎖の評価の微分は座標境界の評価の交代和である。
方針：線形性で旗ごとの微分へ移し、内部面を相殺した境界公式を適用する。
規約：次数 −(n+2) から −(n+1) の微分で、座標1面から0面を引く。
使われ方：HA 1.3.1.16 の比較写像の成分の微分公式。 -/
lemma cubeEvaluation_d {T : Type u} {n : ℕ} (e : Fin (n + 2) ≃ T)
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y) :
    (homObject R D x y).d (-((n + 2 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation e φ) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation (Equiv.ulift.symm : Fin (n + 1) ≃ ULift.{u} (Fin (n + 1)))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceMap e i true ≫ φ) -
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation (Equiv.ulift.symm : Fin (n + 1) ≃ ULift.{u} (Fin (n + 1)))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceMap e i false ≫ φ)) := by
  change ((_root_.SerrePositivity.DifferentialGraded.homObject R D x y).d (-((n + 2 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ))).hom
    (∑ σ : Equiv.Perm (Fin (n + 2)), (Equiv.Perm.sign σ : ℤ) •
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlagEvaluation (σ.trans e) φ) = _
  rw [map_sum]
  simp_rw [map_zsmul]
  refine (Finset.sum_congr rfl (fun σ _ ↦ ?_)).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag_boundary_sum e
      (fun a ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := R) x y (n + 1) (φ.app _ a)))
  congr 1
  exact cubeFlagEvaluation_d (σ.trans e) φ

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
