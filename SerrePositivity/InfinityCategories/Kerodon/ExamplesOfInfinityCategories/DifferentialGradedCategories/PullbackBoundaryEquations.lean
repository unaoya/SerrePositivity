module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.PullbackResidualMatrix

/-! # fiber の逆座標による境界の未知成分の方程式

概要：明示的な Hom-fiber の逆座標は先頭成分の微分と二つの脚・ホモトピーの式を解く。
方針：逆座標の三成分を評価し、残差の行列条件を微分との可換性へ渡す。
規約：HTT §1.2.13、N7.1。使われ方：直接の slice 境界充填の有限線形代数。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded CochainComplex HomComplex

variable {A : Type u} [CommRing A] {X B C D : Complex A}

/-- 概要：逆座標からの先頭成分の B 射影は指定した B 側右辺の負。
方針：逆座標の第一成分を評価する。
規約：HTT §1.2.13、N7.1。使われ方：未知の B 側成分を零とした方程式。 -/
lemma pullbackHomBoundaryLift_projectionB (g : B ⟶ D) (h : C ⟶ D) (q : ℤ)
    (rB : Cochain X B (q + 1)) (rC : Cochain X C (q + 1)) (rT : Cochain X D q) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackHomBoundaryLift g h q rB rC rT).comp
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB g h)) (add_zero (q + 1)) = -rB := by
  have H := congrArg (fun z => z.1.1) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackHomBoundaryLift_coordinates g h q rB rC rT)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackHomCoordinates g h q (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackHomBoundaryLift g h q rB rC rT)).1.1 = -rB at H
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackHomCoordinates_left_eq_comp] at H
  exact H

/-- 概要：逆座標からの先頭成分の C 射影は指定した C 側右辺の負。
方針：逆座標の第二成分を評価する。
規約：HTT §1.2.13、N7.1。使われ方：未知の C 側成分を零とした方程式。 -/
lemma pullbackHomBoundaryLift_projectionC (g : B ⟶ D) (h : C ⟶ D) (q : ℤ)
    (rB : Cochain X B (q + 1)) (rC : Cochain X C (q + 1)) (rT : Cochain X D q) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackHomBoundaryLift g h q rB rC rT).comp
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC g h)) (add_zero (q + 1)) = -rC := by
  have H := congrArg (fun z => z.1.2) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackHomBoundaryLift_coordinates g h q rB rC rT)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackHomCoordinates g h q (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackHomBoundaryLift g h q rB rC rT)).1.2 = -rC at H
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackHomCoordinates_right_eq_comp] at H
  exact H

/-- 概要：逆座標からの先頭成分と標準ホモトピーの合成は指定した第三右辺の負。
方針：逆座標の第三成分を評価する。
規約：HTT §1.2.13、N7.1。使われ方：二つの未知三角形成分を零とした差の方程式。 -/
lemma pullbackHomBoundaryLift_homotopy (g : B ⟶ D) (h : C ⟶ D) (q : ℤ)
    (rB : Cochain X B (q + 1)) (rC : Cochain X C (q + 1)) (rT : Cochain X D q) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackHomBoundaryLift g h q rB rC rT).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberNullHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference g h)) (by omega) = -rT := by
  have H := congrArg (fun z => z.2) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackHomBoundaryLift_coordinates g h q rB rC rT)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackHomCoordinates g h q (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackHomBoundaryLift g h q rB rC rT)).2 = -rT at H
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackHomCoordinates_homotopy_eq_comp] at H
  exact H

/-- 概要：先頭成分と対角射の合成は C 側右辺と h の合成の負。
方針：対角射が C 射影の後に h を合成したものであることと結合律を使う。
規約：HTT §1.2.13、N7.1。使われ方：D 側の未知成分の微分方程式。 -/
lemma pullbackHomBoundaryLift_diagonal (g : B ⟶ D) (h : C ⟶ D) (q : ℤ)
    (rB : Cochain X B (q + 1)) (rC : Cochain X C (q + 1)) (rT : Cochain X D q) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackHomBoundaryLift g h q rB rC rT).comp
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackDiagonal g h)) (add_zero (q + 1)) =
      -rC.comp (Cochain.ofHom h) (add_zero (q + 1)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackDiagonal, Cochain.ofHom_comp,
    ← Cochain.comp_assoc_of_second_is_zero_cochain,
    pullbackHomBoundaryLift_projectionC, Cochain.neg_comp]

/-- 概要：六成分の微分整合式を満たす右辺の明示解は先頭成分の微分方程式を満たす。
方針：整合式から行列条件を作り、逆座標の微分との可換性へ渡す。
規約：HTT §1.2.13、N7.1。使われ方：先頭の式 δa=r₀ の直接検証。
この補題の整合式は前提であり、実際の境界の移送後の導出は別途行う。 -/
lemma pullbackHomBoundaryLift_differential_of_residuals (g : B ⟶ D) (h : C ⟶ D) (q : ℤ)
    (r0 : Cochain X (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackFiber g h) (q + 1 + 1))
    (rB : Cochain X B (q + 1)) (rC : Cochain X C (q + 1))
    (rD : Cochain X D (q + 1)) (rBD rCD : Cochain X D q)
    (hB : δ (q + 1) (q + 1 + 1) rB =
      -r0.comp (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB g h)) (add_zero (q + 1 + 1)))
    (hC : δ (q + 1) (q + 1 + 1) rC =
      -r0.comp (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC g h)) (add_zero (q + 1 + 1)))
    (hBD : δ q (q + 1) rBD = rD - rB.comp (Cochain.ofHom g) (add_zero (q + 1)) -
      r0.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberNullHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference g h)) (by omega))
    (hCD : δ q (q + 1) rCD = rD - rC.comp (Cochain.ofHom h) (add_zero (q + 1))) :
    δ (q + 1) (q + 1 + 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackHomBoundaryLift g h q rB rC (rCD - rBD)) = r0 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackHomBoundaryLift_differential g h q rB rC (rCD - rBD) r0
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackResidual_matrix g h q r0 rB rC rD rBD rCD hB hC hBD hCD)

/-- 概要：D 側の未知成分を右三角形の右辺に取ると、D 側の微分方程式を満たす。
方針：C 側の整合式と先頭の明示解の対角射との合成を比較する。
規約：HTT §1.2.13、N7.1。使われ方：未知六成分のうち d=r_CD の式。
右三角形の整合式は前提であり、実際の境界については別途証明する。 -/
lemma pullbackBoundary_D_equation (g : B ⟶ D) (h : C ⟶ D) (q : ℤ)
    (rB : Cochain X B (q + 1)) (rC : Cochain X C (q + 1))
    (rD : Cochain X D (q + 1)) (rBD rCD : Cochain X D q)
    (hCD : δ q (q + 1) rCD = rD - rC.comp (Cochain.ofHom h) (add_zero (q + 1))) :
    δ q (q + 1) rCD =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackHomBoundaryLift g h q rB rC (rCD - rBD)).comp
        (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackDiagonal g h)) (add_zero (q + 1)) + rD := by
  rw [hCD, pullbackHomBoundaryLift_diagonal]
  abel

/-- 概要：左の三角形の未知成分を零とすると、明示解と d=r_CD はその方程式を満たす。
方針：先頭の明示解のホモトピー座標が二つの三角形の右辺の差の負であることを使う。
規約：HTT §1.2.13、N7.1。使われ方：未知 e=0 の左三角形の式。 -/
lemma pullbackBoundary_left_triangle_equation (g : B ⟶ D) (h : C ⟶ D) (q : ℤ)
    (rB : Cochain X B (q + 1)) (rC : Cochain X C (q + 1)) (rBD rCD : Cochain X D q) :
    (0 : Cochain X D q) = -rCD -
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackHomBoundaryLift g h q rB rC (rCD - rBD)).comp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberNullHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference g h)) (by omega) + rBD := by
  rw [pullbackHomBoundaryLift_homotopy]
  abel

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
