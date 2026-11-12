module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.PullbackHomLift

/-! # 六成分の残差整合条件と fiber の行列条件

概要：先頭・脚・二三角形の微分整合式は Hom-fiber の閉じた右辺の行列条件を与える。
方針：二つの三角形の式を引き、D 側の共通の右辺を消して三座標を比較する。
規約：HTT §1.2.13、N7.1。使われ方：直接充填の先頭成分の微分方程式を含む明示解。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded CochainComplex HomComplex

variable {A : Type u} [CommRing A] {X B C D : Complex A}

/-- 概要：六成分の微分整合式から、三座標の右辺の微分は先頭右辺の像の負になる。
方針：各座標を標準射影・ホモトピーとの合成で書き、三角形の差の微分で共通の D 側成分を消す。
規約：HTT §1.2.13、N7.1。使われ方：実際の境界の整合条件から Hom-fiber の逆座標へ渡す条件。
この補題の整合式は明示的な前提であり、実際の境界からの導出は別途行う。 -/
lemma pullbackResidual_matrix (g : B ⟶ D) (h : C ⟶ D) (q : ℤ)
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
    ((δ (q + 1) (q + 1 + 1) rB, δ (q + 1) (q + 1 + 1) rC),
      (rB.comp (Cochain.ofHom g) (add_zero (q + 1)) -
        rC.comp (Cochain.ofHom h) (add_zero (q + 1))) - δ q (q + 1) (rCD - rBD)) =
      -(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackHomCoordinates g h (q + 1) r0) := by
  apply Prod.ext
  · apply Prod.ext
    · change δ (q + 1) (q + 1 + 1) rB = -(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackHomCoordinates g h (q + 1) r0).1.1
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackHomCoordinates_left_eq_comp, hB]
    · change δ (q + 1) (q + 1 + 1) rC = -(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackHomCoordinates g h (q + 1) r0).1.2
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackHomCoordinates_right_eq_comp, hC]
  · change (rB.comp (Cochain.ofHom g) (add_zero (q + 1)) -
        rC.comp (Cochain.ofHom h) (add_zero (q + 1))) - δ q (q + 1) (rCD - rBD) =
      -(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackHomCoordinates g h (q + 1) r0).2
    rw [δ_sub, hCD, hBD, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackHomCoordinates_homotopy_eq_comp]
    abel

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
