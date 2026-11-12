module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.PullbackHomCoordinates

/-! # Hom-fiber の閉じた右辺からの明示解

概要：比較の錐の整合条件から、最上位成分の微分方程式も満たす明示解を得る。
方針：三成分の線形同値の逆を右辺の負へ適用し、微分との可換性を使う。
規約：HTT §1.2.13、N7.1。使われ方：N7c の I=V の制約を含む線形充填。
この補題では整合条件を明示的に仮定し、実際の slice 境界からの導出は後続で行う。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded CochainComplex HomComplex

variable {A : Type u} [CommRing A] {X B C D : Complex A}

/-- 概要：Hom-fiber の比較の錐の右辺を解く全次数の明示的な持ち上げ。
方針：右辺の三成分を座標同値の逆で戻して負にする。
規約：HTT §1.2.13、N7.1。使われ方：錐の頂点へ向かう未知の最上位成分。 -/
def pullbackHomBoundaryLift (g : B ⟶ D) (h : C ⟶ D) (n : ℤ)
    (a : Cochain X B (n + 1)) (b : Cochain X C (n + 1)) (c : Cochain X D n) :
    Cochain X (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackFiber g h) (n + 1) :=
  -((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackHomCoordinates g h n).symm ((a, b), c))

/-- 概要：明示的な持ち上げの三座標は指定右辺の負。
方針：線形同値の負の保存と片側の逆則を使う。
規約：HTT §1.2.13、N7.1。使われ方：最上位を含む三つの線形方程式の検証。 -/
lemma pullbackHomBoundaryLift_coordinates (g : B ⟶ D) (h : C ⟶ D) (n : ℤ)
    (a : Cochain X B (n + 1)) (b : Cochain X C (n + 1)) (c : Cochain X D n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackHomCoordinates g h n (pullbackHomBoundaryLift g h n a b c) = -((a, b), c) := by
  rw [pullbackHomBoundaryLift, map_neg, LinearEquiv.apply_symm_apply]

/-- 概要：右辺の整合条件を満たす持ち上げは I=V の微分方程式も満たす。
方針：逆座標の微分を行列で展開し、整合条件と線形同値の逆則で相殺する。
規約：HTT §1.2.13、N7.1。使われ方：I=V の式を省略しない直接の線形充填。
整合条件が実際の境界から従うことは、この定理の主張に含めない。 -/
lemma pullbackHomBoundaryLift_differential (g : B ⟶ D) (h : C ⟶ D) (n : ℤ)
    (a : Cochain X B (n + 1)) (b : Cochain X C (n + 1)) (c : Cochain X D n)
    (r : Cochain X (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackFiber g h) (n + 1 + 1))
    (hR : ((δ (n + 1) (n + 1 + 1) a, δ (n + 1) (n + 1 + 1) b),
        (a.comp (Cochain.ofHom g) (add_zero (n + 1)) -
          b.comp (Cochain.ofHom h) (add_zero (n + 1))) - δ n (n + 1) c) =
      -(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackHomCoordinates g h (n + 1) r)) :
    δ (n + 1) (n + 1 + 1) (pullbackHomBoundaryLift g h n a b c) = r := by
  rw [pullbackHomBoundaryLift, δ_neg, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackHomCoordinates_symm_differential,
    hR, map_neg, LinearEquiv.symm_apply_apply, neg_neg]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
