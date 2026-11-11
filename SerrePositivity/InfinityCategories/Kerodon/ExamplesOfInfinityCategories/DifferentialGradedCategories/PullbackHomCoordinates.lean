module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FiberConeVertex
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.BiproductHomCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FiberHomProjection

/-! # 引き戻し fiber への Hom の三成分表示

概要：標準 fiber への Hom は B・C への成分と D への一段低い成分の三つと線形に同値。
方針：fiber の二成分と直和の二成分を合成し、微分が N7.1 の行列となることを示す。
規約：HTT §1.2.13、N7.1。使われ方：slice 境界の六成分方程式の全次数の明示解。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Limits DifferentialGraded CochainComplex HomComplex

variable {A : Type u} [CommRing A] {X B C D : Complex A}

/-- 概要：標準引き戻し fiber への Hom の全次数の三成分 A 線形同値。
方針：fiber の座標の第一成分を直和の二射影で分解する。
規約：HTT §1.2.13、N7.1。使われ方：Hom(X,P) の厳密な fiber の座標。 -/
def pullbackHomCoordinates (g : B ⟶ D) (h : C ⟶ D) (n : ℤ) :
    Cochain X (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackFiber g h) (n + 1) ≃ₗ[A]
      ((Cochain X B (n + 1) × Cochain X C (n + 1)) × Cochain X D n) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberHomCoordinates (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference g h) n).trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.biproductHomCoordinates X B C (n + 1)).prodCongr (LinearEquiv.refl A _))

/-- 概要：三成分から fiber への復元は、二つの脚を直和にまとめて fiber へ復元する。
方針：二つの線形同値の合成の逆を評価する。
規約：HTT §1.2.13、N7.1。使われ方：明示解の成分計算。 -/
lemma pullbackHomCoordinates_symm (g : B ⟶ D) (h : C ⟶ D) (n : ℤ)
    (a : (Cochain X B (n + 1) × Cochain X C (n + 1)) × Cochain X D n) :
    (pullbackHomCoordinates g h n).symm a =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberHomCoordinates (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference g h) n).symm
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.biproductHomCoordinates X B C (n + 1)).symm a.1, a.2) := rfl

/-- 概要：直和へ復元した成分に差の射を後合成すると二つの脚の差になる。
方針：二包含と差の射の合成を評価する。
規約：HTT §1.2.13、N7.1。使われ方：fiber の微分の三成分表示。 -/
lemma biproductHomCoordinates_comp_difference (g : B ⟶ D) (h : C ⟶ D) (n : ℤ)
    (a : Cochain X B n) (b : Cochain X C n) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.biproductHomCoordinates X B C n).symm (a, b)).comp
        (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference g h)) (add_zero n) =
      a.comp (Cochain.ofHom g) (add_zero n) - b.comp (Cochain.ofHom h) (add_zero n) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.biproductHomCoordinates_symm, Cochain.add_comp,
    Cochain.comp_assoc_of_second_is_zero_cochain, ← Cochain.ofHom_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference, biprod.inl_desc, biprod.inr_desc, Cochain.ofHom_neg, Cochain.comp_neg,
    sub_eq_add_neg]

/-- 概要：三成分の逆座標写像は fiber の行列微分と可換。
方針：fiber と直和の二つの微分保存の式を合成する。
規約：HTT §1.2.13、N7.1。使われ方：Hom-fiber の厳密な複体の比較と明示的充填。 -/
lemma pullbackHomCoordinates_symm_differential (g : B ⟶ D) (h : C ⟶ D) (n : ℤ)
    (a : Cochain X B (n + 1)) (b : Cochain X C (n + 1)) (c : Cochain X D n) :
    δ (n + 1) (n + 1 + 1) ((pullbackHomCoordinates g h n).symm ((a, b), c)) =
      (pullbackHomCoordinates g h (n + 1)).symm
        ((δ (n + 1) (n + 1 + 1) a, δ (n + 1) (n + 1 + 1) b),
          (a.comp (Cochain.ofHom g) (add_zero (n + 1)) -
            b.comp (Cochain.ofHom h) (add_zero (n + 1))) - δ n (n + 1) c) := by
  rw [pullbackHomCoordinates_symm, pullbackHomCoordinates_symm,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberHomCoordinates_symm_differential, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.biproductHomCoordinates_symm_differential,
    biproductHomCoordinates_comp_difference]

/-- 概要：三成分表示の B 座標は標準の B への脚との後合成。
方針：fiber の第一座標と直和の第一射影を合成し、結合律を使う。
規約：HTT §1.2.13、N7.1。使われ方：錐の B 成分の比較。 -/
lemma pullbackHomCoordinates_left_eq_comp (g : B ⟶ D) (h : C ⟶ D) (n : ℤ)
    (a : Cochain X (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackFiber g h) (n + 1)) :
    (pullbackHomCoordinates g h n a).1.1 =
      a.comp (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB g h)) (add_zero (n + 1)) := by
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberHomCoordinates (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference g h) n a).1).comp
    (Cochain.ofHom biprod.fst) (add_zero (n + 1)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberHomCoordinates_fst_eq_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB, Cochain.ofHom_comp]
  exact Cochain.comp_assoc_of_second_is_zero_cochain _ _ _ (add_zero (n + 1))

/-- 概要：三成分表示の C 座標は標準の C への脚との後合成。
方針：fiber の第一座標と直和の第二射影を合成し、結合律を使う。
規約：HTT §1.2.13、N7.1。使われ方：錐の C 成分の比較。 -/
lemma pullbackHomCoordinates_right_eq_comp (g : B ⟶ D) (h : C ⟶ D) (n : ℤ)
    (a : Cochain X (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackFiber g h) (n + 1)) :
    (pullbackHomCoordinates g h n a).1.2 =
      a.comp (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC g h)) (add_zero (n + 1)) := by
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberHomCoordinates (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference g h) n a).1).comp
    (Cochain.ofHom biprod.snd) (add_zero (n + 1)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberHomCoordinates_fst_eq_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC, Cochain.ofHom_comp]
  exact Cochain.comp_assoc_of_second_is_zero_cochain _ _ _ (add_zero (n + 1))

/-- 概要：三成分表示の D 座標は標準ホモトピーとの後合成。
方針：fiber の第二座標と標準ホモトピーの計算を使う。
規約：HTT §1.2.13、N7.1。使われ方：錐の二つの三角形の差の比較。 -/
lemma pullbackHomCoordinates_homotopy_eq_comp (g : B ⟶ D) (h : C ⟶ D) (n : ℤ)
    (a : Cochain X (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackFiber g h) (n + 1)) :
    (pullbackHomCoordinates g h n a).2 =
      a.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberNullHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference g h)) (by omega) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberHomCoordinates_snd_eq_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference g h) n a

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
