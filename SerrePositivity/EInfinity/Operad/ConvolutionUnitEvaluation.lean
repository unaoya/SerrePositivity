module

public import SerrePositivity.EInfinity.Operad.ConvolutionEvaluation

/-!
# Convolution の一次評価と単位子

概要：Berger–Fresse §3.1 の convolution の単位則に必要な一次評価を比較する。
方針：tensorμ と左右単位子の整合性から、一次冪の余分な単位因子を消す。
規約：全ての等式は複体の chain map の等式である。
使われ方：convolution 演算の単位公理を通常の内部 Hom 評価へ帰着する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

/-- 概要：二つの右単位因子を含む評価は各単位子で縮約できる（BF §3.1）。
方針：右単位子のモノイダル性と評価射についての自然性を使う。
規約：任意の対称モノイダル圏の二項射に適用する。
使われ方：反復評価の一次冪を通常の評価へ直す。 -/
lemma tensorμ_rightUnit_evaluation {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [SymmetricCategory C] {X Y Z : C} (e : X ⊗ Y ⟶ Z) :
    tensorμ X (𝟙_ C) Y (𝟙_ C) ≫ (e ⊗ₘ (λ_ (𝟙_ C)).hom) ≫ (ρ_ Z).hom =
      ((ρ_ X).hom ⊗ₘ (ρ_ Y).hom) ≫ e := by
  rw [tensorHom_def', Category.assoc, rightUnitor_naturality]
  exact (rightUnitor_monoidal_assoc X Y e).symm

variable {A : Type u} [CommRing A]

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：一次の反復評価は一次冪の比較を介して通常の評価になる（BF §3.1）。
方針：反復評価の一段を展開し、二つの右単位因子の縮約を使う。
規約：入力・点・出力の一次冪の比較を全て明示する。
使われ方：convolution の単位則で余代数・代数の単位公理を適用する。 -/
@[reassoc]
lemma convolutionPowerEvaluation_one (H B : Complex A) :
    convolutionPowerEvaluation H B 1 ≫ (oneIso B).hom =
      ((oneIso (homComplex A H B)).hom ⊗ₘ (oneIso H).hom) ≫
        convolutionEvaluation H B := by
  change tensorμ (homComplex A H B) (𝟙_ (Complex A)) H (𝟙_ (Complex A)) ≫
    (convolutionEvaluation H B ⊗ₘ (λ_ (𝟙_ (Complex A))).hom) ≫ (ρ_ B).hom =
    ((ρ_ (homComplex A H B)).hom ⊗ₘ (ρ_ H).hom) ≫ convolutionEvaluation H B
  exact tensorμ_rightUnit_evaluation (C := Complex A)
    (X := homComplex A H B) (Y := H) (Z := B) (convolutionEvaluation H B)

/-- 概要：右転置の逆は通常の評価への前合成で計算できる（BF §3.1）。
方針：右 tensor 転置の自然性と恒等射の往復則を使う。
規約：任意の chain map から内部 Hom への射に適用する。
使われ方：代数公理の射の等式を評価後の等式で検査する。 -/
lemma convolutionEvaluation_uncurry {H B V : Complex A} (f : V ⟶ homComplex A H B) :
    uncurryRight f = (f ▷ H) ≫ convolutionEvaluation H B := by
  apply (tensorRightHomEquiv H V B).injective
  change curryRight _ = curryRight _
  rw [← tensorHom_id]
  rw [curryRight_uncurryRight, curryRight_naturality_source]
  simp only [convolutionEvaluation, curryRight_uncurryRight, Category.comp_id]

end SerrePositivity.EInfinity
