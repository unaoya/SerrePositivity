module
public import SerrePositivity.KST.SConstruction.DGParameterConjugationReverse
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorParameters

/-! # 実 tensor 結合比較の逆による全パラメータ共役
概要：D レーンの任意 K の結合自然性を、実延長で使う逆比較の共役へ移す。
方針：元の全 Hom 可換式を比較共役へ移し、同じ実同型の逆律を使う。
規約：第一・中間因子の全次数変換を保つ。使われ方：実加群延長の入力横合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [Small.{u} B] [DGCategory A C] [Small.{u} C]
  [DGCategory A E] [Small.{u} E] [DGCategory A F]

/-- 第一因子の K 作用は、元の逆結合比較による共役で左括弧の作用を回収する。 -/
lemma bimoduleAssociator_firstParam_inverse_conjugation {K : Complex A}
    {P P' : Bimodule A B C} (Q : Bimodule A C E) (R : Bimodule A E F)
    (τ : BimoduleParamTrans A B C K P P') (f : F) :
    (BimoduleTensor.firstParam A B C F (BimoduleTensor.compose A C E F Q R) τ).app f ≫
        enrichedClosedIsoConjugation (Complex A)
          (BimoduleTensor.associatorRightModuleIso A B C E F P Q R f).symm
          (BimoduleTensor.associatorRightModuleIso A B C E F P' Q R f).symm =
      (BimoduleTensor.firstParam A B E F R (BimoduleTensor.firstParam A B C E Q τ)).app f :=
  enrichedClosedIsoConjugation_reverse (Complex A) _ _ _ _
    (enrichedConjugation_of_naturality (Complex A) _ _ _ _
      (BimoduleTensor.associator_firstParam A B C E F Q R τ f))

/-- 中間因子の K 作用は、元の逆結合比較による共役で左括弧の作用を回収する。 -/
lemma bimoduleAssociator_middleParam_inverse_conjugation {K : Complex A}
    (P : Bimodule A B C) {Q Q' : Bimodule A C E} (R : Bimodule A E F)
    (τ : BimoduleParamTrans A C E K Q Q') (f : F) :
    (BimoduleTensor.secondParam A B C F P (BimoduleTensor.firstParam A C E F R τ)).app f ≫
        enrichedClosedIsoConjugation (Complex A)
          (BimoduleTensor.associatorRightModuleIso A B C E F P Q R f).symm
          (BimoduleTensor.associatorRightModuleIso A B C E F P Q' R f).symm =
      (BimoduleTensor.firstParam A B E F R (BimoduleTensor.secondParam A B C E P τ)).app f :=
  enrichedClosedIsoConjugation_reverse (Complex A) _ _ _ _
    (enrichedConjugation_of_naturality (Complex A) _ _ _ _
      (BimoduleTensor.associator_middleParam A B C E F P R τ f))

end SerrePositivity.KST.SConstruction
