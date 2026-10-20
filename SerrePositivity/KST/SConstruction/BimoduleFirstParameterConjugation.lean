module
public import SerrePositivity.KST.SConstruction.BimoduleFirstParameterSquare
public import SerrePositivity.KST.SConstruction.DGConjugationNaturality

/-! # 実 tensor と任意パラメータの比較共役
概要：元の閉零比較同型を実 tensor へ送り、全パラメータ作用の共役後の一致を得る。
方針：実 tensor の通常関手で比較を移し、全 Hom 可換四角形を共役へ変換する。
規約：元の tensor 射・比較同型を保つ。使われ方：実加群延長の入力合成比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [Small.{u} B] [DGCategory A C] [Small.{u} C] [DGCategory A E]

/-- 第二因子を固定した、元の閉零双加群の実 tensor 関手。 -/
def bimoduleFirstTensorFunctor (Q : Bimodule A C E) :
    BimoduleCategory A B C ⥤ BimoduleCategory A B E :=
  (Functor.prod' (𝟭 (BimoduleCategory A B C))
    ((Functor.const (BimoduleCategory A B C)).obj (BimoduleCategory.of A C E Q))) ⋙
      BimoduleTensor.composeFunctor A B C E

/-- 元の比較同型を、同じ tensor 関手と右端の評価で移す。 -/
def bimoduleFirstTensorIsoAt (Q : Bimodule A C E)
    {P N : BimoduleCategory A B C} (a : P ≅ N) (e : E) :
    ForgetEnrichment.of (Complex A)
        ((BimoduleTensor.compose A B C E (BimoduleCategory.underlying A B C P) Q).rightAt e) ≅
      ForgetEnrichment.of (Complex A)
        ((BimoduleTensor.compose A B C E (BimoduleCategory.underlying A B C N) Q).rightAt e) :=
  (BimoduleCategory.evaluation A B E e).mapIso ((bimoduleFirstTensorFunctor A B C E Q).mapIso a)

/-- 任意 K の入力四角形は、元の実 tensor 比較による共役後の等号を与える。 -/
lemma bimoduleFirstParam_conjugation {K : Complex A}
    {P P' N N' : BimoduleCategory A B C}
    (τ : BimoduleParamTrans A B C K (BimoduleCategory.underlying A B C P)
      (BimoduleCategory.underlying A B C P'))
    (υ : BimoduleParamTrans A B C K (BimoduleCategory.underlying A B C N)
      (BimoduleCategory.underlying A B C N')) (a : P ≅ N) (a' : P' ≅ N')
    (h : ∀ c, τ.app c ≫ moduleHomPostcompose A B _ _ _ (a'.hom.val c) =
      υ.app c ≫ moduleHomPrecompose A B _ _ _ (a.hom.val c))
    (Q : Bimodule A C E) (e : E) :
    (BimoduleTensor.firstParam A B C E Q τ).app e ≫
        enrichedClosedIsoConjugation (Complex A)
          (bimoduleFirstTensorIsoAt A B C E Q a e) (bimoduleFirstTensorIsoAt A B C E Q a' e) =
      (BimoduleTensor.firstParam A B C E Q υ).app e := by
  apply enrichedConjugation_of_naturality (Complex A)
  exact bimoduleFirstParam_square A B C E τ υ a.hom a'.hom Q h e

end SerrePositivity.KST.SConstruction
