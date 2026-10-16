module
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleParameters
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorElements

/-! # P変数の任意パラメータ作用を三重生成元で評価する -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]
variable {K : Complex A} {P P' : Bimodule A B C}
  (Q : Bimodule A C E) (R : Bimodule A E F) (τ : BimoduleParamTrans A B C K P P')

lemma tripleFirstLeft_element (b : B) (c : C) (e : E) (f : F)
    {p k r s i m n : ℤ} (x : K.X p) (t : (R.value e f).X k)
    (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hi : r + s = i) (hm : k + i = m) (hn : m + p = n) :
    (((firstParamHom A B E F R (firstParam A B C E Q τ) b f).f p x).v m n hn)
      (associatorLeftElement A B C E F P Q R b c e f t q v hi hm) =
    (p * k).negOnePow • ((p * r).negOnePow •
      associatorLeftElement A B C E F P' Q R b c e f t q
        ((((Bimodule.paramValue A B C τ b c).f p x).v s (p + s) (by omega)) v)
        (i := p + i) (by omega) (by omega)) := by
  change (((firstParamHom A B E F R (firstParam A B C E Q τ) b f).f p x).v m n hn)
    (BalancedTensor.element A E (R.rightAt f) ((compose A B C E P Q).leftAt b) e t
      (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v hi) hm) = _
  rw [firstParamHom_element, firstParam_value, firstParamHom_element,
    BalancedTensor.element_units_smul_right]
  rfl

lemma tripleFirstRight_element (b : B) (c : C) (e : E) (f : F)
    {p k r s l m n : ℤ} (x : K.X p) (t : (R.value e f).X k)
    (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hl : k + r = l) (hm : l + s = m) (hn : m + p = n) :
    (((firstParamHom A B C F (compose A C E F Q R) τ b f).f p x).v m n hn)
      (associatorRightElement A B C E F P Q R b c e f t q v hl hm) =
    (p * l).negOnePow • associatorRightElement A B C E F P' Q R b c e f t q
      ((((Bimodule.paramValue A B C τ b c).f p x).v s (p + s) (by omega)) v)
      hl (by omega) := by
  exact firstParamHom_element A B C F (compose A C E F Q R) τ b c f x
    (BalancedTensor.element A E (R.rightAt f) (Q.leftAt c) e t q hl) v hm hn

end SerrePositivity.DifferentialGraded.BimoduleTensor
