module
public import SerrePositivity.DifferentialGraded.Tensor.TripleParameterFirst

/-! # Q/R変数の任意パラメータ作用を三重生成元で評価する -/
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
variable {K : Complex A} (P : Bimodule A B C)

lemma tripleMiddleLeft_element {Q Q' : Bimodule A C E} (R : Bimodule A E F)
    (τ : BimoduleParamTrans A C E K Q Q') (b : B) (c : C) (e : E) (f : F)
    {p k r s i m n : ℤ} (x : K.X p) (t : (R.value e f).X k)
    (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hi : r + s = i) (hm : k + i = m) (hn : m + p = n) :
    (((firstParamHom A B E F R (secondParam A B C E P τ) b f).f p x).v m n hn)
      (associatorLeftElement A B C E F P Q R b c e f t q v hi hm) =
    (p * k).negOnePow • associatorLeftElement A B C E F P Q' R b c e f t
      ((((Bimodule.paramValue A C E τ c e).f p x).v r (p + r) (by omega)) q) v
      (i := p + i) (by omega) (by omega) := by
  change (((firstParamHom A B E F R (secondParam A B C E P τ) b f).f p x).v m n hn)
    (BalancedTensor.element A E (R.rightAt f) ((compose A B C E P Q).leftAt b) e t
      (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v hi) hm) = _
  rw [firstParamHom_element, secondParam_value, secondParamHom_element]
  rfl

lemma tripleMiddleRight_element {Q Q' : Bimodule A C E} (R : Bimodule A E F)
    (τ : BimoduleParamTrans A C E K Q Q') (b : B) (c : C) (e : E) (f : F)
    {p k r s l m n : ℤ} (x : K.X p) (t : (R.value e f).X k)
    (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hl : k + r = l) (hm : l + s = m) (hn : m + p = n) :
    (((secondParamHom A B C F P (firstParam A C E F R τ) b f).f p x).v m n hn)
      (associatorRightElement A B C E F P Q R b c e f t q v hl hm) =
    (p * k).negOnePow • associatorRightElement A B C E F P Q' R b c e f t
      ((((Bimodule.paramValue A C E τ c e).f p x).v r (p + r) (by omega)) q) v
      (l := p + l) (by omega) (by omega) := by
  change (((secondParamHom A B C F P (firstParam A C E F R τ) b f).f p x).v m n hn)
    (BalancedTensor.element A C ((compose A C E F Q R).rightAt f) (P.leftAt b) c
      (BalancedTensor.element A E (R.rightAt f) (Q.leftAt c) e t q hl) v hm) = _
  rw [secondParamHom_element, firstParam_value, firstParamHom_element,
    param_element_units_smul_left]
  rfl

lemma tripleLastLeft_element (Q : Bimodule A C E) {R R' : Bimodule A E F}
    (τ : BimoduleParamTrans A E F K R R') (b : B) (c : C) (e : E) (f : F)
    {p k r s i m n : ℤ} (x : K.X p) (t : (R.value e f).X k)
    (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hi : r + s = i) (hm : k + i = m) (hn : m + p = n) :
    (((secondParamHom A B E F (compose A B C E P Q) τ b f).f p x).v m n hn)
      (associatorLeftElement A B C E F P Q R b c e f t q v hi hm) =
    associatorLeftElement A B C E F P Q R' b c e f
      ((((Bimodule.paramValue A E F τ e f).f p x).v k (p + k) (by omega)) t) q v
      hi (by omega) :=
  secondParamHom_element A B E F (compose A B C E P Q) τ b e f x t
    (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v hi) hm hn

lemma tripleLastRight_element (Q : Bimodule A C E) {R R' : Bimodule A E F}
    (τ : BimoduleParamTrans A E F K R R') (b : B) (c : C) (e : E) (f : F)
    {p k r s l m n : ℤ} (x : K.X p) (t : (R.value e f).X k)
    (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hl : k + r = l) (hm : l + s = m) (hn : m + p = n) :
    (((secondParamHom A B C F P (secondParam A C E F Q τ) b f).f p x).v m n hn)
      (associatorRightElement A B C E F P Q R b c e f t q v hl hm) =
    associatorRightElement A B C E F P Q R' b c e f
      ((((Bimodule.paramValue A E F τ e f).f p x).v k (p + k) (by omega)) t) q v
      (l := p + l) (by omega) (by omega) := by
  change (((secondParamHom A B C F P (secondParam A C E F Q τ) b f).f p x).v m n hn)
    (BalancedTensor.element A C ((compose A C E F Q R).rightAt f) (P.leftAt b) c
      (BalancedTensor.element A E (R.rightAt f) (Q.leftAt c) e t q hl) v hm) = _
  rw [secondParamHom_element, secondParam_value, secondParamHom_element]
  rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
