module

public import SerrePositivity.DifferentialGraded.Tensor.Associator.Components
public import SerrePositivity.DifferentialGraded.Bimodule.Value
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.Actions
public import SerrePositivity.DifferentialGraded.Tensor.Enriched
public import SerrePositivity.DifferentialGraded.Tensor.BalancedElements
public import SerrePositivity.DifferentialGraded.Tensor.Fubini
public import SerrePositivity.DifferentialGraded.Bimodule.Basic

/-!
# Tensor.Triple

## 概要
15 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## AssociatorValueEvaluation（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorValueEvaluation.lean） -/

/-! # 閉零bimodule結合同型の値の複体への評価 -/

@[expose] public section AssociatorValueEvaluation
universe u v w z t

noncomputable section
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

@[simp]
lemma associatorIso_hom_value_eval (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (d : F) :
    (BimoduleCategory.valueEvaluation A B F b d).map (associatorIso A B C E F P Q R).hom =
      (associatorValueIso A B C E F P Q R b d).hom :=
  associatorRightModuleIso_hom_eval A B C E F P Q R b d

@[simp]
lemma associatorIso_inv_value_eval (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (d : F) :
    (BimoduleCategory.valueEvaluation A B F b d).map (associatorIso A B C E F P Q R).inv =
      (associatorValueIso A B C E F P Q R b d).inv :=
  associatorRightModuleIso_inv_eval A B C E F P Q R b d

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorValueEvaluation

/-! ## AssociatorIsoElements（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorIsoElements.lean） -/

/-! # 閉零bimodule結合同型の値を三重生成元で評価する -/

@[expose] public section AssociatorIsoElements
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

lemma associatorIso_hom_value_element (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (d : F) {k r s i l n : ℤ}
    (τ : (R.value e d).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    ((BimoduleCategory.valueEvaluation A B F b d).map
      (associatorIso A B C E F P Q R).hom).f n
      (associatorLeftElement A B C E F P Q R b c e d τ q v hi hn) =
    associatorRightElement A B C E F P Q R b c e d τ q v hl (by omega) := by
  have h := (associatorIso_hom_value_eval A B C E F P Q R b d).trans
    (associatorValueHom_eq A B C E F P Q R b d).symm
  have he := congrArg (fun a : (compose A B E F (compose A B C E P Q) R).value b d ⟶
      (compose A B C F P (compose A C E F Q R)).value b d =>
    a.f n (associatorLeftElement A B C E F P Q R b c e d τ q v hi hn)) h
  exact he.trans (associatorValueComponent_element A B C E F P Q R b c e d τ q v hi hl hn)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorIsoElements

/-! ## QuadElements（旧 SerrePositivity/DifferentialGraded/Tensor/QuadElements.lean） -/

/-! # 四つのbimoduleの両端括弧付けにおける四重斉次生成元 -/

@[expose] public section QuadElements
universe u v w z t x

noncomputable section
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  (F : Type t) (G : Type x)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]

/-- 合成の完全左括弧付け（値はS⊗(R⊗(Q⊗P))）の四重生成元。 -/
def quadLeftElement (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (S : Bimodule A F G)
    (b : B) (c : C) (e : E) (f : F) (g : G) {a k r s i m n : ℤ}
    (σ : (S.value f g).X a) (τ : (R.value e f).X k)
    (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hi : r + s = i) (hm : k + i = m) (hn : a + m = n) :
    ((compose A B F G (compose A B E F (compose A B C E P Q) R) S).value b g).X n :=
  BalancedTensor.element A F (S.rightAt g)
    ((compose A B E F (compose A B C E P Q) R).leftAt b) f σ
    (associatorLeftElement A B C E F P Q R b c e f τ q v hi hm) hn

/-- 合成の完全右括弧付け（値は((S⊗R)⊗Q)⊗P）の四重生成元。 -/
def quadRightElement (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (S : Bimodule A F G)
    (b : B) (c : C) (e : E) (f : F) (g : G) {a k r s l j n : ℤ}
    (σ : (S.value f g).X a) (τ : (R.value e f).X k)
    (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hl : a + k = l) (hj : l + r = j) (hn : j + s = n) :
    ((compose A B C G P (compose A C E G Q (compose A E F G R S))).value b g).X n :=
  BalancedTensor.element A C ((compose A C E G Q (compose A E F G R S)).rightAt g)
    (P.leftAt b) c (associatorRightElement A C E F G Q R S c e f g σ τ q hl hj) v hn

/-- 五角の長い経路の中間（値は(S⊗(R⊗Q))⊗P）の生成元。 -/
def quadMiddleElement (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (S : Bimodule A F G)
    (b : B) (c : C) (e : E) (f : F) (g : G) {a k r s z j n : ℤ}
    (σ : (S.value f g).X a) (τ : (R.value e f).X k)
    (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hz : k + r = z) (hj : a + z = j) (hn : j + s = n) :
    ((compose A B C G P (compose A C F G (compose A C E F Q R) S)).value b g).X n :=
  BalancedTensor.element A C ((compose A C F G (compose A C E F Q R) S).rightAt g)
    (P.leftAt b) c (associatorLeftElement A C E F G Q R S c e f g σ τ q hz hj) v hn

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end QuadElements

/-! ## QuadCochainExt（旧 SerrePositivity/DifferentialGraded/Tensor/QuadCochainExt.lean） -/

/-! # 四重生成元による完全左反復tensorからのcochainの外延性 -/

@[expose] public section QuadCochainExt
universe u v w z t x

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  (F : Type t) (G : Type x)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]

lemma quadLeft_cochain_element_ext (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (S : Bimodule A F G) (b : B) (g : G)
    {T : Complex A} {p : ℤ}
    (u v : Cochain ((compose A B F G (compose A B E F (compose A B C E P Q) R) S).value b g) T p)
    (heq : ∀ (c : C) (e : E) (f : F) (a k r s i m n t : ℤ)
      (hi : r + s = i) (hm : k + i = m) (hn : a + m = n) (ht : n + p = t)
      (σ : (S.value f g).X a) (τ : (R.value e f).X k)
      (q : (Q.value c e).X r) (w : (P.value b c).X s),
      u.v n t ht (quadLeftElement A B C E F G P Q R S b c e f g σ τ q w hi hm hn) =
        v.v n t ht (quadLeftElement A B C E F G P Q R S b c e f g σ τ q w hi hm hn)) : u = v := by
  apply BalancedTensor.cochain_element_ext A F (S.rightAt g)
    ((compose A B E F (compose A B C E P Q) R).leftAt b)
  intro f a m n t hn ht σ z
  let K := (compose A B E F (compose A B C E P Q) R).value b f
  let L : K.X m →ₗ[A] T.X t := (u.v n t ht).hom.comp
    (((BalancedTensor.ι A F (S.rightAt g)
      ((compose A B E F (compose A B C E P Q) R).leftAt b) f).f n).hom.comp
        ((ιTensorObj (S.value f g) K a m n hn).hom.comp (TensorProduct.mk A _ _ σ)))
  let H : K.X m →ₗ[A] T.X t := (v.v n t ht).hom.comp
    (((BalancedTensor.ι A F (S.rightAt g)
      ((compose A B E F (compose A B C E P Q) R).leftAt b) f).f n).hom.comp
        ((ιTensorObj (S.value f g) K a m n hn).hom.comp (TensorProduct.mk A _ _ σ)))
  have hh : ModuleCat.ofHom L = ModuleCat.ofHom H := by
    apply associatorLeft_degree_element_ext A B C E F P Q R b f
    intro c e k r s i hi hm τ q w
    exact heq c e f a k r s i m n t hi hm hn ht σ τ q w
  exact congrArg (fun j => j z) hh

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end QuadCochainExt

/-! ## TripleMapElements（旧 SerrePositivity/DifferentialGraded/Tensor/TripleMapElements.lean） -/

/-! # 反復tensor mapの三重斉次生成元上の評価 -/

@[expose] public section TripleMapElements
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]
variable {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
  {R R' : BimoduleCategory A E F}

lemma leftTripleMap_element (f : P ⟶ P') (g : Q ⟶ Q') (h : R ⟶ R')
    (b : B) (c : C) (e : E) (d : F) {k r s i n : ℤ}
    (τ : ((BimoduleCategory.underlying A E F R).value e d).X k)
    (q : ((BimoduleCategory.underlying A C E Q).value c e).X r)
    (v : ((BimoduleCategory.underlying A B C P).value b c).X s)
    (hi : r + s = i) (hn : k + i = n) :
    (composeValueMap A B E F (composeMap A B C E f g) h b d).f n
      (associatorLeftElement A B C E F (BimoduleCategory.underlying A B C P)
        (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R)
        b c e d τ q v hi hn) =
    associatorLeftElement A B C E F (BimoduleCategory.underlying A B C P')
      (BimoduleCategory.underlying A C E Q') (BimoduleCategory.underlying A E F R') b c e d
      (((BimoduleCategory.valueEvaluation A E F e d).map h).f k τ)
      (((BimoduleCategory.valueEvaluation A C E c e).map g).f r q)
      (((BimoduleCategory.valueEvaluation A B C b c).map f).f s v) hi hn := by
  let x := BalancedTensor.element A C ((BimoduleCategory.underlying A C E Q).rightAt e)
    ((BimoduleCategory.underlying A B C P).leftAt b) c q v hi
  have ho := composeValueMap_element A B E F (composeMap A B C E f g) h b e d τ x hn
  have hv := congrArg (fun z :
      (compose A B C E (BimoduleCategory.underlying A B C P)
        (BimoduleCategory.underlying A C E Q)).value b e ⟶
      (compose A B C E (BimoduleCategory.underlying A B C P')
        (BimoduleCategory.underlying A C E Q')).value b e => z.f i x)
    (composeMap_value_eval A B C E f g b e)
  have hi₀ := hv.trans (composeValueMap_element A B C E f g b c e q v hi)
  exact ho.trans (congrArg (fun z :
      ((compose A B C E (BimoduleCategory.underlying A B C P')
        (BimoduleCategory.underlying A C E Q')).value b e).X i =>
    BalancedTensor.element A E ((BimoduleCategory.underlying A E F R').rightAt d)
      ((compose A B C E (BimoduleCategory.underlying A B C P')
        (BimoduleCategory.underlying A C E Q')).leftAt b) e
      (((BimoduleCategory.valueEvaluation A E F e d).map h).f k τ) z hn) hi₀)

lemma rightTripleMap_element (f : P ⟶ P') (g : Q ⟶ Q') (h : R ⟶ R')
    (b : B) (c : C) (e : E) (d : F) {k r s l n : ℤ}
    (τ : ((BimoduleCategory.underlying A E F R).value e d).X k)
    (q : ((BimoduleCategory.underlying A C E Q).value c e).X r)
    (v : ((BimoduleCategory.underlying A B C P).value b c).X s)
    (hl : k + r = l) (hn : l + s = n) :
    (composeValueMap A B C F f (composeMap A C E F g h) b d).f n
      (associatorRightElement A B C E F (BimoduleCategory.underlying A B C P)
        (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R)
        b c e d τ q v hl hn) =
    associatorRightElement A B C E F (BimoduleCategory.underlying A B C P')
      (BimoduleCategory.underlying A C E Q') (BimoduleCategory.underlying A E F R') b c e d
      (((BimoduleCategory.valueEvaluation A E F e d).map h).f k τ)
      (((BimoduleCategory.valueEvaluation A C E c e).map g).f r q)
      (((BimoduleCategory.valueEvaluation A B C b c).map f).f s v) hl hn := by
  let x := BalancedTensor.element A E ((BimoduleCategory.underlying A E F R).rightAt d)
    ((BimoduleCategory.underlying A C E Q).leftAt c) e τ q hl
  have ho := composeValueMap_element A B C F f (composeMap A C E F g h) b c d x v hn
  have hv := congrArg (fun z :
      (compose A C E F (BimoduleCategory.underlying A C E Q)
        (BimoduleCategory.underlying A E F R)).value c d ⟶
      (compose A C E F (BimoduleCategory.underlying A C E Q')
        (BimoduleCategory.underlying A E F R')).value c d => z.f l x)
    (composeMap_value_eval A C E F g h c d)
  have hi₀ := hv.trans (composeValueMap_element A C E F g h c e d τ q hl)
  exact ho.trans (congrArg (fun z :
      ((compose A C E F (BimoduleCategory.underlying A C E Q')
        (BimoduleCategory.underlying A E F R')).value c d).X l =>
    BalancedTensor.element A C
      ((compose A C E F (BimoduleCategory.underlying A C E Q')
        (BimoduleCategory.underlying A E F R')).rightAt d)
      ((BimoduleCategory.underlying A B C P').leftAt b) c z
      (((BimoduleCategory.valueEvaluation A B C b c).map f).f s v) hn) hi₀)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end TripleMapElements

/-! ## TripleMapComponents（旧 SerrePositivity/DifferentialGraded/Tensor/TripleMapComponents.lean） -/

/-! # 反復tensor mapの三重斉次生成元上の評価 -/

@[expose] public section TripleMapComponents
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]
variable {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
  {R R' : BimoduleCategory A E F}

lemma leftTripleComponent_element (f : P ⟶ P') (g : Q ⟶ Q') (h : R ⟶ R')
    (b : B) (c : C) (e : E) (d : F) {k r s i n : ℤ}
    (τ : ((BimoduleCategory.underlying A E F R).value e d).X k)
    (q : ((BimoduleCategory.underlying A C E Q).value c e).X r)
    (v : ((BimoduleCategory.underlying A B C P).value b c).X s)
    (hi : r + s = i) (hn : k + i = n) :
    composeMapComponent A B E F (composeMap A B C E f g) h b d n
      (associatorLeftElement A B C E F (BimoduleCategory.underlying A B C P)
        (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R)
        b c e d τ q v hi hn) =
    associatorLeftElement A B C E F (BimoduleCategory.underlying A B C P')
      (BimoduleCategory.underlying A C E Q') (BimoduleCategory.underlying A E F R') b c e d
      (((BimoduleCategory.valueEvaluation A E F e d).map h).f k τ)
      (((BimoduleCategory.valueEvaluation A C E c e).map g).f r q)
      (((BimoduleCategory.valueEvaluation A B C b c).map f).f s v) hi hn :=
  (composeMapComponent_eq A B E F (composeMap A B C E f g) h b d n _).trans
    (leftTripleMap_element A B C E F f g h b c e d τ q v hi hn)

lemma rightTripleComponent_element (f : P ⟶ P') (g : Q ⟶ Q') (h : R ⟶ R')
    (b : B) (c : C) (e : E) (d : F) {k r s l n : ℤ}
    (τ : ((BimoduleCategory.underlying A E F R).value e d).X k)
    (q : ((BimoduleCategory.underlying A C E Q).value c e).X r)
    (v : ((BimoduleCategory.underlying A B C P).value b c).X s)
    (hl : k + r = l) (hn : l + s = n) :
    composeMapComponent A B C F f (composeMap A C E F g h) b d n
      (associatorRightElement A B C E F (BimoduleCategory.underlying A B C P)
        (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R)
        b c e d τ q v hl hn) =
    associatorRightElement A B C E F (BimoduleCategory.underlying A B C P')
      (BimoduleCategory.underlying A C E Q') (BimoduleCategory.underlying A E F R') b c e d
      (((BimoduleCategory.valueEvaluation A E F e d).map h).f k τ)
      (((BimoduleCategory.valueEvaluation A C E c e).map g).f r q)
      (((BimoduleCategory.valueEvaluation A B C b c).map f).f s v) hl hn :=
  (composeMapComponent_eq A B C F f (composeMap A C E F g h) b d n _).trans
    (rightTripleMap_element A B C E F f g h b c e d τ q v hl hn)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end TripleMapComponents

/-! ## TripleParameterFirst（旧 SerrePositivity/DifferentialGraded/Tensor/TripleParameterFirst.lean） -/

/-! # P変数の任意パラメータ作用を三重生成元で評価する -/

@[expose] public section TripleParameterFirst
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end TripleParameterFirst

/-! ## TripleParameterRest（旧 SerrePositivity/DifferentialGraded/Tensor/TripleParameterRest.lean） -/

/-! # Q/R変数の任意パラメータ作用を三重生成元で評価する -/

@[expose] public section TripleParameterRest
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end TripleParameterRest

/-! ## LeftDiagonalValues（旧 SerrePositivity/DifferentialGraded/Tensor/LeftDiagonalValues.lean） -/

/-! # 対角bimoduleとの左単位比較 -/

@[expose] public section LeftDiagonalValues
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]

/-- 対角の左制限を既存leftRepresentableへ比較した左単位同型。 -/
def leftUnitValueIso (M : RightModule A B) (b : B) :
    obj A B M ((Bimodule.diagonal A B).leftAt b) ≅ M.obj (op b) :=
  BalancedTensor.changeLeft A B M (Bimodule.diagonal_leftAt A B b) ≪≫
    BalancedTensor.leftYonedaIso A B b M

@[reassoc (attr := simp)]
lemma ι_leftUnitValueIso_hom (M : RightModule A B) (b x : B) :
    BalancedTensor.ι A B M ((Bimodule.diagonal A B).leftAt b) x ≫
      (leftUnitValueIso A B M b).hom = BalancedTensor.rightAction A B M b x := by
  change BalancedTensor.ι A B M ((Bimodule.diagonal A B).leftAt b) x ≫
      (BalancedTensor.changeLeft A B M (Bimodule.diagonal_leftAt A B b)).hom ≫
        BalancedTensor.leftYonedaEvaluation A B b M = _
  rw [BalancedTensor.ι_changeLeft_hom_assoc]
  change 𝟙 _ ≫ BalancedTensor.ι A B M (leftRepresentable A b) x ≫
    BalancedTensor.leftYonedaEvaluation A B b M = _
  rw [Category.id_comp, BalancedTensor.ι_leftYonedaEvaluation]

lemma leftUnitValueIso_hom_element (M : RightModule A B) (b x : B)
    {r s n : ℤ} (m : (M.obj (op x)).X r) (f : GradedHom A b x s) (hn : r + s = n) :
    (leftUnitValueIso A B M b).hom.f n
      (BalancedTensor.element A B M ((Bimodule.diagonal A B).leftAt b) x m f hn) =
    (r * s).negOnePow • moduleAction A M f m hn := by
  have h := BalancedTensor.element_postcompose A B M
    ((Bimodule.diagonal A B).leftAt b) x (leftUnitValueIso A B M b).hom
    (BalancedTensor.rightAction A B M b x)
    (ι_leftUnitValueIso_hom A B M b x) m f hn
  exact h.trans (BalancedTensor.rightAction_apply A B M b x r s n hn m f)

/-- 型を明示した左単位の射。等式輸送を含む同型の展開を避ける入口。 -/
def leftUnitValueHom (M : RightModule A B) (b : B) :
    BalancedTensor.obj A B M ((Bimodule.diagonal A B).leftAt b) ⟶ M.obj (op b) :=
  (leftUnitValueIso A B M b).hom

lemma leftUnitValueHom_element (M : RightModule A B) (b x : B)
    {r s n : ℤ} (m : (M.obj (op x)).X r) (f : GradedHom A b x s) (hn : r + s = n) :
    (leftUnitValueHom A B M b).f n
      (BalancedTensor.element A B M ((Bimodule.diagonal A B).leftAt b) x m f hn) =
    (r * s).negOnePow • moduleAction A M f m hn :=
  leftUnitValueIso_hom_element A B M b x m f hn

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end LeftDiagonalValues

/-! ## LeftDiagonalHom（旧 SerrePositivity/DifferentialGraded/Tensor/LeftDiagonalHom.lean） -/

/-! # 対角左制限とのYoneda評価の加群変数自然性 -/

@[expose] public section LeftDiagonalHom
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]

/-- 左representableの表示を等式で替えても、全Hom自然性は保たれる。 -/
lemma leftYoneda_changeLeft_enriched_naturality (M M' : RightModule A B) (b : B)
    (N : LeftModule A B) (h : N = leftRepresentable A b) :
    rightHomMap A B M M' N ≫ homPostcompose (obj A B M N)
      ((changeLeft A B M' h).hom ≫ leftYonedaEvaluation A B b M') =
    moduleHomπ A B M M' b ≫
      homPrecompose ((changeLeft A B M h).hom ≫ leftYonedaEvaluation A B b M)
        (M'.obj (op b)) := by
  subst N
  simpa only [changeLeft, eqToIso_refl, Iso.refl_hom, Category.id_comp] using
    leftYonedaEvaluation_enriched_naturality A B b M M'

lemma leftUnitValueHom_enriched_naturality (M M' : RightModule A B) (b : B) :
    rightHomMap A B M M' ((Bimodule.diagonal A B).leftAt b) ≫
      homPostcompose (obj A B M ((Bimodule.diagonal A B).leftAt b))
        (leftUnitValueHom A B M' b) =
    moduleHomπ A B M M' b ≫
      homPrecompose (leftUnitValueHom A B M b) (M'.obj (op b)) :=
  leftYoneda_changeLeft_enriched_naturality A B M M' b
    ((Bimodule.diagonal A B).leftAt b) (Bimodule.diagonal_leftAt A B b)

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end LeftDiagonalHom

/-! ## LeftDiagonalUnit（旧 SerrePositivity/DifferentialGraded/Tensor/LeftDiagonalUnit.lean） -/

/-! # 左単位比較の全Hom自然性 -/

@[expose] public section LeftDiagonalUnit
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]

/-- 対角の転置と左tensor作用を、値のHom複体の射として固定する。 -/
def diagonalTensorHomMap (M : RightModule A B) (b b' : B) :
    (op b ⟶[Complex A] op b') ⟶
      homComplex A (obj A B M ((Bimodule.diagonal A B).leftAt b))
        (obj A B M ((Bimodule.diagonal A B).leftAt b')) :=
  (Bimodule.diagonal A B).transposeHom (op b) (op b') ≫
    leftHomMap A B M ((Bimodule.diagonal A B).leftAt b) ((Bimodule.diagonal A B).leftAt b')

lemma diagonalTensorHomMap_element (M : RightModule A B) (b b' x : B)
    {p r s a n : ℤ} (ha : r + s = a) (hn : a + p = n)
    (f : GradedHom A (op b) (op b') p) (m : (M.obj (op x)).X r)
    (h : GradedHom A b x s) :
    ((diagonalTensorHomMap A B M b b').f p f).v a n hn
      (element A B M ((Bimodule.diagonal A B).leftAt b) x m h ha) =
    (p * r).negOnePow • element A B M ((Bimodule.diagonal A B).leftAt b') x m
      (forward A (D := B) (x := b') (y := b) (z := x) (n := p + s) f h (by omega))
      (by omega) := by
  have he := leftHomMap_element_of_sum A B M
    (((Bimodule.diagonal A B).transposeHom (op b) (op b')).f p f) x m h ha rfl hn
  have hd := Bimodule.diagonal_transpose_element A B (b := op b) (b' := op b')
    x f h (show s + p = p + s by omega)
  exact he.trans (congrArg (fun t => (p * r).negOnePow •
    element A B M ((Bimodule.diagonal A B).leftAt b') x m t (by omega)) hd)

/-- 左単位の自然性を純粋斉次生成元で計算する。 -/
lemma leftUnitValue_element_naturality_of_evaluation (M : RightModule A B) (b b' x : B)
    (ε : obj A B M ((Bimodule.diagonal A B).leftAt b) ⟶ M.obj (op b))
    (ε' : obj A B M ((Bimodule.diagonal A B).leftAt b') ⟶ M.obj (op b'))
    (he : ∀ (x : B) (r s a : ℤ) (m : (M.obj (op x)).X r) (h : GradedHom A b x s)
      (ha : r + s = a), ε.f a
        (element A B M ((Bimodule.diagonal A B).leftAt b) x m h ha) =
      (r * s).negOnePow • moduleAction A M h m ha)
    (he' : ∀ (x : B) (r s a : ℤ) (m : (M.obj (op x)).X r) (h : GradedHom A b' x s)
      (ha : r + s = a), ε'.f a
        (element A B M ((Bimodule.diagonal A B).leftAt b') x m h ha) =
      (r * s).negOnePow • moduleAction A M h m ha)
    (p r s a n : ℤ) (ha : r + s = a) (hn : a + p = n)
    (f : GradedHom A (op b) (op b') p) (m : (M.obj (op x)).X r)
    (h : GradedHom A b x s) :
    ε'.f n
      (((diagonalTensorHomMap A B M b b').f p f).v a n hn
        (element A B M ((Bimodule.diagonal A B).leftAt b) x m h ha)) =
    ((M.map (op b) (op b')).f p f).v a n hn
      (ε.f a
        (element A B M ((Bimodule.diagonal A B).leftAt b) x m h ha)) := by
  rw [diagonalTensorHomMap_element]
  simp only [Units.smul_def, map_zsmul]
  rw [he', he]
  simp only [Units.smul_def, map_zsmul]
  change (p * r).negOnePow • ((r * (p + s)).negOnePow •
      moduleAction A M (x := op x) (y := op b')
        (forward A (D := B) (x := b') (y := b) (z := x) (n := p + s) f h (by omega)) m (by omega)) =
    (r * s).negOnePow • moduleAction A M f
      (moduleAction A M h m ha) hn
  exact moduleAction_signed_representable A B M b b' x p r s a n ha hn f h m

/-- 左単位の自然性を純粋斉次生成元で計算する。 -/
lemma leftUnitValue_element_naturality (M : RightModule A B) (b b' x : B)
    (p r s a n : ℤ) (ha : r + s = a) (hn : a + p = n)
    (f : GradedHom A (op b) (op b') p) (m : (M.obj (op x)).X r)
    (h : GradedHom A b x s) :
    (leftUnitValueHom A B M b').f n
      (((diagonalTensorHomMap A B M b b').f p f).v a n hn
        (element A B M ((Bimodule.diagonal A B).leftAt b) x m h ha)) =
    ((M.map (op b) (op b')).f p f).v a n hn
      ((leftUnitValueHom A B M b).f a
        (element A B M ((Bimodule.diagonal A B).leftAt b) x m h ha)) :=
  leftUnitValue_element_naturality_of_evaluation A B M b b' x
    (leftUnitValueHom A B M b) (leftUnitValueHom A B M b')
    (fun x _r _s _a m h ha => leftUnitValueHom_element A B M b x m h ha)
    (fun x _r _s _a m h ha => leftUnitValueHom_element A B M b' x m h ha)
    p r s a n ha hn f m h

/-- 左単位の比較は残る右Bの全Homに関して自然。 -/
lemma leftUnitValue_naturality (M : RightModule A B) (b b' : B) :
    diagonalTensorHomMap A B M b b' ≫
      homPostcompose (BalancedTensor.obj A B M ((Bimodule.diagonal A B).leftAt b))
        (Q := BalancedTensor.obj A B M ((Bimodule.diagonal A B).leftAt b'))
        (T := M.obj (op b')) (leftUnitValueHom A B M b') =
    M.map (op b) (op b') ≫
      homPrecompose
        (P := BalancedTensor.obj A B M ((Bimodule.diagonal A B).leftAt b))
        (Q := M.obj (op b)) (leftUnitValueHom A B M b)
        (M.obj (op b')) := by
  exact homMap_post_pre_eq A B M ((Bimodule.diagonal A B).leftAt b)
    (diagonalTensorHomMap A B M b b')
    (M.map (op b) (op b')) (leftUnitValueHom A B M b') (leftUnitValueHom A B M b)
    (fun p f x r s a n ha hn m h =>
      leftUnitValue_element_naturality A B M b b' x p r s a n ha hn f m h)

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end LeftDiagonalUnit

/-! ## LeftUnit（旧 SerrePositivity/DifferentialGraded/Tensor/LeftUnit.lean） -/

/-! # 対角bimoduleとの左単位比較 -/

@[expose] public section LeftUnit
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 対角の左制限を既存leftRepresentableへ比較した左単位同型。 -/
def leftUnitValueIso (P : Bimodule A B C) (b : B) (c : C) :
    (compose A B B C (Bimodule.diagonal A B) P).value b c ≅ P.value b c :=
  BalancedTensor.leftUnitValueIso A B (P.rightAt c) b

@[reassoc (attr := simp)]
lemma ι_leftUnitValueIso_hom (P : Bimodule A B C) (b x : B) (c : C) :
    BalancedTensor.ι A B (P.rightAt c) ((Bimodule.diagonal A B).leftAt b) x ≫
      (leftUnitValueIso A B C P b c).hom = BalancedTensor.rightAction A B (P.rightAt c) b x :=
  BalancedTensor.ι_leftUnitValueIso_hom A B (P.rightAt c) b x

lemma leftUnitValueIso_hom_element (P : Bimodule A B C) (b x : B) (c : C)
    {r s n : ℤ} (m : (P.value x c).X r) (f : GradedHom A b x s) (hn : r + s = n) :
    (leftUnitValueIso A B C P b c).hom.f n
      (BalancedTensor.element A B (P.rightAt c) ((Bimodule.diagonal A B).leftAt b) x m f hn) =
    (r * s).negOnePow • moduleAction A (P.rightAt c) f m hn :=
  BalancedTensor.leftUnitValueIso_hom_element A B (P.rightAt c) b x m f hn

/-- 型を明示した左単位の射。等式輸送を含む同型の展開を避ける入口。 -/
def leftUnitValueHom (P : Bimodule A B C) (b : B) (c : C) :
    BalancedTensor.obj A B (P.rightAt c) ((Bimodule.diagonal A B).leftAt b) ⟶ P.value b c :=
  (leftUnitValueIso A B C P b c).hom

lemma leftUnitValueHom_element (P : Bimodule A B C) (b x : B) (c : C)
    {r s n : ℤ} (m : (P.value x c).X r) (f : GradedHom A b x s) (hn : r + s = n) :
    (leftUnitValueHom A B C P b c).f n
      (BalancedTensor.element A B (P.rightAt c) ((Bimodule.diagonal A B).leftAt b) x m f hn) =
    (r * s).negOnePow • moduleAction A (P.rightAt c) f m hn :=
  leftUnitValueIso_hom_element A B C P b x c m f hn

/-- 左単位の比較は残る右Bの全Homに関して自然。 -/
lemma leftUnitValue_naturality (P : Bimodule A B C) (b b' : B) (c : C) :
    ((compose A B B C (Bimodule.diagonal A B) P).rightAt c).map (op b) (op b') ≫
      homPostcompose (BalancedTensor.obj A B (P.rightAt c) ((Bimodule.diagonal A B).leftAt b))
        (Q := BalancedTensor.obj A B (P.rightAt c) ((Bimodule.diagonal A B).leftAt b'))
        (T := (P.rightAt c).obj (op b')) (leftUnitValueHom A B C P b' c) =
    (P.rightAt c).map (op b) (op b') ≫
      homPrecompose
        (P := BalancedTensor.obj A B (P.rightAt c) ((Bimodule.diagonal A B).leftAt b))
        (Q := (P.rightAt c).obj (op b)) (leftUnitValueHom A B C P b c)
        ((P.rightAt c).obj (op b')) := by
  change ((Bimodule.diagonal A B).transposeHom (op b) (op b') ≫
      BalancedTensor.leftHomMap A B (P.rightAt c) ((Bimodule.diagonal A B).leftAt b)
        ((Bimodule.diagonal A B).leftAt b')) ≫
      homPostcompose _ (BalancedTensor.leftUnitValueHom A B (P.rightAt c) b') =
    (P.rightAt c).map (op b) (op b') ≫
      homPrecompose (BalancedTensor.leftUnitValueHom A B (P.rightAt c) b) _
  exact BalancedTensor.leftUnitValue_naturality A B (P.rightAt c) b b'

/-- 値ごとの左単位を実際の右B加群同型へ束ねる。 -/
def leftUnitIso (P : Bimodule A B C) (c : C) :
    ForgetEnrichment.of (Complex A) ((compose A B B C (Bimodule.diagonal A B) P).rightAt c) ≅
      ForgetEnrichment.of (Complex A) (P.rightAt c) :=
  moduleIsoMk A B (fun b => leftUnitValueIso A B C P b.unop c)
    (fun b b' => by
      change ((compose A B B C (Bimodule.diagonal A B) P).rightAt c).map b b' ≫
          homPostcompose
            (BalancedTensor.obj A B (P.rightAt c) ((Bimodule.diagonal A B).leftAt b.unop))
            (leftUnitValueIso A B C P b'.unop c).hom =
        (P.rightAt c).map b b' ≫
          homPrecompose (leftUnitValueIso A B C P b.unop c).hom ((P.rightAt c).obj b')
      have h := leftUnitValue_naturality A B C P b.unop b'.unop c
      simpa only [Opposite.op_unop, leftUnitValueHom] using h)

@[simp]
lemma leftUnitIso_hom_eval (P : Bimodule A B C) (b : B) (c : C) :
    (moduleEvaluation A B b).map
      (X := ForgetEnrichment.of (Complex A)
        ((compose A B B C (Bimodule.diagonal A B) P).rightAt c))
      (Y := ForgetEnrichment.of (Complex A) (P.rightAt c)) (leftUnitIso A B C P c).hom =
      (leftUnitValueIso A B C P b c).hom :=
  moduleIsoMk_hom_eval A B _ _ b

@[simp]
lemma leftUnitIso_inv_eval (P : Bimodule A B C) (b : B) (c : C) :
    (moduleEvaluation A B b).map
      (X := ForgetEnrichment.of (Complex A) (P.rightAt c))
      (Y := ForgetEnrichment.of (Complex A)
        ((compose A B B C (Bimodule.diagonal A B) P).rightAt c)) (leftUnitIso A B C P c).inv =
      (leftUnitValueIso A B C P b c).inv :=
  moduleIsoMk_inv_eval A B _ _ b

@[simp]
lemma leftUnitIso_hom_component (P : Bimodule A B C) (b : B) (c : C) :
    moduleMorphismComponent A B
      ((compose A B B C (Bimodule.diagonal A B) P).rightAt c) (P.rightAt c)
      (leftUnitIso A B C P c).hom b = (leftUnitValueIso A B C P b c).hom :=
  moduleIsoMk_hom_eval A B _ _ b

/-- 左単位は左Cの全Homにも自然。Cの対象のsmallnessは不要。 -/
lemma leftUnitValue_left_naturality (P : Bimodule A B C) (b : B) (c c' : C) :
    (compose A B B C (Bimodule.diagonal A B) P).toFunctor.map c c' ≫
      moduleHomπ A B (rightAt A B B C (Bimodule.diagonal A B) P c)
        (rightAt A B B C (Bimodule.diagonal A B) P c') b ≫
      homPostcompose ((compose A B B C (Bimodule.diagonal A B) P).value b c)
        (leftUnitValueIso A B C P b c').hom =
    P.toFunctor.map c c' ≫ moduleHomπ A B (P.rightAt c) (P.rightAt c') b ≫
      homPrecompose (leftUnitValueIso A B C P b c).hom (P.value b c') := by
  change ((compose A B B C (Bimodule.diagonal A B) P).toFunctor.map c c' ≫
      moduleHomπ A B (rightAt A B B C (Bimodule.diagonal A B) P c)
        (rightAt A B B C (Bimodule.diagonal A B) P c') b) ≫
      homPostcompose (BalancedTensor.obj A B (P.rightAt c) ((Bimodule.diagonal A B).leftAt b))
        (BalancedTensor.leftUnitValueHom A B (P.rightAt c') b) =
    (P.toFunctor.map c c' ≫ moduleHomπ A B (P.rightAt c) (P.rightAt c') b) ≫
      homPrecompose (BalancedTensor.leftUnitValueHom A B (P.rightAt c) b) (P.value b c')
  rw [compose_leftMap_π]
  rw [Category.assoc, BalancedTensor.leftUnitValueHom_enriched_naturality, ← Category.assoc]

/-- 値ごとの自然性を右B加群の主Hom endへ束ねる。 -/
lemma leftUnitIso_naturality (P : Bimodule A B C) (c c' : C) :
    (compose A B B C (Bimodule.diagonal A B) P).toFunctor.map c c' ≫
      moduleHomPostcompose A B
        ((compose A B B C (Bimodule.diagonal A B) P).rightAt c)
        ((compose A B B C (Bimodule.diagonal A B) P).rightAt c') (P.rightAt c')
        (leftUnitIso A B C P c').hom =
    P.toFunctor.map c c' ≫ moduleHomPrecompose A B
      ((compose A B B C (Bimodule.diagonal A B) P).rightAt c) (P.rightAt c) (P.rightAt c')
      (leftUnitIso A B C P c).hom := by
  apply moduleHom_ext
  intro b
  simp only [Category.assoc]
  rw [moduleHomPostcompose_π, moduleHomPrecompose_π]
  simp only [leftUnitIso_hom_component]
  exact leftUnitValue_left_naturality A B C P b c c'

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end LeftUnit

/-! ## UnitBimoduleIso（旧 SerrePositivity/DifferentialGraded/Tensor/UnitBimoduleIso.lean） -/

/-! # 対角bimoduleの単位比較を全Hom自然な閉零同型として読む -/

@[expose] public section UnitBimoduleIso
universe u v w

noncomputable section
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 対角Bとの合成の閉零bimodule圏での左単位同型。 -/
def leftBimoduleUnitIso (P : Bimodule A B C) :
    BimoduleCategory.of A B C (compose A B B C (Bimodule.diagonal A B) P) ≅
      BimoduleCategory.of A B C P :=
  BimoduleCategory.isoOfFamily A B C (leftUnitIso A B C P) (leftUnitIso_naturality A B C P)

@[simp]
lemma leftBimoduleUnitIso_hom_value (P : Bimodule A B C) (b : B) (c : C) :
    (BimoduleCategory.valueEvaluation A B C b c).map (leftBimoduleUnitIso A B C P).hom =
      (leftUnitValueIso A B C P b c).hom := leftUnitIso_hom_eval A B C P b c

@[simp]
lemma leftBimoduleUnitIso_inv_value (P : Bimodule A B C) (b : B) (c : C) :
    (BimoduleCategory.valueEvaluation A B C b c).map (leftBimoduleUnitIso A B C P).inv =
      (leftUnitValueIso A B C P b c).inv := leftUnitIso_inv_eval A B C P b c

variable [Small.{u} C]

/-- 対角Cとの合成の閉零bimodule圏での右単位同型。 -/
def rightBimoduleUnitIso (P : Bimodule A B C) :
    BimoduleCategory.of A B C (compose A B C C P (Bimodule.diagonal A C)) ≅
      BimoduleCategory.of A B C P :=
  BimoduleCategory.isoOfFamily A B C (rightUnitIso A B C P) (rightUnitIso_naturality A B C P)

@[simp]
lemma rightBimoduleUnitIso_hom_value (P : Bimodule A B C) (b : B) (c : C) :
    (BimoduleCategory.valueEvaluation A B C b c).map (rightBimoduleUnitIso A B C P).hom =
      (rightUnitValueIso A B C P b c).hom := rightUnitIso_hom_eval A B C P b c

@[simp]
lemma rightBimoduleUnitIso_inv_value (P : Bimodule A B C) (b : B) (c : C) :
    (BimoduleCategory.valueEvaluation A B C b c).map (rightBimoduleUnitIso A B C P).inv =
      (rightUnitValueIso A B C P b c).inv := rightUnitIso_inv_eval A B C P b c

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end UnitBimoduleIso

/-! ## UnitMapNaturality（旧 SerrePositivity/DifferentialGraded/Tensor/UnitMapNaturality.lean） -/

/-! # 単位比較の閉零bimodule変数に関する自然性 -/

@[expose] public section UnitMapNaturality
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite

namespace BalancedTensor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]

/-- 対角の左制限による単位評価の右加群変数に関する自然性。 -/
lemma leftUnitValueHom_map_naturality {M M' : ModuleCategory A B} (f : M ⟶ M') (b : B) :
    map A B f (𝟙 (ForgetEnrichment.of (Complex A) ((Bimodule.diagonal A B).leftAt b))) ≫
      leftUnitValueHom A B (ForgetEnrichment.to (Complex A) M') b =
    leftUnitValueHom A B (ForgetEnrichment.to (Complex A) M) b ≫
      (moduleEvaluation A B b).map f := by
  apply hom_ext
  intro x
  simp only [ι_map_assoc, CategoryTheory.Functor.map_id]
  change ((moduleEvaluation A B x).map f ⊗ₘ 𝟙 _) ≫
      ι A B (ForgetEnrichment.to (Complex A) M') ((Bimodule.diagonal A B).leftAt b) x ≫
        leftUnitValueHom A B (ForgetEnrichment.to (Complex A) M') b =
    ι A B (ForgetEnrichment.to (Complex A) M) ((Bimodule.diagonal A B).leftAt b) x ≫
      leftUnitValueHom A B (ForgetEnrichment.to (Complex A) M) b ≫
        (moduleEvaluation A B b).map f
  rw [leftUnitValueHom, leftUnitValueHom, ι_leftUnitValueIso_hom,
    ι_leftUnitValueIso_hom_assoc]
  exact (rightAction_morphism A B f b x).symm

end BalancedTensor

namespace BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]
variable {P P' : BimoduleCategory A B C}
local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "P₁" => BimoduleCategory.underlying A B C P'

lemma leftUnitValue_map_naturality (f : P ⟶ P') (b : B) (c : C) :
    composeValueMap A B B C (𝟙 (BimoduleCategory.of A B B (Bimodule.diagonal A B)))
      f b c ≫ (leftUnitValueIso A B C P₁ b c).hom =
    (leftUnitValueIso A B C P₀ b c).hom ≫
      (BimoduleCategory.valueEvaluation A B C b c).map f := by
  unfold composeValueMap
  rw [CategoryTheory.Functor.map_id]
  exact BalancedTensor.leftUnitValueHom_map_naturality A B
    ((BimoduleCategory.evaluation A B C c).map f) b

/-- 左単位同型の閉零bimodule射に関する自然性。Cのsmall性は不要。 -/
lemma leftBimoduleUnitIso_naturality (f : P ⟶ P') :
    composeMap A B B C (𝟙 (BimoduleCategory.of A B B (Bimodule.diagonal A B))) f ≫
      (leftBimoduleUnitIso A B C P₁).hom =
    (leftBimoduleUnitIso A B C P₀).hom ≫ f := by
  apply BimoduleCategory.value_hom_ext A B C
  intro b c
  simp only [CategoryTheory.Functor.map_comp, composeMap_value_eval,
    leftBimoduleUnitIso_hom_value]
  exact leftUnitValue_map_naturality A B C f b c

variable [Small.{u} C]

lemma rightUnitValue_map_naturality (f : P ⟶ P') (b : B) (c : C) :
    composeValueMap A B C C f
      (𝟙 (BimoduleCategory.of A C C (Bimodule.diagonal A C))) b c ≫
      (rightUnitValueIso A B C P₁ b c).hom =
    (rightUnitValueIso A B C P₀ b c).hom ≫
      (BimoduleCategory.valueEvaluation A B C b c).map f := by
  unfold composeValueMap
  rw [CategoryTheory.Functor.map_id]
  have h := BalancedTensor.yonedaEvaluation_naturality A C c
    ((BimoduleCategory.leftEvaluation A B C b).map f)
  exact h.trans (congrArg (fun k =>
    (rightUnitValueIso A B C P₀ b c).hom ≫ k)
    (BimoduleCategory.leftEvaluation_map_eval A B C f b c))

/-- 右単位同型の閉零bimodule射に関する自然性。 -/
lemma rightBimoduleUnitIso_naturality (f : P ⟶ P') :
    composeMap A B C C f (𝟙 (BimoduleCategory.of A C C (Bimodule.diagonal A C))) ≫
      (rightBimoduleUnitIso A B C P₁).hom =
    (rightBimoduleUnitIso A B C P₀).hom ≫ f := by
  apply BimoduleCategory.value_hom_ext A B C
  intro b c
  simp only [CategoryTheory.Functor.map_comp, composeMap_value_eval,
    rightBimoduleUnitIso_hom_value]
  exact rightUnitValue_map_naturality A B C f b c

end BimoduleTensor
end SerrePositivity.DifferentialGraded
end

end UnitMapNaturality

/-! ## UnitFunctors（旧 SerrePositivity/DifferentialGraded/Tensor/UnitFunctors.lean） -/

/-! # 閉零bimodule圏における単位合成関手と単位自然同型 -/

@[expose] public section UnitFunctors
universe u v w

noncomputable section
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 対角Bを前に合成する関手。 -/
def leftUnitFunctor : BimoduleCategory A B C ⥤ BimoduleCategory A B C :=
  (((Functor.const (BimoduleCategory A B C)).obj
      (BimoduleCategory.of A B B (Bimodule.diagonal A B))).prod'
    (𝟭 (BimoduleCategory A B C))) ⋙ composeFunctor A B B C

/-- 全Hom自然な閉零bimodule圏における左単位自然同型。 -/
def leftUnitNatIso : leftUnitFunctor A B C ≅ 𝟭 (BimoduleCategory A B C) :=
  NatIso.ofComponents
    (fun P => leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P))
    (fun f => leftBimoduleUnitIso_naturality A B C f)

@[simp]
lemma leftUnitNatIso_app (P : BimoduleCategory A B C) :
    (leftUnitNatIso A B C).app P =
      leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P) := rfl

variable [Small.{u} C]

/-- 対角Cを後に合成する関手。 -/
def rightUnitFunctor : BimoduleCategory A B C ⥤ BimoduleCategory A B C :=
  ((𝟭 (BimoduleCategory A B C)).prod'
    ((Functor.const (BimoduleCategory A B C)).obj
      (BimoduleCategory.of A C C (Bimodule.diagonal A C)))) ⋙ composeFunctor A B C C

/-- 全Hom自然な閉零bimodule圏における右単位自然同型。 -/
def rightUnitNatIso : rightUnitFunctor A B C ≅ 𝟭 (BimoduleCategory A B C) :=
  NatIso.ofComponents
    (fun P => rightBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P))
    (fun f => rightBimoduleUnitIso_naturality A B C f)

@[simp]
lemma rightUnitNatIso_app (P : BimoduleCategory A B C) :
    (rightUnitNatIso A B C).app P =
      rightBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P) := rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end UnitFunctors
