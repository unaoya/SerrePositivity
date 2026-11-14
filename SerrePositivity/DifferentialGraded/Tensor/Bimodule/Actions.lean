module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.DifferentialGraded.Bimodule.Basic
public import SerrePositivity.DifferentialGraded.Tensor.Enriched
public import SerrePositivity.DifferentialGraded.Tensor.BalancedElements
public import SerrePositivity.DifferentialGraded.Bimodule.Value
public import SerrePositivity.DifferentialGraded.Tensor.Parameter
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying

public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtension.CategoriesAndModules
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations

/-!
# Tensor.Bimodule.Actions

## 概要
bimodule tensor の両作用・射・パラメータと中間圏比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## BimoduleActions（旧 SerrePositivity/DifferentialGraded/Tensor/BimoduleActions.lean） -/

/-! # 相対tensorに残るbimoduleの二作用 -/

@[expose] public section BimoduleActions
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

/-- 値Q(c,e)⊗_C P(b,c)に残る右B作用。 -/
def rightAt (P : Bimodule A B C) (Q : Bimodule A C E) (e : E) : RightModule A B :=
  P.transposeDG.comp (BalancedTensor.leftTensorDG A C (Q.rightAt e))

/-- 同じ値に残る左E作用。 -/
def leftAt (P : Bimodule A B C) (Q : Bimodule A C E) (b : B) : LeftModule A E :=
  Q.toFunctor.comp (BalancedTensor.rightTensorDG A C (P.leftAt b))

/-- 残る二作用の交換は相対tensorの主Hom交換則から従う。 -/
lemma interchange (P : Bimodule A B C) (Q : Bimodule A C E)
    {b b' : Bᵒᵖ} {e e' : E} {p q : ℤ}
    (f : GradedHom A b b' p) (g : GradedHom A e e' q) :
    (((rightAt A B C E P Q e).map b b').f p f).comp
      (((leftAt A B C E P Q b'.unop).map e e').f q g)
        (by omega : p + q = q + p) =
    (q * p).negOnePow • ((((leftAt A B C E P Q b.unop).map e e').f q g).comp
      (((rightAt A B C E P Q e').map b b').f p f) rfl) := by
  have h := congrArg (fun t => (q * p).negOnePow • t)
    (BalancedTensor.homMaps_interchange A C
      ((Q.toFunctor.map e e').f q g) ((P.transposeHom b b').f p f) rfl)
  rw [smul_smul, Int.units_mul_self, one_smul] at h
  exact h.symm

/-- 左EのHomをパラメータにした全次数自然な右B加群変換。 -/
def paramTrans (P : Bimodule A B C) (Q : Bimodule A C E) (e e' : E) :
    ModuleParamTrans A B (e ⟶[Complex A] e')
      (rightAt A B C E P Q e) (rightAt A B C E P Q e') where
  app b := (leftAt A B C E P Q b.unop).map e e'
  naturality x y := by
    apply moduleParamNaturality_of_apply A
    intro x y q p r n hn g f m
    have h := Cochain.congr_v (interchange A B C E P Q f g) r n (by omega)
    rw [Cochain.comp_v _ _ _ r (r + p) n rfl (by omega), Cochain.units_smul_v,
      Cochain.comp_v _ _ _ r (r + q) n rfl (by omega)] at h
    exact congrArg (fun t => t m) h

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleActions

/-! ## Bimodule（旧 SerrePositivity/DifferentialGraded/Tensor/Bimodule.lean） -/

/-! # 多対象dg bimoduleの相対tensor合成 -/

@[expose] public section Bimodule
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

lemma paramTrans_unit (P : Bimodule A B C) (Q : Bimodule A C E) (e : E) (b : Bᵒᵖ) :
    eId (Complex A) e ≫ (paramTrans A B C E P Q e e).app b =
      identity ((rightAt A B C E P Q e).obj b) := by
  change eId (Complex A) e ≫ (leftAt A B C E P Q b.unop).map e e =
    identity (BalancedTensor.obj A C (Q.rightAt e) (P.leftAt b.unop))
  exact (leftAt A B C E P Q b.unop).map_id e

lemma paramTrans_comp (P : Bimodule A B C) (Q : Bimodule A C E)
    (e e' e'' : E) (b : Bᵒᵖ) :
    eComp (Complex A) e e' e'' ≫ (paramTrans A B C E P Q e e'').app b =
      ((paramTrans A B C E P Q e e').app b ⊗ₘ (paramTrans A B C E P Q e' e'').app b) ≫
        enrichedComposition _ _ _ :=
  (leftAt A B C E P Q b.unop).map_comp e e' e''

/-- Q(c,e)⊗_C P(b,c)を値とする、実際の右B・左E dg bimodule。 -/
def compose (P : Bimodule A B C) (Q : Bimodule A C E) : Bimodule A B E :=
  Bimodule.ofParamTrans A B E (rightAt A B C E P Q) (paramTrans A B C E P Q)
    (paramTrans_unit A B C E P Q) (paramTrans_comp A B C E P Q)

lemma compose_value (P : Bimodule A B C) (Q : Bimodule A C E) (b : B) (e : E) :
    (compose A B C E P Q).value b e =
      BalancedTensor.obj A C (Q.rightAt e) (P.leftAt b) := rfl

lemma compose_rightMap (P : Bimodule A B C) (Q : Bimodule A C E)
    (e : E) (b b' : Bᵒᵖ) :
    ((compose A B C E P Q).rightAt e).map b b' =
      P.transposeHom b b' ≫ BalancedTensor.leftHomMap A C (Q.rightAt e)
        (P.leftAt b.unop) (P.leftAt b'.unop) := rfl

@[reassoc]
lemma compose_leftMap_π (P : Bimodule A B C) (Q : Bimodule A C E)
    (e e' : E) (b : B) :
    (compose A B C E P Q).toFunctor.map e e' ≫
      moduleHomπ A B (rightAt A B C E P Q e) (rightAt A B C E P Q e') b =
    Q.toFunctor.map e e' ≫
      BalancedTensor.rightHomMap A C (Q.rightAt e) (Q.rightAt e') (P.leftAt b) :=
  Bimodule.ofParamTrans_map_π A B E (rightAt A B C E P Q) (paramTrans A B C E P Q)
    (paramTrans_unit A B C E P Q) (paramTrans_comp A B C E P Q) e e' b

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end Bimodule

/-! ## BimoduleElements（旧 SerrePositivity/DifferentialGraded/Tensor/BimoduleElements.lean） -/

/-! # bimodule合成の左作用の斉次生成元公式 -/

@[expose] public section BimoduleElements
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

/-- 合成の左作用は先頭のtensor因子へ作用し、余分な符号を生じない。 -/
lemma compose_leftAction_element (P : Bimodule A B C) (Q : Bimodule A C E)
    (b : B) (c : C) (e e' : E) {p k r i j n : ℤ}
    (ha : k + r = i) (hj : k + p = j) (hn : i + p = n)
    (g : GradedHom A e e' p) (q : (Q.value c e).X k) (v : (P.value b c).X r) :
    SerrePositivity.DifferentialGraded.leftAction A ((compose A B C E P Q).leftAt b) g
      (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v ha) hn =
    BalancedTensor.element A C (Q.rightAt e') (P.leftAt b) c
      (SerrePositivity.DifferentialGraded.leftAction A (Q.leftAt c) g q hj) v (by omega) := by
  have h := compose_leftMap_π A B C E P Q e e' b
  change ((compose A B C E P Q).leftAt b).map e e' =
    Q.toFunctor.map e e' ≫
      BalancedTensor.rightHomMap A C (Q.rightAt e) (Q.rightAt e') (P.leftAt b) at h
  have hc := congrArg (fun z => z.f p g) h
  have he := BalancedTensor.rightHomMap_element_of_sum A C (P.leftAt b) (l := j)
    ((Q.toFunctor.map e e').f p g) c q v ha (by omega) hn
  exact (congrArg (fun z => z.v i n hn
    (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v ha)) hc).trans he

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleElements

/-! ## BimoduleValueMaps（旧 SerrePositivity/DifferentialGraded/Tensor/BimoduleValueMaps.lean） -/

/-! # bimodule射の相対tensorへの作用を各値で構成する -/

@[expose] public section BimoduleValueMaps
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

/-- bimodule射を左右から作用させた、相対tensorの各値のchain map。 -/
def composeValueMap {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    (f : P ⟶ P') (g : Q ⟶ Q') (b : B) (e : E) :
    (compose A B C E (BimoduleCategory.underlying A B C P)
      (BimoduleCategory.underlying A C E Q)).value b e ⟶
    (compose A B C E (BimoduleCategory.underlying A B C P')
      (BimoduleCategory.underlying A C E Q')).value b e :=
  BalancedTensor.map A C
    (M := (BimoduleCategory.evaluation A C E e).obj Q)
    (M' := (BimoduleCategory.evaluation A C E e).obj Q')
    (N := (BimoduleCategory.leftEvaluation A B C b).obj P)
    (N' := (BimoduleCategory.leftEvaluation A B C b).obj P')
    ((BimoduleCategory.evaluation A C E e).map g)
    ((BimoduleCategory.leftEvaluation A B C b).map f)

@[reassoc (attr := simp)]
lemma ι_composeValueMap {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    (f : P ⟶ P') (g : Q ⟶ Q') (b : B) (c : C) (e : E) :
    BalancedTensor.ι A C ((BimoduleCategory.underlying A C E Q).rightAt e)
      ((BimoduleCategory.underlying A B C P).leftAt b) c ≫ composeValueMap A B C E f g b e =
    ((BimoduleCategory.valueEvaluation A C E c e).map g ⊗ₘ
      (BimoduleCategory.valueEvaluation A B C b c).map f) ≫
    BalancedTensor.ι A C ((BimoduleCategory.underlying A C E Q').rightAt e)
      ((BimoduleCategory.underlying A B C P').leftAt b) c := by
  have hh := BalancedTensor.ι_map A C
    (M := (BimoduleCategory.evaluation A C E e).obj Q)
    (M' := (BimoduleCategory.evaluation A C E e).obj Q')
    (N := (BimoduleCategory.leftEvaluation A B C b).obj P)
    (N' := (BimoduleCategory.leftEvaluation A B C b).obj P')
    ((BimoduleCategory.evaluation A C E e).map g)
    ((BimoduleCategory.leftEvaluation A B C b).map f) c
  have he := BimoduleCategory.leftEvaluation_map_eval A B C f b c
  exact hh.trans (congrArg (fun k : (BimoduleCategory.underlying A B C P).value b c ⟶
      (BimoduleCategory.underlying A B C P').value b c =>
    ((BimoduleCategory.valueEvaluation A C E c e).map g ⊗ₘ k) ≫
      BalancedTensor.ι A C ((BimoduleCategory.underlying A C E Q').rightAt e)
        ((BimoduleCategory.underlying A B C P').leftAt b) c) he)

lemma composeValueMap_id (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E)
    (b : B) (e : E) :
    composeValueMap A B C E (𝟙 P) (𝟙 Q) b e = 𝟙 _ := by
  unfold composeValueMap
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  exact BalancedTensor.map_id A C _ _

lemma composeValueMap_comp {P P' P'' : BimoduleCategory A B C}
    {Q Q' Q'' : BimoduleCategory A C E} (f : P ⟶ P') (f' : P' ⟶ P'')
    (g : Q ⟶ Q') (g' : Q' ⟶ Q'') (b : B) (e : E) :
    composeValueMap A B C E (f ≫ f') (g ≫ g') b e =
      composeValueMap A B C E f g b e ≫ composeValueMap A B C E f' g' b e := by
  unfold composeValueMap
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  exact BalancedTensor.map_comp A C _ _ _ _

/-- 固定した両端の値における、実際の閉零bimodule圏上のtensor双関手。 -/
def valueFunctor (b : B) (e : E) :
    BimoduleCategory A B C × BimoduleCategory A C E ⥤ Complex A where
  obj PQ := (compose A B C E (BimoduleCategory.underlying A B C PQ.1)
    (BimoduleCategory.underlying A C E PQ.2)).value b e
  map fg := composeValueMap A B C E fg.1 fg.2 b e
  map_id PQ := composeValueMap_id A B C E PQ.1 PQ.2 b e
  map_comp fg gh := composeValueMap_comp A B C E fg.1 gh.1 fg.2 gh.2 b e

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleValueMaps

/-! ## BimoduleValueElements（旧 SerrePositivity/DifferentialGraded/Tensor/BimoduleValueElements.lean） -/

/-! # bimodule射による相対tensorの斉次生成元の評価 -/

@[expose] public section BimoduleValueElements
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

/-- 閉零bimodule射の作用には純tensor上で追加のKoszul符号が生じない。 -/
lemma composeValueMap_element {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    (f : P ⟶ P') (g : Q ⟶ Q') (b : B) (c : C) (e : E) {r s n : ℤ}
    (m : ((BimoduleCategory.underlying A C E Q).value c e).X r)
    (t : ((BimoduleCategory.underlying A B C P).value b c).X s) (hn : r + s = n) :
    (composeValueMap A B C E f g b e).f n
      (BalancedTensor.element A C ((BimoduleCategory.underlying A C E Q).rightAt e)
        ((BimoduleCategory.underlying A B C P).leftAt b) c m t hn) =
    BalancedTensor.element A C ((BimoduleCategory.underlying A C E Q').rightAt e)
      ((BimoduleCategory.underlying A B C P').leftAt b) c
      (((BimoduleCategory.valueEvaluation A C E c e).map g).f r m)
      (((BimoduleCategory.valueEvaluation A B C b c).map f).f s t) hn := by
  have h := BalancedTensor.map_element A C
    (M := (BimoduleCategory.evaluation A C E e).obj Q)
    (M' := (BimoduleCategory.evaluation A C E e).obj Q')
    (N := (BimoduleCategory.leftEvaluation A B C b).obj P)
    (N' := (BimoduleCategory.leftEvaluation A B C b).obj P')
    ((BimoduleCategory.evaluation A C E e).map g)
    ((BimoduleCategory.leftEvaluation A B C b).map f) c m t hn
  have he := congrArg (fun k : (BimoduleCategory.underlying A B C P).value b c ⟶
      (BimoduleCategory.underlying A B C P').value b c => k.f s t)
    (BimoduleCategory.leftEvaluation_map_eval A B C f b c)
  exact h.trans (congrArg (fun v : ((BimoduleCategory.underlying A B C P').value b c).X s =>
    BalancedTensor.element A C ((BimoduleCategory.underlying A C E Q').rightAt e)
      ((BimoduleCategory.underlying A B C P').leftAt b) c
      (((BimoduleCategory.valueEvaluation A C E c e).map g).f r m) v hn) he)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleValueElements

/-! ## BimoduleMapComponent（旧 SerrePositivity/DifferentialGraded/Tensor/BimoduleMapComponent.lean） -/

/-! # 相対tensorの値のmapを固定した成分関数で表示する -/

@[expose] public section BimoduleMapComponent
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

/-- 外側の作用との比較で値のchain mapの構成を展開しないための成分表示。 -/
@[irreducible]
def composeMapComponent {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    (f : P ⟶ P') (g : Q ⟶ Q') (b : B) (e : E) (n : ℤ) :
    ((compose A B C E (BimoduleCategory.underlying A B C P)
      (BimoduleCategory.underlying A C E Q)).value b e).X n →
    ((compose A B C E (BimoduleCategory.underlying A B C P')
      (BimoduleCategory.underlying A C E Q')).value b e).X n :=
  fun x => (composeValueMap A B C E f g b e).f n x

lemma composeMapComponent_eq {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    (f : P ⟶ P') (g : Q ⟶ Q') (b : B) (e : E) (n : ℤ) (x) :
    composeMapComponent A B C E f g b e n x = (composeValueMap A B C E f g b e).f n x := by
  unfold composeMapComponent
  rfl

lemma composeMapComponent_element {P P' : BimoduleCategory A B C}
    {Q Q' : BimoduleCategory A C E} (f : P ⟶ P') (g : Q ⟶ Q') (b : B) (c : C) (e : E)
    {r s n : ℤ} (m : ((BimoduleCategory.underlying A C E Q).value c e).X r)
    (t : ((BimoduleCategory.underlying A B C P).value b c).X s) (hn : r + s = n) :
    composeMapComponent A B C E f g b e n
      (BalancedTensor.element A C ((BimoduleCategory.underlying A C E Q).rightAt e)
        ((BimoduleCategory.underlying A B C P).leftAt b) c m t hn) =
    BalancedTensor.element A C ((BimoduleCategory.underlying A C E Q').rightAt e)
      ((BimoduleCategory.underlying A B C P').leftAt b) c
      (((BimoduleCategory.valueEvaluation A C E c e).map g).f r m)
      (((BimoduleCategory.valueEvaluation A B C b c).map f).f s t) hn :=
  (composeMapComponent_eq A B C E f g b e n _).trans
    (composeValueMap_element A B C E f g b c e m t hn)

lemma composeMapComponent_units_smul {P P' : BimoduleCategory A B C}
    {Q Q' : BimoduleCategory A C E} (f : P ⟶ P') (g : Q ⟶ Q') (b : B) (e : E)
    (n : ℤ) (u : ℤˣ) (x) :
    composeMapComponent A B C E f g b e n (u • x) =
      u • composeMapComponent A B C E f g b e n x :=
  (composeMapComponent_eq A B C E f g b e n (u • x)).trans
    ((chain_units_smul (composeValueMap A B C E f g b e) n u x).trans
      (congrArg (fun z => u • z) (composeMapComponent_eq A B C E f g b e n x).symm))

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMapComponent

/-! ## BimoduleMapLeftAction（旧 SerrePositivity/DifferentialGraded/Tensor/BimoduleMapLeftAction.lean） -/

/-! # 相対tensorの値のmapと外側の左作用の可換式 -/

@[expose] public section BimoduleMapLeftAction
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

lemma composeMapComponent_leftAction_element {P P' : BimoduleCategory A B C}
    {Q Q' : BimoduleCategory A C E} (f : P ⟶ P') (g : Q ⟶ Q')
    (b : B) (c : C) (e e' : E) {p k r i j n : ℤ}
    (ha : k + r = i) (hj : k + p = j) (hn : i + p = n) (u : GradedHom A e e' p)
    (q : ((BimoduleCategory.underlying A C E Q).value c e).X k)
    (v : ((BimoduleCategory.underlying A B C P).value b c).X r) :
    composeMapComponent A B C E f g b e' n
      (SerrePositivity.DifferentialGraded.leftAction A
        ((compose A B C E (BimoduleCategory.underlying A B C P)
          (BimoduleCategory.underlying A C E Q)).leftAt b) u
        (BalancedTensor.element A C ((BimoduleCategory.underlying A C E Q).rightAt e)
          ((BimoduleCategory.underlying A B C P).leftAt b) c q v ha) hn) =
    SerrePositivity.DifferentialGraded.leftAction A
      ((compose A B C E (BimoduleCategory.underlying A B C P')
        (BimoduleCategory.underlying A C E Q')).leftAt b) u
      (composeMapComponent A B C E f g b e i
        (BalancedTensor.element A C ((BimoduleCategory.underlying A C E Q).rightAt e)
          ((BimoduleCategory.underlying A B C P).leftAt b) c q v ha)) hn := by
  have hS := compose_leftAction_element A B C E
    (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q)
    b c e e' ha hj hn u q v
  have hC := composeMapComponent_element A B C E f g b c e q v ha
  have hM := composeMapComponent_element A B C E f g b c e' (r := j) (s := r) (n := n)
    (SerrePositivity.DifferentialGraded.leftAction A
      ((BimoduleCategory.underlying A C E Q).leftAt c) u q hj) v (by omega)
  have hQ := BimoduleCategory.valueMap_leftAction A C E g c e e' hj u q
  have hT := compose_leftAction_element A B C E
    (BimoduleCategory.underlying A B C P') (BimoduleCategory.underlying A C E Q')
    b c e e' ha hj hn u
    (((BimoduleCategory.valueEvaluation A C E c e).map g).f k q)
    (((BimoduleCategory.valueEvaluation A B C b c).map f).f r v)
  have hR := hT.trans (congrArg (fun z :
      ((BimoduleCategory.underlying A C E Q').value c e').X j =>
    BalancedTensor.element A C ((BimoduleCategory.underlying A C E Q').rightAt e')
      ((BimoduleCategory.underlying A B C P').leftAt b) c z
      (((BimoduleCategory.valueEvaluation A B C b c).map f).f r v) (by omega)) hQ).symm
  exact element_square
    (composeMapComponent A B C E f g b e i) (composeMapComponent A B C E f g b e' n)
    (fun z => SerrePositivity.DifferentialGraded.leftAction A
      ((compose A B C E (BimoduleCategory.underlying A B C P)
        (BimoduleCategory.underlying A C E Q)).leftAt b) u z hn)
    (fun z => SerrePositivity.DifferentialGraded.leftAction A
      ((compose A B C E (BimoduleCategory.underlying A B C P')
        (BimoduleCategory.underlying A C E Q')).leftAt b) u z hn)
    _ _ _ _ hS hC hM hR

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMapLeftAction

/-! ## BimoduleMapElementValues（旧 SerrePositivity/DifferentialGraded/Tensor/BimoduleMapElementValues.lean） -/

/-! # 成分の指定した値を使うtensor mapの生成元評価 -/

@[expose] public section BimoduleMapElementValues
universe u v w z

noncomputable section
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

lemma composeMapComponent_element_of_values {P P' : BimoduleCategory A B C}
    {Q Q' : BimoduleCategory A C E} (f : P ⟶ P') (g : Q ⟶ Q') (b : B) (c : C) (e : E)
    {r s n : ℤ} (m : ((BimoduleCategory.underlying A C E Q).value c e).X r)
    (v : ((BimoduleCategory.underlying A B C P).value b c).X s)
    (m' : ((BimoduleCategory.underlying A C E Q').value c e).X r)
    (v' : ((BimoduleCategory.underlying A B C P').value b c).X s)
    (hn : r + s = n)
    (hg : ((BimoduleCategory.valueEvaluation A C E c e).map g).f r m = m')
    (hf : ((BimoduleCategory.valueEvaluation A B C b c).map f).f s v = v') :
    composeMapComponent A B C E f g b e n
      (BalancedTensor.element A C ((BimoduleCategory.underlying A C E Q).rightAt e)
        ((BimoduleCategory.underlying A B C P).leftAt b) c m v hn) =
    BalancedTensor.element A C ((BimoduleCategory.underlying A C E Q').rightAt e)
      ((BimoduleCategory.underlying A B C P').leftAt b) c m' v' hn :=
  (composeMapComponent_element A B C E f g b c e m v hn).trans
    (congrArg₂ (fun x y => BalancedTensor.element A C
      ((BimoduleCategory.underlying A C E Q').rightAt e)
      ((BimoduleCategory.underlying A B C P').leftAt b) c x y hn) hg hf)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMapElementValues

/-! ## BimoduleValueHom（旧 SerrePositivity/DifferentialGraded/Tensor/BimoduleValueHom.lean） -/

/-! # 相対tensorの値のmapを固定した成分関数で表示する -/

@[expose] public section BimoduleValueHom
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

/-- 値のmapを、固定した成分関数を持つchain mapとして再表示する。 -/
def composeValueHom {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    (f : P ⟶ P') (g : Q ⟶ Q') (b : B) (e : E) :
    (compose A B C E (BimoduleCategory.underlying A B C P)
      (BimoduleCategory.underlying A C E Q)).value b e ⟶
    (compose A B C E (BimoduleCategory.underlying A B C P')
      (BimoduleCategory.underlying A C E Q')).value b e :=
  chainMapOfComponentFunctions (composeValueMap A B C E f g b e)
    (composeMapComponent A B C E f g b e) (composeMapComponent_eq A B C E f g b e)

@[simp]
lemma composeValueHom_apply {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    (f : P ⟶ P') (g : Q ⟶ Q') (b : B) (e : E) (n : ℤ) (x) :
    (composeValueHom A B C E f g b e).f n x =
      composeMapComponent A B C E f g b e n x := rfl

lemma composeValueHom_eq {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    (f : P ⟶ P') (g : Q ⟶ Q') (b : B) (e : E) :
    composeValueHom A B C E f g b e = composeValueMap A B C E f g b e :=
  chainMapOfComponentFunctions_eq _ _ _

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleValueHom

/-! ## BimoduleRightElements（旧 SerrePositivity/DifferentialGraded/Tensor/BimoduleRightElements.lean） -/

/-! # bimodule合成の右作用の斉次生成元公式 -/

@[expose] public section BimoduleRightElements
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

/-- 右B作用は先頭Q因子の次数とのKoszul符号を伴ってP因子へ作用する。 -/
lemma compose_rightAction_element (P : Bimodule A B C) (Q : Bimodule A C E)
    (b b' : Bᵒᵖ) (c : C) (e : E) {p k r i j n : ℤ}
    (ha : k + r = i) (hj : r + p = j) (hn : i + p = n)
    (g : GradedHom A b b' p) (q : (Q.value c e).X k) (v : (P.value b.unop c).X r) :
    moduleAction A ((compose A B C E P Q).rightAt e) g
      (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b.unop) c q v ha) hn =
    (p * k).negOnePow • BalancedTensor.element A C (Q.rightAt e) (P.leftAt b'.unop) c q
      (moduleAction A (P.rightAt c) g v hj) (by omega) := by
  have he := BalancedTensor.leftHomMap_element_of_sum A C (Q.rightAt e) (l := j)
    ((P.transposeHom b b').f p g) c q v ha (by omega) hn
  have h := congrArg (fun z => z.f p g) (P.transposeHom_π b b' c)
  change (leftModuleHomπ A C (P.leftAt b.unop) (P.leftAt b'.unop) c).f p
    ((P.transposeHom b b').f p g) = ((P.rightAt c).map b b').f p g at h
  rw [h] at he
  exact he

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleRightElements

/-! ## BimoduleMapRightAction（旧 SerrePositivity/DifferentialGraded/Tensor/BimoduleMapRightAction.lean） -/

/-! # 相対tensorの値のmapと外側の右作用のKoszul可換式 -/

@[expose] public section BimoduleMapRightAction
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

lemma composeMapComponent_rightAction_element {P P' : BimoduleCategory A B C}
    {Q Q' : BimoduleCategory A C E} (f : P ⟶ P') (g : Q ⟶ Q')
    (b b' : Bᵒᵖ) (c : C) (e : E) {p k r i j n : ℤ}
    (ha : k + r = i) (hj : r + p = j) (hn : i + p = n) (u : GradedHom A b b' p)
    (q : ((BimoduleCategory.underlying A C E Q).value c e).X k)
    (v : ((BimoduleCategory.underlying A B C P).value b.unop c).X r) :
    composeMapComponent A B C E f g b'.unop e n
      (moduleAction A ((compose A B C E (BimoduleCategory.underlying A B C P)
          (BimoduleCategory.underlying A C E Q)).rightAt e) u
        (BalancedTensor.element A C ((BimoduleCategory.underlying A C E Q).rightAt e)
          ((BimoduleCategory.underlying A B C P).leftAt b.unop) c q v ha) hn) =
    moduleAction A ((compose A B C E (BimoduleCategory.underlying A B C P')
        (BimoduleCategory.underlying A C E Q')).rightAt e) u
      (composeMapComponent A B C E f g b.unop e i
        (BalancedTensor.element A C ((BimoduleCategory.underlying A C E Q).rightAt e)
          ((BimoduleCategory.underlying A B C P).leftAt b.unop) c q v ha)) hn := by
  let σ : ℤˣ := (p * k).negOnePow
  have hS := compose_rightAction_element A B C E
    (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q)
    b b' c e ha hj hn u q v
  have hC := composeMapComponent_element A B C E f g b.unop c e q v ha
  have hM := composeMapComponent_element A B C E f g b'.unop c e
    (r := k) (s := j) (n := n) q
    (moduleAction A ((BimoduleCategory.underlying A B C P).rightAt c) u v hj) (by omega)
  have hσ := composeMapComponent_units_smul A B C E f g b'.unop e n σ
    (BalancedTensor.element A C ((BimoduleCategory.underlying A C E Q).rightAt e)
      ((BimoduleCategory.underlying A B C P).leftAt b'.unop) c q
      (moduleAction A ((BimoduleCategory.underlying A B C P).rightAt c) u v hj) (by omega))
  have hMσ := hσ.trans (congrArg (fun z => σ • z) hM)
  have hP := BimoduleCategory.valueMap_rightAction A B C f b b' c hj u v
  have hT := compose_rightAction_element A B C E
    (BimoduleCategory.underlying A B C P') (BimoduleCategory.underlying A C E Q')
    b b' c e ha hj hn u
    (((BimoduleCategory.valueEvaluation A C E c e).map g).f k q)
    (((BimoduleCategory.valueEvaluation A B C b.unop c).map f).f r v)
  have hR := hT.trans (congrArg (fun z :
      ((BimoduleCategory.underlying A B C P').value b'.unop c).X j =>
    σ • BalancedTensor.element A C ((BimoduleCategory.underlying A C E Q').rightAt e)
      ((BimoduleCategory.underlying A B C P').leftAt b'.unop) c
      (((BimoduleCategory.valueEvaluation A C E c e).map g).f k q) z (by omega)) hP).symm
  exact element_square
    (composeMapComponent A B C E f g b.unop e i)
    (composeMapComponent A B C E f g b'.unop e n)
    (fun z => moduleAction A ((compose A B C E (BimoduleCategory.underlying A B C P)
      (BimoduleCategory.underlying A C E Q)).rightAt e) u z hn)
    (fun z => moduleAction A ((compose A B C E (BimoduleCategory.underlying A B C P')
      (BimoduleCategory.underlying A C E Q')).rightAt e) u z hn)
    _ _ _ _ hS hC hMσ hR

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMapRightAction

/-! ## BimoduleMapNaturality（旧 SerrePositivity/DifferentialGraded/Tensor/BimoduleMapNaturality.lean） -/

/-! # 相対tensorの値のmapの左右全Hom自然性 -/

@[expose] public section BimoduleMapNaturality
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

lemma composeValueHom_right_naturality {P P' : BimoduleCategory A B C}
    {Q Q' : BimoduleCategory A C E} (f : P ⟶ P') (g : Q ⟶ Q') (b b' : Bᵒᵖ) (e : E) :
    ((compose A B C E (BimoduleCategory.underlying A B C P)
      (BimoduleCategory.underlying A C E Q)).rightAt e).map b b' ≫
      homPostcompose _ (composeValueHom A B C E f g b'.unop e) =
    ((compose A B C E (BimoduleCategory.underlying A B C P')
      (BimoduleCategory.underlying A C E Q')).rightAt e).map b b' ≫
      homPrecompose (composeValueHom A B C E f g b.unop e) _ := by
  apply BalancedTensor.homMap_post_pre_eq A C
    ((BimoduleCategory.underlying A C E Q).rightAt e)
    ((BimoduleCategory.underlying A B C P).leftAt b.unop)
  intro p u c k r i n ha hn q v
  exact composeMapComponent_rightAction_element A B C E f g b b' c e
    (j := r + p) ha rfl hn u q v

lemma composeValueHom_left_naturality {P P' : BimoduleCategory A B C}
    {Q Q' : BimoduleCategory A C E} (f : P ⟶ P') (g : Q ⟶ Q') (b : B) (e e' : E) :
    ((compose A B C E (BimoduleCategory.underlying A B C P)
      (BimoduleCategory.underlying A C E Q)).leftAt b).map e e' ≫
      homPostcompose _ (composeValueHom A B C E f g b e') =
    ((compose A B C E (BimoduleCategory.underlying A B C P')
      (BimoduleCategory.underlying A C E Q')).leftAt b).map e e' ≫
      homPrecompose (composeValueHom A B C E f g b e) _ := by
  apply BalancedTensor.homMap_post_pre_eq A C
    ((BimoduleCategory.underlying A C E Q).rightAt e)
    ((BimoduleCategory.underlying A B C P).leftAt b)
  intro p u c k r i n ha hn q v
  exact composeMapComponent_leftAction_element A B C E f g b c e e'
    (j := k + p) ha rfl hn u q v

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMapNaturality

/-! ## BimoduleMapFamilies（旧 SerrePositivity/DifferentialGraded/Tensor/BimoduleMapFamilies.lean） -/

/-! # 相対tensorの値のmapを全Hom自然な右加群射へ束ねる -/

@[expose] public section BimoduleMapFamilies
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]
variable {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}

/-- tensorの値のmapを右B加群の実際の閉零射へ持ち上げる。 -/
def composeRightMap (f : P ⟶ P') (g : Q ⟶ Q') (e : E) :
    ForgetEnrichment.of (Complex A)
      ((compose A B C E (BimoduleCategory.underlying A B C P)
        (BimoduleCategory.underlying A C E Q)).rightAt e) ⟶
    ForgetEnrichment.of (Complex A)
      ((compose A B C E (BimoduleCategory.underlying A B C P')
        (BimoduleCategory.underlying A C E Q')).rightAt e) :=
  moduleMorphismMk A B
    (M := (compose A B C E (BimoduleCategory.underlying A B C P)
      (BimoduleCategory.underlying A C E Q)).rightAt e)
    (N := (compose A B C E (BimoduleCategory.underlying A B C P')
      (BimoduleCategory.underlying A C E Q')).rightAt e)
    (fun b => composeValueHom A B C E f g b.unop e)
    (fun b b' => composeValueHom_right_naturality A B C E f g b b' e)

@[simp]
lemma composeRightMap_eval (f : P ⟶ P') (g : Q ⟶ Q') (b : B) (e : E) :
    (moduleEvaluation A B b).map (composeRightMap A B C E f g e) =
      composeValueHom A B C E f g b e :=
  moduleMorphismMk_eval A B
    (M := (compose A B C E (BimoduleCategory.underlying A B C P)
      (BimoduleCategory.underlying A C E Q)).rightAt e)
    (N := (compose A B C E (BimoduleCategory.underlying A B C P')
      (BimoduleCategory.underlying A C E Q')).rightAt e)
    (fun b => composeValueHom A B C E f g b.unop e)
    (fun b b' => composeValueHom_right_naturality A B C E f g b b' e) b

@[simp]
lemma composeRightMap_component (f : P ⟶ P') (g : Q ⟶ Q') (b : B) (e : E) :
    moduleMorphismComponent A B
      ((compose A B C E (BimoduleCategory.underlying A B C P)
        (BimoduleCategory.underlying A C E Q)).rightAt e)
      ((compose A B C E (BimoduleCategory.underlying A B C P')
        (BimoduleCategory.underlying A C E Q')).rightAt e)
      (composeRightMap A B C E f g e) b = composeValueHom A B C E f g b e :=
  composeRightMap_eval A B C E f g b e

/-- この右加群射族は、左E作用の主Hom endに関しても全次数で自然。 -/
lemma composeRightMap_naturality (f : P ⟶ P') (g : Q ⟶ Q') (e e' : E) :
    (compose A B C E (BimoduleCategory.underlying A B C P)
      (BimoduleCategory.underlying A C E Q)).toFunctor.map e e' ≫
      moduleHomPostcompose A B _ _ _ (composeRightMap A B C E f g e') =
    (compose A B C E (BimoduleCategory.underlying A B C P')
      (BimoduleCategory.underlying A C E Q')).toFunctor.map e e' ≫
      moduleHomPrecompose A B _ _ _ (composeRightMap A B C E f g e) := by
  apply moduleHom_ext
  intro b
  simp only [Category.assoc]
  rw [moduleHomPostcompose_π, moduleHomPrecompose_π]
  simp only [composeRightMap_component]
  have hh := composeValueHom_left_naturality A B C E f g b e e'
  change ((compose A B C E (BimoduleCategory.underlying A B C P)
      (BimoduleCategory.underlying A C E Q)).toFunctor.map e e' ≫
      moduleHomπ A B _ _ b) ≫ _ =
    ((compose A B C E (BimoduleCategory.underlying A B C P')
      (BimoduleCategory.underlying A C E Q')).toFunctor.map e e' ≫
      moduleHomπ A B _ _ b) ≫ _ at hh
  exact (Category.assoc _ _ _).symm.trans (hh.trans (Category.assoc _ _ _))

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMapFamilies

/-! ## BimoduleFunctor（旧 SerrePositivity/DifferentialGraded/Tensor/BimoduleFunctor.lean） -/

/-! # 全Hom自然な閉零bimodule圏上の相対tensor双関手 -/

@[expose] public section BimoduleFunctor
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

/-- 既存のbimodule対象の合成を全Hom自然な閉零射へ拡張する。 -/
def composeMap {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    BimoduleCategory.of A B E (compose A B C E (BimoduleCategory.underlying A B C P)
      (BimoduleCategory.underlying A C E Q)) ⟶
    BimoduleCategory.of A B E (compose A B C E (BimoduleCategory.underlying A B C P')
      (BimoduleCategory.underlying A C E Q')) :=
  ⟨composeRightMap A B C E f g, composeRightMap_naturality A B C E f g⟩

@[simp]
lemma composeMap_eval {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    (f : P ⟶ P') (g : Q ⟶ Q') (e : E) :
    (BimoduleCategory.evaluation A B E e).map (composeMap A B C E f g) =
      composeRightMap A B C E f g e := rfl

@[simp]
lemma composeMap_value_eval {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    (f : P ⟶ P') (g : Q ⟶ Q') (b : B) (e : E) :
    (BimoduleCategory.valueEvaluation A B E b e).map (composeMap A B C E f g) =
      composeValueMap A B C E f g b e :=
  (composeRightMap_eval A B C E f g b e).trans (composeValueHom_eq A B C E f g b e)

lemma composeMap_id (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E) :
    composeMap A B C E (𝟙 P) (𝟙 Q) =
      𝟙 (BimoduleCategory.of A B E
        (compose A B C E (BimoduleCategory.underlying A B C P)
          (BimoduleCategory.underlying A C E Q))) := by
  apply BimoduleCategory.value_hom_ext A B E
  intro b e
  rw [composeMap_value_eval, CategoryTheory.Functor.map_id]
  exact composeValueMap_id A B C E P Q b e

lemma composeMap_comp {P P' P'' : BimoduleCategory A B C}
    {Q Q' Q'' : BimoduleCategory A C E} (f : P ⟶ P') (f' : P' ⟶ P'')
    (g : Q ⟶ Q') (g' : Q' ⟶ Q'') :
    composeMap A B C E (f ≫ f') (g ≫ g') =
      composeMap A B C E f g ≫ composeMap A B C E f' g' := by
  apply BimoduleCategory.value_hom_ext A B E
  intro b e
  rw [composeMap_value_eval, (BimoduleCategory.valueEvaluation A B E b e).map_comp,
    composeMap_value_eval, composeMap_value_eval]
  exact composeValueMap_comp A B C E f f' g g' b e

/-- 全Hom自然性を射に保持した、実際の閉零bimodule圏上の合成双関手。 -/
def composeFunctor :
    BimoduleCategory A B C × BimoduleCategory A C E ⥤ BimoduleCategory A B E where
  obj PQ := BimoduleCategory.of A B E
    (compose A B C E (BimoduleCategory.underlying A B C PQ.1)
      (BimoduleCategory.underlying A C E PQ.2))
  map fg := composeMap A B C E fg.1 fg.2
  map_id PQ := composeMap_id A B C E PQ.1 PQ.2
  map_comp fg gh := composeMap_comp A B C E fg.1 gh.1 fg.2 gh.2

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleFunctor

/-! ## BimoduleParameterValues（旧 SerrePositivity/DifferentialGraded/Tensor/BimoduleParameterValues.lean） -/

/-! # 任意パラメータのbimodule変換の相対tensorへの値ごとの作用 -/

@[expose] public section BimoduleParameterValues
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]
variable {K : Complex A}

/-- 前の合成因子Pの変換を値ごとに作用させる。 -/
def firstParamValue {P P' : Bimodule A B C} (Q : Bimodule A C E)
    (τ : BimoduleParamTrans A B C K P P') (b : B) (e : E) :
    K ⊗ (compose A B C E P Q).value b e ⟶ (compose A B C E P' Q).value b e :=
  BalancedTensor.leftParamMap A C (Q.rightAt e)
    (Bimodule.paramLeftAt A B C τ b).app (Bimodule.paramLeftAt A B C τ b).naturality

/-- 後の合成因子Qの変換を値ごとに作用させる。 -/
def secondParamValue (P : Bimodule A B C) {Q Q' : Bimodule A C E}
    (τ : BimoduleParamTrans A C E K Q Q') (b : B) (e : E) :
    K ⊗ (compose A B C E P Q).value b e ⟶ (compose A B C E P Q').value b e :=
  BalancedTensor.rightParamMap A C (P.leftAt b)
    (Bimodule.paramRightAt A C E τ e).app (Bimodule.paramRightAt A C E τ e).naturality

/-- P変数の作用ではパラメータがQの値を横切る。 -/
lemma firstParamValue_element {P P' : Bimodule A B C} (Q : Bimodule A C E)
    (τ : BimoduleParamTrans A B C K P P') (b : B) (c : C) (e : E)
    {k r s n : ℤ} (t : K.X k) (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hn : k + (r + s) = n) :
    (firstParamValue A B C E Q τ b e).f n
      (ιTensorObj K ((compose A B C E P Q).value b e) k (r + s) n hn
        (t ⊗ₜ[A] BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v rfl)) =
    (k * r).negOnePow • BalancedTensor.element A C (Q.rightAt e) (P'.leftAt b) c q
      ((((Bimodule.paramValue A B C τ b c).f k t).v s (k + s) (by omega)) v)
      (by omega) :=
  BalancedTensor.leftParamMap_element A C (Q.rightAt e)
    (Bimodule.paramLeftAt A B C τ b).app (Bimodule.paramLeftAt A B C τ b).naturality
    c t q v hn

/-- Q変数の作用では追加の交差符号はない。 -/
lemma secondParamValue_element (P : Bimodule A B C) {Q Q' : Bimodule A C E}
    (τ : BimoduleParamTrans A C E K Q Q') (b : B) (c : C) (e : E)
    {k r s n : ℤ} (t : K.X k) (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hn : k + (r + s) = n) :
    (secondParamValue A B C E P τ b e).f n
      (ιTensorObj K ((compose A B C E P Q).value b e) k (r + s) n hn
        (t ⊗ₜ[A] BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v rfl)) =
    BalancedTensor.element A C (Q'.rightAt e) (P.leftAt b) c
      ((((Bimodule.paramValue A C E τ c e).f k t).v r (k + r) (by omega)) q) v
      (by omega) :=
  BalancedTensor.rightParamMap_element A C (P.leftAt b)
    (Bimodule.paramRightAt A C E τ e).app (Bimodule.paramRightAt A C E τ e).naturality
    c t q v hn

/-- P変数の作用の主Hom複体表示。 -/
def firstParamHom {P P' : Bimodule A B C} (Q : Bimodule A C E)
    (τ : BimoduleParamTrans A B C K P P') (b : B) (e : E) :
    K ⟶ homComplex A ((compose A B C E P Q).value b e)
      ((compose A B C E P' Q).value b e) := curryRight (firstParamValue A B C E Q τ b e)

/-- Q変数の作用の主Hom複体表示。 -/
def secondParamHom (P : Bimodule A B C) {Q Q' : Bimodule A C E}
    (τ : BimoduleParamTrans A C E K Q Q') (b : B) (e : E) :
    K ⟶ homComplex A ((compose A B C E P Q).value b e)
      ((compose A B C E P Q').value b e) := curryRight (secondParamValue A B C E P τ b e)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleParameterValues

/-! ## BimoduleParameterElements（旧 SerrePositivity/DifferentialGraded/Tensor/BimoduleParameterElements.lean） -/

/-! # 相対tensorのパラメータ作用のHom複体成分 -/

@[expose] public section BimoduleParameterElements
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory HomologicalComplex CochainComplex HomComplex Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]
variable {K : Complex A}

lemma param_rightAction_units_smul {D : Type w} [DGCategory A D]
    (M : RightModule A D) {x y : Dᵒᵖ} {p r n : ℤ}
    (f : GradedHom A x y p) (u : ℤˣ) (v : (M.obj x).X r) (hn : r + p = n) :
    moduleAction A M f (u • v) hn = u • moduleAction A M f v hn :=
  map_zsmul (((M.map x y).f p f).v r n hn).hom (u : ℤ) v

lemma param_leftAction_units_smul {D : Type w} [DGCategory A D]
    (M : LeftModule A D) {x y : D} {p r n : ℤ}
    (f : GradedHom A x y p) (u : ℤˣ) (v : (M.obj x).X r) (hn : r + p = n) :
    leftAction A M f (u • v) hn = u • leftAction A M f v hn :=
  map_zsmul (((M.map x y).f p f).v r n hn).hom (u : ℤ) v

lemma param_element_units_smul_left (M : RightModule A C) (N : LeftModule A C) (c : C)
    {r s n : ℤ} (u : ℤˣ) (q : (M.obj (op c)).X r) (v : (N.obj c).X s)
    (hn : r + s = n) :
    BalancedTensor.element A C M N c (u • q) v hn =
      u • BalancedTensor.element A C M N c q v hn := by
  have ht : (u • q) ⊗ₜ[A] v = u • (q ⊗ₜ[A] v) :=
    map_zsmul ((TensorProduct.mk A _ _).flip v) (u : ℤ) q
  unfold BalancedTensor.element
  rw [ht]
  simp only [Units.smul_def, map_zsmul]

lemma firstParamHom_element {P P' : Bimodule A B C} (Q : Bimodule A C E)
    (τ : BimoduleParamTrans A B C K P P') (b : B) (c : C) (e : E)
    {k r s i n : ℤ} (t : K.X k) (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hi : r + s = i) (hn : i + k = n) :
    (((firstParamHom A B C E Q τ b e).f k t).v i n hn)
      (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v hi) =
    (k * r).negOnePow • BalancedTensor.element A C (Q.rightAt e) (P'.leftAt b) c q
      ((((Bimodule.paramValue A B C τ b c).f k t).v s (k + s) (by omega)) v) (by omega) := by
  subst i
  change (curryComponent (firstParamValue A B C E Q τ b e) k t).v (r + s) n hn _ = _
  rw [curryComponent_apply]
  exact firstParamValue_element A B C E Q τ b c e (n := n) t q v (by omega)

lemma secondParamHom_element (P : Bimodule A B C) {Q Q' : Bimodule A C E}
    (τ : BimoduleParamTrans A C E K Q Q') (b : B) (c : C) (e : E)
    {k r s i n : ℤ} (t : K.X k) (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hi : r + s = i) (hn : i + k = n) :
    (((secondParamHom A B C E P τ b e).f k t).v i n hn)
      (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v hi) =
    BalancedTensor.element A C (Q'.rightAt e) (P.leftAt b) c
      ((((Bimodule.paramValue A C E τ c e).f k t).v r (k + r) (by omega)) q) v (by omega) := by
  subst i
  change (curryComponent (secondParamValue A B C E P τ b e) k t).v (r + s) n hn _ = _
  rw [curryComponent_apply]
  exact secondParamValue_element A B C E P τ b c e (n := n) t q v (by omega)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleParameterElements

/-! ## BimoduleParameterLeft（旧 SerrePositivity/DifferentialGraded/Tensor/BimoduleParameterLeft.lean） -/

/-! # 任意パラメータの相対tensor作用と外側の左dg作用 -/

@[expose] public section BimoduleParameterLeft
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]
variable {K : Complex A}

lemma firstParamHom_left_cochain {P P' : Bimodule A B C} (Q : Bimodule A C E)
    (τ : BimoduleParamTrans A B C K P P') (b : B) (e e' : E)
    {k p m : ℤ} (hm : k + p = m) (t : K.X k) (f : GradedHom A e e' p) :
    (((((compose A B C E P Q).leftAt b).map e e').f p f).comp
      ((firstParamHom A B C E Q τ b e').f k t) (by omega)) =
    (k * p).negOnePow • (((firstParamHom A B C E Q τ b e).f k t).comp
      ((((compose A B C E P' Q).leftAt b).map e e').f p f) hm) := by
  apply BalancedTensor.cochain_element_ext A C (Q.rightAt e) (P.leftAt b)
  intro c r s i n hi hn q v
  rw [Cochain.comp_v _ _ (by omega) i (i + p) n rfl (by omega),
    Cochain.units_smul_v, Cochain.comp_v _ _ hm i (i + k) n rfl (by omega)]
  change (((firstParamHom A B C E Q τ b e').f k t).v (i + p) n (by omega))
      (leftAction A ((compose A B C E P Q).leftAt b) f
        (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v hi) rfl) =
    (k * p).negOnePow • leftAction A ((compose A B C E P' Q).leftAt b) f
      ((((firstParamHom A B C E Q τ b e).f k t).v i (i + k) rfl)
        (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v hi)) (by omega)
  rw [compose_leftAction_element A B C E P Q b c e e'
    (j := r + p) hi rfl rfl f q v, firstParamHom_element, firstParamHom_element]
  rw [param_leftAction_units_smul]
  rw [compose_leftAction_element A B C E P' Q b c e e'
    (j := r + p) (by omega) rfl (by omega) f]
  simp only [smul_smul, ← Int.negOnePow_add]
  congr 1
  congr 1
  ring

lemma secondParamHom_left_cochain (P : Bimodule A B C) {Q Q' : Bimodule A C E}
    (τ : BimoduleParamTrans A C E K Q Q') (b : B) (e e' : E)
    {k p m : ℤ} (hm : k + p = m) (t : K.X k) (f : GradedHom A e e' p) :
    (((((compose A B C E P Q).leftAt b).map e e').f p f).comp
      ((secondParamHom A B C E P τ b e').f k t) (by omega)) =
    (k * p).negOnePow • (((secondParamHom A B C E P τ b e).f k t).comp
      ((((compose A B C E P Q').leftAt b).map e e').f p f) hm) := by
  apply BalancedTensor.cochain_element_ext A C (Q.rightAt e) (P.leftAt b)
  intro c r s i n hi hn q v
  rw [Cochain.comp_v _ _ (by omega) i (i + p) n rfl (by omega),
    Cochain.units_smul_v, Cochain.comp_v _ _ hm i (i + k) n rfl (by omega)]
  change (((secondParamHom A B C E P τ b e').f k t).v (i + p) n (by omega))
      (leftAction A ((compose A B C E P Q).leftAt b) f
        (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v hi) rfl) =
    (k * p).negOnePow • leftAction A ((compose A B C E P Q').leftAt b) f
      ((((secondParamHom A B C E P τ b e).f k t).v i (i + k) rfl)
        (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v hi)) (by omega)
  rw [compose_leftAction_element A B C E P Q b c e e'
    (j := r + p) hi rfl rfl f q v, secondParamHom_element, secondParamHom_element]
  have ht := leftParamNaturality_apply_of_sum A
    (Bimodule.paramLeftAt A C E τ c).app (Bimodule.paramLeftAt A C E τ c).naturality
    (n := k + (r + p)) (l := k + r) t f q rfl (by omega) (by omega)
  change (((Bimodule.paramValue A C E τ c e').f k t).v (r + p)
      (k + (r + p)) (by omega)) (leftAction A (Q.leftAt c) f q rfl) =
    (k * p).negOnePow • leftAction A (Q'.leftAt c) f
      ((((Bimodule.paramValue A C E τ c e).f k t).v r (k + r) (by omega)) q)
      (by omega) at ht
  rw [ht, compose_leftAction_element A B C E P Q' b c e e'
    (j := k + (r + p)) (by omega) (by omega) (by omega) f]
  exact param_element_units_smul_left A C (Q'.rightAt e') (P.leftAt b) c
    (k * p).negOnePow _ v (by omega)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleParameterLeft

/-! ## BimoduleParameterRight（旧 SerrePositivity/DifferentialGraded/Tensor/BimoduleParameterRight.lean） -/

/-! # 任意パラメータの相対tensor作用と外側の右dg作用 -/

@[expose] public section BimoduleParameterRight
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]
variable {K : Complex A}

lemma secondParamHom_right_cochain (P : Bimodule A B C) {Q Q' : Bimodule A C E}
    (τ : BimoduleParamTrans A C E K Q Q') (b b' : Bᵒᵖ) (e : E)
    {k p m : ℤ} (hm : k + p = m) (t : K.X k) (f : GradedHom A b b' p) :
    (((((compose A B C E P Q).rightAt e).map b b').f p f).comp
      ((secondParamHom A B C E P τ b'.unop e).f k t) (by omega)) =
    (k * p).negOnePow • (((secondParamHom A B C E P τ b.unop e).f k t).comp
      ((((compose A B C E P Q').rightAt e).map b b').f p f) hm) := by
  apply BalancedTensor.cochain_element_ext A C (Q.rightAt e) (P.leftAt b.unop)
  intro c r s i n hi hn q v
  rw [Cochain.comp_v _ _ (by omega) i (i + p) n rfl (by omega),
    Cochain.units_smul_v, Cochain.comp_v _ _ hm i (i + k) n rfl (by omega)]
  change (((secondParamHom A B C E P τ b'.unop e).f k t).v (i + p) n (by omega))
      (moduleAction A ((compose A B C E P Q).rightAt e) f
        (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b.unop) c q v hi) rfl) =
    (k * p).negOnePow • moduleAction A ((compose A B C E P Q').rightAt e) f
      ((((secondParamHom A B C E P τ b.unop e).f k t).v i (i + k) rfl)
        (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b.unop) c q v hi)) (by omega)
  rw [compose_rightAction_element A B C E P Q b b' c e
    (j := s + p) hi rfl rfl f q v]
  simp only [Units.smul_def, map_zsmul]
  rw [secondParamHom_element, secondParamHom_element,
    compose_rightAction_element A B C E P Q' b b' c e
      (j := s + p) (by omega) rfl (by omega) f]
  simp only [← Units.smul_def, smul_smul, ← Int.negOnePow_add]
  have hs : k * p + p * (k + r) = p * r + 2 * (k * p) := by ring
  rw [hs, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

lemma firstParamHom_right_cochain {P P' : Bimodule A B C} (Q : Bimodule A C E)
    (τ : BimoduleParamTrans A B C K P P') (b b' : Bᵒᵖ) (e : E)
    {k p m : ℤ} (hm : k + p = m) (t : K.X k) (f : GradedHom A b b' p) :
    (((((compose A B C E P Q).rightAt e).map b b').f p f).comp
      ((firstParamHom A B C E Q τ b'.unop e).f k t) (by omega)) =
    (k * p).negOnePow • (((firstParamHom A B C E Q τ b.unop e).f k t).comp
      ((((compose A B C E P' Q).rightAt e).map b b').f p f) hm) := by
  apply BalancedTensor.cochain_element_ext A C (Q.rightAt e) (P.leftAt b.unop)
  intro c r s i n hi hn q v
  rw [Cochain.comp_v _ _ (by omega) i (i + p) n rfl (by omega),
    Cochain.units_smul_v, Cochain.comp_v _ _ hm i (i + k) n rfl (by omega)]
  change (((firstParamHom A B C E Q τ b'.unop e).f k t).v (i + p) n (by omega))
      (moduleAction A ((compose A B C E P Q).rightAt e) f
        (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b.unop) c q v hi) rfl) =
    (k * p).negOnePow • moduleAction A ((compose A B C E P' Q).rightAt e) f
      ((((firstParamHom A B C E Q τ b.unop e).f k t).v i (i + k) rfl)
        (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b.unop) c q v hi)) (by omega)
  rw [compose_rightAction_element A B C E P Q b b' c e
    (j := s + p) hi rfl rfl f q v]
  simp only [Units.smul_def, map_zsmul]
  rw [firstParamHom_element, firstParamHom_element]
  simp only [Units.smul_def]
  have ht := moduleParamNaturality_apply_of_sum A
    (Bimodule.paramRightAt A B C τ c).app (Bimodule.paramRightAt A B C τ c).naturality
    (m := k + p) (n := k + (s + p)) (l := k + s) t f v rfl (by omega) rfl (by omega)
  change (((Bimodule.paramValue A B C τ b'.unop c).f k t).v (s + p)
      (k + (s + p)) (by omega)) (moduleAction A (P.rightAt c) f v rfl) =
    (k * p).negOnePow • moduleAction A (P'.rightAt c) f
      ((((Bimodule.paramValue A B C τ b.unop c).f k t).v s (k + s) (by omega)) v)
      (by omega) at ht
  rw [ht]
  simp only [← Units.smul_def]
  rw [param_rightAction_units_smul]
  rw [compose_rightAction_element A B C E P' Q b b' c e
    (j := k + (s + p)) (by omega) (by omega) (by omega) f]
  rw [BalancedTensor.element_units_smul_right]
  simp only [smul_smul, ← Int.negOnePow_add]
  congr 1
  congr 1
  ring

/-- 前の合成因子の変換を、全Hom自然な右B加群変換へ束ねる。 -/
def firstParamRightAt {P P' : Bimodule A B C} (Q : Bimodule A C E)
    (τ : BimoduleParamTrans A B C K P P') (e : E) :
    ModuleParamTrans A B K ((compose A B C E P Q).rightAt e)
      ((compose A B C E P' Q).rightAt e) where
  app b := firstParamHom A B C E Q τ b.unop e
  naturality := moduleParamNaturality_of_cochain A _
    (fun b b' _k _p _m hm t f => firstParamHom_right_cochain A B C E Q τ b b' e hm t f)

/-- 後の合成因子の変換を、全Hom自然な右B加群変換へ束ねる。 -/
def secondParamRightAt (P : Bimodule A B C) {Q Q' : Bimodule A C E}
    (τ : BimoduleParamTrans A C E K Q Q') (e : E) :
    ModuleParamTrans A B K ((compose A B C E P Q).rightAt e)
      ((compose A B C E P Q').rightAt e) where
  app b := secondParamHom A B C E P τ b.unop e
  naturality := moduleParamNaturality_of_cochain A _
    (fun b b' _k _p _m hm t f => secondParamHom_right_cochain A B C E P τ b b' e hm t f)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleParameterRight

/-! ## BimoduleParameters（旧 SerrePositivity/DifferentialGraded/Tensor/BimoduleParameters.lean） -/

/-! # 相対tensor合成の各変数の全次数パラメータ付きbimodule変換 -/

@[expose] public section BimoduleParameters
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]
variable {K : Complex A}

/-- 前の合成因子に作用する、任意Kパラメータの全dg自然な変換。 -/
def firstParam {P P' : Bimodule A B C} (Q : Bimodule A C E)
    (τ : BimoduleParamTrans A B C K P P') :
    BimoduleParamTrans A B E K (compose A B C E P Q) (compose A B C E P' Q) :=
  Bimodule.paramFamilyTrans A B E (firstParamRightAt A B C E Q τ)
    (fun b e e' => Bimodule.leftParamNaturality_of_cochain A
      (M := (compose A B C E P Q).leftAt b) (N := (compose A B C E P' Q).leftAt b)
      (fun d => firstParamHom A B C E Q τ b d)
      (fun d d' _k _p _m hm t f => firstParamHom_left_cochain A B C E Q τ b d d' hm t f)
      e e')

/-- 後の合成因子に作用する、任意Kパラメータの全dg自然な変換。 -/
def secondParam (P : Bimodule A B C) {Q Q' : Bimodule A C E}
    (τ : BimoduleParamTrans A C E K Q Q') :
    BimoduleParamTrans A B E K (compose A B C E P Q) (compose A B C E P Q') :=
  Bimodule.paramFamilyTrans A B E (secondParamRightAt A B C E P τ)
    (fun b e e' => Bimodule.leftParamNaturality_of_cochain A
      (M := (compose A B C E P Q).leftAt b) (N := (compose A B C E P Q').leftAt b)
      (fun d => secondParamHom A B C E P τ b d)
      (fun d d' _k _p _m hm t f => secondParamHom_left_cochain A B C E P τ b d d' hm t f)
      e e')

@[simp]
lemma firstParam_value {P P' : Bimodule A B C} (Q : Bimodule A C E)
    (τ : BimoduleParamTrans A B C K P P') (b : B) (e : E) :
    Bimodule.paramValue A B E (firstParam A B C E Q τ) b e =
      firstParamHom A B C E Q τ b e :=
  Bimodule.paramFamilyTrans_value A B E _ _ b e

@[simp]
lemma secondParam_value (P : Bimodule A B C) {Q Q' : Bimodule A C E}
    (τ : BimoduleParamTrans A C E K Q Q') (b : B) (e : E) :
    Bimodule.paramValue A B E (secondParam A B C E P τ) b e =
      secondParamHom A B C E P τ b e :=
  Bimodule.paramFamilyTrans_value A B E _ _ b e

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleParameters

/-! ## BimoduleMiddleComparison（旧 SerrePositivity/DifferentialGraded/Tensor/BimoduleMiddleComparison.lean） -/

/-! # 中間dg圏の制限とbimodule合成の値での比較

## 概要
中間dg圏の制限とbimodule合成の値での比較。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleComparison
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] (F : DGFunctor A D C)

/-- 制限した二因子のbalanced族を元のtensorの包含で指定する。 -/
def middleRestrictionFamily (P : Bimodule A B C) (Q : Bimodule A C E) (b : B) (e : E) :
    BalancedTensor.BalancedFamily A D
      ((Bimodule.rightRestriction A C D E F Q).rightAt e)
      ((Bimodule.leftRestriction A B C D F P).leftAt b)
      (BalancedTensor.obj A C (Q.rightAt e) (P.leftAt b)) := by
  refine ⟨fun d => BalancedTensor.ι A C (Q.rightAt e) (P.leftAt b) (F.obj d), ?_⟩
  intro x y
  have h := (BalancedTensor.restrictFamily A D C F (Q.rightAt e) (P.leftAt b)
    ⟨fun c => BalancedTensor.ι A C (Q.rightAt e) (P.leftAt b) c,
      BalancedTensor.condition A C (Q.rightAt e) (P.leftAt b)⟩).property x y
  have hl : BalancedTensor.leftAction A D
      ((Bimodule.leftRestriction A B C D F P).leftAt b) x y =
      BalancedTensor.leftAction A D (F.comp (P.leftAt b)) x y := by
    change uncurryRight ((F.map x y ≫ P.map (F.obj x) (F.obj y)) ≫
      moduleHomπ A B _ _ b) = uncurryRight
        (F.map x y ≫ (P.map (F.obj x) (F.obj y) ≫ moduleHomπ A B _ _ b))
    rw [Category.assoc]
  rw [hl]
  exact h

lemma middleRestrictionFamily_val (P : Bimodule A B C) (Q : Bimodule A C E)
    (b : B) (e : E) (d : D) :
    (middleRestrictionFamily A B C D E F P Q b e).val d =
      BalancedTensor.ι A C (Q.rightAt e) (P.leftAt b) (F.obj d) := rfl

/-- 二つの制限の合成から元の合成への、各値での実際のchain map。 -/
def middleRestrictionComparisonValue (P : Bimodule A B C) (Q : Bimodule A C E)
    (b : B) (e : E) :
    (compose A B D E (Bimodule.leftRestriction A B C D F P)
      (Bimodule.rightRestriction A C D E F Q)).value b e ⟶
        (compose A B C E P Q).value b e :=
  BalancedTensor.desc A D _ _ (middleRestrictionFamily A B C D E F P Q b e)

@[reassoc (attr := simp)]
lemma ι_middleRestrictionComparisonValue (P : Bimodule A B C) (Q : Bimodule A C E)
    (b : B) (e : E) (d : D) :
    BalancedTensor.ι A D ((Bimodule.rightRestriction A C D E F Q).rightAt e)
        ((Bimodule.leftRestriction A B C D F P).leftAt b) d ≫
          middleRestrictionComparisonValue A B C D E F P Q b e =
      BalancedTensor.ι A C (Q.rightAt e) (P.leftAt b) (F.obj d) := by
  exact (BalancedTensor.ι_desc A D _ _
    (middleRestrictionFamily A B C D E F P Q b e) d).trans
      (middleRestrictionFamily_val A B C D E F P Q b e d)

lemma middleRestrictionComparisonValue_element (P : Bimodule A B C) (Q : Bimodule A C E)
    (b : B) (e : E) (d : D) {r s n : ℤ}
    (q : (Q.value (F.obj d) e).X r) (p : (P.value b (F.obj d)).X s) (hn : r + s = n) :
    (middleRestrictionComparisonValue A B C D E F P Q b e).f n
        (BalancedTensor.element A D ((Bimodule.rightRestriction A C D E F Q).rightAt e)
          ((Bimodule.leftRestriction A B C D F P).leftAt b) d q p hn) =
      BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) (F.obj d) q p hn :=
  congrArg (fun k => k.f n
    (ιTensorObj (Q.value (F.obj d) e) (P.value b (F.obj d)) r s n hn (q ⊗ₜ[A] p)))
      (ι_middleRestrictionComparisonValue A B C D E F P Q b e d)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleComparison

/-! ## BimoduleMiddleActions（旧 SerrePositivity/DifferentialGraded/Tensor/BimoduleMiddleActions.lean） -/

/-! # 中間圏のtensor比較と外側の両dg作用の可換性

## 概要
中間圏のtensor比較と外側の両dg作用の可換性。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleActions
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] (F : DGFunctor A D C)
  (P : Bimodule A B C) (Q : Bimodule A C E)

lemma middleRestrictionComparisonValue_rightAction (b b' : Bᵒᵖ) (d : D) (e : E)
    {p k r i j n : ℤ} (ha : k + r = i) (hj : r + p = j) (hn : i + p = n)
    (g : GradedHom A b b' p) (q : (Q.value (F.obj d) e).X k)
    (v : (P.value b.unop (F.obj d)).X r) :
    (middleRestrictionComparisonValue A B C D E F P Q b'.unop e).f n
      (moduleAction A ((compose A B D E (Bimodule.leftRestriction A B C D F P)
          (Bimodule.rightRestriction A C D E F Q)).rightAt e) g
        (BalancedTensor.element A D ((Bimodule.rightRestriction A C D E F Q).rightAt e)
          ((Bimodule.leftRestriction A B C D F P).leftAt b.unop) d q v ha) hn) =
    moduleAction A ((compose A B C E P Q).rightAt e) g
      ((middleRestrictionComparisonValue A B C D E F P Q b.unop e).f i
        (BalancedTensor.element A D ((Bimodule.rightRestriction A C D E F Q).rightAt e)
          ((Bimodule.leftRestriction A B C D F P).leftAt b.unop) d q v ha)) hn := by
  rw [compose_rightAction_element A B D E _ _ b b' d e ha hj hn]
  simp only [Units.smul_def, map_zsmul]
  rw [middleRestrictionComparisonValue_element, middleRestrictionComparisonValue_element,
    compose_rightAction_element A B C E P Q b b' (F.obj d) e ha hj hn]
  rfl

lemma middleRestrictionComparisonValue_leftAction (b : B) (d : D) (e e' : E)
    {p k r i j n : ℤ} (ha : k + r = i) (hj : k + p = j) (hn : i + p = n)
    (g : GradedHom A e e' p) (q : (Q.value (F.obj d) e).X k)
    (v : (P.value b (F.obj d)).X r) :
    (middleRestrictionComparisonValue A B C D E F P Q b e').f n
      (SerrePositivity.DifferentialGraded.leftAction A
        ((compose A B D E (Bimodule.leftRestriction A B C D F P)
          (Bimodule.rightRestriction A C D E F Q)).leftAt b) g
        (BalancedTensor.element A D ((Bimodule.rightRestriction A C D E F Q).rightAt e)
          ((Bimodule.leftRestriction A B C D F P).leftAt b) d q v ha) hn) =
    SerrePositivity.DifferentialGraded.leftAction A ((compose A B C E P Q).leftAt b) g
      ((middleRestrictionComparisonValue A B C D E F P Q b e).f i
        (BalancedTensor.element A D ((Bimodule.rightRestriction A C D E F Q).rightAt e)
          ((Bimodule.leftRestriction A B C D F P).leftAt b) d q v ha)) hn := by
  rw [compose_leftAction_element A B D E _ _ b d e e' ha hj hn,
    Bimodule.rightRestriction_leftAction,
    middleRestrictionComparisonValue_element, middleRestrictionComparisonValue_element,
    compose_leftAction_element A B C E P Q b (F.obj d) e e' ha hj hn]

lemma middleRestrictionComparisonValue_right_naturality (b b' : Bᵒᵖ) (e : E) :
    ((compose A B D E (Bimodule.leftRestriction A B C D F P)
        (Bimodule.rightRestriction A C D E F Q)).rightAt e).map b b' ≫
      homPostcompose _ (middleRestrictionComparisonValue A B C D E F P Q b'.unop e) =
    ((compose A B C E P Q).rightAt e).map b b' ≫
      homPrecompose (middleRestrictionComparisonValue A B C D E F P Q b.unop e) _ := by
  apply BalancedTensor.homMap_post_pre_eq A D
    ((Bimodule.rightRestriction A C D E F Q).rightAt e)
    ((Bimodule.leftRestriction A B C D F P).leftAt b.unop)
  intro p g d k r i n ha hn q v
  exact middleRestrictionComparisonValue_rightAction A B C D E F P Q b b' d e
    (j := r + p) ha rfl hn g q v

lemma middleRestrictionComparisonValue_left_naturality (b : B) (e e' : E) :
    ((compose A B D E (Bimodule.leftRestriction A B C D F P)
        (Bimodule.rightRestriction A C D E F Q)).leftAt b).map e e' ≫
      homPostcompose _ (middleRestrictionComparisonValue A B C D E F P Q b e') =
    ((compose A B C E P Q).leftAt b).map e e' ≫
      homPrecompose (middleRestrictionComparisonValue A B C D E F P Q b e) _ := by
  apply BalancedTensor.homMap_post_pre_eq A D
    ((Bimodule.rightRestriction A C D E F Q).rightAt e)
    ((Bimodule.leftRestriction A B C D F P).leftAt b)
  intro p g d k r i n ha hn q v
  exact middleRestrictionComparisonValue_leftAction A B C D E F P Q b d e e'
    (j := k + p) ha rfl hn g q v

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleActions

/-! ## BimoduleMiddleMap（旧 SerrePositivity/DifferentialGraded/Tensor/BimoduleMiddleMap.lean） -/

/-! # 中間dg圏の制限と合成の全Hom自然なbimodule比較射

## 概要
中間dg圏の制限と合成の全Hom自然なbimodule比較射。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleMap
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] (F : DGFunctor A D C)
  (P : Bimodule A B C) (Q : Bimodule A C E)

/-- 各左対象で、値のchain mapを全Hom自然な右加群射へ束ねる。 -/
def middleRestrictionComparisonRightMap (e : E) :
    ForgetEnrichment.of (Complex A)
      ((compose A B D E (Bimodule.leftRestriction A B C D F P)
        (Bimodule.rightRestriction A C D E F Q)).rightAt e) ⟶
      ForgetEnrichment.of (Complex A) ((compose A B C E P Q).rightAt e) :=
  moduleMorphismMk A B
    (fun b => middleRestrictionComparisonValue A B C D E F P Q b.unop e)
    (fun b b' => middleRestrictionComparisonValue_right_naturality A B C D E F P Q b b' e)

@[simp]
lemma middleRestrictionComparisonRightMap_eval (b : B) (e : E) :
    (moduleEvaluation A B b).map (middleRestrictionComparisonRightMap A B C D E F P Q e) =
      middleRestrictionComparisonValue A B C D E F P Q b e :=
  moduleMorphismMk_eval A B _ _ b

@[simp]
lemma middleRestrictionComparisonRightMap_component (b : B) (e : E) :
    moduleMorphismComponent A B
      ((compose A B D E (Bimodule.leftRestriction A B C D F P)
        (Bimodule.rightRestriction A C D E F Q)).rightAt e)
      ((compose A B C E P Q).rightAt e)
      (middleRestrictionComparisonRightMap A B C D E F P Q e) b =
        middleRestrictionComparisonValue A B C D E F P Q b e :=
  middleRestrictionComparisonRightMap_eval A B C D E F P Q b e

lemma middleRestrictionComparisonRightMap_naturality (e e' : E) :
    (compose A B D E (Bimodule.leftRestriction A B C D F P)
        (Bimodule.rightRestriction A C D E F Q)).map e e' ≫
      moduleHomPostcompose A B _ _ _ (middleRestrictionComparisonRightMap A B C D E F P Q e') =
    (compose A B C E P Q).map e e' ≫
      moduleHomPrecompose A B _ _ _ (middleRestrictionComparisonRightMap A B C D E F P Q e) := by
  apply moduleHom_ext
  intro b
  simp only [Category.assoc]
  rw [moduleHomPostcompose_π, moduleHomPrecompose_π]
  simp only [middleRestrictionComparisonRightMap_component]
  have h := middleRestrictionComparisonValue_left_naturality A B C D E F P Q b e e'
  change (((compose A B D E (Bimodule.leftRestriction A B C D F P)
      (Bimodule.rightRestriction A C D E F Q)).map e e') ≫ moduleHomπ A B _ _ b) ≫ _ =
    ((compose A B C E P Q).map e e' ≫ moduleHomπ A B _ _ b) ≫ _ at h
  exact (Category.assoc _ _ _).symm.trans (h.trans (Category.assoc _ _ _))

/-- 中間圏を制限してから合成するbimoduleから、元の合成への実際の閉零射。 -/
def middleRestrictionComparisonMap :
    BimoduleCategory.of A B E (compose A B D E (Bimodule.leftRestriction A B C D F P)
      (Bimodule.rightRestriction A C D E F Q)) ⟶
        BimoduleCategory.of A B E (compose A B C E P Q) :=
  ⟨middleRestrictionComparisonRightMap A B C D E F P Q,
    middleRestrictionComparisonRightMap_naturality A B C D E F P Q⟩

@[simp]
lemma middleRestrictionComparisonMap_value_eval (b : B) (e : E) :
    (BimoduleCategory.valueEvaluation A B E b e).map
        (middleRestrictionComparisonMap A B C D E F P Q) =
      middleRestrictionComparisonValue A B C D E F P Q b e :=
  middleRestrictionComparisonRightMap_eval A B C D E F P Q b e

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleMap

/-! ## BimoduleMiddleNaturality（旧 SerrePositivity/DifferentialGraded/Tensor/BimoduleMiddleNaturality.lean） -/

/-! # 中間dg圏の合成比較射の両因子に関する自然性

## 概要
中間dg圏の合成比較射の両因子に関する自然性。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleNaturality
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] (F : DGFunctor A D C)

lemma middleRestrictionComparisonValue_naturality
    {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    (f : P ⟶ P') (g : Q ⟶ Q') (b : B) (e : E) :
    composeValueMap A B D E (BimoduleCategory.middleLeftRestrictionMap A B C D F f)
        (BimoduleCategory.middleRightRestrictionMap A C D E F g) b e ≫
      middleRestrictionComparisonValue A B C D E F
        (BimoduleCategory.underlying A B C P') (BimoduleCategory.underlying A C E Q') b e =
    middleRestrictionComparisonValue A B C D E F
        (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q) b e ≫
      composeValueMap A B C E f g b e := by
  apply BalancedTensor.hom_ext
  intro d
  have hs := ι_composeValueMap A B D E
    (BimoduleCategory.middleLeftRestrictionMap A B C D F f)
    (BimoduleCategory.middleRightRestrictionMap A C D E F g) b d e
  simp only [BimoduleCategory.middleLeftRestrictionMap_value_eval,
    BimoduleCategory.middleRightRestrictionMap_value_eval] at hs
  have ht := ι_composeValueMap A B C E f g b (F.obj d) e
  have hc := ι_middleRestrictionComparisonValue A B C D E F
    (BimoduleCategory.underlying A B C P') (BimoduleCategory.underlying A C E Q') b e d
  have hp := ι_middleRestrictionComparisonValue_assoc A B C D E F
    (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q) b e d
      (composeValueMap A B C E f g b e)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ middleRestrictionComparisonValue A B C D E F
      (BimoduleCategory.underlying A B C P') (BimoduleCategory.underlying A C E Q') b e) hs).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => ((BimoduleCategory.valueEvaluation A C E (F.obj d) e).map g ⊗ₘ
          (BimoduleCategory.valueEvaluation A B C b (F.obj d)).map f) ≫ k) hc).trans
            (ht.symm.trans hp.symm))))

/-- 既存の合成双関手の射と実際の中間圏比較射が両変数で可換。 -/
lemma middleRestrictionComparisonMap_naturality
    {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    composeMap A B D E (BimoduleCategory.middleLeftRestrictionMap A B C D F f)
        (BimoduleCategory.middleRightRestrictionMap A C D E F g) ≫
      middleRestrictionComparisonMap A B C D E F
        (BimoduleCategory.underlying A B C P') (BimoduleCategory.underlying A C E Q') =
    middleRestrictionComparisonMap A B C D E F
        (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q) ≫
      composeMap A B C E f g := by
  apply BimoduleCategory.value_hom_ext A B E
  intro b e
  simp only [CategoryTheory.Functor.map_comp, composeMap_value_eval,
    middleRestrictionComparisonMap_value_eval]
  exact middleRestrictionComparisonValue_naturality A B C D E F f g b e

/-- 制限してから合成する、既存の関手の積と合成からなる関手。 -/
def middleRestrictedComposeFunctor :
    BimoduleCategory A B C × BimoduleCategory A C E ⥤ BimoduleCategory A B E :=
  ((BimoduleCategory.middleLeftRestrictionFunctor A B C D F).prod
    (BimoduleCategory.middleRightRestrictionFunctor A C D E F)) ⋙ composeFunctor A B D E

/-- 実際の閉零bimodule圏の積上の中間圏比較自然変換。 -/
def middleRestrictionComparisonNatTrans :
    middleRestrictedComposeFunctor A B C D E F ⟶ composeFunctor A B C E where
  app PQ := middleRestrictionComparisonMap A B C D E F
    (BimoduleCategory.underlying A B C PQ.1) (BimoduleCategory.underlying A C E PQ.2)
  naturality {_X _Y} f := middleRestrictionComparisonMap_naturality A B C D E F f.1 f.2

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleNaturality

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "4.4.2.10" (partial := special) "仮定：通常の dg 両側加群の圏と固定した三つの dg 圏（Lean は dg の厳密な相対テンソルの模型に限る）。結論：中間の dg 圏で釣合テンソルを取る合成双関手を与える（固定端点での相対テンソル関手の成分に一致）。operadic 左 Kan 延長による一般の ∞ 圏での定義は含まれない。"] _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeFunctor
attribute [cite HA "4.4.2.11" (partial := special) "仮定：固定した三つの dg 圏、または余等化子と必要なテンソル保存を持つ通常モノイダル圏の内部モノイド（Lean は通常の固定端点の場合に限る）。結論：中間で釣合テンソルを取り外側の両作用を持つ両側加群を与え、dg 模型では双関手となる（固定 A,B,C の成分に一致）。全代数が変動する ∞ 圏の関手は含まれない。"] _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeFunctor
attribute [cite HA "4.4.2.12" (partial := special) "仮定：固定した三つの dg 圏（Lean は三つの作用圏を同じ dg 模型に取る場合に限る）。結論：二つの両側加群を中間でテンソルし、左と右の外端を持つ両側加群を与える（固定端点の関手の成分に一致）。異なる bitensored ∞ 圏と Tens の退縮は含まれない。"] _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeFunctor
attribute [cite HA "4.4.2.13" (partial := special) "仮定：固定した三つの dg 圏（Lean は左右の作用圏が同じ dg 模型の場合に限る）。結論：右に置いた両側加群との相対テンソルを双関手として与える（同じ作用圏にした成分に一致）。異なる作用圏と逆側の Tens の退縮は含まれない。"] _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeFunctor
