module

public import SerrePositivity.DifferentialGraded.Tensor.Compose
public import SerrePositivity.DifferentialGraded.Tensor.Triple
public import SerrePositivity.DifferentialGraded.Complexes.MapComponentFunctions
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.Actions
public import SerrePositivity.DifferentialGraded.Tensor.Associator.Components

/-!
# Tensor.Associator.Restriction

## 概要
外側・二つの中間圏の制限と結合子の可換 squareをまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## OuterUnitRestriction（旧 SerrePositivity/DifferentialGraded/Tensor/OuterUnitRestriction.lean） -/

/-! # 外側だけを制限した合成比較と対角の単位子

## 概要
外側だけを制限した合成比較と対角の単位子。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section OuterUnitRestriction
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory

section Left
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] (D : Type z) [DGCategory A D] (F : DGFunctor A D C)
  (Q : BimoduleCategory A B C)

lemma leftUnitValue_leftRestriction (b : B) (d : D) :
    (leftUnitValueIso A B D
      (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C Q)) b d).hom =
    (leftUnitValueIso A B C (BimoduleCategory.underlying A B C Q) b (F.obj d)).hom := rfl

/-- 外側左制限比較と左単位子の可換square。C・Dのsmallnessは不要。 -/
lemma leftBimoduleUnitIso_leftRestriction :
    (composeLeftRestrictionIso A B B C D F
        (BimoduleCategory.of A B B (Bimodule.diagonal A B)) Q).hom ≫
      (BimoduleCategory.middleLeftRestrictionFunctor A B C D F).map
        (leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C Q)).hom =
    (leftBimoduleUnitIso A B D
      (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C Q))).hom := by
  apply BimoduleCategory.value_hom_ext A B D
  intro b d
  simp only [CategoryTheory.Functor.map_comp, composeLeftRestrictionIso_hom_value]
  rw [Category.id_comp]
  erw [BimoduleCategory.middleLeftRestrictionMap_value_eval,
    leftBimoduleUnitIso_hom_value]
end Left

section Right
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C] (F : DGFunctor A D B)
  (P : BimoduleCategory A B C)

/-- 右制限での左加群表示のYoneda自然性から、値での右単位squareを得る。 -/
lemma rightUnitValue_rightRestriction (d : D) (c : C) :
    (composeRightRestrictionValueIso A B D C C F (BimoduleCategory.underlying A B C P)
        (Bimodule.diagonal A C) d c).hom ≫
      (rightUnitValueIso A B C (BimoduleCategory.underlying A B C P) (F.obj d) c).hom =
    (rightUnitValueIso A D C
      (Bimodule.rightRestriction A B D C F (BimoduleCategory.underlying A B C P)) d c).hom := by
  have h := BalancedTensor.yonedaEvaluation_naturality A C c
    (Bimodule.rightRestrictionLeftEvaluationIso A B D C F P d).hom
  rw [Bimodule.rightRestrictionLeftEvaluationIso_hom_eval] at h
  erw [Category.comp_id] at h
  exact h

/-- 外側右制限比較と右単位子の可換square。Fの準同値性・局所Hom条件は不要。 -/
lemma rightBimoduleUnitIso_rightRestriction :
    (composeRightRestrictionIso A B D C C F P
        (BimoduleCategory.of A C C (Bimodule.diagonal A C))).hom ≫
      (BimoduleCategory.middleRightRestrictionFunctor A B D C F).map
        (rightBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom =
    (rightBimoduleUnitIso A D C
      (Bimodule.rightRestriction A B D C F (BimoduleCategory.underlying A B C P))).hom := by
  apply BimoduleCategory.value_hom_ext A D C
  intro d c
  simp only [CategoryTheory.Functor.map_comp, composeRightRestrictionIso_hom_value]
  have he := BimoduleCategory.middleRightRestrictionMap_value_eval A B D C F
    (rightBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom d c
  have hu := rightBimoduleUnitIso_hom_value A B C
    (BimoduleCategory.underlying A B C P) (F.obj d) c
  have hv := rightBimoduleUnitIso_hom_value A D C
    (Bimodule.rightRestriction A B D C F (BimoduleCategory.underlying A B C P)) d c
  exact (congrArg (fun k =>
    (composeRightRestrictionValueIso A B D C C F (BimoduleCategory.underlying A B C P)
      (Bimodule.diagonal A C) d c).hom ≫ k) (he.trans hu)).trans
    ((rightUnitValue_rightRestriction A B D C F P d c).trans hv.symm)
end Right

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end OuterUnitRestriction

/-! ## RightRestrictionValueHom（旧 SerrePositivity/DifferentialGraded/Tensor/RightRestrictionValueHom.lean） -/

/-! # 外側右制限比較の値を固定した成分関数で表示する

## 概要
外側右制限比較の値を固定した成分関数で表示する。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RightRestrictionValueHom
universe u v w z t

noncomputable section
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] (F : DGFunctor A D B)
  (P : Bimodule A B C) (Q : Bimodule A C E)

/-- 右制限比較の構成を展開せずに使う、型を固定した次数別成分関数。 -/
@[irreducible]
def composeRightRestrictionValueComponent (d : D) (e : E) (n : ℤ) :
    ((compose A D C E (Bimodule.rightRestriction A B D C F P) Q).value d e).X n →
      ((compose A B C E P Q).value (F.obj d) e).X n :=
  fun x => (composeRightRestrictionValueIso A B D C E F P Q d e).hom.f n x

lemma composeRightRestrictionValueComponent_eq (d : D) (e : E) (n : ℤ) (x) :
    composeRightRestrictionValueComponent A B D C E F P Q d e n x =
      (composeRightRestrictionValueIso A B D C E F P Q d e).hom.f n x := by
  unfold composeRightRestrictionValueComponent
  rfl

/-- 固定成分による再表示は、元の右制限比較と同じchain mapである。 -/
def composeRightRestrictionValueHom (d : D) (e : E) :
    (compose A D C E (Bimodule.rightRestriction A B D C F P) Q).value d e ⟶
      (compose A B C E P Q).value (F.obj d) e :=
  chainMapOfComponentFunctions (composeRightRestrictionValueIso A B D C E F P Q d e).hom
    (composeRightRestrictionValueComponent A B D C E F P Q d e)
    (composeRightRestrictionValueComponent_eq A B D C E F P Q d e)

@[simp]
lemma composeRightRestrictionValueHom_apply (d : D) (e : E) (n : ℤ) (x) :
    (composeRightRestrictionValueHom A B D C E F P Q d e).f n x =
      composeRightRestrictionValueComponent A B D C E F P Q d e n x := rfl

lemma composeRightRestrictionValueHom_eq (d : D) (e : E) :
    composeRightRestrictionValueHom A B D C E F P Q d e =
      (composeRightRestrictionValueIso A B D C E F P Q d e).hom :=
  chainMapOfComponentFunctions_eq _ _ _

lemma composeRightRestrictionValueComponent_element (d : D) (c : C) (e : E)
    {r s n : ℤ} (hn : r + s = n) (q : (Q.value c e).X r)
    (p : (P.value (F.obj d) c).X s) :
    composeRightRestrictionValueComponent A B D C E F P Q d e n
        (BalancedTensor.element A C (Q.rightAt e)
          ((Bimodule.rightRestriction A B D C F P).leftAt d) c q p hn) =
      BalancedTensor.element A C (Q.rightAt e) (P.leftAt (F.obj d)) c q p hn :=
  (composeRightRestrictionValueComponent_eq A B D C E F P Q d e n _).trans
    (composeRightRestrictionValueIso_element A B D C E F P Q d c e hn q p)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end RightRestrictionValueHom

/-! ## MiddleRestrictionValueHom（旧 SerrePositivity/DifferentialGraded/Tensor/MiddleRestrictionValueHom.lean） -/

/-! # 中間制限比較の値を固定した成分関数で表示する

## 概要
中間制限比較の値を固定した成分関数で表示する。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section MiddleRestrictionValueHom
universe u v w z t

noncomputable section
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] (F : DGFunctor A D C)
  (P : Bimodule A B C) (Q : Bimodule A C E)

/-- 中間制限比較の構成を展開せずに使う、型を固定した次数別成分関数。 -/
@[irreducible]
def middleRestrictionValueComponent (d : B) (e : E) (n : ℤ) :
    ((compose A B D E (Bimodule.leftRestriction A B C D F P)
      (Bimodule.rightRestriction A C D E F Q)).value d e).X n →
      ((compose A B C E P Q).value d e).X n :=
  fun x => (middleRestrictionComparisonValue A B C D E F P Q d e).f n x

lemma middleRestrictionValueComponent_eq (d : B) (e : E) (n : ℤ) (x) :
    middleRestrictionValueComponent A B C D E F P Q d e n x =
      (middleRestrictionComparisonValue A B C D E F P Q d e).f n x := by
  unfold middleRestrictionValueComponent
  rfl

/-- 固定成分による再表示は、元の中間制限比較と同じchain mapである。 -/
def middleRestrictionValueHom (d : B) (e : E) :
    (compose A B D E (Bimodule.leftRestriction A B C D F P)
      (Bimodule.rightRestriction A C D E F Q)).value d e ⟶
      (compose A B C E P Q).value d e :=
  chainMapOfComponentFunctions (middleRestrictionComparisonValue A B C D E F P Q d e)
    (middleRestrictionValueComponent A B C D E F P Q d e)
    (middleRestrictionValueComponent_eq A B C D E F P Q d e)

@[simp]
lemma middleRestrictionValueHom_apply (d : B) (e : E) (n : ℤ) (x) :
    (middleRestrictionValueHom A B C D E F P Q d e).f n x =
      middleRestrictionValueComponent A B C D E F P Q d e n x := rfl

lemma middleRestrictionValueHom_eq (d : B) (e : E) :
    middleRestrictionValueHom A B C D E F P Q d e =
      (middleRestrictionComparisonValue A B C D E F P Q d e) :=
  chainMapOfComponentFunctions_eq _ _ _

lemma middleRestrictionValueComponent_element (b : B) (d : D) (e : E)
    {r s n : ℤ} (hn : r + s = n) (q : (Q.value (F.obj d) e).X r)
    (p : (P.value b (F.obj d)).X s) :
    middleRestrictionValueComponent A B C D E F P Q b e n
        (BalancedTensor.element A D ((Bimodule.rightRestriction A C D E F Q).rightAt e)
          ((Bimodule.leftRestriction A B C D F P).leftAt b) d q p hn) =
      BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) (F.obj d) q p hn :=
  (middleRestrictionValueComponent_eq A B C D E F P Q b e n _).trans
    (middleRestrictionComparisonValue_element A B C D E F P Q b e d q p hn)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end MiddleRestrictionValueHom

/-! ## AssociatorLeftRestriction（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorLeftRestriction.lean） -/

/-! # 外側左作用の制限は通常のbimodule結合子を保つ

## 概要
外側左作用の制限は通常のbimodule結合子を保つ。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorLeftRestriction
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] (D : Type s) [DGCategory A D]
  (G : DGFunctor A D T) (P : BimoduleCategory A B C)
  (Q : BimoduleCategory A C E) (R : BimoduleCategory A E T)

local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "Q₀" => BimoduleCategory.underlying A C E Q
local notation "R₀" => BimoduleCategory.underlying A E T R
local notation "LR" => Functor.obj (BimoduleCategory.middleLeftRestrictionFunctor A E T D G) R
local notation "PQ" => BimoduleCategory.of A B E (compose A B C E P₀ Q₀)
local notation "QR" => BimoduleCategory.of A C T (compose A C E T Q₀ R₀)

/-- 内側合成の左制限比較を後因子へ作用させても、各値での射は恒等である。 -/
lemma composeMap_leftRestrictionIso_value (b : B) (d : D) :
    (BimoduleCategory.valueEvaluation A B D b d).map
      (composeMap A B C D (𝟙 P) (composeLeftRestrictionIso A C E T D G Q R).hom) =
      𝟙 _ := by
  rw [composeMap_value_eval]
  apply BalancedTensor.hom_ext A C
    ((compose A C E D Q₀ (BimoduleCategory.underlying A E D LR)).rightAt d) ((P₀).leftAt b)
  intro c
  erw [Category.comp_id]
  have h := ι_composeValueMap A B C D (𝟙 P)
    (composeLeftRestrictionIso A C E T D G Q R).hom b c d
  simp only [composeLeftRestrictionIso_hom_value, CategoryTheory.Functor.map_id,
    tensorHom_id, id_whiskerRight, Category.id_comp] at h
  exact h

/-- 結合子の各値は、後因子の外側左作用を制限してから評価しても変わらない。 -/
lemma associatorValue_leftRestriction (b : B) (d : D) :
    (associatorValueIso A B C E D P₀ Q₀ (BimoduleCategory.underlying A E D LR) b d).hom =
      (associatorValueIso A B C E T P₀ Q₀ R₀ b (G.obj d)).hom := by
  unfold associatorValueIso
  rfl

/-- 外側左制限の二段階比較と通常結合子の可換square。終端のsmallness・flatnessは不要。 -/
lemma associatorIso_leftRestriction :
    (associatorIso A B C E D P₀ Q₀ (BimoduleCategory.underlying A E D LR)).hom ≫
      composeMap A B C D (𝟙 P) (composeLeftRestrictionIso A C E T D G Q R).hom ≫
      (composeLeftRestrictionIso A B C T D G P QR).hom =
    (composeLeftRestrictionIso A B E T D G PQ R).hom ≫
      (BimoduleCategory.middleLeftRestrictionFunctor A B T D G).map
        (associatorIso A B C E T P₀ Q₀ R₀).hom := by
  apply BimoduleCategory.value_hom_ext A B D
  intro b d
  have h₁ := associatorIso_hom_value_eval A B C E D P₀ Q₀
    (BimoduleCategory.underlying A E D LR) b d
  have h₂ := composeMap_leftRestrictionIso_value A B C E T D G P Q R b d
  have h₃ := composeLeftRestrictionIso_hom_value A B C T D G P QR b d
  have h₄ := composeLeftRestrictionIso_hom_value A B E T D G PQ R b d
  have h₅ : (BimoduleCategory.valueEvaluation A B D b d).map
      ((BimoduleCategory.middleLeftRestrictionFunctor A B T D G).map
        (associatorIso A B C E T P₀ Q₀ R₀).hom) =
      (BimoduleCategory.valueEvaluation A B T b (G.obj d)).map
        (associatorIso A B C E T P₀ Q₀ R₀).hom := rfl
  have h₆ := associatorIso_hom_value_eval A B C E T P₀ Q₀ R₀ b (G.obj d)
  simp only [CategoryTheory.Functor.map_comp]
  rw [h₁, h₂, h₃, h₄, h₅, h₆]
  erw [Category.comp_id, Category.id_comp]
  exact associatorValue_leftRestriction A B C E T D G P Q R b d

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorLeftRestriction

/-! ## AssociatorRightRestrictionElements（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorRightRestrictionElements.lean） -/

/-! # 外側右制限比較の三重斉次生成元上の計算

## 概要
外側右制限比較の三重斉次生成元上の計算。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorRightRestrictionElements
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] (F : DGFunctor A D B)
  (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E T)

local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "Q₀" => BimoduleCategory.underlying A C E Q
local notation "R₀" => BimoduleCategory.underlying A E T R
local notation "RP" => Bimodule.rightRestriction A B D C F P₀

/-- 右括弧の生成元に外側右制限比較を作用させても、三つの成分と次数を保つ。 -/
lemma composeRightRestriction_rightElement (d : D) (c : C) (e : E) (t : T)
    {k r s l n : ℤ} (τ : ((R₀).value e t).X k) (q : ((Q₀).value c e).X r)
    (p : ((P₀).value (F.obj d) c).X s) (hl : k + r = l) (hn : l + s = n) :
    (composeRightRestrictionValueIso A B D C T F P₀ (compose A C E T Q₀ R₀) d t).hom.f n
        (associatorRightElement A D C E T RP Q₀ R₀ d c e t τ q p hl hn) =
      associatorRightElement A B C E T P₀ Q₀ R₀ (F.obj d) c e t τ q p hl hn := by
  exact composeRightRestrictionValueIso_element A B D C T F P₀ (compose A C E T Q₀ R₀)
    d c t hn (BalancedTensor.element A E ((R₀).rightAt t) ((Q₀).leftAt c) e τ q hl) p

/-- 内側合成の右制限比較を前因子へ作用させた、左括弧の生成元の計算。 -/
lemma composeValueMap_rightRestriction_leftElement (d : D) (c : C) (e : E) (t : T)
    {k r s i n : ℤ} (τ : ((R₀).value e t).X k) (q : ((Q₀).value c e).X r)
    (p : ((P₀).value (F.obj d) c).X s) (hi : r + s = i) (hn : k + i = n) :
    (composeValueMap A D E T (composeRightRestrictionIso A B D C E F P Q).hom (𝟙 R) d t).f n
        (associatorLeftElement A D C E T RP Q₀ R₀ d c e t τ q p hi hn) =
    BalancedTensor.element A E ((R₀).rightAt t)
      ((Bimodule.rightRestriction A B D E F (compose A B C E P₀ Q₀)).leftAt d) e τ
      (BalancedTensor.element A C ((Q₀).rightAt e) ((P₀).leftAt (F.obj d)) c q p hi) hn := by
  have h := composeValueMap_element A D E T
    (composeRightRestrictionIso A B D C E F P Q).hom (𝟙 R) d e t τ
    (BalancedTensor.element A C ((Q₀).rightAt e) ((RP).leftAt d) c q p hi) hn
  simp only [CategoryTheory.Functor.map_id, HomologicalComplex.id_f, ModuleCat.id_apply,
    composeRightRestrictionIso_hom_value] at h
  erw [composeRightRestrictionValueIso_element A B D C E F P₀ Q₀ d c e hi q p] at h
  exact h

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorRightRestrictionElements

/-! ## AssociatorRightRestrictionPathElements（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorRightRestrictionPathElements.lean） -/

/-! # 右制限・結合子の二経路を三重斉次生成元で計算する

## 概要
右制限・結合子の二経路を三重斉次生成元で計算する。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorRightRestrictionPathElements
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] (F : DGFunctor A D B)
  (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E T)

local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "Q₀" => BimoduleCategory.underlying A C E Q
local notation "R₀" => BimoduleCategory.underlying A E T R
local notation "RP" => Bimodule.rightRestriction A B D C F P₀

private lemma eval_two {X Y Z : Type*} (f : X → Y) (g : Y → Z) (x : X) (y : Y) (z : Z)
    (hf : f x = y) (hg : g y = z) : g (f x) = z := (congrArg g hf).trans hg

/-- 結合子の後で右制限比較を行う経路の、三重斉次生成元での計算。 -/
lemma associatorRightRestriction_left_path_element (d : D) (c : C) (e : E) (t : T)
    {k r s i l n : ℤ} (τ : ((R₀).value e t).X k) (q : ((Q₀).value c e).X r)
    (p : ((P₀).value (F.obj d) c).X s) (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    (composeRightRestrictionValueIso A B D C T F P₀ (compose A C E T Q₀ R₀) d t).hom.f n
        ((associatorValueIso A D C E T RP Q₀ R₀ d t).hom.f n
          (associatorLeftElement A D C E T RP Q₀ R₀ d c e t τ q p hi hn)) =
      associatorRightElement A B C E T P₀ Q₀ R₀ (F.obj d) c e t τ q p hl (by omega) := by
  have h₁ := associatorValueIso_hom_element A D C E T RP Q₀ R₀ d c e t τ q p hi hl hn
  have h₂ := composeRightRestriction_rightElement A B D C E T F P Q R
    d c e t τ q p hl (show l + s = n by omega)
  exact eval_two _ _ _ _ _ h₁ h₂

/-- 二つの右制限比較を続けると、元の左括弧の三重生成元を与える。 -/
lemma composeRightRestriction_leftElement (d : D) (c : C) (e : E) (t : T)
    {k r s i n : ℤ} (τ : ((R₀).value e t).X k) (q : ((Q₀).value c e).X r)
    (p : ((P₀).value (F.obj d) c).X s) (hi : r + s = i) (hn : k + i = n) :
    (composeRightRestrictionValueIso A B D E T F (compose A B C E P₀ Q₀) R₀ d t).hom.f n
        ((composeValueMap A D E T (composeRightRestrictionIso A B D C E F P Q).hom
          (𝟙 R) d t).f n
            (associatorLeftElement A D C E T RP Q₀ R₀ d c e t τ q p hi hn)) =
      associatorLeftElement A B C E T P₀ Q₀ R₀ (F.obj d) c e t τ q p hi hn := by
  have h₁ := composeValueMap_rightRestriction_leftElement A B D C E T F P Q R
    d c e t τ q p hi hn
  have h₂ := composeRightRestrictionValueIso_element A B D E T F (compose A B C E P₀ Q₀) R₀
    d e t (r := k) (s := i) (n := n) hn τ
      (BalancedTensor.element A C ((Q₀).rightAt e) ((P₀).leftAt (F.obj d)) c q p hi)
  exact (congrArg (fun z => (composeRightRestrictionValueIso A B D E T F
    (compose A B C E P₀ Q₀) R₀ d t).hom.f n z) h₁).trans h₂

/-- 二段階の右制限比較の後で結合子を行う経路も、同じ三重生成元を与える。 -/
lemma associatorRightRestriction_right_path_element (d : D) (c : C) (e : E) (t : T)
    {k r s i l n : ℤ} (τ : ((R₀).value e t).X k) (q : ((Q₀).value c e).X r)
    (p : ((P₀).value (F.obj d) c).X s) (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    (associatorValueIso A B C E T P₀ Q₀ R₀ (F.obj d) t).hom.f n
        ((composeRightRestrictionValueIso A B D E T F (compose A B C E P₀ Q₀) R₀ d t).hom.f n
          ((composeValueMap A D E T (composeRightRestrictionIso A B D C E F P Q).hom
            (𝟙 R) d t).f n
              (associatorLeftElement A D C E T RP Q₀ R₀ d c e t τ q p hi hn))) =
      associatorRightElement A B C E T P₀ Q₀ R₀ (F.obj d) c e t τ q p hl (by omega) := by
  have h₁ := composeRightRestriction_leftElement A B D C E T F P Q R
    d c e t τ q p hi hn
  have h₂ := associatorValueIso_hom_element A B C E T P₀ Q₀ R₀ (F.obj d) c e t τ q p hi hl hn
  exact (congrArg (fun z =>
    (associatorValueIso A B C E T P₀ Q₀ R₀ (F.obj d) t).hom.f n z) h₁).trans h₂

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorRightRestrictionPathElements

/-! ## AssociatorRightRestrictionComponents（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorRightRestrictionComponents.lean） -/

/-! # 右制限・結合子の二経路の固定成分関数による計算

## 概要
右制限・結合子の二経路の固定成分関数による計算。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorRightRestrictionComponents
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] (F : DGFunctor A D B)
  (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E T)

local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "Q₀" => BimoduleCategory.underlying A C E Q
local notation "R₀" => BimoduleCategory.underlying A E T R
local notation "RP" => Bimodule.rightRestriction A B D C F P₀

/-- 左経路の固定成分は、元の三重生成元をそのまま右括弧へ送る。 -/
lemma associatorRightRestriction_left_component_element (d : D) (c : C) (e : E) (t : T)
    {k r s i l n : ℤ} (τ : ((R₀).value e t).X k) (q : ((Q₀).value c e).X r)
    (p : ((P₀).value (F.obj d) c).X s) (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    composeRightRestrictionValueComponent A B D C T F P₀ (compose A C E T Q₀ R₀) d t n
        (associatorValueComponent A D C E T RP Q₀ R₀ d t n
          (associatorLeftElement A D C E T RP Q₀ R₀ d c e t τ q p hi hn)) =
      associatorRightElement A B C E T P₀ Q₀ R₀ (F.obj d) c e t τ q p hl (by omega) := by
  have h := associatorRightRestriction_left_path_element A B D C E T F P Q R
    d c e t τ q p hi hl hn
  rw [composeRightRestrictionValueComponent_eq, associatorValueComponent_eq]
  exact h

/-- 右経路の固定成分も同じ三重生成元を与える。 -/
lemma associatorRightRestriction_right_component_element (d : D) (c : C) (e : E) (t : T)
    {k r s i l n : ℤ} (τ : ((R₀).value e t).X k) (q : ((Q₀).value c e).X r)
    (p : ((P₀).value (F.obj d) c).X s) (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    associatorValueComponent A B C E T P₀ Q₀ R₀ (F.obj d) t n
        (composeRightRestrictionValueComponent A B D E T F (compose A B C E P₀ Q₀) R₀ d t n
          (composeMapComponent A D E T (composeRightRestrictionIso A B D C E F P Q).hom
            (𝟙 R) d t n
              (associatorLeftElement A D C E T RP Q₀ R₀ d c e t τ q p hi hn))) =
      associatorRightElement A B C E T P₀ Q₀ R₀ (F.obj d) c e t τ q p hl (by omega) := by
  have h := associatorRightRestriction_right_path_element A B D C E T F P Q R
    d c e t τ q p hi hl hn
  rw [associatorValueComponent_eq, composeRightRestrictionValueComponent_eq,
    composeMapComponent_eq]
  exact h

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorRightRestrictionComponents

/-! ## AssociatorRightRestrictionValues（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorRightRestrictionValues.lean） -/

/-! # 外側右制限と結合子の、各値の複体における可換square

## 概要
外側右制限と結合子の、各値の複体における可換square。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorRightRestrictionValues
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] (F : DGFunctor A D B)
  (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E T)

local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "Q₀" => BimoduleCategory.underlying A C E Q
local notation "R₀" => BimoduleCategory.underlying A E T R
local notation "RP" => Bimodule.rightRestriction A B D C F P₀

/-- 固定した成分関数によるchain mapとして、右制限と結合子は可換。 -/
lemma associatorValueHom_rightRestriction (d : D) (t : T) :
    associatorValueHom A D C E T RP Q₀ R₀ d t ≫
      composeRightRestrictionValueHom A B D C T F P₀ (compose A C E T Q₀ R₀) d t =
    composeValueHom A D E T (composeRightRestrictionIso A B D C E F P Q).hom (𝟙 R) d t ≫
      composeRightRestrictionValueHom A B D E T F (compose A B C E P₀ Q₀) R₀ d t ≫
      associatorValueHom A B C E T P₀ Q₀ R₀ (F.obj d) t := by
  apply Cochain.ofHom_injective
  apply associatorLeft_cochain_element_ext A D C E T RP Q₀ R₀ d t
  intro c e k r s i m n hi hm hn τ q p
  simp only [add_zero] at hn
  cases hn
  simp only [Cochain.ofHom_v]
  change composeRightRestrictionValueComponent A B D C T F P₀ (compose A C E T Q₀ R₀) d t m
      (associatorValueComponent A D C E T RP Q₀ R₀ d t m
        (associatorLeftElement A D C E T RP Q₀ R₀ d c e t τ q p hi hm)) =
    associatorValueComponent A B C E T P₀ Q₀ R₀ (F.obj d) t m
      (composeRightRestrictionValueComponent A B D E T F (compose A B C E P₀ Q₀) R₀ d t m
        (composeMapComponent A D E T (composeRightRestrictionIso A B D C E F P Q).hom
          (𝟙 R) d t m (associatorLeftElement A D C E T RP Q₀ R₀ d c e t τ q p hi hm)))
  exact (associatorRightRestriction_left_component_element A B D C E T F P Q R
    d c e t (l := k + r) τ q p hi rfl hm).trans
    (associatorRightRestriction_right_component_element A B D C E T F P Q R
      d c e t (l := k + r) τ q p hi rfl hm).symm

/-- 外側右制限の二段階比較と結合子は、各値の複体で可換。 -/
lemma associatorValue_rightRestriction (d : D) (t : T) :
    (associatorValueIso A D C E T RP Q₀ R₀ d t).hom ≫
      (composeRightRestrictionValueIso A B D C T F P₀ (compose A C E T Q₀ R₀) d t).hom =
    composeValueMap A D E T (composeRightRestrictionIso A B D C E F P Q).hom (𝟙 R) d t ≫
      (composeRightRestrictionValueIso A B D E T F (compose A B C E P₀ Q₀) R₀ d t).hom ≫
      (associatorValueIso A B C E T P₀ Q₀ R₀ (F.obj d) t).hom := by
  simpa only [associatorValueHom_eq, composeValueHom_eq, composeRightRestrictionValueHom_eq]
    using associatorValueHom_rightRestriction A B D C E T F P Q R d t

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorRightRestrictionValues

/-! ## AssociatorRightRestriction（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorRightRestriction.lean） -/

/-! # 外側右作用の制限は通常のbimodule結合子を保つ

## 概要
外側右作用の制限は通常のbimodule結合子を保つ。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorRightRestriction
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] (F : DGFunctor A D B)
  (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E T)

local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "Q₀" => BimoduleCategory.underlying A C E Q
local notation "R₀" => BimoduleCategory.underlying A E T R
local notation "RP" => Bimodule.rightRestriction A B D C F P₀
local notation "PQ" => BimoduleCategory.of A B E (compose A B C E P₀ Q₀)
local notation "QR" => BimoduleCategory.of A C T (compose A C E T Q₀ R₀)

/-- 外側右制限の二段階比較と通常結合子の可換square。終端のsmallness・flatnessは不要。 -/
lemma associatorIso_rightRestriction :
    (associatorIso A D C E T RP Q₀ R₀).hom ≫
      (composeRightRestrictionIso A B D C T F P QR).hom =
    composeMap A D E T (composeRightRestrictionIso A B D C E F P Q).hom (𝟙 R) ≫
      (composeRightRestrictionIso A B D E T F PQ R).hom ≫
      (BimoduleCategory.middleRightRestrictionFunctor A B D T F).map
        (associatorIso A B C E T P₀ Q₀ R₀).hom := by
  apply BimoduleCategory.value_hom_ext A D T
  intro d t
  have hrestrict : (BimoduleCategory.valueEvaluation A D T d t).map
      ((BimoduleCategory.middleRightRestrictionFunctor A B D T F).map
        (associatorIso A B C E T P₀ Q₀ R₀).hom) =
      (BimoduleCategory.valueEvaluation A B T (F.obj d) t).map
        (associatorIso A B C E T P₀ Q₀ R₀).hom :=
    BimoduleCategory.middleRightRestrictionMap_value_eval A B D T F _ d t
  have h₁ := associatorIso_hom_value_eval A D C E T RP Q₀ R₀ d t
  have h₂ := composeRightRestrictionIso_hom_value A B D C T F P QR d t
  have h₃ := composeMap_value_eval A D E T
    (composeRightRestrictionIso A B D C E F P Q).hom (𝟙 R) d t
  have h₄ := composeRightRestrictionIso_hom_value A B D E T F PQ R d t
  have h₅ := associatorIso_hom_value_eval A B C E T P₀ Q₀ R₀ (F.obj d) t
  simp only [CategoryTheory.Functor.map_comp]
  rw [h₁, h₂, h₃, h₄, hrestrict, h₅]
  exact associatorValue_rightRestriction A B D C E T F P Q R d t

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorRightRestriction

/-! ## AssociatorMiddleRestrictionElements（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorMiddleRestrictionElements.lean） -/

/-! # 第一中間圏の制限と結合子の斉次生成元計算

## 概要
第一中間圏の制限と結合子の斉次生成元計算。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorMiddleRestrictionElements
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] (F : DGFunctor A D C)
  (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E T)

local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "Q₀" => BimoduleCategory.underlying A C E Q
local notation "R₀" => BimoduleCategory.underlying A E T R
local notation "LP" => Bimodule.leftRestriction A B C D F P₀
local notation "RQ" => Bimodule.rightRestriction A C D E F Q₀
local notation "LPc" => BimoduleCategory.of A B D LP

/-- 内側の中間比較を作用させると、元の左括弧の三重生成元になる。 -/
lemma composeValueMap_middleRestriction_leftElement (b : B) (d : D) (e : E) (t : T)
    {k r s i n : ℤ} (τ : ((R₀).value e t).X k) (q : ((Q₀).value (F.obj d) e).X r)
    (p : ((P₀).value b (F.obj d)).X s) (hi : r + s = i) (hn : k + i = n) :
    (composeValueMap A B E T (middleRestrictionComparisonMap A B C D E F P₀ Q₀)
        (𝟙 R) b t).f n
        (associatorLeftElement A B D E T LP RQ R₀ b d e t τ q p hi hn) =
      associatorLeftElement A B C E T P₀ Q₀ R₀ b (F.obj d) e t τ q p hi hn := by
  have h := composeValueMap_element A B E T
    (middleRestrictionComparisonMap A B C D E F P₀ Q₀) (𝟙 R) b e t τ
    (BalancedTensor.element A D ((RQ).rightAt e) ((LP).leftAt b) d q p hi) hn
  simp only [CategoryTheory.Functor.map_id, HomologicalComplex.id_f, ModuleCat.id_apply,
    middleRestrictionComparisonMap_value_eval] at h
  erw [middleRestrictionComparisonValue_element A B C D E F P₀ Q₀ b e d q p hi] at h
  exact h

/-- 右括弧の内側の右制限比較は、三成分を保って後の中間比較の生成元を与える。 -/
lemma composeValueMap_rightRestriction_rightElement (b : B) (d : D) (e : E) (t : T)
    {k r s l n : ℤ} (τ : ((R₀).value e t).X k) (q : ((Q₀).value (F.obj d) e).X r)
    (p : ((P₀).value b (F.obj d)).X s) (hl : k + r = l) (hn : l + s = n) :
    (composeValueMap A B D T (𝟙 LPc)
        (composeRightRestrictionIso A C D E T F Q R).hom b t).f n
        (associatorRightElement A B D E T LP RQ R₀ b d e t τ q p hl hn) =
      BalancedTensor.element A D
        ((Bimodule.rightRestriction A C D T F (compose A C E T Q₀ R₀)).rightAt t)
        ((LP).leftAt b) d
        (BalancedTensor.element A E ((R₀).rightAt t) ((Q₀).leftAt (F.obj d)) e τ q hl) p hn := by
  have h := composeValueMap_element A B D T (𝟙 LPc)
    (composeRightRestrictionIso A C D E T F Q R).hom b d t
    (BalancedTensor.element A E ((R₀).rightAt t) ((RQ).leftAt d) e τ q hl) p hn
  simp only [CategoryTheory.Functor.map_id, HomologicalComplex.id_f, ModuleCat.id_apply,
    composeRightRestrictionIso_hom_value] at h
  erw [composeRightRestrictionValueIso_element A C D E T F Q₀ R₀ d e t hl τ q] at h
  exact h

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorMiddleRestrictionElements

/-! ## AssociatorMiddleRestrictionPaths（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorMiddleRestrictionPaths.lean） -/

/-! # 第一中間圏の制限と結合子の二経路の計算

## 概要
第一中間圏の制限と結合子の二経路の計算。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorMiddleRestrictionPaths
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] (F : DGFunctor A D C)
  (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E T)

local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "Q₀" => BimoduleCategory.underlying A C E Q
local notation "R₀" => BimoduleCategory.underlying A E T R
local notation "LP" => Bimodule.leftRestriction A B C D F P₀
local notation "RQ" => Bimodule.rightRestriction A C D E F Q₀
local notation "LPc" => BimoduleCategory.of A B D LP

/-- 右制限比較と中間比較を続けると、元の右括弧の三重生成元になる。 -/
lemma middleRestriction_rightElement (b : B) (d : D) (e : E) (t : T)
    {k r s l n : ℤ} (τ : ((R₀).value e t).X k) (q : ((Q₀).value (F.obj d) e).X r)
    (p : ((P₀).value b (F.obj d)).X s) (hl : k + r = l) (hn : l + s = n) :
    (middleRestrictionComparisonValue A B C D T F P₀ (compose A C E T Q₀ R₀) b t).f n
        ((composeValueMap A B D T (𝟙 LPc)
          (composeRightRestrictionIso A C D E T F Q R).hom b t).f n
          (associatorRightElement A B D E T LP RQ R₀ b d e t τ q p hl hn)) =
      associatorRightElement A B C E T P₀ Q₀ R₀ b (F.obj d) e t τ q p hl hn := by
  have h₁ := composeValueMap_rightRestriction_rightElement A B C D E T F P Q R
    b d e t τ q p hl hn
  have h₂ := middleRestrictionComparisonValue_element A B C D T F P₀
    (compose A C E T Q₀ R₀) b t d
    (BalancedTensor.element A E ((R₀).rightAt t) ((Q₀).leftAt (F.obj d)) e τ q hl) p hn
  exact (congrArg (fun x => (middleRestrictionComparisonValue A B C D T F P₀
    (compose A C E T Q₀ R₀) b t).f n x) h₁).trans h₂

/-- 結合子、内側右比較、中間比較を続ける経路の生成元計算。 -/
lemma associatorMiddleRestriction_left_path_element (b : B) (d : D) (e : E) (t : T)
    {k r s i l n : ℤ} (τ : ((R₀).value e t).X k) (q : ((Q₀).value (F.obj d) e).X r)
    (p : ((P₀).value b (F.obj d)).X s) (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    (middleRestrictionComparisonValue A B C D T F P₀ (compose A C E T Q₀ R₀) b t).f n
        ((composeValueMap A B D T (𝟙 LPc)
          (composeRightRestrictionIso A C D E T F Q R).hom b t).f n
          ((associatorValueIso A B D E T LP RQ R₀ b t).hom.f n
            (associatorLeftElement A B D E T LP RQ R₀ b d e t τ q p hi hn))) =
      associatorRightElement A B C E T P₀ Q₀ R₀ b (F.obj d) e t τ q p hl (by omega) := by
  have h₁ := associatorValueIso_hom_element A B D E T LP RQ R₀ b d e t τ q p hi hl hn
  have h₂ := middleRestriction_rightElement A B C D E T F P Q R b d e t τ q p hl
    (show l + s = n by omega)
  exact (congrArg (fun x => (middleRestrictionComparisonValue A B C D T F P₀
    (compose A C E T Q₀ R₀) b t).f n
    ((composeValueMap A B D T (𝟙 LPc)
      (composeRightRestrictionIso A C D E T F Q R).hom b t).f n x)) h₁).trans h₂

/-- 内側の中間比較の後で結合子を適用する経路も、同じ三重生成元になる。 -/
lemma associatorMiddleRestriction_right_path_element (b : B) (d : D) (e : E) (t : T)
    {k r s i l n : ℤ} (τ : ((R₀).value e t).X k) (q : ((Q₀).value (F.obj d) e).X r)
    (p : ((P₀).value b (F.obj d)).X s) (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    (associatorValueIso A B C E T P₀ Q₀ R₀ b t).hom.f n
        ((composeValueMap A B E T (middleRestrictionComparisonMap A B C D E F P₀ Q₀)
          (𝟙 R) b t).f n
          (associatorLeftElement A B D E T LP RQ R₀ b d e t τ q p hi hn)) =
      associatorRightElement A B C E T P₀ Q₀ R₀ b (F.obj d) e t τ q p hl (by omega) := by
  have h₁ := composeValueMap_middleRestriction_leftElement A B C D E T F P Q R
    b d e t τ q p hi hn
  have h₂ := associatorValueIso_hom_element A B C E T P₀ Q₀ R₀ b (F.obj d) e t τ q p hi hl hn
  exact (congrArg (fun x => (associatorValueIso A B C E T P₀ Q₀ R₀ b t).hom.f n x) h₁).trans h₂

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorMiddleRestrictionPaths

/-! ## AssociatorMiddleRestrictionComponents（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorMiddleRestrictionComponents.lean） -/

/-! # 第一中間圏の制限と結合子の固定成分関数計算

## 概要
第一中間圏の制限と結合子の固定成分関数計算。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorMiddleRestrictionComponents
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] (F : DGFunctor A D C)
  (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E T)

local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "Q₀" => BimoduleCategory.underlying A C E Q
local notation "R₀" => BimoduleCategory.underlying A E T R
local notation "LP" => Bimodule.leftRestriction A B C D F P₀
local notation "RQ" => Bimodule.rightRestriction A C D E F Q₀
local notation "LPc" => BimoduleCategory.of A B D LP

lemma associatorMiddleRestriction_left_component_element (b : B) (d : D) (e : E) (t : T)
    {k r s i l n : ℤ} (τ : ((R₀).value e t).X k) (q : ((Q₀).value (F.obj d) e).X r)
    (p : ((P₀).value b (F.obj d)).X s) (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    middleRestrictionValueComponent A B C D T F P₀ (compose A C E T Q₀ R₀) b t n
        (composeMapComponent A B D T (𝟙 LPc)
          (composeRightRestrictionIso A C D E T F Q R).hom b t n
          (associatorValueComponent A B D E T LP RQ R₀ b t n
            (associatorLeftElement A B D E T LP RQ R₀ b d e t τ q p hi hn))) =
      associatorRightElement A B C E T P₀ Q₀ R₀ b (F.obj d) e t τ q p hl (by omega) := by
  have h := associatorMiddleRestriction_left_path_element A B C D E T F P Q R
    b d e t τ q p hi hl hn
  rw [middleRestrictionValueComponent_eq, composeMapComponent_eq, associatorValueComponent_eq]
  exact h

lemma associatorMiddleRestriction_right_component_element (b : B) (d : D) (e : E) (t : T)
    {k r s i l n : ℤ} (τ : ((R₀).value e t).X k) (q : ((Q₀).value (F.obj d) e).X r)
    (p : ((P₀).value b (F.obj d)).X s) (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    associatorValueComponent A B C E T P₀ Q₀ R₀ b t n
        (composeMapComponent A B E T (middleRestrictionComparisonMap A B C D E F P₀ Q₀)
          (𝟙 R) b t n (associatorLeftElement A B D E T LP RQ R₀ b d e t τ q p hi hn)) =
      associatorRightElement A B C E T P₀ Q₀ R₀ b (F.obj d) e t τ q p hl (by omega) := by
  have h := associatorMiddleRestriction_right_path_element A B C D E T F P Q R
    b d e t τ q p hi hl hn
  rw [associatorValueComponent_eq, composeMapComponent_eq]
  exact h

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorMiddleRestrictionComponents

/-! ## AssociatorMiddleRestrictionValues（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorMiddleRestrictionValues.lean） -/

/-! # 第一中間圏の制限と結合子の値での可換square

## 概要
第一中間圏の制限と結合子の値での可換square。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorMiddleRestrictionValues
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] (F : DGFunctor A D C)
  (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E T)

local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "Q₀" => BimoduleCategory.underlying A C E Q
local notation "R₀" => BimoduleCategory.underlying A E T R
local notation "LP" => Bimodule.leftRestriction A B C D F P₀
local notation "RQ" => Bimodule.rightRestriction A C D E F Q₀
local notation "LPc" => BimoduleCategory.of A B D LP

lemma associatorValueHom_middleRestriction (b : B) (t : T) :
    associatorValueHom A B D E T LP RQ R₀ b t ≫
      composeValueHom A B D T (𝟙 LPc)
        (composeRightRestrictionIso A C D E T F Q R).hom b t ≫
      middleRestrictionValueHom A B C D T F P₀ (compose A C E T Q₀ R₀) b t =
    composeValueHom A B E T (middleRestrictionComparisonMap A B C D E F P₀ Q₀) (𝟙 R) b t ≫
      associatorValueHom A B C E T P₀ Q₀ R₀ b t := by
  apply Cochain.ofHom_injective
  apply associatorLeft_cochain_element_ext A B D E T LP RQ R₀ b t
  intro d e k r s i m n hi hm hn τ q p
  simp only [add_zero] at hn
  cases hn
  simp only [Cochain.ofHom_v]
  change middleRestrictionValueComponent A B C D T F P₀ (compose A C E T Q₀ R₀) b t m
      (composeMapComponent A B D T (𝟙 LPc)
        (composeRightRestrictionIso A C D E T F Q R).hom b t m
        (associatorValueComponent A B D E T LP RQ R₀ b t m
          (associatorLeftElement A B D E T LP RQ R₀ b d e t τ q p hi hm))) =
    associatorValueComponent A B C E T P₀ Q₀ R₀ b t m
      (composeMapComponent A B E T (middleRestrictionComparisonMap A B C D E F P₀ Q₀)
        (𝟙 R) b t m (associatorLeftElement A B D E T LP RQ R₀ b d e t τ q p hi hm))
  exact (associatorMiddleRestriction_left_component_element A B C D E T F P Q R
    b d e t (l := k + r) τ q p hi rfl hm).trans
    (associatorMiddleRestriction_right_component_element A B C D E T F P Q R
      b d e t (l := k + r) τ q p hi rfl hm).symm

lemma associatorValue_middleRestriction (b : B) (t : T) :
    (associatorValueIso A B D E T LP RQ R₀ b t).hom ≫
      composeValueMap A B D T (𝟙 LPc)
        (composeRightRestrictionIso A C D E T F Q R).hom b t ≫
      middleRestrictionComparisonValue A B C D T F P₀ (compose A C E T Q₀ R₀) b t =
    composeValueMap A B E T (middleRestrictionComparisonMap A B C D E F P₀ Q₀) (𝟙 R) b t ≫
      (associatorValueIso A B C E T P₀ Q₀ R₀ b t).hom := by
  simpa only [associatorValueHom_eq, composeValueHom_eq, middleRestrictionValueHom_eq]
    using associatorValueHom_middleRestriction A B C D E T F P Q R b t

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorMiddleRestrictionValues

/-! ## AssociatorMiddleRestriction（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorMiddleRestriction.lean） -/

/-! # 第一中間圏の制限は通常のbimodule結合子と可換

## 概要
第一中間圏の制限は通常のbimodule結合子と可換。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorMiddleRestriction
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] (F : DGFunctor A D C)
  (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E T)

local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "Q₀" => BimoduleCategory.underlying A C E Q
local notation "R₀" => BimoduleCategory.underlying A E T R
local notation "LP" => Bimodule.leftRestriction A B C D F P₀
local notation "RQ" => Bimodule.rightRestriction A C D E F Q₀
local notation "LPc" => BimoduleCategory.of A B D LP
local notation "QR" => BimoduleCategory.of A C T (compose A C E T Q₀ R₀)

/-- 最初の中間圏を制限する比較は、三因子の通常結合子と可換。 -/
lemma associatorIso_middleRestriction :
    (associatorIso A B D E T LP RQ R₀).hom ≫
      composeMap A B D T (𝟙 LPc) (composeRightRestrictionIso A C D E T F Q R).hom ≫
      middleRestrictionComparisonMap A B C D T F P₀ (compose A C E T Q₀ R₀) =
    composeMap A B E T (middleRestrictionComparisonMap A B C D E F P₀ Q₀) (𝟙 R) ≫
      (associatorIso A B C E T P₀ Q₀ R₀).hom := by
  apply BimoduleCategory.value_hom_ext A B T
  intro b t
  have h₁ := associatorIso_hom_value_eval A B D E T LP RQ R₀ b t
  have h₂ := composeMap_value_eval A B D T (𝟙 LPc)
    (composeRightRestrictionIso A C D E T F Q R).hom b t
  have h₃ := middleRestrictionComparisonMap_value_eval A B C D T F P₀
    (compose A C E T Q₀ R₀) b t
  have h₄ := composeMap_value_eval A B E T
    (middleRestrictionComparisonMap A B C D E F P₀ Q₀) (𝟙 R) b t
  have h₅ := associatorIso_hom_value_eval A B C E T P₀ Q₀ R₀ b t
  simp only [CategoryTheory.Functor.map_comp]
  rw [h₁, h₂, h₃, h₄, h₅]
  exact associatorValue_middleRestriction A B C D E T F P Q R b t

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorMiddleRestriction

/-! ## AssociatorSecondMiddleRestrictionElements（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorSecondMiddleRestrictionElements.lean） -/

/-! # 第二中間圏の制限と三重斉次生成元の計算

## 概要
第二中間圏の制限と三重斉次生成元の計算。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorSecondMiddleRestrictionElements
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] (F : DGFunctor A D E)
  (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E T)

local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "Q₀" => BimoduleCategory.underlying A C E Q
local notation "R₀" => BimoduleCategory.underlying A E T R
local notation "LQ" => Bimodule.leftRestriction A C E D F Q₀
local notation "RR" => Bimodule.rightRestriction A E D T F R₀
local notation "RRc" => BimoduleCategory.of A D T RR

lemma composeValueMap_leftRestriction_leftElement (b : B) (c : C) (d : D) (t : T)
    {k r s i n : ℤ} (τ : ((R₀).value (F.obj d) t).X k)
    (q : ((Q₀).value c (F.obj d)).X r) (p : ((P₀).value b c).X s)
    (hi : r + s = i) (hn : k + i = n) :
    (composeValueMap A B D T (composeLeftRestrictionIso A B C E D F P Q).hom
        (𝟙 RRc) b t).f n
        (associatorLeftElement A B C D T P₀ LQ RR b c d t τ q p hi hn) =
      BalancedTensor.element A D ((RR).rightAt t)
        ((Bimodule.leftRestriction A B E D F (compose A B C E P₀ Q₀)).leftAt b) d τ
        (BalancedTensor.element A C ((Q₀).rightAt (F.obj d)) ((P₀).leftAt b) c q p hi) hn := by
  have h := composeValueMap_element A B D T
    (composeLeftRestrictionIso A B C E D F P Q).hom (𝟙 RRc) b d t τ
    (BalancedTensor.element A C ((LQ).rightAt d) ((P₀).leftAt b) c q p hi) hn
  simp only [composeLeftRestrictionIso_hom_value, CategoryTheory.Functor.map_id,
    HomologicalComplex.id_f, ModuleCat.id_apply] at h
  exact h

/-- 左制限比較と中間比較の二段階合成は、元の左括弧の生成元になる。 -/
lemma middleRestriction_leftElement (b : B) (c : C) (d : D) (t : T)
    {k r s i n : ℤ} (τ : ((R₀).value (F.obj d) t).X k)
    (q : ((Q₀).value c (F.obj d)).X r) (p : ((P₀).value b c).X s)
    (hi : r + s = i) (hn : k + i = n) :
    (middleRestrictionComparisonValue A B E D T F (compose A B C E P₀ Q₀) R₀ b t).f n
        ((composeValueMap A B D T (composeLeftRestrictionIso A B C E D F P Q).hom
          (𝟙 RRc) b t).f n
          (associatorLeftElement A B C D T P₀ LQ RR b c d t τ q p hi hn)) =
      associatorLeftElement A B C E T P₀ Q₀ R₀ b c (F.obj d) t τ q p hi hn := by
  have h₁ := composeValueMap_leftRestriction_leftElement A B C D E T F P Q R
    b c d t τ q p hi hn
  have h₂ := middleRestrictionComparisonValue_element A B E D T F
    (compose A B C E P₀ Q₀) R₀ b t d τ
    (BalancedTensor.element A C ((Q₀).rightAt (F.obj d)) ((P₀).leftAt b) c q p hi) hn
  exact (congrArg (fun x => (middleRestrictionComparisonValue A B E D T F
    (compose A B C E P₀ Q₀) R₀ b t).f n x) h₁).trans h₂

lemma composeValueMap_middleRestriction_rightElement (b : B) (c : C) (d : D) (t : T)
    {k r s l n : ℤ} (τ : ((R₀).value (F.obj d) t).X k)
    (q : ((Q₀).value c (F.obj d)).X r) (p : ((P₀).value b c).X s)
    (hl : k + r = l) (hn : l + s = n) :
    (composeValueMap A B C T (𝟙 P) (middleRestrictionComparisonMap A C E D T F Q₀ R₀)
        b t).f n (associatorRightElement A B C D T P₀ LQ RR b c d t τ q p hl hn) =
      associatorRightElement A B C E T P₀ Q₀ R₀ b c (F.obj d) t τ q p hl hn := by
  have h := composeValueMap_element A B C T (𝟙 P)
    (middleRestrictionComparisonMap A C E D T F Q₀ R₀) b c t
    (BalancedTensor.element A D ((RR).rightAt t) ((LQ).leftAt c) d τ q hl) p hn
  simp only [CategoryTheory.Functor.map_id, HomologicalComplex.id_f, ModuleCat.id_apply,
    middleRestrictionComparisonMap_value_eval] at h
  erw [middleRestrictionComparisonValue_element A C E D T F Q₀ R₀ c t d τ q hl] at h
  exact h

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorSecondMiddleRestrictionElements

/-! ## AssociatorSecondMiddleRestrictionPaths（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorSecondMiddleRestrictionPaths.lean） -/

/-! # 第二中間圏の制限と結合子の二経路

## 概要
第二中間圏の制限と結合子の二経路。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorSecondMiddleRestrictionPaths
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] (F : DGFunctor A D E)
  (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E T)

local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "Q₀" => BimoduleCategory.underlying A C E Q
local notation "R₀" => BimoduleCategory.underlying A E T R
local notation "LQ" => Bimodule.leftRestriction A C E D F Q₀
local notation "RR" => Bimodule.rightRestriction A E D T F R₀
local notation "RRc" => BimoduleCategory.of A D T RR

lemma associatorSecondMiddleRestriction_left_path_element (b : B) (c : C) (d : D) (t : T)
    {k r s i l n : ℤ} (τ : ((R₀).value (F.obj d) t).X k)
    (q : ((Q₀).value c (F.obj d)).X r) (p : ((P₀).value b c).X s)
    (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    (associatorValueIso A B C E T P₀ Q₀ R₀ b t).hom.f n
        ((middleRestrictionComparisonValue A B E D T F (compose A B C E P₀ Q₀) R₀ b t).f n
          ((composeValueMap A B D T (composeLeftRestrictionIso A B C E D F P Q).hom
            (𝟙 RRc) b t).f n
            (associatorLeftElement A B C D T P₀ LQ RR b c d t τ q p hi hn))) =
      associatorRightElement A B C E T P₀ Q₀ R₀ b c (F.obj d) t τ q p hl (by omega) := by
  have h₁ := middleRestriction_leftElement A B C D E T F P Q R b c d t τ q p hi hn
  have h₂ := associatorValueIso_hom_element A B C E T P₀ Q₀ R₀ b c (F.obj d) t τ q p hi hl hn
  exact (congrArg (fun x => (associatorValueIso A B C E T P₀ Q₀ R₀ b t).hom.f n x) h₁).trans h₂

lemma associatorSecondMiddleRestriction_right_path_element (b : B) (c : C) (d : D) (t : T)
    {k r s i l n : ℤ} (τ : ((R₀).value (F.obj d) t).X k)
    (q : ((Q₀).value c (F.obj d)).X r) (p : ((P₀).value b c).X s)
    (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    (composeValueMap A B C T (𝟙 P) (middleRestrictionComparisonMap A C E D T F Q₀ R₀)
        b t).f n ((associatorValueIso A B C D T P₀ LQ RR b t).hom.f n
          (associatorLeftElement A B C D T P₀ LQ RR b c d t τ q p hi hn)) =
      associatorRightElement A B C E T P₀ Q₀ R₀ b c (F.obj d) t τ q p hl (by omega) := by
  have h₁ := associatorValueIso_hom_element A B C D T P₀ LQ RR b c d t τ q p hi hl hn
  have h₂ := composeValueMap_middleRestriction_rightElement A B C D E T F P Q R
    b c d t τ q p hl (show l + s = n by omega)
  exact (congrArg (fun x => (composeValueMap A B C T (𝟙 P)
    (middleRestrictionComparisonMap A C E D T F Q₀ R₀) b t).f n x) h₁).trans h₂

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorSecondMiddleRestrictionPaths

/-! ## AssociatorSecondMiddleRestrictionComponents（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorSecondMiddleRestrictionComponents.lean） -/

/-! # 第二中間圏の制限と結合子の固定成分計算

## 概要
第二中間圏の制限と結合子の固定成分計算。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorSecondMiddleRestrictionComponents
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] (F : DGFunctor A D E)
  (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E T)

local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "Q₀" => BimoduleCategory.underlying A C E Q
local notation "R₀" => BimoduleCategory.underlying A E T R
local notation "LQ" => Bimodule.leftRestriction A C E D F Q₀
local notation "RR" => Bimodule.rightRestriction A E D T F R₀
local notation "RRc" => BimoduleCategory.of A D T RR

lemma associatorSecondMiddleRestriction_left_component_element
    (b : B) (c : C) (d : D) (t : T) {k r s i l n : ℤ}
    (τ : ((R₀).value (F.obj d) t).X k) (q : ((Q₀).value c (F.obj d)).X r)
    (p : ((P₀).value b c).X s) (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    associatorValueComponent A B C E T P₀ Q₀ R₀ b t n
        (middleRestrictionValueComponent A B E D T F (compose A B C E P₀ Q₀) R₀ b t n
          (composeMapComponent A B D T (composeLeftRestrictionIso A B C E D F P Q).hom
            (𝟙 RRc) b t n
            (associatorLeftElement A B C D T P₀ LQ RR b c d t τ q p hi hn))) =
      associatorRightElement A B C E T P₀ Q₀ R₀ b c (F.obj d) t τ q p hl (by omega) := by
  have h := associatorSecondMiddleRestriction_left_path_element A B C D E T F P Q R
    b c d t τ q p hi hl hn
  rw [associatorValueComponent_eq, middleRestrictionValueComponent_eq, composeMapComponent_eq]
  exact h

lemma associatorSecondMiddleRestriction_right_component_element
    (b : B) (c : C) (d : D) (t : T) {k r s i l n : ℤ}
    (τ : ((R₀).value (F.obj d) t).X k) (q : ((Q₀).value c (F.obj d)).X r)
    (p : ((P₀).value b c).X s) (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    composeMapComponent A B C T (𝟙 P) (middleRestrictionComparisonMap A C E D T F Q₀ R₀)
        b t n (associatorValueComponent A B C D T P₀ LQ RR b t n
          (associatorLeftElement A B C D T P₀ LQ RR b c d t τ q p hi hn)) =
      associatorRightElement A B C E T P₀ Q₀ R₀ b c (F.obj d) t τ q p hl (by omega) := by
  have h := associatorSecondMiddleRestriction_right_path_element A B C D E T F P Q R
    b c d t τ q p hi hl hn
  rw [composeMapComponent_eq, associatorValueComponent_eq]
  exact h

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorSecondMiddleRestrictionComponents

/-! ## AssociatorSecondMiddleRestrictionValues（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorSecondMiddleRestrictionValues.lean） -/

/-! # 第二中間圏の制限と結合子の値での可換square

## 概要
第二中間圏の制限と結合子の値での可換square。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorSecondMiddleRestrictionValues
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] (F : DGFunctor A D E)
  (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E T)

local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "Q₀" => BimoduleCategory.underlying A C E Q
local notation "R₀" => BimoduleCategory.underlying A E T R
local notation "LQ" => Bimodule.leftRestriction A C E D F Q₀
local notation "RR" => Bimodule.rightRestriction A E D T F R₀
local notation "RRc" => BimoduleCategory.of A D T RR

lemma associatorValueHom_secondMiddleRestriction (b : B) (t : T) :
    composeValueHom A B D T (composeLeftRestrictionIso A B C E D F P Q).hom (𝟙 RRc) b t ≫
      middleRestrictionValueHom A B E D T F (compose A B C E P₀ Q₀) R₀ b t ≫
      associatorValueHom A B C E T P₀ Q₀ R₀ b t =
    associatorValueHom A B C D T P₀ LQ RR b t ≫
      composeValueHom A B C T (𝟙 P) (middleRestrictionComparisonMap A C E D T F Q₀ R₀) b t := by
  apply Cochain.ofHom_injective
  apply associatorLeft_cochain_element_ext A B C D T P₀ LQ RR b t
  intro c d k r s i m n hi hm hn τ q p
  simp only [add_zero] at hn
  cases hn
  simp only [Cochain.ofHom_v]
  change associatorValueComponent A B C E T P₀ Q₀ R₀ b t m
      (middleRestrictionValueComponent A B E D T F (compose A B C E P₀ Q₀) R₀ b t m
        (composeMapComponent A B D T (composeLeftRestrictionIso A B C E D F P Q).hom
          (𝟙 RRc) b t m (associatorLeftElement A B C D T P₀ LQ RR b c d t τ q p hi hm))) =
    composeMapComponent A B C T (𝟙 P) (middleRestrictionComparisonMap A C E D T F Q₀ R₀)
      b t m (associatorValueComponent A B C D T P₀ LQ RR b t m
        (associatorLeftElement A B C D T P₀ LQ RR b c d t τ q p hi hm))
  exact (associatorSecondMiddleRestriction_left_component_element A B C D E T F P Q R
    b c d t (l := k + r) τ q p hi rfl hm).trans
    (associatorSecondMiddleRestriction_right_component_element A B C D E T F P Q R
      b c d t (l := k + r) τ q p hi rfl hm).symm

lemma associatorValue_secondMiddleRestriction (b : B) (t : T) :
    composeValueMap A B D T (composeLeftRestrictionIso A B C E D F P Q).hom (𝟙 RRc) b t ≫
      middleRestrictionComparisonValue A B E D T F (compose A B C E P₀ Q₀) R₀ b t ≫
      (associatorValueIso A B C E T P₀ Q₀ R₀ b t).hom =
    (associatorValueIso A B C D T P₀ LQ RR b t).hom ≫
      composeValueMap A B C T (𝟙 P) (middleRestrictionComparisonMap A C E D T F Q₀ R₀) b t := by
  simpa only [associatorValueHom_eq, composeValueHom_eq, middleRestrictionValueHom_eq]
    using associatorValueHom_secondMiddleRestriction A B C D E T F P Q R b t

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorSecondMiddleRestrictionValues

/-! ## AssociatorSecondMiddleRestriction（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorSecondMiddleRestriction.lean） -/

/-! # 第二中間圏の制限は通常のbimodule結合子と可換

## 概要
第二中間圏の制限は通常のbimodule結合子と可換。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorSecondMiddleRestriction
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] (F : DGFunctor A D E)
  (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E T)

local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "Q₀" => BimoduleCategory.underlying A C E Q
local notation "R₀" => BimoduleCategory.underlying A E T R
local notation "LQ" => Bimodule.leftRestriction A C E D F Q₀
local notation "RR" => Bimodule.rightRestriction A E D T F R₀
local notation "RRc" => BimoduleCategory.of A D T RR

/-- 後二因子の間の圏を制限する比較と、三因子の通常結合子の可換square。 -/
lemma associatorIso_secondMiddleRestriction :
    composeMap A B D T (composeLeftRestrictionIso A B C E D F P Q).hom (𝟙 RRc) ≫
      middleRestrictionComparisonMap A B E D T F (compose A B C E P₀ Q₀) R₀ ≫
      (associatorIso A B C E T P₀ Q₀ R₀).hom =
    (associatorIso A B C D T P₀ LQ RR).hom ≫
      composeMap A B C T (𝟙 P) (middleRestrictionComparisonMap A C E D T F Q₀ R₀) := by
  apply BimoduleCategory.value_hom_ext A B T
  intro b t
  have h₁ := composeMap_value_eval A B D T
    (composeLeftRestrictionIso A B C E D F P Q).hom (𝟙 RRc) b t
  have h₂ := middleRestrictionComparisonMap_value_eval A B E D T F
    (compose A B C E P₀ Q₀) R₀ b t
  have h₃ := associatorIso_hom_value_eval A B C E T P₀ Q₀ R₀ b t
  have h₄ := associatorIso_hom_value_eval A B C D T P₀ LQ RR b t
  have h₅ := composeMap_value_eval A B C T (𝟙 P)
    (middleRestrictionComparisonMap A C E D T F Q₀ R₀) b t
  simp only [CategoryTheory.Functor.map_comp]
  rw [h₁, h₂, h₃, h₄, h₅]
  exact associatorValue_secondMiddleRestriction A B C D E T F P Q R b t

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorSecondMiddleRestriction
