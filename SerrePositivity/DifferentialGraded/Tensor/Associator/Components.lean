module

public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.Actions
public import SerrePositivity.DifferentialGraded.Tensor.Fubini
public import SerrePositivity.DifferentialGraded.Tensor.BalancedElements
public import SerrePositivity.DifferentialGraded.Complexes.MapEvaluation
public import SerrePositivity.DifferentialGraded.Complexes.HomMapEvaluation
public import SerrePositivity.DifferentialGraded.Bimodule.Basic
public import SerrePositivity.DifferentialGraded.Complexes.UnitScalarEvaluation
public import SerrePositivity.DifferentialGraded.Complexes.MapComponentFunctions
public import SerrePositivity.DifferentialGraded.Module.Isomorphism
public import SerrePositivity.DifferentialGraded.Module.HomWhisker

/-!
# Tensor.Associator.Components

## 概要
結合比較の三重生成元・左右作用・全 Hom 自然性と同型成分をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

universe u v w z t

/-! ## TripleFunctors（旧 SerrePositivity/DifferentialGraded/Tensor/TripleFunctors.lean） -/

/-! # 三つの閉零bimoduleの反復合成関手 -/

@[expose] public section TripleFunctors

noncomputable section
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 左括弧付けの実際の三変数合成関手。 -/
def leftTripleFunctor :
    (BimoduleCategory A B C × BimoduleCategory A C E) × BimoduleCategory A E F ⥤
      BimoduleCategory A B F :=
  ((composeFunctor A B C E).prod (𝟭 (BimoduleCategory A E F))) ⋙ composeFunctor A B E F

/-- 右括弧付けの実際の三変数合成関手。 -/
def rightTripleFunctor :
    (BimoduleCategory A B C × BimoduleCategory A C E) × BimoduleCategory A E F ⥤
      BimoduleCategory A B F where
  obj X := BimoduleCategory.of A B F
    (compose A B C F (BimoduleCategory.underlying A B C X.1.1)
      (compose A C E F (BimoduleCategory.underlying A C E X.1.2)
        (BimoduleCategory.underlying A E F X.2)))
  map f := composeMap A B C F f.1.1 (composeMap A C E F f.1.2 f.2)
  map_id X := by
    change composeMap A B C F (𝟙 X.1.1) (composeMap A C E F (𝟙 X.1.2) (𝟙 X.2)) = _
    rw [composeMap_id]
    exact composeMap_id A B C F _ _
  map_comp f g := by
    change composeMap A B C F (f.1.1 ≫ g.1.1)
      (composeMap A C E F (f.1.2 ≫ g.1.2) (f.2 ≫ g.2)) = _
    rw [composeMap_comp]
    exact composeMap_comp A B C F _ _ _ _

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end TripleFunctors

/-! ## AssociatorValues（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorValues.lean） -/

/-! # bimodule合成の値における結合比較 -/

@[expose] public section AssociatorValues

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

/-- 実際の合成bimoduleを左加群として読むと、既存の左作用関手と一致する。 -/
lemma compose_leftAt_eq (P : Bimodule A B C) (Q : Bimodule A C E) (b : B) :
    (compose A B C E P Q).leftAt b = leftAt A B C E P Q b := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (compose A B C E P Q).leftAt b) (G := leftAt A B C E P Q b) (fun _ => rfl)
  intro e e'
  change ((compose A B C E P Q).toFunctor.map e e' ≫
    moduleHomπ A B (rightAt A B C E P Q e) (rightAt A B C E P Q e') b) ≫ 𝟙 _ =
    Q.toFunctor.map e e' ≫
      BalancedTensor.rightHomMap A C (Q.rightAt e) (Q.rightAt e') (P.leftAt b)
  rw [Category.comp_id, compose_leftMap_π]

variable (F : Type t) [DGCategory A F] [Small.{u} E]

/-- 右端Fのsmallnessを要求しない、三つのbimoduleの結合比較の値。 -/
-- Keep the equality transport behind the generator computation API.
@[irreducible]
def associatorValueIso (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b : B) (f : F) :
    (compose A B E F (compose A B C E P Q) R).value b f ≅
      (compose A B C F P (compose A C E F Q R)).value b f :=
  eqToIso (congrArg (fun N : LeftModule A E => BalancedTensor.obj A E (R.rightAt f) N)
      (compose_leftAt_eq A B C E P Q b)) ≪≫
    BalancedTensor.Fubini.iso A C E Q (R.rightAt f) (P.leftAt b)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorValues

/-! ## AssociatorGenerators（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorGenerators.lean） -/

/-! # 実際のbimodule結合比較と三重生成元 -/

@[expose] public section AssociatorGenerators

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 左括弧の実際の合成bimoduleの値への三重包含。 -/
def associatorLeftι (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b : B) (c : C) (e : E) (f : F) :
    R.value e f ⊗ (Q.value c e ⊗ P.value b c) ⟶
      (compose A B E F (compose A B C E P Q) R).value b f :=
  (R.value e f ◁ BalancedTensor.ι A C (Q.rightAt e) (P.leftAt b) c) ≫
    BalancedTensor.ι A E (R.rightAt f) ((compose A B C E P Q).leftAt b) e

/-- 右括弧の実際の合成bimoduleの値への三重包含。 -/
def associatorRightι (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b : B) (c : C) (e : E) (f : F) :
    R.value e f ⊗ (Q.value c e ⊗ P.value b c) ⟶
      (compose A B C F P (compose A C E F Q R)).value b f :=
  BalancedTensor.Fubini.rightι A C E Q (R.rightAt f) (P.leftAt b) c e

/-- 左加群構造の比較による輸送は実際の三重包含をFubiniの包含へ送る。 -/
lemma associatorLeftι_transport (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (f : F) :
    associatorLeftι A B C E F P Q R b c e f ≫
      eqToHom (congrArg (fun N : LeftModule A E => BalancedTensor.obj A E (R.rightAt f) N)
        (compose_leftAt_eq A B C E P Q b)) =
    BalancedTensor.Fubini.leftι A C E Q (R.rightAt f) (P.leftAt b) c e := by
  have h := BalancedTensor.ι_changeLeft_hom A E (R.rightAt f)
    (compose_leftAt_eq A B C E P Q b) e
  have he : eqToHom (congrArg (fun N : LeftModule A E => R.value e f ⊗ N.obj e)
      (compose_leftAt_eq A B C E P Q b)) =
      𝟙 (R.value e f ⊗ BalancedTensor.obj A C (Q.rightAt e) (P.leftAt b)) := rfl
  have hh := h.trans (congrArg (fun g : R.value e f ⊗
      BalancedTensor.obj A C (Q.rightAt e) (P.leftAt b) ⟶ R.value e f ⊗
        BalancedTensor.obj A C (Q.rightAt e) (P.leftAt b) =>
      g ≫ BalancedTensor.ι A E (R.rightAt f) (leftAt A B C E P Q b) e) he)
  have hlast := hh.trans (Category.id_comp _)
  have hraw := congrArg (fun g => (R.value e f ◁
    BalancedTensor.ι A C (Q.rightAt e) (P.leftAt b) c) ≫ g) hlast
  dsimp only [associatorLeftι, BalancedTensor.Fubini.leftι,
    BalancedTensor.Fubini.leftModule, leftAt, BalancedTensor.changeLeft, eqToIso.hom] at hraw ⊢
  exact (Category.assoc (R.value e f ◁ BalancedTensor.ι A C (Q.rightAt e) (P.leftAt b) c)
    (BalancedTensor.ι A E (R.rightAt f) ((compose A B C E P Q).leftAt b) e)
    (eqToHom (congrArg (fun N : LeftModule A E => BalancedTensor.obj A E (R.rightAt f) N)
      (compose_leftAt_eq A B C E P Q b)))).trans hraw

@[reassoc (attr := simp)]
lemma associatorLeftι_hom (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b : B) (c : C) (e : E) (f : F) :
    associatorLeftι A B C E F P Q R b c e f ≫ (associatorValueIso A B C E F P Q R b f).hom =
      associatorRightι A B C E F P Q R b c e f := by
  have h := congrArg (fun g => g ≫
    (BalancedTensor.Fubini.iso A C E Q (R.rightAt f) (P.leftAt b)).hom)
    (associatorLeftι_transport A B C E F P Q R b c e f)
  rw [BalancedTensor.Fubini.leftι_iso_hom] at h
  unfold associatorValueIso
  simp only [Iso.trans_hom, eqToIso.hom]
  rw [← Category.assoc]
  exact h

@[reassoc (attr := simp)]
lemma associatorRightι_inv (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b : B) (c : C) (e : E) (f : F) :
    associatorRightι A B C E F P Q R b c e f ≫ (associatorValueIso A B C E F P Q R b f).inv =
      associatorLeftι A B C E F P Q R b c e f := by
  rw [← associatorLeftι_hom A B C E F P Q R b c e f, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- 実際の左括弧の合成からの射を三重生成元で判定する。 -/
lemma associatorLeft_hom_ext (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b : B) (f : F) {T : Complex A}
    {g h : (compose A B E F (compose A B C E P Q) R).value b f ⟶ T}
    (heq : ∀ c e, associatorLeftι A B C E F P Q R b c e f ≫ g =
      associatorLeftι A B C E F P Q R b c e f ≫ h) : g = h := by
  apply BalancedTensor.hom_ext A E (R.rightAt f) ((compose A B C E P Q).leftAt b)
  intro e
  apply BalancedTensor.param_hom_ext A C (Q.rightAt e) (P.leftAt b)
  intro c
  exact heq c e

lemma associatorRight_hom_ext (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b : B) (f : F) {T : Complex A}
    {g h : (compose A B C F P (compose A C E F Q R)).value b f ⟶ T}
    (heq : ∀ c e, associatorRightι A B C E F P Q R b c e f ≫ g =
      associatorRightι A B C E F P Q R b c e f ≫ h) : g = h :=
  BalancedTensor.Fubini.right_hom_ext A C E Q (R.rightAt f) (P.leftAt b) heq

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorGenerators

/-! ## AssociatorCochainExt（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorCochainExt.lean） -/

/-! # 実際の反復bimodule tensorを源とする全次数cochainの外延性 -/

@[expose] public section AssociatorCochainExt

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 微分との可換性を仮定せず、左括弧の反復tensorからのcochainを三重生成元で判定する。 -/
lemma associatorLeft_cochain_element_ext (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f : F) {T : Complex A} {p : ℤ}
    (g h : Cochain ((compose A B E F (compose A B C E P Q) R).value b f) T p)
    (heq : ∀ (c : C) (e : E) (k r s i m n : ℤ)
      (hi : r + s = i) (hm : k + i = m) (hn : m + p = n)
      (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s),
      g.v m n hn (BalancedTensor.element A E (R.rightAt f)
        ((compose A B C E P Q).leftAt b) e t
        (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v hi) hm) =
      h.v m n hn (BalancedTensor.element A E (R.rightAt f)
        ((compose A B C E P Q).leftAt b) e t
        (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v hi) hm)) : g = h := by
  apply BalancedTensor.cochain_element_ext A E (R.rightAt f) ((compose A B C E P Q).leftAt b)
  intro e k i m n hm hn t z
  let K := BalancedTensor.obj A C (Q.rightAt e) (P.leftAt b)
  let L : K.X i →ₗ[A] T.X n :=
    (g.v m n hn).hom.comp
      (((BalancedTensor.ι A E (R.rightAt f) ((compose A B C E P Q).leftAt b) e).f m).hom.comp
        ((ιTensorObj (R.value e f) K k i m hm).hom.comp
          (TensorProduct.mk A ((R.value e f).X k) (K.X i) t)))
  let H : K.X i →ₗ[A] T.X n :=
    (h.v m n hn).hom.comp
      (((BalancedTensor.ι A E (R.rightAt f) ((compose A B C E P Q).leftAt b) e).f m).hom.comp
        ((ιTensorObj (R.value e f) K k i m hm).hom.comp
          (TensorProduct.mk A ((R.value e f).X k) (K.X i) t)))
  have ht : ModuleCat.ofHom L = ModuleCat.ofHom H := by
    apply BalancedTensor.degree_element_ext A C (Q.rightAt e) (P.leftAt b)
    intro c r s hi q v
    exact heq c e k r s i m n hi hm hn t q v
  exact congrArg (fun j => j z) ht

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorCochainExt

/-! ## AssociatorElements（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorElements.lean） -/

/-! # bimodule結合比較の斉次三重生成元での計算 -/

@[expose] public section AssociatorElements

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 左括弧の合成の斉次三重生成元。 -/
def associatorLeftElement (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b : B) (c : C) (e : E) (f : F) {k r s i n : ℤ}
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hi : r + s = i) (hn : k + i = n) :
    ((compose A B E F (compose A B C E P Q) R).value b f).X n :=
  BalancedTensor.element A E (R.rightAt f) ((compose A B C E P Q).leftAt b) e t
    (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v hi) hn

/-- 右括弧の合成の斉次三重生成元。 -/
def associatorRightElement (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b : B) (c : C) (e : E) (f : F) {k r s l n : ℤ}
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hl : k + r = l) (hn : l + s = n) :
    ((compose A B C F P (compose A C E F Q R)).value b f).X n :=
  BalancedTensor.element A C ((compose A C E F Q R).rightAt f) (P.leftAt b) c
    (BalancedTensor.element A E (R.rightAt f) (Q.leftAt c) e t q hl) v hn

lemma associatorLeftElement_eq_ι (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (f : F) {k r s i n : ℤ}
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hi : r + s = i) (hn : k + i = n) :
    associatorLeftElement A B C E F P Q R b c e f t q v hi hn =
    (associatorLeftι A B C E F P Q R b c e f).f n
      (ιTensorObj (R.value e f) (Q.value c e ⊗ P.value b c) k i n hn
        (t ⊗ₜ[A] ιTensorObj (Q.value c e) (P.value b c) r s i hi (q ⊗ₜ[A] v))) := by
  have h := whiskerLeft_apply (R.value e f)
    (BalancedTensor.ι A C (Q.rightAt e) (P.leftAt b) c) k i n hn t
      (ιTensorObj ((Q.rightAt e).obj (op c)) ((P.leftAt b).obj c) r s i hi (q ⊗ₜ[A] v))
  exact (congrArg (fun z =>
    (BalancedTensor.ι A E (R.rightAt f) ((compose A B C E P Q).leftAt b) e).f n z) h).symm

lemma associatorRightElement_eq_ι (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (f : F) {k r s i l n : ℤ}
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    associatorRightElement A B C E F P Q R b c e f t q v hl (by omega) =
    (associatorRightι A B C E F P Q R b c e f).f n
      (ιTensorObj (R.value e f) (Q.value c e ⊗ P.value b c) k i n hn
        (t ⊗ₜ[A] ιTensorObj (Q.value c e) (P.value b c) r s i hi (q ⊗ₜ[A] v))) := by
  have h := BalancedTensor.Fubini.tripleElement_rightι A C E
    (Q := Q) (R := R.rightAt f) (N := P.leftAt b)
    (𝟙 (BalancedTensor.Fubini.rightObj A C E Q (R.rightAt f) (P.leftAt b)))
    c e t q v hi hl hn
  exact h.symm

/-- 結合比較はR,Q,Pの順の三重生成元を符号なしで送る。 -/
lemma associatorValueIso_hom_element (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (f : F) {k r s i l n : ℤ}
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    (associatorValueIso A B C E F P Q R b f).hom.f n
      (associatorLeftElement A B C E F P Q R b c e f t q v hi hn) =
    associatorRightElement A B C E F P Q R b c e f t q v hl (by omega) := by
  have hpoint := chain_comp_apply_of_eq
    (associatorLeftι A B C E F P Q R b c e f)
    (associatorValueIso A B C E F P Q R b f).hom
    (associatorRightι A B C E F P Q R b c e f)
    (associatorLeftι_hom A B C E F P Q R b c e f) n
    (ιTensorObj (R.value e f) (Q.value c e ⊗ P.value b c) k i n hn
      (t ⊗ₜ[A] ιTensorObj (Q.value c e) (P.value b c) r s i hi (q ⊗ₜ[A] v)))
  calc
    _ = (associatorValueIso A B C E F P Q R b f).hom.f n
        ((associatorLeftι A B C E F P Q R b c e f).f n
          (ιTensorObj (R.value e f) (Q.value c e ⊗ P.value b c) k i n hn
            (t ⊗ₜ[A] ιTensorObj (Q.value c e) (P.value b c) r s i hi (q ⊗ₜ[A] v)))) :=
      congrArg (fun z => (associatorValueIso A B C E F P Q R b f).hom.f n z)
        (associatorLeftElement_eq_ι A B C E F P Q R b c e f t q v hi hn)
    _ = (associatorRightι A B C E F P Q R b c e f).f n
        (ιTensorObj (R.value e f) (Q.value c e ⊗ P.value b c) k i n hn
          (t ⊗ₜ[A] ιTensorObj (Q.value c e) (P.value b c) r s i hi (q ⊗ₜ[A] v))) :=
      hpoint
    _ = _ := (associatorRightElement_eq_ι A B C E F P Q R b c e f t q v hi hl hn).symm

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorElements

/-! ## AssociatorDegreeExt（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorDegreeExt.lean） -/

/-! # 三重生成元による各次数の線形写像の外延性 -/

@[expose] public section AssociatorDegreeExt

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

lemma associatorLeft_degree_element_ext (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (d : F) {n : ℤ} {T : ModuleCat.{u} A}
    (a h : ((compose A B E F (compose A B C E P Q) R).value b d).X n ⟶ T)
    (heq : ∀ (c : C) (e : E) (k r s i : ℤ) (hi : r + s = i) (hn : k + i = n)
      (τ : (R.value e d).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s),
      a (associatorLeftElement A B C E F P Q R b c e d τ q v hi hn) =
        h (associatorLeftElement A B C E F P Q R b c e d τ q v hi hn)) : a = h := by
  apply BalancedTensor.degree_element_ext A E (R.rightAt d) ((compose A B C E P Q).leftAt b)
  intro e k i hn τ z
  let K := BalancedTensor.obj A C (Q.rightAt e) (P.leftAt b)
  let L : K.X i →ₗ[A] T := a.hom.comp
    (((BalancedTensor.ι A E (R.rightAt d) ((compose A B C E P Q).leftAt b) e).f n).hom.comp
      ((ιTensorObj (R.value e d) K k i n hn).hom.comp (TensorProduct.mk A _ _ τ)))
  let H : K.X i →ₗ[A] T := h.hom.comp
    (((BalancedTensor.ι A E (R.rightAt d) ((compose A B C E P Q).leftAt b) e).f n).hom.comp
      ((ιTensorObj (R.value e d) K k i n hn).hom.comp (TensorProduct.mk A _ _ τ)))
  have ht : ModuleCat.ofHom L = ModuleCat.ofHom H := by
    apply BalancedTensor.degree_element_ext A C (Q.rightAt e) (P.leftAt b)
    intro c r s hi q v
    exact heq c e k r s i hi hn τ q v
  exact congrArg (fun j => j z) ht

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorDegreeExt

/-! ## AssociatorLeftAction（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorLeftAction.lean） -/

/-! # 結合比較の左端のdg作用との整合性 -/

@[expose] public section AssociatorLeftAction

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

lemma associatorLeft_leftAction_element (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (f f' : F)
    {p k r s i m j n : ℤ} (hi : r + s = i) (hm : k + i = m)
    (hj : k + p = j) (hn : m + p = n) (g : GradedHom A f f' p)
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s) :
    SerrePositivity.DifferentialGraded.leftAction A
      ((compose A B E F (compose A B C E P Q) R).leftAt b) g
      (associatorLeftElement A B C E F P Q R b c e f t q v hi hm) hn =
    associatorLeftElement A B C E F P Q R b c e f'
      (SerrePositivity.DifferentialGraded.leftAction A (R.leftAt e) g t hj) q v hi (by omega) :=
  compose_leftAction_element A B E F (compose A B C E P Q) R b e f f'
    hm hj hn g t (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v hi)

lemma associatorRight_leftAction_element (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (f f' : F)
    {p k r s l m j l' n : ℤ} (hl : k + r = l) (hm : l + s = m)
    (hj : k + p = j) (hl' : l + p = l') (hn : m + p = n) (g : GradedHom A f f' p)
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s) :
    SerrePositivity.DifferentialGraded.leftAction A
      ((compose A B C F P (compose A C E F Q R)).leftAt b) g
      (associatorRightElement A B C E F P Q R b c e f t q v hl hm) hn =
    associatorRightElement A B C E F P Q R b c e f' (l := l')
      (SerrePositivity.DifferentialGraded.leftAction A (R.leftAt e) g t hj) q v
      (by omega) (by omega) := by
  have ho := compose_leftAction_element A B C F P (compose A C E F Q R) b c f f'
    hm hl' hn g (BalancedTensor.element A E (R.rightAt f) (Q.leftAt c) e t q hl) v
  have hi := compose_leftAction_element A C E F Q R c e f f' hl hj hl' g t q
  rw [hi] at ho
  exact ho


end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorLeftAction

/-! ## AssociatorLeftMaps（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorLeftMaps.lean） -/

/-! # 反復tensorの左端dg作用の主Homとcochain評価 -/

@[expose] public section AssociatorLeftMaps

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 左括弧の値に固定した全次数の作用cochain。 -/
@[irreducible]
def associatorLeftCochain (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b : B) (f f' : F) (p : ℤ) (g : GradedHom A f f' p) :
    Cochain ((compose A B E F (compose A B C E P Q) R).value b f)
      ((compose A B E F (compose A B C E P Q) R).value b f') p :=
  (compose A B E F (compose A B C E P Q) R).leftCochain g b

/-- 右括弧の値に固定した全次数の作用cochain。 -/
@[irreducible]
def associatorRightCochain (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b : B) (f f' : F) (p : ℤ) (g : GradedHom A f f' p) :
    Cochain ((compose A B C F P (compose A C E F Q R)).value b f)
      ((compose A B C F P (compose A C E F Q R)).value b f') p :=
  (compose A B C F P (compose A C E F Q R)).leftCochain g b

lemma associatorLeftCochain_apply (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f f' : F) {p m n : ℤ} (g : GradedHom A f f' p)
    (v : ((compose A B E F (compose A B C E P Q) R).value b f).X m) (hn : m + p = n) :
    (associatorLeftCochain A B C E F P Q R b f f' p g).v m n hn v =
      SerrePositivity.DifferentialGraded.leftAction A
        ((compose A B E F (compose A B C E P Q) R).leftAt b) g v hn := by
  unfold associatorLeftCochain
  exact Bimodule.leftCochain_apply A B F _ g b v hn

lemma associatorRightCochain_apply (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f f' : F) {p m n : ℤ} (g : GradedHom A f f' p)
    (v : ((compose A B C F P (compose A C E F Q R)).value b f).X m) (hn : m + p = n) :
    (associatorRightCochain A B C E F P Q R b f f' p g).v m n hn v =
      SerrePositivity.DifferentialGraded.leftAction A
        ((compose A B C F P (compose A C E F Q R)).leftAt b) g v hn := by
  unfold associatorRightCochain
  exact Bimodule.leftCochain_apply A B F _ g b v hn

/-- 左括弧の合成のF作用を、その値の主Hom間の射として固定する。 -/
@[irreducible]
def associatorLeftMap (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b : B) (f f' : F) : (f ⟶[Complex A] f') ⟶
    homComplex A ((compose A B E F (compose A B C E P Q) R).value b f)
      ((compose A B E F (compose A B C E P Q) R).value b f') :=
  (compose A B E F (compose A B C E P Q) R).toFunctor.map f f' ≫
    moduleHomπ A B ((compose A B E F (compose A B C E P Q) R).rightAt f)
      ((compose A B E F (compose A B C E P Q) R).rightAt f') b

/-- 右括弧の合成のF作用を、その値の主Hom間の射として固定する。 -/
@[irreducible]
def associatorRightMap (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b : B) (f f' : F) : (f ⟶[Complex A] f') ⟶
    homComplex A ((compose A B C F P (compose A C E F Q R)).value b f)
      ((compose A B C F P (compose A C E F Q R)).value b f') :=
  (compose A B C F P (compose A C E F Q R)).toFunctor.map f f' ≫
    moduleHomπ A B ((compose A B C F P (compose A C E F Q R)).rightAt f)
      ((compose A B C F P (compose A C E F Q R)).rightAt f') b

lemma associatorLeftMap_apply (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f f' : F) (p : ℤ) (g : GradedHom A f f' p) :
    (associatorLeftMap A B C E F P Q R b f f').f p g =
      associatorLeftCochain A B C E F P Q R b f f' p g := by
  unfold associatorLeftMap associatorLeftCochain
  rfl

lemma associatorRightMap_apply (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f f' : F) (p : ℤ) (g : GradedHom A f f' p) :
    (associatorRightMap A B C E F P Q R b f f').f p g =
      associatorRightCochain A B C E F P Q R b f f' p g := by
  unfold associatorRightMap associatorRightCochain
  rfl


end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorLeftMaps

/-! ## AssociatorRightAction（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorRightAction.lean） -/

/-! # 両括弧付けの右B作用と三重生成元の符号 -/

@[expose] public section AssociatorRightAction

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 左括弧の右B作用はR/Qの次数の和とのKoszul符号を伴う。 -/
lemma associatorLeft_rightAction_element (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b b' : Bᵒᵖ) (c : C) (e : E) (f : F)
    {p k r s i j i' m n : ℤ} (hi : r + s = i) (hm : k + i = m)
    (hj : s + p = j) (hi' : i + p = i') (hn : m + p = n) (g : GradedHom A b b' p)
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b.unop c).X s) :
    moduleAction A ((compose A B E F (compose A B C E P Q) R).rightAt f) g
      (associatorLeftElement A B C E F P Q R b.unop c e f t q v hi hm) hn =
    (p * (k + r)).negOnePow •
      associatorLeftElement A B C E F P Q R b'.unop c e f (i := i') (n := n) t q
        (moduleAction A (P.rightAt c) g v hj) (by omega) (by omega) := by
  have ho := compose_rightAction_element A B E F (compose A B C E P Q) R b b' e f
    hm hi' hn g t (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b.unop) c q v hi)
  have hi₀ := compose_rightAction_element A B C E P Q b b' c e hi hj hi' g q v
  rw [hi₀, BalancedTensor.element_units_smul_right, smul_smul, ← Int.negOnePow_add] at ho
  have hs : p * k + p * r = p * (k + r) := by ring
  rw [hs] at ho
  exact ho

/-- 右括弧の右B作用では内側coend全体の次数が同じ符号を与える。 -/
lemma associatorRight_rightAction_element (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b b' : Bᵒᵖ) (c : C) (e : E) (f : F)
    {p k r s l j m n : ℤ} (hl : k + r = l) (hm : l + s = m)
    (hj : s + p = j) (hn : m + p = n) (g : GradedHom A b b' p)
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b.unop c).X s) :
    moduleAction A ((compose A B C F P (compose A C E F Q R)).rightAt f) g
      (associatorRightElement A B C E F P Q R b.unop c e f t q v hl hm) hn =
    (p * l).negOnePow •
      associatorRightElement A B C E F P Q R b'.unop c e f (l := l) (n := n) t q
        (moduleAction A (P.rightAt c) g v hj) hl (by omega) :=
  compose_rightAction_element A B C F P (compose A C E F Q R) b b' c f hm hj hn g
    (BalancedTensor.element A E (R.rightAt f) (Q.leftAt c) e t q hl) v

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorRightAction

/-! ## AssociatorRightMaps（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorRightMaps.lean） -/

/-! # 反復tensorの右B作用の主Homとcochain評価 -/

@[expose] public section AssociatorRightMaps

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

@[irreducible]
def associatorLeftBMap (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b b' : Bᵒᵖ) (f : F) : (b ⟶[Complex A] b') ⟶
    homComplex A ((compose A B E F (compose A B C E P Q) R).value b.unop f)
      ((compose A B E F (compose A B C E P Q) R).value b'.unop f) :=
  ((compose A B E F (compose A B C E P Q) R).rightAt f).map b b'

@[irreducible]
def associatorRightBMap (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b b' : Bᵒᵖ) (f : F) : (b ⟶[Complex A] b') ⟶
    homComplex A ((compose A B C F P (compose A C E F Q R)).value b.unop f)
      ((compose A B C F P (compose A C E F Q R)).value b'.unop f) :=
  ((compose A B C F P (compose A C E F Q R)).rightAt f).map b b'

@[irreducible]
def associatorLeftBCochain (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b b' : Bᵒᵖ) (f : F) (p : ℤ) (g : GradedHom A b b' p) :
    Cochain ((compose A B E F (compose A B C E P Q) R).value b.unop f)
      ((compose A B E F (compose A B C E P Q) R).value b'.unop f) p :=
  (((compose A B E F (compose A B C E P Q) R).rightAt f).map b b').f p g

@[irreducible]
def associatorRightBCochain (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b b' : Bᵒᵖ) (f : F) (p : ℤ) (g : GradedHom A b b' p) :
    Cochain ((compose A B C F P (compose A C E F Q R)).value b.unop f)
      ((compose A B C F P (compose A C E F Q R)).value b'.unop f) p :=
  (((compose A B C F P (compose A C E F Q R)).rightAt f).map b b').f p g

lemma associatorLeftBMap_apply (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b b' : Bᵒᵖ) (f : F) (p : ℤ) (g : GradedHom A b b' p) :
    (associatorLeftBMap A B C E F P Q R b b' f).f p g =
      associatorLeftBCochain A B C E F P Q R b b' f p g := by
  unfold associatorLeftBMap associatorLeftBCochain
  rfl

lemma associatorRightBMap_apply (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b b' : Bᵒᵖ) (f : F) (p : ℤ) (g : GradedHom A b b' p) :
    (associatorRightBMap A B C E F P Q R b b' f).f p g =
      associatorRightBCochain A B C E F P Q R b b' f p g := by
  unfold associatorRightBMap associatorRightBCochain
  rfl

lemma associatorLeftBCochain_apply (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b b' : Bᵒᵖ) (f : F) {p m n : ℤ} (g : GradedHom A b b' p)
    (x : ((compose A B E F (compose A B C E P Q) R).value b.unop f).X m) (hn : m + p = n) :
    (associatorLeftBCochain A B C E F P Q R b b' f p g).v m n hn x =
      moduleAction A ((compose A B E F (compose A B C E P Q) R).rightAt f) g x hn := by
  unfold associatorLeftBCochain
  rfl

lemma associatorRightBCochain_apply (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b b' : Bᵒᵖ) (f : F) {p m n : ℤ} (g : GradedHom A b b' p)
    (x : ((compose A B C F P (compose A C E F Q R)).value b.unop f).X m) (hn : m + p = n) :
    (associatorRightBCochain A B C E F P Q R b b' f p g).v m n hn x =
      moduleAction A ((compose A B C F P (compose A C E F Q R)).rightAt f) g x hn := by
  unfold associatorRightBCochain
  rfl


end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorRightMaps

/-! ## AssociatorParameterExt（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorParameterExt.lean） -/

/-! # 三重生成元によるパラメータ付きHomの自然性の判定 -/

@[expose] public section AssociatorParameterExt

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

lemma associatorLeft_homMap_post_pre_eq (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f : F) {K U V T : Complex A}
    (a : K ⟶ homComplex A ((compose A B E F (compose A B C E P Q) R).value b f) U)
    (d : K ⟶ homComplex A V T) (h : U ⟶ T)
    (g : (compose A B E F (compose A B C E P Q) R).value b f ⟶ V)
    (heq : ∀ (p : ℤ) (x : K.X p) (c : C) (e : E) (k r s i m n : ℤ)
      (hi : r + s = i) (hm : k + i = m) (hn : m + p = n)
      (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s),
      h.f n (((a.f p x).v m n hn)
        (associatorLeftElement A B C E F P Q R b c e f t q v hi hm)) =
      (d.f p x).v m n hn
        (g.f m (associatorLeftElement A B C E F P Q R b c e f t q v hi hm))) :
    a ≫ homPostcompose _ h = d ≫ homPrecompose g T := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (homPostcompose _ h).f p (a.f p x) = (homPrecompose g _).f p (d.f p x)
  rw [homPostcompose_apply, homPrecompose_apply]
  apply associatorLeft_cochain_element_ext A B C E F P Q R b f
  intro c e k r s i m n hi hm hn t q v
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Cochain.ofHom_v]
  exact heq p x c e k r s i m n hi hm hn t q v

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorParameterExt

/-! ## AssociatorCochainAction（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorCochainAction.lean） -/

/-! # 左端作用cochainの三重生成元上の計算

実際のHom写像の評価と既存の作用計算を、結合同型との比較から独立に検証する。
-/

@[expose] public section AssociatorCochainAction

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 左括弧のF作用cochainは三重生成元のR成分に作用する。 -/
lemma associatorLeftCochain_element (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (f f' : F)
    {p k r s i m j n : ℤ} (hi : r + s = i) (hm : k + i = m)
    (hj : k + p = j) (hn : m + p = n) (g : GradedHom A f f' p)
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s) :
    (associatorLeftCochain A B C E F P Q R b f f' p g).v m n hn
      (associatorLeftElement A B C E F P Q R b c e f t q v hi hm) =
    associatorLeftElement A B C E F P Q R b c e f'
      (SerrePositivity.DifferentialGraded.leftAction A (R.leftAt e) g t hj)
      q v hi (by omega) :=
  (associatorLeftCochain_apply A B C E F P Q R b f f' g _ hn).trans
    (associatorLeft_leftAction_element A B C E F P Q R b c e f f' hi hm hj hn g t q v)

/-- 右括弧のF作用cochainも三重生成元のR成分に作用する。 -/
lemma associatorRightCochain_element (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (f f' : F)
    {p k r s l m j l' n : ℤ} (hl : k + r = l) (hm : l + s = m)
    (hj : k + p = j) (hl' : l + p = l') (hn : m + p = n) (g : GradedHom A f f' p)
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s) :
    (associatorRightCochain A B C E F P Q R b f f' p g).v m n hn
      (associatorRightElement A B C E F P Q R b c e f t q v hl hm) =
    associatorRightElement A B C E F P Q R b c e f' (l := l')
      (SerrePositivity.DifferentialGraded.leftAction A (R.leftAt e) g t hj)
      q v (by omega) (by omega) :=
  (associatorRightCochain_apply A B C E F P Q R b f f' g _ hn).trans
    (associatorRight_leftAction_element A B C E F P Q R b c e f f' hl hm hj hl' hn g t q v)

/-- 左括弧の右B作用cochainはR/Qの次数の和とのKoszul符号を持つ。 -/
lemma associatorLeftBCochain_element (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b b' : Bᵒᵖ) (c : C) (e : E) (f : F)
    {p k r s i j i' m n : ℤ} (hi : r + s = i) (hm : k + i = m)
    (hj : s + p = j) (hi' : i + p = i') (hn : m + p = n) (g : GradedHom A b b' p)
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b.unop c).X s) :
    (associatorLeftBCochain A B C E F P Q R b b' f p g).v m n hn
      (associatorLeftElement A B C E F P Q R b.unop c e f t q v hi hm) =
    (p * (k + r)).negOnePow •
      associatorLeftElement A B C E F P Q R b'.unop c e f (i := i') (n := n) t q
        (moduleAction A (P.rightAt c) g v hj) (by omega) (by omega) :=
  (associatorLeftBCochain_apply A B C E F P Q R b b' f g _ hn).trans
    (associatorLeft_rightAction_element A B C E F P Q R b b' c e f hi hm hj hi' hn g t q v)

/-- 右括弧の右B作用cochainは内側coend全体の次数とのKoszul符号を持つ。 -/
lemma associatorRightBCochain_element (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b b' : Bᵒᵖ) (c : C) (e : E) (f : F)
    {p k r s l j m n : ℤ} (hl : k + r = l) (hm : l + s = m)
    (hj : s + p = j) (hn : m + p = n) (g : GradedHom A b b' p)
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b.unop c).X s) :
    (associatorRightBCochain A B C E F P Q R b b' f p g).v m n hn
      (associatorRightElement A B C E F P Q R b.unop c e f t q v hl hm) =
    (p * l).negOnePow •
      associatorRightElement A B C E F P Q R b'.unop c e f (l := l) (n := n) t q
        (moduleAction A (P.rightAt c) g v hj) hl (by omega) :=
  (associatorRightBCochain_apply A B C E F P Q R b b' f g _ hn).trans
    (associatorRight_rightAction_element A B C E F P Q R b b' c e f hl hm hj hn g t q v)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorCochainAction

/-! ## AssociatorActionDegree（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorActionDegree.lean） -/

/-! # 左作用を適用した三重生成元の結合比較 -/

@[expose] public section AssociatorActionDegree

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 左作用後の生成元を結合同型で送る。 -/
lemma associatorValueIso_hom_actionElement_of_degree (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (f f' : F) {p k r s i j l n : ℤ}
    (hi : r + s = i) (hj : k + p = j) (hl : j + r = l) (hn : j + i = n) (g : GradedHom A f f' p)
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s) :
    (associatorValueIso A B C E F P Q R b f').hom.f n
      (associatorLeftElement A B C E F P Q R b c e f' (n := n)
        (Bimodule.leftActionElement A R g e t hj)
        q v hi hn) =
    associatorRightElement A B C E F P Q R b c e f' (l := l) (n := n)
      (Bimodule.leftActionElement A R g e t hj)
      q v hl (by omega) :=
  associatorValueIso_hom_element A B C E F P Q R b c e f'
    (k := j) (r := r) (s := s) (i := i) (l := l) (n := n)
    (Bimodule.leftActionElement A R (n := j) g e t hj)
    q v hi hl hn

/-- 左作用後の生成元を結合同型で送る。 -/
lemma associatorValueIso_hom_leftActed_of_degree (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (f f' : F) {p k r s i j l n : ℤ}
    (hi : r + s = i) (hj : k + p = j) (hl : j + r = l) (hn : j + i = n) (g : GradedHom A f f' p)
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s) :
    (associatorValueIso A B C E F P Q R b f').hom.f n
      (associatorLeftElement A B C E F P Q R b c e f' (n := n)
        (SerrePositivity.DifferentialGraded.leftAction A (R.leftAt e) g t hj)
        q v hi hn) =
    associatorRightElement A B C E F P Q R b c e f' (l := l) (n := n)
      (SerrePositivity.DifferentialGraded.leftAction A (R.leftAt e) g t hj)
      q v hl (by omega) :=
  associatorValueIso_hom_element A B C E F P Q R b c e f'
    (k := j) (r := r) (s := s) (i := i) (l := l) (n := n)
    (SerrePositivity.DifferentialGraded.leftAction A (R.leftAt e) (n := j) g t hj)
    q v hi hl hn

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorActionDegree

/-! ## AssociatorComponent（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorComponent.lean） -/

/-! # 結合比較と左作用の二段の生成元輸送 -/

@[expose] public section AssociatorComponent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 結合同型の成分を、両括弧の値を型に固定した関数として読む。 -/
@[irreducible]
def associatorValueComponent (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f : F) (n : ℤ) :
    ((compose A B E F (compose A B C E P Q) R).value b f).X n →
      ((compose A B C F P (compose A C E F Q R)).value b f).X n :=
  fun z => (associatorValueIso A B C E F P Q R b f).hom.f n z

lemma associatorValueComponent_eq (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f : F) (n : ℤ)
    (z : ((compose A B E F (compose A B C E P Q) R).value b f).X n) :
    associatorValueComponent A B C E F P Q R b f n z =
      (associatorValueIso A B C E F P Q R b f).hom.f n z := by
  unfold associatorValueComponent
  rfl

lemma associatorValueComponent_element (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (f : F) {k r s i l n : ℤ}
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    associatorValueComponent A B C E F P Q R b f n
      (associatorLeftElement A B C E F P Q R b c e f t q v hi hn) =
    associatorRightElement A B C E F P Q R b c e f t q v hl (by omega) :=
  (associatorValueComponent_eq A B C E F P Q R b f n _).trans
    (associatorValueIso_hom_element A B C E F P Q R b c e f t q v hi hl hn)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorComponent

/-! ## AssociatorValueHom（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorValueHom.lean） -/

/-! # 結合比較と左作用の二段の生成元輸送 -/

@[expose] public section AssociatorValueHom

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 固定した成分関数を使って結合比較のchain mapを表示する。 -/
def associatorValueHom (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f : F) :
    (compose A B E F (compose A B C E P Q) R).value b f ⟶
      (compose A B C F P (compose A C E F Q R)).value b f :=
  chainMapOfComponentFunctions (associatorValueIso A B C E F P Q R b f).hom
    (associatorValueComponent A B C E F P Q R b f)
    (associatorValueComponent_eq A B C E F P Q R b f)

@[simp]
lemma associatorValueHom_apply (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f : F) (n : ℤ)
    (z : ((compose A B E F (compose A B C E P Q) R).value b f).X n) :
    (associatorValueHom A B C E F P Q R b f).f n z =
      associatorValueComponent A B C E F P Q R b f n z := rfl

lemma associatorValueHom_eq (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f : F) :
    associatorValueHom A B C E F P Q R b f =
      (associatorValueIso A B C E F P Q R b f).hom :=
  chainMapOfComponentFunctions_eq _ _ _

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorValueHom

/-! ## AssociatorLeftActionMap（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorLeftActionMap.lean） -/

/-! # 結合比較と左作用の二段の生成元輸送 -/

@[expose] public section AssociatorLeftActionMap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 左作用の生成元公式を任意の値写像の後で使う。 -/
lemma associatorLeftCochain_element_map (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (f f' : F)
    {p k r s i j m n : ℤ} (hi : r + s = i) (hm : k + i = m)
    (hj : k + p = j) (hn : m + p = n) (g : GradedHom A f f' p)
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s)
    {Z : Type u}
    (a : ((compose A B E F (compose A B C E P Q) R).value b f').X n → Z) :
    a ((associatorLeftCochain A B C E F P Q R b f f' p g).v m n hn
      (associatorLeftElement A B C E F P Q R b c e f t q v hi hm)) =
    a (associatorLeftElement A B C E F P Q R b c e f'
      (SerrePositivity.DifferentialGraded.leftAction A (R.leftAt e) g t hj)
      q v hi (by omega)) :=
  congrArg a (associatorLeftCochain_element A B C E F P Q R b c e f f'
    (p := p) (k := k) (r := r) (s := s) (i := i) (j := j) (m := m) (n := n)
    hi hm hj hn g t q v)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorLeftActionMap

/-! ## AssociatorRightTransport（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorRightTransport.lean） -/

/-! # 結合比較と左作用の二段の生成元輸送 -/

@[expose] public section AssociatorRightTransport

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 結合同型の後に左作用を適用した生成元の評価。 -/
lemma associatorRightCochain_transport (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (f f' : F) {p k r s i m n : ℤ}
    (hi : r + s = i) (hm : k + i = m) (hn : m + p = n) (g : GradedHom A f f' p)
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s) :
    (associatorRightCochain A B C E F P Q R b f f' p g).v m n hn
      ((associatorValueIso A B C E F P Q R b f).hom.f m
        (associatorLeftElement A B C E F P Q R b c e f (n := m) t q v hi hm)) =
    associatorRightElement A B C E F P Q R b c e f' (l := k + r + p) (n := n)
      (SerrePositivity.DifferentialGraded.leftAction A (R.leftAt e) g t rfl)
      q v (by omega) (by omega) := by
  have hS := associatorValueIso_hom_element A B C E F P Q R b c e f
    (i := i) (l := k + r) (n := m) t q v hi rfl hm
  have hR := associatorRightCochain_element A B C E F P Q R b c e f f'
    (j := k + p) (l' := k + r + p) rfl (by omega) rfl rfl hn g t q v
  exact (congrArg (fun z =>
    (associatorRightCochain A B C E F P Q R b f f' p g).v m n hn z) hS).trans hR

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorRightTransport

/-! ## AssociatorRightComponentCompatibility（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorRightComponentCompatibility.lean） -/

/-! # 結合比較のRight作用の三重生成元上の整合性 -/

@[expose] public section AssociatorRightComponentCompatibility

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 右B作用のKoszul符号は結合比較の両側で一致する。 -/
lemma associatorComponent_rightCochain_compatibility (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b b' : Bᵒᵖ) (c : C) (e : E) (f : F) {p k r s i m n : ℤ}
    (hi : r + s = i) (hm : k + i = m) (hn : m + p = n) (g : GradedHom A b b' p)
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b.unop c).X s) :
    associatorValueComponent A B C E F P Q R b'.unop f n
      ((associatorLeftBCochain A B C E F P Q R b b' f p g).v m n hn
        (associatorLeftElement A B C E F P Q R b.unop c e f (n := m) t q v hi hm)) =
    (associatorRightBCochain A B C E F P Q R b b' f p g).v m n hn
      (associatorValueComponent A B C E F P Q R b.unop f m
        (associatorLeftElement A B C E F P Q R b.unop c e f (n := m) t q v hi hm)) := by
  have hkrm : (k + r) + s = m :=
    (add_assoc k r s).trans ((congrArg (fun z : ℤ => k + z) hi).trans hm)
  have hri : r + (s + p) = i + p :=
    (add_assoc r s p).symm.trans (congrArg (fun z : ℤ => z + p) hi)
  have hki : k + (i + p) = n :=
    (add_assoc k i p).symm.trans ((congrArg (fun z : ℤ => z + p) hm).trans hn)
  have hkrsp : (k + r) + (s + p) = n :=
    (add_assoc (k + r) s p).symm.trans ((congrArg (fun z : ℤ => z + p) hkrm).trans hn)
  let v' := moduleAction A (P.rightAt c) (n := s + p) g v rfl
  let x₀ := associatorLeftElement A B C E F P Q R b.unop c e f (n := m) t q v hi hm
  let x₁ := associatorLeftElement A B C E F P Q R b'.unop c e f (i := i + p) (n := n)
    t q v' hri hki
  let y₀ := associatorRightElement A B C E F P Q R b.unop c e f (l := k + r) (n := m)
    t q v rfl hkrm
  let y₁ := associatorRightElement A B C E F P Q R b'.unop c e f (l := k + r) (n := n)
    t q v' rfl hkrsp
  let σ : ℤˣ := (p * (k + r)).negOnePow
  have hL := associatorLeft_rightAction_element A B C E F P Q R b b' c e f
    (j := s + p) (i' := i + p) hi hm rfl rfl hn g t q v
  have hR := associatorRight_rightAction_element A B C E F P Q R b b' c e f
    (l := k + r) (j := s + p) rfl hkrm rfl hn g t q v
  have hS := associatorValueComponent_element A B C E F P Q R b.unop c e f
    (i := i) (l := k + r) (n := m) t q v hi rfl hm
  have hM := associatorValueComponent_element A B C E F P Q R b'.unop c e f
    (i := i + p) (l := k + r) (n := n) t q v' hri rfl hki
  have hLP := associatorLeftBCochain_apply A B C E F P Q R b b' f g x₀ hn
  have hRP := associatorRightBCochain_apply A B C E F P Q R b b' f g y₀ hn
  have hσ := chain_units_smul (associatorValueHom A B C E F P Q R b'.unop f) n σ x₁
  simp only [associatorValueHom_apply] at hσ
  have hMσ := hσ.trans (congrArg (fun z => σ • z) hM)
  exact element_square
    (fun z => associatorValueComponent A B C E F P Q R b.unop f m z)
    (fun z => associatorValueComponent A B C E F P Q R b'.unop f n z)
    (fun z => (associatorLeftBCochain A B C E F P Q R b b' f p g).v m n hn z)
    (fun z => (associatorRightBCochain A B C E F P Q R b b' f p g).v m n hn z)
    x₀ (σ • x₁) y₀ (σ • y₁) (hLP.trans hL) hS hMσ (hRP.trans hR)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorRightComponentCompatibility

/-! ## AssociatorRightValueHomNaturality（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorRightValueHomNaturality.lean） -/

/-! # 結合比較の右B全Hom自然性と右加群同型 -/

@[expose] public section AssociatorRightValueHomNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 右B作用の主Hom写像についての結合比較の自然性。 -/
lemma associatorValueHom_right_naturality (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b b' : Bᵒᵖ) (f : F) :
    associatorLeftBMap A B C E F P Q R b b' f ≫
      homPostcompose ((compose A B E F (compose A B C E P Q) R).value b.unop f)
        (associatorValueHom A B C E F P Q R b'.unop f) =
    associatorRightBMap A B C E F P Q R b b' f ≫
      homPrecompose (associatorValueHom A B C E F P Q R b.unop f)
        ((compose A B C F P (compose A C E F Q R)).value b'.unop f) := by
  apply hom_naturality_of_apply
  intro p g
  rw [associatorLeftBMap_apply, associatorRightBMap_apply]
  apply associatorLeft_cochain_element_ext A B C E F P Q R b.unop f
  intro c e k r s i m n hi hm hn t q v
  have hL := cochain_comp_ofHom_apply
    (associatorLeftBCochain A B C E F P Q R b b' f p g)
    (associatorValueHom A B C E F P Q R b'.unop f) hn
    (associatorLeftElement A B C E F P Q R b.unop c e f (n := m) t q v hi hm)
  have hR := cochain_ofHom_comp_apply
    (associatorValueHom A B C E F P Q R b.unop f)
    (associatorRightBCochain A B C E F P Q R b b' f p g) hn
    (associatorLeftElement A B C E F P Q R b.unop c e f (n := m) t q v hi hm)
  have hc := associatorComponent_rightCochain_compatibility A B C E F P Q R b b' c e f
    hi hm hn g t q v
  simp only [associatorValueHom_apply] at hL hR
  exact hL.trans (hc.trans hR.symm)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorRightValueHomNaturality

/-! ## AssociatorRightNaturality（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorRightNaturality.lean） -/

/-! # 結合比較の右B全Hom自然性と右加群同型 -/

@[expose] public section AssociatorRightNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 右B作用の主Hom写像についての結合比較の自然性。 -/
lemma associatorValue_right_naturality (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b b' : Bᵒᵖ) (f : F) :
    associatorLeftBMap A B C E F P Q R b b' f ≫
      homPostcompose ((compose A B E F (compose A B C E P Q) R).value b.unop f)
        (associatorValueIso A B C E F P Q R b'.unop f).hom =
    associatorRightBMap A B C E F P Q R b b' f ≫
      homPrecompose (associatorValueIso A B C E F P Q R b.unop f).hom
        ((compose A B C F P (compose A C E F Q R)).value b'.unop f) := by
  simpa only [associatorValueHom_eq] using
    associatorValueHom_right_naturality A B C E F P Q R b b' f

lemma associatorValue_right_naturality_actual (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b b' : Bᵒᵖ) (f : F) :
    ((compose A B E F (compose A B C E P Q) R).rightAt f).map b b' ≫
      homPostcompose ((compose A B E F (compose A B C E P Q) R).value b.unop f)
        (associatorValueIso A B C E F P Q R b'.unop f).hom =
    ((compose A B C F P (compose A C E F Q R)).rightAt f).map b b' ≫
      homPrecompose (associatorValueIso A B C E F P Q R b.unop f).hom
        ((compose A B C F P (compose A C E F Q R)).value b'.unop f) := by
  have h := associatorValue_right_naturality A B C E F P Q R b b' f
  unfold associatorLeftBMap associatorRightBMap at h
  exact h

/-- 固定F対象での結合比較を全dg自然な右B加群同型へ束ねる。 -/
def associatorRightModuleIso (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (f : F) :
    ForgetEnrichment.of (Complex A) ((compose A B E F (compose A B C E P Q) R).rightAt f) ≅
      ForgetEnrichment.of (Complex A) ((compose A B C F P (compose A C E F Q R)).rightAt f) :=
  moduleIsoMk A B
    (M := (compose A B E F (compose A B C E P Q) R).rightAt f)
    (N := (compose A B C F P (compose A C E F Q R)).rightAt f)
    (fun b => associatorValueIso A B C E F P Q R b.unop f)
    (fun b b' => associatorValue_right_naturality_actual A B C E F P Q R b b' f)

@[simp]
lemma associatorRightModuleIso_hom_eval (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f : F) :
    (moduleEvaluation A B b).map
      (X := ForgetEnrichment.of (Complex A)
        ((compose A B E F (compose A B C E P Q) R).rightAt f))
      (Y := ForgetEnrichment.of (Complex A)
        ((compose A B C F P (compose A C E F Q R)).rightAt f))
      (associatorRightModuleIso A B C E F P Q R f).hom =
      (associatorValueIso A B C E F P Q R b f).hom :=
  moduleIsoMk_hom_eval A B
    (M := (compose A B E F (compose A B C E P Q) R).rightAt f)
    (N := (compose A B C F P (compose A C E F Q R)).rightAt f) _ _ b

@[simp]
lemma associatorRightModuleIso_inv_eval (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f : F) :
    (moduleEvaluation A B b).map
      (X := ForgetEnrichment.of (Complex A)
        ((compose A B C F P (compose A C E F Q R)).rightAt f))
      (Y := ForgetEnrichment.of (Complex A)
        ((compose A B E F (compose A B C E P Q) R).rightAt f))
      (associatorRightModuleIso A B C E F P Q R f).inv =
      (associatorValueIso A B C E F P Q R b f).inv :=
  moduleIsoMk_inv_eval A B
    (M := (compose A B E F (compose A B C E P Q) R).rightAt f)
    (N := (compose A B C F P (compose A C E F Q R)).rightAt f) _ _ b

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorRightNaturality

/-! ## AssociatorComponentTransport（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorComponentTransport.lean） -/

/-! # 結合比較と左作用の二段の生成元輸送 -/

@[expose] public section AssociatorComponentTransport

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 左作用後に結合同型を適用した生成元の評価。 -/
lemma associatorLeftComponent_transport (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (f f' : F) {p k r s i j l m n : ℤ}
    (hi : r + s = i) (hm : k + i = m) (hj : k + p = j)
    (hl : j + r = l) (hn : m + p = n) (g : GradedHom A f f' p)
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s) :
    associatorValueComponent A B C E F P Q R b f' n
      ((associatorLeftCochain A B C E F P Q R b f f' p g).v m n hn
        (associatorLeftElement A B C E F P Q R b c e f (n := m) t q v hi hm)) =
    associatorRightElement A B C E F P Q R b c e f' (l := l) (n := n)
      (SerrePositivity.DifferentialGraded.leftAction A (R.leftAt e) g t hj)
      q v hl (by omega) := by
  exact (associatorLeftCochain_element_map A B C E F P Q R b c e f f'
    hi hm hj hn g t q v
    (fun z => associatorValueComponent A B C E F P Q R b f' n z)).trans
    (associatorValueComponent_element A B C E F P Q R b c e f'
      (k := j) (r := r) (s := s) (i := i) (l := l) (n := n)
      (SerrePositivity.DifferentialGraded.leftAction A (R.leftAt e) (n := j) g t hj)
      q v hi hl (by omega))

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorComponentTransport

/-! ## AssociatorComponentCompatibility（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorComponentCompatibility.lean） -/

/-! # 結合比較のLeft作用の三重生成元上の整合性 -/

@[expose] public section AssociatorComponentCompatibility

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 左F作用と結合比較の三重生成元上での可換式。 -/
lemma associatorComponent_leftCochain_compatibility (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (f f' : F) {p k r s i m n : ℤ}
    (hi : r + s = i) (hm : k + i = m) (hn : m + p = n) (g : GradedHom A f f' p)
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s) :
    associatorValueComponent A B C E F P Q R b f' n
      ((associatorLeftCochain A B C E F P Q R b f f' p g).v m n hn
        (associatorLeftElement A B C E F P Q R b c e f (n := m) t q v hi hm)) =
    (associatorRightCochain A B C E F P Q R b f f' p g).v m n hn
      (associatorValueComponent A B C E F P Q R b f m
        (associatorLeftElement A B C E F P Q R b c e f (n := m) t q v hi hm)) := by
  have hkrm : (k + r) + s = m := by omega
  have hS := associatorValueComponent_element A B C E F P Q R b c e f
    (i := i) (l := k + r) (n := m) t q v hi rfl hm
  have hR := associatorRightCochain_element A B C E F P Q R b c e f f'
    (j := k + p) (l' := k + r + p) rfl hkrm rfl rfl hn g t q v
  have hL := associatorLeftComponent_transport A B C E F P Q R b c e f f'
    (j := k + p) (l := k + r + p) hi hm rfl (by omega) hn g t q v
  exact hL.trans ((congrArg (fun z =>
    (associatorRightCochain A B C E F P Q R b f f' p g).v m n hn z) hS).trans hR).symm

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorComponentCompatibility

/-! ## AssociatorValueHomNaturality（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorValueHomNaturality.lean） -/

/-! # 結合比較の左端のdg作用との整合性 -/

@[expose] public section AssociatorValueHomNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 左F作用と結合比較の三重生成元上での可換式。 -/
lemma associatorValueHom_leftAction_compatibility (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (f f' : F) {p k r s i m n : ℤ}
    (hi : r + s = i) (hm : k + i = m) (hn : m + p = n) (g : GradedHom A f f' p)
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s) :
    (associatorValueHom A B C E F P Q R b f').f n
      (SerrePositivity.DifferentialGraded.leftAction A
        ((compose A B E F (compose A B C E P Q) R).leftAt b) g
        (associatorLeftElement A B C E F P Q R b c e f (n := m) t q v hi hm) hn) =
    SerrePositivity.DifferentialGraded.leftAction A
      ((compose A B C F P (compose A C E F Q R)).leftAt b) g
      ((associatorValueHom A B C E F P Q R b f).f m
        (associatorLeftElement A B C E F P Q R b c e f (n := m) t q v hi hm)) hn := by
  have hLC := associatorLeftCochain_apply A B C E F P Q R b f f' g
    (associatorLeftElement A B C E F P Q R b c e f (n := m) t q v hi hm) hn
  have hRC := associatorRightCochain_apply A B C E F P Q R b f f' g
    ((associatorValueHom A B C E F P Q R b f).f m
      (associatorLeftElement A B C E F P Q R b c e f (n := m) t q v hi hm)) hn
  have hc := associatorComponent_leftCochain_compatibility A B C E F P Q R b c e f f'
    hi hm hn g t q v
  simp only [associatorValueHom_apply] at hLC hRC ⊢
  exact (congrArg (fun z =>
    associatorValueComponent A B C E F P Q R b f' n z) hLC.symm).trans (hc.trans hRC)

/-- 結合比較は左F作用の主Hom写像と全次数で可換。 -/
lemma associatorValueHom_left_naturality (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f f' : F) :
    associatorLeftMap A B C E F P Q R b f f' ≫
      homPostcompose ((compose A B E F (compose A B C E P Q) R).value b f)
        (associatorValueHom A B C E F P Q R b f') =
    associatorRightMap A B C E F P Q R b f f' ≫
      homPrecompose (associatorValueHom A B C E F P Q R b f)
        ((compose A B C F P (compose A C E F Q R)).value b f') := by
  apply hom_naturality_of_apply
  intro p g
  rw [associatorLeftMap_apply, associatorRightMap_apply]
  apply associatorLeft_cochain_element_ext A B C E F P Q R b f
  intro c e k r s i m n hi hm hn t q v
  have hL := cochain_comp_ofHom_apply
    (associatorLeftCochain A B C E F P Q R b f f' p g)
    (associatorValueHom A B C E F P Q R b f') hn
    (associatorLeftElement A B C E F P Q R b c e f (n := m) t q v hi hm)
  have hR := cochain_ofHom_comp_apply
    (associatorValueHom A B C E F P Q R b f)
    (associatorRightCochain A B C E F P Q R b f f' p g) hn
    (associatorLeftElement A B C E F P Q R b c e f (n := m) t q v hi hm)
  have hc := associatorComponent_leftCochain_compatibility A B C E F P Q R b c e f f'
    hi hm hn g t q v
  simp only [associatorValueHom_apply] at hL hR
  exact hL.trans (hc.trans hR.symm)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorValueHomNaturality

/-! ## AssociatorLeftNaturality（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorLeftNaturality.lean） -/

/-! # 結合比較の左端のdg作用との整合性 -/

@[expose] public section AssociatorLeftNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 結合比較は左F作用の主Hom写像と全次数で可換。 -/
lemma associatorValue_left_naturality (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f f' : F) :
    associatorLeftMap A B C E F P Q R b f f' ≫
      homPostcompose ((compose A B E F (compose A B C E P Q) R).value b f)
        (associatorValueIso A B C E F P Q R b f').hom =
    associatorRightMap A B C E F P Q R b f f' ≫
      homPrecompose (associatorValueIso A B C E F P Q R b f).hom
        ((compose A B C F P (compose A C E F Q R)).value b f') := by
  simpa only [associatorValueHom_eq] using
    associatorValueHom_left_naturality A B C E F P Q R b f f'

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorLeftNaturality

/-! ## AssociatorBimodule（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorBimodule.lean） -/

/-! # 結合比較の右加群同型と左作用の全Hom自然性 -/

@[expose] public section AssociatorBimodule

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

@[simp]
lemma associatorRightModuleIso_hom_component (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f : F) :
    moduleMorphismComponent A B
      ((compose A B E F (compose A B C E P Q) R).rightAt f)
      ((compose A B C F P (compose A C E F Q R)).rightAt f)
      (associatorRightModuleIso A B C E F P Q R f).hom b =
      (associatorValueIso A B C E F P Q R b f).hom :=
  associatorRightModuleIso_hom_eval A B C E F P Q R b f

/-- 左F作用に関する自然性は値のHomだけでなく右B加群の主Hom endで成り立つ。 -/
lemma associatorRightModuleIso_naturality (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (f f' : F) :
    (compose A B E F (compose A B C E P Q) R).toFunctor.map f f' ≫
      moduleHomPostcompose A B
        ((compose A B E F (compose A B C E P Q) R).rightAt f)
        ((compose A B E F (compose A B C E P Q) R).rightAt f')
        ((compose A B C F P (compose A C E F Q R)).rightAt f')
        (associatorRightModuleIso A B C E F P Q R f').hom =
    (compose A B C F P (compose A C E F Q R)).toFunctor.map f f' ≫
      moduleHomPrecompose A B
        ((compose A B E F (compose A B C E P Q) R).rightAt f)
        ((compose A B C F P (compose A C E F Q R)).rightAt f)
        ((compose A B C F P (compose A C E F Q R)).rightAt f')
        (associatorRightModuleIso A B C E F P Q R f).hom := by
  apply moduleHom_ext
  intro b
  simp only [Category.assoc]
  rw [moduleHomPostcompose_π, moduleHomPrecompose_π]
  simp only [associatorRightModuleIso_hom_component]
  have h := associatorValue_left_naturality A B C E F P Q R b f f'
  unfold associatorLeftMap associatorRightMap at h
  exact h

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorBimodule

/-! ## AssociatorTransforms（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorTransforms.lean） -/

/-! # 結合比較の右加群同型と左作用の全Hom自然性 -/

@[expose] public section AssociatorTransforms

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]


/-- 結合比較の全Homに関して豊穣自然な単位パラメータ変換。 -/
def associatorHom (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) :
    BimoduleParamTrans A B F (𝟙_ (Complex A))
      (compose A B E F (compose A B C E P Q) R) (compose A B C F P (compose A C E F Q R)) :=
  Bimodule.isoFamilyHom A B F (associatorRightModuleIso A B C E F P Q R)
    (associatorRightModuleIso_naturality A B C E F P Q R)

@[simp]
lemma associatorHom_app (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (f : F) :
    (associatorHom A B C E F P Q R).app f =
      ForgetEnrichment.homTo (Complex A) (associatorRightModuleIso A B C E F P Q R f).hom := rfl

/-- 結合比較の全Homに関して豊穣自然な単位パラメータ変換。 -/
def associatorInv (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) :
    BimoduleParamTrans A B F (𝟙_ (Complex A))
      (compose A B C F P (compose A C E F Q R)) (compose A B E F (compose A B C E P Q) R) :=
  Bimodule.isoFamilyInv A B F (associatorRightModuleIso A B C E F P Q R)
    (associatorRightModuleIso_naturality A B C E F P Q R)

@[simp]
lemma associatorInv_app (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (f : F) :
    (associatorInv A B C E F P Q R).app f =
      ForgetEnrichment.homTo (Complex A) (associatorRightModuleIso A B C E F P Q R f).inv := rfl

/-- 結合比較の順逆の合成は全Hom endの閉単位元。 -/
lemma associator_hom_inv_app (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (f : F) :
    (λ_ (𝟙_ (Complex A))).inv ≫
      ((associatorHom A B C E F P Q R).app f ⊗ₘ
        (associatorInv A B C E F P Q R).app f) ≫
      eComp (Complex A) ((compose A B E F (compose A B C E P Q) R).rightAt f)
        ((compose A B C F P (compose A C E F Q R)).rightAt f)
        ((compose A B E F (compose A B C E P Q) R).rightAt f) =
      eId (Complex A) ((compose A B E F (compose A B C E P Q) R).rightAt f) :=
  Bimodule.isoFamily_hom_inv_app A B F (associatorRightModuleIso A B C E F P Q R)
    (associatorRightModuleIso_naturality A B C E F P Q R) f

/-- 結合比較の順逆の合成は全Hom endの閉単位元。 -/
lemma associator_inv_hom_app (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (f : F) :
    (λ_ (𝟙_ (Complex A))).inv ≫
      ((associatorInv A B C E F P Q R).app f ⊗ₘ
        (associatorHom A B C E F P Q R).app f) ≫
      eComp (Complex A) ((compose A B C F P (compose A C E F Q R)).rightAt f)
        ((compose A B E F (compose A B C E P Q) R).rightAt f)
        ((compose A B C F P (compose A C E F Q R)).rightAt f) =
      eId (Complex A) ((compose A B C F P (compose A C E F Q R)).rightAt f) :=
  Bimodule.isoFamily_inv_hom_app A B F (associatorRightModuleIso A B C E F P Q R)
    (associatorRightModuleIso_naturality A B C E F P Q R) f

/-- 主Hom endを評価すると元の結合同型の閉成分に戻る。 -/
lemma associatorHom_π (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f : F) :
    (associatorHom A B C E F P Q R).app f ≫
      moduleHomπ A B ((compose A B E F (compose A B C E P Q) R).rightAt f)
        ((compose A B C F P (compose A C E F Q R)).rightAt f) b =
      closedMap A (associatorValueIso A B C E F P Q R b f).hom := by
  exact (moduleEvaluation_closedMap A B b
    (associatorRightModuleIso A B C E F P Q R f).hom).symm.trans
      (congrArg (fun k : (compose A B E F (compose A B C E P Q) R).value b f ⟶
          (compose A B C F P (compose A C E F Q R)).value b f => closedMap A k)
        (associatorRightModuleIso_hom_eval A B C E F P Q R b f))

/-- 主Hom endを評価すると元の結合同型の閉成分に戻る。 -/
lemma associatorInv_π (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f : F) :
    (associatorInv A B C E F P Q R).app f ≫
      moduleHomπ A B ((compose A B C F P (compose A C E F Q R)).rightAt f)
        ((compose A B E F (compose A B C E P Q) R).rightAt f) b =
      closedMap A (associatorValueIso A B C E F P Q R b f).inv := by
  exact (moduleEvaluation_closedMap A B b
    (associatorRightModuleIso A B C E F P Q R f).inv).symm.trans
      (congrArg (fun k : (compose A B C F P (compose A C E F Q R)).value b f ⟶
          (compose A B E F (compose A B C E P Q) R).value b f => closedMap A k)
        (associatorRightModuleIso_inv_eval A B C E F P Q R b f))

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorTransforms

/-! ## AssociatorIso（旧 SerrePositivity/DifferentialGraded/Tensor/AssociatorIso.lean） -/

/-! # 全Hom自然な閉零bimodule圏での結合同型 -/

@[expose] public section AssociatorIso

noncomputable section
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 全Hom自然な閉零射の圏におけるbimodule合成の結合同型。 -/
def associatorIso (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F) :
    BimoduleCategory.of A B F (compose A B E F (compose A B C E P Q) R) ≅
      BimoduleCategory.of A B F (compose A B C F P (compose A C E F Q R)) :=
  BimoduleCategory.isoOfFamily A B F (associatorRightModuleIso A B C E F P Q R)
    (associatorRightModuleIso_naturality A B C E F P Q R)

@[simp]
lemma associatorIso_hom_eval (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (f : F) :
    (BimoduleCategory.evaluation A B F f).map (associatorIso A B C E F P Q R).hom =
      (associatorRightModuleIso A B C E F P Q R f).hom := rfl

@[simp]
lemma associatorIso_inv_eval (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (f : F) :
    (BimoduleCategory.evaluation A B F f).map (associatorIso A B C E F P Q R).inv =
      (associatorRightModuleIso A B C E F P Q R f).inv := rfl

lemma associatorIso_hom_trans (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) :
    (BimoduleCategory.homEquiv A B F _ _ (associatorIso A B C E F P Q R).hom) =
      associatorHom A B C E F P Q R := rfl

lemma associatorIso_inv_trans (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) :
    (BimoduleCategory.homEquiv A B F _ _ (associatorIso A B C E F P Q R).inv) =
      associatorInv A B C E F P Q R := rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorIso
