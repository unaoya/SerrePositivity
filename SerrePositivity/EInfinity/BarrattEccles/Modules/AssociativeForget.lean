module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.StandardCoefficient
public import SerrePositivity.HomologicalAlgebra.Complexes.HomologyZero.TernaryInput
public import SerrePositivity.HomologicalAlgebra.Complexes.HomologyZero.NullaryInput
public import Mathlib.CategoryTheory.Monoidal.Mon
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CommutativeBinaryCriterion

/-!
# Barratt–Eccles 代数の結合的 dg 代数への忘却

概要：Berger–Fresse §1.1.3 の標準零単体の操作で同じ台に厳密な単位と積を入れる。
方針：零入力と二入力の部分合成を代数公理へ入力し、三つのモノイド公理を得る。
規約：可換性は要求せず、任意の可換係数環上の非有界複体を使う。
使われ方：HA §4.2 の加群模型を既存の dg 代数上の右加群へ接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable {A : Type u} [CommRing A]
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] TensorPowers.power

/-- 概要：標準零単体による n 入力作用（Berger–Fresse §1.1.3）。
方針：指定係数を作用へ入力する。規約：零入力も含む。
使われ方：結合的忘却の演算。 -/
def standardOperation (X : (operad A).Algebra) (n : ℕ) :
    power X.carrier n ⟶ X.carrier := coefficientOperation X n (standardCoefficient A n)

/-- 概要：標準二入力作用による積（Berger–Fresse §1.1.3）。
方針：二乗冪の末尾の単位因子を挿入する。規約：元の carrier の二入力射。
使われ方：結合的 dg 代数の積。 -/
def standardBinary (X : (operad A).Algebra) : X.carrier ⊗ X.carrier ⟶ X.carrier :=
  (X.carrier ◁ (oneIso X.carrier).inv) ≫ standardOperation X 2

/-- 概要：標準一入力作用は恒等演算（Berger–Fresse §1.1.3）。
方針：標準係数の単位との一致と代数の単位則。
規約：一乗冪の構造同型を保つ。使われ方：モノイドの単位則。 -/
lemma standardOperation_one (X : (operad A).Algebra) :
    standardOperation X 1 = (oneIso X.carrier).hom := by
  simp only [standardOperation, coefficientOperation, standardCoefficient_unit,
    X.unit_action, Iso.inv_hom_id_assoc]

/-- 概要：標準作用の部分合成則（Berger–Fresse §1.1.3）。
方針：係数の厳密な部分合成を代数の合成則へ入力。
規約：零入力も含む。使われ方：結合的忘却の三つの公理。 -/
lemma standardOperation_composite (X : (operad A).Algebra)
    (m n : ℕ) (i : Fin (m+1)) :
    standardOperation X (m+n) =
      (λ_ (power X.carrier (m+n))).inv ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction X.carrier (𝟙_ (Complex A)) m n i
        ((λ_ (power X.carrier n)).hom ≫ standardOperation X n) ≫
      standardOperation X (m+1) := by
  have h := coefficientOperation_comp X m n i
    (standardCoefficient A (m+1)) (standardCoefficient A n)
  rw [standardCoefficient_composite] at h
  simpa only [standardOperation, coefficientOperation, Iso.hom_inv_id_assoc] using h

/-- 概要：標準二入力積は厳密に結合的（Berger–Fresse §1.1.3）。
方針：同じ三入力作用を二つの位置の部分合成として表す。
規約：元の複体の結合子を用いる。使われ方：結合的 dg 代数構造。 -/
lemma standardBinary_assoc (X : (operad A).Algebra) :
    (standardBinary X ▷ X.carrier) ≫ standardBinary X =
      (α_ X.carrier X.carrier X.carrier).hom ≫
        (X.carrier ◁ standardBinary X) ≫ standardBinary X := by
  have hl := congrArg (fun f => _root_.SerrePositivity.HomologyZero.ternaryInput X.carrier ≫ f)
    (standardOperation_composite X 1 2 0)
  have hr := congrArg (fun f => _root_.SerrePositivity.HomologyZero.ternaryInput X.carrier ≫ f)
    (standardOperation_composite X 1 2 1)
  simp only [Nat.reduceAdd] at hl hr
  rw [_root_.SerrePositivity.HomologyZero.binaryAssociativityLeftInput] at hl
  rw [_root_.SerrePositivity.HomologyZero.binaryAssociativityRightInput] at hr
  exact hl.symm.trans hr

/-- 概要：標準零入力作用は積の左単位（Berger–Fresse §1.1.3）。
方針：第一位置への零入力代入と一入力作用の単位則を使う。
規約：厳密な複体射の等式。使われ方：結合的 dg 代数構造。 -/
lemma standardBinary_one_mul (X : (operad A).Algebra) :
    (standardOperation X 0 ▷ X.carrier) ≫ standardBinary X =
      (λ_ X.carrier).hom := by
  have h := congrArg (fun f => (oneIso X.carrier).inv ≫ f)
    (standardOperation_composite X 1 0 0)
  rw [standardOperation_one] at h
  simp only [Iso.inv_hom_id] at h
  change 𝟙 X.carrier = (oneIso X.carrier).inv ≫
    (λ_ (power X.carrier 1)).inv ≫
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction X.carrier (𝟙_ (Complex A)) 1 0 0
      ((λ_ (𝟙_ (Complex A))).hom ≫ standardOperation X 0) ≫ standardOperation X 2 at h
  rw [reassoc_of% (_root_.SerrePositivity.HomologyZero.nullaryBinaryInsertion X.carrier (standardOperation X 0))] at h
  apply (cancel_epi (λ_ X.carrier).inv).mp
  simpa only [standardBinary, Category.assoc, Iso.inv_hom_id] using h.symm

/-- 概要：標準零入力作用は積の右単位（Berger–Fresse §1.1.3）。
方針：第二位置への零入力代入と一入力作用の単位則を使う。
規約：積の可換性は使わない。使われ方：結合的 dg 代数構造。 -/
lemma standardBinary_mul_one (X : (operad A).Algebra) :
    (X.carrier ◁ standardOperation X 0) ≫ standardBinary X =
      (ρ_ X.carrier).hom := by
  have h := congrArg (fun f => (oneIso X.carrier).inv ≫ f)
    (standardOperation_composite X 1 0 1)
  rw [standardOperation_one] at h
  simp only [Iso.inv_hom_id] at h
  change 𝟙 X.carrier = (oneIso X.carrier).inv ≫
    (λ_ (power X.carrier 1)).inv ≫
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction X.carrier (𝟙_ (Complex A)) 1 0 1
      ((λ_ (𝟙_ (Complex A))).hom ≫ standardOperation X 0) ≫ standardOperation X 2 at h
  have he : (oneIso X.carrier).inv ≫ (λ_ (power X.carrier 1)).inv ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction X.carrier (𝟙_ (Complex A)) 1 0 1
        ((λ_ (𝟙_ (Complex A))).hom ≫ standardOperation X 0) =
      (ρ_ X.carrier).inv ≫ (X.carrier ◁ standardOperation X 0) ≫
        (X.carrier ◁ (oneIso X.carrier).inv) := by
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction, Fin.val_one, appendIso, oneIso, power,
      Iso.trans_inv, Iso.trans_hom, whiskerLeftIso_inv, whiskerLeftIso_hom,
      eqToIso.inv, eqToIso.hom, eqToHom_refl, Category.id_comp, Category.comp_id,
      comp_whiskerRight, whiskerLeft_comp, Category.assoc]
    rw [braiding_tensorUnit_left]
    monoidal
  rw [reassoc_of% he] at h
  apply (cancel_epi (ρ_ X.carrier).inv).mp
  simpa only [standardBinary, Category.assoc, Iso.inv_hom_id] using h.symm

/-- 概要：標準作用は全 BE 代数射で保たれる（Berger–Fresse §1.1.3）。
方針：代数射の作用保存と係数・単位子の自然性。
規約：全 arity を動かす。使われ方：結合的忘却の射成分。 -/
lemma standardOperation_map {X Y : (operad A).Algebra} (f : X ⟶ Y) (n : ℕ) :
    standardOperation X n ≫ f.hom =
      TensorPowers.map f.hom n ≫ standardOperation Y n := by
  simp only [standardOperation, coefficientOperation, Category.assoc]
  rw [f.comm]
  simp only [tensorHom_def, id_whiskerRight, Category.id_comp]
  rw [← whisker_exchange_assoc, leftUnitor_inv_naturality_assoc]

/-- 概要：BE の同じ carrier の結合的 dg 代数（Berger–Fresse §1.1.3）。
方針：標準零入力・二入力作用と三つの厳密なモノイド則を束ねる。
規約：可換性を仮定しない。使われ方：右 dg 加群の係数代数。 -/
def associativeAlgebra (X : (operad A).Algebra) : Mon (Complex A) where
  X := X.carrier
  mon := {
    one := standardOperation X 0
    mul := standardBinary X
    one_mul := standardBinary_one_mul X
    mul_one := standardBinary_mul_one X
    mul_assoc := standardBinary_assoc X }

/-- 概要：BE 代数射は指定した単位と積を保つ（Berger–Fresse §1.1.3）。
方針：零入力・二入力の作用保存に入力冪の自然性を適用。
規約：元の複体射を使う。使われ方：結合的忘却の全関手性。 -/
def associativeAlgebraMap {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    associativeAlgebra X ⟶ associativeAlgebra Y :=
  Mon.Hom.mk' f.hom
    (by
      change standardOperation X 0 ≫ f.hom = standardOperation Y 0
      have h := standardOperation_map f 0
      change standardOperation X 0 ≫ f.hom = 𝟙 _ ≫ standardOperation Y 0 at h
      exact h.trans (Category.id_comp _))
    (by
      change (X.carrier ◁ (oneIso X.carrier).inv) ≫ standardOperation X 2 ≫ f.hom =
        (f.hom ⊗ₘ f.hom) ≫ (Y.carrier ◁ (oneIso Y.carrier).inv) ≫ standardOperation Y 2
      rw [standardOperation_map, ← Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryInput_naturality, Category.assoc])

variable (A)
/-- 概要：BE 代数から同じ台の結合的 dg 代数への忘却（Berger–Fresse §1.1.3）。
方針：標準係数の作用で対象を、元の代数射で射を送る。
規約：全射を含み carrier を変えない。使われ方：一般の BE 底上の加群模型。 -/
def assocForget : (operad A).Algebra ⥤ Mon (Complex A) where
  obj := associativeAlgebra
  map := associativeAlgebraMap
  map_id _ := Mon.Hom.ext rfl
  map_comp _ _ := Mon.Hom.ext rfl

/-- 概要：結合的忘却の台の関手は元の BE 忘却と一致（Berger–Fresse §1.1.3）。
方針：対象・全射を同じにした定義を比較。規約：関手そのものの等式。
使われ方：台の擬同型性を指定した dg 代数射へ運ぶ。 -/
lemma assocForget_forget : assocForget A ⋙ Mon.forget (Complex A) =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A) := rfl

end SerrePositivity.EInfinity.BarrattEccles
