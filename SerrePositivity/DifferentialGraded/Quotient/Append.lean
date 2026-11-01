module

public import SerrePositivity.DifferentialGraded.Quotient.Erasure
public import SerrePositivity.DifferentialGraded.Complexes.AssociatorCochainNaturality
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoinHomNaturality
public import SerrePositivity.DifferentialGraded.Quotient.Path.Construction
public import SerrePositivity.DifferentialGraded.Quotient.Scalar
public import SerrePositivity.DifferentialGraded.Complexes.TensorCarryUnit
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproductExt
public import SerrePositivity.DifferentialGraded.Complexes.PrefixTensorCochain
public import SerrePositivity.DifferentialGraded.Complexes.TensorCarryAssociativity

/-!
# Quotient.Append

## 概要
19 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

universe u v

/-! ## PrependTailNaturality（旧 SerrePositivity/DifferentialGraded/Quotient/PrependTailNaturality.lean） -/

/-! # 先頭Hom合成と後方cochainの整合性

先頭の中間対象を保ったまま、それより後のtensor部分に任意次数cochainを作用させる場合を扱う。
先頭εを消す場合の結合則は別途必要である。
-/

@[expose] public section PrependTailNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- prependMapは先頭の中間対象より後の任意次数cochainと可換する。 -/
lemma prependMap_tail_cochain {S : Set D} (c : S) (w w' : Word S) (x y z : D)
    (p : ℤ) (f : Cochain (epsilonComplex A ⊗ term A D w c.val z)
      (epsilonComplex A ⊗ term A D w' c.val z) p) :
    (Cochain.ofHom (prependMap A D (c :: w) x y z)).comp
      ((tensorLeftHom (homObject A D x c.val) _ _).f p f) (zero_add p) =
    ((tensorLeftHom (homObject A D x y) _ _).f p
      ((tensorLeftHom (homObject A D y c.val) _ _).f p f)).comp
      (Cochain.ofHom (prependMap A D (c :: w') x y z)) (add_zero p) := by
  simpa only [prependMap, tensorHom_id] using
    tensorJoin_cochain_naturality (homObject A D x y) (homObject A D y c.val)
      (homObject A D x c.val) _ _ (eComp (Complex A) x y c.val) p f

end SerrePositivity.DifferentialGraded.DGQuotient
end

end PrependTailNaturality

/-! ## PrependHomNaturality（旧 SerrePositivity/DifferentialGraded/Quotient/PrependHomNaturality.lean） -/

/-! # 先頭Hom合成の後方自然性を表す全Hom写像の等式 -/

@[expose] public section PrependHomNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 後方tensor部分への作用と先頭Hom合成の可換式を全Homのchain mapとして保持する。 -/
lemma prependMap_tail_hom {S : Set D} (c : S) (w w' : Word S) (x y z : D) :
    (tensorLeftHom (homObject A D y c.val)
      (epsilonComplex A ⊗ term A D w c.val z) (epsilonComplex A ⊗ term A D w' c.val z) ≫
      tensorLeftHom (homObject A D x y) (term A D (c :: w) y z) (term A D (c :: w') y z)) ≫
      homPostcompose (homObject A D x y ⊗ term A D (c :: w) y z)
        (prependMap A D (c :: w') x y z) =
    tensorLeftHom (homObject A D x c.val)
      (epsilonComplex A ⊗ term A D w c.val z) (epsilonComplex A ⊗ term A D w' c.val z) ≫
      homPrecompose (prependMap A D (c :: w) x y z) (term A D (c :: w') x z) := by
  simpa only [prependMap, term_cons, tensorHom_id] using
    tensorJoin_hom_naturality (homObject A D x y) (homObject A D y c.val)
      (homObject A D x c.val) (epsilonComplex A ⊗ term A D w c.val z)
      (epsilonComplex A ⊗ term A D w' c.val z) (eComp (Complex A) x y c.val)

/-- ε因子を保持する操作も先に合成し、残るpathの全Homを始域とする。 -/
lemma prependMap_suffix_hom {S : Set D} (c : S) (w w' : Word S) (x y z : D) :
    tensorLeftHom (epsilonComplex A) (term A D w c.val z) (term A D w' c.val z) ≫
      ((tensorLeftHom (homObject A D y c.val)
        (epsilonComplex A ⊗ term A D w c.val z) (epsilonComplex A ⊗ term A D w' c.val z) ≫
        tensorLeftHom (homObject A D x y) (term A D (c :: w) y z) (term A D (c :: w') y z)) ≫
        homPostcompose (homObject A D x y ⊗ term A D (c :: w) y z)
          (prependMap A D (c :: w') x y z)) =
    tensorLeftHom (epsilonComplex A) (term A D w c.val z) (term A D w' c.val z) ≫
      (tensorLeftHom (homObject A D x c.val)
        (epsilonComplex A ⊗ term A D w c.val z) (epsilonComplex A ⊗ term A D w' c.val z) ≫
        homPrecompose (prependMap A D (c :: w) x y z) (term A D (c :: w') x z)) := by
  rw [prependMap_tail_hom]

end SerrePositivity.DifferentialGraded.DGQuotient
end

end PrependHomNaturality

/-! ## PrependFirstNaturality（旧 SerrePositivity/DifferentialGraded/Quotient/PrependFirstNaturality.lean） -/

/-! # 先頭Hom合成と最初のε消去の整合性 -/

@[expose] public section PrependFirstNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

lemma prependMap_eraseMiddle {S : Set D} (c : S) (w : Word S) (x y z : D) :
    (Cochain.ofHom (prependMap A D (c :: w) x y z)).comp
      (eraseMiddle A (homObject A D x c.val) (term A D w c.val z)) (zero_add 1) =
    ((tensorLeftHom (homObject A D x y)
      (homObject A D y c.val ⊗ (epsilonComplex A ⊗ term A D w c.val z))
      (homObject A D y c.val ⊗ term A D w c.val z)).f 1
      (eraseMiddle A (homObject A D y c.val) (term A D w c.val z))).comp
      (Cochain.ofHom ((α_ (homObject A D x y) (homObject A D y c.val)
        (term A D w c.val z)).inv ≫ eComp (Complex A) x y c.val ▷ term A D w c.val z))
      (add_zero 1) := by
  simpa only [prependMap, tensorHom_id] using
    tensorJoin_eraseMiddle A (homObject A D x y) (homObject A D y c.val)
      (homObject A D x c.val) (term A D w c.val z) (eComp (Complex A) x y c.val)

/-- prependMapは最初のεを消す操作とも可換する。 -/
lemma prependMap_eraseFirst {S : Set D} (c : S) (w : Word S) (x y z : D) :
    (Cochain.ofHom (prependMap A D (c :: w) x y z)).comp
      (eraseFirst A D c w x z) (zero_add 1) =
    ((tensorLeftHom (homObject A D x y) (term A D (c :: w) y z)
      (term A D w y z)).f 1 (eraseFirst A D c w y z)).comp
      (Cochain.ofHom (prependMap A D w x y z)) (add_zero 1) := by
  have hc : (α_ (homObject A D x y) (homObject A D y c.val) (term A D w c.val z)).inv ≫
      (eComp (Complex A) x y c.val ▷ term A D w c.val z) ≫ prependMap A D w x c.val z =
      (homObject A D x y) ◁ prependMap A D w y c.val z ≫ prependMap A D w x y z := by
    rw [prependMap_assoc, Iso.inv_hom_id_assoc]
  rw [eraseFirst, eraseFirst, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    prependMap_eraseMiddle, tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp]
  let M : Cochain (homObject A D x y ⊗ term A D (c :: w) y z)
      (homObject A D x y ⊗ (homObject A D y c.val ⊗ term A D w c.val z)) 1 :=
    (tensorLeftHom (homObject A D x y) (term A D (c :: w) y z)
      (homObject A D y c.val ⊗ term A D w c.val z)).f 1
        (eraseMiddle A (homObject A D y c.val) (term A D w c.val z))
  change M.comp (Cochain.ofHom _) (add_zero 1) = M.comp (Cochain.ofHom _) (add_zero 1)
  exact congrArg (fun f : homObject A D x y ⊗
      (homObject A D y c.val ⊗ term A D w c.val z) ⟶ term A D w x z =>
    M.comp (Cochain.ofHom f) (add_zero 1)) hc

end SerrePositivity.DifferentialGraded.DGQuotient
end

end PrependFirstNaturality

/-! ## PrependErasureNaturality（旧 SerrePositivity/DifferentialGraded/Quotient/PrependErasureNaturality.lean） -/

/-! # 後方ε消去とprependMapの可換式 -/

@[expose] public section PrependErasureNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
attribute [local irreducible] eraseFace

/-- prependMapは先頭εより後のε消去と可換する。 -/
lemma prependMap_eraseFace_succ {S : Set D} (c : S) (w : Word S) (i : ℕ) (x y z : D) :
    (Cochain.ofHom (prependMap A D (c :: w) x y z)).comp
      (eraseFace A D (c :: w) (i + 1) x z) (zero_add 1) =
    ((tensorLeftHom (homObject A D x y) (term A D (c :: w) y z)
      (term A D ((c :: w).eraseIdx (i + 1)) y z)).f 1
        (eraseFace A D (c :: w) (i + 1) y z)).comp
      (Cochain.ofHom (prependMap A D ((c :: w).eraseIdx (i + 1)) x y z)) (add_zero 1) := by
  have h := congrArg (fun t : homComplex A (term A D w c.val z)
      (term A D (w.eraseIdx i) c.val z) ⟶
      homComplex A (homObject A D x y ⊗ term A D (c :: w) y z)
        (term A D (c :: w.eraseIdx i) x z) => t.f 1 (eraseFace A D w i c.val z))
    (prependMap_suffix_hom A D c w (w.eraseIdx i) x y z)
  simp only [chain_comp_apply, homPostcompose_apply] at h
  rw [eraseFace_cons_succ, eraseFace_cons_succ]
  exact h.symm

end SerrePositivity.DifferentialGraded.DGQuotient
end

end PrependErasureNaturality

/-! ## PrependErasureRows（旧 SerrePositivity/DifferentialGraded/Quotient/PrependErasureRows.lean） -/

/-! # 先頭Homの作用と全てのε消去項の自然性

空pathを左に置く合成について、ε消去のLeibniz則の基底式を構成する。
-/

@[expose] public section PrependErasureRows

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 先頭Hom合成は任意の位置のε消去と可換する。範囲外の位置も含む。 -/
lemma prependMap_eraseFace {S : Set D} (w : Word S) (i : ℕ) (x y z : D) :
    (Cochain.ofHom (prependMap A D w x y z)).comp (eraseFace A D w i x z) (zero_add 1) =
    ((tensorLeftHom (homObject A D x y) (term A D w y z)
      (term A D (w.eraseIdx i) y z)).f 1 (eraseFace A D w i y z)).comp
      (Cochain.ofHom (prependMap A D (w.eraseIdx i) x y z)) (add_zero 1) := by
  cases w with
  | nil => simp only [eraseFace_nil, map_zero, Cochain.comp_zero, Cochain.zero_comp]
  | cons c w =>
    cases i with
    | zero => exact prependMap_eraseFirst A D c w x y z
    | succ i => exact prependMap_eraseFace_succ A D c w i x y z

variable [Small.{u} D]

/-- 元のHomを全path直和の先頭へ合成する内部chain map。 -/
def internalPrepend (S : Set D) (x y z : D) :
    homObject A D x y ⊗ internalHom A D S y z ⟶ internalHom A D S x z :=
  (originalHom A D S x y ▷ internalHom A D S y z) ≫ internalComposition A D S x y z

lemma internalPrepend_ι (S : Set D) (x y z : D) (w : Word S) :
    ((homObject A D x y) ◁ ι A D S y z w) ≫ internalPrepend A D S x y z =
      prependMap A D w x y z ≫ ι A D S x z w := by
  rw [internalPrepend, ← Category.assoc, ← tensorHom_def', internalComposition_original_left]

/-- 一つのε消去項を全直和へ入れた後も先頭Hom作用と可換する。 -/
lemma prependMap_eraseSummand {S : Set D} (w : Word S) (i : ℕ) (x y z : D) :
    (Cochain.ofHom (prependMap A D w x y z)).comp (eraseSummand A D w i x z) (zero_add 1) =
    ((tensorLeftHom (homObject A D x y) (term A D w y z)
      (internalHom A D S y z)).f 1 (eraseSummand A D w i y z)).comp
      (Cochain.ofHom (internalPrepend A D S x y z)) (add_zero 1) := by
  rw [eraseSummand, eraseSummand, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    prependMap_eraseFace, tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain, Cochain.comp_assoc_of_third_is_zero_cochain,
    ← Cochain.ofHom_comp, ← Cochain.ofHom_comp, internalPrepend_ι]

/-- 一つのpath上の有限消去和は先頭Hom作用と可換する。 -/
lemma prependMap_eraseRow {S : Set D} (w : Word S) (x y z : D) :
    (Cochain.ofHom (prependMap A D w x y z)).comp (eraseRow A D w x z) (zero_add 1) =
    ((tensorLeftHom (homObject A D x y) (term A D w y z)
      (internalHom A D S y z)).f 1 (eraseRow A D w y z)).comp
      (Cochain.ofHom (internalPrepend A D S x y z)) (add_zero 1) := by
  let L : Cochain (term A D w x z) (internalHom A D S x z) 1 →+
      Cochain (homObject A D x y ⊗ term A D w y z) (internalHom A D S x z) 1 :=
    { toFun := fun f => (Cochain.ofHom (prependMap A D w x y z)).comp f (zero_add 1)
      map_zero' := Cochain.comp_zero _ _
      map_add' := fun f g => Cochain.comp_add _ f g _ }
  let R : Cochain (term A D w y z) (internalHom A D S y z) 1 →+
      Cochain (homObject A D x y ⊗ term A D w y z) (internalHom A D S x z) 1 :=
    { toFun := fun f => ((tensorLeftHom (homObject A D x y) (term A D w y z)
        (internalHom A D S y z)).f 1 f).comp
        (Cochain.ofHom (internalPrepend A D S x y z)) (add_zero 1)
      map_zero' := by rw [map_zero]; exact Cochain.zero_comp _ _
      map_add' := fun f g => by rw [map_add, Cochain.add_comp] }
  change L (eraseRow A D w x z) = R (eraseRow A D w y z)
  rw [eraseRow, eraseRow, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact prependMap_eraseSummand A D w i x y z

end SerrePositivity.DifferentialGraded.DGQuotient
end

end PrependErasureRows

/-! ## PrependErasure（旧 SerrePositivity/DifferentialGraded/Quotient/PrependErasure.lean） -/

/-! # 全path直和における先頭Hom作用とε消去の可換性 -/

@[expose] public section PrependErasure

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 空pathを左に置く合成のε消去Leibniz則。左の元のHomには消去項がない。 -/
lemma internalPrepend_erasure (S : Set D) (x y z : D) :
    (Cochain.ofHom (internalPrepend A D S x y z)).comp (erasure A D S x z) (zero_add 1) =
    ((tensorLeftHom (homObject A D x y) (internalHom A D S y z)
      (internalHom A D S y z)).f 1 (erasure A D S y z)).comp
      (Cochain.ofHom (internalPrepend A D S x y z)) (add_zero 1) := by
  apply tensorLeftPathCochain_ext A D S y z (homObject A D x y) 1
  intro w
  have hb : (Cochain.ofHom ((homObject A D x y) ◁ ι A D S y z w)).comp
      ((tensorLeftHom (homObject A D x y) (internalHom A D S y z)
        (internalHom A D S y z)).f 1 (erasure A D S y z)) (zero_add 1) =
      (tensorLeftHom (homObject A D x y) (term A D w y z)
        (internalHom A D S y z)).f 1 (eraseRow A D w y z) := by
    rw [← tensorLeftHom_ofHom, ← tensorLeftHom_cochain_comp, erasure_precomp]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    internalPrepend_ι, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    erasure_precomp, ← Cochain.comp_assoc_of_first_is_zero_cochain, hb]
  exact prependMap_eraseRow A D w x y z

/-- 空pathを左に置く消去Leibniz則の斉次成分。右側の消去には(-1)^pが付く。 -/
lemma internalPrepend_erasure_apply (S : Set D) (x y z : D) (p q n : ℤ)
    (hn : p + q = n) (a : (homObject A D x y).X p) (b : (internalHom A D S y z).X q) :
    (erasure A D S x z).v n (n + 1) rfl
      ((internalPrepend A D S x y z).f n
        (ιTensorObj (homObject A D x y) (internalHom A D S y z) p q n hn (a ⊗ₜ[A] b))) =
    p.negOnePow • (internalPrepend A D S x y z).f (n + 1)
      (ιTensorObj (homObject A D x y) (internalHom A D S y z) p (q + 1) (n + 1)
        (by omega) (a ⊗ₜ[A] (erasure A D S y z).v q (q + 1) rfl b)) := by
  have h := congrArg (fun f : Cochain
      (homObject A D x y ⊗ internalHom A D S y z) (internalHom A D S x z) 1 =>
    f.v n (n + 1) rfl
      (ιTensorObj (homObject A D x y) (internalHom A D S y z) p q n hn (a ⊗ₜ[A] b)))
    (internalPrepend_erasure A D S x y z)
  rw [cochain_ofHom_comp_apply, cochain_comp_ofHom_apply,
    tensorLeftHom_apply, chain_units_smul] at h
  simpa only [one_mul] using h

end SerrePositivity.DifferentialGraded.DGQuotient
end

end PrependErasure

/-! ## AppendRight（旧 SerrePositivity/DifferentialGraded/Quotient/AppendRight.lean） -/

/-! # 左pathを固定した全path直和への連結 -/

@[expose] public section AppendRight

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 左の有限pathを固定し、右の全pathへ連結する内部chain map。 -/
def appendRight {S : Set D} (w : Word S) (x y z : D) :
    term A D w x y ⊗ internalHom A D S y z ⟶ internalHom A D S x z :=
  tensorCoproductRightDesc (term A D w x y) (fun v : Word S => term A D v y z)
    (internalHom A D S x z) (fun v => appendMap A D w v x y z ≫ ι A D S x z (w ++ v))

lemma appendRight_ι {S : Set D} (w v : Word S) (x y z : D) :
    (term A D w x y ◁ ι A D S y z v) ≫ appendRight A D w x y z =
      appendMap A D w v x y z ≫ ι A D S x z (w ++ v) :=
  tensorCoproductRightDesc_ι _ _ _ _ v

lemma internalComposition_left_ι (S : Set D) (w : Word S) (x y z : D) :
    (ι A D S x y w ▷ internalHom A D S y z) ≫ internalComposition A D S x y z =
      appendRight A D w x y z := tensorCoproductDesc_left _ _ _ _ w

/-- 左pathが空なら先頭Hom作用に戻る。 -/
lemma appendRight_nil (S : Set D) (x y z : D) :
    appendRight A D ([] : Word S) x y z = internalPrepend A D S x y z := by
  apply (tensorLeftCoproductIsColimit (homObject A D x y)
    (fun v : Word S => term A D v y z)).hom_ext
  rintro ⟨v⟩
  change (homObject A D x y ◁ ι A D S y z v) ≫ appendRight A D [] x y z =
    (homObject A D x y ◁ ι A D S y z v) ≫ internalPrepend A D S x y z
  exact (appendRight_ι A D [] v x y z).trans (internalPrepend_ι A D S x y z v).symm

/-- 非空の左pathの連結は、短いpathの連結に前方Homとεを戻したもの。 -/
lemma appendRight_cons {S : Set D} (b : S) (w : Word S) (x y z : D) :
    appendRight A D (b :: w) x y z =
    (α_ (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)
      (internalHom A D S y z)).hom ≫
    (homObject A D x b.val) ◁
      ((α_ (epsilonComplex A) (term A D w b.val y) (internalHom A D S y z)).hom ≫
        (epsilonComplex A) ◁ appendRight A D w b.val y z) ≫ prefixPath A D b x z := by
  apply (tensorLeftCoproductIsColimit (term A D (b :: w) x y)
    (fun v : Word S => term A D v y z)).hom_ext
  rintro ⟨v⟩
  have hm : ((epsilonComplex A ⊗ term A D w b.val y) ◁ ι A D S y z v) ≫
      (α_ (epsilonComplex A) (term A D w b.val y) (internalHom A D S y z)).hom ≫
        (epsilonComplex A) ◁ appendRight A D w b.val y z =
    (α_ (epsilonComplex A) (term A D w b.val y) (term A D v y z)).hom ≫
      (epsilonComplex A) ◁ appendMap A D w v b.val y z ≫
        (epsilonComplex A) ◁ ι A D S b.val z (w ++ v) := by
    rw [associator_naturality_right_assoc, ← whiskerLeft_comp, appendRight_ι, whiskerLeft_comp]
  have ht : ((homObject A D x b.val ⊗ (epsilonComplex A ⊗ term A D w b.val y)) ◁
      ι A D S y z v) ≫
      (α_ (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)
        (internalHom A D S y z)).hom ≫
      (homObject A D x b.val) ◁
        ((α_ (epsilonComplex A) (term A D w b.val y) (internalHom A D S y z)).hom ≫
          (epsilonComplex A) ◁ appendRight A D w b.val y z) =
    (α_ (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)
      (term A D v y z)).hom ≫
      (homObject A D x b.val) ◁ (α_ (epsilonComplex A) (term A D w b.val y)
        (term A D v y z)).hom ≫
      (homObject A D x b.val) ◁ ((epsilonComplex A) ◁ appendMap A D w v b.val y z) ≫
      (homObject A D x b.val) ◁ ((epsilonComplex A) ◁ ι A D S b.val z (w ++ v)) := by
    rw [associator_naturality_right_assoc, ← whiskerLeft_comp, hm]
    simp only [whiskerLeft_comp]
  have h := congrArg (fun f => f ≫ prefixPath A D b x z) ht
  simp only [Category.assoc, prefixPath_ι] at h
  change (term A D (b :: w) x y ◁ ι A D S y z v) ≫ appendRight A D (b :: w) x y z = _
  rw [appendRight_ι]
  simpa only [Cofan.mk_ι_app, term_cons, appendMap, ι, List.cons_append,
    whiskerLeft_comp, Category.assoc] using h.symm

end SerrePositivity.DifferentialGraded.DGQuotient
end

end AppendRight

/-! ## AppendRightUnit（旧 SerrePositivity/DifferentialGraded/Quotient/AppendRightUnit.lean） -/

/-! # 全右pathへの連結の右単位 -/

@[expose] public section AppendRightUnit

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 右側の空pathに恒等射を入れた連結は元のpath包含となる。 -/
lemma appendRight_right_unit {S : Set D} (w : Word S) (x y : D) :
    (ρ_ (term A D w x y)).inv ≫ term A D w x y ◁ internalIdentity A D S y ≫
      appendRight A D w x y y = ι A D S x y w := by
  induction w generalizing x with
  | nil =>
    rw [appendRight_nil]
    simp only [internalIdentity, term_nil, originalHom, whiskerLeft_comp, Category.assoc]
    rw [internalPrepend_ι]
    simpa only [prependMap_nil, originalHom] using
      e_comp_id_assoc (Complex A) x y (originalHom A D S x y)
  | cons b w ih =>
    have h := tensorCarry_right_unit (homObject A D x b.val)
      (epsilonComplex A ⊗ term A D w b.val y) (internalHom A D S y y)
      (epsilonComplex A ⊗ internalHom A D S b.val y) (internalIdentity A D S y)
      ((α_ (epsilonComplex A) (term A D w b.val y) (internalHom A D S y y)).hom ≫
        (epsilonComplex A) ◁ appendRight A D w b.val y y)
    have ht := tensorCarry_right_unit (epsilonComplex A) (term A D w b.val y)
      (internalHom A D S y y) (internalHom A D S b.val y) (internalIdentity A D S y)
      (appendRight A D w b.val y y)
    rw [ih b.val] at ht
    rw [ht] at h
    have hp := congrArg (fun f => f ≫ prefixPath A D b x y) h
    simp only [Category.assoc, prefixPath_ι] at hp
    simpa only [appendRight_cons, term_cons, Category.assoc] using hp

end SerrePositivity.DifferentialGraded.DGQuotient
end

end AppendRightUnit

/-! ## AppendRightPrepend（旧 SerrePositivity/DifferentialGraded/Quotient/AppendRightPrepend.lean） -/

/-! # 左有限pathの連結と先頭Hom作用の全右pathに関する結合則 -/

@[expose] public section AppendRightPrepend

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma appendRight_prepend {S : Set D} (w : Word S) (x y z t : D) :
    (prependMap A D w x y z ▷ internalHom A D S z t) ≫ appendRight A D w x z t =
    (α_ (homObject A D x y) (term A D w y z) (internalHom A D S z t)).hom ≫
      (homObject A D x y) ◁ appendRight A D w y z t ≫ internalPrepend A D S x y t := by
  apply (tensorLeftCoproductIsColimit (homObject A D x y ⊗ term A D w y z)
    (fun v : Word S => term A D v z t)).hom_ext
  rintro ⟨v⟩
  change ((homObject A D x y ⊗ term A D w y z) ◁ ι A D S z t v) ≫
      (prependMap A D w x y z ▷ internalHom A D S z t) ≫ appendRight A D w x z t =
    ((homObject A D x y ⊗ term A D w y z) ◁ ι A D S z t v) ≫
      (α_ (homObject A D x y) (term A D w y z) (internalHom A D S z t)).hom ≫
      (homObject A D x y) ◁ appendRight A D w y z t ≫ internalPrepend A D S x y t
  rw [whisker_exchange_assoc, appendRight_ι, appendMap_prepend_assoc,
    associator_naturality_right_assoc, ← whiskerLeft_comp_assoc, appendRight_ι,
    whiskerLeft_comp_assoc, internalPrepend_ι]

end SerrePositivity.DifferentialGraded.DGQuotient
end

end AppendRightPrepend

/-! ## AppendErasureHead（旧 SerrePositivity/DifferentialGraded/Quotient/AppendErasureHead.lean） -/

/-! # 全右pathへの連結と先頭ε消去の整合式 -/

@[expose] public section AppendErasureHead

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 後方pathを連結してから先頭εを消す項は、先に先頭εを消した連結と一致する。 -/
lemma appendRight_eraseFirst {S : Set D} (b : S) (w : Word S) (x y z : D) :
    ((Cochain.ofHom
      ((α_ (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)
        (internalHom A D S y z)).hom ≫
       (homObject A D x b.val) ◁
         (α_ (epsilonComplex A) (term A D w b.val y) (internalHom A D S y z)).hom ≫
       (homObject A D x b.val) ◁ ((epsilonComplex A) ◁ appendRight A D w b.val y z))).comp
      (eraseMiddle A (homObject A D x b.val) (internalHom A D S b.val z)) (zero_add 1)).comp
      (Cochain.ofHom (internalPrepend A D S x b.val z)) (add_zero 1) =
    ((tensorRightHom (internalHom A D S y z) (term A D (b :: w) x y) (term A D w x y)).f 1
      (eraseFirst A D b w x y)).comp (Cochain.ofHom (appendRight A D w x y z)) (add_zero 1) := by
  rw [eraseMiddle_tensorRight_naturality,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, Category.assoc,
    ← appendRight_prepend, Cochain.ofHom_comp,
    ← Cochain.comp_assoc_of_third_is_zero_cochain,
    ← tensorRightHom_ofHom, ← tensorRightHom_cochain_comp]
  rfl

end SerrePositivity.DifferentialGraded.DGQuotient
end

end AppendErasureHead

/-! ## PrefixErasure（旧 SerrePositivity/DifferentialGraded/Quotient/PrefixErasure.lean） -/

/-! # 前方Homとεを追加する操作に対する全消去作用素の再帰式 -/

@[expose] public section PrefixErasure

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 非空pathの全消去は、追加した先頭εの消去と、後方の全消去の和。 -/
lemma prefixPath_erasure {S : Set D} (b : S) (x y : D) :
    (Cochain.ofHom (prefixPath A D b x y)).comp (erasure A D S x y) (zero_add 1) =
    (eraseMiddle A (homObject A D x b.val) (internalHom A D S b.val y)).comp
      (Cochain.ofHom (internalPrepend A D S x b.val y)) (add_zero 1) +
    ((tensorLeftHom (homObject A D x b.val)
      (epsilonComplex A ⊗ internalHom A D S b.val y)
      (epsilonComplex A ⊗ internalHom A D S b.val y)).f 1
      ((tensorLeftHom (epsilonComplex A) (internalHom A D S b.val y)
        (internalHom A D S b.val y)).f 1 (erasure A D S b.val y))).comp
      (Cochain.ofHom (prefixPath A D b x y)) (add_zero 1) := by
  apply prefixPathCochain_ext A D b x y 1
  intro w
  have ht :
      (Cochain.ofHom ((homObject A D x b.val) ◁ ((epsilonComplex A) ◁ ι A D S b.val y w))).comp
        ((tensorLeftHom (homObject A D x b.val)
          (epsilonComplex A ⊗ internalHom A D S b.val y)
          (epsilonComplex A ⊗ internalHom A D S b.val y)).f 1
          ((tensorLeftHom (epsilonComplex A) (internalHom A D S b.val y)
            (internalHom A D S b.val y)).f 1 (erasure A D S b.val y))) (zero_add 1) =
      (tensorLeftHom (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)
        (epsilonComplex A ⊗ internalHom A D S b.val y)).f 1
        ((tensorLeftHom (epsilonComplex A) (term A D w b.val y)
          (internalHom A D S b.val y)).f 1 (eraseRow A D w b.val y)) := by
    rw [← tensorLeftHom_ofHom (homObject A D x b.val), ← tensorLeftHom_cochain_comp,
      ← tensorLeftHom_ofHom (epsilonComplex A), ← tensorLeftHom_cochain_comp, erasure_precomp]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    prefixPath_ι, erasure_precomp, Cochain.comp_add,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, eraseMiddle_naturality,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, internalPrepend_ι,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, ht]
  exact eraseRow_cons A D b w x y

end SerrePositivity.DifferentialGraded.DGQuotient
end

end PrefixErasure

/-! ## PrefixGeneration（旧 SerrePositivity/DifferentialGraded/Quotient/PrefixGeneration.lean） -/

/-! # 前方Hom・ε追加を元のHomとεの合成から復元する -/

@[expose] public section PrefixGeneration

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma epsilon_internalComposition_ι {S : Set D} (b : S) (w : Word S) (y : D) :
    ((epsilonComplex A) ◁ ι A D S b.val y w) ≫
      (epsilon A D S b ▷ internalHom A D S b.val y) ≫ internalComposition A D S b.val b.val y =
    (epsilonTerm A D b ▷ term A D w b.val y) ≫ appendMap A D [b] w b.val b.val y ≫
      ι A D S b.val y (b :: w) := by
  rw [epsilon, comp_whiskerRight, Category.assoc, whisker_exchange_assoc,
    ← tensorHom_def'_assoc, internalComposition_ι]
  rfl

lemma prefixPath_generated {S : Set D} (b : S) (x y : D) :
    (homObject A D x b.val) ◁
      ((epsilon A D S b ▷ internalHom A D S b.val y) ≫ internalComposition A D S b.val b.val y) ≫
      internalPrepend A D S x b.val y = prefixPath A D b x y := by
  apply (prefixPathCofanIsColimit A D b x y).hom_ext
  rintro ⟨w⟩
  change ((homObject A D x b.val) ◁ ((epsilonComplex A) ◁ ι A D S b.val y w)) ≫
      (homObject A D x b.val) ◁
        ((epsilon A D S b ▷ internalHom A D S b.val y) ≫
          internalComposition A D S b.val b.val y) ≫ internalPrepend A D S x b.val y =
    ((homObject A D x b.val) ◁ ((epsilonComplex A) ◁ ι A D S b.val y w)) ≫ prefixPath A D b x y
  rw [prefixPath_ι, ← whiskerLeft_comp_assoc, epsilon_internalComposition_ι]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [internalPrepend_ι]
  have h := congrArg (fun f => f ≫ ι A D S x y (b :: w))
    (prependMap_epsilonTerm_append A D b w x y)
  simpa only [term_cons, whiskerLeft_comp, Category.assoc, Category.id_comp] using h

end SerrePositivity.DifferentialGraded.DGQuotient
end

end PrefixGeneration

/-! ## InternalRightUnit（旧 SerrePositivity/DifferentialGraded/Quotient/InternalRightUnit.lean） -/

/-! # 内部path合成の全直和における右単位 -/

@[expose] public section InternalRightUnit

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma internalComposition_right_unit (S : Set D) (x y : D) :
    (ρ_ (internalHom A D S x y)).inv ≫ internalHom A D S x y ◁ internalIdentity A D S y ≫
      internalComposition A D S x y y = 𝟙 _ := by
  apply hom_ext A D S x y
  intro w
  simp only [Category.comp_id]
  rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
    internalComposition_left_ι, appendRight_right_unit]

end SerrePositivity.DifferentialGraded.DGQuotient
end

end InternalRightUnit

/-! ## CompositionPrefix（旧 SerrePositivity/DifferentialGraded/Quotient/CompositionPrefix.lean） -/

/-! # 全path合成と先頭Hom・εの追加の整合性 -/

@[expose] public section CompositionPrefix

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma composition_prefix_left_ι {S : Set D} (b : S) (w : Word S) (x y z : D) :
    (((homObject A D x b.val) ◁ ((epsilonComplex A) ◁ ι A D S b.val y w)) ▷
    internalHom A D S y z) ≫ (prefixPath A D b x y ▷ internalHom A D S y z) ≫
      internalComposition A D S x y z = appendRight A D (b :: w) x y z := by
  rw [← comp_whiskerRight_assoc, prefixPath_ι, internalComposition_left_ι]

lemma composition_prefix_middle_ι {S : Set D} (b : S) (w : Word S) (y z : D) :
    (((epsilonComplex A) ◁ ι A D S b.val y w) ▷ internalHom A D S y z) ≫
    (α_ (epsilonComplex A) (internalHom A D S b.val y) (internalHom A D S y z)).hom ≫
      (epsilonComplex A) ◁ internalComposition A D S b.val y z =
  (α_ (epsilonComplex A) (term A D w b.val y) (internalHom A D S y z)).hom ≫
    (epsilonComplex A) ◁ appendRight A D w b.val y z := by
  rw [associator_naturality_middle_assoc, ← whiskerLeft_comp, internalComposition_left_ι]

lemma composition_prefix_outer_ι {S : Set D} (b : S) (w : Word S) (x y z : D) :
    (((homObject A D x b.val) ◁ ((epsilonComplex A) ◁ ι A D S b.val y w)) ▷
    internalHom A D S y z) ≫
    (α_ (homObject A D x b.val) (epsilonComplex A ⊗ internalHom A D S b.val y)
      (internalHom A D S y z)).hom ≫
    (homObject A D x b.val) ◁
      ((α_ (epsilonComplex A) (internalHom A D S b.val y) (internalHom A D S y z)).hom ≫
        (epsilonComplex A) ◁ internalComposition A D S b.val y z) =
  (α_ (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)
    (internalHom A D S y z)).hom ≫
  (homObject A D x b.val) ◁
    ((α_ (epsilonComplex A) (term A D w b.val y) (internalHom A D S y z)).hom ≫
      (epsilonComplex A) ◁ appendRight A D w b.val y z) := by
  rw [associator_naturality_middle_assoc, ← whiskerLeft_comp, composition_prefix_middle_ι]

/-- 各path上で先頭追加と全合成の二つの順序を比較する。 -/
lemma composition_prefix_restrict {S : Set D} (b : S) (w : Word S) (x y z : D) :
    (((homObject A D x b.val) ◁ ((epsilonComplex A) ◁ ι A D S b.val y w)) ▷
      internalHom A D S y z) ≫ (prefixPath A D b x y ▷ internalHom A D S y z) ≫
      internalComposition A D S x y z =
    (((homObject A D x b.val) ◁ ((epsilonComplex A) ◁ ι A D S b.val y w)) ▷
      internalHom A D S y z) ≫
      (α_ (homObject A D x b.val) (epsilonComplex A ⊗ internalHom A D S b.val y)
        (internalHom A D S y z)).hom ≫ (homObject A D x b.val) ◁
        ((α_ (epsilonComplex A) (internalHom A D S b.val y) (internalHom A D S y z)).hom ≫
          (epsilonComplex A) ◁ internalComposition A D S b.val y z) ≫ prefixPath A D b x z := by
  have hr := congrArg (fun f => f ≫ prefixPath A D b x z)
    (composition_prefix_outer_ι A D b w x y z)
  simp only [Category.assoc] at hr
  exact (composition_prefix_left_ι A D b w x y z).trans
      ((appendRight_cons A D b w x y z).trans hr.symm)

/-- 先頭Homとεを追加してから合成しても、後方を合成してから追加しても一致する。 -/
lemma internalComposition_prefixPath {S : Set D} (b : S) (x y z : D) :
    (prefixPath A D b x y ▷ internalHom A D S y z) ≫ internalComposition A D S x y z =
    (α_ (homObject A D x b.val) (epsilonComplex A ⊗ internalHom A D S b.val y)
      (internalHom A D S y z)).hom ≫
    (homObject A D x b.val) ◁
      ((α_ (epsilonComplex A) (internalHom A D S b.val y) (internalHom A D S y z)).hom ≫
        (epsilonComplex A) ◁ internalComposition A D S b.val y z) ≫ prefixPath A D b x z := by
  apply tensorLeftTwoRightCoproduct_hom_ext (homObject A D x b.val) (epsilonComplex A)
    (internalHom A D S y z) (fun w : Word S => term A D w b.val y)
  intro w
  exact composition_prefix_restrict A D b w x y z

end SerrePositivity.DifferentialGraded.DGQuotient
end

end CompositionPrefix

/-! ## CompositionPrepend（旧 SerrePositivity/DifferentialGraded/Quotient/CompositionPrepend.lean） -/

/-! # 全path合成と元のHomの先頭作用の結合則 -/

@[expose] public section CompositionPrepend

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma internalComposition_prepend (S : Set D) (x y z t : D) :
    (internalPrepend A D S x y z ▷ internalHom A D S z t) ≫ internalComposition A D S x z t =
    (α_ (homObject A D x y) (internalHom A D S y z) (internalHom A D S z t)).hom ≫
      (homObject A D x y) ◁ internalComposition A D S y z t ≫ internalPrepend A D S x y t := by
  apply tensorLeftRightCoproduct_hom_ext (homObject A D x y) (internalHom A D S z t)
    (fun w : Word S => term A D w y z)
  intro w
  let s : (homObject A D x y ⊗ term A D w y z) ⊗ internalHom A D S z t ⟶
      (homObject A D x y ⊗ internalHom A D S y z) ⊗ internalHom A D S z t :=
    ((homObject A D x y) ◁ ι A D S y z w) ▷ internalHom A D S z t
  change s ≫ (internalPrepend A D S x y z ▷ internalHom A D S z t) ≫
      internalComposition A D S x z t =
    s ≫ (α_ (homObject A D x y) (internalHom A D S y z) (internalHom A D S z t)).hom ≫
      (homObject A D x y) ◁ internalComposition A D S y z t ≫ internalPrepend A D S x y t
  have hl : (((homObject A D x y) ◁ ι A D S y z w) ▷ internalHom A D S z t) ≫
      (internalPrepend A D S x y z ▷ internalHom A D S z t) ≫
      internalComposition A D S x z t =
    (prependMap A D w x y z ▷ internalHom A D S z t) ≫ appendRight A D w x z t := by
    rw [← comp_whiskerRight_assoc, internalPrepend_ι, comp_whiskerRight,
      Category.assoc, internalComposition_left_ι]
  have hm : (((homObject A D x y) ◁ ι A D S y z w) ▷ internalHom A D S z t) ≫
      (α_ (homObject A D x y) (internalHom A D S y z) (internalHom A D S z t)).hom ≫
      (homObject A D x y) ◁ internalComposition A D S y z t =
    (α_ (homObject A D x y) (term A D w y z) (internalHom A D S z t)).hom ≫
      (homObject A D x y) ◁ appendRight A D w y z t := by
    rw [associator_naturality_middle_assoc, ← whiskerLeft_comp, internalComposition_left_ι]
  have hr := congrArg (fun f => f ≫ internalPrepend A D S x y t) hm
  simpa only [Category.assoc] using hl.trans ((appendRight_prepend A D w x y z t).trans hr.symm)

end SerrePositivity.DifferentialGraded.DGQuotient
end

end CompositionPrepend

/-! ## AppendLiftCochain（旧 SerrePositivity/DifferentialGraded/Quotient/AppendLiftCochain.lean） -/

/-! # 連結の帰納ステップへ後方cochainを持ち上げる操作 -/

@[expose] public section AppendLiftCochain

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 前方Homとεを付け直し、後方の連結cochainを全pathへ戻す。 -/
def appendLiftCochain {S : Set D} (b : S) (w : Word S) (x y z : D) (p : ℤ)
    (f : Cochain (term A D w b.val y ⊗ internalHom A D S y z)
      (internalHom A D S b.val z) p) :
    Cochain (term A D (b :: w) x y ⊗ internalHom A D S y z) (internalHom A D S x z) p :=
  ((Cochain.ofHom ((α_ (homObject A D x b.val)
      (epsilonComplex A ⊗ term A D w b.val y) (internalHom A D S y z)).hom ≫
      (homObject A D x b.val) ◁
        (α_ (epsilonComplex A) (term A D w b.val y) (internalHom A D S y z)).hom)).comp
    ((tensorLeftHom (homObject A D x b.val)
      (epsilonComplex A ⊗ (term A D w b.val y ⊗ internalHom A D S y z))
      (epsilonComplex A ⊗ internalHom A D S b.val z)).f p
      ((tensorLeftHom (epsilonComplex A) (term A D w b.val y ⊗ internalHom A D S y z)
        (internalHom A D S b.val z)).f p f)) (zero_add p)).comp
      (Cochain.ofHom (prefixPath A D b x z)) (add_zero p)

lemma appendLiftCochain_add {S : Set D} (b : S) (w : Word S) (x y z : D) (p : ℤ)
    (f g : Cochain (term A D w b.val y ⊗ internalHom A D S y z)
      (internalHom A D S b.val z) p) :
    appendLiftCochain A D b w x y z p (f + g) =
      appendLiftCochain A D b w x y z p f + appendLiftCochain A D b w x y z p g := by
  simp only [appendLiftCochain, map_add]
  rw [Cochain.comp_add _ _ _ (zero_add p)]
  exact Cochain.add_comp _ _ _ (add_zero p)

/-- 左語の後方cochainによる項は、短い語での項の持ち上げに等しい。 -/
lemma appendLiftCochain_left {S : Set D} (b : S) (w : Word S) (x y z : D) (p : ℤ)
    (f : Cochain (term A D w b.val y) (internalHom A D S b.val y) p) :
    ((tensorRightHom (internalHom A D S y z) (term A D (b :: w) x y)
      (internalHom A D S x y)).f p (prefixTailCochain A D b w x y p f)).comp
      (Cochain.ofHom (internalComposition A D S x y z)) (add_zero p) =
    appendLiftCochain A D b w x y z p
      (((tensorRightHom (internalHom A D S y z) (term A D w b.val y)
        (internalHom A D S b.val y)).f p f).comp
          (Cochain.ofHom (internalComposition A D S b.val y z)) (add_zero p)) := by
  rw [prefixTailCochain, tensorRightHom_cochain_comp, tensorRightHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp,
    internalComposition_prefixPath]
  rw [appendLiftCochain, tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    tensorLeftHom_cochain_comp, tensorLeftHom_ofHom]
  have h := prefixTensor_cochain_middle (homObject A D x b.val) (epsilonComplex A)
    (term A D w b.val y) (internalHom A D S b.val y) (internalHom A D S y z) p f
  simp only [term_cons, whiskerLeft_comp, Cochain.ofHom_comp,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.comp_assoc_of_second_is_zero_cochain] at h ⊢
  rw [h]

/-- 右側cochainによる項も短い語での項の持ち上げに等しい。 -/
lemma appendLiftCochain_right {S : Set D} (b : S) (w : Word S) (x y z : D) (p : ℤ)
    (f : Cochain (internalHom A D S y z) (internalHom A D S y z) p) :
    ((tensorLeftHom (term A D (b :: w) x y) (internalHom A D S y z)
      (internalHom A D S y z)).f p f).comp
      (Cochain.ofHom (appendRight A D (b :: w) x y z)) (add_zero p) =
    appendLiftCochain A D b w x y z p
      (((tensorLeftHom (term A D w b.val y) (internalHom A D S y z)
        (internalHom A D S y z)).f p f).comp
          (Cochain.ofHom (appendRight A D w b.val y z)) (add_zero p)) := by
  rw [appendRight_cons, appendLiftCochain,
    tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    tensorLeftHom_cochain_comp, tensorLeftHom_ofHom]
  have h := prefixTensor_cochain_right (homObject A D x b.val) (epsilonComplex A)
    (term A D w b.val y) (internalHom A D S y z) (internalHom A D S y z) p f
  simp only [term_cons, whiskerLeft_comp, Cochain.ofHom_comp,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.comp_assoc_of_second_is_zero_cochain] at h ⊢
  rw [h]

end SerrePositivity.DifferentialGraded.DGQuotient
end

end AppendLiftCochain

/-! ## AppendErasureRecursion（旧 SerrePositivity/DifferentialGraded/Quotient/AppendErasureRecursion.lean） -/

/-! # 非空左pathの連結後の消去作用素の再帰式 -/

@[expose] public section AppendErasureRecursion

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 非空左pathの連結後の消去は、先頭ε消去と短いpathの消去の持ち上げの和。 -/
lemma appendRight_erasure_cons {S : Set D} (b : S) (w : Word S) (x y z : D) :
    (Cochain.ofHom (appendRight A D (b :: w) x y z)).comp (erasure A D S x z)
      (zero_add 1) =
    ((tensorRightHom (internalHom A D S y z) (term A D (b :: w) x y) (term A D w x y)).f 1
      (eraseFirst A D b w x y)).comp (Cochain.ofHom (appendRight A D w x y z)) (add_zero 1) +
    appendLiftCochain A D b w x y z 1
      ((Cochain.ofHom (appendRight A D w b.val y z)).comp (erasure A D S b.val z)
        (zero_add 1)) := by
  let sigma := (α_ (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)
    (internalHom A D S y z)).hom ≫ (homObject A D x b.val) ◁
      (α_ (epsilonComplex A) (term A D w b.val y) (internalHom A D S y z)).hom
  let tau := (homObject A D x b.val) ◁ ((epsilonComplex A) ◁ appendRight A D w b.val y z)
  have hc : appendRight A D (b :: w) x y z =
      (sigma ≫ tau) ≫ prefixPath A D b x z := by
    rw [appendRight_cons]
    simp only [sigma, tau, whiskerLeft_comp, Category.assoc]
  have hh : ((Cochain.ofHom (sigma ≫ tau)).comp
      (eraseMiddle A (homObject A D x b.val) (internalHom A D S b.val z)) (zero_add 1)).comp
      (Cochain.ofHom (internalPrepend A D S x b.val z)) (add_zero 1) =
    ((tensorRightHom (internalHom A D S y z) (term A D (b :: w) x y) (term A D w x y)).f 1
      (eraseFirst A D b w x y)).comp (Cochain.ofHom (appendRight A D w x y z)) (add_zero 1) := by
    simpa only [sigma, tau, Category.assoc] using appendRight_eraseFirst A D b w x y z
  rw [hc, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain, prefixPath_erasure]
  rw [Cochain.comp_add _ _ _ (zero_add 1),
    ← Cochain.comp_assoc_of_first_is_zero_cochain, hh]
  congr 1
  simp only [appendLiftCochain, sigma, tau, tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    term_cons, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain]

end SerrePositivity.DifferentialGraded.DGQuotient
end

end AppendErasureRecursion

/-! ## AppendErasure（旧 SerrePositivity/DifferentialGraded/Quotient/AppendErasure.lean） -/

/-! # 左有限pathを固定した連結のε消去Leibniz則 -/

@[expose] public section AppendErasure

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全右pathへの連結に対する、左右のε消去のLeibniz則。 -/
lemma appendRight_erasure {S : Set D} (w : Word S) (x y z : D) :
    (Cochain.ofHom (appendRight A D w x y z)).comp (erasure A D S x z) (zero_add 1) =
    ((tensorRightHom (internalHom A D S y z) (term A D w x y)
      (internalHom A D S x y)).f 1 (eraseRow A D w x y)).comp
      (Cochain.ofHom (internalComposition A D S x y z)) (add_zero 1) +
    ((tensorLeftHom (term A D w x y) (internalHom A D S y z)
      (internalHom A D S y z)).f 1 (erasure A D S y z)).comp
      (Cochain.ofHom (appendRight A D w x y z)) (add_zero 1) := by
  induction w generalizing x with
  | nil =>
    rw [appendRight_nil, eraseRow_nil, map_zero, Cochain.zero_comp, zero_add]
    exact internalPrepend_erasure A D S x y z
  | cons b w ih =>
    rw [appendRight_erasure_cons, ih b.val, appendLiftCochain_add,
      ← appendLiftCochain_left, ← appendLiftCochain_right, eraseRow_cons, map_add]
    rw [Cochain.add_comp _ _ _ (add_zero 1)]
    rw [tensorRightHom_cochain_comp, tensorRightHom_ofHom,
      Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp,
      internalComposition_left_ι]
    exact (add_assoc _ _ _).symm

end SerrePositivity.DifferentialGraded.DGQuotient
end

end AppendErasure

/-! ## AppendRightAssociativity（旧 SerrePositivity/DifferentialGraded/Quotient/AppendRightAssociativity.lean） -/

/-! # 任意左pathと二つの全右pathの連結の結合則 -/

@[expose] public section AppendRightAssociativity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma appendRight_assoc {S : Set D} (w : Word S) (x y z t : D) :
    (appendRight A D w x y z ▷ internalHom A D S z t) ≫ internalComposition A D S x z t =
    (α_ (term A D w x y) (internalHom A D S y z) (internalHom A D S z t)).hom ≫
      (term A D w x y) ◁ internalComposition A D S y z t ≫ appendRight A D w x y t := by
  induction w generalizing x with
  | nil =>
    simpa only [appendRight_nil, term_nil] using internalComposition_prepend A D S x y z t
  | cons b w ih =>
    have he := tensorCarry_assoc (epsilonComplex A) (term A D w b.val y)
      (internalHom A D S y z) (internalHom A D S z t) (internalHom A D S b.val z)
      (internalHom A D S b.val t) (internalHom A D S y t)
      (appendRight A D w b.val y z) (internalComposition A D S b.val z t)
      (internalComposition A D S y z t) (appendRight A D w b.val y t) (ih b.val)
    have hk := tensorCarry_assoc (homObject A D x b.val)
      (epsilonComplex A ⊗ term A D w b.val y) (internalHom A D S y z)
      (internalHom A D S z t) (epsilonComplex A ⊗ internalHom A D S b.val z)
      (epsilonComplex A ⊗ internalHom A D S b.val t) (internalHom A D S y t)
      ((α_ (epsilonComplex A) (term A D w b.val y) (internalHom A D S y z)).hom ≫
        (epsilonComplex A) ◁ appendRight A D w b.val y z)
      ((α_ (epsilonComplex A) (internalHom A D S b.val z) (internalHom A D S z t)).hom ≫
        (epsilonComplex A) ◁ internalComposition A D S b.val z t)
      (internalComposition A D S y z t)
      ((α_ (epsilonComplex A) (term A D w b.val y) (internalHom A D S y t)).hom ≫
        (epsilonComplex A) ◁ appendRight A D w b.val y t) he
    have hp := congrArg (fun f => f ≫ prefixPath A D b x t) hk
    simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc] at hp
    rw [appendRight_cons]
    simp only [comp_whiskerRight, Category.assoc]
    rw [internalComposition_prefixPath]
    simpa only [appendRight_cons, term_cons, whiskerLeft_comp, comp_whiskerRight,
      Category.assoc] using hp

end SerrePositivity.DifferentialGraded.DGQuotient
end

end AppendRightAssociativity
