module

public import SerrePositivity.DifferentialGraded.Resolution.Cells.Append.BoundaryCompatibility
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Append.Recursion
public import SerrePositivity.DifferentialGraded.Complexes.UnitorCochainNaturality
public import SerrePositivity.DifferentialGraded.Complexes.RightUnitorEvaluation
public import SerrePositivity.DifferentialGraded.Complexes.TensorRightTwoCoproductExt
public import SerrePositivity.DifferentialGraded.Complexes.TensorCompositionAssociativity
public import SerrePositivity.DifferentialGraded.Functor.Basic
public import SerrePositivity.DifferentialGraded.Complexes.CoproductSubfamily
public import SerrePositivity.DifferentialGraded.Complexes.PerturbationRestriction
public import SerrePositivity.DifferentialGraded.Complexes.PerturbationMap
public import SerrePositivity.DifferentialGraded.Tensor.Graded

/-!
# Resolution.Cells.Length

## 概要
11 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

universe u v w

/-! ## Identity（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/Identity.lean） -/

/-! # cell付加の最終Hom合成：Identity

## 概要
cell付加の最終Hom合成：Identity。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section Identity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

/-- 元の恒等射を最終Homへ入れた閉次数0の単位。 -/
def attachedIdentity (x : D) : 𝟙_ (Complex A) ⟶ C.attachedHom A D I x x :=
  eId (Complex A) x ≫ C.originalHomInclusion A D I x x

lemma attachedIdentity_f (x : D) (n : ℤ) :
    (C.attachedIdentity A D I x).f n = (C.internalIdentity A D I x).f n := rfl

lemma attachedComposition_left_unit (x y : D) :
    (λ_ (C.attachedHom A D I x y)).inv ≫ C.attachedIdentity A D I x ▷ C.attachedHom A D I x y ≫
      C.attachedComposition A D I x x y = 𝟙 _ := by
  apply chain_ext_apply
  intro n a
  simp only [chain_comp_apply]
  rw [complexLeftUnitor_inv_apply, whiskerRight_apply, attachedComposition_f, attachedIdentity_f]
  have h := congrArg (fun f : C.internalHom A D I x y ⟶ C.internalHom A D I x y => f.f n a)
    (C.internalComposition_left_unit A D I x y)
  change (C.internalComposition A D I x x y).f n
    ((C.internalIdentity A D I x ▷ C.internalHom A D I x y).f n
      ((λ_ (C.internalHom A D I x y)).inv.f n a)) = a at h
  rw [complexLeftUnitor_inv_apply, whiskerRight_apply] at h
  exact h

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end Identity

/-! ## RightIdentity（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/RightIdentity.lean） -/

/-! # cell付加の最終Hom合成：RightIdentity

## 概要
cell付加の最終Hom合成：RightIdentity。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RightIdentity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

lemma attachedComposition_right_unit (x y : D) :
    (ρ_ (C.attachedHom A D I x y)).inv ≫ C.attachedHom A D I x y ◁ C.attachedIdentity A D I y ≫
      C.attachedComposition A D I x y y = 𝟙 _ := by
  apply chain_ext_apply
  intro n a
  simp only [chain_comp_apply]
  rw [complexRightUnitor_inv_apply, whiskerLeft_apply, attachedComposition_f, attachedIdentity_f]
  have h := congrArg (fun f : C.internalHom A D I x y ⟶ C.internalHom A D I x y => f.f n a)
    (C.internalComposition_right_unit A D I x y)
  change (C.internalComposition A D I x y y).f n
    ((C.internalHom A D I x y ◁ C.internalIdentity A D I y).f n
      ((ρ_ (C.internalHom A D I x y)).inv.f n a)) = a at h
  rw [complexRightUnitor_inv_apply, whiskerLeft_apply] at h
  exact h

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end RightIdentity

/-! ## InternalAssociativity（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/InternalAssociativity.lean） -/

/-! # 任意次数cell path：InternalAssociativity

## 概要
任意次数cell path：InternalAssociativity。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section InternalAssociativity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

lemma internalComposition_assoc (x y z t : D) :
    (C.internalComposition A D I x y z ▷ C.internalHom A D I z t) ≫
      C.internalComposition A D I x z t =
    (α_ (C.internalHom A D I x y) (C.internalHom A D I y z) (C.internalHom A D I z t)).hom ≫
      C.internalHom A D I x y ◁ C.internalComposition A D I y z t ≫
        C.internalComposition A D I x y t := by
  apply tensorRightTwoCoproduct_hom_ext (fun w : List I => C.term A D I w x y)
    (C.internalHom A D I y z) (C.internalHom A D I z t) (C.internalHom A D I x t)
  intro w
  change ((C.inclusion A D I w x y ▷ C.internalHom A D I y z) ▷ C.internalHom A D I z t) ≫
      (C.internalComposition A D I x y z ▷ C.internalHom A D I z t) ≫
        C.internalComposition A D I x z t = _
  rw [← comp_whiskerRight_assoc, internalComposition_left_inclusion,
    associator_naturality_left_assoc, ← whisker_exchange_assoc]
  change (C.appendRight A D I w x y z ▷ C.internalHom A D I z t) ≫
      C.internalComposition A D I x z t =
    (α_ (C.term A D I w x y) (C.internalHom A D I y z) (C.internalHom A D I z t)).hom ≫
      (C.term A D I w x y) ◁ C.internalComposition A D I y z t ≫
        (C.inclusion A D I w x y ▷ C.internalHom A D I y t) ≫ C.internalComposition A D I x y t
  rw [internalComposition_left_inclusion, appendRight_assoc]

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end InternalAssociativity

/-! ## Associativity（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/Associativity.lean） -/

/-! # cell付加の最終Hom合成：Associativity

## 概要
cell付加の最終Hom合成：Associativity。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section Associativity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

lemma attachedComposition_assoc (x y z t : D) :
    (C.attachedComposition A D I x y z ▷ C.attachedHom A D I z t) ≫
      C.attachedComposition A D I x z t =
    (α_ (C.attachedHom A D I x y) (C.attachedHom A D I y z) (C.attachedHom A D I z t)).hom ≫
      C.attachedHom A D I x y ◁ C.attachedComposition A D I y z t ≫
        C.attachedComposition A D I x y t := by
  apply tensorComposition_assoc_of_apply
  intro p q r n hn a b c
  simp only [attachedComposition_apply]
  exact tensorComposition_assoc_apply
    (C.internalHom A D I x y) (C.internalHom A D I y z) (C.internalHom A D I z t)
    (C.internalHom A D I x z) (C.internalHom A D I y t) (C.internalHom A D I x t)
    (C.internalComposition A D I x y z) (C.internalComposition A D I x z t)
    (C.internalComposition A D I y z t) (C.internalComposition A D I x y t)
    (C.internalComposition_assoc A D I x y z t) p q r n hn a b c

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end Associativity

/-! ## Category（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/Category.lean） -/

/-! # 指定境界を持つ任意次数cell付加の主豊穣dg圏

## 概要
対象を元のdg圏と区別して、Homの追加微分を持つ別の豊穣構造を登録する。
cell生成元の境界式・増大・K-flat filtrationは後続で扱う。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section Category

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]

/-- cell族と結び付けた対象型。元のDの豊穣instanceは変更しない。 -/
structure Objects (_C : Family A D I) where
  val : D

variable (C : Family A D I)

def objectEquiv : D ≃ C.Objects A D I where
  toFun x := ⟨x⟩
  invFun x := x.val
  left_inv _ := rfl
  right_inv _ := rfl

instance objectsSmall [Small.{u} D] : Small.{u} (C.Objects A D I) :=
  small_of_injective (f := fun x : C.Objects A D I => x.val) (by
    rintro ⟨x⟩ ⟨y⟩ h
    cases h
    rfl)

/-- 追加微分後のHom・閉単位・合成と三つの圏法則によるMathlib豊穣構造。 -/
instance attachedDGCategory : DGCategory A (C.Objects A D I) :=
  ofHomObjects A (C.Objects A D I)
    (fun x y => C.attachedHom A D I x.val y.val)
    (fun x => C.attachedIdentity A D I x.val)
    (fun x y z => C.attachedComposition A D I x.val y.val z.val)
    (fun x y => C.attachedComposition_left_unit A D I x.val y.val)
    (fun x y => C.attachedComposition_right_unit A D I x.val y.val)
    (fun a b c d => by rw [attachedComposition_assoc, Iso.inv_hom_id_assoc])

/-- 元のHomを空pathへ入れるdg関手。 -/
def embedding : DGFunctor A D (C.Objects A D I) where
  obj x := ⟨x⟩
  map x y := C.originalHomInclusion A D I x y
  map_id _x := rfl
  map_comp x y z := (C.attachedComposition_original A D I x y z).symm

/-- 豊穣順合成と通常順dg合成のKoszul符号の一致。 -/
lemma attachedComposition_eq_signed_compose (x y z : D) (p q n : ℤ) (hn : p + q = n)
    (f : (C.attachedHom A D I x y).X p) (g : (C.attachedHom A D I y z).X q) :
    (C.attachedComposition A D I x y z).f n
      (ιTensorObj (C.attachedHom A D I x y) (C.attachedHom A D I y z) p q n hn (f ⊗ₜ[A] g)) =
    (p * q).negOnePow • compose A (x := (⟨x⟩ : C.Objects A D I))
      (y := (⟨y⟩ : C.Objects A D I)) (z := (⟨z⟩ : C.Objects A D I)) g f hn :=
  forward_eq_signed_compose A (D := C.Objects A D I)
    (x := ⟨x⟩) (y := ⟨y⟩) (z := ⟨z⟩) f g hn

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end Category

/-! ## LengthBoundary（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/LengthBoundary.lean） -/

/-! # path長上限による内部Homと指定境界置換の制限

## 概要
path長上限による内部Homと指定境界置換の制限。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section LengthBoundary

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I)

def lengthSet (n : ℕ) : Set (List I) := {w | w.length ≤ n}

abbrev lengthInternalHom (n : ℕ) (x y : D) : Complex A :=
  ComplexCoproduct.subfamily (fun w => C.term A D I w x y) (lengthSet I n)

def lengthInclusion (n : ℕ) (x y : D) :
    C.lengthInternalHom A D I n x y ⟶ C.internalHom A D I x y :=
  ComplexCoproduct.inclusion (fun w => C.term A D I w x y) (lengthSet I n)

def lengthProjection (n : ℕ) (x y : D) :
    C.internalHom A D I x y ⟶ C.lengthInternalHom A D I n x y :=
  ComplexCoproduct.projection (fun w => C.term A D I w x y) (lengthSet I n)

lemma lengthInclusion_projection (n : ℕ) (x y : D) :
    C.lengthInclusion A D I n x y ≫ C.lengthProjection A D I n x y = 𝟙 _ :=
  ComplexCoproduct.inclusion_projection _ _

def lengthReplacement (n : ℕ) (x y : D) :
    Cochain (C.lengthInternalHom A D I n x y) (C.lengthInternalHom A D I n x y) 1 :=
  ((Cochain.ofHom (C.lengthInclusion A D I n x y)).comp
    (C.replacement A D I x y) (zero_add 1)).comp
    (Cochain.ofHom (C.lengthProjection A D I n x y)) (add_zero 1)

lemma replaceSummand_length_projection_inclusion (n : ℕ) (x y : D)
    (w : List I) (hw : w.length ≤ n) (j : ℕ) :
    (C.replaceSummand A D I w j x y).comp
      (Cochain.ofHom (C.lengthProjection A D I n x y ≫ C.lengthInclusion A D I n x y))
        (add_zero 1) = C.replaceSummand A D I w j x y := by
  have hj : w.eraseIdx j ∈ lengthSet I n := (List.length_eraseIdx_le w j).trans hw
  have h : C.inclusion A D I (w.eraseIdx j) x y ≫
      (C.lengthProjection A D I n x y ≫ C.lengthInclusion A D I n x y) =
      C.inclusion A D I (w.eraseIdx j) x y := by
    change Sigma.ι (fun w => C.term A D I w x y) (w.eraseIdx j) ≫
      (ComplexCoproduct.projection _ (lengthSet I n) ≫
        ComplexCoproduct.inclusion _ (lengthSet I n)) = _
    rw [← Category.assoc, ComplexCoproduct.ι_projection_mem
      (fun w : List I => C.term A D I w x y) (lengthSet I n) (w.eraseIdx j) hj]
    exact ComplexCoproduct.ι_inclusion (fun w : List I => C.term A D I w x y)
      (lengthSet I n) ⟨w.eraseIdx j, hj⟩
  rw [replaceSummand, Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, h]

lemma replaceRow_length_projection_inclusion (n : ℕ) (x y : D)
    (w : List I) (hw : w.length ≤ n) :
    (C.replaceRow A D I w x y).comp
      (Cochain.ofHom (C.lengthProjection A D I n x y ≫ C.lengthInclusion A D I n x y))
        (add_zero 1) = C.replaceRow A D I w x y := by
  rw [replaceRow]
  let R : Cochain (C.term A D I w x y) (C.internalHom A D I x y) 1 →+
      Cochain (C.term A D I w x y) (C.internalHom A D I x y) 1 :=
    { toFun := fun f => f.comp (Cochain.ofHom
        (C.lengthProjection A D I n x y ≫ C.lengthInclusion A D I n x y)) (add_zero 1)
      map_zero' := Cochain.zero_comp _ _
      map_add' := fun f g => Cochain.add_comp f g _ _ }
  change R (∑ j ∈ Finset.range w.length, C.replaceSummand A D I w j x y) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact C.replaceSummand_length_projection_inclusion A D I n x y w hw j

lemma lengthReplacement_inclusion (n : ℕ) (x y : D) :
    (Cochain.ofHom (C.lengthInclusion A D I n x y)).comp
      (C.replacement A D I x y) (zero_add 1) =
    (C.lengthReplacement A D I n x y).comp
      (Cochain.ofHom (C.lengthInclusion A D I n x y)) (add_zero 1) := by
  rw [lengthReplacement, Cochain.comp_assoc_of_third_is_zero_cochain,
    ← Cochain.ofHom_comp]
  apply ComplexCoproduct.cochain_ext
  intro w
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]
  have h : Sigma.ι (fun w : lengthSet I n => C.term A D I w.val x y) w ≫
      C.lengthInclusion A D I n x y = C.inclusion A D I w.val x y :=
    ComplexCoproduct.ι_inclusion _ _ w
  rw [h, replacement_precomp, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, h, replacement_precomp]
  exact (C.replaceRow_length_projection_inclusion A D I n x y w.val w.property).symm

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end LengthBoundary

/-! ## LengthFiltration（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/LengthFiltration.lean） -/

/-! # path長上限で切った最終Hom複体とその包含

## 概要
path長上限で切った最終Hom複体とその包含。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section LengthFiltration

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I)

lemma lengthReplacement_closed (n : ℕ) (x y : D) :
    δ 1 2 (C.lengthReplacement A D I n x y) = 0 :=
  perturbation_closed_of_inclusion (C.lengthInclusion A D I n x y)
    (C.lengthProjection A D I n x y) (C.lengthInclusion_projection A D I n x y)
    (C.lengthReplacement A D I n x y) (C.replacement A D I x y)
    (C.replacement_closed A D I x y) (C.lengthReplacement_inclusion A D I n x y)

lemma lengthReplacement_square_zero (n : ℕ) (x y : D) :
    (C.lengthReplacement A D I n x y).comp (C.lengthReplacement A D I n x y)
      (show (1 : ℤ) + 1 = 2 by omega) = 0 :=
  perturbation_square_zero_of_inclusion (C.lengthInclusion A D I n x y)
    (C.lengthProjection A D I n x y) (C.lengthInclusion_projection A D I n x y)
    (C.lengthReplacement A D I n x y) (C.replacement A D I x y)
    (C.replacement_square_zero A D I x y) (C.lengthReplacement_inclusion A D I n x y)

/-- 内部微分だけでなく、指定境界置換を含む長さn以下のpath複体。 -/
def lengthHom (n : ℕ) (x y : D) : Complex A :=
  perturbComplex (C.lengthInternalHom A D I n x y) (C.lengthReplacement A D I n x y)
    (C.lengthReplacement_closed A D I n x y) (C.lengthReplacement_square_zero A D I n x y)

lemma lengthHom_d (n : ℕ) (x y : D) (i : ℤ) :
    (C.lengthHom A D I n x y).d i (i + 1) =
    (C.lengthInternalHom A D I n x y).d i (i + 1) +
      (C.lengthReplacement A D I n x y).v i (i + 1) rfl :=
  perturbComplex_d _ _ _ _ _

def lengthHomInclusion (n : ℕ) (x y : D) :
    C.lengthHom A D I n x y ⟶ C.attachedHom A D I x y :=
  perturbMap (C.lengthInclusion A D I n x y)
    (C.lengthReplacement A D I n x y) (C.replacement A D I x y)
    (C.lengthReplacement_closed A D I n x y) (C.replacement_closed A D I x y)
    (C.lengthReplacement_square_zero A D I n x y) (C.replacement_square_zero A D I x y)
    (C.lengthReplacement_inclusion A D I n x y)

lemma lengthHomInclusion_f (n : ℕ) (x y : D) (i : ℤ) :
    (C.lengthHomInclusion A D I n x y).f i = (C.lengthInclusion A D I n x y).f i := rfl

instance lengthHomInclusion_degreewiseMono (n : ℕ) (x y : D) (i : ℤ) :
    Mono ((C.lengthHomInclusion A D I n x y).f i) := by
  let : IsSplitMono ((C.lengthHomInclusion A D I n x y).f i) :=
    ⟨⟨{ retraction := (C.lengthProjection A D I n x y).f i, id := by
           change (C.lengthInclusion A D I n x y).f i ≫
             (C.lengthProjection A D I n x y).f i =
             𝟙 ((C.lengthInternalHom A D I n x y).X i)
           simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
             congrArg (fun f => f.f i) (C.lengthInclusion_projection A D I n x y) }⟩⟩
  infer_instance

instance lengthHomInclusion_mono (n : ℕ) (x y : D) :
    Mono (C.lengthHomInclusion A D I n x y) := by
  apply HomologicalComplex.mono_of_mono_f
  intro i
  infer_instance

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end LengthFiltration

/-! ## LengthTransition（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/LengthTransition.lean） -/

/-! # path長filtrationの遷移射と最終Homへの包含

## 概要
path長filtrationの遷移射と最終Homへの包含。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section LengthTransition

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I)

def lengthInternalMap (m n : ℕ) (x y : D) :
    C.lengthInternalHom A D I m x y ⟶ C.lengthInternalHom A D I n x y :=
  ComplexCoproduct.select (fun w => C.term A D I w x y) (lengthSet I m) (lengthSet I n)

lemma lengthInternalMap_inclusion (m n : ℕ) (h : m ≤ n) (x y : D) :
    C.lengthInternalMap A D I m n x y ≫ C.lengthInclusion A D I n x y =
      C.lengthInclusion A D I m x y :=
  ComplexCoproduct.select_inclusion _ _ _ (fun _ hw => hw.trans h)

lemma lengthInternalMap_replacement (m n : ℕ) (h : m ≤ n) (x y : D) :
    (Cochain.ofHom (C.lengthInternalMap A D I m n x y)).comp
      (C.lengthReplacement A D I n x y) (zero_add 1) =
    (C.lengthReplacement A D I m x y).comp
      (Cochain.ofHom (C.lengthInternalMap A D I m n x y)) (add_zero 1) := by
  apply cochain_postcomp_injective_of_retraction
    (C.lengthInclusion A D I n x y) (C.lengthProjection A D I n x y)
    (C.lengthInclusion_projection A D I n x y) _ 1
  dsimp only
  rw [Cochain.comp_assoc_of_third_is_zero_cochain, ← lengthReplacement_inclusion,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    lengthInternalMap_inclusion A D I C m n h,
    lengthReplacement_inclusion, Cochain.comp_assoc_of_third_is_zero_cochain,
    ← Cochain.ofHom_comp, lengthInternalMap_inclusion A D I C m n h]

def lengthMap (m n : ℕ) (h : m ≤ n) (x y : D) :
    C.lengthHom A D I m x y ⟶ C.lengthHom A D I n x y :=
  perturbMap (C.lengthInternalMap A D I m n x y)
    (C.lengthReplacement A D I m x y) (C.lengthReplacement A D I n x y)
    (C.lengthReplacement_closed A D I m x y) (C.lengthReplacement_closed A D I n x y)
    (C.lengthReplacement_square_zero A D I m x y) (C.lengthReplacement_square_zero A D I n x y)
    (C.lengthInternalMap_replacement A D I m n h x y)

lemma lengthMap_f (m n : ℕ) (h : m ≤ n) (x y : D) (i : ℤ) :
    (C.lengthMap A D I m n h x y).f i = (C.lengthInternalMap A D I m n x y).f i := rfl

lemma lengthMap_inclusion (m n : ℕ) (h : m ≤ n) (x y : D) :
    C.lengthMap A D I m n h x y ≫ C.lengthHomInclusion A D I n x y =
      C.lengthHomInclusion A D I m x y := by
  apply HomologicalComplex.Hom.ext
  funext i
  change (C.lengthInternalMap A D I m n x y).f i ≫
    (C.lengthInclusion A D I n x y).f i = (C.lengthInclusion A D I m x y).f i
  exact congrArg (fun f => f.f i) (C.lengthInternalMap_inclusion A D I m n h x y)

lemma lengthMap_self (n : ℕ) (x y : D) :
    C.lengthMap A D I n n le_rfl x y = 𝟙 _ := by
  apply (cancel_mono (C.lengthHomInclusion A D I n x y)).1
  rw [lengthMap_inclusion, Category.id_comp]

lemma lengthMap_comp (l m n : ℕ) (hlm : l ≤ m) (hmn : m ≤ n) (x y : D) :
    C.lengthMap A D I l m hlm x y ≫ C.lengthMap A D I m n hmn x y =
      C.lengthMap A D I l n (hlm.trans hmn) x y := by
  apply (cancel_mono (C.lengthHomInclusion A D I n x y)).1
  rw [Category.assoc, lengthMap_inclusion, lengthMap_inclusion, lengthMap_inclusion]

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end LengthTransition

/-! ## LengthGraded（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/LengthGraded.lean） -/

/-! # 固定長pathの次数付き商：境界置換は商で消える

## 概要
固定長pathの次数付き商：境界置換は商で消える。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section LengthGraded

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I)

def exactLengthSet (n : ℕ) : Set (List I) := {w | w.length = n}

/-- 固定長pathには内部微分だけを置く。 -/
abbrev exactLengthHom (n : ℕ) (x y : D) : Complex A :=
  ComplexCoproduct.subfamily (fun w => C.term A D I w x y) (exactLengthSet I n)

def exactLengthProjection (n : ℕ) (x y : D) :
    C.internalHom A D I x y ⟶ C.exactLengthHom A D I n x y :=
  ComplexCoproduct.projection (fun w => C.term A D I w x y) (exactLengthSet I n)

lemma replaceSummand_exactLength_projection (n : ℕ) (x y : D)
    (w : List I) (hw : w.length ≤ n) (j : ℕ) (hj : j < w.length) :
    (C.replaceSummand A D I w j x y).comp
      (Cochain.ofHom (C.exactLengthProjection A D I n x y)) (add_zero 1) = 0 := by
  have hn : w.eraseIdx j ∉ exactLengthSet I n := by
    change (w.eraseIdx j).length ≠ n
    rw [List.length_eraseIdx_of_lt hj]
    omega
  have h : C.inclusion A D I (w.eraseIdx j) x y ≫
      C.exactLengthProjection A D I n x y = 0 :=
    ComplexCoproduct.ι_projection_not_mem (fun w : List I => C.term A D I w x y)
      (exactLengthSet I n) (w.eraseIdx j) hn
  rw [replaceSummand, Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp,
    h, Cochain.ofHom_zero, Cochain.comp_zero]

lemma replaceRow_exactLength_projection (n : ℕ) (x y : D) (w : List I) (hw : w.length ≤ n) :
    (C.replaceRow A D I w x y).comp
      (Cochain.ofHom (C.exactLengthProjection A D I n x y)) (add_zero 1) = 0 := by
  let R : Cochain (C.term A D I w x y) (C.internalHom A D I x y) 1 →+
      Cochain (C.term A D I w x y) (C.exactLengthHom A D I n x y) 1 :=
    { toFun := fun f => f.comp (Cochain.ofHom (C.exactLengthProjection A D I n x y)) (add_zero 1)
      map_zero' := Cochain.zero_comp _ _
      map_add' := fun f g => Cochain.add_comp f g _ _ }
  change R (∑ j ∈ Finset.range w.length, C.replaceSummand A D I w j x y) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  exact C.replaceSummand_exactLength_projection A D I n x y w hw j (Finset.mem_range.mp hj)

def lengthInternalQuotient (n : ℕ) (x y : D) :
    C.lengthInternalHom A D I n x y ⟶ C.exactLengthHom A D I n x y :=
  ComplexCoproduct.select (fun w => C.term A D I w x y) (lengthSet I n) (exactLengthSet I n)

lemma lengthReplacement_quotient_zero (n : ℕ) (x y : D) :
    (C.lengthReplacement A D I n x y).comp
      (Cochain.ofHom (C.lengthInternalQuotient A D I n x y)) (add_zero 1) = 0 := by
  change (C.lengthReplacement A D I n x y).comp
    (Cochain.ofHom (C.lengthInclusion A D I n x y ≫ C.exactLengthProjection A D I n x y))
      (add_zero 1) = 0
  rw [Cochain.ofHom_comp, ← Cochain.comp_assoc_of_third_is_zero_cochain,
    ← lengthReplacement_inclusion]
  apply ComplexCoproduct.cochain_ext
  intro w
  rw [Cochain.comp_zero, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]
  have h : Sigma.ι (fun w : lengthSet I n => C.term A D I w.val x y) w ≫
      C.lengthInclusion A D I n x y = C.inclusion A D I w.val x y :=
    ComplexCoproduct.ι_inclusion _ _ w
  rw [h, replacement_precomp]
  exact C.replaceRow_exactLength_projection A D I n x y w.val w.property

/-- 最終微分を持つ長さn以下のpathから、固定長nの内部複体へのchain map。 -/
def lengthQuotient (n : ℕ) (x y : D) :
    C.lengthHom A D I n x y ⟶ C.exactLengthHom A D I n x y :=
  perturbSourceMap (C.lengthInternalHom A D I n x y) (C.exactLengthHom A D I n x y)
    (C.lengthReplacement A D I n x y) (C.lengthReplacement_closed A D I n x y)
    (C.lengthReplacement_square_zero A D I n x y)
    (Cochain.ofHom (C.lengthInternalQuotient A D I n x y)) (by
      rw [δ_ofHom, lengthReplacement_quotient_zero])

lemma lengthQuotient_f (n : ℕ) (x y : D) (i : ℤ) :
    (C.lengthQuotient A D I n x y).f i = (C.lengthInternalQuotient A D I n x y).f i := rfl

lemma exactLengthHom_kFlat (hD : localHomKFlat A D) (n : ℕ) (x y : D) :
    complexKFlat A (C.exactLengthHom A D I n x y) := by
  have : HasExactColimitsOfShape (Discrete (exactLengthSet I n)) (ModuleCat.{u} A) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
      (Discrete.equivalence (equivShrink.{u} (exactLengthSet I n)).symm)
  exact complexKFlat_colimit A
    (Discrete.functor fun w : exactLengthSet I n => C.term A D I w.val x y)
    (fun w => C.term_kFlat A D I hD w.as.val x y)

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end LengthGraded

/-! ## LengthSplit（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/LengthSplit.lean） -/

/-! # path長filtrationの次数ごとの分裂と有限段階のK-flat性

## 概要
path長filtrationの次数ごとの分裂と有限段階のK-flat性。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section LengthSplit

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I)

omit [Small.{u} I] in
lemma lengthSet_subset_succ (n : ℕ) : lengthSet I n ⊆ lengthSet I (n + 1) :=
  fun _ h => Nat.le_trans h (Nat.le_succ n)

omit [Small.{u} I] in
lemma exactLengthSet_subset (n : ℕ) : exactLengthSet I n ⊆ lengthSet I n :=
  fun _ h => Nat.le_of_eq h

omit [Small.{u} I] in
lemma lengthSet_disjoint_exact_succ (n : ℕ) : Disjoint (lengthSet I n) (exactLengthSet I (n + 1)) :=
  Set.disjoint_left.mpr (by
    intro w hw ht
    change w.length ≤ n at hw
    change w.length = n + 1 at ht
    omega)

omit [Small.{u} I] in
lemma lengthSet_partition_succ (n : ℕ) :
    lengthSet I (n + 1) ⊆ lengthSet I n ∪ exactLengthSet I (n + 1) := by
  intro w hw
  change w.length ≤ n + 1 at hw
  change w.length ≤ n ∨ w.length = n + 1
  omega

lemma lengthMap_quotient (n : ℕ) (x y : D) :
    C.lengthMap A D I n (n + 1) (Nat.le_succ n) x y ≫
      C.lengthQuotient A D I (n + 1) x y = 0 := by
  have h := ComplexCoproduct.select_comp (fun w => C.term A D I w x y)
    (lengthSet I n) (lengthSet I (n + 1)) (exactLengthSet I (n + 1)) (lengthSet_subset_succ I n)
  rw [ComplexCoproduct.select_zero _ _ _ (lengthSet_disjoint_exact_succ I n)] at h
  apply HomologicalComplex.Hom.ext
  funext i
  change ((ComplexCoproduct.select (fun w => C.term A D I w x y)
    (lengthSet I n) (lengthSet I (n + 1))).f i) ≫
    ((ComplexCoproduct.select (fun w => C.term A D I w x y)
      (lengthSet I (n + 1)) (exactLengthSet I (n + 1))).f i) = 0
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
    congrArg (fun f => f.f i) h

def lengthShortComplex (n : ℕ) (x y : D) : ShortComplex (Complex A) :=
  ShortComplex.mk (C.lengthMap A D I n (n + 1) (Nat.le_succ n) x y)
    (C.lengthQuotient A D I (n + 1) x y) (C.lengthMap_quotient A D I n x y)

def lengthSplitting (n : ℕ) (x y : D) (i : ℤ) :
    ((C.lengthShortComplex A D I n x y).map
      (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i)).Splitting where
  r := (ComplexCoproduct.select (fun w => C.term A D I w x y)
    (lengthSet I (n + 1)) (lengthSet I n)).f i
  s := (ComplexCoproduct.select (fun w => C.term A D I w x y)
    (exactLengthSet I (n + 1)) (lengthSet I (n + 1))).f i
  f_r := by
    change (ComplexCoproduct.select (fun w => C.term A D I w x y)
      (lengthSet I n) (lengthSet I (n + 1))).f i ≫
      (ComplexCoproduct.select (fun w => C.term A D I w x y)
        (lengthSet I (n + 1)) (lengthSet I n)).f i = 𝟙 _
    have h := ComplexCoproduct.select_comp (fun w => C.term A D I w x y)
      (lengthSet I n) (lengthSet I (n + 1)) (lengthSet I n) (lengthSet_subset_succ I n)
    rw [ComplexCoproduct.select_self] at h
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
      congrArg (fun f => f.f i) h
  s_g := by
    change (ComplexCoproduct.select (fun w => C.term A D I w x y)
      (exactLengthSet I (n + 1)) (lengthSet I (n + 1))).f i ≫
      (ComplexCoproduct.select (fun w => C.term A D I w x y)
        (lengthSet I (n + 1)) (exactLengthSet I (n + 1))).f i = 𝟙 _
    have h := ComplexCoproduct.select_comp (fun w => C.term A D I w x y)
      (exactLengthSet I (n + 1)) (lengthSet I (n + 1)) (exactLengthSet I (n + 1))
      (exactLengthSet_subset I (n + 1))
    rw [ComplexCoproduct.select_self] at h
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
      congrArg (fun f => f.f i) h
  id := by
    change
      (ComplexCoproduct.select (fun w => C.term A D I w x y)
        (lengthSet I (n + 1)) (lengthSet I n)).f i ≫
        (ComplexCoproduct.select (fun w => C.term A D I w x y)
          (lengthSet I n) (lengthSet I (n + 1))).f i +
      (ComplexCoproduct.select (fun w => C.term A D I w x y)
        (lengthSet I (n + 1)) (exactLengthSet I (n + 1))).f i ≫
        (ComplexCoproduct.select (fun w => C.term A D I w x y)
          (exactLengthSet I (n + 1)) (lengthSet I (n + 1))).f i = 𝟙 _
    have h := ComplexCoproduct.select_partition (fun w => C.term A D I w x y)
      (lengthSet I n) (exactLengthSet I (n + 1)) (lengthSet I (n + 1))
      (lengthSet_subset_succ I n) (exactLengthSet_subset I (n + 1))
      (lengthSet_disjoint_exact_succ I n) (lengthSet_partition_succ I n)
    simpa only [HomologicalComplex.add_f_apply, HomologicalComplex.comp_f,
      HomologicalComplex.id_f] using congrArg (fun f => f.f i) h

instance lengthQuotient_zero_isIso (x y : D) : IsIso (C.lengthQuotient A D I 0 x y) := by
  have h0 : lengthSet I 0 = exactLengthSet I 0 := by
    ext w
    change w.length ≤ 0 ↔ w.length = 0
    omega
  have hs : IsIso (C.lengthInternalQuotient A D I 0 x y) := by
    change IsIso (ComplexCoproduct.select (fun w => C.term A D I w x y)
      (lengthSet I 0) (exactLengthSet I 0))
    rw [← h0, ComplexCoproduct.select_self]
    infer_instance
  have : ∀ i, IsIso ((C.lengthQuotient A D I 0 x y).f i) := by
    intro i
    change IsIso ((C.lengthInternalQuotient A D I 0 x y).f i)
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

lemma lengthHom_kFlat (hD : localHomKFlat A D) (n : ℕ) (x y : D) :
    complexKFlat A (C.lengthHom A D I n x y) := by
  induction n with
  | zero =>
    exact complexKFlat_of_iso A (asIso (C.lengthQuotient A D I 0 x y))
      (C.exactLengthHom_kFlat A D I hD 0 x y)
  | succ n ih =>
    exact complexKFlat_of_degreewiseSplit A (C.lengthShortComplex A D I n x y)
      (C.lengthSplitting A D I n x y) ih (C.exactLengthHom_kFlat A D I hD (n + 1) x y)

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end LengthSplit

/-! ## LengthColimit（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/LengthColimit.lean） -/

/-! # path長filtrationの網羅性と最終HomのK-flat性

## 概要
path長filtrationの網羅性と最終HomのK-flat性。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section LengthColimit

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I)

omit [Small.{u} I] in
lemma mem_lengthSet_self (w : List I) : w ∈ lengthSet I w.length := Nat.le_refl _

def lengthDiagram (x y : D) : ℕ ⥤ Complex A where
  obj n := C.lengthHom A D I n x y
  map f := C.lengthMap A D I _ _ (leOfHom f) x y
  map_id n := C.lengthMap_self A D I n x y
  map_comp f g := (C.lengthMap_comp A D I _ _ _ (leOfHom f) (leOfHom g) x y).symm

def lengthCocone (x y : D) : Cocone (C.lengthDiagram A D I x y) where
  pt := C.attachedHom A D I x y
  ι :=
    { app := fun n => C.lengthHomInclusion A D I n x y
      naturality := fun m n f => by
        change C.lengthMap A D I m n (leOfHom f) x y ≫ C.lengthHomInclusion A D I n x y =
          C.lengthHomInclusion A D I m x y ≫ 𝟙 _
        rw [Category.comp_id, lengthMap_inclusion] }

lemma lengthMap_ι (m n : ℕ) (h : m ≤ n) (x y : D) (w : lengthSet I m) :
    Sigma.ι (fun w : lengthSet I m => C.term A D I w.val x y) w ≫
      C.lengthInternalMap A D I m n x y =
    Sigma.ι (fun w : lengthSet I n => C.term A D I w.val x y) ⟨w.val, w.property.trans h⟩ :=
  ComplexCoproduct.ι_select_mem (fun w => C.term A D I w x y)
    (lengthSet I m) (lengthSet I n) w (w.property.trans h)

def lengthEvalIsColimit (x y : D) (i : ℤ) :
    IsColimit ((HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i).mapCocone
      (C.lengthCocone A D I x y)) := by
  let H : IsColimit (Cofan.mk ((C.internalHom A D I x y).X i)
      (fun w : List I => (C.inclusion A D I w x y).f i)) :=
    isColimitOfHasCoproductOfPreservesColimit
      (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i)
      (fun w : List I => C.term A D I w x y)
  let inc (w : List I) : (C.term A D I w x y).X i ⟶ (C.lengthInternalHom A D I w.length x y).X i :=
    (Sigma.ι (fun w : lengthSet I w.length => C.term A D I w.val x y)
      ⟨w, mem_lengthSet_self I w⟩).f i
  let leg (s : Cocone (C.lengthDiagram A D I x y ⋙
      HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i)) (n : ℕ) :
      (C.lengthInternalHom A D I n x y).X i ⟶ s.pt := s.ι.app n
  have hfac (s : Cocone (C.lengthDiagram A D I x y ⋙
      HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i)) (w : List I) :
      (C.inclusion A D I w x y).f i ≫
        H.desc (Cofan.mk s.pt (fun w => inc w ≫ leg s w.length)) =
      inc w ≫ leg s w.length := H.fac _ ⟨w⟩
  refine
    { desc := fun s => H.desc (Cofan.mk s.pt (fun w => inc w ≫ leg s w.length))
      fac := ?_
      uniq := ?_ }
  · intro s n
    apply (isColimitOfHasCoproductOfPreservesColimit
      (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i)
      (fun w : lengthSet I n => C.term A D I w.val x y)).hom_ext
    intro w
    change (Sigma.ι (fun w : lengthSet I n => C.term A D I w.val x y) w.as).f i ≫
      (C.lengthInclusion A D I n x y).f i ≫
        H.desc (Cofan.mk s.pt (fun w => inc w ≫ leg s w.length)) =
      (Sigma.ι (fun w : lengthSet I n => C.term A D I w.val x y) w.as).f i ≫ leg s n
    have hp : Sigma.ι (fun w : lengthSet I n => C.term A D I w.val x y) w.as ≫
        C.lengthInclusion A D I n x y = C.inclusion A D I w.as.val x y :=
      ComplexCoproduct.ι_inclusion (fun w => C.term A D I w x y) (lengthSet I n) w.as
    rw [← Category.assoc, ← HomologicalComplex.comp_f, hp, hfac]
    have hs := s.w (homOfLE w.as.property)
    change (C.lengthInternalMap A D I w.as.val.length n x y).f i ≫ leg s n =
      leg s w.as.val.length at hs
    rw [← hs, ← Category.assoc, ← HomologicalComplex.comp_f]
    exact congrArg (fun f => f.f i ≫ leg s n)
      (C.lengthMap_ι A D I w.as.val.length n w.as.property x y
        ⟨w.as.val, mem_lengthSet_self I w.as.val⟩)
  · intro s m hm
    let m' : (C.internalHom A D I x y).X i ⟶ s.pt := m
    change m' = H.desc (Cofan.mk s.pt (fun w => inc w ≫ leg s w.length))
    apply H.hom_ext
    intro w
    have hn := congrArg (fun f => inc w.as ≫ f) (hm w.as.length)
    change inc w.as ≫ (C.lengthInclusion A D I w.as.length x y).f i ≫ m' =
      inc w.as ≫ leg s w.as.length at hn
    have hi := congrArg (fun f => f.f i)
      (ComplexCoproduct.ι_inclusion (fun w => C.term A D I w x y)
        (lengthSet I w.as.length) ⟨w.as, mem_lengthSet_self I w.as⟩)
    change inc w.as ≫ (C.lengthInclusion A D I w.as.length x y).f i =
      (C.inclusion A D I w.as x y).f i at hi
    rw [← Category.assoc, hi] at hn
    change (C.inclusion A D I w.as x y).f i ≫ m' =
      (C.inclusion A D I w.as x y).f i ≫
        H.desc (Cofan.mk s.pt (fun w => inc w ≫ leg s w.length))
    rw [hfac]
    exact hn

def lengthIsColimit (x y : D) : IsColimit (C.lengthCocone A D I x y) :=
  HomologicalComplex.isColimitOfEval _ _ (C.lengthEvalIsColimit A D I x y)

/-- 追加微分後の最終Homは、path長filtrationとexactな逐次余極限によりK-flat。 -/
lemma attachedHom_kFlat (hD : localHomKFlat A D) (x y : D) :
    complexKFlat A (C.attachedHom A D I x y) := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u} A) := AB5OfSize_of_univLE (ModuleCat.{u} A)
  have h := complexKFlat_colimit A (C.lengthDiagram A D I x y)
    (fun n => C.lengthHom_kFlat A D I hD n x y)
  exact complexKFlat_of_iso A
    ((colimit.isColimit _).coconePointUniqueUpToIso (C.lengthIsColimit A D I x y)).symm h

lemma attachedDGCategory_localHomKFlat (hD : localHomKFlat A D) :
    localHomKFlat A (C.Objects A D I) :=
  fun x y => C.attachedHom_kFlat A D I hD x.val y.val

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end LengthColimit
