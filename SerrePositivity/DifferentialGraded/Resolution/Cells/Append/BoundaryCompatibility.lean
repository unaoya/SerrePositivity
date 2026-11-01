module

public import SerrePositivity.DifferentialGraded.Resolution.Cells.Append.Recursion
public import SerrePositivity.DifferentialGraded.Complexes.Composition
public import SerrePositivity.DifferentialGraded.Complexes.TensorCarryCochain
public import SerrePositivity.DifferentialGraded.Complexes.TensorCarryAssociativity
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Boundary
public import SerrePositivity.DifferentialGraded.Complexes.TensorClosedZero
public import SerrePositivity.DifferentialGraded.Complexes.PrefixTensorCochainAction
public import SerrePositivity.DifferentialGraded.Complexes.PrefixTensorCochainPrecomp

/-!
# Resolution.Cells.Append.BoundaryCompatibility

## 概要
連結と指定境界置換の Leibniz 則・最終微分の整合性をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

universe u v w

/-! ## PrependBoundary（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/PrependBoundary.lean） -/

/-! # 任意次数cell path：PrependBoundary

## 概要
任意次数cell path：PrependBoundary。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section PrependBoundary

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits Preadditive MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

/-- 空pathを左に置く合成の境界置換Leibniz則。左の元のHomには消去項がない。 -/
lemma internalPrepend_replacement (x y z : D) :
    (Cochain.ofHom (C.internalPrepend A D I x y z)).comp (C.replacement A D I x z) (zero_add 1) =
    ((tensorLeftHom (homObject A D x y) (C.internalHom A D I y z)
      (C.internalHom A D I y z)).f 1 (C.replacement A D I y z)).comp
      (Cochain.ofHom (C.internalPrepend A D I x y z)) (add_zero 1) := by
  apply C.tensorLeftPathCochain_ext A D I y z (homObject A D x y) 1
  intro w
  have hb : (Cochain.ofHom ((homObject A D x y) ◁ C.inclusion A D I w y z)).comp
      ((tensorLeftHom (homObject A D x y) (C.internalHom A D I y z)
        (C.internalHom A D I y z)).f 1 (C.replacement A D I y z)) (zero_add 1) =
      (tensorLeftHom (homObject A D x y) (C.term A D I w y z)
        (C.internalHom A D I y z)).f 1 (C.replaceRow A D I w y z) := by
    rw [← tensorLeftHom_ofHom, ← tensorLeftHom_cochain_comp, replacement_precomp]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    internalPrepend_inclusion, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    replacement_precomp, ← Cochain.comp_assoc_of_first_is_zero_cochain, hb]
  exact C.prependMap_replaceRow A D I w x y z

/-- 空pathを左に置く消去Leibniz則の斉次成分。右側の消去には(-1)^pが付く。 -/
lemma internalPrepend_replacement_apply (x y z : D) (p q n : ℤ)
    (hn : p + q = n) (a : (homObject A D x y).X p) (b : (C.internalHom A D I y z).X q) :
    (C.replacement A D I x z).v n (n + 1) rfl
      ((C.internalPrepend A D I x y z).f n
        (ιTensorObj (homObject A D x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b))) =
    p.negOnePow • (C.internalPrepend A D I x y z).f (n + 1)
      (ιTensorObj (homObject A D x y) (C.internalHom A D I y z) p (q + 1) (n + 1)
        (by omega) (a ⊗ₜ[A] (C.replacement A D I y z).v q (q + 1) rfl b)) := by
  have h := congrArg (fun f : Cochain
      (homObject A D x y ⊗ C.internalHom A D I y z) (C.internalHom A D I x z) 1 =>
    f.v n (n + 1) rfl
      (ιTensorObj (homObject A D x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b)))
    (C.internalPrepend_replacement A D I x y z)
  rw [cochain_ofHom_comp_apply, cochain_comp_ofHom_apply,
    tensorLeftHom_apply, chain_units_smul] at h
  simpa only [one_mul] using h

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end PrependBoundary

/-! ## PrependDifferential（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/PrependDifferential.lean） -/

/-! # 任意次数cell path：PrependDifferential

## 概要
任意次数cell path：PrependDifferential。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section PrependDifferential

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits Preadditive MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

/-- 空pathを左に置く合成の、最終微分についてのLeibniz則。 -/
lemma internalPrepend_total_d_apply (x y z : D) (p q n : ℤ)
    (hn : p + q = n) (a : (homObject A D x y).X p) (b : (C.internalHom A D I y z).X q) :
    (C.attachedHom A D I x z).d n (n + 1)
      ((C.internalPrepend A D I x y z).f n
        (ιTensorObj (homObject A D x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b))) =
    (C.internalPrepend A D I x y z).f (n + 1)
      (ιTensorObj (homObject A D x y) (C.internalHom A D I y z) (p + 1) q (n + 1)
        (by omega) ((homObject A D x y).d p (p + 1) a ⊗ₜ[A] b)) +
    p.negOnePow • (C.internalPrepend A D I x y z).f (n + 1)
      (ιTensorObj (homObject A D x y) (C.internalHom A D I y z) p (q + 1) (n + 1)
        (by omega) (a ⊗ₜ[A] (C.attachedHom A D I y z).d q (q + 1) b)) := by
  have hi := ConcreteCategory.congr_hom ((C.internalPrepend A D I x y z).comm n (n + 1))
    (ιTensorObj (homObject A D x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b))
  change (C.internalHom A D I x z).d n (n + 1) (_ : (C.internalHom A D I x z).X n) =
    (C.internalPrepend A D I x y z).f (n + 1)
      ((homObject A D x y ⊗ C.internalHom A D I y z).d n (n + 1)
        (ιTensorObj (homObject A D x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b))) at hi
  have hd := SerrePositivity.cochainTensor_d_apply_ι
    (homObject A D x y) (C.internalHom A D I y z) p q n hn a b
  have hi' := hi.trans (congrArg (fun v :
      (homObject A D x y ⊗ C.internalHom A D I y z).X (n + 1) =>
    (C.internalPrepend A D I x y z).f (n + 1) v) hd)
  clear hi
  have hi := hi'
  rw [map_add, chain_units_smul] at hi
  rw [attachedHom_d, attachedHom_d]
  change (C.internalHom A D I x z).d n (n + 1)
      ((C.internalPrepend A D I x y z).f n
        (ιTensorObj (homObject A D x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b))) +
      (C.replacement A D I x z).v n (n + 1) rfl
        ((C.internalPrepend A D I x y z).f n
          (ιTensorObj (homObject A D x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b))) =
    (C.internalPrepend A D I x y z).f (n + 1)
      (ιTensorObj (homObject A D x y) (C.internalHom A D I y z) (p + 1) q (n + 1)
        (by omega) ((homObject A D x y).d p (p + 1) a ⊗ₜ[A] b)) +
    p.negOnePow • (C.internalPrepend A D I x y z).f (n + 1)
      (ιTensorObj (homObject A D x y) (C.internalHom A D I y z) p (q + 1) (n + 1)
        (by omega) (a ⊗ₜ[A] ((C.internalHom A D I y z).d q (q + 1) b +
          (C.replacement A D I y z).v q (q + 1) rfl b)))
  exact (congrArg₂ (· + ·) hi (C.internalPrepend_replacement_apply A D I x y z p q n hn a b)).trans
    (by
    simp only [TensorProduct.tmul_add, map_add, smul_add]
    abel)

/-- 元のHomは最終Hom複体へ先頭から作用する。これは最終微分に関するchain map。 -/
def attachedPrepend (x y z : D) :
    homObject A D x y ⊗ C.attachedHom A D I y z ⟶ C.attachedHom A D I x z :=
  tensorLift (fun i j n h =>
    ιTensorObj (homObject A D x y) (C.internalHom A D I y z) i j n h ≫
      (C.internalPrepend A D I x y z).f n) (fun i j => by
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro a b
        exact C.internalPrepend_total_d_apply A D I x y z i j (i + j) rfl a b)

lemma attachedPrepend_ι (x y z : D) (i j n : ℤ) (hn : i + j = n) :
    ιTensorObj (homObject A D x y) (C.attachedHom A D I y z) i j n hn ≫
      (C.attachedPrepend A D I x y z).f n =
    ιTensorObj (homObject A D x y) (C.internalHom A D I y z) i j n hn ≫
      (C.internalPrepend A D I x y z).f n :=
  ι_tensorLift _ _ i j n hn

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end PrependDifferential

/-! ## InternalBoundaryHead（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/InternalBoundaryHead.lean） -/

/-! # 全path直和に先頭生成元の指定境界を作用させるcochain

## 概要
全path直和に先頭生成元の指定境界を作用させるcochain。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section InternalBoundaryHead

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

def internalReplaceHead (b : I) (y : D) :
    Cochain (C.generator A D I b ⊗ C.internalHom A D I (C.target b) y)
      (C.internalHom A D I (C.source b) y) 1 :=
  ((tensorRightHom (C.internalHom A D I (C.target b) y) _ _).f 1
    (C.boundaryCochain A D I b)).comp
    (Cochain.ofHom (C.internalPrepend A D I (C.source b) (C.target b) y)) (add_zero 1)

def internalReplaceFirst (b : I) (x y : D) :
    Cochain (homObject A D x (C.source b) ⊗
      (C.generator A D I b ⊗ C.internalHom A D I (C.target b) y)) (C.internalHom A D I x y) 1 :=
  ((tensorLeftHom (homObject A D x (C.source b)) _ _).f 1
    (C.internalReplaceHead A D I b y)).comp
    (Cochain.ofHom (C.internalPrepend A D I x (C.source b) y)) (add_zero 1)

lemma internalReplaceHead_inclusion (b : I) (w : List I) (y : D) :
    (Cochain.ofHom ((C.generator A D I b) ◁ C.inclusion A D I w (C.target b) y)).comp
      (C.internalReplaceHead A D I b y) (zero_add 1) =
    (C.replaceHead A D I b w y).comp
      (Cochain.ofHom (C.inclusion A D I w (C.source b) y)) (add_zero 1) := by
  rw [internalReplaceHead, replaceHead, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    tensorRight_cochain_chain_naturality, Cochain.comp_assoc_of_third_is_zero_cochain,
    ← Cochain.ofHom_comp, internalPrepend_inclusion]
  rw [Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp]

lemma internalReplaceFirst_inclusion (b : I) (w : List I) (x y : D) :
    (Cochain.ofHom ((homObject A D x (C.source b)) ◁
      ((C.generator A D I b) ◁ C.inclusion A D I w (C.target b) y))).comp
      (C.internalReplaceFirst A D I b x y) (zero_add 1) =
    (C.replaceFirst A D I b w x y).comp
      (Cochain.ofHom (C.inclusion A D I w x y)) (add_zero 1) := by
  rw [internalReplaceFirst, replaceFirst_eq_head,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← tensorLeftHom_ofHom (homObject A D x (C.source b)),
    ← tensorLeftHom_cochain_comp, internalReplaceHead_inclusion,
    tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp,
    internalPrepend_inclusion]

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end InternalBoundaryHead

/-! ## AppendBoundaryHead（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/AppendBoundaryHead.lean） -/

/-! # 後続pathの連結と先頭生成元の境界置換の整合性

## 概要
後続pathの連結と先頭生成元の境界置換の整合性。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AppendBoundaryHead

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)
attribute [local irreducible] internalReplaceHead internalReplaceFirst replaceHead replaceFirst

lemma appendRight_replaceHead (b : I) (w : List I) (y z : D) :
    (Cochain.ofHom ((α_ (C.generator A D I b) (C.term A D I w (C.target b) y)
      (C.internalHom A D I y z)).hom ≫
      (C.generator A D I b) ◁ C.appendRight A D I w (C.target b) y z)).comp
      (C.internalReplaceHead A D I b z) (zero_add 1) =
    ((tensorRightHom (C.internalHom A D I y z) _ _).f 1
      (C.replaceHead A D I b w y)).comp
      (Cochain.ofHom (C.appendRight A D I w (C.source b) y z)) (add_zero 1) := by
  unfold internalReplaceHead replaceHead
  exact tensorRight_action_cochain (C.generator A D I b)
    (homObject A D (C.source b) (C.target b)) _ _ _ _ _ 1 (C.boundaryCochain A D I b)
    (C.appendRight A D I w (C.target b) y z)
    (C.prependMap A D I w (C.source b) (C.target b) y)
    (C.appendRight A D I w (C.source b) y z)
    (C.internalPrepend A D I (C.source b) (C.target b) z)
    (C.appendRight_prepend A D I w (C.source b) (C.target b) y z)

lemma appendRight_replaceFirst (b : I) (w : List I) (x y z : D) :
    (Cochain.ofHom ((α_ (homObject A D x (C.source b))
      (C.generator A D I b ⊗ C.term A D I w (C.target b) y) (C.internalHom A D I y z)).hom ≫
      (homObject A D x (C.source b)) ◁
        ((α_ (C.generator A D I b) (C.term A D I w (C.target b) y)
          (C.internalHom A D I y z)).hom ≫
          (C.generator A D I b) ◁ C.appendRight A D I w (C.target b) y z))).comp
      (C.internalReplaceFirst A D I b x z) (zero_add 1) =
    ((tensorRightHom (C.internalHom A D I y z) _ _).f 1
      (C.replaceFirst A D I b w x y)).comp
      (Cochain.ofHom (C.appendRight A D I w x y z)) (add_zero 1) := by
  rw [internalReplaceFirst, replaceFirst_eq_head]
  simpa only [term, whiskerLeft_comp, Category.assoc] using
    tensorCarry_cochain (homObject A D x (C.source b))
      (C.generator A D I b ⊗ C.term A D I w (C.target b) y)
      (C.term A D I w (C.source b) y) (C.internalHom A D I y z)
      (C.generator A D I b ⊗ C.internalHom A D I (C.target b) z)
      (C.internalHom A D I (C.source b) z) (C.term A D I w x y) (C.internalHom A D I x z) 1
    (C.replaceHead A D I b w y) (C.internalReplaceHead A D I b z)
    ((α_ (C.generator A D I b) (C.term A D I w (C.target b) y)
      (C.internalHom A D I y z)).hom ≫
      (C.generator A D I b) ◁ C.appendRight A D I w (C.target b) y z)
    (C.appendRight A D I w (C.source b) y z)
    (C.prependMap A D I w x (C.source b) y)
    (C.internalPrepend A D I x (C.source b) z) (C.appendRight A D I w x y z)
    (C.appendRight_replaceHead A D I b w y z) (C.appendRight_prepend A D I w x (C.source b) y z)

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end AppendBoundaryHead

/-! ## AppendRightAssociativity（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/AppendRightAssociativity.lean） -/

/-! # 任意次数cell path：AppendRightAssociativity

## 概要
任意次数cell path：AppendRightAssociativity。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AppendRightAssociativity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

lemma appendRight_assoc (w : List I) (x y z t : D) :
    (C.appendRight A D I w x y z ▷ C.internalHom A D I z t) ≫ C.internalComposition A D I x z t =
    (α_ (C.term A D I w x y) (C.internalHom A D I y z) (C.internalHom A D I z t)).hom ≫
      (C.term A D I w x y) ◁ C.internalComposition A D I y z t ≫ C.appendRight A D I w x y t := by
  induction w generalizing x with
  | nil =>
    simpa only [internalPrepend, term] using C.internalComposition_prepend A D I x y z t
  | cons b w ih =>
    have he := tensorCarry_assoc (C.generator A D I b) (C.term A D I w (C.target b) y)
      (C.internalHom A D I y z) (C.internalHom A D I z t) (C.internalHom A D I (C.target b) z)
      (C.internalHom A D I (C.target b) t) (C.internalHom A D I y t)
      (C.appendRight A D I w (C.target b) y z) (C.internalComposition A D I (C.target b) z t)
      (C.internalComposition A D I y z t) (C.appendRight A D I w (C.target b) y t) (ih (C.target b))
    have hk := tensorCarry_assoc (homObject A D x (C.source b))
      (C.generator A D I b ⊗ C.term A D I w (C.target b) y) (C.internalHom A D I y z)
      (C.internalHom A D I z t) (C.generator A D I b ⊗ C.internalHom A D I (C.target b) z)
      (C.generator A D I b ⊗ C.internalHom A D I (C.target b) t) (C.internalHom A D I y t)
      ((α_ (C.generator A D I b) (C.term A D I w (C.target b) y) (C.internalHom A D I y z)).hom ≫
        (C.generator A D I b) ◁ C.appendRight A D I w (C.target b) y z)
      ((α_ (C.generator A D I b) (C.internalHom A D I (C.target b) z) (C.internalHom A D I z t)).hom
        ≫
        (C.generator A D I b) ◁ C.internalComposition A D I (C.target b) z t)
      (C.internalComposition A D I y z t)
      ((α_ (C.generator A D I b) (C.term A D I w (C.target b) y) (C.internalHom A D I y t)).hom ≫
        (C.generator A D I b) ◁ C.appendRight A D I w (C.target b) y t) he
    have hp := congrArg (fun f => f ≫ C.prefixPath A D I b x t) hk
    simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc] at hp
    rw [appendRight_cons]
    simp only [comp_whiskerRight, Category.assoc]
    rw [internalComposition_prefixPath]
    simpa only [appendRight_cons, term, whiskerLeft_comp, comp_whiskerRight,
      Category.assoc] using hp

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end AppendRightAssociativity

/-! ## BoundaryRowRecursion（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/BoundaryRowRecursion.lean） -/

/-! # 任意次数cell pathの境界置換：BoundaryRowRecursion

## 概要
任意次数cell pathの境界置換：BoundaryRowRecursion。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BoundaryRowRecursion

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

/-- 後方cochainを先頭Homと生成元でtensorし、先頭を追加したpath直和へ送る。 -/
def prefixTailCochain (b : I) (w : List I) (x y : D) (p : ℤ)
    (f : Cochain (C.term A D I w (C.target b) y) (C.internalHom A D I (C.target b) y) p) :
    Cochain (C.term A D I (b :: w) x y) (C.internalHom A D I x y) p :=
  ((tensorLeftHom (homObject A D x (C.source b)) (C.generator A D I b ⊗ C.term A D I w (C.target b)
    y)
    (C.generator A D I b ⊗ C.internalHom A D I (C.target b) y)).f p
    ((tensorLeftHom (C.generator A D I b) (C.term A D I w (C.target b) y)
      (C.internalHom A D I (C.target b) y)).f p f)).comp
    (Cochain.ofHom (C.prefixPath A D I b x y)) (add_zero p)

/-- 後方の消去項は短いpathの消去項を二重tensorし、先頭を追加したもの。 -/
lemma replaceSummand_cons_succ (b : I) (w : List I) (i : ℕ) (x y : D) :
    C.replaceSummand A D I (b :: w) (i + 1) x y =
    C.prefixTailCochain A D I b w x y 1 (C.replaceSummand A D I w i (C.target b) y) := by
  rw [prefixTailCochain, replaceSummand, replaceSummand, replaceFace_succ,
    tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, prefixPath_inclusion]
  rfl

/-- 非空pathの消去和は、先頭生成元の消去と、先頭を保持する後方消去和の和である。 -/
lemma replaceRow_cons (b : I) (w : List I) (x y : D) :
    C.replaceRow A D I (b :: w) x y =
    (C.replaceFirst A D I b w x y).comp (Cochain.ofHom (C.inclusion A D I w x y)) (add_zero 1) +
    C.prefixTailCochain A D I b w x y 1 (C.replaceRow A D I w (C.target b) y) := by
  let R : Cochain (C.term A D I w (C.target b) y) (C.internalHom A D I (C.target b) y) 1 →+
      Cochain (C.term A D I (b :: w) x y) (C.internalHom A D I x y) 1 :=
    { toFun := C.prefixTailCochain A D I b w x y 1
      map_zero' := by simp only [prefixTailCochain, map_zero, Cochain.zero_comp]
      map_add' := fun f g => by
        simp only [prefixTailCochain, map_add]
        exact Cochain.add_comp _ _ _ (add_zero 1) }
  have hs : ∑ i ∈ Finset.range w.length, C.replaceSummand A D I (b :: w) (i + 1) x y =
      R (C.replaceRow A D I w (C.target b) y) := by
    rw [replaceRow, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact C.replaceSummand_cons_succ A D I b w i x y
  have hz : C.replaceSummand A D I (b :: w) 0 x y =
      (C.replaceFirst A D I b w x y).comp (Cochain.ofHom (C.inclusion A D I w x y)) (add_zero 1) :=
        rfl
  rw [replaceRow, List.length_cons, Finset.sum_range_succ', hs, hz]
  exact add_comm _ _

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end BoundaryRowRecursion

/-! ## PrefixBoundary（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/PrefixBoundary.lean） -/

/-! # 先頭cell追加に対する全境界置換作用素の再帰式

## 概要
先頭cell追加に対する全境界置換作用素の再帰式。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section PrefixBoundary

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

lemma prefixPath_replacement (b : I) (x y : D) :
    (Cochain.ofHom (C.prefixPath A D I b x y)).comp (C.replacement A D I x y) (zero_add 1) =
    C.internalReplaceFirst A D I b x y +
    ((tensorLeftHom (homObject A D x (C.source b)) _ _).f 1
      ((tensorLeftHom (C.generator A D I b) _ _).f 1
        (C.replacement A D I (C.target b) y))).comp
      (Cochain.ofHom (C.prefixPath A D I b x y)) (add_zero 1) := by
  apply C.prefixPathCochain_ext A D I b x y 1
  intro w
  have ht : (Cochain.ofHom ((homObject A D x (C.source b)) ◁
      ((C.generator A D I b) ◁ C.inclusion A D I w (C.target b) y))).comp
      ((tensorLeftHom (homObject A D x (C.source b)) _ _).f 1
        ((tensorLeftHom (C.generator A D I b) _ _).f 1
          (C.replacement A D I (C.target b) y))) (zero_add 1) =
    (tensorLeftHom (homObject A D x (C.source b)) _ _).f 1
      ((tensorLeftHom (C.generator A D I b) _ _).f 1
        (C.replaceRow A D I w (C.target b) y)) := by
    rw [← tensorLeftHom_ofHom (homObject A D x (C.source b)),
      ← tensorLeftHom_cochain_comp, ← tensorLeftHom_ofHom (C.generator A D I b),
      ← tensorLeftHom_cochain_comp, replacement_precomp]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    prefixPath_inclusion, replacement_precomp, Cochain.comp_add,
    internalReplaceFirst_inclusion, ← Cochain.comp_assoc_of_first_is_zero_cochain, ht]
  exact C.replaceRow_cons A D I b w x y

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end PrefixBoundary

/-! ## AppendLiftCochain（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/AppendLiftCochain.lean） -/

/-! # 任意次数cell pathの境界置換：AppendLiftCochain

## 概要
任意次数cell pathの境界置換：AppendLiftCochain。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AppendLiftCochain

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

/-- 前方Homと生成元を付け直し、後方の連結cochainを全pathへ戻す。 -/
def appendLiftCochain (b : I) (w : List I) (x y z : D) (p : ℤ)
    (f : Cochain (C.term A D I w (C.target b) y ⊗ C.internalHom A D I y z)
      (C.internalHom A D I (C.target b) z) p) :
    Cochain (C.term A D I (b :: w) x y ⊗ C.internalHom A D I y z) (C.internalHom A D I x z) p :=
  ((Cochain.ofHom ((α_ (homObject A D x (C.source b))
      (C.generator A D I b ⊗ C.term A D I w (C.target b) y) (C.internalHom A D I y z)).hom ≫
      (homObject A D x (C.source b)) ◁
        (α_ (C.generator A D I b) (C.term A D I w (C.target b) y) (C.internalHom A D I y
          z)).hom)).comp
    ((tensorLeftHom (homObject A D x (C.source b))
      (C.generator A D I b ⊗ (C.term A D I w (C.target b) y ⊗ C.internalHom A D I y z))
      (C.generator A D I b ⊗ C.internalHom A D I (C.target b) z)).f p
      ((tensorLeftHom (C.generator A D I b) (C.term A D I w (C.target b) y ⊗ C.internalHom A D I y
        z)
        (C.internalHom A D I (C.target b) z)).f p f)) (zero_add p)).comp
      (Cochain.ofHom (C.prefixPath A D I b x z)) (add_zero p)

lemma appendLiftCochain_add (b : I) (w : List I) (x y z : D) (p : ℤ)
    (f g : Cochain (C.term A D I w (C.target b) y ⊗ C.internalHom A D I y z)
      (C.internalHom A D I (C.target b) z) p) :
    C.appendLiftCochain A D I b w x y z p (f + g) =
      C.appendLiftCochain A D I b w x y z p f + C.appendLiftCochain A D I b w x y z p g := by
  simp only [appendLiftCochain, map_add]
  rw [Cochain.comp_add _ _ _ (zero_add p)]
  exact Cochain.add_comp _ _ _ (add_zero p)

/-- 左語の後方cochainによる項は、短い語での項の持ち上げに等しい。 -/
lemma appendLiftCochain_left (b : I) (w : List I) (x y z : D) (p : ℤ)
    (f : Cochain (C.term A D I w (C.target b) y) (C.internalHom A D I (C.target b) y) p) :
    ((tensorRightHom (C.internalHom A D I y z) (C.term A D I (b :: w) x y)
      (C.internalHom A D I x y)).f p (C.prefixTailCochain A D I b w x y p f)).comp
      (Cochain.ofHom (C.internalComposition A D I x y z)) (add_zero p) =
    C.appendLiftCochain A D I b w x y z p
      (((tensorRightHom (C.internalHom A D I y z) (C.term A D I w (C.target b) y)
        (C.internalHom A D I (C.target b) y)).f p f).comp
          (Cochain.ofHom (C.internalComposition A D I (C.target b) y z)) (add_zero p)) := by
  have ha := C.internalComposition_prefixPath A D I b x y z
  simp only [whiskerLeft_comp, Category.assoc] at ha
  have h := prefixTensor_cochain_action_left (homObject A D x (C.source b))
    (C.generator A D I b) (C.term A D I w (C.target b) y)
    (C.internalHom A D I (C.target b) y) (C.internalHom A D I y z)
    (C.internalHom A D I x y) (C.internalHom A D I (C.target b) z)
    (C.internalHom A D I x z) p f (C.prefixPath A D I b x y)
    (C.internalComposition A D I x y z) (C.internalComposition A D I (C.target b) y z)
    (C.prefixPath A D I b x z) ha
  unfold prefixTailCochain appendLiftCochain
  simp only [term_cons]
  change ((tensorRightHom (C.internalHom A D I y z)
      (homObject A D x (C.source b) ⊗
        (C.generator A D I b ⊗ C.term A D I w (C.target b) y))
      (C.internalHom A D I x y)).f p
      (((tensorLeftHom (homObject A D x (C.source b)) _ _).f p
        ((tensorLeftHom (C.generator A D I b) _ _).f p f)).comp
        (Cochain.ofHom (C.prefixPath A D I b x y)) (add_zero p))).comp
      (Cochain.ofHom (C.internalComposition A D I x y z)) (add_zero p) = _
  with_reducible exact h

/-- 右側cochainによる項も短い語での項の持ち上げに等しい。 -/
lemma appendLiftCochain_right (b : I) (w : List I) (x y z : D) (p : ℤ)
    (f : Cochain (C.internalHom A D I y z) (C.internalHom A D I y z) p) :
    ((tensorLeftHom (C.term A D I (b :: w) x y) (C.internalHom A D I y z)
      (C.internalHom A D I y z)).f p f).comp
      (Cochain.ofHom (C.appendRight A D I (b :: w) x y z)) (add_zero p) =
    C.appendLiftCochain A D I b w x y z p
      (((tensorLeftHom (C.term A D I w (C.target b) y) (C.internalHom A D I y z)
        (C.internalHom A D I y z)).f p f).comp
          (Cochain.ofHom (C.appendRight A D I w (C.target b) y z)) (add_zero p)) := by
  let cmp : (homObject A D x (C.source b) ⊗
      (C.generator A D I b ⊗ C.term A D I w (C.target b) y)) ⊗ C.internalHom A D I y z ⟶
      C.internalHom A D I x z := C.appendRight A D I (b :: w) x y z
  have ha := C.appendRight_cons A D I b w x y z
  simp only [whiskerLeft_comp, Category.assoc] at ha
  have h := prefixTensor_cochain_action_right (homObject A D x (C.source b))
    (C.generator A D I b) (C.term A D I w (C.target b) y)
    (C.internalHom A D I y z) (C.internalHom A D I y z)
    (C.internalHom A D I (C.target b) z) (C.internalHom A D I x z) p f
    cmp (C.appendRight A D I w (C.target b) y z) (C.prefixPath A D I b x z) ha
  unfold appendLiftCochain
  simp only [term_cons]
  change ((tensorLeftHom (homObject A D x (C.source b) ⊗
      (C.generator A D I b ⊗ C.term A D I w (C.target b) y))
      (C.internalHom A D I y z) (C.internalHom A D I y z)).f p f).comp
      (Cochain.ofHom cmp) (add_zero p) = _
  with_reducible exact h

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end AppendLiftCochain

/-! ## AppendBoundaryRecursion（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/AppendBoundaryRecursion.lean） -/

/-! # 非空の左pathの連結後の境界置換の再帰式

## 概要
非空の左pathの連結後の境界置換の再帰式。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AppendBoundaryRecursion

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)


lemma appendRight_cons_factor (b : I) (w : List I) (x y z : D) :
    C.appendRight A D I (b :: w) x y z =
    (((α_ (homObject A D x (C.source b))
      (C.generator A D I b ⊗ C.term A D I w (C.target b) y) (C.internalHom A D I y z)).hom ≫
      (homObject A D x (C.source b)) ◁
        (α_ (C.generator A D I b) (C.term A D I w (C.target b) y)
          (C.internalHom A D I y z)).hom) ≫
      (homObject A D x (C.source b)) ◁
        ((C.generator A D I b) ◁ C.appendRight A D I w (C.target b) y z)) ≫
      C.prefixPath A D I b x z := by
  rw [appendRight_cons]
  simp only [whiskerLeft_comp, Category.assoc]

lemma appendRight_replaceFirst_factored (b : I) (w : List I) (x y z : D) :
    (Cochain.ofHom (((α_ (homObject A D x (C.source b))
      (C.generator A D I b ⊗ C.term A D I w (C.target b) y) (C.internalHom A D I y z)).hom ≫
      (homObject A D x (C.source b)) ◁
        (α_ (C.generator A D I b) (C.term A D I w (C.target b) y)
          (C.internalHom A D I y z)).hom) ≫
      (homObject A D x (C.source b)) ◁
        ((C.generator A D I b) ◁ C.appendRight A D I w (C.target b) y z))).comp
      (C.internalReplaceFirst A D I b x z) (zero_add 1) =
    ((tensorRightHom (C.internalHom A D I y z) (C.term A D I (b :: w) x y)
      (C.term A D I w x y)).f 1
      (C.replaceFirst A D I b w x y)).comp
      (Cochain.ofHom (C.appendRight A D I w x y z)) (add_zero 1) := by
  simpa only [whiskerLeft_comp, Category.assoc] using C.appendRight_replaceFirst A D I b w x y z

lemma appendRight_replacement_cons (b : I) (w : List I) (x y z : D) :
    (Cochain.ofHom (C.appendRight A D I (b :: w) x y z)).comp
      (C.replacement A D I x z) (zero_add 1) =
    ((tensorRightHom (C.internalHom A D I y z) (C.term A D I (b :: w) x y)
      (C.term A D I w x y)).f 1
      (C.replaceFirst A D I b w x y)).comp
      (Cochain.ofHom (C.appendRight A D I w x y z)) (add_zero 1) +
    C.appendLiftCochain A D I b w x y z 1
      ((Cochain.ofHom (C.appendRight A D I w (C.target b) y z)).comp
        (C.replacement A D I (C.target b) z) (zero_add 1)) := by
  have hc := C.appendRight_cons_factor A D I b w x y z
  have hh := C.appendRight_replaceFirst_factored A D I b w x y z
  rw [hc, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    prefixPath_replacement, Cochain.comp_add _ _ _ (zero_add 1), hh]
  apply congrArg₂ (· + ·) rfl
  have ht := prefixTensor_cochain_precomp (homObject A D x (C.source b))
    (C.generator A D I b) (C.term A D I w (C.target b) y) (C.internalHom A D I y z)
    (C.internalHom A D I (C.target b) z) (C.internalHom A D I (C.target b) z)
    (C.internalHom A D I x z) 1 (C.appendRight A D I w (C.target b) y z)
    (C.replacement A D I (C.target b) z) (C.prefixPath A D I b x z)
  change _ = C.appendLiftCochain A D I b w x y z 1 _
  unfold appendLiftCochain
  simp only [term_cons, Category.assoc] at ht ⊢
  with_reducible exact ht

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end AppendBoundaryRecursion

/-! ## AppendBoundary（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/AppendBoundary.lean） -/

/-! # 左有限pathを固定した連結の境界置換Leibniz則

## 概要
左有限pathを固定した連結の境界置換Leibniz則。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AppendBoundary

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

lemma appendRight_replacement (w : List I) (x y z : D) :
    (Cochain.ofHom (C.appendRight A D I w x y z)).comp (C.replacement A D I x z) (zero_add 1) =
    ((tensorRightHom (C.internalHom A D I y z) _ _).f 1 (C.replaceRow A D I w x y)).comp
      (Cochain.ofHom (C.internalComposition A D I x y z)) (add_zero 1) +
    ((tensorLeftHom (C.term A D I w x y) _ _).f 1 (C.replacement A D I y z)).comp
      (Cochain.ofHom (C.appendRight A D I w x y z)) (add_zero 1) := by
  induction w generalizing x with
  | nil =>
    rw [replaceRow_nil, map_zero, Cochain.zero_comp, zero_add]
    exact C.internalPrepend_replacement A D I x y z
  | cons b w ih =>
    rw [appendRight_replacement_cons, ih (C.target b), appendLiftCochain_add,
      ← appendLiftCochain_left, ← appendLiftCochain_right, replaceRow_cons, map_add]
    rw [Cochain.add_comp _ _ _ (add_zero 1)]
    rw [tensorRightHom_cochain_comp, tensorRightHom_ofHom,
      Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp,
      internalComposition_left_inclusion]
    exact (add_assoc _ _ _).symm

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end AppendBoundary

/-! ## CompositionBoundary（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/CompositionBoundary.lean） -/

/-! # 任意次数cellの全合成の微分整合性：CompositionBoundary

## 概要
任意次数cellの全合成の微分整合性：CompositionBoundary。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section CompositionBoundary

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits Preadditive MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

/-- 全path直和の内部合成は境界置換作用素に関してもLeibniz則を満たす。 -/
lemma internalComposition_replacement (x y z : D) :
    (Cochain.ofHom (C.internalComposition A D I x y z)).comp (C.replacement A D I x z)
      (zero_add 1) =
    ((tensorRightHom (C.internalHom A D I y z) (C.internalHom A D I x y)
      (C.internalHom A D I x y)).f 1 (C.replacement A D I x y)).comp
      (Cochain.ofHom (C.internalComposition A D I x y z)) (add_zero 1) +
    ((tensorLeftHom (C.internalHom A D I x y) (C.internalHom A D I y z)
      (C.internalHom A D I y z)).f 1 (C.replacement A D I y z)).comp
      (Cochain.ofHom (C.internalComposition A D I x y z)) (add_zero 1) := by
  apply C.tensorRightPathCochain_ext A D I x y (C.internalHom A D I y z) 1
  intro w
  have hl : (Cochain.ofHom (C.inclusion A D I w x y ▷ C.internalHom A D I y z)).comp
      ((tensorRightHom (C.internalHom A D I y z) (C.internalHom A D I x y)
        (C.internalHom A D I x y)).f 1 (C.replacement A D I x y)) (zero_add 1) =
      (tensorRightHom (C.internalHom A D I y z) (C.term A D I w x y)
        (C.internalHom A D I x y)).f 1 (C.replaceRow A D I w x y) := by
    rw [← tensorRightHom_ofHom, ← tensorRightHom_cochain_comp, replacement_precomp]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    internalComposition_left_inclusion]
  rw [Cochain.comp_add _ _ _ (zero_add 1),
    ← Cochain.comp_assoc_of_first_is_zero_cochain, hl,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← tensorLeftHom_cochain_naturality,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp,
    internalComposition_left_inclusion]
  exact C.appendRight_replacement A D I w x y z

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end CompositionBoundary

/-! ## CompositionDifferential（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/CompositionDifferential.lean） -/

/-! # 任意次数cellの全合成の微分整合性：CompositionDifferential

## 概要
任意次数cellの全合成の微分整合性：CompositionDifferential。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section CompositionDifferential

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits Preadditive MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

/-- 全消去Leibniz則の斉次成分。右の消去項の符号は左の次数p。 -/
lemma internalComposition_replacement_apply (x y z : D) (p q n : ℤ)
    (hn : p + q = n) (a : (C.internalHom A D I x y).X p) (b : (C.internalHom A D I y z).X q) :
    (C.replacement A D I x z).v n (n + 1) rfl
      ((C.internalComposition A D I x y z).f n
        (ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b))) =
    (C.internalComposition A D I x y z).f (n + 1)
      (ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) (p + 1) q (n + 1)
        (by omega) ((C.replacement A D I x y).v p (p + 1) rfl a ⊗ₜ[A] b)) +
    p.negOnePow • (C.internalComposition A D I x y z).f (n + 1)
      (ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) p (q + 1) (n + 1)
        (by omega) (a ⊗ₜ[A] (C.replacement A D I y z).v q (q + 1) rfl b)) := by
  have h := congrArg (fun f : Cochain
      (C.internalHom A D I x y ⊗ C.internalHom A D I y z) (C.internalHom A D I x z) 1 =>
    f.v n (n + 1) rfl
      (ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b)))
    (C.internalComposition_replacement A D I x y z)
  simp only [Cochain.add_v, ModuleCat.hom_add, LinearMap.add_apply] at h
  rw [cochain_ofHom_comp_apply, cochain_comp_ofHom_apply, cochain_comp_ofHom_apply,
    tensorRightHom_apply, tensorLeftHom_apply, chain_units_smul] at h
  simpa only [one_mul] using h

/-- 最終Homの全微分についてのLeibniz則。 -/
lemma internalComposition_total_d_apply (x y z : D) (p q n : ℤ)
    (hn : p + q = n) (a : (C.internalHom A D I x y).X p) (b : (C.internalHom A D I y z).X q) :
    (C.attachedHom A D I x z).d n (n + 1)
      ((C.internalComposition A D I x y z).f n
        (ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b))) =
    (C.internalComposition A D I x y z).f (n + 1)
      (ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) (p + 1) q (n + 1)
        (by omega) ((C.attachedHom A D I x y).d p (p + 1) a ⊗ₜ[A] b)) +
    p.negOnePow • (C.internalComposition A D I x y z).f (n + 1)
      (ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) p (q + 1) (n + 1)
        (by omega) (a ⊗ₜ[A] (C.attachedHom A D I y z).d q (q + 1) b)) := by
  have hi := ConcreteCategory.congr_hom ((C.internalComposition A D I x y z).comm n (n + 1))
    (ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b))
  change (C.internalHom A D I x z).d n (n + 1) (_ : (C.internalHom A D I x z).X n) =
    (C.internalComposition A D I x y z).f (n + 1)
      ((C.internalHom A D I x y ⊗ C.internalHom A D I y z).d n (n + 1)
        (ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b))) at hi
  have hd := SerrePositivity.cochainTensor_d_apply_ι
    (C.internalHom A D I x y) (C.internalHom A D I y z) p q n hn a b
  have hi' := hi.trans (congrArg (fun v :
      (C.internalHom A D I x y ⊗ C.internalHom A D I y z).X (n + 1) =>
    (C.internalComposition A D I x y z).f (n + 1) v) hd)
  clear hi
  have hi := hi'
  rw [map_add, chain_units_smul] at hi
  rw [attachedHom_d, attachedHom_d, attachedHom_d]
  change (C.internalHom A D I x z).d n (n + 1)
      ((C.internalComposition A D I x y z).f n
        (ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b))) +
      (C.replacement A D I x z).v n (n + 1) rfl
        ((C.internalComposition A D I x y z).f n
          (ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b))) =
    (C.internalComposition A D I x y z).f (n + 1)
      (ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) (p + 1) q (n + 1)
        (by omega) (((C.internalHom A D I x y).d p (p + 1) a +
          (C.replacement A D I x y).v p (p + 1) rfl a) ⊗ₜ[A] b)) +
    p.negOnePow • (C.internalComposition A D I x y z).f (n + 1)
      (ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) p (q + 1) (n + 1)
        (by omega) (a ⊗ₜ[A] ((C.internalHom A D I y z).d q (q + 1) b +
          (C.replacement A D I y z).v q (q + 1) rfl b)))
  exact (congrArg₂ (· + ·) hi
    (C.internalComposition_replacement_apply A D I x y z p q n hn a b)).trans (by
    simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, smul_add]
    abel)

/-- 全pathの最終Hom複体間の合成。最終微分に関する実際のchain map。 -/
def attachedComposition (x y z : D) :
    C.attachedHom A D I x y ⊗ C.attachedHom A D I y z ⟶ C.attachedHom A D I x z :=
  tensorLift (fun i j n h =>
    ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) i j n h ≫
      (C.internalComposition A D I x y z).f n) (fun i j => by
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro a b
        exact C.internalComposition_total_d_apply A D I x y z i j (i + j) rfl a b)

lemma attachedComposition_ι (x y z : D) (i j n : ℤ) (hn : i + j = n) :
    ιTensorObj (C.attachedHom A D I x y) (C.attachedHom A D I y z) i j n hn ≫
      (C.attachedComposition A D I x y z).f n =
    ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) i j n hn ≫
      (C.internalComposition A D I x y z).f n :=
  ι_tensorLift _ _ i j n hn

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end CompositionDifferential

/-! ## CompositionEvaluation（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/CompositionEvaluation.lean） -/

/-! # cell付加の最終Hom合成：CompositionEvaluation

## 概要
cell付加の最終Hom合成：CompositionEvaluation。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section CompositionEvaluation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

lemma attachedComposition_apply (x y z : D) (p q n : ℤ) (hn : p + q = n)
    (a : (C.attachedHom A D I x y).X p) (b : (C.attachedHom A D I y z).X q) :
    (C.attachedComposition A D I x y z).f n
      (ιTensorObj (C.attachedHom A D I x y) (C.attachedHom A D I y z) p q n hn (a ⊗ₜ[A] b)) =
    (C.internalComposition A D I x y z).f n
      (ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b)) :=
  ConcreteCategory.congr_hom (C.attachedComposition_ι A D I x y z p q n hn) (a ⊗ₜ[A] b)

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end CompositionEvaluation

/-! ## CompositionComparison（旧 SerrePositivity/DifferentialGraded/Resolution/Cells/CompositionComparison.lean） -/

/-! # cell付加の最終Hom合成：CompositionComparison

## 概要
cell付加の最終Hom合成：CompositionComparison。

## 方針
指定の共通source・準同値・局所化の比較を使い、既存の比較関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。Hom非平坦のdg圏のMorita・tensor・Hochschild型構成・K理論で、分解選択を比較する入口。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section CompositionComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

/-- 微分を変えても最終合成の各次数の射は内部合成の射そのものである。 -/
lemma attachedComposition_f (x y z : D) (n : ℤ) :
    (C.attachedComposition A D I x y z).f n = (C.internalComposition A D I x y z).f n := by
  apply mapBifunctor.hom_ext
  intro i j hij
  exact C.attachedComposition_ι A D I x y z i j n hij

/-- 最終合成は元のdg圏の豊穣合成と包含を通じて一致する。 -/
lemma attachedComposition_original (x y z : D) :
    (C.originalHomInclusion A D I x y ⊗ₘ C.originalHomInclusion A D I y z) ≫
      C.attachedComposition A D I x y z =
    eComp (Complex A) x y z ≫ C.originalHomInclusion A D I x z := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [HomologicalComplex.comp_f, attachedComposition_f,
    HomologicalComplex.comp_f, originalHomInclusion_f]
  have h := congrArg (fun f => f.f n) (C.internalComposition_original_original A D I x y z)
  simp only [HomologicalComplex.comp_f] at h
  exact h

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
end

end CompositionComparison
