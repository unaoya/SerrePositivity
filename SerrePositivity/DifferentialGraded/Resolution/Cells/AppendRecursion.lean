module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Prefix

/-! # 左pathの先頭生成元を残す連結の再帰式

## 概要
左pathの先頭生成元を残す連結の再帰式。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

lemma appendRight_cons (b : I) (w : List I) (x y z : D) :
    C.appendRight A D I (b :: w) x y z =
    (α_ (homObject A D x (C.source b)) (C.generator A D I b ⊗ C.term A D I w (C.target b) y)
      (C.internalHom A D I y z)).hom ≫
    (homObject A D x (C.source b)) ◁
      ((α_ (C.generator A D I b) (C.term A D I w (C.target b) y) (C.internalHom A D I y z)).hom ≫
        (C.generator A D I b) ◁ C.appendRight A D I w (C.target b) y z) ≫
          C.prefixPath A D I b x z := by
  apply (tensorLeftCoproductIsColimit (C.term A D I (b :: w) x y)
    (fun v : List I => C.term A D I v y z)).hom_ext
  rintro ⟨v⟩
  have hm : ((C.generator A D I b ⊗ C.term A D I w (C.target b) y) ◁
      C.inclusion A D I v y z) ≫
      (α_ (C.generator A D I b) (C.term A D I w (C.target b) y) (C.internalHom A D I y z)).hom ≫
        (C.generator A D I b) ◁ C.appendRight A D I w (C.target b) y z =
    (α_ (C.generator A D I b) (C.term A D I w (C.target b) y) (C.term A D I v y z)).hom ≫
      (C.generator A D I b) ◁ C.appendMap A D I w v (C.target b) y z ≫
        (C.generator A D I b) ◁ C.inclusion A D I (w ++ v) (C.target b) z := by
    rw [associator_naturality_right_assoc, ← whiskerLeft_comp, appendRight_inclusion,
      whiskerLeft_comp]
  have ht : ((homObject A D x (C.source b) ⊗
      (C.generator A D I b ⊗ C.term A D I w (C.target b) y)) ◁ C.inclusion A D I v y z) ≫
      (α_ (homObject A D x (C.source b))
        (C.generator A D I b ⊗ C.term A D I w (C.target b) y) (C.internalHom A D I y z)).hom ≫
      (homObject A D x (C.source b)) ◁
        ((α_ (C.generator A D I b) (C.term A D I w (C.target b) y) (C.internalHom A D I y z)).hom ≫
          (C.generator A D I b) ◁ C.appendRight A D I w (C.target b) y z) =
    (α_ (homObject A D x (C.source b))
      (C.generator A D I b ⊗ C.term A D I w (C.target b) y) (C.term A D I v y z)).hom ≫
      (homObject A D x (C.source b)) ◁
        (α_ (C.generator A D I b) (C.term A D I w (C.target b) y) (C.term A D I v y z)).hom ≫
      (homObject A D x (C.source b)) ◁
        ((C.generator A D I b) ◁ C.appendMap A D I w v (C.target b) y z) ≫
      (homObject A D x (C.source b)) ◁
        ((C.generator A D I b) ◁ C.inclusion A D I (w ++ v) (C.target b) z) := by
    rw [associator_naturality_right_assoc, ← whiskerLeft_comp, hm]
    simp only [whiskerLeft_comp]
  have h := congrArg (fun f => f ≫ C.prefixPath A D I b x z) ht
  simp only [Category.assoc, prefixPath_inclusion] at h
  change (C.term A D I (b :: w) x y ◁ C.inclusion A D I v y z) ≫
    C.appendRight A D I (b :: w) x y z = _
  rw [appendRight_inclusion]
  simpa only [Cofan.mk_ι_app, term, appendMap, inclusion, List.cons_append,
    whiskerLeft_comp, Category.assoc] using h.symm

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
