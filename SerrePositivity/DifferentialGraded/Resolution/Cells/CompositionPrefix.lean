module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.AppendRecursion
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproductExt

/-! # 任意次数cell path：CompositionPrefix

## 概要
任意次数cell path：CompositionPrefix。

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
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

lemma composition_prefix_left_ι (b : I) (w : List I) (x y z : D) :
    (((homObject A D x (C.source b)) ◁ ((C.generator A D I b) ◁ C.inclusion A D I w (C.target b) y))
      ▷
    C.internalHom A D I y z) ≫ (C.prefixPath A D I b x y ▷ C.internalHom A D I y z) ≫
      C.internalComposition A D I x y z = C.appendRight A D I (b :: w) x y z := by
  rw [← comp_whiskerRight_assoc, prefixPath_inclusion, internalComposition_left_inclusion]

lemma composition_prefix_middle_ι (b : I) (w : List I) (y z : D) :
    (((C.generator A D I b) ◁ C.inclusion A D I w (C.target b) y) ▷ C.internalHom A D I y z) ≫
    (α_ (C.generator A D I b) (C.internalHom A D I (C.target b) y) (C.internalHom A D I y z)).hom ≫
      (C.generator A D I b) ◁ C.internalComposition A D I (C.target b) y z =
  (α_ (C.generator A D I b) (C.term A D I w (C.target b) y) (C.internalHom A D I y z)).hom ≫
    (C.generator A D I b) ◁ C.appendRight A D I w (C.target b) y z := by
  rw [associator_naturality_middle_assoc, ← whiskerLeft_comp, internalComposition_left_inclusion]

lemma composition_prefix_outer_ι (b : I) (w : List I) (x y z : D) :
    (((homObject A D x (C.source b)) ◁ ((C.generator A D I b) ◁ C.inclusion A D I w (C.target b) y))
      ▷
    C.internalHom A D I y z) ≫
    (α_ (homObject A D x (C.source b)) (C.generator A D I b ⊗ C.internalHom A D I (C.target b) y)
      (C.internalHom A D I y z)).hom ≫
    (homObject A D x (C.source b)) ◁
      ((α_ (C.generator A D I b) (C.internalHom A D I (C.target b) y) (C.internalHom A D I y z)).hom
        ≫
        (C.generator A D I b) ◁ C.internalComposition A D I (C.target b) y z) =
  (α_ (homObject A D x (C.source b)) (C.generator A D I b ⊗ C.term A D I w (C.target b) y)
    (C.internalHom A D I y z)).hom ≫
  (homObject A D x (C.source b)) ◁
    ((α_ (C.generator A D I b) (C.term A D I w (C.target b) y) (C.internalHom A D I y z)).hom ≫
      (C.generator A D I b) ◁ C.appendRight A D I w (C.target b) y z) := by
  rw [associator_naturality_middle_assoc, ← whiskerLeft_comp, composition_prefix_middle_ι]

/-- 各path上で先頭追加と全合成の二つの順序を比較する。 -/
lemma composition_prefix_restrict (b : I) (w : List I) (x y z : D) :
    (((homObject A D x (C.source b)) ◁ ((C.generator A D I b) ◁ C.inclusion A D I w (C.target b) y))
      ▷
      C.internalHom A D I y z) ≫ (C.prefixPath A D I b x y ▷ C.internalHom A D I y z) ≫
      C.internalComposition A D I x y z =
    (((homObject A D x (C.source b)) ◁ ((C.generator A D I b) ◁ C.inclusion A D I w (C.target b) y))
      ▷
      C.internalHom A D I y z) ≫
      (α_ (homObject A D x (C.source b)) (C.generator A D I b ⊗ C.internalHom A D I (C.target b) y)
        (C.internalHom A D I y z)).hom ≫ (homObject A D x (C.source b)) ◁
        ((α_ (C.generator A D I b) (C.internalHom A D I (C.target b) y) (C.internalHom A D I y
          z)).hom ≫
          (C.generator A D I b) ◁ C.internalComposition A D I (C.target b) y z) ≫ C.prefixPath A D I
            b x z := by
  have hr := congrArg (fun f => f ≫ C.prefixPath A D I b x z)
    (C.composition_prefix_outer_ι A D I b w x y z)
  simp only [Category.assoc] at hr
  exact (C.composition_prefix_left_ι A D I b w x y z).trans
      ((C.appendRight_cons A D I b w x y z).trans hr.symm)

/-- 先頭Homと生成元を追加してから合成しても、後方を合成してから追加しても一致する。 -/
lemma internalComposition_prefixPath (b : I) (x y z : D) :
    (C.prefixPath A D I b x y ▷ C.internalHom A D I y z) ≫ C.internalComposition A D I x y z =
    (α_ (homObject A D x (C.source b)) (C.generator A D I b ⊗ C.internalHom A D I (C.target b) y)
      (C.internalHom A D I y z)).hom ≫
    (homObject A D x (C.source b)) ◁
      ((α_ (C.generator A D I b) (C.internalHom A D I (C.target b) y) (C.internalHom A D I y z)).hom
        ≫
        (C.generator A D I b) ◁ C.internalComposition A D I (C.target b) y z) ≫ C.prefixPath A D I b
          x z := by
  apply tensorLeftTwoRightCoproduct_hom_ext (homObject A D x (C.source b)) (C.generator A D I b)
    (C.internalHom A D I y z) (fun w : List I => C.term A D I w (C.target b) y)
  intro w
  exact C.composition_prefix_restrict A D I b w x y z

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
