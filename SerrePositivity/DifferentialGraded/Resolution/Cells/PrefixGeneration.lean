module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.GeneratorAppend
public import SerrePositivity.DifferentialGraded.Resolution.Cells.InternalComposition
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Prefix

/-! # 元のHomと生成元の合成から前方path追加を復元する

## 概要
元のHomと生成元の合成から前方path追加を復元する。

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
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I)

lemma generator_internalComposition_inclusion (i : I) (w : List I) (y : D) :
    ((C.generator A D I i) ◁ C.inclusion A D I w (C.target i) y) ≫
      (C.generatorInclusion A D I i ▷ C.internalHom A D I (C.target i) y) ≫
        C.internalComposition A D I (C.source i) (C.target i) y =
    (C.generatorTerm A D I i ▷ C.term A D I w (C.target i) y) ≫
      C.appendMap A D I [i] w (C.source i) (C.target i) y ≫
        C.inclusion A D I (i :: w) (C.source i) y := by
  rw [generatorInclusion, comp_whiskerRight, Category.assoc, whisker_exchange_assoc,
    ← tensorHom_def'_assoc, internalComposition_inclusion]
  rfl

lemma prefixPath_generated (i : I) (x y : D) :
    (homObject A D x (C.source i)) ◁
      ((C.generatorInclusion A D I i ▷ C.internalHom A D I (C.target i) y) ≫
        C.internalComposition A D I (C.source i) (C.target i) y) ≫
      C.internalPrepend A D I x (C.source i) y = C.prefixPath A D I i x y := by
  apply (C.prefixCofanIsColimit A D I i x y).hom_ext
  rintro ⟨w⟩
  change ((homObject A D x (C.source i)) ◁
      ((C.generator A D I i) ◁ C.inclusion A D I w (C.target i) y)) ≫
      (homObject A D x (C.source i)) ◁
        ((C.generatorInclusion A D I i ▷ C.internalHom A D I (C.target i) y) ≫
          C.internalComposition A D I (C.source i) (C.target i) y) ≫
        C.internalPrepend A D I x (C.source i) y =
    ((homObject A D x (C.source i)) ◁
      ((C.generator A D I i) ◁ C.inclusion A D I w (C.target i) y)) ≫ C.prefixPath A D I i x y
  rw [prefixPath_inclusion, ← whiskerLeft_comp_assoc, generator_internalComposition_inclusion]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [internalPrepend_inclusion]
  have h := congrArg (fun f => f ≫ C.inclusion A D I (i :: w) x y)
    (C.prependMap_generatorTerm_append A D I i w x y)
  simpa only [term_cons, whiskerLeft_comp, Category.assoc, Category.id_comp] using h

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
