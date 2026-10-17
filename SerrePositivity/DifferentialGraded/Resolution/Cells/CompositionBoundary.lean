module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.AppendBoundary
public import SerrePositivity.DifferentialGraded.Resolution.Cells.TensorRightPathCochainExt

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
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
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
