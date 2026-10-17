module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.BoundaryNaturality
public import SerrePositivity.DifferentialGraded.Resolution.Cells.InternalComposition
public import SerrePositivity.DifferentialGraded.Resolution.Cells.BoundaryOperator

/-! # 任意次数cell path：PrependBoundaryRows

## 概要
任意次数cell path：PrependBoundaryRows。

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
/-- 一つの境界置換項を全直和へ入れた後も先頭Hom作用と可換する。 -/
lemma prependMap_replaceSummand (w : List I) (i : ℕ) (x y z : D) :
    (Cochain.ofHom (C.prependMap A D I w x y z)).comp (C.replaceSummand A D I w i x z) (zero_add 1)
      =
    ((tensorLeftHom (homObject A D x y) (C.term A D I w y z)
      (C.internalHom A D I y z)).f 1 (C.replaceSummand A D I w i y z)).comp
      (Cochain.ofHom (C.internalPrepend A D I x y z)) (add_zero 1) := by
  rw [replaceSummand, replaceSummand, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    prependMap_replaceFace, tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain, Cochain.comp_assoc_of_third_is_zero_cochain,
    ← Cochain.ofHom_comp, ← Cochain.ofHom_comp, internalPrepend_inclusion]

/-- 一つのpath上の有限消去和は先頭Hom作用と可換する。 -/
lemma prependMap_replaceRow (w : List I) (x y z : D) :
    (Cochain.ofHom (C.prependMap A D I w x y z)).comp (C.replaceRow A D I w x z) (zero_add 1) =
    ((tensorLeftHom (homObject A D x y) (C.term A D I w y z)
      (C.internalHom A D I y z)).f 1 (C.replaceRow A D I w y z)).comp
      (Cochain.ofHom (C.internalPrepend A D I x y z)) (add_zero 1) := by
  let L : Cochain (C.term A D I w x z) (C.internalHom A D I x z) 1 →+
      Cochain (homObject A D x y ⊗ C.term A D I w y z) (C.internalHom A D I x z) 1 :=
    { toFun := fun f => (Cochain.ofHom (C.prependMap A D I w x y z)).comp f (zero_add 1)
      map_zero' := Cochain.comp_zero _ _
      map_add' := fun f g => Cochain.comp_add _ f g _ }
  let R : Cochain (C.term A D I w y z) (C.internalHom A D I y z) 1 →+
      Cochain (homObject A D x y ⊗ C.term A D I w y z) (C.internalHom A D I x z) 1 :=
    { toFun := fun f => ((tensorLeftHom (homObject A D x y) (C.term A D I w y z)
        (C.internalHom A D I y z)).f 1 f).comp
        (Cochain.ofHom (C.internalPrepend A D I x y z)) (add_zero 1)
      map_zero' := by rw [map_zero]; exact Cochain.zero_comp _ _
      map_add' := fun f g => by rw [map_add, Cochain.add_comp] }
  change L (C.replaceRow A D I w x z) = R (C.replaceRow A D I w y z)
  rw [replaceRow, replaceRow, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact C.prependMap_replaceSummand A D I w i x y z

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
