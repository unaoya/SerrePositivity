module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.BoundaryInterchange
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoinActionNaturality

/-! # 指定境界を左端へ挿入する表示と先頭Hom作用

## 概要
指定境界を左端へ挿入する表示と先頭Hom作用。

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
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w)
variable (C : Family A D I)

def replaceHead (i : I) (w : List I) (y : D) :
    Cochain (C.generator A D I i ⊗ C.term A D I w (C.target i) y)
      (C.term A D I w (C.source i) y) 1 :=
  ((tensorRightHom (C.term A D I w (C.target i) y) _ _).f 1
    (C.boundaryCochain A D I i)).comp
    (Cochain.ofHom (C.prependMap A D I w (C.source i) (C.target i) y)) (add_zero 1)

lemma replaceHead_closed (i : I) (w : List I) (y : D) :
    δ 1 2 (C.replaceHead A D I i w y) = 0 := by
  rw [replaceHead, δ_comp_ofHom]
  have h := homComplexMap_closed
    (tensorRightHom (C.term A D I w (C.target i) y) (C.generator A D I i)
      (homObject A D (C.source i) (C.target i))) 1
    (C.boundaryCochain A D I i) (C.boundaryCochain_closed A D I i)
  change δ 1 2 ((tensorRightHom (C.term A D I w (C.target i) y) (C.generator A D I i)
    (homObject A D (C.source i) (C.target i))).f 1 (C.boundaryCochain A D I i)) = 0 at h
  rw [h]
  exact Cochain.zero_comp _ _

/-- 先頭置換を、左端での置換と元のHom作用へ分解する。 -/
lemma replaceFirst_eq_head (i : I) (w : List I) (x y : D) :
    C.replaceFirst A D I i w x y =
    ((tensorLeftHom (homObject A D x (C.source i)) _ _).f 1
      (C.replaceHead A D I i w y)).comp
      (Cochain.ofHom (C.prependMap A D I w x (C.source i) y)) (add_zero 1) := by
  have hc : (α_ (homObject A D x (C.source i))
      (homObject A D (C.source i) (C.target i)) (C.term A D I w (C.target i) y)).inv ≫
      (eComp (Complex A) x (C.source i) (C.target i) ▷ C.term A D I w (C.target i) y) ≫
      C.prependMap A D I w x (C.target i) y =
      (homObject A D x (C.source i)) ◁ C.prependMap A D I w (C.source i) (C.target i) y ≫
      C.prependMap A D I w x (C.source i) y := by
    rw [C.prependMap_assoc A D I w x (C.source i) (C.target i) y, Iso.inv_hom_id_assoc]
  rw [replaceFirst, hc, replaceHead, tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp]
  rfl

attribute [local irreducible] replaceHead replaceFirst

lemma prependMap_replaceHead (i : I) (w : List I) (x y z : D) :
    (Cochain.ofHom (C.prependMap A D I (i :: w) x y z)).comp
    ((tensorLeftHom (homObject A D x (C.source i)) _ _).f 1
      (C.replaceHead A D I i w z)) (zero_add 1) =
    ((tensorLeftHom (homObject A D x y) _ _).f 1
      ((tensorLeftHom (homObject A D y (C.source i)) _ _).f 1
        (C.replaceHead A D I i w z))).comp
    (Cochain.ofHom ((α_ (homObject A D x y) (homObject A D y (C.source i))
      (C.term A D I w (C.source i) z)).inv ≫
      (eComp (Complex A) x y (C.source i) ▷ C.term A D I w (C.source i) z))) (add_zero 1) := by
  simpa only [prependMap, term, tensorHom_id] using
    tensorJoin_cochain_naturality (homObject A D x y)
      (homObject A D y (C.source i)) (homObject A D x (C.source i)) _ _
      (eComp (Complex A) x y (C.source i)) 1 (C.replaceHead A D I i w z)

/-- 先頭Homの合成は先頭生成元の境界置換とも可換する。 -/
lemma prependMap_replaceFirst (i : I) (w : List I) (x y z : D) :
    (Cochain.ofHom (C.prependMap A D I (i :: w) x y z)).comp
      (C.replaceFirst A D I i w x z) (zero_add 1) =
    ((tensorLeftHom (homObject A D x y) _ _).f 1 (C.replaceFirst A D I i w y z)).comp
      (Cochain.ofHom (C.prependMap A D I w x y z)) (add_zero 1) := by
  have hc : (α_ (homObject A D x y) (homObject A D y (C.source i))
      (C.term A D I w (C.source i) z)).inv ≫
      (eComp (Complex A) x y (C.source i) ▷ C.term A D I w (C.source i) z) ≫
      C.prependMap A D I w x (C.source i) z =
      (homObject A D x y) ◁ C.prependMap A D I w y (C.source i) z ≫
      C.prependMap A D I w x y z := by
    rw [C.prependMap_assoc A D I w x y (C.source i) z, Iso.inv_hom_id_assoc]
  rw [replaceFirst_eq_head, replaceFirst_eq_head]
  simpa only [prependMap, term, tensorHom_id] using
    tensorJoin_action_cochain (homObject A D x y) (homObject A D y (C.source i))
      (homObject A D x (C.source i)) _ _ _ _ 1 (C.replaceHead A D I i w z)
      (eComp (Complex A) x y (C.source i))
      (C.prependMap A D I w x (C.source i) z) (C.prependMap A D I w y (C.source i) z)
      (C.prependMap A D I w x y z) hc

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
