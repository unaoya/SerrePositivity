module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.PathComposition
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoinAssociativity
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoinUnit
public import SerrePositivity.DifferentialGraded.Complexes.AssociatorCochainNaturality

/-! # cell pathの先頭Hom作用の結合・単位・全次数自然性

## 概要
cell pathの先頭Hom作用の結合・単位・全次数自然性。

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

lemma prependMap_assoc (w : List I) (x y z t : D) :
    (eComp (Complex A) x y z ▷ C.term A D I w z t) ≫ C.prependMap A D I w x z t =
    (α_ (homObject A D x y) (homObject A D y z) (C.term A D I w z t)).hom ≫
      (homObject A D x y) ◁ C.prependMap A D I w y z t ≫ C.prependMap A D I w x y t := by
  cases w with
  | nil => exact (e_assoc' (Complex A) x y z t).symm
  | cons i w =>
    simpa only [prependMap, term, tensorHom_id] using
      tensorJoin_assoc (homObject A D x y) (homObject A D y z) (homObject A D z (C.source i))
        (homObject A D x z) (homObject A D y (C.source i)) (homObject A D x (C.source i))
        (C.generator A D I i ⊗ C.term A D I w (C.target i) t)
        (eComp (Complex A) x y z) (eComp (Complex A) y z (C.source i))
        (eComp (Complex A) x z (C.source i)) (eComp (Complex A) x y (C.source i))
        (e_assoc' (Complex A) x y z (C.source i)).symm

lemma prependMap_left_unit (w : List I) (x y : D) :
    (λ_ (C.term A D I w x y)).inv ≫ eId (Complex A) x ▷ C.term A D I w x y ≫
      C.prependMap A D I w x x y = 𝟙 (C.term A D I w x y) := by
  cases w with
  | nil => exact e_id_comp (Complex A) x y
  | cons i w =>
    simpa only [prependMap, term, tensorHom_id] using
      tensorJoin_left_unit (homObject A D x x) (homObject A D x (C.source i))
        (C.generator A D I i ⊗ C.term A D I w (C.target i) y) (eId (Complex A) x)
        (eComp (Complex A) x x (C.source i)) (e_id_comp (Complex A) x (C.source i))

lemma prependMap_tail_cochain (i : I) (w w' : List I) (x y z : D)
    (p : ℤ) (f : Cochain (C.generator A D I i ⊗ C.term A D I w (C.target i) z)
      (C.generator A D I i ⊗ C.term A D I w' (C.target i) z) p) :
    (Cochain.ofHom (C.prependMap A D I (i :: w) x y z)).comp
      ((tensorLeftHom (homObject A D x (C.source i)) _ _).f p f) (zero_add p) =
    ((tensorLeftHom (homObject A D x y) _ _).f p
      ((tensorLeftHom (homObject A D y (C.source i)) _ _).f p f)).comp
      (Cochain.ofHom (C.prependMap A D I (i :: w') x y z)) (add_zero p) := by
  simpa only [prependMap, tensorHom_id] using
    tensorJoin_cochain_naturality (homObject A D x y) (homObject A D y (C.source i))
      (homObject A D x (C.source i)) _ _ (eComp (Complex A) x y (C.source i)) p f

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
