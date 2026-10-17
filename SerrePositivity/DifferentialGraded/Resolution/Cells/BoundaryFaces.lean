module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.BoundaryCochain
public import SerrePositivity.DifferentialGraded.Resolution.Cells.PathComposition

/-! # 各有限pathで一つの生成元を指定境界へ置換するcochain

## 概要
各有限pathで一つの生成元を指定境界へ置換するcochain。

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

/-- 先頭生成元を境界へ置き換え、左の既存Homと豊穣合成する。 -/
def replaceFirst (i : I) (w : List I) (x y : D) :
    Cochain (C.term A D I (i :: w) x y) (C.term A D I w x y) 1 :=
  (C.replaceMiddle A D I i (homObject A D x (C.source i))
      (C.term A D I w (C.target i) y)).comp
    (Cochain.ofHom
      ((α_ (homObject A D x (C.source i)) (homObject A D (C.source i) (C.target i))
        (C.term A D I w (C.target i) y)).inv ≫
        (eComp (Complex A) x (C.source i) (C.target i) ▷ C.term A D I w (C.target i) y) ≫
        C.prependMap A D I w x (C.target i) y)) (add_zero 1)

lemma replaceFirst_closed (i : I) (w : List I) (x y : D) :
    δ 1 2 (C.replaceFirst A D I i w x y) = 0 := by
  rw [replaceFirst, δ_comp_ofHom, replaceMiddle_closed]
  exact Cochain.zero_comp _ _

/-- i番目の生成元を境界へ置換する。範囲外の添字は零。 -/
def replaceFace : ∀ (w : List I) (i : ℕ) (x y : D),
    Cochain (C.term A D I w x y) (C.term A D I (w.eraseIdx i) x y) 1
  | [], _, _, _ => 0
  | i :: w, 0, x, y => C.replaceFirst A D I i w x y
  | i :: w, j + 1, x, y =>
    (tensorLeftHom (homObject A D x (C.source i)) _ _).f 1
      ((tensorLeftHom (C.generator A D I i) _ _).f 1 (replaceFace w j (C.target i) y))

lemma replaceFace_closed (w : List I) (i : ℕ) (x y : D) :
    δ 1 2 (C.replaceFace A D I w i x y) = 0 := by
  induction w generalizing i x y with
  | nil => exact δ_zero _ _
  | cons j w ih =>
    cases i with
    | zero => exact C.replaceFirst_closed A D I j w x y
    | succ i => exact homComplexMap_closed _ 1 _ (homComplexMap_closed _ 1 _ (ih i (C.target j) y))

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
