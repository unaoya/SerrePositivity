module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.BoundaryFaces
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift

/-! # 全path上の指定境界置換作用素

## 概要
各生成元を境界に置換する有限和を、閉じた次数+1の自己cochainへ貼り合わせる。
この段階では二乗零と最終合成のLeibnizはまだ主張しない。

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

def replaceSummand (w : List I) (i : ℕ) (x y : D) :
    Cochain (C.term A D I w x y) (C.internalHom A D I x y) 1 :=
  (C.replaceFace A D I w i x y).comp
    (Cochain.ofHom (C.inclusion A D I (w.eraseIdx i) x y)) (add_zero 1)

lemma replaceSummand_closed (w : List I) (i : ℕ) (x y : D) :
    δ 1 2 (C.replaceSummand A D I w i x y) = 0 := by
  rw [replaceSummand, δ_comp_ofHom, replaceFace_closed]
  exact Cochain.zero_comp _ _

def replaceRow (w : List I) (x y : D) :
    Cochain (C.term A D I w x y) (C.internalHom A D I x y) 1 :=
  ∑ i ∈ Finset.range w.length, C.replaceSummand A D I w i x y

lemma replaceRow_closed (w : List I) (x y : D) :
    δ 1 2 (C.replaceRow A D I w x y) = 0 := by
  change (δ_hom ℤ _ _ 1 2) (C.replaceRow A D I w x y) = 0
  simp only [replaceRow, map_sum, δ_hom_apply, replaceSummand_closed, Finset.sum_const_zero]

lemma replaceRow_nil (x y : D) : C.replaceRow A D I [] x y = 0 := by simp [replaceRow]

def replacementToShift (x y : D) :
    C.internalHom A D I x y ⟶ (C.internalHom A D I x y)⟦(1 : ℤ)⟧ :=
  Sigma.desc (fun w : List I => Cocycle.equivHomShift.symm
    (Cocycle.mk (C.replaceRow A D I w x y) 2 (by omega) (C.replaceRow_closed A D I w x y)))

def replacement (x y : D) : Cochain (C.internalHom A D I x y) (C.internalHom A D I x y) 1 :=
  (Cocycle.equivHomShift (C.replacementToShift A D I x y)).val

lemma replacement_closed (x y : D) : δ 1 2 (C.replacement A D I x y) = 0 :=
  Cocycle.δ_eq_zero _ _

lemma replacement_precomp (w : List I) (x y : D) :
    (Cochain.ofHom (C.inclusion A D I w x y)).comp (C.replacement A D I x y) (zero_add 1) =
      C.replaceRow A D I w x y := by
  have h : C.inclusion A D I w x y ≫ C.replacementToShift A D I x y =
      Cocycle.equivHomShift.symm (Cocycle.mk (C.replaceRow A D I w x y) 2
        (by omega) (C.replaceRow_closed A D I w x y)) := Sigma.ι_comp_desc _ _
  have hc := congrArg (fun f => (Cocycle.equivHomShift f).val) h
  rw [Cocycle.equivHomShift_comp, AddEquiv.apply_symm_apply] at hc
  exact hc

lemma replacement_originalHom (x y : D) :
    (Cochain.ofHom (C.originalHom A D I x y)).comp (C.replacement A D I x y) (zero_add 1) = 0 :=
  (C.replacement_precomp A D I [] x y).trans (C.replaceRow_nil A D I x y)

/-- 二重置換を各pathに制限すると、最初のfaceと短いpathの置換和になる。 -/
lemma replacement_square_precomp (w : List I) (x y : D) :
    (Cochain.ofHom (C.inclusion A D I w x y)).comp
      ((C.replacement A D I x y).comp (C.replacement A D I x y)
        (show (1 : ℤ) + 1 = 2 by omega)) (zero_add 2) =
    ∑ i ∈ Finset.range w.length, (C.replaceFace A D I w i x y).comp
      (C.replaceRow A D I (w.eraseIdx i) x y) (show (1 : ℤ) + 1 = 2 by omega) := by
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, replacement_precomp]
  let R : Cochain (C.term A D I w x y) (C.internalHom A D I x y) 1 →+
      Cochain (C.term A D I w x y) (C.internalHom A D I x y) 2 :=
    { toFun := fun f => f.comp (C.replacement A D I x y) (by omega)
      map_zero' := Cochain.zero_comp _ _
      map_add' := fun f g => Cochain.add_comp f g _ _ }
  change R (C.replaceRow A D I w x y) = _
  rw [replaceRow, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (C.replaceSummand A D I w i x y).comp (C.replacement A D I x y) (by omega) = _
  rw [replaceSummand, Cochain.comp_assoc_of_second_is_zero_cochain, replacement_precomp]

lemma replacement_square_originalHom (x y : D) :
    (Cochain.ofHom (C.originalHom A D I x y)).comp
      ((C.replacement A D I x y).comp (C.replacement A D I x y)
        (show (1 : ℤ) + 1 = 2 by omega)) (zero_add 2) = 0 := by
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, replacement_originalHom]
  exact Cochain.zero_comp _ _

lemma replacement_square_singleton (i : I) (x y : D) :
    (Cochain.ofHom (C.inclusion A D I [i] x y)).comp
      ((C.replacement A D I x y).comp (C.replacement A D I x y)
        (show (1 : ℤ) + 1 = 2 by omega)) (zero_add 2) = 0 := by
  rw [replacement_square_precomp]
  simp only [List.length_cons, List.length_nil, zero_add, Finset.range_one, Finset.sum_singleton]
  change (C.replaceFirst A D I i [] x y).comp (C.replaceRow A D I [] x y) (by omega) = 0
  rw [replaceRow_nil]
  exact Cochain.comp_zero _ _

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
