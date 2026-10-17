module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Category
public import SerrePositivity.DifferentialGraded.Complexes.CoproductSubfamily
public import SerrePositivity.DifferentialGraded.Complexes.PerturbationRestriction

/-! # path長上限による内部Homと指定境界置換の制限

## 概要
path長上限による内部Homと指定境界置換の制限。

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
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I)

def lengthSet (n : ℕ) : Set (List I) := {w | w.length ≤ n}

abbrev lengthInternalHom (n : ℕ) (x y : D) : Complex A :=
  ComplexCoproduct.subfamily (fun w => C.term A D I w x y) (lengthSet I n)

def lengthInclusion (n : ℕ) (x y : D) :
    C.lengthInternalHom A D I n x y ⟶ C.internalHom A D I x y :=
  ComplexCoproduct.inclusion (fun w => C.term A D I w x y) (lengthSet I n)

def lengthProjection (n : ℕ) (x y : D) :
    C.internalHom A D I x y ⟶ C.lengthInternalHom A D I n x y :=
  ComplexCoproduct.projection (fun w => C.term A D I w x y) (lengthSet I n)

lemma lengthInclusion_projection (n : ℕ) (x y : D) :
    C.lengthInclusion A D I n x y ≫ C.lengthProjection A D I n x y = 𝟙 _ :=
  ComplexCoproduct.inclusion_projection _ _

def lengthReplacement (n : ℕ) (x y : D) :
    Cochain (C.lengthInternalHom A D I n x y) (C.lengthInternalHom A D I n x y) 1 :=
  ((Cochain.ofHom (C.lengthInclusion A D I n x y)).comp
    (C.replacement A D I x y) (zero_add 1)).comp
    (Cochain.ofHom (C.lengthProjection A D I n x y)) (add_zero 1)

lemma replaceSummand_length_projection_inclusion (n : ℕ) (x y : D)
    (w : List I) (hw : w.length ≤ n) (j : ℕ) :
    (C.replaceSummand A D I w j x y).comp
      (Cochain.ofHom (C.lengthProjection A D I n x y ≫ C.lengthInclusion A D I n x y))
        (add_zero 1) = C.replaceSummand A D I w j x y := by
  have hj : w.eraseIdx j ∈ lengthSet I n := (List.length_eraseIdx_le w j).trans hw
  have h : C.inclusion A D I (w.eraseIdx j) x y ≫
      (C.lengthProjection A D I n x y ≫ C.lengthInclusion A D I n x y) =
      C.inclusion A D I (w.eraseIdx j) x y := by
    change Sigma.ι (fun w => C.term A D I w x y) (w.eraseIdx j) ≫
      (ComplexCoproduct.projection _ (lengthSet I n) ≫
        ComplexCoproduct.inclusion _ (lengthSet I n)) = _
    rw [← Category.assoc, ComplexCoproduct.ι_projection_mem
      (fun w : List I => C.term A D I w x y) (lengthSet I n) (w.eraseIdx j) hj]
    exact ComplexCoproduct.ι_inclusion (fun w : List I => C.term A D I w x y)
      (lengthSet I n) ⟨w.eraseIdx j, hj⟩
  rw [replaceSummand, Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, h]

lemma replaceRow_length_projection_inclusion (n : ℕ) (x y : D)
    (w : List I) (hw : w.length ≤ n) :
    (C.replaceRow A D I w x y).comp
      (Cochain.ofHom (C.lengthProjection A D I n x y ≫ C.lengthInclusion A D I n x y))
        (add_zero 1) = C.replaceRow A D I w x y := by
  rw [replaceRow]
  let R : Cochain (C.term A D I w x y) (C.internalHom A D I x y) 1 →+
      Cochain (C.term A D I w x y) (C.internalHom A D I x y) 1 :=
    { toFun := fun f => f.comp (Cochain.ofHom
        (C.lengthProjection A D I n x y ≫ C.lengthInclusion A D I n x y)) (add_zero 1)
      map_zero' := Cochain.zero_comp _ _
      map_add' := fun f g => Cochain.add_comp f g _ _ }
  change R (∑ j ∈ Finset.range w.length, C.replaceSummand A D I w j x y) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact C.replaceSummand_length_projection_inclusion A D I n x y w hw j

lemma lengthReplacement_inclusion (n : ℕ) (x y : D) :
    (Cochain.ofHom (C.lengthInclusion A D I n x y)).comp
      (C.replacement A D I x y) (zero_add 1) =
    (C.lengthReplacement A D I n x y).comp
      (Cochain.ofHom (C.lengthInclusion A D I n x y)) (add_zero 1) := by
  rw [lengthReplacement, Cochain.comp_assoc_of_third_is_zero_cochain,
    ← Cochain.ofHom_comp]
  apply ComplexCoproduct.cochain_ext
  intro w
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]
  have h : Sigma.ι (fun w : lengthSet I n => C.term A D I w.val x y) w ≫
      C.lengthInclusion A D I n x y = C.inclusion A D I w.val x y :=
    ComplexCoproduct.ι_inclusion _ _ w
  rw [h, replacement_precomp, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, h, replacement_precomp]
  exact (C.replaceRow_length_projection_inclusion A D I n x y w.val w.property).symm

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
