module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.DoubleFaceSum
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # 任意次数cellの全path上の境界置換作用素は二乗零

## 概要
任意次数cellの全path上の境界置換作用素は二乗零。

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

lemma pathCochain_ext (x y : D) {T : Complex A} (p : ℤ)
    (f g : Cochain (C.internalHom A D I x y) T p)
    (h : ∀ w : List I, (Cochain.ofHom (C.inclusion A D I w x y)).comp f (zero_add p) =
      (Cochain.ofHom (C.inclusion A D I w x y)).comp g (zero_add p)) : f = g := by
  apply Cochain.ext
  intro i n hn
  let ev := HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i
  apply (isColimitOfPreserves ev
    (colimit.isColimit (Discrete.functor (fun w : List I => C.term A D I w x y)))).hom_ext
  intro w
  change (C.inclusion A D I w.as x y).f i ≫ f.v i n hn =
    (C.inclusion A D I w.as x y).f i ≫ g.v i n hn
  simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using
    congrArg (fun z : Cochain (C.term A D I w.as x y) T p => z.v i n hn) (h w.as)

lemma replacement_square_precomp_double_sum (w : List I) (x y : D) :
    (Cochain.ofHom (C.inclusion A D I w x y)).comp
      ((C.replacement A D I x y).comp (C.replacement A D I x y)
        (show (1 : ℤ) + 1 = 2 by omega)) (zero_add 2) =
    ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.range (w.length - 1),
      C.replacementPair A D I w i j x y := by
  rw [replacement_square_precomp]
  apply Finset.sum_congr rfl
  intro i hi
  let R : Cochain (C.term A D I (w.eraseIdx i) x y) (C.internalHom A D I x y) 1 →+
      Cochain (C.term A D I w x y) (C.internalHom A D I x y) 2 :=
    { toFun := fun f => (C.replaceFace A D I w i x y).comp f (by omega)
      map_zero' := Cochain.comp_zero _ _
      map_add' := fun f g => Cochain.comp_add _ f g _ }
  change R (C.replaceRow A D I (w.eraseIdx i) x y) = _
  rw [replaceRow, map_sum, List.length_eraseIdx_of_lt (Finset.mem_range.mp hi)]
  apply Finset.sum_congr rfl
  intro j _
  change (C.replaceFace A D I w i x y).comp
      ((C.replaceFace A D I (w.eraseIdx i) j x y).comp
        (Cochain.ofHom (C.inclusion A D I ((w.eraseIdx i).eraseIdx j) x y)) (add_zero 1))
      (show (1 : ℤ) + 1 = 2 by omega) =
    ((C.replaceFace A D I w i x y).comp (C.replaceFace A D I (w.eraseIdx i) j x y)
      (show (1 : ℤ) + 1 = 2 by omega)).comp
      (Cochain.ofHom (C.inclusion A D I ((w.eraseIdx i).eraseIdx j) x y)) (add_zero 2)
  exact (Cochain.comp_assoc_of_third_is_zero_cochain _ _ _ _).symm

lemma replacement_square_zero (x y : D) :
    (C.replacement A D I x y).comp (C.replacement A D I x y)
      (show (1 : ℤ) + 1 = 2 by omega) = 0 := by
  apply C.pathCochain_ext A D I x y 2
  intro w
  rw [replacement_square_precomp_double_sum, replacementPair_double_sum_zero, Cochain.comp_zero]

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
