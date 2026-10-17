module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.PrependBoundaryRows
public import SerrePositivity.DifferentialGraded.Resolution.Cells.TensorPathCochainExt

/-! # 任意次数cell path：PrependBoundary

## 概要
任意次数cell path：PrependBoundary。

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

/-- 空pathを左に置く合成の境界置換Leibniz則。左の元のHomには消去項がない。 -/
lemma internalPrepend_replacement (x y z : D) :
    (Cochain.ofHom (C.internalPrepend A D I x y z)).comp (C.replacement A D I x z) (zero_add 1) =
    ((tensorLeftHom (homObject A D x y) (C.internalHom A D I y z)
      (C.internalHom A D I y z)).f 1 (C.replacement A D I y z)).comp
      (Cochain.ofHom (C.internalPrepend A D I x y z)) (add_zero 1) := by
  apply C.tensorLeftPathCochain_ext A D I y z (homObject A D x y) 1
  intro w
  have hb : (Cochain.ofHom ((homObject A D x y) ◁ C.inclusion A D I w y z)).comp
      ((tensorLeftHom (homObject A D x y) (C.internalHom A D I y z)
        (C.internalHom A D I y z)).f 1 (C.replacement A D I y z)) (zero_add 1) =
      (tensorLeftHom (homObject A D x y) (C.term A D I w y z)
        (C.internalHom A D I y z)).f 1 (C.replaceRow A D I w y z) := by
    rw [← tensorLeftHom_ofHom, ← tensorLeftHom_cochain_comp, replacement_precomp]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    internalPrepend_inclusion, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    replacement_precomp, ← Cochain.comp_assoc_of_first_is_zero_cochain, hb]
  exact C.prependMap_replaceRow A D I w x y z

/-- 空pathを左に置く消去Leibniz則の斉次成分。右側の消去には(-1)^pが付く。 -/
lemma internalPrepend_replacement_apply (x y z : D) (p q n : ℤ)
    (hn : p + q = n) (a : (homObject A D x y).X p) (b : (C.internalHom A D I y z).X q) :
    (C.replacement A D I x z).v n (n + 1) rfl
      ((C.internalPrepend A D I x y z).f n
        (ιTensorObj (homObject A D x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b))) =
    p.negOnePow • (C.internalPrepend A D I x y z).f (n + 1)
      (ιTensorObj (homObject A D x y) (C.internalHom A D I y z) p (q + 1) (n + 1)
        (by omega) (a ⊗ₜ[A] (C.replacement A D I y z).v q (q + 1) rfl b)) := by
  have h := congrArg (fun f : Cochain
      (homObject A D x y ⊗ C.internalHom A D I y z) (C.internalHom A D I x z) 1 =>
    f.v n (n + 1) rfl
      (ιTensorObj (homObject A D x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b)))
    (C.internalPrepend_replacement A D I x y z)
  rw [cochain_ofHom_comp_apply, cochain_comp_ofHom_apply,
    tensorLeftHom_apply, chain_units_smul] at h
  simpa only [one_mul] using h

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
