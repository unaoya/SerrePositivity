module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.PrependBoundary
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Differential
public import SerrePositivity.DifferentialGraded.Complexes.Composition

/-! # 任意次数cell path：PrependDifferential

## 概要
任意次数cell path：PrependDifferential。

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

/-- 空pathを左に置く合成の、最終微分についてのLeibniz則。 -/
lemma internalPrepend_total_d_apply (x y z : D) (p q n : ℤ)
    (hn : p + q = n) (a : (homObject A D x y).X p) (b : (C.internalHom A D I y z).X q) :
    (C.attachedHom A D I x z).d n (n + 1)
      ((C.internalPrepend A D I x y z).f n
        (ιTensorObj (homObject A D x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b))) =
    (C.internalPrepend A D I x y z).f (n + 1)
      (ιTensorObj (homObject A D x y) (C.internalHom A D I y z) (p + 1) q (n + 1)
        (by omega) ((homObject A D x y).d p (p + 1) a ⊗ₜ[A] b)) +
    p.negOnePow • (C.internalPrepend A D I x y z).f (n + 1)
      (ιTensorObj (homObject A D x y) (C.internalHom A D I y z) p (q + 1) (n + 1)
        (by omega) (a ⊗ₜ[A] (C.attachedHom A D I y z).d q (q + 1) b)) := by
  have hi := ConcreteCategory.congr_hom ((C.internalPrepend A D I x y z).comm n (n + 1))
    (ιTensorObj (homObject A D x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b))
  change (C.internalHom A D I x z).d n (n + 1) (_ : (C.internalHom A D I x z).X n) =
    (C.internalPrepend A D I x y z).f (n + 1)
      ((homObject A D x y ⊗ C.internalHom A D I y z).d n (n + 1)
        (ιTensorObj (homObject A D x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b))) at hi
  have hd := SerrePositivity.cochainTensor_d_apply_ι
    (homObject A D x y) (C.internalHom A D I y z) p q n hn a b
  have hi' := hi.trans (congrArg (fun v :
      (homObject A D x y ⊗ C.internalHom A D I y z).X (n + 1) =>
    (C.internalPrepend A D I x y z).f (n + 1) v) hd)
  clear hi
  have hi := hi'
  rw [map_add, chain_units_smul] at hi
  rw [attachedHom_d, attachedHom_d]
  change (C.internalHom A D I x z).d n (n + 1)
      ((C.internalPrepend A D I x y z).f n
        (ιTensorObj (homObject A D x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b))) +
      (C.replacement A D I x z).v n (n + 1) rfl
        ((C.internalPrepend A D I x y z).f n
          (ιTensorObj (homObject A D x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b))) =
    (C.internalPrepend A D I x y z).f (n + 1)
      (ιTensorObj (homObject A D x y) (C.internalHom A D I y z) (p + 1) q (n + 1)
        (by omega) ((homObject A D x y).d p (p + 1) a ⊗ₜ[A] b)) +
    p.negOnePow • (C.internalPrepend A D I x y z).f (n + 1)
      (ιTensorObj (homObject A D x y) (C.internalHom A D I y z) p (q + 1) (n + 1)
        (by omega) (a ⊗ₜ[A] ((C.internalHom A D I y z).d q (q + 1) b +
          (C.replacement A D I y z).v q (q + 1) rfl b)))
  exact (congrArg₂ (· + ·) hi (C.internalPrepend_replacement_apply A D I x y z p q n hn a b)).trans
    (by
    simp only [TensorProduct.tmul_add, map_add, smul_add]
    abel)

/-- 元のHomは最終Hom複体へ先頭から作用する。これは最終微分に関するchain map。 -/
def attachedPrepend (x y z : D) :
    homObject A D x y ⊗ C.attachedHom A D I y z ⟶ C.attachedHom A D I x z :=
  tensorLift (fun i j n h =>
    ιTensorObj (homObject A D x y) (C.internalHom A D I y z) i j n h ≫
      (C.internalPrepend A D I x y z).f n) (fun i j => by
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro a b
        exact C.internalPrepend_total_d_apply A D I x y z i j (i + j) rfl a b)

lemma attachedPrepend_ι (x y z : D) (i j n : ℤ) (hn : i + j = n) :
    ιTensorObj (homObject A D x y) (C.attachedHom A D I y z) i j n hn ≫
      (C.attachedPrepend A D I x y z).f n =
    ιTensorObj (homObject A D x y) (C.internalHom A D I y z) i j n hn ≫
      (C.internalPrepend A D I x y z).f n :=
  ι_tensorLift _ _ i j n hn

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
