module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.PrimitiveAction
public import SerrePositivity.DifferentialGraded.Resolution.Cells.PathEvaluationPrepend
public import SerrePositivity.DifferentialGraded.Resolution.Cells.BoundaryHead
public import SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochainLeftMap

/-! # 原始元作用の微分と有限path先頭境界の評価

## 概要
原始元作用の微分と有限path先頭境界の評価。

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
universe u v w z
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {I : Type w}
  {C : Family A D I} {E : Type z} [DGCategory A E] {F : DGFunctor A D E}
variable (P : PrimitiveData A D I C E F)

lemma boundaryAction_pathEvaluation (i : I) (w : List I) (y : D) :
    ((tensorLeftHom (C.generator A D I i) (C.term A D I w (C.target i) y)
      (homObject A E (F.obj (C.target i)) (F.obj y))).f 0
        (P.pathEvaluation w (C.target i) y)).comp
      (δ 0 1 (P.primitiveAction i (F.obj y))) (zero_add 1) =
    (C.replaceHead A D I i w y).comp (P.pathEvaluation w (C.source i) y) (add_zero 1) := by
  have h := tensorCochain_interchange (C.generator A D I i)
    (homObject A D (C.source i) (C.target i))
    (C.term A D I w (C.target i) y) (homObject A E (F.obj (C.target i)) (F.obj y))
    1 0 1 (add_zero 1) (zero_add 1)
    (C.boundaryCochain A D I i) (P.pathEvaluation w (C.target i) y)
  simp only [mul_zero, Int.negOnePow_zero, one_smul] at h
  have he :
      ((tensorLeftHom (homObject A D (C.source i) (C.target i))
        (C.term A D I w (C.target i) y)
        (homObject A E (F.obj (C.target i)) (F.obj y))).f 0
          (P.pathEvaluation w (C.target i) y)).comp
        (Cochain.ofHom (P.boundaryOriginalAction i (F.obj y))) (zero_add 0) =
      (tensorZeroCochain (Cochain.ofHom (F.map (C.source i) (C.target i)))
        (P.pathEvaluation w (C.target i) y)).comp
        (Cochain.ofHom (eComp (Complex A) (F.obj (C.source i)) (F.obj (C.target i)) (F.obj y)))
          (zero_add 0) := by
    rw [boundaryOriginalAction, Cochain.ofHom_comp,
      ← Cochain.comp_assoc_of_third_is_zero_cochain, ← tensorZeroCochain_ofHom_left]
  rw [primitiveAction_differential, ← Cochain.comp_assoc_of_third_is_zero_cochain, ← h,
    Cochain.comp_assoc_of_third_is_zero_cochain, he, ← pathEvaluation_prepend,
    ← Cochain.comp_assoc_of_second_is_zero_cochain]
  rfl

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
