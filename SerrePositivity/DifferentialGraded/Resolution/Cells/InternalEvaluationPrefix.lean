module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.InternalEvaluation
public import SerrePositivity.DifferentialGraded.Resolution.Cells.EvaluationPrefix
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Prefix

/-! # 全path直和への前方Hom・任意次数生成元追加と評価の整合性

## 概要
全path直和への前方Hom・任意次数生成元追加と評価の整合性。

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
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {I : Type w} [Small.{u} I]
  {C : Family A D I} {E : Type z} [DGCategory A E] {F : DGFunctor A D E}
variable (P : PrimitiveData A D I C E F)

lemma internalEvaluation_prefixPath (b : I) (x y : D) :
    (Cochain.ofHom (C.prefixPath A D I b x y)).comp (P.internalEvaluation x y) (zero_add 0) =
    ((tensorLeftHom (homObject A D x (C.source b))
      (C.generator A D I b ⊗ C.internalHom A D I (C.target b) y)
      (C.generator A D I b ⊗ homObject A E (F.obj (C.target b)) (F.obj y))).f 0
      ((tensorLeftHom (C.generator A D I b) (C.internalHom A D I (C.target b) y)
        (homObject A E (F.obj (C.target b)) (F.obj y))).f 0
          (P.internalEvaluation (C.target b) y))).comp
      (P.evaluationPrefixAction b x y) (zero_add 0) := by
  apply C.prefixPathCochain_ext A D I b x y 0
  intro w
  have ht :
      (Cochain.ofHom ((homObject A D x (C.source b)) ◁
        ((C.generator A D I b) ◁ C.inclusion A D I w (C.target b) y))).comp
        ((tensorLeftHom (homObject A D x (C.source b))
          (C.generator A D I b ⊗ C.internalHom A D I (C.target b) y)
          (C.generator A D I b ⊗ homObject A E (F.obj (C.target b)) (F.obj y))).f 0
          ((tensorLeftHom (C.generator A D I b) (C.internalHom A D I (C.target b) y)
            (homObject A E (F.obj (C.target b)) (F.obj y))).f 0
              (P.internalEvaluation (C.target b) y))) (zero_add 0) =
      (tensorLeftHom (homObject A D x (C.source b))
        (C.generator A D I b ⊗ C.term A D I w (C.target b) y)
        (C.generator A D I b ⊗ homObject A E (F.obj (C.target b)) (F.obj y))).f 0
        ((tensorLeftHom (C.generator A D I b) (C.term A D I w (C.target b) y)
          (homObject A E (F.obj (C.target b)) (F.obj y))).f 0
            (P.pathEvaluation w (C.target b) y)) := by
    rw [← tensorLeftHom_ofHom (homObject A D x (C.source b)), ← tensorLeftHom_cochain_comp,
      ← tensorLeftHom_ofHom (C.generator A D I b), ← tensorLeftHom_cochain_comp,
      internalEvaluation_precomp]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    Family.prefixPath_inclusion, internalEvaluation_precomp,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, ht]
  exact P.pathEvaluation_cons_action b w x y

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
