module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.InternalEvaluation
public import SerrePositivity.DifferentialGraded.Resolution.Cells.PathEvaluationAppend
public import SerrePositivity.DifferentialGraded.Resolution.Cells.InternalComposition
public import SerrePositivity.DifferentialGraded.Resolution.Cells.TensorTwoPathCochainExt

/-! # 全path直和の評価は内部合成を保つ

## 概要
全path直和の評価は内部合成を保つ。

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

lemma internalEvaluation_composition (x y z : D) :
    (Cochain.ofHom (C.internalComposition A D I x y z)).comp (P.internalEvaluation x z)
      (zero_add 0) =
    (tensorZeroCochain (P.internalEvaluation x y) (P.internalEvaluation y z)).comp
      (Cochain.ofHom (eComp (Complex A) (F.obj x)
        (F.obj y) (F.obj z))) (zero_add 0) := by
  apply C.tensorTwoPathCochain_ext A D I x y z 0
  intro w v
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    Family.internalComposition_inclusion, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain,
    internalEvaluation_precomp,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, tensorZeroCochain_precomp,
    internalEvaluation_precomp, internalEvaluation_precomp]
  exact P.pathEvaluation_append w v x y z

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
