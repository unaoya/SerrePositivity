module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.PathEvaluation
public import SerrePositivity.DifferentialGraded.Resolution.Cells.PathCochainDesc

/-! # 指定原始元付きdg関手による全path直和の評価cochain

## 概要
指定原始元付きdg関手による全path直和の評価cochain。

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

/-- 各有限pathの評価を貼り合わせた次数0 cochain。微分との整合性は別に証明する。 -/
def internalEvaluation (x y : D) :
    Cochain (C.internalHom A D I x y)
      (homObject A E (F.obj x) (F.obj y)) 0 :=
  C.pathCochainDesc A D I x y _ 0 (fun w => P.pathEvaluation w x y)

lemma internalEvaluation_precomp (x y : D) (w : List I) :
    (Cochain.ofHom (C.inclusion A D I w x y)).comp (P.internalEvaluation x y) (zero_add 0) =
      P.pathEvaluation w x y := C.pathCochainDesc_precomp A D I x y _ 0 _ w

lemma internalEvaluation_original (x y : D) :
    (Cochain.ofHom (C.originalHom A D I x y)).comp (P.internalEvaluation x y) (zero_add 0) =
      Cochain.ofHom (F.map x y) := P.internalEvaluation_precomp x y []

lemma internalEvaluation_generator (i : I) :
    (Cochain.ofHom (C.generatorInclusion A D I i)).comp
      (P.internalEvaluation (C.source i) (C.target i)) (zero_add 0) = P.cochain i := by
  rw [Family.generatorInclusion, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain, internalEvaluation_precomp]
  apply (Cochain.fromSingleEquiv (add_zero (C.degree i))).injective
  apply (moduleElementEquiv A _).injective
  change ((Cochain.ofHom (C.generatorTerm A D I i)).comp
      (P.pathEvaluation [i] (C.source i) (C.target i)) (zero_add 0)).v
      (C.degree i) (C.degree i) (add_zero _)
      ((singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).inv (1 : A)) =
    (P.cochain i).v (C.degree i) (C.degree i) (add_zero _)
      ((singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).inv (1 : A))
  rw [cochain_ofHom_comp_apply, pathEvaluation_generatorTerm, cochain_generator]

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
