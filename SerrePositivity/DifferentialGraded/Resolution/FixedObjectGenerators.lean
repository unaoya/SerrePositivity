module
public import SerrePositivity.DifferentialGraded.Resolution.FixedObjectMapExtension

/-! # 固定対象cell付加の生成元と比較による像

## 概要
固定対象cell付加の生成元と比較による像。

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
namespace SerrePositivity.DifferentialGraded.FixedObjectAugmentation
open CategoryTheory HomologicalComplex
variable {A : Type u} [CommRing A] {D : Type v} [dD : DGCategory A D] [Small.{u} D]
  (S : FixedObjectAugmentation A D D id)

/-- 各境界cellの次数にある新しい生成元。 -/
def cellGenerator (i : S.CellIndex) :
    (S.attach.category.Hom i.1 i.2.1).X i.2.2.degree := by
  letI : DGCategory A D := S.category
  exact (@cells A _ D D dD id S).generatorElement A D (@CellIndex A _ D D dD id S) i

lemma attach_map_cellGenerator (i : S.CellIndex) :
    (S.attach.map i.1 i.2.1).f i.2.2.degree (S.cellGenerator i) = i.2.2.primitive := by
  let : DGCategory A D := S.category
  exact @DGCellAttachment.Family.PrimitiveData.attachedEvaluation_generator
    A _ D (@category A _ D D dD id S) (@CellIndex A _ D D dD id S) _ (@cells A _ D D dD id S)
    D dD (@toDGFunctor A _ D D dD id S) (@cellPrimitives A _ D D dD id S) i

namespace Map
variable {S} {E : Type w} [dE : DGCategory A E] [Small.{u} E]
  {T : FixedObjectAugmentation A E E id} {F : DGFunctor A D E} (M : Map S T F)

lemma attachedHom_cellGenerator (i : S.CellIndex) :
    (M.attachedHom i.1 i.2.1).f i.2.2.degree (S.cellGenerator i) =
      T.cellGenerator (M.cellMap i) := by
  let : DGCategory A D := S.category
  let : DGCategory A E := T.category
  exact (extensionPrimitives (dD := dD) (dE := dE) M).extension_generator i

end Map
end SerrePositivity.DifferentialGraded.FixedObjectAugmentation
