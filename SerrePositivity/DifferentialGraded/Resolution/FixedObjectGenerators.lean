module
public import SerrePositivity.DifferentialGraded.Resolution.FixedObjectMapExtension

/-! # 固定対象cell付加の生成元と比較による像 -/
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
