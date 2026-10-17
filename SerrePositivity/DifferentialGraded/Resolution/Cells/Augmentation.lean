module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Extension

/-! # 全境界cellの同時付加と指定原始元への増大 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCategoryBoundaryCells
open CategoryTheory HomologicalComplex
open DGCellAttachment
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] (F : DGFunctor A D E)

/-- 全境界cellをその添字に保存された原始元へ送る実際の増大dg関手。 -/
def attachedAugmentation :
    DGFunctor A ((boundaryFamily A D E F).Objects A D (Index A D E F)) E :=
  (primitiveData A D E F).extension

lemma embedding_comp_attachedAugmentation :
    ((boundaryFamily A D E F).embedding A D (Index A D E F)).comp
      (attachedAugmentation A D E F) = F :=
  (primitiveData A D E F).embedding_comp_extension

/-- 元の各境界cellは次段のHomで埋まり、指定されたtarget原始元へ厳密に送られる。 -/
lemma attachedAugmentation_fills (x y : D) (c : ComplexBoundaryCell A (F.map x y)) :
    ∃ t : ((boundaryFamily A D E F).attachedHom A D (Index A D E F) x y).X c.degree,
      ((boundaryFamily A D E F).attachedHom A D (Index A D E F) x y).d
        c.degree (c.degree + 1) t =
        ((boundaryFamily A D E F).originalHomInclusion A D (Index A D E F) x y).f
          (c.degree + 1) c.cycle.val ∧
      ((attachedAugmentation A D E F).map ⟨x⟩ ⟨y⟩).f c.degree t = c.primitive := by
  let i : Index A D E F := ⟨x, y, c⟩
  refine ⟨(boundaryFamily A D E F).generatorElement A D (Index A D E F) i, ?_, ?_⟩
  · exact (boundaryFamily A D E F).differential_generatorElement A D (Index A D E F) i
  · exact (primitiveData A D E F).extension_generator i

end SerrePositivity.DifferentialGraded.DGCategoryBoundaryCells
