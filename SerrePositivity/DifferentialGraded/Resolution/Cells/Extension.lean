module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.EvaluationComposition

/-! # 指定原始元を持つdg関手の任意次数cell付加への延長 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
open CategoryTheory HomologicalComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {I : Type w} [Small.{u} I]
  {C : Family A D I} {E : Type z} [DGCategory A E] {F : DGFunctor A D E}
variable (P : PrimitiveData A D I C E F)

/-- 各生成cellを指定原始元へ送る主豊穣dg関手。 -/
def extension : DGFunctor A (C.Objects A D I) E where
  obj x := F.obj x.val
  map x y := P.attachedEvaluation x.val y.val
  map_id x := P.attachedEvaluation_unit x.val
  map_comp x y z := P.attachedEvaluation_composition x.val y.val z.val

lemma embedding_comp_extension : (C.embedding A D I).comp P.extension = F := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (C.embedding A D I).comp P.extension) (G := F) (fun _ => rfl)
  intro x y
  change (C.originalHomInclusion A D I x y ≫ P.attachedEvaluation x y) ≫ eqToHom (by rfl) = _
  rw [eqToHom_refl, Category.comp_id, attachedEvaluation_original]

lemma extension_generator (i : I) :
    (P.extension.map (⟨C.source i⟩ : C.Objects A D I) ⟨C.target i⟩).f (C.degree i)
      (C.generatorElement A D I i) = P.primitive i := P.attachedEvaluation_generator i

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
