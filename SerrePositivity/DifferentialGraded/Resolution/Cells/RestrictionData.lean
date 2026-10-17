module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Extension

/-! # cell付加からのdg関手を元の関手と指定原始元へ制限する -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I) {E : Type z} [DGCategory A E]

abbrev restrictFunctor (G : DGFunctor A (C.Objects A D I) E) : DGFunctor A D E :=
  (C.embedding A D I).comp G

def restrictPrimitives (G : DGFunctor A (C.Objects A D I) E) :
    PrimitiveData A D I C E (C.restrictFunctor A D I G) where
  primitive i := (G.map ⟨C.source i⟩ ⟨C.target i⟩).f (C.degree i) (C.generatorElement A D I i)
  boundary i := by
    have h := congrArg (fun f => f (C.generatorElement A D I i))
      ((G.map ⟨C.source i⟩ ⟨C.target i⟩).comm (C.degree i) (C.degree i + 1))
    change (homObject A E (G.obj ⟨C.source i⟩) (G.obj ⟨C.target i⟩)).d
      (C.degree i) (C.degree i + 1)
      ((G.map ⟨C.source i⟩ ⟨C.target i⟩).f (C.degree i) (C.generatorElement A D I i)) =
      (G.map ⟨C.source i⟩ ⟨C.target i⟩).f (C.degree i + 1)
        ((C.attachedHom A D I (C.source i) (C.target i)).d (C.degree i) (C.degree i + 1)
          (C.generatorElement A D I i)) at h
    rw [differential_generatorElement] at h
    exact h

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
