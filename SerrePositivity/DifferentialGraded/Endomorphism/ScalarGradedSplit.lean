module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarHomElements
public import SerrePositivity.DifferentialGraded.Endomorphism.GradedSplitOfElements

/-! # 実際の加群係数拡大は全次数分裂を保存する -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

lemma scalarModuleHomElement_closed {M N : ModuleCategory A D} (f : M ⟶ N) :
    scalarModuleHomElement φ D (endomorphismClosedElement A D f) =
      endomorphismClosedElement A' (ScalarExtension.DGBaseChange φ D)
        ((ScalarExtension.moduleExtension φ D).map f) :=
  scalarModuleHomElement_cycle φ D f

/-- 環の平坦性を要求せず、全斉次作用に関して分裂する拡大を送る。 -/
def scalarModuleGradedSplit {M N P : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}
    (s : ModuleGradedSplit A D f g) :
    ModuleGradedSplit A' (ScalarExtension.DGBaseChange φ D)
      ((ScalarExtension.moduleExtension φ D).map f)
      ((ScalarExtension.moduleExtension φ D).map g) := by
  have hfa := congrArg (scalarModuleHomElement φ D)
    (gradedSplit_inclusion_retraction_element s)
  rw [scalarModuleHomElement_forward, scalarModuleHomElement_unit,
    scalarModuleHomElement_closed] at hfa
  have hbg := congrArg (scalarModuleHomElement φ D)
    (gradedSplit_section_projection_element s)
  rw [scalarModuleHomElement_forward, scalarModuleHomElement_unit,
    scalarModuleHomElement_closed] at hbg
  have hba := congrArg (scalarModuleHomElement φ D)
    (gradedSplit_section_retraction_element s)
  rw [scalarModuleHomElement_forward, scalarModuleHomElement_zero] at hba
  have hdec := congrArg (scalarModuleHomElement φ D)
    (gradedSplit_decomposition_element s)
  rw [scalarModuleHomElement_add, scalarModuleHomElement_forward,
    scalarModuleHomElement_forward, scalarModuleHomElement_unit,
    scalarModuleHomElement_closed, scalarModuleHomElement_closed] at hdec
  exact moduleGradedSplitOfHomElements A' (ScalarExtension.DGBaseChange φ D)
    ((ScalarExtension.moduleExtension φ D).map f) ((ScalarExtension.moduleExtension φ D).map g)
    (scalarModuleHomElement φ D s.retractionElement)
    (scalarModuleHomElement φ D s.sectionElement)
    hfa hbg hba hdec (by
      rw [← Functor.map_comp, s.inclusion_projection, Functor.map_zero])

end SerrePositivity.DifferentialGraded
