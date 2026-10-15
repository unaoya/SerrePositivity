module
public import SerrePositivity.HomologicalAlgebra.ProjectiveExtNaturality
public import SerrePositivity.HomologicalAlgebra.LocalCohomologyKoszulComparison

/-! # Strict sequential coefficient-complex models for inverse-system Ext -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
variable {R : Type u} [CommRing R]

/-- Chosen resolutions are dualized only along adjacent standard lifts.
`Functor.ofSequence` supplies the strictly composable coefficient-complex diagram. -/
def projectiveExtCoefficientDiagram (X : ℕᵒᵖ ⥤ ModuleCat.{u} R) :
    ℕ ⥤ (ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℕ) :=
  Functor.ofSequence
    (X := fun n => chainLinearYonedaFunctor (projectiveResolution (X.obj (op n))).complex)
    (fun n => chainLinearYonedaMap (ProjectiveResolution.lift
      (X.map (homOfLE (Nat.le_succ n)).op)
      (projectiveResolution (X.obj (op (n + 1)))) (projectiveResolution (X.obj (op n)))))

/-- The ordinary Ext diagram associated to an inverse coefficient-source system. -/
def inverseSystemExtDiagram (X : ℕᵒᵖ ⥤ ModuleCat.{u} R) (i : ℕ) :
    ℕ ⥤ (ModuleCat.{u} R ⥤ ModuleCat.{u} R) :=
  opOp ℕ ⋙ X.op ⋙ Ext R (ModuleCat.{u} R) i

/-- Actual homology of the strict coefficient-complex diagram computes Ext,
including all transition maps and arbitrary coefficient morphisms. -/
def projectiveExtCoefficientDiagramHomologyNatIso (X : ℕᵒᵖ ⥤ ModuleCat.{u} R) (i : ℕ) :
    inverseSystemExtDiagram X i ≅
      projectiveExtCoefficientDiagram X ⋙
        (Functor.whiskeringRight _ _ _).obj (homologyFunctor (ModuleCat.{u} R) (.up ℕ) i) := by
  let α : inverseSystemExtDiagram X i ⟶
      projectiveExtCoefficientDiagram X ⋙
        (Functor.whiskeringRight _ _ _).obj (homologyFunctor (ModuleCat.{u} R) (.up ℕ) i) :=
    NatTrans.ofSequence (fun n => (projectiveResolutionExtNatIso
      (projectiveResolution (X.obj (op n))) i).hom) (by
        intro n
        simp only [inverseSystemExtDiagram, projectiveExtCoefficientDiagram,
          Functor.comp_map, Functor.ofSequence_map_homOfLE_succ,
          Functor.whiskeringRight_obj_map]
        apply NatTrans.ext
        funext M
        exact projectiveResolutionIsoExt_first_naturality
          (X.map (homOfLE (Nat.le_succ n)).op)
          (projectiveResolution (X.obj (op (n + 1))))
          (projectiveResolution (X.obj (op n))) _
          (ProjectiveResolution.lift_commutes_zero _ _ _) M i)
  exact NatIso.ofComponents
    (fun n => projectiveResolutionExtNatIso (projectiveResolution (X.obj (op n))) i)
    (fun f => α.naturality f)

local instance : AB5OfSize.{0, 0} (ModuleCat.{u} R) :=
  AB5OfSize_of_univLE (ModuleCat.{u} R)

/-- The strict Ext model as a diagram of complexes of coefficient functors. -/
def projectiveExtFunctorComplexDiagram (X : ℕᵒᵖ ⥤ ModuleCat.{u} R) :
    ℕ ⥤ CochainComplex (ModuleCat.{u} R ⥤ ModuleCat.{u} R) ℕ :=
  projectiveExtCoefficientDiagram X ⋙
    functorCochainComplexFunctor (ModuleCat.{u} R) (ModuleCat.{u} R)

/-- The actual coefficient-complex colimit realizing inverse-system Ext. -/
def projectiveExtColimitComplex (X : ℕᵒᵖ ⥤ ModuleCat.{u} R) :
    CochainComplex (ModuleCat.{u} R ⥤ ModuleCat.{u} R) ℕ :=
  colimit (projectiveExtFunctorComplexDiagram X)

/-- Exact sequential colimits identify the homology of the actual model
with the entire Ext colimit, naturally in arbitrary coefficients. -/
def projectiveExtColimitHomologyNatIso (X : ℕᵒᵖ ⥤ ModuleCat.{u} R) (i : ℕ) :
    (projectiveExtColimitComplex X).homology i ≅ colimit (inverseSystemExtDiagram X i) :=
  sequentialCochainHomologyColimitIso (projectiveExtFunctorComplexDiagram X) i ≪≫
    HasColimit.isoOfNatIso (Functor.isoWhiskerLeft (projectiveExtCoefficientDiagram X)
      (functorCochainHomologyNatIso (ModuleCat.{u} R) (ModuleCat.{u} R) i)) ≪≫
    (HasColimit.isoOfNatIso (projectiveExtCoefficientDiagramHomologyNatIso X i)).symm

end SerrePositivity
