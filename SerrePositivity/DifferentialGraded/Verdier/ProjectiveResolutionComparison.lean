module
public import SerrePositivity.DifferentialGraded.Endomorphism.ProjectiveHomotopyComparison
public import SerrePositivity.DifferentialGraded.Morita.CoherenceIdentity

/-! # 実際の射影解像度関手と、射影的ホモトピー圏からの三角同値の逆関手 -/
@[expose] public section
noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance projectiveModuleHomotopyToDerivedEssSurj :
    (projectiveModuleHomotopyToDerived A D).EssSurj where
  mem_essImage X := by
    obtain ⟨⟨M⟩⟩ := X
    let R := moduleCanonicalProjectiveResolution A D M
    refine ⟨⟨(moduleToHomotopy A D).obj R.obj, R.projective⟩, ⟨?_⟩⟩
    exact (moduleToHomotopyDerivedIso A D).app R.obj ≪≫ moduleDerivedIso A D R.π R.quasiIso

instance projectiveModuleHomotopyToDerivedIsEquivalence :
    (projectiveModuleHomotopyToDerived A D).IsEquivalence where

def projectiveModuleDerivedEquivalence :
    projectiveModuleHomotopyCategory A D ≌ DerivedModuleCategory A D :=
  (projectiveModuleHomotopyToDerived A D).asEquivalence

instance projectiveModuleDerivedEquivalenceFunctorCommShift :
    (projectiveModuleDerivedEquivalence A D).functor.CommShift ℤ :=
  projectiveModuleHomotopyToDerivedCommShift A D
instance projectiveModuleDerivedEquivalenceInverseCommShift :
    (projectiveModuleDerivedEquivalence A D).inverse.CommShift ℤ :=
  (projectiveModuleDerivedEquivalence A D).commShiftInverse ℤ
instance projectiveModuleDerivedEquivalenceCommShift :
    (projectiveModuleDerivedEquivalence A D).CommShift ℤ :=
  (projectiveModuleDerivedEquivalence A D).commShift_of_functor ℤ
instance projectiveModuleDerivedEquivalenceIsTriangulated :
    (projectiveModuleDerivedEquivalence A D).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _ (projectiveModuleHomotopyToDerivedIsTriangulated A D)

variable (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)

lemma derivedResolution_projective (X : DerivedModuleCategory A D) :
    moduleHomotopyProjectiveLocus A D ((moduleDerivedResolutionFunctor A D R).obj X) := by
  obtain ⟨⟨M⟩⟩ := X
  exact (moduleHomotopyProjectiveLocus A D).prop_of_iso
    (moduleDerivedResolutionComputation A D R M).symm (R M).projective

def derivedResolutionToProjectives :
    DerivedModuleCategory A D ⥤ projectiveModuleHomotopyCategory A D :=
  (moduleHomotopyProjectiveLocus A D).lift (moduleDerivedResolutionFunctor A D R)
    (derivedResolution_projective A D R)

def derivedResolutionToProjectivesInverseIso :
    derivedResolutionToProjectives A D R ≅ (projectiveModuleDerivedEquivalence A D).inverse :=
  ((whiskeringRight _ _ _).obj (projectiveModuleDerivedEquivalence A D).functor).preimageIso
    (Morita.kernelInputResolutionDerivedCounitIso A D R ≪≫
      (projectiveModuleDerivedEquivalence A D).counitIso.symm)

/-- 元の入力解像度関手そのものは、三角同値の逆関手を包含したものと自然同型。 -/
def derivedResolutionProjectiveComparison :
    moduleDerivedResolutionFunctor A D R ≅
      (projectiveModuleDerivedEquivalence A D).inverse ⋙ (moduleHomotopyProjectiveLocus A D).ι :=
  ((moduleHomotopyProjectiveLocus A D).liftCompιIso _ _).symm ≪≫
    isoWhiskerRight (derivedResolutionToProjectivesInverseIso A D R)
      (moduleHomotopyProjectiveLocus A D).ι
end SerrePositivity.DifferentialGraded
