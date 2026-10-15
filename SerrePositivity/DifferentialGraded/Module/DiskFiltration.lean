module
public import SerrePositivity.DifferentialGraded.Complexes.DiskFiltration
public import SerrePositivity.DifferentialGraded.Complexes.TensorGradedZero
public import SerrePositivity.DifferentialGraded.Module.Cells
public import SerrePositivity.DifferentialGraded.Module.GradedSplitCokernel

/-! # 自由diskの自由sphereによる二段filtration -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def freeDiskToSphere (x : D) (n : ℤ) : freeDisk A D x n ⟶ freeSphere A D x n :=
  (freeAt x).map (complexDiskToSphere A n)

@[simp] lemma freeDiskToSphere_eval (x y : D) (n : ℤ) :
    (moduleEvaluation A D y).map (freeDiskToSphere A D x n) =
      complexDiskToSphere A n ▷ (y ⟶[Complex A] x) :=
  tensorModuleMap_eval _ _ _

@[simp] lemma freeCellBoundary_eval (x y : D) (n : ℤ) :
    (moduleEvaluation A D y).map (freeCellBoundary A D x n) =
      complexSphereToDisk A n ▷ (y ⟶[Complex A] x) :=
  tensorModuleMap_eval _ _ _

lemma freeCellBoundary_toSphere (x : D) (n : ℤ) :
    freeCellBoundary A D x n ≫ freeDiskToSphere A D x n = 0 := by
  apply moduleMorphism_ext
  intro y
  rw [CategoryTheory.Functor.map_comp, freeCellBoundary_eval, freeDiskToSphere_eval,
    CategoryTheory.Functor.map_zero, ← comp_whiskerRight, complexSphereToDiskToSphere,
    MonoidalPreadditive.zero_whiskerRight]

/-- 自由diskの二段filtrationは全斉次作用に関して分裂する。 -/
def freeDiskGradedSplit (x : D) (n : ℤ) :
    ModuleGradedSplit A D (freeCellBoundary A D x n) (freeDiskToSphere A D x n) where
  retraction y k := tensorGradedZeroComponent (complexDiskGradedRetraction A n)
    (y ⟶[Complex A] x) k
  section_ y k := tensorGradedZeroComponent (complexDiskGradedSection A n)
    (y ⟶[Complex A] x) k
  inclusion_retraction y k := by
    rw [freeCellBoundary_eval]
    change (complexSphereToDisk A n ▷ (y ⟶[Complex A] x)).f k ≫
      tensorGradedZeroComponent (complexDiskGradedRetraction A n) (y ⟶[Complex A] x) k = 𝟙 _
    rw [← tensorGradedZeroComponent_ofHom, tensorGradedZeroComponent_comp,
      complexDiskGraded_inclusion_retraction_cochain, tensorGradedZeroComponent_id]
  section_projection y k := by
    rw [freeDiskToSphere_eval]
    change tensorGradedZeroComponent (complexDiskGradedSection A n) (y ⟶[Complex A] x) k ≫
      (complexDiskToSphere A n ▷ (y ⟶[Complex A] x)).f k = 𝟙 _
    rw [← tensorGradedZeroComponent_ofHom, tensorGradedZeroComponent_comp,
      complexDiskGraded_section_projection_cochain, tensorGradedZeroComponent_id]
  section_retraction y k := by
    rw [tensorGradedZeroComponent_comp, complexDiskGraded_section_retraction_cochain,
      tensorGradedZeroComponent_zero]
  inclusion_projection := freeCellBoundary_toSphere A D x n
  decomposition y k := by
    rw [freeCellBoundary_eval, freeDiskToSphere_eval]
    change tensorGradedZeroComponent (complexDiskGradedRetraction A n) (y ⟶[Complex A] x) k ≫
        (complexSphereToDisk A n ▷ (y ⟶[Complex A] x)).f k +
      (complexDiskToSphere A n ▷ (y ⟶[Complex A] x)).f k ≫
        tensorGradedZeroComponent (complexDiskGradedSection A n) (y ⟶[Complex A] x) k = 𝟙 _
    rw [← tensorGradedZeroComponent_ofHom, ← tensorGradedZeroComponent_ofHom,
      tensorGradedZeroComponent_comp, tensorGradedZeroComponent_comp,
      ← tensorGradedZeroComponent_add, complexDiskGraded_decomposition_cochain,
      tensorGradedZeroComponent_id]
  retraction_naturality y z p i j hij a :=
    tensorGradedZeroComponent_naturality _ p i j hij _
  section_naturality y z p i j hij a :=
    (tensorGradedZeroComponent_naturality _ p i j hij _).symm

lemma freeCellBoundary_mono (x : D) (n : ℤ) : Mono (freeCellBoundary A D x n) :=
  (freeDiskGradedSplit A D x n).mono

lemma freeDiskToSphere_epi (x : D) (n : ℤ) : Epi (freeDiskToSphere A D x n) :=
  (freeDiskGradedSplit A D x n).epi

/-- 自由diskの商は同じ対象xで生成する次数nの自由sphere。 -/
def freeDiskSphereCokernel (x : D) (n : ℤ) :
    IsColimit (CokernelCofork.ofπ (freeDiskToSphere A D x n) (freeCellBoundary_toSphere A D x n)) :=
  moduleGradedSplitCokernel A D (freeDiskGradedSplit A D x n)

end SerrePositivity.DifferentialGraded
