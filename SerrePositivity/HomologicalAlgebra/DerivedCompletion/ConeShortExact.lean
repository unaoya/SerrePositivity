module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerComplex
public import SerrePositivity.HomologicalAlgebra.CochainConeCoordinates
public import SerrePositivity.HomologicalAlgebra.CochainConeNaturality
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # 写像錐の標準の次数ごとに分裂する短完全列 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open HomologicalComplex.homotopyCofiber
variable (R : Type u) [CommRing R]
variable {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (φ : P ⟶ Q)

/-- 写像錐の標準のシフトした始域への射影。 -/
def coneStandardProjection : CochainComplex.mappingCone φ ⟶ P⟦(1 : ℤ)⟧ :=
  (CochainComplex.mappingCone.triangle φ).mor₃

/-- 標準射影は左包含に対し、シフトの各項の同型の負を与える。 -/
@[reassoc] theorem coneStandardProjection_inl (i : ℤ) :
    (CochainComplex.mappingCone.inl φ).v (i + 1) i (by omega) ≫
      (coneStandardProjection R φ).f i =
        -(CochainComplex.shiftFunctorObjXIso P 1 i (i + 1) rfl).inv :=
  CochainComplex.mappingCone.inl_v_triangle_mor₃_f φ (i + 1) i (by omega)

/-- 標準射影は右包含を零へ送る。 -/
@[reassoc] theorem coneStandardProjection_inr (i : ℤ) :
    (CochainComplex.mappingCone.inr φ).f i ≫ (coneStandardProjection R φ).f i = 0 :=
  CochainComplex.mappingCone.inr_f_triangle_mor₃_f φ i

/-- Q→Cone(φ)→P[1]の標準短複体。 -/
def coneStandardShortComplex : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  ShortComplex.mk (CochainComplex.mappingCone.inr φ) (coneStandardProjection R φ) (by
    apply HomologicalComplex.hom_ext
    intro i
    exact coneStandardProjection_inr R φ i)

/-- 写像錐の標準短複体は、各次数で標準的に分裂する。 -/
def coneStandardShortComplexSplitting (i : ℤ) :
    ((coneStandardShortComplex R φ).map
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) i)).Splitting where
  r := (CochainComplex.mappingCone.snd φ).v i i (add_zero i)
  s := (-(CochainComplex.shiftFunctorObjXIso P 1 i (i + 1) rfl).hom) ≫
    (CochainComplex.mappingCone.inl φ).v (i + 1) i (by omega)
  f_r := CochainComplex.mappingCone.inr_f_snd_v φ i
  s_g := by
    change ((-(CochainComplex.shiftFunctorObjXIso P 1 i (i + 1) rfl).hom) ≫
      (CochainComplex.mappingCone.inl φ).v (i + 1) i (by omega)) ≫
        (coneStandardProjection R φ).f i = 𝟙 _
    rw [Category.assoc, coneStandardProjection_inl]
    simp
  id := by
    change (CochainComplex.mappingCone.snd φ).v i i (add_zero i) ≫
      (CochainComplex.mappingCone.inr φ).f i + (coneStandardProjection R φ).f i ≫
      ((-(CochainComplex.shiftFunctorObjXIso P 1 i (i + 1) rfl).hom) ≫
        (CochainComplex.mappingCone.inl φ).v (i + 1) i (by omega)) = 𝟙 _
    apply CochainComplex.mappingCone.ext_from φ (i + 1) i rfl
    · simp only [Preadditive.comp_add, CochainComplex.mappingCone.inl_v_snd_v_assoc]
      erw [coneStandardProjection_inl_assoc]
      simp
    · simp only [Preadditive.comp_add, CochainComplex.mappingCone.inr_f_snd_v_assoc]
      erw [coneStandardProjection_inr_assoc]
      simp

/-- Q→Cone(φ)→P[1]は複体の圏の短完全列である。 -/
theorem coneStandardShortComplex_shortExact : (coneStandardShortComplex R φ).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  exact (coneStandardShortComplexSplitting R φ i).shortExact

end SerrePositivity.DerivedCompletion
