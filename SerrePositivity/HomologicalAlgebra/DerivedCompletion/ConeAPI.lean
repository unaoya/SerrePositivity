module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Tower.HolimModel
public import SerrePositivity.HomologicalAlgebra.Complex.Cone
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import SerrePositivity.HomologicalAlgebra.Complex.ConeLES
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-! # 写像錐の標準の短完全列と連結射の符号

## 概要

写像錐の次数ごとに分裂する標準の短完全列（`coneStandardShortComplex`）と、標準三角形の連結射と一段シフトした錐の射影の符号の関係（`coneShiftBoundary_eq_neg_fst`）を与える。

## 方針

標準三角形の第 3 射は負の第 1 成分から作られることを使う。

## 規約

旧 `ConeShortExact`・`ConeBoundaryNormalization`（Mathlib の `CochainComplex.mappingCone` の API と一部重なる見込み、refactor-plan §3.6.2）。

## 使われ方

`Koszul/Tower`、`ComplexCompletion/Reconstruction`。
-/

@[expose] public noncomputable section

universe u

section ConeShortExactPart

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

end ConeShortExactPart

section ConeBoundaryNormalizationPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
variable (R : Type u) [CommRing R]
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ} (φ : K ⟶ L)

/-- 錐の連結射は、具体的な複体の第3射に対するshiftMap。 -/
theorem coneBoundary_eq_shiftMap (i j : ℤ) (h : i + 1 = j) :
    Cone.δ φ i j h =
      (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) 0).shiftMap
        (CochainComplex.mappingCone.triangle φ).mor₃ i j (by omega) := by
  rw [Cone.δ, CategoryTheory.Functor.homologySequenceδ]
  change (Cone.e i _).inv ≫
    (HomotopyCategory.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) 0).shiftMap
      (ShiftedHom.map (CochainComplex.mappingCone.triangle φ).mor₃
        (HomotopyCategory.quotient _ _)) i j _ ≫ (Cone.e j _).hom = _
  rw [HomotopyCategory.homologyFunctor_shiftMap]
  simp only [Iso.app_inv, Functor.comp_obj, Iso.app_hom, assoc,
    Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc]
  exact Category.comp_id _

/-- 三角形の第3射を一段戻すと、第1射影の負になる。 -/
theorem coneTriangle_shift_mor3 :
    (CochainComplex.mappingCone.triangle φ).mor₃⟦(-1 : ℤ)⟧' ≫
      (shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).hom.app K =
        -CochainComplex.mappingCocone.fst φ := by
  apply HomologicalComplex.hom_ext
  intro n
  simp [CochainComplex.mappingCocone.fst, CochainComplex.mappingCone.triangle,
    CochainComplex.HomComplex.Cochain.leftShift,
    CochainComplex.HomComplex.Cochain.rightShift,
    shiftFunctorCompIsoId, CochainComplex.shiftFunctorAdd'_inv_app_f',
    CochainComplex.shiftFunctorZero_hom_app_f, CochainComplex.shiftFunctorObjXIso,
    CochainComplex.HomComplex.Cochain.v_comp_XIsoOfEq_hom]

/-- 一段シフトの同定を経た連結射は、標準射影のホモロジー写像の負。 -/
theorem coneShiftBoundary_eq_neg_fst (i : ℤ) :
    ((CochainComplex.ShiftSequence.shiftIso (ModuleCat R) (-1) i (i - 1)
      (by omega)).app (CochainComplex.mappingCone φ)).hom ≫
      Cone.δ φ (i - 1) i (by omega) =
        -HomologicalComplex.homologyMap (CochainComplex.mappingCocone.fst φ) i := by
  rw [coneBoundary_eq_shiftMap]
  change ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) 0).shiftIso
    (-1) i (i - 1) (by omega)).hom.app _ ≫ _ = _
  rw [CategoryTheory.Functor.shiftIso_hom_app_comp_shiftMap_of_add_eq_zero
    _ _ (-1) (by norm_num)]
  change HomologicalComplex.homologyMap
    ((CochainComplex.mappingCone.triangle φ).mor₃⟦(-1 : ℤ)⟧' ≫
      (shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).hom.app K) i = _
  rw [coneTriangle_shift_mor3]
  exact HomologicalComplex.homologyMap_neg _ _

end SerrePositivity.DerivedCompletion

end ConeBoundaryNormalizationPart
