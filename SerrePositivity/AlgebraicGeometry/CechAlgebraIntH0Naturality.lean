module

public import SerrePositivity.AlgebraicGeometry.CechAlgebraEqualizerAddMap
public import SerrePositivity.AlgebraicGeometry.FullCechH0KernelNaturality

/-!
概要：適合切断の加法群と整数係数の Čech H⁰ を自然に比較する。
方針：二つの面の差の核と適合条件を同定し、H⁰ の核表示の自然性を使う。
規約：係数写像には整数線形性だけを要求し、Frobenius の半線形性を許す。
使われ方：切断代数の Frobenius 系と Čech H⁰ の系の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v w
variable {R : Type u} [CommRing R] {ι : Type v} [DecidableEq ι]
private theorem kernel_hom_subtype (D : Finset ι ⥤ ModuleCat.{w} R) :
    (fullCechH0KernelIso D).hom ≫
      ModuleCat.ofHom (LinearMap.ker (fullCechDifferential D 1)).subtype =
    inv ((fullCechComplex D).homologyπ 0) ≫ (fullCechComplex D).iCycles 0 := by
  simp only [fullCechH0KernelIso, Iso.trans_hom, Category.assoc]
  change inv ((fullCechComplex D).homologyπ 0) ≫
    ((fullCechComplex D).cyclesIsoSc' 0 0 1 (by simp) (by simp)).hom ≫
      ((fullCechComplex D).sc' 0 0 1).moduleCatCyclesIso.hom ≫
        ((fullCechComplex D).sc' 0 0 1).moduleCatLeftHomologyData.i = _
  rw [ShortComplex.moduleCatCyclesIso_hom_i, HomologicalComplex.cyclesIsoSc'_hom_iCycles]

private theorem kernel_naturality_apply {D E : Finset ι ⥤ ModuleCat.{w} R}
    (η : D ⟶ E) (a : (fullCechComplex D).homology 0) :
    ((fullCechH0KernelIso E).hom.hom
      ((HomologicalComplex.homologyMap (fullCechComplexMap η) 0).hom a)).val =
    fullCechCochainsMap η 1 ((fullCechH0KernelIso D).hom.hom a).val := by
  have h : HomologicalComplex.homologyMap (fullCechComplexMap η) 0 ≫
      (fullCechH0KernelIso E).hom ≫
        ModuleCat.ofHom (LinearMap.ker (fullCechDifferential E 1)).subtype =
    (fullCechH0KernelIso D).hom ≫
      ModuleCat.ofHom (LinearMap.ker (fullCechDifferential D 1)).subtype ≫
        (fullCechComplexMap η).f 0 := by
    rw [kernel_hom_subtype, ← Category.assoc (fullCechH0KernelIso D).hom,
      kernel_hom_subtype]
    rw [← cancel_epi ((fullCechComplex D).homologyπ 0)]
    simp only [Category.assoc, HomologicalComplex.homologyπ_naturality_assoc,
      IsIso.hom_inv_id_assoc, HomologicalComplex.cyclesMap_i]
  exact congrArg (fun f ↦ f.hom a) h

variable (D : Finset ι ⥤ CommAlgCat.{u} R)
local instance intH0RingCochainsModule (D : Finset ι ⥤ CommAlgCat.{u} R) (k : ℕ) :
    Module ℤ (FullRingCechCochains (algebraCechRingDiagram D) k) :=
  Pi.module (Fin k → ι) (fun t ↦ (algebraCechIntDiagram D).obj (cechTupleSupport t)) ℤ
local instance intH0CochainsModule (D : Finset ι ⥤ CommAlgCat.{u} R) (k : ℕ) :
    Module ℤ (FullCechCochains (algebraCechIntDiagram D) k) :=
  Pi.module (Fin k → ι) (fun t ↦ (algebraCechIntDiagram D).obj (cechTupleSupport t)) ℤ

local instance intH0KernelModule (D : Finset ι ⥤ CommAlgCat.{u} R) :
    Module ℤ (LinearMap.ker (fullCechDifferential (algebraCechIntDiagram D) 1)) :=
  Submodule.module _

/-- 適合条件は、整数係数で計算しても最初の余境界の核。 -/
theorem fullAlgebraCechEqualizer_int_kernel_iff
    (a : FullRingCechCochains (algebraCechRingDiagram D) 1) :
    a ∈ fullAlgebraCechEqualizer D ↔
      a ∈ LinearMap.ker (fullCechDifferential (algebraCechIntDiagram D) 1) := by
  change (fullAlgebraCechFace D 0 a = fullAlgebraCechFace D 1 a) ↔ _
  rw [LinearMap.mem_ker, funext_iff, funext_iff]
  apply forall_congr'
  intro t
  have he : fullCechDifferential (algebraCechIntDiagram D) 1 a t =
      fullAlgebraCechFace D 0 a t - fullAlgebraCechFace D 1 a t :=
    fullCechDifferential_one_apply (algebraCechIntDiagram D) a t
  constructor
  · intro h
    exact he.trans (sub_eq_zero.mpr h)
  · intro h
    exact sub_eq_zero.mp (he.symm.trans h)

/-- 適合切断の整数加群と、最初の余境界の核との同型。 -/
def fullAlgebraCechIntKernelEquiv :
    fullAlgebraCechEqualizer D ≃ₗ[ℤ]
      LinearMap.ker (fullCechDifferential (algebraCechIntDiagram D) 1) :=
  AddEquiv.toIntLinearEquiv {
  toFun a := ⟨a.val, (fullAlgebraCechEqualizer_int_kernel_iff D a.val).mp a.property⟩
  invFun a := ⟨a.val, (fullAlgebraCechEqualizer_int_kernel_iff D a.val).mpr a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  }

/-- 適合切断の加法群と整数係数の Čech H⁰ の同型。
BST13 Lemma 3.8・3.9 の H⁰ に用いる Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def fullAlgebraCechIntH0Equiv :
    fullAlgebraCechEqualizer D ≃ₗ[ℤ]
      (fullCechComplex (algebraCechIntDiagram D)).homology 0 :=
  (fullAlgebraCechIntKernelEquiv D).trans
    (fullCechH0KernelIso (algebraCechIntDiagram D)).toLinearEquiv.symm

/-- 整数係数の H⁰ と核の比較で元の切断族に戻る。 -/
theorem fullAlgebraCechIntH0Equiv_kernel (a : fullAlgebraCechEqualizer D) :
    ((fullCechH0KernelIso (algebraCechIntDiagram D)).hom.hom
      (fullAlgebraCechIntH0Equiv D a)).val = a.val := by
  change ((fullCechH0KernelIso (algebraCechIntDiagram D)).toLinearEquiv
    ((fullCechH0KernelIso (algebraCechIntDiagram D)).toLinearEquiv.symm
      (fullAlgebraCechIntKernelEquiv D a))).val = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

variable {D} {E : Finset ι ⥤ CommAlgCat.{u} R}

/-- H⁰ の比較は整数線形な係数写像に自然。基底上で半線形な Frobenius も含む。 -/
theorem fullAlgebraCechIntH0Equiv_naturality
    (η : algebraCechIntDiagram D ⟶ algebraCechIntDiagram E)
    (a : fullAlgebraCechEqualizer D) :
    fullAlgebraCechIntH0Equiv E (fullAlgebraCechEqualizerAddMap η a) =
      (HomologicalComplex.homologyMap (fullCechComplexMap η) 0).hom
        (fullAlgebraCechIntH0Equiv D a) := by
  apply (fullCechH0KernelIso (algebraCechIntDiagram E)).toLinearEquiv.injective
  apply Subtype.ext
  have h := kernel_naturality_apply (R := ℤ)
    (D := algebraCechIntDiagram D) (E := algebraCechIntDiagram E) η
    (fullAlgebraCechIntH0Equiv D a)
  change ((fullCechH0KernelIso (algebraCechIntDiagram E)).hom.hom
    (fullAlgebraCechIntH0Equiv E (fullAlgebraCechEqualizerAddMap η a))).val =
    ((fullCechH0KernelIso (algebraCechIntDiagram E)).hom.hom
      ((HomologicalComplex.homologyMap (fullCechComplexMap η) 0).hom
        (fullAlgebraCechIntH0Equiv D a))).val
  rw [fullAlgebraCechIntH0Equiv_kernel]
  rw [show ((fullCechH0KernelIso (algebraCechIntDiagram E)).hom.hom
    ((HomologicalComplex.homologyMap (fullCechComplexMap η) 0).hom
      (fullAlgebraCechIntH0Equiv D a))).val =
    (fullCechCochainsMap η 1)
      (((fullCechH0KernelIso (algebraCechIntDiagram D)).hom.hom
        (fullAlgebraCechIntH0Equiv D a)).val) from h]
  rw [fullAlgebraCechIntH0Equiv_kernel]
  rfl

end SerrePositivity.AlgebraicGeometry
