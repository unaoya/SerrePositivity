module

public import SerrePositivity.AlgebraicGeometry.FullCechH0Kernel

/-!
概要：Čech H⁰ と最初の余境界の核の比較を係数写像に自然にする。
方針：核の包含と cycles の包含を照合し、homologyπ の自然性を使う。
規約：比較する写像は既存の全タプル Čech 複体の射。
使われ方：閉厚化の適合切断環の射と、核・像の評価に使う H⁰ の射を一致させる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type u} [CommRing R] {ι : Type v} [DecidableEq ι]

/-- H⁰ と核の比較の後の包含は、homologyπ の逆と cycles の包含の合成。 -/
theorem fullCechH0KernelIso_hom_subtype (D : Finset ι ⥤ ModuleCat.{u} R) :
    (fullCechH0KernelIso D).hom ≫
      ModuleCat.ofHom (LinearMap.ker (fullCechDifferential D 1)).subtype =
    inv ((fullCechComplex D).homologyπ 0) ≫ (fullCechComplex D).iCycles 0 := by
  simp only [fullCechH0KernelIso, Iso.trans_hom, Category.assoc]
  change inv ((fullCechComplex D).homologyπ 0) ≫
    ((fullCechComplex D).cyclesIsoSc' 0 0 1 (by simp) (by simp)).hom ≫
      ((fullCechComplex D).sc' 0 0 1).moduleCatCyclesIso.hom ≫
        ((fullCechComplex D).sc' 0 0 1).moduleCatLeftHomologyData.i = _
  rw [ShortComplex.moduleCatCyclesIso_hom_i, HomologicalComplex.cyclesIsoSc'_hom_iCycles]

/-- H⁰ の写像と最初の余境界の核への比較は、実際の零次項の写像と可換。 -/
theorem fullCechH0KernelIso_naturality_subtype
    {D E : Finset ι ⥤ ModuleCat.{u} R} (η : D ⟶ E) :
    HomologicalComplex.homologyMap (fullCechComplexMap η) 0 ≫
      (fullCechH0KernelIso E).hom ≫
        ModuleCat.ofHom (LinearMap.ker (fullCechDifferential E 1)).subtype =
    (fullCechH0KernelIso D).hom ≫
      ModuleCat.ofHom (LinearMap.ker (fullCechDifferential D 1)).subtype ≫
        (fullCechComplexMap η).f 0 := by
  rw [fullCechH0KernelIso_hom_subtype,
    ← Category.assoc (fullCechH0KernelIso D).hom,
    fullCechH0KernelIso_hom_subtype]
  rw [← cancel_epi ((fullCechComplex D).homologyπ 0)]
  simp only [Category.assoc, HomologicalComplex.homologyπ_naturality_assoc,
    IsIso.hom_inv_id_assoc, HomologicalComplex.cyclesMap_i]

end SerrePositivity.AlgebraicGeometry
