module

public import SerrePositivity.AlgebraicGeometry.CechAlgebraEqualizerMap
public import SerrePositivity.AlgebraicGeometry.FullCechH0KernelNaturality

/-!
概要：適合切断環と Čech H⁰ の比較を係数図式の射に自然にする。
方針：H⁰ から核への比較と核の包含で、同じ成分写像へ帰着する。
規約：環の写像と H⁰ の線形写像は任意の同型で置き換えない。
使われ方：閉厚化の環の制限に 2e の核の評価と像の安定化を適用する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Functor
universe u v
variable {R : Type u} [CommRing R] {ι : Type v} [DecidableEq ι]
variable {D E : Finset ι ⥤ CommAlgCat.{u} R}

/-- 適合切断から H⁰ を経由して核へ戻すと、元の切断族になる。 -/
theorem fullAlgebraCechH0Equiv_kernel (a : fullAlgebraCechEqualizer D) :
    ((fullCechH0KernelIso (algebraCechModuleDiagram D)).hom.hom
      (fullAlgebraCechH0Equiv D a)).val = a.val := by
  change ((fullCechH0KernelIso (algebraCechModuleDiagram D)).toLinearEquiv
    ((fullCechH0KernelIso (algebraCechModuleDiagram D)).toLinearEquiv.symm
      ((LinearEquiv.ofEq _ _ (fullAlgebraCechEqualizer_toSubmodule D)) a))).val = _
  rw [LinearEquiv.apply_symm_apply]
  exact LinearEquiv.coe_ofEq_apply _ _

/-- 環の適合切断から Čech H⁰ への比較は、実際の係数図式の射に自然。 -/
theorem fullAlgebraCechH0Equiv_naturality (η : D ⟶ E)
    (a : fullAlgebraCechEqualizer D) :
    fullAlgebraCechH0Equiv E (fullAlgebraCechEqualizerMap η a) =
      (HomologicalComplex.homologyMap (fullCechComplexMap
        (whiskerRight η (forget₂ (CommAlgCat R) (AlgCat R) ⋙
          forget₂ (AlgCat R) (ModuleCat R)))) 0).hom
        (fullAlgebraCechH0Equiv D a) := by
  apply (fullCechH0KernelIso (algebraCechModuleDiagram E)).toLinearEquiv.injective
  apply Subtype.ext
  let ηM := whiskerRight η (forget₂ (CommAlgCat R) (AlgCat R) ⋙
    forget₂ (AlgCat R) (ModuleCat R))
  have h := congrArg (fun f ↦ f.hom (fullAlgebraCechH0Equiv D a))
    (fullCechH0KernelIso_naturality_subtype ηM)
  change ((fullCechH0KernelIso (algebraCechModuleDiagram E)).hom.hom
    (fullAlgebraCechH0Equiv E (fullAlgebraCechEqualizerMap η a))).val =
    ((fullCechH0KernelIso (algebraCechModuleDiagram E)).hom.hom
    ((HomologicalComplex.homologyMap (fullCechComplexMap ηM) 0).hom
      (fullAlgebraCechH0Equiv D a))).val
  rw [fullAlgebraCechH0Equiv_kernel]
  rw [show ((fullCechH0KernelIso (algebraCechModuleDiagram E)).hom.hom
    ((HomologicalComplex.homologyMap (fullCechComplexMap ηM) 0).hom
      (fullAlgebraCechH0Equiv D a))).val =
    (fullCechCochainsMap ηM 1)
      (((fullCechH0KernelIso (algebraCechModuleDiagram D)).hom.hom
        (fullAlgebraCechH0Equiv D a)).val) from h]
  rw [fullAlgebraCechH0Equiv_kernel]
  rfl

end SerrePositivity.AlgebraicGeometry
