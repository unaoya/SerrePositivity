module
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfHomComparisonZero
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfFullyFaithful
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveFiniteOperations
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-! # 列間の全次数の導来 Hom の計算

源の列だけの射影解像度から、全 Hom 複体の各次数のホモロジーを計算する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

/-- 源の列の s-shift からの導来射は、比較の終域の H^(-s) である。 -/
def criterionPerfColumnDerivedShiftedHomEquiv (d d' : D)
    (R : ModuleProjectiveResolution A E (criterionPerfColumn A D E P d)) (s : ℤ) :
    (((moduleToDerived A E).obj (criterionPerfColumn A D E P d))⟦s⟧ ⟶
        (moduleToDerived A E).obj (criterionPerfColumn A D E P d')) ≃
      (homObject A (RightModule A E) R.obj (criterionPerfColumn A D E P d')).homology (-s) := by
  let Q := moduleToDerived A E
  letI := moduleToDerived_inverts A E R.π R.quasiIso
  let eSource : Q.obj (R.obj⟦s⟧) ≅ (Q.obj (criterionPerfColumn A D E P d))⟦s⟧ :=
    (Q.commShiftIso s).app R.obj ≪≫ (shiftFunctor (DerivedModuleCategory A E) s).mapIso
      (asIso (Q.map R.π))
  let H := moduleHom A E (ForgetEnrichment.to (Complex A) R.obj) (P.rightAt d')
  let eHom := moduleHomSourceShiftIso A E (ForgetEnrichment.to (Complex A) R.obj)
    (P.rightAt d') s
  let eH := homologyMapIso eHom 0 ≪≫
    (CochainComplex.ShiftSequence.shiftIso (ModuleCat A) (-s) 0 (-s) (by omega)).app H
  exact (Iso.homCongr eSource.symm (Iso.refl _)).trans
    ((moduleProjectiveDerivedHomologyEquiv A E
      (moduleHomotopicallyProjective_shift A E R.projective s) _).trans
      eH.toLinearEquiv.toEquiv)

/-- 表現可能対象間の全次数の導来射は、元の dg 圏の全 Hom のホモロジー。 -/
def criterionPerfRepresentableDerivedShiftedHomEquiv [Small.{u} D] (d d' : D) (s : ℤ) :
    ((criterionPerfRepresentable A D d)⟦s⟧ ⟶ criterionPerfRepresentable A D d') ≃
      (homObject A D d d').homology (-s) := by
  let R := moduleIdentityProjectiveResolution A D
    (ForgetEnrichment.of (Complex A) (representable A d))
    (representable_homotopicallyProjective A D d)
  exact (criterionPerfColumnDerivedShiftedHomEquiv A D D (Bimodule.diagonal A D)
    d d' R s).trans
    (homologyMapIso (dgYonedaIso A d (representable A d')) (-s)).toLinearEquiv.toEquiv

end SerrePositivity.DifferentialGraded.Morita
