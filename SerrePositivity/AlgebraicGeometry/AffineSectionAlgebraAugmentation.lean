module

public import SerrePositivity.AlgebraicGeometry.CechAlgebraAugmentationInjective
public import SerrePositivity.AlgebraicGeometry.SchemeSectionAlgebraCech
public import SerrePositivity.AlgebraicGeometry.SchemeModuleAffineCoverCech
public import SerrePositivity.AlgebraicGeometry.OpenCoverCechScalarRestriction

/-!
概要：アフィンスキームの被覆で、実際の切断代数の増大写像は全射。
方針：全空間にアフィン被覆の増大完全性を適用し、代数の図式へ移す。
規約：基底環は任意の大域スカラー写像で指定する。
使われ方：中心外の局所化後に次数零の余核が消えることの入口。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] {Y : Scheme.{u}} [IsAffine Y]
variable (φ : R →+* Γ(Y, ⊤)) (M : Y.Modules) [M.IsQuasicoherent]
variable {ι : Type} [LinearOrder ι] (U : ι → Y.Opens)
variable (hU : ∀ i, IsAffineOpen (U i)) (hcU : (⨆ i, U i) = ⊤)

include hU hcU in
/-- アフィンスキームの準連接係数のアフィン被覆は、任意の基底環上で増大 Čech が完全。
BST13 Lemma 3.8 の次数零で使う Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem affineSchemeModuleCech_acyclic :
    OpenCoverCechAcyclic (schemeModuleCechPresheaf M ⋙ ModuleCat.restrictScalars φ) U := by
  apply openCoverCechAcyclic_restrictScalars
  apply openCoverCechAcyclic_of_iso
    (openCoverIntersectionPresheaf (schemeModuleCechPresheaf M) ⊤) U
    (openCoverIntersectionPresheafTopIso (schemeModuleCechPresheaf M))
  apply schemeModuleAffineOpenCech_acyclic M ⊤ (isAffineOpen_top Y) U
  · intro i
    simpa using hU i
  · rw [hcU]

include hU hcU in
/-- アフィン被覆で、代数の実際の増大写像は適合する切断へ全射。 -/
theorem affineSchemeSectionAlgebraAugmentation_surjective :
    Function.Surjective
      (fullAlgebraCechAugmentation (schemeSectionAlgebraCechDiagram Y φ U)) := by
  apply fullAlgebraCechAugmentation_surjective_of_exact
  have h := affineSchemeModuleCech_acyclic φ (schemeStructureModule Y) U hU hcU
  exact fullCechCoefficientEquiv_exact (schemeSectionAlgebraCechModuleIso Y φ U).symm 0
    (h.exact 0)

include hU hcU in
/-- アフィン被覆の実際の代数の増大写像は全単射。 -/
theorem affineSchemeSectionAlgebraAugmentation_bijective :
    Function.Bijective
      (fullAlgebraCechAugmentation (schemeSectionAlgebraCechDiagram Y φ U)) := by
  constructor
  · apply fullAlgebraCechAugmentation_injective_of_differential
    have h := affineSchemeModuleCech_acyclic φ (schemeStructureModule Y) U hU hcU
    exact fullCechCoefficientEquiv_zero_injective
      (schemeSectionAlgebraCechModuleIso Y φ U).symm h.injective_zero
  · exact affineSchemeSectionAlgebraAugmentation_surjective φ U hU hcU

end SerrePositivity.AlgebraicGeometry
