module

public import SerrePositivity.AlgebraicGeometry.AffineSectionAlgebraScalar
public import SerrePositivity.AlgebraicGeometry.SchemeScalarMorphism

/-!
概要：アフィン基底への同型なら、切断部分代数のスカラー写像は全射。
方針：Γ–Spec の同型と構造射の大域切断の同型を合成する。
規約：実際の構造射から定まるスカラー写像を用いる。
使われ方：中心外の局所化による次数零の消滅。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] (Y : Scheme.{u})
variable (iY : Y ⟶ Spec (CommRingCat.of R)) [IsIso iY]

/-- アフィン基底への構造射が同型なら、実際の大域スカラー写像は全単射。 -/
theorem schemeScalarHom_bijective_of_isIso :
    Function.Bijective (schemeScalarHom Y iY) := by
  letI : IsIso iY.appTop := inferInstanceAs (IsIso (Scheme.Γ.map iY.op))
  exact ConcreteCategory.bijective_of_isIso
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ iY.appTop)

/-- アフィン基底への同型の、アフィン被覆の切断部分代数へのスカラーは全射。 -/
theorem schemeSectionAlgebra_scalar_surjective_of_isIso
    {ι : Type} [LinearOrder ι] (U : ι → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcU : (⨆ i, U i) = ⊤) :
    Function.Surjective (algebraMap R (fullAlgebraCechEqualizer
      (schemeSectionAlgebraCechDiagram Y (schemeScalarHom Y iY) U))) := by
  letI : IsAffine Y := isAffine_of_isAffineHom iY
  exact affineSchemeSectionAlgebra_scalar_surjective Y (schemeScalarHom Y iY) U hU hcU
    (schemeScalarHom_bijective_of_isIso Y iY).2

end SerrePositivity.AlgebraicGeometry
