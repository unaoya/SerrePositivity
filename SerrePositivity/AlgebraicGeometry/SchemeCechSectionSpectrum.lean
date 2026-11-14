module

public import SerrePositivity.AlgebraicGeometry.SchemeCechGlobalSections
public import SerrePositivity.AlgebraicGeometry.SchemeScalarMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
概要：構造射を Čech の適合切断環の Spec を介して分解する。
方針：大域切断との環の同型と Γ–Spec の標準射を使う。
規約：全空間のアフィン性や Stein 分解は仮定しない。
使われ方：F7 の有限切断環への Spec 全射性を元の構造射から供給する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace _root_.AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] (Y : Scheme.{u}) {ι : Type} [DecidableEq ι]
variable (U : ι → Y.Opens) (φ : R →+* Γ(Y, ⊤)) (hcover : (⨆ i, U i) = ⊤)

/-- 元のスキームから Čech の適合切断環の Spec への標準射。 -/
def schemeToCechSectionSpectrum : Y ⟶
    Spec (CommRingCat.of (fullAlgebraCechEqualizer (schemeSectionAlgebraCechDiagram Y φ U))) :=
  Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (schemeCechGlobalSectionsEquiv Y U φ hcover).toRingHom)

/-- この標準射と基底スカラーの Spec を合成すると、元の構造射になる。 -/
theorem schemeToCechSectionSpectrum_comp :
    schemeToCechSectionSpectrum Y U φ hcover ≫
      Spec.map (CommRingCat.ofHom (algebraMap R
        (fullAlgebraCechEqualizer (schemeSectionAlgebraCechDiagram Y φ U)))) =
      schemeScalarMorphism Y φ := by
  unfold schemeToCechSectionSpectrum schemeScalarMorphism
  rw [Category.assoc, ← Spec.map_comp]
  congr 2
  ext r
  letI := φ.toAlgebra
  exact (schemeCechGlobalSectionsAlgEquiv Y U φ hcover).commutes r

include hcover in
/-- 構造射が全射なら、基底環から Čech の適合切断環への射は Spec 上で全射。 -/
theorem schemeCechSectionAlgebra_surjectiveSpectrum
    [Surjective (schemeScalarMorphism Y φ)] :
    Function.Surjective (PrimeSpectrum.comap (algebraMap R
      (fullAlgebraCechEqualizer (schemeSectionAlgebraCechDiagram Y φ U)))) := by
  let f := schemeToCechSectionSpectrum Y U φ hcover
  let g := Spec.map (CommRingCat.ofHom (algebraMap R
    (fullAlgebraCechEqualizer (schemeSectionAlgebraCechDiagram Y φ U))))
  have hfg : f ≫ g = schemeScalarMorphism Y φ :=
    schemeToCechSectionSpectrum_comp Y U φ hcover
  haveI : Surjective (f ≫ g) := by rw [hfg]; infer_instance
  haveI : Surjective g := Surjective.of_comp f g
  exact g.surjective

end SerrePositivity.AlgebraicGeometry
