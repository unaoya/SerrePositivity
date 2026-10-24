module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeRightInverseRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConnectiveCoverSurjective

/-!
概要：実右逆 roof の分母に元の源の非正次数細分を持ち上げ、左欠損の実経路を保つ。
方針：cell lift と cover 包含を前合成し、右三角形を元の塔の自然性で戻す。
規約：元の射の先の経路を左三角形と扱わない。使われ方：対角右逆による反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {X Y : Tower (Mon (Complex R))}
  {f : LevelHom X Y} {i m : ℕ} {hi : i ≤ m} (c : NativeRightInverseRoof R f i m hi)

namespace NativeRightInverseRoof

lemma denominator_surjective (n : ℤ) :
    Function.Surjective (c.roof.denominator.hom.f n) := by
  have := c.roof.denominator_epi
  exact (ModuleCat.epi_iff_surjective _).1 inferInstance

def cellLift : cellResolution R (X.obj m) ⟶ c.roof.apex :=
  cellResolutionMapLift R (f.app m) c.roof.denominator (c.denominator_surjective R)
    c.roof.denominator_quasiIso

lemma cellLift_denominator : c.cellLift R ≫ c.roof.denominator =
    cellAugmentation R (X.obj m) ≫ f.app m := cellResolutionMapLift_projection R _ _ _ _

def leftDefectAfterF : Path.Witness R ((c.cellLift R ≫ c.roof.numerator) ≫ f.app i)
    ((cellAugmentation R (X.obj m) ≫ X.transition hi) ≫ f.app i) := by
  let w := c.rightPath.precomp (c.cellLift R)
  refine ⟨w.hom, w.source_eq.trans (Category.assoc _ _ _).symm, w.target_eq.trans ?_⟩
  rw [← Category.assoc, c.cellLift_denominator R, Category.assoc,
    ← f.naturality hi, ← Category.assoc]

abbrev nonpositiveSource (_c : NativeRightInverseRoof R f i m hi) :=
  connectiveCover R (cellResolution R (X.obj m))

def sourceProjection : c.nonpositiveSource R ⟶ X.obj m :=
  connectiveCoverInclusion R (cellResolution R (X.obj m)) ≫ cellAugmentation R (X.obj m)

def sourceLift : c.nonpositiveSource R ⟶ c.roof.apex :=
  connectiveCoverInclusion R (cellResolution R (X.obj m)) ≫ c.cellLift R

lemma sourceLift_denominator : c.sourceLift R ≫ c.roof.denominator =
    c.sourceProjection R ≫ f.app m := by
  rw [sourceLift, Category.assoc, c.cellLift_denominator R, ← Category.assoc]
  rfl

variable [(X.obj m).X.IsStrictlyLE 0]

lemma sourceProjection_quasiIso : QuasiIso (c.sourceProjection R).hom :=
  connectiveCoverInclusion_comp_quasiIso R (cellAugmentation R (X.obj m))
    (cellAugmentation_quasiIso R _)

lemma sourceProjection_surjective (n : ℤ) :
    Function.Surjective ((c.sourceProjection R).hom.f n) := by
  exact connectiveCoverInclusion_comp_surjective R (cellAugmentation R (X.obj m))
    (cellAugmentation_surjective R _) (cellAugmentation_quasiIso R _) n

def sourceDefectAfterF : Path.Witness R ((c.sourceLift R ≫ c.roof.numerator) ≫ f.app i)
    ((c.sourceProjection R ≫ X.transition hi) ≫ f.app i) := by
  let w := (c.leftDefectAfterF R).precomp
    (connectiveCoverInclusion R (cellResolution R (X.obj m)))
  exact ⟨w.hom,
    w.source_eq.trans (by simp only [sourceLift, Category.assoc]),
    w.target_eq.trans (by simp only [sourceProjection, Category.assoc])⟩

end NativeRightInverseRoof
end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
