module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNonpositiveNativeInverseRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellPathFixedBase
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraIteratedCellResolution

/-!
概要：実逆 roof の左三角形を用い、元の射の先の経路を遷移後の源へ反映する。
方針：左右の端を同じ左細分へ持ち上げ、指定した全分母経路を固定して持ち上げる。
規約：元の射の準同型性は仮定しない。使われ方：高次切断の底の実経路の反映。
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
  {f : LevelHom X Y} {i m : ℕ} {hi : i ≤ m}
  (c : NonpositiveInverseRoof R f i m hi) {T : Mon (Complex R)}

namespace NonpositiveInverseRoof

lemma sourceProjection_surjective (n : ℤ) :
    Function.Surjective (c.sourceProjection.hom.f n) := by
  have := c.sourceProjection_epi
  exact (ModuleCat.epi_iff_surjective _).1 inferInstance

def cellSourceLift (a : T ⟶ X.obj m) : cellResolution R T ⟶ c.source :=
  cellResolutionMapLift R a c.sourceProjection (c.sourceProjection_surjective R)
    c.sourceProjection_quasiIso

lemma cellSourceLift_projection (a : T ⟶ X.obj m) :
    c.cellSourceLift R a ≫ c.sourceProjection = cellAugmentation R T ≫ a :=
  cellResolutionMapLift_projection R _ _ _ _

def cellRoofLift (a : T ⟶ X.obj m) : cellResolution R T ⟶ c.roof.apex :=
  c.cellSourceLift R a ≫ c.sourceLift

lemma cellRoofLift_denominator (a : T ⟶ X.obj m) :
    c.cellRoofLift R a ≫ c.roof.denominator =
      cellAugmentation R T ≫ (a ≫ f.app m) := by
  rw [cellRoofLift, Category.assoc, c.source_denominator,
    ← Category.assoc, cellSourceLift_projection, Category.assoc]

lemma cellRoofLift_numerator (a : T ⟶ X.obj m) :
    c.cellRoofLift R a ≫ c.roof.numerator =
      cellAugmentation R T ≫ (a ≫ X.transition hi) := by
  rw [cellRoofLift, Category.assoc, c.source_numerator,
    ← Category.assoc, cellSourceLift_projection, Category.assoc]

variable {a b : T ⟶ X.obj m} (w : Path.Witness R (a ≫ f.app m) (b ≫ f.app m))

def cellDenominatorPath : Path.Witness R
    (c.cellRoofLift R a ≫ c.roof.denominator)
    (c.cellRoofLift R b ≫ c.roof.denominator) :=
  ⟨cellAugmentation R T ≫ w.hom,
    (w.precomp (cellAugmentation R T)).source_eq.trans
      (c.cellRoofLift_denominator R a).symm,
    (w.precomp (cellAugmentation R T)).target_eq.trans
      (c.cellRoofLift_denominator R b).symm⟩

lemma denominator_surjective (n : ℤ) :
    Function.Surjective (c.roof.denominator.hom.f n) := by
  have := c.roof.denominator_epi
  exact (ModuleCat.epi_iff_surjective _).1 inferInstance

def cellRoofPath : Path.Witness R
    (cellAugmentation R (cellResolution R T) ≫ c.cellRoofLift R a)
    (cellAugmentation R (cellResolution R T) ≫ c.cellRoofLift R b) :=
  (c.cellDenominatorPath R w).cellLiftFixedBase R c.roof.denominator
    (c.denominator_surjective R) c.roof.denominator_quasiIso

lemma cellRoofPath_map : (c.cellRoofPath R w).hom ≫ Path.map R c.roof.denominator =
    iteratedCellAugmentation R T 2 ≫ w.hom := by
  rw [cellRoofPath, Path.Witness.cellLiftFixedBase_map]
  rfl

def reflectCellPath : Path.Witness R
    (iteratedCellAugmentation R T 2 ≫ (a ≫ X.transition hi))
    (iteratedCellAugmentation R T 2 ≫ (b ≫ X.transition hi)) := by
  let v := (c.cellRoofPath R w).postcomp c.roof.numerator
  refine ⟨v.hom, v.source_eq.trans ?_, v.target_eq.trans ?_⟩
  · rw [Category.assoc, c.cellRoofLift_numerator R a]
    rfl
  · rw [Category.assoc, c.cellRoofLift_numerator R b]
    rfl

end NonpositiveInverseRoof
end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
