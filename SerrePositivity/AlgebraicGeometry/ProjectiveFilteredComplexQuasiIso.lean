module

public import SerrePositivity.AlgebraicGeometry.ProjectiveFilteredHomologyNaturality
public import Mathlib.Algebra.Homology.QuasiIso

/-!
概要：各有限段の複体の H の同型性を filtered 余極限へ渡す。
方針：既存の canonical な H と余極限の比較の自然性で共役する。
規約：係数環と加群の宇宙を分離し、任意の大きい整数加群に適用する。
使われ方：Frobenius 順極限後の共通アフィン細分の Čech H の同型性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe u v
variable {R : Type v} [CommRing R] {J : Type u} [SmallCategory J] [IsFiltered J]
variable {F G : J ⥤ CochainComplex (ModuleCat.{u} R) ℕ}

/-- 各段で次数 q の H に同型を誘導する射は、filtered 余極限でもそうなる。 -/
theorem projectiveFilteredComplexMap_quasiIsoAt (η : F ⟶ G) (q : ℕ)
    (hη : ∀ j, QuasiIsoAt (η.app j) q) : QuasiIsoAt (colim.map η) q := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q
  let eF := projectiveFilteredComplexHomologyIso F q
  let eG := projectiveFilteredComplexHomologyIso G q
  haveI (j : J) : IsIso ((whiskerRight η H).app j) :=
    (quasiIsoAt_iff_isIso_homologyMap (η.app j) q).mp (hη j)
  haveI : IsIso (whiskerRight η H) := NatIso.isIso_of_isIso_app _
  let d := eF ≪≫ colim.mapIso (asIso (whiskerRight η H)) ≪≫ eG.symm
  have he : H.map (colim.map η) = d.hom := by
    change H.map (colim.map η) = (eF.hom ≫ colim.map (whiskerRight η H)) ≫ eG.inv
    exact (eG.eq_comp_inv).mpr (projectiveFilteredComplexHomologyIso_naturality η q)
  haveI : IsIso (H.map (colim.map η)) := by
    rw [he]
    exact d.isIso_hom
  exact (quasiIsoAt_iff_isIso_homologyMap (colim.map η) q).mpr
    (show IsIso (H.map (colim.map η)) from inferInstance)

/-- 各段の quasi-isomorphism は filtered 余極限でも quasi-isomorphism。 -/
theorem projectiveFilteredComplexMap_quasiIso (η : F ⟶ G)
    [∀ j, QuasiIso (η.app j)] : QuasiIso (colim.map η) where
  quasiIsoAt q := projectiveFilteredComplexMap_quasiIsoAt η q (fun _ ↦ inferInstance)

end SerrePositivity.AlgebraicGeometry
