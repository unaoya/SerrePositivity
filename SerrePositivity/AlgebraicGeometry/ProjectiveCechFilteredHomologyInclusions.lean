module

public import SerrePositivity.AlgebraicGeometry.ProjectiveFilteredComplexStage
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFilteredInclusions

/-!
概要：Čech H の filtered 比較を有限段からの canonical な標準写像と照合する。
方針：複体の比較と複体の H の比較の標準写像の公式を合成する。
規約：比較は既存の projectiveCechFilteredHomologyIso そのもの。
使われ方：Frobenius 順極限の増大写像の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {ι : Type} [DecidableEq ι] [Fintype ι]
variable {J : Type u} [SmallCategory J] [IsFiltered J]

/-- 有限段の Čech H の射は、filtered 比較によって各段の H の標準写像へ送られる。 -/
theorem projectiveCechFilteredHomologyIso_ι
    (D : J ⥤ Finset ι ⥤ ModuleCat.{u} R) (j : J) (q : ℕ) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map
        (fullCechComplexMap (colimit.ι D j)) ≫ (projectiveCechFilteredHomologyIso D q).hom =
      colimit.ι (D ⋙ fullCechComplexFunctor ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q) j := by
  rw [projectiveCechFilteredHomologyIso_ι_factor,
    projectiveFilteredComplexHomologyIso_ι_canonical]
  rfl

end SerrePositivity.AlgebraicGeometry
