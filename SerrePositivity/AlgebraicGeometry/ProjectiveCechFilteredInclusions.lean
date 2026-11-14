module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFilteredComplex

/-!
概要：有限段からの標準写像と Čech の filtered 比較の整合性。
方針：複体の canonical な余極限比較の標準写像の公式を使う。
規約：有限段の写像は colimit.ι が誘導する実際の複体の射。
使われ方：Frobenius 順極限の H⁰ の増大写像の有限段での照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {ι : Type} [DecidableEq ι] [Fintype ι]
variable {J : Type u} [SmallCategory J] [IsFiltered J]
variable (D : J ⥤ Finset ι ⥤ ModuleCat.{u} R)

/-- 複体の余極限比較は、有限段からの実際の標準写像を標準写像へ送る。 -/
theorem projectiveCechFilteredComplexIso_ι (j : J) :
    fullCechComplexMap (colimit.ι D j) ≫ (projectiveCechFilteredComplexIso D).hom =
      colimit.ι (D ⋙ fullCechComplexFunctor) j :=
  ι_preservesColimitIso_hom (fullCechComplexFunctor (R := R) (ι := ι)) D j

/-- 逆比較で標準写像を戻すと、有限段の係数から誘導した同じ複体の射となる。 -/
theorem projectiveCechFilteredComplexIso_inv_ι (j : J) :
    colimit.ι (D ⋙ fullCechComplexFunctor) j ≫ (projectiveCechFilteredComplexIso D).inv =
      fullCechComplexMap (colimit.ι D j) :=
  ι_preservesColimitIso_inv (fullCechComplexFunctor (R := R) (ι := ι)) D j

/-- 有限段の Čech H の写像と filtered 比較を、複体の余極限の H の比較へ分離する。
原典 Stacks 30.6.1 の Hⁱ の極限比較に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveCechFilteredHomologyIso_ι_factor (j : J) (q : ℕ) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map
        (fullCechComplexMap (colimit.ι D j)) ≫ (projectiveCechFilteredHomologyIso D q).hom =
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map
        (colimit.ι (D ⋙ fullCechComplexFunctor) j) ≫
          (projectiveFilteredComplexHomologyIso (D ⋙ fullCechComplexFunctor) q).hom := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q
  change H.map _ ≫ (H.map _ ≫ _) = H.map _ ≫ _
  rw [← H.map_comp_assoc, projectiveCechFilteredComplexIso_ι]

end SerrePositivity.AlgebraicGeometry
