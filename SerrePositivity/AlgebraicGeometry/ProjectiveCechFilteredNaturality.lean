module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFilteredComplex
public import SerrePositivity.AlgebraicGeometry.ProjectiveFilteredHomologyNaturality

/-!
概要：有限被覆の Čech と filtered 余極限の比較を、係数図式の射に自然にする。
方針：複体の canonical な余極限比較と、短複体からの H の比較を合成する。
規約：同じ有限な被覆の添字を固定する。
使われ方：Noether 近似と底変換・閉厚化の写像との整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {ι : Type} [DecidableEq ι] [Fintype ι]
variable {J : Type u} [SmallCategory J] [IsFiltered J]
variable {D E : J ⥤ Finset ι ⥤ ModuleCat.{u} R}

/-- 有限被覆の Čech 複体と filtered 余極限の比較は、係数図式の射に自然。 -/
theorem projectiveCechFilteredComplexIso_naturality (η : D ⟶ E) :
    fullCechComplexMap (colim.map η) ≫ (projectiveCechFilteredComplexIso E).hom =
      (projectiveCechFilteredComplexIso D).hom ≫
        colim.map (Functor.whiskerRight η fullCechComplexFunctor) :=
  (preservesColimitNatIso (fullCechComplexFunctor (R := R) (ι := ι))).hom.naturality η

/-- 有限被覆の Čech H の filtered 余極限比較は、係数図式の射に自然。
原典 Stacks 30.6.1 の Hⁱ の極限比較に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveCechFilteredHomologyIso_naturality (η : D ⟶ E) (q : ℕ) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map
        (fullCechComplexMap (colim.map η)) ≫ (projectiveCechFilteredHomologyIso E q).hom =
      (projectiveCechFilteredHomologyIso D q).hom ≫
        colim.map (Functor.whiskerRight η
          (fullCechComplexFunctor ⋙
            HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q)) := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q
  change H.map (fullCechComplexMap (colim.map η)) ≫
      H.map (projectiveCechFilteredComplexIso E).hom ≫
        (projectiveFilteredComplexHomologyIso (E ⋙ fullCechComplexFunctor) q).hom =
    (H.map (projectiveCechFilteredComplexIso D).hom ≫
      (projectiveFilteredComplexHomologyIso (D ⋙ fullCechComplexFunctor) q).hom) ≫ _
  rw [← H.map_comp_assoc, projectiveCechFilteredComplexIso_naturality, H.map_comp_assoc]
  have hs : H.map (colim.map (Functor.whiskerRight η fullCechComplexFunctor)) ≫
      (projectiveFilteredComplexHomologyIso (E ⋙ fullCechComplexFunctor) q).hom =
    (projectiveFilteredComplexHomologyIso (D ⋙ fullCechComplexFunctor) q).hom ≫
      colim.map (Functor.whiskerRight η (fullCechComplexFunctor ⋙ H)) :=
    projectiveFilteredComplexHomologyIso_naturality
      (Functor.whiskerRight η fullCechComplexFunctor) q
  simpa only [Category.assoc] using congrArg
    (fun k ↦ H.map (projectiveCechFilteredComplexIso D).hom ≫ k) hs

end SerrePositivity.AlgebraicGeometry
