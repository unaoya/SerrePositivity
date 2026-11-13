module

public import SerrePositivity.AlgebraicGeometry.ColimitInclusionTransport
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFilteredHomologyInclusions
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechIntFiltered

/-!
概要：整数係数の Čech H の filtered 比較を有限段の標準写像と照合する。
方針：ULift ℤ への移送、Čech H の比較、係数の制限の比較を合成する。
規約：既存の projectiveIntCechFilteredHomologyIso の標準写像の公式。
使われ方：Frobenius 系の有限段からの増大写像の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe u
variable {ι : Type} [DecidableEq ι] [Fintype ι]
variable {J : Type u} [SmallCategory J] [IsFiltered J]

/-- 整数係数の Čech H の既存の比較は有限段からの標準写像を保つ。 -/
theorem projectiveIntCechFilteredHomologyIso_ι
    (D : J ⥤ Finset ι ⥤ ModuleCat.{u} ℤ) (j : J) (q : ℕ) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q).map
        (fullCechComplexMap (colimit.ι D j)) ≫
      (projectiveIntCechFilteredHomologyIso D q).hom =
    colimit.ι (D ⋙ fullCechComplexFunctor ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q) j := by
  let L := projectiveIntCechLiftFunctor.{u} (ι := ι)
  let H := fullCechComplexFunctor (R := ULift.{u} ℤ) (ι := ι) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} (ULift.{u} ℤ)) (.up ℕ) q
  let U := ModuleCat.restrictScalars (Int.castRingHom (ULift.{u} ℤ))
  let a := preservesColimitIso L D
  let b := projectiveCechFilteredHomologyIso (D ⋙ L) q
  let c := preservesColimitIso U ((D ⋙ L) ⋙ H)
  have hab := colimitInclusion_composition D L H a b
    (fun k ↦ ι_preservesColimitIso_hom L D k)
    (fun k ↦ projectiveCechFilteredHomologyIso_ι (D ⋙ L) k q)
  have habc := colimitInclusion_composition D (L ⋙ H) U (H.mapIso a ≪≫ b) c
    hab (fun k ↦ ι_preservesColimitIso_hom U ((D ⋙ L) ⋙ H) k)
  have h := colimitInclusion_natIso D
    (projectiveIntCechLiftHomologyNatIso.{u} (ι := ι) q)
    (U.mapIso (H.mapIso a ≪≫ b) ≪≫ c) habc j
  change (fullCechComplexFunctor ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q).map
      (colimit.ι D j) ≫
    ((projectiveIntCechLiftHomologyNatIso.{u} (ι := ι) q).app (colimit D)).hom ≫
    U.map (H.map a.hom) ≫ U.map b.hom ≫ c.hom ≫
    colim.map (isoWhiskerLeft D
      (projectiveIntCechLiftHomologyNatIso.{u} (ι := ι) q)).inv = _
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    Iso.symm_hom, Category.assoc] using h

end SerrePositivity.AlgebraicGeometry
