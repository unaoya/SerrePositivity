module

public import SerrePositivity.AlgebraicGeometry.ProjectiveChartFrobeniusRingColimit
public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitIntNaturality
public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousChartRestriction

/-!
概要：標準開の Frobenius 系の比較が、実際の標準開の制限と可換であることを示す。
方針：有限段では既存の斉次局所化の制限比較を使い、余極限の関手で移す。
規約：標準開の環準同型に沿う射を用い、任意の加法写像で代用しない。
使われ方：F6 の各標準開の比較を Čech の係数図式へ接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

/-- 標準開を狭める実際の環の射が誘導する、Frobenius 系の自然変換。 -/
abbrev projectiveChartRingFrobeniusRestriction {T U : Finset ι} (h : T ⊆ U) :
    projectiveChartRingFrobeniusFunctor G p hp hR T ⟶
      projectiveChartRingFrobeniusFunctor G p hp hR U :=
  frobeniusIntDirectSystemNatTrans p hp
    (projectiveHomogeneousChart_primeCast G p hR T)
    (projectiveHomogeneousChart_primeCast G p hR U)
    (projectiveHomogeneousChartRestrictionRingHom G h)

/-- 係数関手と環の Frobenius 系の比較は標準開の制限に自然。 -/
theorem projectiveChartFrobeniusRingSystemIso_restriction
    {T U : Finset ι} (h : T ⊆ U) :
    whiskerLeft (projectiveCechFrobeniusCoefficientFunctor G p hp hR hA)
        ((evaluation (Finset ι) (ModuleCat.{u} ℤ)).map (homOfLE h)) ≫
        (projectiveChartFrobeniusRingSystemIso G p hp hR hA U).hom =
      (projectiveChartFrobeniusRingSystemIso G p hp hR hA T).hom ≫
        projectiveChartRingFrobeniusRestriction G p hp hR h := by
  apply NatTrans.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change projectiveHomogeneousChartLinearEquiv G U
      (((projectiveNatGradedModuleChartDiagram G 0).map (homOfLE h)).hom x) =
    projectiveHomogeneousChartRestrictionRingHom G h
      (projectiveHomogeneousChartLinearEquiv G T x)
  have hh := congrArg (fun k ↦ k.hom x)
    ((projectiveHomogeneousChartDiagramIso G).hom.naturality (homOfLE h))
  exact hh.trans (projectiveHomogeneousChartDiagram_map G h
    (projectiveHomogeneousChartLinearEquiv G T x))

/-- 標準開の制限に関する同じ可換四角形は、系の余極限でも成り立つ。 -/
theorem projectiveChartFrobeniusRingSystemColimit_restriction
    {T U : Finset ι} (h : T ⊆ U) :
    colim.map (whiskerLeft (projectiveCechFrobeniusCoefficientFunctor G p hp hR hA)
        ((evaluation (Finset ι) (ModuleCat.{u} ℤ)).map (homOfLE h))) ≫
        (colim.mapIso (projectiveChartFrobeniusRingSystemIso G p hp hR hA U)).hom =
      (colim.mapIso (projectiveChartFrobeniusRingSystemIso G p hp hR hA T)).hom ≫
        colim.map (projectiveChartRingFrobeniusRestriction G p hp hR h) := by
  simpa only [Functor.mapIso_hom, ← colim.map_comp] using
    congrArg (fun η ↦ colim.map η)
      (projectiveChartFrobeniusRingSystemIso_restriction G p hp hR hA h)

/-- 標準開ごとの環の順極限表示は、実際の標準開環の制限に自然。 -/
theorem projectiveChartFrobeniusRingColimitIso_restriction
    {T U : Finset ι} (h : T ⊆ U) :
    (colimit (projectiveCechFrobeniusCoefficientFunctor G p hp hR hA)).map (homOfLE h) ≫
        (projectiveChartFrobeniusRingColimitIso G p hp hR hA U).hom =
      (projectiveChartFrobeniusRingColimitIso G p hp hR hA T).hom ≫
        ModuleCat.ofHom (frobeniusDirectLimitMap p hp
          (projectiveHomogeneousChart_primeCast G p hR T)
          (projectiveHomogeneousChart_primeCast G p hR U)
          (projectiveHomogeneousChartRestrictionRingHom G h)).toAddMonoidHom.toIntLinearMap := by
  let rT := ringDirectLimitIntColimitIso
    (frobeniusDirectSystemMap _ p hp (projectiveHomogeneousChart_primeCast G p hR T))
  let rU := ringDirectLimitIntColimitIso
    (frobeniusDirectSystemMap _ p hp (projectiveHomogeneousChart_primeCast G p hR U))
  have hr : colim.map (projectiveChartRingFrobeniusRestriction G p hp hR h) ≫ rU.inv =
      rT.inv ≫ ModuleCat.ofHom (frobeniusDirectLimitMap p hp
        (projectiveHomogeneousChart_primeCast G p hR T)
        (projectiveHomogeneousChart_primeCast G p hR U)
        (projectiveHomogeneousChartRestrictionRingHom G h)).toAddMonoidHom.toIntLinearMap := by
    apply (cancel_mono rU.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [frobeniusDirectLimitIntColimitIso_naturality]
    simp only [← Category.assoc, rT, Iso.inv_hom_id, Category.id_comp]
  have he := colimit_map_colimitObjIsoColimitCompEvaluation_hom
    (projectiveCechFrobeniusCoefficientFunctor G p hp hR hA) (homOfLE h)
  dsimp only [colimitObjIsoColimitCompEvaluation] at he
  have hs := projectiveChartFrobeniusRingSystemColimit_restriction G p hp hR hA h
  simp only [projectiveChartFrobeniusRingColimitIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Category.assoc, he]
  simp only [Category.assoc]
  let eT := preservesColimitIso ((evaluation (Finset ι) (ModuleCat.{u} ℤ)).obj T)
    (projectiveCechFrobeniusCoefficientFunctor G p hp hR hA)
  have hs' := congrArg (fun k ↦ eT.hom ≫ k ≫ rU.inv) hs
  calc
    _ = eT.hom ≫ (colim.mapIso
        (projectiveChartFrobeniusRingSystemIso G p hp hR hA T)).hom ≫
        colim.map (projectiveChartRingFrobeniusRestriction G p hp hR h) ≫ rU.inv := by
      simpa only [Category.assoc, colimMap_eq, eT, rU] using hs'
    _ = _ := by rw [hr]

end SerrePositivity.AlgebraicGeometry
