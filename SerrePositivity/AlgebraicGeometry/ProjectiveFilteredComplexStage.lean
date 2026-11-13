module

public import SerrePositivity.AlgebraicGeometry.ProjectiveFilteredHomologyInclusions

/-!
概要：複体の有限段の標準写像と、余極限の短複体の比較を照合する。
方針：各次数の評価関手の canonical な余極限比較の公式を使う。
規約：有限段の短複体と評価で得る短複体を明示的に同定する。
使われ方：Frobenius 順極限の H⁰ 比較を標準写像と可換にする。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
private theorem stage_square_inverse {C : Type*} [Category* C]
    {X Y X' Y' : C} (e : X ≅ X') (d : Y ≅ Y') (f : X ⟶ Y) (g : X' ⟶ Y')
    (h : f ≫ d.hom = e.hom ≫ g) : g ≫ d.inv = e.inv ≫ f := by
  apply (cancel_mono d.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, Iso.inv_hom_id_assoc]

variable {R : Type u} [CommRing R] {J : Type u} [SmallCategory J] [IsFiltered J]
variable (F : J ⥤ CochainComplex (ModuleCat.{u} R) ℕ)

/-- 短複体の図式を評価すると、同じ有限段の複体の短複体となる。 -/
def projectiveFilteredComplexStageIso (n : ℕ) (j : J) :
    (projectiveFilteredShortComplexDiagram
      (F ⋙ HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) n)).map
        ((evaluation J (ModuleCat.{u} R)).obj j) ≅ (F.obj j).sc n :=
  Iso.refl _

/-- 有限段からの短複体の射と、複体の余極限の標準写像は比較を介して一致する。 -/
theorem projectiveFilteredComplexShortComplexIso_ι (n : ℕ) (j : J) :
    (projectiveFilteredShortComplexDiagram
      (F ⋙ HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) n)).mapNatTrans
        (projectiveFilteredColimitInclusion j) ≫
      (projectiveFilteredComplexShortComplexIso F n).hom =
    (projectiveFilteredComplexStageIso F n j).hom ≫
      (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) n).map
        (colimit.ι F j) := by
  apply ShortComplex.hom_ext
  · exact ι_preservesColimitIso_inv
      (HomologicalComplex.eval (ModuleCat.{u} R) (.up ℕ) ((ComplexShape.up ℕ).prev n)) F j
  · exact ι_preservesColimitIso_inv
      (HomologicalComplex.eval (ModuleCat.{u} R) (.up ℕ) n) F j
  · exact ι_preservesColimitIso_inv
      (HomologicalComplex.eval (ModuleCat.{u} R) (.up ℕ) ((ComplexShape.up ℕ).next n)) F j

/-- 複体の filtered H 比較は、有限段からの標準写像と可換。
評価した短複体と各段の短複体の H の比較を明示する。 -/
theorem projectiveFilteredComplexHomologyIso_ι (n : ℕ) (j : J) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) n).map
        (colimit.ι F j) ≫ (projectiveFilteredComplexHomologyIso F n).hom =
      (ShortComplex.homologyFunctor (ModuleCat.{u} R)).map
        (projectiveFilteredComplexStageIso F n j).inv ≫
      ((projectiveFilteredShortComplexDiagram
        (F ⋙ HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) n)).mapHomologyIso
          ((evaluation J (ModuleCat.{u} R)).obj j)).hom ≫
      (projectiveFilteredShortComplexHomologyDiagramIso
        (F ⋙ HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) n)).hom.app j ≫
      colimit.ι (F ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) n) j := by
  let H := ShortComplex.homologyFunctor (ModuleCat.{u} R)
  let D := F ⋙ HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) n
  let S := projectiveFilteredShortComplexDiagram D
  have hs := stage_square_inverse (projectiveFilteredComplexStageIso F n j)
    (projectiveFilteredComplexShortComplexIso F n)
    (S.mapNatTrans (projectiveFilteredColimitInclusion j))
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) n).map (colimit.ι F j))
    (projectiveFilteredComplexShortComplexIso_ι F n j)
  have h := congrArg H.map hs
  simp only [Functor.map_comp] at h
  change H.map _ ≫ (H.map _ ≫ (projectiveFilteredShortComplexHomologyIso D).hom) = _
  simp only [Iso.symm_hom]
  dsimp only [H, D, S] at h ⊢
  rw [← Category.assoc, h, Category.assoc]
  change (ShortComplex.homologyFunctor (ModuleCat.{u} R)).map
      (projectiveFilteredComplexStageIso F n j).inv ≫
    (ShortComplex.homologyMap (S.mapNatTrans (projectiveFilteredColimitInclusion j)) ≫
      (projectiveFilteredShortComplexHomologyIso D).hom) = _
  rw [projectiveFilteredShortComplexHomologyIso_ι]
  dsimp only [D, ShortComplex.homologyFunctor]
  rfl

/-- 複体の H の比較は、各段の H からの canonical な標準写像を保つ。 -/
theorem projectiveFilteredComplexHomologyIso_ι_canonical (n : ℕ) (j : J) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) n).map
        (colimit.ι F j) ≫ (projectiveFilteredComplexHomologyIso F n).hom =
      colimit.ι (F ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) n) j := by
  rw [projectiveFilteredComplexHomologyIso_ι]
  simp only [projectiveFilteredComplexStageIso, Iso.refl_inv, Functor.map_id, Category.id_comp,
    projectiveFilteredShortComplexHomologyDiagramIso, NatIso.ofComponents_hom_app,
    Iso.symm_hom, Iso.hom_inv_id_assoc]
  exact (congrArg (fun f ↦ f ≫ colimit.ι
    (F ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) n) j)
    ((ShortComplex.homologyFunctor (ModuleCat.{u} R)).map_id _)).trans (Category.id_comp _)

end SerrePositivity.AlgebraicGeometry
