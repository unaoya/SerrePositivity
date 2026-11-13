module

public import SerrePositivity.AlgebraicGeometry.ProjectiveFilteredHomology

/-!
概要：filtered 余極限の短複体の H の比較を有限段の標準写像に沿って計算する。
方針：評価関手から余極限関手への自然変換と homologyMap_mapNatTrans を使う。
規約：短複体の各成分の射は colimit.ι そのもの。
使われ方：Frobenius 順極限の Čech H⁰ 比較の標準写像との整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {J : Type u} [SmallCategory J] [IsFiltered J]

/-- 評価関手から余極限関手への、標準写像の自然変換。 -/
def projectiveFilteredColimitInclusion (j : J) :
    (evaluation J (ModuleCat.{u} R)).obj j ⟶ colim (J := J) where
  app D := colimit.ι D j
  naturality D E f := (colimit.ι_map f j).symm

/-- 短複体の H の比較は、有限段からの標準写像と可換。 -/
theorem projectiveFilteredShortComplexHomologyInclusion
    (S : ShortComplex (J ⥤ ModuleCat.{u} R)) (j : J) :
    (S.mapHomologyIso ((evaluation J (ModuleCat.{u} R)).obj j)).inv ≫
      ShortComplex.homologyMap (S.mapNatTrans (projectiveFilteredColimitInclusion j)) ≫
        (S.mapHomologyIso (colim (J := J))).hom = colimit.ι S.homology j := by
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- 短複体の図式の H の比較は、各段からの標準写像を標準写像へ送る。 -/
theorem projectiveFilteredShortComplexHomologyIso_ι
    (D : J ⥤ ShortComplex (ModuleCat.{u} R)) (j : J) :
    ShortComplex.homologyMap ((projectiveFilteredShortComplexDiagram D).mapNatTrans
      (projectiveFilteredColimitInclusion j)) ≫
        (projectiveFilteredShortComplexHomologyIso D).hom =
      ((projectiveFilteredShortComplexDiagram D).mapHomologyIso
        ((evaluation J (ModuleCat.{u} R)).obj j)).hom ≫
      (projectiveFilteredShortComplexHomologyDiagramIso D).hom.app j ≫
      colimit.ι (D ⋙ ShortComplex.homologyFunctor (ModuleCat.{u} R)) j := by
  let S := projectiveFilteredShortComplexDiagram D
  rw [← cancel_epi (S.mapHomologyIso ((evaluation J (ModuleCat.{u} R)).obj j)).inv]
  change (S.mapHomologyIso ((evaluation J (ModuleCat.{u} R)).obj j)).inv ≫
      ShortComplex.homologyMap (S.mapNatTrans (projectiveFilteredColimitInclusion j)) ≫
        (S.mapHomologyIso (colim (J := J))).hom ≫
          colim.map (projectiveFilteredShortComplexHomologyDiagramIso D).hom = _
  have h := congrArg (fun f ↦ f ≫ colim.map
    (projectiveFilteredShortComplexHomologyDiagramIso D).hom)
    (projectiveFilteredShortComplexHomologyInclusion S j)
  rw [colimit.ι_map] at h
  dsimp only [S] at h ⊢
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h

end SerrePositivity.AlgebraicGeometry
