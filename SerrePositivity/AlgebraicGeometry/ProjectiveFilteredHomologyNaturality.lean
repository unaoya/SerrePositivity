module

public import SerrePositivity.AlgebraicGeometry.ProjectiveFilteredHomology

/-!
概要：filtered 余極限とコホモロジーの比較を、図式の射に自然にする。
方針：短複体の係数制限・余極限の比較の自然性を合成する。
規約：同型は構成した canonical な比較を使う。
使われ方：Čech 版の近似と各係数操作との整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type v} [CommRing R] {J : Type u} [SmallCategory J] [IsFiltered J]

local instance projectiveFilteredHomologyNaturalityExactColimits :
    HasExactColimitsOfShape J (ModuleCat.{u} R) :=
  moduleCatFiltered_hasExactColimitsOfShape R J

/-- 関手圏の短複体の H と各段の H の比較は、図式の射に自然。 -/
theorem projectiveFilteredShortComplexHomologyDiagramIso_naturality
    {S T : J ⥤ ShortComplex (ModuleCat.{u} R)} (η : S ⟶ T) :
    ShortComplex.homologyMap
        ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).inverse.map η) ≫
          (projectiveFilteredShortComplexHomologyDiagramIso T).hom =
      (projectiveFilteredShortComplexHomologyDiagramIso S).hom ≫
        Functor.whiskerRight η (ShortComplex.homologyFunctor (ModuleCat.{u} R)) := by
  apply NatTrans.ext
  funext j
  exact ShortComplex.mapHomologyIso_inv_naturality
    ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).inverse.map η)
    ((evaluation J (ModuleCat.{u} R)).obj j)

/-- 短複体の filtered 余極限の H の比較は、図式の射に自然。 -/
theorem projectiveFilteredShortComplexHomologyIso_naturality
    {S T : J ⥤ ShortComplex (ModuleCat.{u} R)} (η : S ⟶ T) :
    ShortComplex.homologyMap
        ((colim (J := J) (C := ModuleCat.{u} R)).mapShortComplex.map
          ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).inverse.map η)) ≫
        (projectiveFilteredShortComplexHomologyIso T).hom =
      (projectiveFilteredShortComplexHomologyIso S).hom ≫
        colim.map (Functor.whiskerRight η (ShortComplex.homologyFunctor (ModuleCat.{u} R))) := by
  simp only [projectiveFilteredShortComplexHomologyIso, Iso.trans_hom, Functor.mapIso_hom]
  simp only [projectiveFilteredShortComplexDiagram]
  have h := ShortComplex.mapHomologyIso_hom_naturality
    ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).inverse.map η)
    (colim (J := J) (C := ModuleCat.{u} R))
  rw [← Category.assoc, h, Category.assoc, ← Functor.map_comp,
    projectiveFilteredShortComplexHomologyDiagramIso_naturality, Functor.map_comp]
  simp only [Category.assoc]

variable {F G : J ⥤ CochainComplex (ModuleCat.{u} R) ℕ}

/-- 複体の短複体と各項の余極限の比較は、図式の射に自然。 -/
theorem projectiveFilteredComplexShortComplexIso_naturality (η : F ⟶ G) (q : ℕ) :
    (colim (J := J) (C := ModuleCat.{u} R)).mapShortComplex.map
        ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).inverse.map
          (Functor.whiskerRight η
            (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) q))) ≫
        (projectiveFilteredComplexShortComplexIso G q).hom =
      (projectiveFilteredComplexShortComplexIso F q).hom ≫
        (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) q).map
          (colim.map η) := by
  apply ShortComplex.hom_ext
  · exact (preservesColimitNatIso
      (HomologicalComplex.eval (ModuleCat.{u} R) (.up ℕ) ((ComplexShape.up ℕ).prev q))).inv.naturality η
  · exact (preservesColimitNatIso
      (HomologicalComplex.eval (ModuleCat.{u} R) (.up ℕ) q)).inv.naturality η
  · exact (preservesColimitNatIso
      (HomologicalComplex.eval (ModuleCat.{u} R) (.up ℕ) ((ComplexShape.up ℕ).next q))).inv.naturality η

/-- 短複体の比較の逆向きも、図式の射に自然。 -/
theorem projectiveFilteredComplexShortComplexIso_inv_naturality (η : F ⟶ G) (q : ℕ) :
    (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) q).map (colim.map η) ≫
        (projectiveFilteredComplexShortComplexIso G q).inv =
      (projectiveFilteredComplexShortComplexIso F q).inv ≫
        (colim (J := J) (C := ModuleCat.{u} R)).mapShortComplex.map
          ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).inverse.map
            (Functor.whiskerRight η
              (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) q))) := by
  apply (cancel_epi (projectiveFilteredComplexShortComplexIso F q).hom).mp
  apply (cancel_mono (projectiveFilteredComplexShortComplexIso G q).hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc] using
    (projectiveFilteredComplexShortComplexIso_naturality η q).symm

/-- 複体の filtered 余極限と各次数の H の比較は、図式の射に自然。
Čech 版の近似比較（原典 Stacks 30.6.1 の Hⁱ）への加群圏の計算。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveFilteredComplexHomologyIso_naturality (η : F ⟶ G) (q : ℕ) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map (colim.map η) ≫
        (projectiveFilteredComplexHomologyIso G q).hom =
      (projectiveFilteredComplexHomologyIso F q).hom ≫
        colim.map (Functor.whiskerRight η
          (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q)) := by
  let H := ShortComplex.homologyFunctor (ModuleCat.{u} R)
  let V := HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) q
  change H.map (V.map (colim.map η)) ≫
      H.map (projectiveFilteredComplexShortComplexIso G q).inv ≫
        (projectiveFilteredShortComplexHomologyIso (G ⋙ V)).hom =
    (H.map (projectiveFilteredComplexShortComplexIso F q).inv ≫
      (projectiveFilteredShortComplexHomologyIso (F ⋙ V)).hom) ≫ _
  rw [← H.map_comp_assoc, projectiveFilteredComplexShortComplexIso_inv_naturality,
    H.map_comp_assoc]
  have hs : H.map
      ((colim (J := J) (C := ModuleCat.{u} R)).mapShortComplex.map
        ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).inverse.map
          (Functor.whiskerRight η V))) ≫
      (projectiveFilteredShortComplexHomologyIso (G ⋙ V)).hom =
    (projectiveFilteredShortComplexHomologyIso (F ⋙ V)).hom ≫
      colim.map (Functor.whiskerRight η
        (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q)) :=
    projectiveFilteredShortComplexHomologyIso_naturality (Functor.whiskerRight η V)
  simpa only [Category.assoc] using congrArg
    (fun k ↦ H.map (projectiveFilteredComplexShortComplexIso F q).inv ≫ k) hs

end SerrePositivity.AlgebraicGeometry
