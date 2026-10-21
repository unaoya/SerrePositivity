module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeNativeSectionPostHom
public import SerrePositivity.InfinityCategories.F1.CocartesianStrictTransportEnrichedRealization
public import SerrePositivity.InfinityCategories.F1.QuasicategoryDiagramNaturalHom

/-!
概要：元の全空間の結合同型の図式値豊穣像は、底全体の既存の同じ結合比較。
方針：元の section 成分の自然性で通常の射を作り、全成分の豊穣表示を照合する。
規約：元の分類図式と既存の結合比較成分を保持する。
使われ方：同じ結合比較を coherent な辺へ実現し、元の Hom 輸送と同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p : CocartesianFibrationCategory (nerve C))

/-- 底全体の既存の同じ結合比較を、元の strict 図式の圏の射に束ねる。 -/
def cocartesianBaseChangeNativeDiagramHom :
    let T := (cocartesianStrictTransportEnrichedDiagram A).toCoreEnrichedFunctor
    let P₂ := (cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
    let P₁ := (cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj p
    T.obj P₂ ⟶ T.obj P₁ := by
  dsimp only
  apply quasicategoryDiagramHom
  refine
    { app := fun a ↦ (cocartesianBaseChangeAssociativityComponent p.val.hom l k a).hom
      naturality := ?_ }
  intro a b f
  exact cocartesianBaseChangeAssociativityComponent_naturality p.val.hom l k f

/-- 結合同型の図式値豊穣像は、底全体の既存の同じ結合比較の豊穣表示。 -/
lemma cocartesianBaseChangeNativeDiagramHom_enriched
    : let T := (cocartesianStrictTransportEnrichedDiagram A).toCoreEnrichedFunctor
      let P₂ := (cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
      let P₁ := (cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj p
      eHomEquiv SSet.{u} (cocartesianBaseChangeNativeObjectIso l k p).hom ≫ T.map P₂ P₁ =
        eHomEquiv SSet.{u} (cocartesianBaseChangeNativeDiagramHom l k p) := by
  dsimp only
  apply (SSet.unitHomEquiv _).injective
  apply Subtype.ext
  apply Subtype.ext
  funext a
  exact congrArg (SSet.unitHomEquiv _)
    (cocartesianBaseChangeNativeObjectIso_sectionPostHom l k p a)

end SerrePositivity.InfinityCategories
