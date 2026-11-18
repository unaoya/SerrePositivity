module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanDiagramOppositeValueNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.DiagramIsoNormalizationAlgebra

/-!
概要：同じ指定反転比較の値を、元の通常のKan図式と指定添字制限に沿って照合する。
方針：既存の同じ左右の成分を名付け、元の自然変換の実現の添字制限則を使う。
規約：HTT §1.1.5・Kerodon §3.1・§5.6（Tag 028T）の構成の特殊な照合。
使われ方：P3-C1PNQ、反転係数の自然性と指定νへの接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 既存の同じ左右の指定成分を、元の通常の図式の値として名付ける。 -/
def kanDiagramOppositeValueIso {J : Type u} [SmallCategory J] (F : KanDiagramObject J) :
    FunctorIso (kanDiagramCoherentNerve F.val) (kanDiagramCoherentNerve (F.val ⋙ kanObjectOpFunctor)) :=
  let D := kanDiagramUniversalEnriched J
  let Z := edgewiseOrdinaryObject F
  (kanEnrichedRealizationValueIso D.edgewiseRightComparison
    (fun j X => isQCatEquivalence_of_trivialKanFibration (edgewiseRight ((D.obj j).obj X.val).obj)) Z).symm ≪≫
  kanEnrichedRealizationValueIso D.edgewiseLeftComparison
    (fun j X => isQCatEquivalence_of_trivialKanFibration (edgewiseLeft ((D.obj j).obj X.val).obj)) Z

/-- 同じ値の指定自然性を、通常の図式を引数にした記法で回収する。 -/
lemma kanDiagramOppositeValueIso_naturality {J : Type u} [SmallCategory J]
    {F G : KanDiagramObject J} (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget) :
    Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge η).toTruncated ≫
      (kanDiagramOppositeValueIso G).hom = (kanDiagramOppositeValueIso F).hom ≫
        Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge
          (F := ⟨F.val ⋙ kanObjectOpFunctor, trivial⟩) (G := ⟨G.val ⋙ kanObjectOpFunctor, trivial⟩)
          (Functor.whiskerRight η SSet.opFunctor)).toTruncated :=
  kanDiagramOppositeValue_naturality η

/-- 元の豊穣図式で評価した左右の成分は、同じ通常の図式の指定値そのもの。 -/
lemma kanEnrichedOppositeValueIso_eq_universal
    {C : Type (u+1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [SmallCategory J] (D : KanEnrichedDiagram C J) (X : C) :
    (kanEnrichedRealizationValueIso D.edgewiseRightComparison
      (fun j Y => isQCatEquivalence_of_trivialKanFibration (edgewiseRight ((D.obj j).obj Y.val).obj))
      (edgewiseOrdinaryObject X)).symm ≪≫
    kanEnrichedRealizationValueIso D.edgewiseLeftComparison
      (fun j Y => isQCatEquivalence_of_trivialKanFibration (edgewiseLeft ((D.obj j).obj Y.val).obj))
      (edgewiseOrdinaryObject X) = kanDiagramOppositeValueIso ⟨D.evaluate X, trivial⟩ := by
  unfold kanDiagramOppositeValueIso
  simp only [kanEnrichedRealizationValueIso_eq_native]
  rfl

private lemma nativeIso_precomp {I J : Type u} [SmallCategory I] [SmallCategory J]
    (H : I ⥤ J) {F G : KanDiagramObject J}
    (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget)
    (hη : ∀ j, IsQCatEquivalence (η.app j)) :
    diagramIsoCongr (kanDiagramCoherentNerve_precomp H F.val)
      (kanDiagramCoherentNerve_precomp H G.val)
      ((kanDiagramFunctorIsoOfPointwise η hη).precomp ((SSet.uliftFunctor.{u+1,u}).map (nerveMap H))) =
    kanDiagramFunctorIsoOfPointwise (F := ⟨H ⋙ F.val, trivial⟩) (G := ⟨H ⋙ G.val, trivial⟩)
      (Functor.whiskerLeft H η) (fun i => hη (H.obj i)) := by
  apply Iso.ext
  rw [diagramIsoCongr_hom, functorIsoPrecomp_hom]
  exact kanDiagramNaturalTransformationHom_precomp H η

/-- 指定添字関手で制限した同じ反転比較の値は、制限した通常の図式の指定値。 -/
@[cite HTT "1.1.5" (partial := special) "通常の小さい図式の指定係数反転比較と添字制限の照合。"]
lemma kanDiagramOppositeValueIso_precomp :
    ∀ {I J : Type u} [SmallCategory I] [SmallCategory J] (H : I ⥤ J) (F : KanDiagramObject J),
    diagramIsoCongr (kanDiagramCoherentNerve_precomp H F.val)
      (kanDiagramCoherentNerve_precomp H (F.val ⋙ kanObjectOpFunctor))
      ((kanDiagramOppositeValueIso F).precomp ((SSet.uliftFunctor.{u+1,u}).map (nerveMap H))) =
    kanDiagramOppositeValueIso ⟨H ⋙ F.val, trivial⟩ := by
  intro I J instI instJ H F
  let q := (SSet.uliftFunctor.{u+1,u}).map (nerveMap H)
  let D := kanDiagramUniversalEnriched J
  let E := kanDiagramUniversalEnriched I
  let R := fun P : KanDiagramObject J => kanEnrichedRealizationValueIso D.edgewiseRightComparison
    (fun j Y => isQCatEquivalence_of_trivialKanFibration (edgewiseRight ((D.obj j).obj Y.val).obj))
    (edgewiseOrdinaryObject P)
  let L := fun P : KanDiagramObject J => kanEnrichedRealizationValueIso D.edgewiseLeftComparison
    (fun j Y => isQCatEquivalence_of_trivialKanFibration (edgewiseLeft ((D.obj j).obj Y.val).obj))
    (edgewiseOrdinaryObject P)
  let R' := fun P : KanDiagramObject I => kanEnrichedRealizationValueIso E.edgewiseRightComparison
    (fun i Y => isQCatEquivalence_of_trivialKanFibration (edgewiseRight ((E.obj i).obj Y.val).obj))
    (edgewiseOrdinaryObject P)
  let L' := fun P : KanDiagramObject I => kanEnrichedRealizationValueIso E.edgewiseLeftComparison
    (fun i Y => isQCatEquivalence_of_trivialKanFibration (edgewiseLeft ((E.obj i).obj Y.val).obj))
    (edgewiseOrdinaryObject P)
  let HF : KanDiagramObject I := ⟨H ⋙ F.val, trivial⟩
  let he := kanDiagramCoherentNerve_precomp H (F.val ⋙ kanEdgewiseFunctor)
  let hf := kanDiagramCoherentNerve_precomp H F.val
  let hg := kanDiagramCoherentNerve_precomp H (F.val ⋙ kanObjectOpFunctor)
  have hR : diagramIsoCongr he hf (FunctorIso.precomp (R F) q) = R' HF := by
    dsimp only [R, R']
    rw [kanEnrichedRealizationValueIso_eq_native, kanEnrichedRealizationValueIso_eq_native,
      nativeIso_precomp]
    rfl
  have hL : diagramIsoCongr he hg (FunctorIso.precomp (L F) q) = L' HF := by
    dsimp only [L, L']
    rw [kanEnrichedRealizationValueIso_eq_native, kanEnrichedRealizationValueIso_eq_native,
      nativeIso_precomp]
    rfl
  change diagramIsoCongr hf hg (FunctorIso.precomp ((R F).symm ≪≫ L F) q) =
    (R' HF).symm ≪≫ L' HF
  rw [functorIso_precomp_trans, functorIso_precomp_symm, diagramIsoCongr_trans hf he hg,
    diagramIsoCongr_symm, hR, hL]

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
