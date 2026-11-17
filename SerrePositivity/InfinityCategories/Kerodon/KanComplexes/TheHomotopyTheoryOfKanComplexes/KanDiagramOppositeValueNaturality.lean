module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedOppositeValueFactorization
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanDiagramNaturalTransformationPrecomposition

/-!
概要：指定した係数反転比較の値が、元の通常の自然変換と可換することを示す。
方針：共通解像の左右の射影の既存の自然性を同じcoherent実現へ送り、右比較を相殺する。
規約：HTT §1.1.5・Kerodon §3.1、§5.6（Tag 028T）の構成の照合法則の特殊化。
  全図式の射の類を比較し、点ごとの像の一致だけを仮定しない。
使われ方：P3-C1PNの指定された反転比較と元のstrict底変換の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 指定共同比較の正規化した値は、元の同じ通常の自然変換の実現同型。 -/
lemma kanEnrichedRealizationValueIso_eq_native {C : Type (u+1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E : KanEnrichedDiagram C J}
    (η : KanEnrichedDiagramComparison D E)
    (hη : ∀ j (X : C), IsQCatEquivalence ((η.component j).val X)) (X : C) :
    kanEnrichedRealizationValueIso η hη X =
      kanDiagramFunctorIsoOfPointwise (F := ⟨D.evaluate X, trivial⟩)
        (G := ⟨E.evaluate X, trivial⟩) (η.app X) (fun j => hη j X) := by
  apply Iso.ext
  rw [kanEnrichedRealizationValueIso_hom]
  rfl

private def rightComponent {J : Type u} [SmallCategory J] (F : KanDiagramObject J) :
    (F.val ⋙ kanEdgewiseFunctor) ⋙ kanObjectForget ⟶ F.val ⋙ kanObjectForget :=
  (kanDiagramUniversalEnriched J).edgewiseRightComparison.app (edgewiseOrdinaryObject F)

private def leftComponent {J : Type u} [SmallCategory J] (F : KanDiagramObject J) :
    (F.val ⋙ kanEdgewiseFunctor) ⋙ kanObjectForget ⟶
      (F.val ⋙ kanObjectOpFunctor) ⋙ kanObjectForget :=
  (kanDiagramUniversalEnriched J).edgewiseLeftComparison.app (edgewiseOrdinaryObject F)

private def rightIso {J : Type u} [SmallCategory J] (F : KanDiagramObject J) :=
  kanDiagramFunctorIsoOfPointwise (F := ⟨F.val ⋙ kanEdgewiseFunctor, trivial⟩) (G := F)
    (rightComponent F) (fun j =>
      isQCatEquivalence_of_trivialKanFibration (edgewiseRight (F.val.obj j).obj))

private def leftIso {J : Type u} [SmallCategory J] (F : KanDiagramObject J) :=
  kanDiagramFunctorIsoOfPointwise (F := ⟨F.val ⋙ kanEdgewiseFunctor, trivial⟩)
    (G := ⟨F.val ⋙ kanObjectOpFunctor, trivial⟩) (leftComponent F) (fun j =>
      isQCatEquivalence_of_trivialKanFibration (edgewiseLeft (F.val.obj j).obj))

private lemma inverse_square {L : Type*} [Category* L]
    {a a' b b' c c' : L} (r : a ≅ b) (s : a' ≅ b') (l : a ⟶ c) (m : a' ⟶ c')
    (f : b ⟶ b') (e : a ⟶ a') (g : c ⟶ c')
    (hr : e ≫ s.hom = r.hom ≫ f) (hl : e ≫ m = l ≫ g) :
    f ≫ s.inv ≫ m = r.inv ≫ l ≫ g := by
  apply (cancel_epi r.hom).mp
  calc
    r.hom ≫ (f ≫ s.inv ≫ m) = (r.hom ≫ f) ≫ s.inv ≫ m := by
      simp only [Category.assoc]
    _ = (e ≫ s.hom) ≫ s.inv ≫ m := by rw [hr]
    _ = e ≫ m := by simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = l ≫ g := hl
    _ = r.hom ≫ (r.inv ≫ l ≫ g) := by
      simp only [Iso.hom_inv_id_assoc]

/-- 同じ係数反転比較の指定された値は、元の自然変換の実現と可換する。 -/
@[cite HTT "1.1.5" (partial := special) "小さい通常の図式の指定係数反転比較の自然性。"]
lemma kanDiagramOppositeValue_naturality :
∀ {J : Type u} [SmallCategory J] {F G : KanDiagramObject J}
    (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget),
  let D := kanDiagramUniversalEnriched J
  let hR := fun j (Y : SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject (KanDiagramObject J)) =>
    isQCatEquivalence_of_trivialKanFibration (edgewiseRight ((D.obj j).obj Y.val).obj)
  let hL := fun j (Y : SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject (KanDiagramObject J)) =>
    isQCatEquivalence_of_trivialKanFibration (edgewiseLeft ((D.obj j).obj Y.val).obj)
  let o := fun P : KanDiagramObject J =>
    (kanEnrichedRealizationValueIso D.edgewiseRightComparison hR (edgewiseOrdinaryObject P)).symm ≪≫
      kanEnrichedRealizationValueIso D.edgewiseLeftComparison hL (edgewiseOrdinaryObject P)
  Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge η).toTruncated ≫
    (o G).hom = (o F).hom ≫
      Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge
        (F := ⟨F.val ⋙ kanObjectOpFunctor, trivial⟩)
        (G := ⟨G.val ⋙ kanObjectOpFunctor, trivial⟩)
        (Functor.whiskerRight η SSet.opFunctor)).toTruncated := by
  intro J instJ F G η
  dsimp only
  let Fs : KanDiagramObject J := ⟨F.val ⋙ kanEdgewiseFunctor, trivial⟩
  let Gs : KanDiagramObject J := ⟨G.val ⋙ kanEdgewiseFunctor, trivial⟩
  let Fo : KanDiagramObject J := ⟨F.val ⋙ kanObjectOpFunctor, trivial⟩
  let Go : KanDiagramObject J := ⟨G.val ⋙ kanObjectOpFunctor, trivial⟩
  let ηs : Fs.val ⋙ kanObjectForget ⟶ Gs.val ⋙ kanObjectForget :=
    Functor.whiskerRight η edgewiseSubdivisionFunctor
  let ηo : Fo.val ⋙ kanObjectForget ⟶ Go.val ⋙ kanObjectForget :=
    Functor.whiskerRight η SSet.opFunctor
  have hr : ηs ≫ rightComponent G = rightComponent F ≫ η := by
    apply NatTrans.ext
    funext j
    exact edgewiseRight_naturality (η.app j)
  have hl : ηs ≫ leftComponent G = leftComponent F ≫ ηo := by
    apply NatTrans.ext
    funext j
    exact edgewiseLeft_naturality (η.app j)
  have hrh :
      Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge ηs).toTruncated ≫
        (rightIso G).hom = (rightIso F).hom ≫
          Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge η).toTruncated := by
    change Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge ηs).toTruncated ≫
      Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge (rightComponent G)).toTruncated =
      Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge (rightComponent F)).toTruncated ≫
        Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge η).toTruncated
    rw [← kanDiagramNaturalTransformationHom_comp, ← kanDiagramNaturalTransformationHom_comp, hr]
  have hlh :
      Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge ηs).toTruncated ≫
        (leftIso G).hom = (leftIso F).hom ≫
          Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge ηo).toTruncated := by
    change Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge ηs).toTruncated ≫
      Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge (leftComponent G)).toTruncated =
      Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge (leftComponent F)).toTruncated ≫
        Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge ηo).toTruncated
    rw [← kanDiagramNaturalTransformationHom_comp, ← kanDiagramNaturalTransformationHom_comp, hl]
  simp only [kanEnrichedRealizationValueIso_eq_native]
  change Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge η).toTruncated ≫
      ((rightIso G).symm ≪≫ leftIso G).hom =
    ((rightIso F).symm ≪≫ leftIso F).hom ≫
      Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge ηo).toTruncated
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  exact inverse_square (rightIso F) (rightIso G) (leftIso F).hom (leftIso G).hom _ _ _ hrh hlh

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
