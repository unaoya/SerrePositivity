module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedComparisonEvaluation

/-!
概要：共同比較の実現値同型の射を元の通常の自然変換へ同定する。
方針：同じ共同辺の係数制限と、既存の端点移送の法則を使う。
規約：値ごとに別の可逆射を選ばず、指定した実現同型の射を計算する。
使われ方：Kerodon §3.1（Tag 00SZ）・Corollary 5.6.0.6（Tag 028T）の
共同切断実現における、引き戻しの貼り合わせ比較の射の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open Project.LocalizationAndKanExtensionAuxiliaries
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes
namespace TheHomotopyTheoryOfKanComplexes

/-- 概要：指定した共同比較の実現値同型の射は元の自然変換の辺の類。
方針：元の共同辺の係数制限を計算し、同じ端点移送を消去する。
規約：全添字の図式間の射として一致する。使われ方：同じ貼り合わせ比較の分類像の計算。 -/
lemma kanEnrichedRealizationValueIso_hom
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E : KanEnrichedDiagram C J}
    (η : KanEnrichedDiagramComparison D E)
    (hη : ∀ j (X : C), IsQCatEquivalence
      (X := ((D.obj j).obj X).obj) (Y := ((E.obj j).obj X).obj) ((η.component j).val X))
    (X : C) :
    (kanEnrichedRealizationValueIso η hη X).hom =
      Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge
        (F := ⟨D.evaluate X, trivial⟩) (G := ⟨E.evaluate X, trivial⟩) (η.app X)).toTruncated := by
  let ι := lift (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj (nerve J)))
    (SSet.const (coherentNerveVertex X))
  let e := (η.jointComparisonIso hη).precomp ι
  have hd : ι ≫ D.jointEvaluation = kanDiagramCoherentNerve (D.evaluate X) :=
    kanEnrichedJointEvaluation_restrict D X
  have he : ι ≫ E.jointEvaluation = kanDiagramCoherentNerve (E.evaluate X) :=
    kanEnrichedJointEvaluation_restrict E X
  have h := iso_endpoints_heq e
    (congrArg (fun f ↦ HomotopyCategory.mk (functorVertex f)) hd)
    (congrArg (fun f ↦ HomotopyCategory.mk (functorVertex f)) he)
  have hv := kanEnrichedRealizationValueIso_heq_precomp η hη X
  have hEq := eq_of_heq (hv.trans h.symm)
  rw [hEq]
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.inv, eqToIso.hom]
  change eqToHom _ ≫
      (hoFunctor.map ((pre ι).app SpaceInfinity.{u})).toFunctor.map
        (Truncated.HomotopyCategory.homMk η.jointComparisonEdge.toTruncated) ≫
      eqToHom _ = _
  apply Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homMk_transport
    (congrArg functorVertex hd) (congrArg functorVertex he)
  exact η.jointComparisonEdge_restrict X

end TheHomotopyTheoryOfKanComplexes
end SerrePositivity.InfinityCategories.Kerodon.KanComplexes
