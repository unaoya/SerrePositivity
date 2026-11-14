module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.CoherentDiagrams.CoherentOppositeEdge
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.Reindexing.FinalHornFilledRestriction
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.InitialFinalComparisons.FinalHornLastEdge
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RelativeOuterHornOp

/-!
概要：前合成が trivial Kan な固定初期辺を持つ coherent ホーンを充填する。
方針：反対豊穣圏上の最終ホーンで二つの Hom を延長し、単体を元へ反転する。
規約：反対圏のモデル構造を要求しない。使われ方：元の左 Quillen 辺の coCartesian 性。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory SSet
open CategoryTheory.SimplicialThickening

open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

variable {n : ℕ}
  (σ : (Λ[n + 2, 0] : SSet.{max u v}) ⟶ SimplicialNerve C)

/-- 初期ホーンを反対豊穣圏の最終ホーンへ送る。 -/
def initialHornOppositeMap :
    (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ SimplicialNerve Cᵒᵖ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.reverseInitialHornMap n σ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeIso C).hom

/-- 固定初期辺は同じ射の反対を表す固定最終辺になる。 -/
lemma initialHornOppositeMap_edge {X Y : C} (f : X ⟶ Y)
    (h : σ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge n) = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge) :
    (initialHornOppositeMap σ).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f.op).edge := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeMap C).app _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.reverseInitialHornMap n σ).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.reverseInitialHornMap_edge, h, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentNerveOppositeMap_edge]

/-- 反対ホーンの対象は、反転した添字の元の対象の反対である。 -/
lemma initialHornOppositeMap_obj (a : Fin (n + 3)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj (initialHornOppositeMap σ) a = Opposite.op (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ a.rev) := by
  rfl

/-- 元の固定初期辺の前合成条件から、元の初期ホーンの充填を得る。 -/
lemma initialHornFiller_of_precomposition {X Y : C} (f : X ⟶ Y)
    (h : σ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge n) = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge)
    [KanComplex (SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (Fin.last (n + 2))))]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (eHomWhiskerRight SSet f (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (Fin.last (n + 2))))] :
    ∃ l : (Δ[n + 2] : SSet.{max u v}) ⟶ SimplicialNerve C, (Λ[n + 2, 0]).ι ≫ l = σ := by
  have hKan : KanComplex (SimplicialCategory.sHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj (initialHornOppositeMap σ) 0)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj (initialHornOppositeMap σ) (Fin.last (n + 2)))) := by
    rw [initialHornOppositeMap_obj, initialHornOppositeMap_obj, Fin.rev_zero, Fin.rev_last]
    exact inferInstanceAs (KanComplex
      (SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (Fin.last (n + 2)))))
  have hTF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (eHomWhiskerLeft SSet
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj (initialHornOppositeMap σ) 0) f.op) := by
    rw [initialHornOppositeMap_obj, Fin.rev_zero, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.eHomWhiskerLeft_op_eq_right]
    infer_instance
  obtain ⟨g, hz, hg, front, hf, hfg⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornUnknownHom_extension_of_fixedEdge
    (initialHornOppositeMap σ) f.op (initialHornOppositeMap_edge σ f h)
  let l' := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFiller (initialHornOppositeMap σ) g front hf hg hfg
  have hl' : (Λ[n + 2, Fin.last (n + 2)]).ι ≫ l' = initialHornOppositeMap σ :=
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFiller_restriction (initialHornOppositeMap σ) g front hf hg hfg hz
  let lbar := l' ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeIso C).inv
  have hlbar : (Λ[n + 2, Fin.last (n + 2)]).ι ≫ lbar = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.reverseInitialHornMap n σ := by
    change ((Λ[n + 2, Fin.last (n + 2)]).ι ≫ l') ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeIso C).inv = _
    rw [hl']
    simp only [initialHornOppositeMap, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let l := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex (n + 2) lbar ≫
    (SSet.opFunctorCompOpFunctorIso.app (SimplicialNerve C)).hom
  refine ⟨l, ?_⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseHornMap_injective (SimplicialNerve C) (n + 2) 0
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseHornMap_restrict, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex_back]
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornReverseIndexIso n).hom).1
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornReverseIndexIso_hom_ι]
  exact hlbar

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
