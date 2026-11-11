module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.ConeHeadRestriction
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.KanLeftCutHeadNaturality
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.KanLeftCutCone

/-!
概要：実際の左区間上に組んだ始点固定 cone は、全ての面・退化と可換。
方針：初点・head・空の逆向き Hom・正頂点間の四分岐で豊穣関手を照合する。
規約：元の対角単体と head の証明済みの自然性だけを使う。
使われ方：全ての weighted cone 単体を一つの coslice 値の prism へ束ねる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.SetWeightedTensors


/-- 実際の始点固定 cone 全体は、prepend による任意の面・退化と厳密に可換。 -/
lemma weightedKanLeftCutConeSimplex_reindex {I : Type u} [SmallCategory I]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) {m n : ℕ}
    (α : ⦋m⦌ ⟶ ⦋n⦌) (σ : (nerve I) _⦋n⦌)
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.val x ⋙ SSet.opFunctor)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) :
    (SimplicialThickening.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom α.toOrderHom).uliftMap).comp SSet
      (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedKanLeftCutConeSimplex F G x σ τ s t) =
    _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedKanLeftCutConeSimplex F G x ((nerve I).map α.op σ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeightRestriction α ≫
        Functor.whiskerLeft (SimplexCategory.toCat.map α).toFunctor τ)
      ((SimplicialCategory.sHom F G).op.map α.op s) (Δ[1].map α.op t) := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentConeSimplexOfHead_reindex x α _ _
    (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedKanLeftCutConeHead F G x σ τ s t) _
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex_naturality F G α σ s t)
    (fun j => _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedKanLeftCutHead_reindex F G x α σ τ s t j)

end SerrePositivity.InfinityCategories.Project.SetWeightedTensors
