module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.KanLeftCutConeNaturality

/-!
概要：実際の weighted cone の全単体を、始点固定 coslice 値の一つの prism へ束ねる。
方針：cone の prepend 自然性を join の標準同型で移し、次数ごとの射を組む。
規約：全ての面・退化の両立を証明し、各対象の prism の存在だけで代用しない。
使われ方：共通 weighted 始域上の native pointed prism の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.SetWeightedTensors


/-- 実際の coslice 単体は、底・係数・時刻・変換を同時に制限する全ての面・退化と可換。 -/
lemma weightedKanLeftCutCosliceSimplex_naturality {I : Type u} [SmallCategory I]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) {m n : ℕ}
    (α : ⦋m⦌ ⟶ ⦋n⦌) (σ : (nerve I) _⦋n⦌)
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.val x ⋙ SSet.opFunctor)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x))).map α.op
      (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedKanLeftCutCosliceSimplex F G x σ τ s t) =
    _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedKanLeftCutCosliceSimplex F G x ((nerve I).map α.op σ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeightRestriction α ≫
        Functor.whiskerLeft (SimplexCategory.toCat.map α).toFunctor τ)
      ((SimplicialCategory.sHom F G).op.map α.op s) (Δ[1].map α.op t) := by
  apply Subtype.ext
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (stdSimplex.map α) ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedKanLeftCutConeSimplex F G x σ τ s t)) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso m).hom ≫ SSet.yonedaEquiv.symm _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_point_naturality, Category.assoc,
    SSet.yonedaEquiv_symm_naturality_left]
  congr 1
  exact congrArg SSet.yonedaEquiv.symm
    (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedKanLeftCutConeSimplex_reindex F G x α σ τ s t)

/-- 左区間の実際の共同評価を覆う、全 weighted 係数と全 Hom 変換の coslice 値の prism。 -/
def weightedKanLeftCutCoslicePrism {I : Type u} [SmallCategory I]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    ((Δ[1] : SSet.{u + 1}) ⊗ (SSet.uliftFunctor.{u + 1, u}).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.val x ⋙ SSet.opFunctor))) ⊗
      (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom F G).op ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)) where
  app _ := ↾fun q => _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedKanLeftCutCosliceSimplex F G x q.1.2.down.1
    q.1.2.down.2 q.2.down q.1.1
  naturality := by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨t, σ, τ⟩, s⟩
    exact (weightedKanLeftCutCosliceSimplex_naturality F G x α.unop σ τ s.down t).symm

/-- 構成した全 prism の射影は、元の左区間の共同実現そのもの。 -/
lemma weightedKanLeftCutCoslicePrism_projection {I : Type u} [SmallCategory I]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    weightedKanLeftCutCoslicePrism F G x ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)) =
    ((Δ[1] ◁ (SSet.uliftFunctor.{u + 1, u}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.val x ⋙ SSet.opFunctor))) ▷
        (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom F G).op) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDiagramLeftHomInterval (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramUniversalEnriched I) F G rfl rfl)) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨t, σ, τ⟩, s⟩
  exact (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedKanLeftCutCosliceSimplex_projection F G x σ τ s.down t).trans
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex_prism F G σ s.down t).symm

end SerrePositivity.InfinityCategories.Project.SetWeightedTensors
