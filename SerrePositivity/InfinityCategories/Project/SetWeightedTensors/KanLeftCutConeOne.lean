module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.KanLeftCutConeZero
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.KanHomCompositeDiagram

/-!
概要：左切断の時刻一で、実際の weighted Hom 作用後の元の cone を回収する。
方針：時刻一の切断係数を、元の全変換で評価した合成係数へ厳密に戻す。
規約：合成係数の自然性は元の weighted nerve の作用から構成済み。
使われ方：共通 weighted 始域上の pointed prism の終点の固定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.SetWeightedTensors


/-- 全頂点が時刻一なら、切断 cone は元の weighted Hom 作用後の cone そのもの。 -/
lemma weightedKanLeftCutConeSimplex_one {I : Type u} [SmallCategory I]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) {n : ℕ} (σ : (nerve I) _⦋n⦌)
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.val x ⋙ SSet.opFunctor)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌)
    (ht : ∀ j, (stdSimplex.objEquiv t).toOrderHom j = 1) :
    _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedKanLeftCutConeSimplex F G x σ τ s t =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeSimplex G.val x (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedKanHomCompositeDiagram F G x σ τ s) := by
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentConeSimplexOfHead_eq_weighted G.val x σ
    (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedKanHomCompositeDiagram F G x σ τ s) _
    (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedKanLeftCutConeHead F G x σ τ s t)
    (fun j => _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex_obj_one F G σ s t j (ht j)) (fun j => ?_)
    (fun i j hij => _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedKanLeftCutTail_one F G σ s t i j hij (ht i) (ht j))
  change _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedKanLeftCutHead F G x σ τ s t j ≫
    eqToHom (congrArg (SimplicialCategory.sHom x)
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex_obj_one F G σ s t j (ht j))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedKanLeftCutHead_one F G x σ τ s t j (ht j)]
  change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumMap j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap
    ((_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedKanHomCompositeDiagram F G x σ τ s).app j)
  rw [_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedKanHomCompositeDiagram_app]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.weightedConeCutCoefficient_one x (F.val.obj (σ.obj j)) (G.val.obj (σ.obj j))
    (stdSimplex.objEquiv t).toOrderHom ht j (τ.app j) _

/-- 時刻一の coslice 単体は、元の全変換による weighted 作用後の同じ比較単体。 -/
lemma weightedKanLeftCutCosliceSimplex_one {I : Type u} [SmallCategory I]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) {n : ℕ} (σ : (nerve I) _⦋n⦌)
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.val x ⋙ SSet.opFunctor)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌)
    (ht : ∀ j, (stdSimplex.objEquiv t).toOrderHom j = 1) :
    _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedKanLeftCutCosliceSimplex F G x σ τ s t =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCosliceSimplex G.val x ⟨σ, _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedKanHomCompositeDiagram F G x σ τ s⟩ := by
  apply Subtype.ext
  exact congrArg (fun A : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋n + 1⦌ =>
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftPointStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm A)
      (weightedKanLeftCutConeSimplex_one F G x σ τ s t ht)

/-- 元の全 Hom に沿う weighted 係数の反転後合成を、同じ宇宙へ持ち上げた実際の族。 -/
def weightedKanHomCompositeFamily {I : Type u} [SmallCategory I]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.val x ⋙ SSet.opFunctor)) ⊗
        (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom F G).op ⟶
    (SSet.uliftFunctor.{u + 1, u}).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram G.val x ⋙ SSet.opFunctor)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso _ _).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.val x ⋙ SSet.opFunctor)) ◁
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramReflectedHomPostcomposition F G x) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveMappingFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.val x ⋙ SSet.opFunctor)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram G.val x ⋙ SSet.opFunctor))

/-- 全 weighted 係数・全 Hom の prism の終点は、元の weighted 作用後の coslice 比較。 -/
lemma weightedKanLeftCutCoslicePrism_one {I : Type u} [SmallCategory I]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ▷ _) ≫ _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedKanLeftCutCoslicePrism F G x =
      weightedKanHomCompositeFamily F G x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCosliceComparison G.val x := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨⟨σ, τ⟩⟩, s⟩
  exact weightedKanLeftCutCosliceSimplex_one F G x σ τ s.down _ (fun _ => rfl)

end SerrePositivity.InfinityCategories.Project.SetWeightedTensors
