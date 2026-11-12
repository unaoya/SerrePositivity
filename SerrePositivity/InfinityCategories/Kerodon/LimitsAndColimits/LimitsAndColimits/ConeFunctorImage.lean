module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.HomFunctorImage
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NervePostcomposition

/-!
概要：weighted cone の元の単体は豊穣関手による後合成と可換。
方針：係数評価の後合成則と、初点・正頂点の Hom の四分岐を照合する。
規約：全係数単体を保ち、Kan 性や同値性の仮定を追加しない。
使われ方：実際の weighted coslice 比較の後合成自然性。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits


/-- 反転した係数の自然変換で写した係数評価は、元の係数評価への後合成。 -/
lemma weightedCoherentCoefficient_functorImage {I : Type u} [SmallCategory I]
    {H K : I ⥤ SSet.{u}} (η : H ⟶ K) {n : ℕ} {σ : ComposableArrows I n}
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ σ ⋙ H ⋙ SSet.opFunctor) (j : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentCoefficient
      (τ ≫ Functor.whiskerLeft σ (Functor.whiskerRight η SSet.opFunctor)) j =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentCoefficient τ j ≫ η.app (σ.obj j) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumMap j ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap (τ.app j ≫ SSet.opFunctor.map (η.app (σ.obj j))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap_post]
  exact (Category.assoc _ _ _).symm

/-- 元の weighted cone の全単体を豊穣関手で写すと、写した係数からの同じ cone になる。 -/
lemma weightedConeSimplex_functorImage {I : Type u} [SmallCategory I]
    {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    (F : I ⥤ C) (R : EnrichedFunctor SSet.{u} C D) (x : C) {n : ℕ}
    {σ : ComposableArrows I n}
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeSimplex F x τ).comp SSet R =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeSimplex (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R) (R.obj x)
        (τ ≫ Functor.whiskerLeft σ
          (Functor.whiskerRight (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedHomFunctorImage F R x) SSet.opFunctor)) := by
  refine EnrichedFunctor.ext SSet (fun i => ?_) (fun i j => ?_)
  · rcases i with ⟨⟨i⟩⟩
    induction i using Fin.cases <;> rfl
  · rcases i with ⟨⟨i⟩⟩
    rcases j with ⟨⟨j⟩⟩
    induction i using Fin.cases <;> induction j using Fin.cases
    all_goals simp only [eqToHom_refl, Category.comp_id]
    case zero.zero =>
      change (SemiCartesianMonoidalCategory.toUnit _ ≫ eId SSet x) ≫ R.map x x = _
      rw [Category.assoc, R.map_id x]
      rfl
    case zero.succ j =>
      change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentCoefficient τ j ≫ R.map x (F.obj (σ.obj j)) = _
      exact (weightedCoherentCoefficient_functorImage (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedHomFunctorImage F R x) τ j).symm
    case succ.zero i =>
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro P
      have h := SimplicialThickening.Path.le (P.obj 0)
      change i.succ ≤ 0 at h
      simp at h
    case succ.succ i j =>
      apply SSet.hom_ext
      rintro ⟨⟨d⟩⟩
      apply ConcreteCategory.hom_ext
      intro P
      change (R.map (F.obj (σ.obj i)) (F.obj (σ.obj j))).app (Opposite.op ⦋d⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' _ _
          ((σ ⋙ F).map (homOfLE _))) d) = _
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map]
      exact congrArg (fun z => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant z d)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor_vertex R ((σ ⋙ F).map
          (homOfLE (Fin.succ_le_succ_iff.mp
            (show i.succ ≤ j.succ from
              SimplicialThickening.Path.le (J := ULift.{u} (Fin (n + 2))) (P.obj 0)))))).symm

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
