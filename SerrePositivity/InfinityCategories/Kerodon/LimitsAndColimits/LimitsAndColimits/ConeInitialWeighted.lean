module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeInitialReindex
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedConePrecomposition

/-!
概要：任意の coherent simplex の始点の取り替えを、既存の weighted cone の前合成と同定する。
方針：各 Hom の分岐を比較し、head で既証の係数の豊穣合成公式を使う。
規約：単体全体の厳密な等式。元の図式上の制限の同定に用いる。
使われ方：HTT 4.2.4.1 の錐全体上の族から元の図式への制限の検証。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C]

/-- weighted cone での始点の取り替えは既存の全 Hom パラメータの前合成そのもの。 -/
lemma coneInitialSimplex_weighted (F : I ⥤ C) (x z : C) {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F z ⋙ SSet.opFunctor)) _⦋n⦌)
    (a : (SimplicialCategory.sHom x z).op _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneInitialSimplex x (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeSimplex F z s.2) (SSet.yonedaEquiv.symm a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeSimplex F x
        ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedConePrecompositionMap F x z).app (Opposite.op ⦋n⦌) (s, a)).2 := by
  refine EnrichedFunctor.ext SSet (fun i ↦ ?_) (fun i j ↦ ?_)
  · rcases i with ⟨⟨i⟩⟩
    induction i using Fin.cases <;> rfl
  · rcases i with ⟨⟨i⟩⟩
    rcases j with ⟨⟨j⟩⟩
    induction i using Fin.cases <;> induction j using Fin.cases
    all_goals simp only [eqToHom_refl, Category.comp_id]
    case zero.zero => rfl
    case zero.succ j =>
      change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneInitialHead x (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeSimplex F z s.2) (SSet.yonedaEquiv.symm a) j =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentCoefficient
          ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedConePrecompositionMap F x z).app (Opposite.op ⦋n⦌) (s, a)).2 j
      rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedCoherentCoefficient_precomposition]
      rfl
    case succ.zero i => rfl
    case succ.succ i j => rfl

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
