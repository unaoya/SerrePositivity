module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceSourcePrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.WeightedConstantSimplex

/-!
概要：定値の coherent simplex への始点置換は、標準の反転 Hom の simplex を与える。
方針：豊穣合成の右単位則で初点の Hom を簡約し、weighted な定値係数と照合する。
規約：局所 Kan 性を仮定せず、全次数の simplex そのものの等式を示す。
使われ方：錐全体上の明示的な Hom の族の頂点評価の計算。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 定値の coherent simplex の始点置換は、定値図式の weighted cone simplex に一致する。 -/
lemma coneInitialSimplex_constant (x z : C) {n : ℕ}
    (s : (SimplicialCategory.sHom x z).op _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneInitialSimplex x (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex z) (n + 1))
        (SSet.yonedaEquiv.symm s) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeSimplex ((Functor.const (Discrete PUnit.{u + 1})).obj z) x
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantDiagram
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram ((Functor.const (Discrete PUnit.{u + 1})).obj z) x ⋙
            SSet.opFunctor) ⟨PUnit.unit⟩ s) := by
  refine EnrichedFunctor.ext SSet (fun a ↦ ?_) (fun a b ↦ ?_)
  · rcases a with ⟨⟨a⟩⟩
    induction a using Fin.cases <;> rfl
  · rcases a with ⟨⟨a⟩⟩
    rcases b with ⟨⟨b⟩⟩
    induction a using Fin.cases <;> induction b using Fin.cases
    all_goals simp only [eqToHom_refl, Category.comp_id]
    case zero.zero => rfl
    case zero.succ b =>
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro P
      change (eComp SSet x z z).app d
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pathFirstParameterMap b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap (SSet.yonedaEquiv.symm s)).app d P,
          (eId SSet z).app d PUnit.unit) = _
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_comp_id_app]
      rfl
    case succ.zero a => rfl
    case succ.succ a b =>
      apply SSet.hom_ext
      rintro ⟨⟨d⟩⟩
      apply ConcreteCategory.hom_ext
      intro P
      change (eId SSet z).app (Opposite.op ⦋d⦌) PUnit.unit =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' z z (𝟙 z)) d
      simp only [SimplicialCategory.homEquiv', Equiv.trans_apply, eHomEquiv_id]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.unitHom_app_constant (eId SSet z) d

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
