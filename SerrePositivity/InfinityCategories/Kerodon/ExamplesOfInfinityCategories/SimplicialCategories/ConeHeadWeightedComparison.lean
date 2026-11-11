module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.ConeHeadSimplex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedConeSimplex

/-!
概要：head と正頂点間の Hom の厳密な式から、元の weighted cone を回収する。
方針：対象表示を移し、Hom の四分岐で比較する。
規約：tail の初点には条件を課さず、正頂点側だけを使う。
使われ方：左切断 prism の時刻零・一の厳密な端点計算。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories


/-- head と tail の元の係数表示は、構成した cone 全体を元の weighted cone と同定する。 -/
lemma coherentConeSimplexOfHead_eq_weighted {I : Type u} [SmallCategory I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : I ⥤ C) (x : C) {n : ℕ} (σ : (nerve I) _⦋n⦌)
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor)
    (T : (SimplicialNerve C) _⦋n + 1⦌) (H : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CoherentConeHead x T)
    (e : ∀ j : Fin (n + 1), T.obj ⟨ULift.up j.succ⟩ = F.obj (σ.obj j))
    (hh : ∀ j, H.hom j ≫ eqToHom (congrArg (SimplicialCategory.sHom x) (e j)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentCoefficient τ j)
    (ht : ∀ i j, i ≤ j → T.map ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom (e i) (e j)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeTailHom (σ ⋙ F) i j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentConeSimplexOfHead x T H = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeSimplex F x τ := by
  refine EnrichedFunctor.ext SSet (fun i => ?_) (fun i j => ?_)
  · rcases i with ⟨⟨i⟩⟩
    induction i using Fin.cases with
    | zero => rfl
    | succ i => exact e i
  · rcases i with ⟨⟨i⟩⟩
    rcases j with ⟨⟨j⟩⟩
    induction i using Fin.cases <;> induction j using Fin.cases
    case zero.zero =>
      simp only [eqToHom_refl, Category.comp_id]
      rfl
    case zero.succ j => exact hh j
    case succ.zero i =>
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro P
      have h := Path.le (P.obj 0)
      change i.succ ≤ 0 at h
      simp at h
    case succ.succ i j =>
      by_cases hij : i ≤ j
      · exact ht i j hij
      · apply SSet.hom_ext
        intro d
        apply ConcreteCategory.hom_ext
        intro P
        exact False.elim (hij (Fin.succ_le_succ_iff.mp
          (Path.le (J := ULift.{u} (Fin (n + 2))) (P.obj 0))))

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
