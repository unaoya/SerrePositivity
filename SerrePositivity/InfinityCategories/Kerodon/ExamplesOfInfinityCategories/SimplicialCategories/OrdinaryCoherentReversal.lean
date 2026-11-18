module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.CoherentCoconeTransport
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderDiagrams

/-!
概要：通常の射列の coherent 表示の反転と帰還の法則。
方針：Mathlib の射列の反対同値と、既存の coherent 反転の対象・Hom を比較する。
規約：対象の宇宙と Hom の宇宙を分離し、全高次資料を保持する。
使われ方：HTT 4.2.4.1、Kerodon §4.6.7（Tag 01LA）、S8 の押し出しの三角形。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 通常の射列の coherent 表示を反転すると、同じ射列の反対の coherent 表示。
HTT 4.2.4.1、Kerodon §4.6.7（Tag 01LA）。全ての長さに対する反転則。 -/
lemma coherentOppositeSimplex_ordinary {n : ℕ} (A : ComposableArrows C n) :
    coherentOppositeSimplex ((nerveToCoherent C).app (Opposite.op ⦋n⦌) A) =
      (nerveToCoherent Cᵒᵖ).app (Opposite.op ⦋n⦌)
        ((ComposableArrows.opEquivalence C n).functor.obj (Opposite.op A)) := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro i j
  simp only [eqToHom_refl, Category.comp_id]

/-- 反対の通常の射列の coherent 表示を帰還させると、元の全単体になる。
HTT 4.2.4.1、Kerodon §4.6.7（Tag 01LA）。指定三角形の頂点や辺だけに弱めない。 -/
lemma coherentOppositeReturnIso_ordinary {n : ℕ} (A : ComposableArrows C n) :
    (coherentOppositeReturnIso C).hom.app (Opposite.op ⦋n⦌)
      (SSet.opObjEquiv.symm ((nerveToCoherent Cᵒᵖ).app (Opposite.op ⦋n⦌)
        ((ComposableArrows.opEquivalence C n).functor.obj (Opposite.op A)))) =
      (nerveToCoherent C).app (Opposite.op ⦋n⦌) A := by
  change (SSet.opFunctorCompOpFunctorIso.app (SimplicialNerve C)).hom.app (Opposite.op ⦋n⦌)
      ((SSet.opFunctor.map (coherentNerveOppositeIso C).inv).app (Opposite.op ⦋n⦌)
        (SSet.opObjEquiv.symm ((nerveToCoherent Cᵒᵖ).app (Opposite.op ⦋n⦌)
          ((ComposableArrows.opEquivalence C n).functor.obj (Opposite.op A))))) = _
  rw [SSet.opFunctor_map, Equiv.apply_symm_apply]
  change coherentOppositeInverseSimplex ((nerveToCoherent Cᵒᵖ).app (Opposite.op ⦋n⦌)
      ((ComposableArrows.opEquivalence C n).functor.obj (Opposite.op A))) = _
  rw [← coherentOppositeSimplex_ordinary]
  exact coherentOppositeInverseSimplex_opposite _

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
