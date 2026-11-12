module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.BousfieldKanConePointSection
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentConeSourceWeightedRestriction

/-!
概要：Kan coend の錐全体上の明示的な Hom の族を、既存の coend 比較と同定する。
方針：普遍点の weighted な切断と前合成の一致へ還元し、全パラメータの評価を計算する。
規約：同じ始域と終域を持つ同値性だけでなく、比較射そのものを照合する。
使われ方：HTT 4.2.4.1 の余極限性の制限条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {I : Type u} [SmallCategory I]

/-- 錐全体上の明示的な族の制限は、Kan coend の既存の反転 Hom 比較に一致する。 -/
lemma bousfieldKanCoherentConeSourceFamily_restrict (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    (Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentConeSourceFamily (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentOppositeCone F)
        (Opposite.op (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F))
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentOppositeCone_vertex F) (Opposite.op Y) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneSectionRestriction (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentOppositeCone F)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op Y)) = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentConeComparison F Y := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op Y))))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F.op)
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentConeSourceFamily_restriction_weighted F.op _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanConeWeightedPointSection F)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentOppositeCone_cosliceSection_weighted F)]
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentConeComparison_uncurry]
  simp only [← Category.assoc]
  congr 1
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, s⟩
  change (ULift.up
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeightedNerveEvaluation
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.op
          (Opposite.op (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F)) ⋙ SSet.opFunctor)).app
            (Opposite.op ⦋n⦌)
              (((inv (fst _ (Δ[0] : SSet.{u + 1}))).app
                (Opposite.op ⦋n⦌) σ).1.down, ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanLiftedEndPoint F).app (Opposite.op ⦋n⦌)
                ((inv (fst _ (Δ[0] : SSet.{u + 1}))).app (Opposite.op ⦋n⦌) σ).2).down)),
        s) =
    (ULift.up
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeightedNerveEvaluation
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.op
          (Opposite.op (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F)) ⋙ SSet.opFunctor)).app
            (Opposite.op ⦋n⦌)
              (σ.down, (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitHomPoint F).app
                (Opposite.op ⦋n⦌) PUnit.unit)), s)
  have hf := ConcreteCategory.congr_hom
    (NatTrans.congr_app (IsIso.inv_hom_id
      (fst ((SSet.uliftFunctor.{u + 1, u}).obj (nerve Iᵒᵖ))
        (Δ[0] : SSet.{u + 1}))) (Opposite.op ⦋n⦌)) σ
  change ((inv (fst _ (Δ[0] : SSet.{u + 1}))).app (Opposite.op ⦋n⦌) σ).1 = σ at hf
  rw [hf]
  congr 3
  simp only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanLiftedEndPoint, SSet.yonedaEquiv_symm_zero]
  congr 1
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitHomPoint F).app (Opposite.op ⦋0⦌) PUnit.unit) n =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitHomPoint F).app (Opposite.op ⦋n⦌) PUnit.unit
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.unitHom_app_constant (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitHomPoint F) n).symm

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
