module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.PosetLowerRestrictionCofinality
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndConeTargetEvaluationCofinality

/-!
概要：元の有限半順序全図式の任意の指定点で、実表示 comma の評価は right cofinal。
方針：指定点の弱下方部分へ制限し、元の厳密下方余錐の極大点評価を接続する。
規約：元の全評価写像と元の指定点を保持する。
使われ方：有限半順序形状の同じ標準全余錐の余極限性。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
/-- 概要：元の有限半順序図式の各指定点評価自身は right cofinal。
方針：弱下方制限と余錐極大点評価を合成する。
規約：元の全評価。使われ方：同じ全図式の単一 filtered 表示。 -/
lemma diagramCommaEvaluation_finitePoset_isRightCofinal (κ : Cardinal.{u}) [Fact κ.IsRegular]
    {P : Type u} [PartialOrder P] [Finite P] {C : SSet.{u}} [Quasicategory C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve P) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)
    (k : (nerve P) _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaEvaluation κ D k) := by
  let p := nerveEquiv k
  let U : Set P := Set.Iic p
  let r := nerveMap (OrderHom.Subtype.val U).toFunctor
  let L := nerve {x : P // x < p}
  let s := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.posetLowerJoinIso p).hom
  let D₁ := (SSet.uliftFunctor.{u + 1, u}).map r ≫ D
  let D₂ := (SSet.uliftFunctor.{u + 1, u}).map s ≫ D₁
  have hR₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D r) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction_poset_lowerSet_isRightCofinal κ U
      (by intro x y hxy hy; exact le_trans hxy hy) D
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction_isIso κ D₁ s
  have hR₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_isIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D₁ s)
  have hLower : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.smallDiagramComma κ
      ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L (Δ[0] : SSet.{u})) ≫ D₂)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.smallFinitePosetDiagramComma_isKappaFiltered κ _
  have hE := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaEvaluation_cone_apex_isRightCofinal κ D₂
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_of_finite (Fact.out : κ.IsRegular).aleph0_le L) hLower
  have h := hR₁.comp (hR₂.comp hE)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D r ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D₁ s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaEvaluation κ D₂ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneApex L)) at h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction_evaluate, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction_evaluate] at h
  have hk : r.app (Opposite.op ⦋0⦌) (s.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneApex L)) = k := by
    have hpoint := congrArg (fun f : (Δ[0] : SSet.{u}) ⟶ nerve {x : P // x ≤ p} ↦
      f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.posetLowerJoinIso_inr p)
    change s.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneApex L) = _ at hpoint
    rw [hpoint]
    apply nerveEquiv.injective
    rfl
  exact Eq.mp (congrArg (fun v ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaEvaluation κ D v)) hk) h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
