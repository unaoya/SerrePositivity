module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleKappaCompactClassicalTransport
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FilteredRetraction

/-!
概要：元の κ-compact 頂点を、指定した native κ-filtered 表示の同じ一段の retract にする。
方針：全共変 Hom による恒等点の因子化を元の余錐に適用する。
規約：native 余錐の普遍性は明示引数。cell 表示の存在はこの補題の結論に含めない。
使われ方：D-8 d の compact 性から段階への還元。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
open CategoryTheory DifferentialGraded SSet
open _root_.SerrePositivity.KST.NonConnective
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}}

/-- D-bar から受け取る native 余極限性を使い、同じ cell 段の retract を得る。 -/
lemma dgKappaCompact_retract_of_nativeCellPresentation
    {J : SSet.{u}} [Quasicategory J] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ J]
    (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj J ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (M : J _⦋0⦌ → _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D)
    (hM : ∀ i, F.app (Opposite.op ⦋0⦌) (ULift.up i) = dgConeModuleDerivedVertex R D (M i))
    {y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) _⦋0⦌}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso c.vertex y) (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, max (u + 1) v} κ y) :
    ∃ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf y (dgConeModuleDerivedVertex R D (M i)) := by
  have hcpt := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_iff_of_iso e).mpr hy
  obtain ⟨i, hi⟩ := hcpt.retract_of_colimit F c hc
  rw [hM i] at hi
  exact ⟨i, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf.of_iso e.symm).trans hi⟩

/-- 主導来像も、上と同じ一段の retract である。 -/
lemma dgKappaCompact_classicalRetract_of_nativeCellPresentation
    {J : SSet.{u}} [Quasicategory J] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ J]
    (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj J ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (M : J _⦋0⦌ → _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D)
    (hM : ∀ i, F.app (Opposite.op ⦋0⦌) (ULift.up i) = dgConeModuleDerivedVertex R D (M i))
    {y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) _⦋0⦌}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso c.vertex y) (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, max (u + 1) v} κ y) :
    ∃ i, Nonempty (Retract
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedHoComparison R D).obj (HomotopyCategory.mk y))
      ((_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).obj (M i))) := by
  obtain ⟨i, ⟨r⟩⟩ := dgKappaCompact_retract_of_nativeCellPresentation R D F c hc M hM e hy
  exact ⟨i, ⟨(r.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedHoComparison R D)).trans
    (Retract.ofIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgConeModuleDerivedVertex_classicalIso R D (M i)))⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
