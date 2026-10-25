module
public import SerrePositivity.InfinityCategories.Derived.DGModuleKappaCompactClassicalTransport
public import SerrePositivity.InfinityCategories.F2.Compact.FilteredRetraction

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet F2
open SerrePositivity.KST.NonConnective
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}}

/-- D-bar から受け取る native 余極限性を使い、同じ cell 段の retract を得る。 -/
lemma dgKappaCompact_retract_of_nativeCellPresentation
    {J : SSet.{u}} [Quasicategory J] [IsKappaFiltered κ J]
    (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj J ⟶ dgModuleDerivedInfinityCategory R D)
    (c : JoinCocone F) (hc : IsColimitCone c)
    (M : J _⦋0⦌ → ModuleCategory R D)
    (hM : ∀ i, F.app (Opposite.op ⦋0⦌) (ULift.up i) = dgConeModuleDerivedVertex R D (M i))
    {y : (dgModuleDerivedInfinityCategory R D) _⦋0⦌}
    (e : VertexIso c.vertex y) (hy : F2.Compact.IsKappaCompact.{u, max (u + 1) v} κ y) :
    ∃ i, F2.Idempotent.IsVertexRetractOf y (dgConeModuleDerivedVertex R D (M i)) := by
  have hcpt := (F2.Compact.isKappaCompact_iff_of_iso e).mpr hy
  obtain ⟨i, hi⟩ := hcpt.retract_of_colimit F c hc
  rw [hM i] at hi
  exact ⟨i, (F2.Idempotent.IsVertexRetractOf.of_iso e.symm).trans hi⟩

/-- 主導来像も、上と同じ一段の retract である。 -/
lemma dgKappaCompact_classicalRetract_of_nativeCellPresentation
    {J : SSet.{u}} [Quasicategory J] [IsKappaFiltered κ J]
    (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj J ⟶ dgModuleDerivedInfinityCategory R D)
    (c : JoinCocone F) (hc : IsColimitCone c)
    (M : J _⦋0⦌ → ModuleCategory R D)
    (hM : ∀ i, F.app (Opposite.op ⦋0⦌) (ULift.up i) = dgConeModuleDerivedVertex R D (M i))
    {y : (dgModuleDerivedInfinityCategory R D) _⦋0⦌}
    (e : VertexIso c.vertex y) (hy : F2.Compact.IsKappaCompact.{u, max (u + 1) v} κ y) :
    ∃ i, Nonempty (Retract
      ((dgModuleDerivedHoComparison R D).obj (HomotopyCategory.mk y))
      ((moduleToDerived R D).obj (M i))) := by
  obtain ⟨i, ⟨r⟩⟩ := dgKappaCompact_retract_of_nativeCellPresentation R D F c hc M hM e hy
  exact ⟨i, ⟨(r.map (dgModuleDerivedHoComparison R D)).trans
    (Retract.ofIso (dgConeModuleDerivedVertex_classicalIso R D (M i)))⟩⟩

end SerrePositivity.InfinityCategories
