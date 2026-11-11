module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.VerdierRelativeConeRecovery

/-!
概要：パラメータ形状の同型に沿って、元の境界を固定する商錐回収を移す。
方針：同じ実図式と実比較円柱を積の同型で前合成し、厳密な両側逆を使う。
規約：比較を同型類で選び直さず、元の全境界を保持する。
使われ方：c5 の左錐の帰納から標準単体の各次数への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.LocalizingInvariants

/-- パラメータの同型は、元の有限境界を全時刻固定する商錐回収を保つ。 -/
lemma hasVerdierRelativeConeRecovery_of_iso {X Y S T : SSet.{u}} (q : X ⟶ Y)
    (e : S ≅ T) (hs : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.HasVerdierRelativeConeRecovery q S) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.HasVerdierRelativeConeRecovery q T := by
  intro K _ p H hb
  let j := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) K
  let pS := (K ◁ e.hom) ≫ p
  let HS := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K ◁ e.hom) ≫ H
  have hbS : (j ▷ S) ≫ HS = pS ≫ q := by
    change (j ▷ S) ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K ◁ e.hom) ≫ H) = _
    rw [← Category.assoc, ← whisker_exchange, Category.assoc, hb]
    rfl
  obtain ⟨d⟩ := hs K pS HS hbS
  let D := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K ◁ e.inv) ≫ d.diagram
  let V : SSet.Homotopy (D ≫ q) H := {
    h := ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K ◁ e.inv) ▷ (Δ[1] : SSet.{u})) ≫ d.comparison.h
    h₀ := by rw [SSet.ι₀_comp_assoc, d.comparison.h₀]; rfl
    h₁ := by
      rw [SSet.ι₁_comp_assoc, d.comparison.h₁]
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K ◁ e.inv) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K ◁ e.hom) ≫ H = H
      rw [← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id, Category.id_comp]
    rel := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp d.comparison
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K ◁ e.inv)).rel }
  refine ⟨⟨D, ?_, V, ?_, ?_⟩⟩
  · change (j ▷ T) ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K ◁ e.inv) ≫ d.diagram) = p
    rw [← Category.assoc, ← whisker_exchange, Category.assoc, d.boundary]
    change (K ◁ e.inv) ≫ (K ◁ e.hom) ≫ p = p
    rw [← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id, Category.id_comp]
  · change ((j ▷ T) ▷ Δ[1]) ≫
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K ◁ e.inv) ▷ Δ[1]) ≫ d.comparison.h) = _
    rw [← comp_whiskerRight_assoc, ← whisker_exchange, comp_whiskerRight]
    simp only [Category.assoc]
    rw [d.fixed]
    have hp : ((K ◁ e.inv) ▷ (Δ[1] : SSet.{u})) ≫ fst (K ⊗ S) Δ[1] =
        fst (K ⊗ T) Δ[1] ≫ (K ◁ e.inv) := rfl
    rw [← Category.assoc, hp, Category.assoc]
    change fst _ Δ[1] ≫ (K ◁ e.inv) ≫ (K ◁ e.hom) ≫ p ≫ q = _
    rw [← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id, Category.id_comp]
  · intro x
    have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge V x).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp d.comparison
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K ◁ e.inv)) x).edge := rfl
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.simplicialHomotopyVertexEdge_precomp_edge d.comparison
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K ◁ e.inv) x)).mpr (d.invertible _)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.hasVerdierRelativeConeRecovery_of_iso := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.hasVerdierRelativeConeRecovery_of_iso
