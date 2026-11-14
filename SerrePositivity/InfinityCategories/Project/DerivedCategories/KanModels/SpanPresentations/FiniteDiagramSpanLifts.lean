module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.FiniteHomotopyRelativeFillers
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.FiniteMappingCylinder
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SpanHomotopyGluing
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-! # 一般有限図式のホモトピー部分持ち上げ

概要：有限射の厳密比較正方形を、終域の持ち上げと指定始域への比較の span へ変える。
方針：始域を写像円柱の単射へ置き換えて有限対充填を適用し、円柱の二端を読む。
規約：元の射の単射性を要求しない。使われ方：Kan 置換後の有限相対切断。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits SSet
open scoped _root_.Simplicial

/-- 一般の有限比較図式を持ち上げると、指定始域へ向かう二つの比較を同じ始点で得る。 -/
lemma HasFiniteHomotopyRelativeFillers.finiteDiagramSpanLift
    {E Q : SSet.{u}} {F : E ⟶ Q} (hF : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.HasFiniteHomotopyRelativeFillers F)
    {A B : SSet.{u}} [A.Finite] [B.Finite] (j : A ⟶ B) (a : A ⟶ E) (b : B ⟶ Q)
    (ha : a ≫ F = j ≫ b) :
    ∃ t : B ⟶ E, Nonempty (SSet.Homotopy (t ≫ F) b) ∧
      ∃ u : A ⟶ E, Nonempty (SSet.Homotopy u a) ∧ Nonempty (SSet.Homotopy u (j ≫ t)) := by
  have hw : a ≫ F = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinderSource j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection j ≫ b := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinderSource_projection]
    exact ha
  obtain ⟨R⟩ := hF (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinderSource j) a (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection j ≫ b) hw
  let t := pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A) j ≫ R.filler
  let u := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinderSource j ≫ R.filler
  refine ⟨t, ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp R.comparison
    (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A) j)) ?_ ?_⟩, u, ⟨R.boundary⟩,
      ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinderHomotopy j) R.filler) rfl ?_⟩⟩
  · exact (Category.assoc _ _ _).symm
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection_inr, Category.id_comp]
  · exact Category.assoc _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
