module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversePinchedHom
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniverseMorphismDown
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulCalculus
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniverseKan

/-!
概要：元の全写像空間の充満忠実性の宇宙降下。
方針：元の pinched Hom の厳密同型を相殺し、同じホモトピー逆を降ろす。
規約：両端は quasicategory。既存の F1 の深層モジュールは変更しない。
使われ方：局所化の普遍性の充満忠実性の成分を元の宇宙で回収する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

/-- 厳密な同型は同じ厳密逆による単体的ホモトピー同値である。 -/
lemma homotopyEquivalence_of_iso {X Y : SSet.{u}} (e : X ≅ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence e.hom := by
  refine ⟨e.inv, ?_, ?_⟩
  · rw [e.hom_inv_id]
    exact ⟨SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm _)⟩
  · rw [e.inv_hom_id]
    exact ⟨SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm _)⟩

/-- 同じ元の射の全 pinched Hom 作用のホモトピー逆を元の宇宙へ戻す。 -/
lemma fullyFaithful_of_ulift {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] {f : X ⟶ Y}
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((SSet.uliftFunctor.{v, u}).map f)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f := by
  intro x y
  have hh := homotopyEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.uliftPinchedHomIso.{u, v} x y)
  have hc := hh.comp (h (ULift.up x) (ULift.up y))
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.uliftPinchedHomIso_naturality] at hc
  have hj := homotopyEquivalence_of_iso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.uliftPinchedHomIso.{u, v} (f.app (Opposite.op ⦋0⦌) x)
      (f.app (Opposite.op ⦋0⦌) y))
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsSimplicialHomotopyEquivalence.of_ulift (hj.cancel_right hc)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
