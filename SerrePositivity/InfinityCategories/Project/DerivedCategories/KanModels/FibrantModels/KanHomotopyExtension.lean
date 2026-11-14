module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalencePathLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.OuterHornConverse

/-! # 指定ホモトピーの Kan 標的への延長

概要：単射上のホモトピーを、既存の始点写像とともに全体へ延長する。
方針：Kan 標的では全辺が可逆なので、可逆 prism の厳密延長を適用する。
規約：始点と部分図式の全時刻を厳密に保つ。使われ方：相対骨格の商写像の更新。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

/-- Kan 標的の指定部分ホモトピーは、始点を固定したまま全体へ延長できる。 -/
lemma kanHomotopyExtension_exists {L K Y : SSet.{u}} [KanComplex Y]
    (i : L ⟶ K) [Mono i] (g : K ⟶ Y) (f : L ⟶ Y)
    (H : SSet.Homotopy (i ≫ g) f) :
    ∃ g' : K ⟶ Y, ∃ H' : SSet.Homotopy g g',
      i ≫ g' = f ∧ (i ▷ (Δ[1] : SSet.{u})) ≫ H'.h = H.h := by
  let h := (β_ (Δ[1] : SSet.{u}) L).hom ≫ H.h
  have h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 L ≫ h = i ≫ g := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_zero_braiding]
    exact H.h₀
  have hv : ∀ x : L _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
      (h.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1))) := by
    intro x
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.isInvertibleEdge_of_hasFinalHornFillers _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasFinalHornFillers_of_kanComplex _)
  obtain ⟨F, hF, hF₀, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.equivalenceHomotopy_extend i h g h₀ hv
  let g' := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ F
  let H' : SSet.Homotopy g g' := {
    h := (β_ K (Δ[1] : SSet.{u})).hom ≫ F
    h₀ := by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ F = g
      exact hF₀
    h₁ := by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ F = g'
      rfl
    rel := by
      ext n s
      exact False.elim s.1.property }
  refine ⟨g', H', ?_, ?_⟩
  · change i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ F = f
    rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, hF]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 L ≫ (β_ Δ[1] L).hom ≫ H.h = f
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_one_braiding]
    exact H.h₁
  · change (i ▷ Δ[1]) ≫ (β_ K Δ[1]).hom ≫ F = H.h
    rw [← Category.assoc, BraidedCategory.braiding_naturality_left, Category.assoc, hF]
    dsimp [h]
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
