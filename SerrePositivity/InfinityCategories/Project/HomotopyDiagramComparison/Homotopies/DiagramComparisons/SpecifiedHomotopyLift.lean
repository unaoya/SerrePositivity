module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.PrismEndpointPairPullback
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TrivialFibrationHomotopy

/-!
概要：指定した底の全ホモトピーを、上の二つの端面を厳密に保って持ち上げる。
方針：円柱の両端の和の単射に、自明 Kan fibration の右持ち上げ性を使う。
規約：底の円柱の raw な射を保持する。使われ方：右長辺上の相対 coslice 族の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 自明 Kan fibration は、指定した底の円柱を指定した二つの端面の間に持ち上げる。 -/
lemma exists_specifiedHomotopyLift {A E B : SSet.{u}} (p : E ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] (f g : A ⟶ E) (H : SSet.Homotopy (f ≫ p) (g ≫ p)) :
    ∃ K : SSet.Homotopy f g, K.h ≫ p = H.h := by
  let b := (β_ (Δ[1] : SSet.{u}) A).hom ≫ H.h
  have hb₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ b = f ≫ p := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_zero_braiding]
    exact H.h₀
  have hb₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ b = g ≫ p := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_one_braiding]
    exact H.h₁
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := p) (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismEndpointPair A) inferInstance
  have sq : CommSq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc f g) (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismEndpointPair A) p b := by
    constructor
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    cases x with
    | inl x => exact ConcreteCategory.congr_hom (NatTrans.congr_app hb₀.symm n) x
    | inr x => exact ConcreteCategory.congr_hom (NatTrans.congr_app hb₁.symm n) x
  have h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ sq.lift = f := by
    have h := congrArg (fun k ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl A A ≫ k) sq.fac_left
    exact h
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ sq.lift = g := by
    have h := congrArg (fun k ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr A A ≫ k) sq.fac_left
    exact h
  let K : SSet.Homotopy f g :=
    { h := (β_ A (Δ[1] : SSet.{u})).hom ≫ sq.lift
      h₀ := by
        rw [← Category.assoc]
        exact h₀
      h₁ := by
        rw [← Category.assoc]
        exact h₁
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro x
        exact False.elim x.1.property }
  refine ⟨K, ?_⟩
  change ((β_ A (Δ[1] : SSet.{u})).hom ≫ sq.lift) ≫ p = H.h
  rw [Category.assoc, sq.fac_right]
  change (β_ A (Δ[1] : SSet.{u})).hom ≫
    ((β_ (Δ[1] : SSet.{u}) A).hom ≫ H.h) = H.h
  rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
