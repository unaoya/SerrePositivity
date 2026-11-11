module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorFamilyPrism
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence

/-!
概要：端点を指定した prism から関手空間の実際の辺を厳密に回収する。
方針：対称子で区間を右因子に移し単体的ホモトピーの辺表示を使う。
規約：標的の充填性は不要。
使われ方：collage から復元した変換を既存の写像空間比較へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 概要：端点を指定した prism の関手空間の辺。
方針：区間を右に移した単体的ホモトピーから辺を作る。
規約：同値類への選択を挟まない。
使われ方：復元した coherent な変換の写像空間の頂点表示。 -/
def functorEdgeFromPrism {B X : SSet.{u}} {F G : B ⟶ X}
    (H : (Δ[1] : SSet.{u}) ⊗ B ⟶ X)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ H = F) (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ≫ H = G) :
    SSet.Truncated.Edge (X := (truncation 2).obj ((ihom B).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (f := F) (g := G)
    { h := (β_ B (Δ[1] : SSet.{u})).hom ≫ H
      h₀ := by
        change SSet.ι₀ ≫ ((β_ B (Δ[1] : SSet.{u})).hom ≫ H) = F
        rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_zero_braiding B]
        simpa only [Category.assoc, SymmetricCategory.symmetry_assoc] using h₀
      h₁ := by
        change SSet.ι₁ ≫ ((β_ B (Δ[1] : SSet.{u})).hom ≫ H) = G
        rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_one_braiding B]
        simpa only [Category.assoc, SymmetricCategory.symmetry_assoc] using h₁
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro x
        exact False.elim x.1.property }

/-- 概要：prism から回収した辺の prism は元の射と一致する。
方針：Yoneda、curry と uncurry、対称子の往復を消去する。
規約：射の厳密な等式。
使われ方：写像空間比較の既存の辺での公式へ戻す。 -/
lemma functorEdgeFromPrism_prism {B X : SSet.{u}} {F G : B ⟶ X}
    (H : (Δ[1] : SSet.{u}) ⊗ B ⟶ X)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ H = F) (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ≫ H = G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgePrism (functorEdgeFromPrism H h₀ h₁) = H := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgePrism, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorFamilyPrism, functorEdgeFromPrism,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy, Equiv.symm_apply_apply, uncurry_curry]
  simp

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
