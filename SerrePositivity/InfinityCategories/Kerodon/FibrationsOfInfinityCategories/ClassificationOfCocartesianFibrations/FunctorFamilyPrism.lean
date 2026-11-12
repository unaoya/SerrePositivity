module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FunctorFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.HomotopyBoundaryExtension

/-!
概要：関手単体集合の族・辺・三角形を、パラメーターを左因子とする prism に変換する。
方針：uncurry の後で対称子を使い、制限の自然性から辺と三角形の計算を得る。
規約：標的の充填性は不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な図式の関手空間と unstraightening の変換の接続。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：関手空間への族を、パラメーターを左因子に置いた評価の族にする。
方針：テンソルの対称子の後で uncurry する。
規約：パラメーター K と関手の定義域 B は任意。
使われ方：Kerodon §5.6（Tag 027M）、coherent な変換と三角形の prism 表示。 -/
def functorFamilyPrism {K B X : SSet.{u}} (q : K ⟶ (ihom B).obj X) : K ⊗ B ⟶ X :=
  (β_ K B).hom ≫ uncurry q

/-- 概要：関手空間の族の prism はパラメーターの制限と可換。
方針：対称子の自然性と uncurry の自然性を使う。
規約：制限する射 i は任意。
使われ方：Kerodon §5.6（Tag 027M）、三角形の辺への制限の整合性。 -/
lemma functorFamilyPrism_restrict {K L B X : SSet.{u}}
    (q : K ⟶ (ihom B).obj X) (i : L ⟶ K) :
    (i ▷ B) ≫ functorFamilyPrism q = functorFamilyPrism (i ≫ q) := by
  rw [functorFamilyPrism, functorFamilyPrism, ← Category.assoc, BraidedCategory.braiding_naturality_left,
    Category.assoc, ← uncurry_natural_left]

/-- 概要：二つの関手を結ぶ関手空間の辺を prism にする。
方針：辺の Yoneda 射をパラメーター付き評価へ移す。
規約：区間を左因子に置く。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、unstraightening の変換の入力。 -/
def functorEdgePrism {B X : SSet.{u}} {F G : B ⟶ X}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom B).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) : (Δ[1] : SSet.{u}) ⊗ B ⟶ X :=
  functorFamilyPrism (SSet.yonedaEquiv.symm e.edge)

/-- 概要：関手空間の辺の prism の始点は元の始域側の関手。
方針：対称子による端点の変換と辺のホモトピー表示を使う。
規約：辺の始点条件は functorVertex で与える。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、変換の始点の固定。 -/
lemma functorEdgePrism_zero {B X : SSet.{u}} {F G : B ⟶ X}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom B).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ functorEdgePrism e = F := by
  rw [functorEdgePrism, functorFamilyPrism, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_zero_braiding]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e).h₀

/-- 概要：関手空間の辺の prism の終点は元の標的側の関手。
方針：対称子による端点の変換と辺のホモトピー表示を使う。
規約：辺の終点条件は functorVertex で与える。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、変換の終点の固定。 -/
lemma functorEdgePrism_one {B X : SSet.{u}} {F G : B ⟶ X}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom B).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ≫ functorEdgePrism e = G := by
  rw [functorEdgePrism, functorFamilyPrism, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_one_braiding]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e).h₁

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
