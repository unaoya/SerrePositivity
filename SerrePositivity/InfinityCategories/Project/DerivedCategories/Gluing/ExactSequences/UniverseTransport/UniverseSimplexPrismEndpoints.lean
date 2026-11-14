module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.UniverseTransport.UniverseSimplexPrismFamilies
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.UniverseTransport.UniverseSimplexFamilies
/-! # 標準単体 prism の宇宙輸送と二射影

概要：全 prism の宇宙輸送が、両端の標準単体族を厳密に保持する。
方針：標準単体同型と積同型の全単体上の値を比較する。
規約：端点ごとの代表を選び直さず、元の全入力を保持する。
使われ方：正規化四面体の始側・終側射影を native 導来四面体へ輸送する。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
lemma dgGluingUliftSimplexPrismFamily_endpoint {K X : SSet.{u}} (n : ℕ)
    (V : (Δ[1] : SSet.{u}) ⊗ (Δ[n] ⊗ K) ⟶ X) (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i (Δ[n] ⊗ (SSet.uliftFunctor.{v, u}).obj K) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexPrismFamily.{u,v} n V =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily.{u,v} n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i (Δ[n] ⊗ K) ≫ V) := by
  apply SSet.hom_ext
  intro m
  apply ConcreteCategory.hom_ext
  intro p
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
