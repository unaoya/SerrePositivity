module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.RoofCompositionFaces
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
/-!
概要：任意パラメータの指定二ホモトピーを、実合成三角形ごと合成する。
方針：関手圏の Hom の合成を実三角形で表し、その対角を実ホモトピーへ戻す。
規約：二入力の全時刻を保持する。使われ方：指定商評価から実 AW 合成への比較。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
/-- 任意パラメータの指定二ホモトピーに、二外面を保持する実合成三角形が存在する。 -/
lemma roofHomotopyComposition_exists {K X : SSet.{u}} [Quasicategory X]
    {U V W : K ⟶ X} (l : SSet.Homotopy U V) (r : SSet.Homotopy V W) :
    ∃ d : SSet.Homotopy U W, Nonempty (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d) := by
  let e₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l
  let e₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r
  obtain ⟨k, hk⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective (X := (ihom K).obj X) _ _
    (Truncated.HomotopyCategory.homMk e₀ ≫ Truncated.HomotopyCategory.homMk e₁)
  obtain ⟨t⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac hk.symm
  have h₀ : stdSimplex.δ (0 : Fin 3) ≫ SSet.yonedaEquiv.symm t.simplex = curry r.h := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp]
    exact (congrArg (((ihom K).obj X).δ 0)
      (SSet.yonedaEquiv.apply_symm_apply t.simplex)).trans t.d₀
  have h₂ : stdSimplex.δ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm t.simplex = curry l.h := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp]
    exact (congrArg (((ihom K).obj X).δ 2)
      (SSet.yonedaEquiv.apply_symm_apply t.simplex)).trans t.d₂
  obtain ⟨d, T, _⟩ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.roofCompositionTriangle_of_outerFaces l r
    (SSet.yonedaEquiv.symm t.simplex) h₀ h₂
  exact ⟨d, ⟨T⟩⟩
end SerrePositivity.InfinityCategories.Project.DerivedCategories
