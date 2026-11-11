module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedAugmentationRawFactorHom
/-!
概要：元の分解関手上の通常後続 augmentation を、合成子計算と同じ端点のホモトピーで表す。
方針：同じ円柱射を保って nerve の合成式で端点を揃える。
規約：別の代表ホモトピーを選ばない。使われ方：指定合成子の射と通常 tensor の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E K : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] [_root_.SerrePositivity.DifferentialGraded.DGCategory R K] [Small.{u} K]
  (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
  (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R (_root_.SerrePositivity.DifferentialGraded.RightModule R E) (_root_.SerrePositivity.DifferentialGraded.RightModule R K))
/-- 通常合成の端点で表した、同じ実 augmentation の通常後続ホモトピー。 -/
def dgModuleResolvedAugmentationRawHomotopy :
    SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R C E F ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((dgFullSubcategoryInclusion R (RightModule R E)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E)).comp H) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (F.comp H) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K))) := by
  let A := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedAugmentationHomotopy R C E F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R K) K
      (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R K)))
  exact { h := A.h
          h₀ := A.h₀.trans (by simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, Category.assoc]; rfl)
          h₁ := A.h₁.trans (by simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, Category.assoc]; rfl)
          rel := A.rel }
/-- 指定された通常後続比較の射は、同じ型の元の実ホモトピーの類に厳密に等しい。 -/
lemma dgModuleResolvedAugmentationRawFactorIso_hom
    (hq : ∀ X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F,
      _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R K (H.onClosed.map X.augmentation)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedAugmentationRawFactorIso R C E K F H hq).hom =
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (dgModuleResolvedAugmentationRawHomotopy R C E K F H)) := by
  have h1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedAugmentationRawFactorIso_hom_heq R C E K F H hq
  have h2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomotopyHom_heq_of_raw_eq
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedAugmentationHomotopy R C E F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R K) K
        (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R K))))
    (dgModuleResolvedAugmentationRawHomotopy R C E K F H) rfl
  exact eq_of_heq (h1.trans h2)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
