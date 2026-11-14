module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveUniverseMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGFunctors.DGFunctorFullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InnerFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceCalculus

/-! # 共通宇宙での dg 関手の nerve の充満忠実性

概要：対象宇宙が異なっても Hom 複体同型な dg 関手は実写像空間で充満忠実。
方針：対象を上げた同一宇宙の dg 関手へ分解し、両端の実同型で輸送する。
規約：h の充満忠実性だけでは判定しない。使われ方：dg Yoneda の全加群 nerve への比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} {E : Type w}
variable [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E]

/-- 共通宇宙での nerve は対象を上げた dg 関手と両端の実同型へ分解できる。 -/
lemma dgNerveUniverseMap_factor (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseMap F = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseLiftIso.{u, v, w} A D).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, v, w, w, v} F) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseLiftIso.{u, w, v} A E).inv := by
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseMap F ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseLiftIso.{u, w, v} A E).hom) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseLiftIso.{u, w, v} A E).inv := by
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = _ := by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseMap_lift, Category.assoc]

/-- Hom 複体同型な dg 関手の共通宇宙での nerve は充満忠実。 -/
lemma dgNerveUniverseMap_isFullyFaithful_of_homIso (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)
    (hi : ∀ x y, IsIso (F.map x y)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseMap F) := by
  have hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, v, w, w, v} F)) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_map_isFullyFaithful_of_homIso _ (fun x y => hi x.label.down y.label.down)
  rw [dgNerveUniverseMap_factor]
  have hD := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseLiftIso.{u, v, w} A D)).isQCatEquivalence.isFullyFaithful
  have hE := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseLiftIso.{u, w, v} A E).symm).isQCatEquivalence.isFullyFaithful
  exact hD.comp (hF.comp hE)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
