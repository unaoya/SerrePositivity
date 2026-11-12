module
public import SerrePositivity.KST.Fibration.SmallSpaceDiagram
public import SerrePositivity.KST.LocalizingInvariants.LocalizationFactorization
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.QCatEquivalence

/-! # 小さい商局所化の普遍性による、元の空間値図式の宇宙を合わせた降下 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {X Q : SSet.{u}} [Quasicategory Q] (q : X ⟶ Q) (W : Set (X _⦋1⦌))
  (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization q W) (F : (SSet.uliftFunctor.{u + 1, u}).obj X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (ULift.up '' W))

/-- 元の全図式を小さい全充満像へ移して商の実局所化を適用し、その後で宇宙を戻す。 -/
def spaceDiagramLocalizationDescend :
    (SSet.uliftFunctor.{u + 1, u}).obj Q ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  (SSet.uliftFunctor.{u + 1, u}).map
    (localizationDescend q W hq (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.smallSpaceDiagram F) (smallSpaceDiagram_inverts F W hF)) ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.smallSpaceDiagramInclusion F

/-- 宇宙を跨ぐ商への降下でも、元の図式との全関手 ∞ 圏内の自然同型を保持する。 -/
def spaceDiagramLocalizationDescendIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((SSet.uliftFunctor.{u + 1, u}).map q ≫
      spaceDiagramLocalizationDescend q W hq F hF) F := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorIso.ulift.{u, u + 1}
      (localizationDescendIso q W hq (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.smallSpaceDiagram F) (smallSpaceDiagram_inverts F W hF)))
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.smallSpaceDiagramInclusion F)
  rw [Functor.map_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.smallSpaceDiagram_inclusion] at e
  exact e

end SerrePositivity.KST.Fibration
