module
public import SerrePositivity.KST.Fibration.SmallSpaceDiagram
public import SerrePositivity.KST.LocalizingInvariants.LocalizationFactorization
public import SerrePositivity.InfinityCategories.F1.Universe.QCatEquivalence

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
  (hq : IsLocalization q W) (F : (SSet.uliftFunctor.{u + 1, u}).obj X ⟶ SpaceInfinity.{u})
  (hF : InvertsEdges F (ULift.up '' W))

/-- 元の全図式を小さい全充満像へ移して商の実局所化を適用し、その後で宇宙を戻す。 -/
def spaceDiagramLocalizationDescend :
    (SSet.uliftFunctor.{u + 1, u}).obj Q ⟶ SpaceInfinity.{u} :=
  (SSet.uliftFunctor.{u + 1, u}).map
    (localizationDescend q W hq (_root_.SerrePositivity.InfinityCategories.Stable.Transport.smallSpaceDiagram F) (smallSpaceDiagram_inverts F W hF)) ≫
      _root_.SerrePositivity.InfinityCategories.Stable.Transport.smallSpaceDiagramInclusion F

/-- 宇宙を跨ぐ商への降下でも、元の図式との全関手 ∞ 圏内の自然同型を保持する。 -/
def spaceDiagramLocalizationDescendIso :
    FunctorIso ((SSet.uliftFunctor.{u + 1, u}).map q ≫
      spaceDiagramLocalizationDescend q W hq F hF) F := by
  have e := FunctorIso.postcomp
    (FunctorIso.ulift.{u, u + 1}
      (localizationDescendIso q W hq (_root_.SerrePositivity.InfinityCategories.Stable.Transport.smallSpaceDiagram F) (smallSpaceDiagram_inverts F W hF)))
    (_root_.SerrePositivity.InfinityCategories.Stable.Transport.smallSpaceDiagramInclusion F)
  rw [Functor.map_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.Stable.Transport.smallSpaceDiagram_inclusion] at e
  exact e

end SerrePositivity.KST.Fibration
