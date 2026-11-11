module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraFreeGeneratorExt
public import SerrePositivity.KST.LocalizingInvariants.CochainCycleCoverLift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraExtensionInfinity
public import SerrePositivity.DifferentialGraded.Resolution.Basic

/-!
概要：自由 cycle 被覆による初期 dg 圏を、全射準同型な実 dg 代数射を通って持ち上げる。
方針：各 cycle の厳密な持ち上げを生成辺へ与え、自由 dg 圏の実普遍性を使う。
規約：増大との合成を dg 関手全体で証明。使われ方：cell 分解の持ち上げの初期段。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)} (p : C ⟶ B)
  (hs : ∀ n : ℤ, Function.Surjective (p.hom.f n)) (hq : QuasiIso p.hom)

def initialCellLiftFunctor :
    DGFunctor R (DGCategoryCycleCover.Source R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R C) :=
  FreeDGCategory.lift R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R C)
    (DGCategoryCycleCover.edges R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B)) (fun _ ↦ .star)
    (fun _ _ ↦ cycleCoverLift p.hom hs hq)

lemma initialCellLift_augmentation :
    (initialCellLiftFunctor R p hs hq).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraPointMap R p) =
      DGCategoryCycleCover.augmentation R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) := by
  apply (FreeDGCategory.universalEquiv R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B)
    (DGCategoryCycleCover.edges R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B))).injective
  apply dgAlgebraGeneratorMap_ext
  intro x y
  change FreeDGCategory.edgeInclusion R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B)
      (DGCategoryCycleCover.edges R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B)) x y ≫
        ((initialCellLiftFunctor R p hs hq).map x y ≫ p.hom) =
    FreeDGCategory.edgeInclusion R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B)
      (DGCategoryCycleCover.edges R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B)) x y ≫
        (DGCategoryCycleCover.augmentation R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B)).map x y
  rw [← Category.assoc]
  change (FreeDGCategory.edgeInclusion R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B)
      (DGCategoryCycleCover.edges R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B)) x y ≫
        (FreeDGCategory.lift R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R C)
          (DGCategoryCycleCover.edges R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B)) (fun _ ↦ .star)
          (fun _ _ ↦ cycleCoverLift p.hom hs hq)).map x y) ≫ p.hom = _
  rw [FreeDGCategory.lift_edge, cycleCoverLift_projection]
  exact (DGCategoryCycleCover.edge_augmentation R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) x y).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
