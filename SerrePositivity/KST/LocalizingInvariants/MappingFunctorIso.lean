module

public import SerrePositivity.KST.LocalizingInvariants.MappingTargetIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorComposition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFamilyComparisonBijective

/-!
概要：関手同型は、指定した二頂点間の元の写像空間比較の同値性を保つ。
方針：関手圏の Hom 全単射を自然同型で移し、区間模型の実逆を復元する。
規約：大域的な充満忠実性は要求しない。使われ方：全族 cofiber と元の差の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma functorMap_bijective_of_natIso {C : Type*} {D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} (e : F ≅ F') (x z : C)
    (h : Function.Bijective (F'.map (X := x) (Y := z))) :
    Function.Bijective (F.map (X := x) (Y := z)) := by
  let t := (e.app x).homCongr (e.app z)
  have he : F.map (X := x) (Y := z) = fun f => t.symm (F'.map f) := by
    funext f
    change F.map f = e.hom.app x ≫ F'.map f ≫ e.inv.app z
    have hn := congrArg (fun m => m ≫ e.inv.app z) (e.hom.naturality f)
    simpa only [Category.assoc, e.hom_inv_id_app, Category.comp_id] using hn
  rw [he]
  exact t.symm.bijective.comp h

lemma constantFunctorPostMap_bijective_iff {X Y : SSet.{u}} (F : X ⟶ Y)
    (A : SSet.{u}) (x z : X _⦋0⦌) :
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.constantFunctorPostMap F A x z) ↔
      Function.Bijective (fun α : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantFunctorHom A X x z =>
        (hoFunctor.map ((ihom A).map F)).toFunctor.map α) :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso A x F).homCongr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso A z F)).bijective.of_comp_iff' _

lemma constantFunctorPostMap_bijective_of_interval {X Y A : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (F : X ⟶ Y) (x z : X _⦋0⦌)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap F x z)) :
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.constantFunctorPostMap F A x z) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilyComparison_bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap F x z) h
  intro f
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.intervalFunctorMap_familyHom_post f F).symm

lemma pinchedHomMap_equivalence_of_functorIso {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F F' : X ⟶ Y} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F F')
    (x z : X _⦋0⦌) (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap F' x z)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap F x z) := by
  have hh := h.isQCatEquivalence.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence
    (F'.app (Opposite.op ⦋0⦌) x) (F'.app (Opposite.op ⦋0⦌) z))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.pinchedIntervalComparison_naturality] at hh
  have hi := ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence x z).cancel_left hh
    ).isSimplicialHomotopyEquivalence
  have hf := intervalFunctorMap_equivalence_of_constantHom_bijective F x z (by
    intro A _
    apply (constantFunctorPostMap_bijective_iff F A x z).mpr
    apply functorMap_bijective_of_natIso (e.map_post A).toNatIso
    exact (constantFunctorPostMap_bijective_iff F' A x z).mp
      (constantFunctorPostMap_bijective_of_interval F' x z hi))
  have hg := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence x z).comp hf.isQCatEquivalence
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.pinchedIntervalComparison_naturality] at hg
  exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence
    (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) z)).cancel_right hg
    ).isSimplicialHomotopyEquivalence

end SerrePositivity.KST.LocalizingInvariants
