module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.ReflectiveTargetConstants

public import SerrePositivity.KST.LocalizingInvariants.ReflectiveTargetHom
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFunctorHom

/-!
概要：反射の左関手による定値関手間の Hom の比較は、局所な終点で全単射。
方針：任意の関手圏の比較を使い、定値関手の合成の厳密比較で両端を正規化する。
規約：元の後合成を表す写像。使われ方：実写像空間の q による比較の同値性。
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

variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
  {F : X ⟶ Y} {G : Y ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful G)

include a hG in
lemma reflectiveConstantPostMap_bijective (A : SSet.{u}) [Quasicategory A]
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.constantFunctorPostMap F A x (G.app (Opposite.op ⦋0⦌) y)) := by
  have h := reflectiveTargetHom_bijective a hG (SSet.const x : A ⟶ X) (SSet.const y : A ⟶ Y)
  have h' : Function.Bijective (fun α : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantFunctorHom A X x
      (G.app (Opposite.op ⦋0⦌) y) =>
      (hoFunctor.map ((ihom A).map F)).toFunctor.map α) := by
    unfold _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom at h
    rw [SSet.const_comp (X := A) y G] at h
    exact h
  exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso A x F).homCongr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso A (G.app (Opposite.op ⦋0⦌) y) F)).bijective.comp h'

end SerrePositivity.KST.LocalizingInvariants
