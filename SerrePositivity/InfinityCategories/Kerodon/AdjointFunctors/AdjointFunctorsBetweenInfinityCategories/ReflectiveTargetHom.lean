module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.ReflectiveTargetHom

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.AdjunctInverseFormula
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulPostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveIdempotence

/-!
概要：反射の左関手は、右随伴の像を終点とする全関手圏の Hom を保つ。
方針：逆 adjunct は左関手の像と可逆余単位の合成なので、余単位を相殺する。
規約：任意の quasicategory パラメータでの主張。使われ方：Tamme の写像空間の比較。
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

lemma reflectiveTargetHomEquiv_apply {A : SSet.{u}} [Quasicategory A]
    (U : A ⟶ X) (V : A ⟶ Y) (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U (V ≫ G)) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.reflectiveTargetHomEquiv a hG U V α =
      (hoFunctor.map ((ihom A).map F)).toFunctor.map α := by
  have := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.reflectiveCounitHom_isIso a hG
  change 𝟙 _ ≫ (a.homEquiv U V).symm α ≫
    inv ((hoFunctor.map ((pre V).app Y)).toFunctor.map a.counitHom) = _
  rw [Category.id_comp, adjunctInverseHomFormula, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]

include a hG in
lemma reflectiveTargetHom_bijective {A : SSet.{u}} [Quasicategory A]
    (U : A ⟶ X) (V : A ⟶ Y) :
    Function.Bijective (fun α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U (V ≫ G) =>
      (hoFunctor.map ((ihom A).map F)).toFunctor.map α) := by
  have he : (fun α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U (V ≫ G) =>
      (hoFunctor.map ((ihom A).map F)).toFunctor.map α) =
        ⇑(_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.reflectiveTargetHomEquiv a hG U V) := by
    funext α
    exact (reflectiveTargetHomEquiv_apply a hG U V α).symm
  rw [he]
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.reflectiveTargetHomEquiv a hG U V).bijective

end SerrePositivity.KST.LocalizingInvariants
