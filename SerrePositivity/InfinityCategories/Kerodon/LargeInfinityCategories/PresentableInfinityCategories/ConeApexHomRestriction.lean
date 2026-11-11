module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinPoint
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RelativeJoinRightColimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorHomWhiskering

/-!
概要：円錐図式から定値図式への射は右頂点での射によって決まる。
方針：点を底とする相対 join の同型と既存の右端 Hom 対応を使う。
規約：元の右包含による制限作用そのものを全単射とする。
使われ方：余極限関手と定値関手の随伴。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：円錐から定値図式への Hom の右頂点制限は全単射。
方針：相対 join の同型で既存の右端対応へ移し、同じ前合成作用へ戻す。
規約：標的のみを quasicategory とする。
使われ方：普遍余錐からの単位の全 Hom 判定。 -/
lemma coneApex_homRestriction_bijective {K X : SSet.{u}} [Quasicategory X]
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}) ⟶ X) (y : X _⦋0⦌) :
    Function.Bijective
      ((hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K (Δ[0] : SSet.{u}))).app X)).toFunctor.map :
        _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom H (SSet.const y) → _) := by
  let p : K ⟶ (Δ[0] : SSet.{u}) := stdSimplex.isTerminalObj₀.from K
  let r := pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap p (𝟙 (Δ[0] : SSet.{u}))) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal (Δ[0] : SSet.{u}))
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr p (𝟙 (Δ[0] : SSet.{u}))
  have hi : i ≫ r = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K (Δ[0] : SSet.{u}) := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr_fst p (𝟙 _)
  have hr : Function.Bijective
      ((hoFunctor.map ((pre r).app X)).toFunctor.map :
        _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom H (SSet.const y) → _) := by
    have he := ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (asIso r)) X).choose.isFullyFaithful
    exact he.homotopyCategoryMap_bijective _ _
  have hl := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.relativeJoinRight_homMap_bijective p (r ≫ H) (SSet.const y : Δ[0] ⟶ X)
  simp only [SSet.comp_const] at hl
  have hh : (hoFunctor.map ((pre r).app X)).toFunctor ⋙
      (hoFunctor.map ((pre i).app X)).toFunctor =
        (hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K (Δ[0] : SSet.{u}))).app X)).toFunctor := by
    rw [← Cat.Hom.comp_toFunctor, ← CategoryTheory.Functor.map_comp,
      ← NatTrans.comp_app, ← pre_map, hi]
  have h := hl.comp hr
  change Function.Bijective
    (((hoFunctor.map ((pre r).app X)).toFunctor ⋙
      (hoFunctor.map ((pre i).app X)).toFunctor).map :
        _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom H (SSet.const y) → _) at h
  rw [hh] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
