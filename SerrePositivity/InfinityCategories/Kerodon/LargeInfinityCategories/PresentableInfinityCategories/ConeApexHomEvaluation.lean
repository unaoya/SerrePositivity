module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ConeApexHomRestriction
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PresheafCoconeFlip
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ConstantPointFunctorIso

/-!
概要：全余錐から定値図式への射を右頂点で評価する対応の全単射。
方針：右端への制限と一点関手圏の評価同型を合成する。
規約：標的のみを quasicategory とする。
使われ方：余極限単位による Hom 対応。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：円錐から定値図式への Hom の右頂点評価は全単射。
方針：右端制限の全単射と一点関手圏の評価同型を合成する。
規約：元の評価関手の作用を使う。
使われ方：普遍余錐の Hom と頂点の Hom の比較。 -/
lemma coneApex_homEvaluation_bijective {K X : SSet.{u}} [Quasicategory X]
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}) ⟶ X) (y : X _⦋0⦌) :
    Function.Bijective
      ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeRightApexVertex K))).toFunctor.map :
        _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom H (SSet.const y) → _) := by
  let a := SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))
  have hv : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) a) := by
    change IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.constantPointFunctorIso X).inv
    infer_instance
  have hb := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) a))).isFullyFaithful
  have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneApex_homRestriction_bijective H y
  have h := (hb.homotopyCategoryMap_bijective _ _).comp hp
  have hf : (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K (Δ[0] : SSet.{u}))).app X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeRightApexVertex K) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.evaluateFunctorAt_precomp]
    congr 1
  have hh : (hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K (Δ[0] : SSet.{u}))).app X)).toFunctor ⋙
      (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) a)).toFunctor =
        (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeRightApexVertex K))).toFunctor := by
    rw [← Cat.Hom.comp_toFunctor, ← CategoryTheory.Functor.map_comp, hf]
  change Function.Bijective
    (((hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K (Δ[0] : SSet.{u}))).app X)).toFunctor ⋙
      (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) a)).toFunctor).map :
        _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom H (SSet.const y) → _) at h
  rw [hh] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
