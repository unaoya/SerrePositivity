module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.EdgeRepresentativeLift
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct

/-!
概要：後合成したホモトピーの代表を指定し、元の h Fun の類を保つ。
方針：後合成の inner 性と写像空間による辺の代表修正を使い、辺を uncurry する。
規約：元の二つの関手を変えず、指定された像の円柱と厳密に一致させる。
使われ方：相対左 Kan 単位の像を底で定値な代表へ直す。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：指定した像のホモトピーと同じ類なら、元の類を保つ厳密な代表がある。
方針：関手圏の後合成に辺の代表修正を適用し、得た辺をホモトピーへ戻す。
規約：両端の関手は固定し、像は raw な円柱の等式。
使われ方：底で恒等な単位の代表を相対 Kan 厳密化へ渡す。 -/
lemma exists_kanHomotopyRepresentative_lift {K D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) [InnerFibration U]
    {f g : K ⟶ D} (β : SSet.Homotopy f g) (γ : SSet.Homotopy (f ≫ U) (g ≫ U))
    (h : SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp β U)) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy γ)) :
    ∃ β' : SSet.Homotopy f g, β'.h ≫ U = γ.h ∧
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β') =
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β) := by
  let p := (ihom K).map U
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β
  let t := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy γ
  have hh : SSet.Truncated.HomotopyCategory.homMk (e.map ((truncation 2).map p)) =
      SSet.Truncated.HomotopyCategory.homMk t := by exact h
  obtain ⟨e', he', hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_kanEdgeRepresentative_lift p e t hh
  let β' := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e'
  have hm : SSet.yonedaEquiv.symm e'.edge ≫ p = SSet.yonedaEquiv.symm t.edge := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact he'
  have hraw := congrArg uncurry hm
  rw [uncurry_natural_right] at hraw
  have heq : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β' = e' := by
    apply SSet.Truncated.Edge.ext
    change SSet.yonedaEquiv (curry (uncurry (SSet.yonedaEquiv.symm e'.edge))) = e'.edge
    rw [curry_uncurry, Equiv.apply_symm_apply]
  refine ⟨β', ?_, ?_⟩
  · change uncurry (SSet.yonedaEquiv.symm e'.edge) ≫ U =
      uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry γ.h))) at hraw
    rw [Equiv.symm_apply_apply, uncurry_curry] at hraw
    exact hraw
  · rw [heq]
    exact hc

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
