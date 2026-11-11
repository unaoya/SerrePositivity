module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorDiagramPath
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorDiagramPathLifting

/-!
概要：境界上の可逆 path の図式を、指定した始点の全体図式から持ち上げる。
方針：path の図式の全単射を使って関手単体集合内へ移し、相対 path 持ち上げを適用して戻す。
規約：境界の path と始点を厳密に保つ。
使われ方：基準合成三角形を対角辺の指定 path に沿って運ぶ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：境界上の可逆 path の全体図式への拡張。
方針：path の全体図式と制限・始点の厳密な等式を保持する。
規約：終点の拡張だけでなく指定した path の全体を保持する。
使われ方：三角形の基準図式の輸送。 -/
structure FunctorDiagramPathExtension {A B X : SSet.{u}} (i : A ⟶ B)
    (Q : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath X) (F : B ⟶ X) where
  diagram : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath X
  restriction : i ≫ diagram = Q
  start : diagram ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0 = F

/-- 概要：単射で指定した部分図式の可逆 path は、その始点を延長した全体図式から持ち上がる。
方針：零単体で表した関手図式の相対 path 持ち上げを使い、path の図式へ戻す。
規約：始域の quasicategory 性は不要。元の境界 path を厳密に保つ。
使われ方：対角辺の path を含む境界から合成三角形を運ぶ。 -/
lemma nonempty_functorDiagramPathExtension {A B X : SSet.{u}} [Quasicategory X]
    (i : A ⟶ B) [Mono i] (Q : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath X) (F : B ⟶ X)
    (h : Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0 = i ≫ F) :
    Nonempty (FunctorDiagramPathExtension i Q F) := by
  let a := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorDiagramPathEquiv A X Q
  let b := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorDiagramPointEquiv B X F
  have ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 0 = b ≫ (pre i).app X := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorDiagramPathEquiv_endpoint, h, ← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorDiagramPointEquiv_precomp]
  obtain ⟨L, _, hL, hstart⟩ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.exists_functorDiagramPath_lift_relative i
    (initial.to (Δ[0] : SSet.{u})) a b ha (initial.to _)
    (initialIsInitial.hom_ext _ _) (initialIsInitial.hom_ext _ _)
  let R := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorDiagramPathEquiv B X).symm L
  have hR : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorDiagramPathEquiv B X R = L := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorDiagramPathEquiv B X).apply_symm_apply L
  refine ⟨⟨R, ?_, ?_⟩⟩
  · apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorDiagramPathEquiv A X).injective
    rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorDiagramPathEquiv_precomp, hR]
    exact hL
  · apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorDiagramPointEquiv B X).injective
    rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorDiagramPathEquiv_endpoint, hR]
    exact hstart

/-- 概要：与えられた始点を保つ可逆 path の全体図式の拡張を選ぶ。
方針：相対 path 持ち上げの存在から一つ取る。
規約：制限後の path の等式を構造に含める。
使われ方：基準三角形の輸送の実際の図式。 -/
noncomputable def functorDiagramPathExtension {A B X : SSet.{u}} [Quasicategory X]
    (i : A ⟶ B) [Mono i] (Q : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath X) (F : B ⟶ X)
    (h : Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0 = i ≫ F) : FunctorDiagramPathExtension i Q F :=
  (nonempty_functorDiagramPathExtension i Q F h).some

/-- 概要：運んだ図式の終点は境界 path の終点を厳密に延長する。
方針：path の制限公式を終点で評価する。
規約：選んだ拡張の終点についての等式。
使われ方：運んだ三角形の三辺を指定する。 -/
lemma FunctorDiagramPathExtension.end_restriction {A B X : SSet.{u}}
    {i : A ⟶ B} {Q : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath X} {F : B ⟶ X}
    (E : FunctorDiagramPathExtension i Q F) :
    i ≫ (E.diagram ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 1) = Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 1 := by
  rw [← Category.assoc, E.restriction]

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
