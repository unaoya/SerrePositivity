module
public import SerrePositivity.KST.SConstruction.FamilySquareCurry
public import SerrePositivity.KST.SConstruction.FamilyChainCompositeClasses

/-! # 元の全交換セルが与える長方形の二辺路の合成式
概要：円柱間の有限補正全列から、両側の辺路が同じ合成を表すことを証明する。
方針：各元の実正方形の二三角形の式を、共有面で順に合成する。
規約：途中の全区間を保持した二列を用い、端点の一致だけでは結論しない。
使われ方：保存済みの全交換セルから端点固定の実辺路比較を構成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の円柱間の実ホモトピーを、同じ四辺を持つ内部 Hom の全正方形にする。 -/
def familyHomotopySquareBoundary {U E : SSet.{u}}
    {f g : U ⊗ (Δ[1] : SSet.{u}) ⟶ E} (H : SSet.Homotopy f g) :
    MappingSquareBoundaryData
      (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (familyCylinder f)))
      (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (familyCylinder g)))
      (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H (SSet.ι₀ (X := U)))))
      (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H (SSet.ι₁ (X := U))))) where
  square := familySquareCurry H.h
  bottom_eq := by
    change SSet.ι₀ ≫ familySquareCurry H.h =
      SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry f))
    rw [familySquareCurry_zero, H.h₀, Equiv.symm_apply_apply]
  top_eq := by
    change SSet.ι₁ ≫ familySquareCurry H.h =
      SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry g))
    rw [familySquareCurry_one, H.h₁, Equiv.symm_apply_apply]
  left_eq := by
    change pastingSquareVertical 0 ≫ familySquareCurry H.h =
      SSet.yonedaEquiv.symm (SSet.yonedaEquiv
        (curry ((SSet.ι₀ (X := U) ▷ (Δ[1] : SSet.{u})) ≫ H.h)))
    rw [familySquareCurry_source, Equiv.symm_apply_apply]
  right_eq := by
    change pastingSquareVertical 1 ≫ familySquareCurry H.h =
      SSet.yonedaEquiv.symm (SSet.yonedaEquiv
        (curry ((SSet.ι₁ (X := U) ▷ (Δ[1] : SSet.{u})) ≫ H.h)))
    rw [familySquareCurry_target, Equiv.symm_apply_apply]

/-- 元の全正方形の二三角形による、同じ四実辺の合成の式。 -/
lemma familyHomotopySquare_class {U E : SSet.{u}}
    {f g : U ⊗ (Δ[1] : SSet.{u}) ⟶ E} (H : SSet.Homotopy f g) :
    SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (familyCylinder f)) ≫
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H SSet.ι₁)) =
    SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H SSet.ι₀)) ≫
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (familyCylinder g)) :=
  (familyHomotopySquareBoundary H).homMk_comp

/-- 元の二次元補正全列の両側の辺路は、全区間を順に合成すると一致する。 -/
lemma familyChainRectangle_class {U E : SSet.{u}}
    {f g : U ⊗ (Δ[1] : SSet.{u}) ⟶ E} (c : FamilyHomotopyChain f g) :
    SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (familyCylinder f)) ≫
      familyChainCompositeClass (familyHomotopyChainPrecomp (SSet.ι₁ (X := U)) c) =
    familyChainCompositeClass (familyHomotopyChainPrecomp (SSet.ι₀ (X := U)) c) ≫
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (familyCylinder g)) := by
  induction c with
  | nil => exact (Category.comp_id _).trans (Category.id_comp _).symm
  | cons H tail ih =>
      change _ ≫ (_ ≫ familyChainCompositeClass
          (familyHomotopyChainPrecomp (SSet.ι₁ (X := U)) tail)) =
        (_ ≫ familyChainCompositeClass
          (familyHomotopyChainPrecomp (SSet.ι₀ (X := U)) tail)) ≫ _
      rw [← Category.assoc, familyHomotopySquare_class, Category.assoc, ih, ← Category.assoc]

end SerrePositivity.KST.SConstruction
