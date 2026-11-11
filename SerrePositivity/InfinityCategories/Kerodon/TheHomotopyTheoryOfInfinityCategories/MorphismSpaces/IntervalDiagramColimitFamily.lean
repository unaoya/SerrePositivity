module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalDiagramRestriction

/-!
概要：底の余極限を覆う両端固定の区間 Hom の族を貼り合わせる。
方針：展開した区間族を関手空間で貼り、両端の等式を全ての脚で検査する。
規約：元の二つの図式と全パラメーターを固定する。
使われ方：同じ分類主写像の区間 Hom 作用の降下。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

variable {J : Type v} [Category.{w} J] {D : J ⥤ SSet.{u}} {T X : SSet.{u}}
  (c : Cocone D) (hc : IsColimit c) (F G : c.pt ⟶ X)
  (s : ∀ j, T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (c.ι.app j ≫ F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (c.ι.app j ≫ G)))
  (hs : ∀ {j k} (f : j ⟶ k), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (s j) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (s k) ≫ (pre (D.map f)).app X)

/-- 元の各区間族を、余極限上の同じ二変数の族へ貼る。 -/
def intervalDiagramFamilyColimitUncurry :
    (Δ[1] : SSet.{u}) ⊗ T ⟶ (ihom c.pt).obj X :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorSpaceColimitLift c hc (fun j ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (s j)) hs

/-- 貼った二変数の族は、元の各区間族を回収する。 -/
lemma intervalDiagramFamilyColimitUncurry_fac (j : J) :
    intervalDiagramFamilyColimitUncurry c hc F G s hs ≫ (pre (c.ι.app j)).app X =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (s j) :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorSpaceColimitLift_fac c hc _ hs j

/-- 同じ貼り合わせの零端点は、元の始域図式に定値。 -/
lemma intervalDiagramFamilyColimitUncurry_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 T ≫ intervalDiagramFamilyColimitUncurry c hc F G s hs =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorSpaceColimit_hom_ext c hc
  intro j
  rw [Category.assoc, intervalDiagramFamilyColimitUncurry_fac,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_zero, SSet.const_comp]
  rfl

/-- 同じ貼り合わせの一端点は、元の終域図式に定値。 -/
lemma intervalDiagramFamilyColimitUncurry_one :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 T ≫ intervalDiagramFamilyColimitUncurry c hc F G s hs =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorSpaceColimit_hom_ext c hc
  intro j
  rw [Category.assoc, intervalDiagramFamilyColimitUncurry_fac,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_one, SSet.const_comp]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
