module
public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1B.Compact.UniverseColimits
public import SerrePositivity.InfinityCategories.F2.Compact.Definition
public import SerrePositivity.InfinityCategories.F1.Compact.YonedaEvaluationClassification
public import SerrePositivity.InfinityCategories.F2.Filtered.FilteredInfinity


/-!
概要：指定した空間の宇宙変更は、小さい κ-filtered 図式の元の余極限余錐を保存する。
方針：元の fiber 写像の弱同値を同じ余錐像へ移し、標準全空間余錐で判定する。
規約：値ごとの同値で代用せず、指定された元の全余錐像の余極限性を証明する。
使われ方：元の Yoneda 像の κ-compact 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Compact
variable {B : SSet.{u + 1}} [Quasicategory B] {F : B ⟶ SpaceInfinity.{u}}

/-- 指定した同じ宇宙変更は、小さい κ-filtered 図式の元の余極限余錐を保存する。 -/
lemma spaceUniverseDiagram_preservesKappaFilteredColimits (κ : Cardinal.{u}) :
    PreservesKappaFilteredColimits.{u, u + 1} κ spaceUniverseDiagram.{u} := by
  intro I hI hFiltered D c hc
  exact spaceUniverseDiagram_map_isColimit D c hc

end SerrePositivity.InfinityCategories.F2.Compact
