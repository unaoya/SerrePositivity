module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.F1CompactUniverseColimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.Definition
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.YonedaEvaluationClassification
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredInfinity


/-!
概要：指定した空間の宇宙変更は、小さい κ-filtered 図式の元の余極限余錐を保存する。
方針：元の fiber 写像の弱同値を同じ余錐像へ移し、標準全空間余錐で判定する。
規約：値ごとの同値で代用せず、指定された元の全余錐像の余極限性を証明する。
使われ方：元の Yoneda 像の κ-compact 性。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
variable {B : SSet.{u + 1}} [Quasicategory B] {F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}}

/-- 指定した同じ宇宙変更は、小さい κ-filtered 図式の元の余極限余錐を保存する。 -/
lemma spaceUniverseDiagram_preservesKappaFilteredColimits (κ : Cardinal.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.{u, u + 1} κ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram.{u} := by
  intro I hI hFiltered D c hc
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram_map_isColimit D c hc

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
