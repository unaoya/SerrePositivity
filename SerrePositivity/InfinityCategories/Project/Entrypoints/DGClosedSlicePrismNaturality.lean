module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SliceComparisons.DGClosedSlicePrismGeneral
public import SerrePositivity.InfinityCategories.Project.Entrypoints.DGWalkingHomPrismNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGClosedPrecompositionSlicePrism
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGStrictNatTransSliceWhisker

/-! # 閉前合成の実 slice prism の dg 関手自然性

概要：全係数の閉細分 prism は、固定標的の輸送を含めて dg 関手像と可換。
方針：join の台を比較し、自由係数の全二相単体の自然性を使う。
規約：全単体の厳密等式。使われ方：元・商の実屋根 prism の比較。
-/
