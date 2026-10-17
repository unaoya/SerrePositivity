# Stage 4 の依存監査（2026-10-17）

F1・F2を「指定した両関手的分解を持つモデル圏」に限定した場合の監査。
生成コマンド：`python3 scripts/audit_stage4_dependencies.py`。
ソースのimportと下表の直接参照を調べ、再帰的な全プロジェクト依存を追跡した。
基準はS3完了コミット `9969643992424d419484ab27069a24b8973b45d7`（k-theory.md §223）。

Localization全60、Spectra/Stable全17、レベルのCombinatorial・LeftProperの2、計79モジュールが対象。
依存閉包は663ソースモジュール。基準以後に追加された依存は0、基準から内容が変わった到達モジュールも0。
従って中断対象の§224以降への依存はない。Foundationsは全成果をまとめる入口として別監査し、
この独立性の検査対象には加えない。663のうち宣言を持つ660モジュール・8392宣言を
`lake env lean scripts/audit_stage4_contract.lean`で監査済み（標準3公理のみ）。

下表の名前は `SerrePositivity.` を省略したモジュール名。参照欄は該当ソース中の
chosenResolutionHom・resolutionHom・smallHomと、その比較名前空間の直接参照を抽出する。
「間接」は不要という意味ではなく、import先の条件付きAPIを介することを表す。
各行の再帰的依存とソース一致検査は上記コマンドのJSON出力で再現できる。

| モジュール | 直接import | 直接のRMap/F2参照 | 再帰的ソース数 | §224以降 |
| --- | --- | --- | ---: | ---: |
| `HomotopicalAlgebra.Localization.AccessibleHomotopyGenerators` | `HomotopicalAlgebra.Localization.HomotopyGenerators`<br>`HomotopicalAlgebra.Localization.AccessibleLocalObjects`<br>`HomotopicalAlgebra.HomotopyFunctionComplex.SmallHomAccessible` | `SmallHomComparison.chosenHom`<br>`SmallHomComparison.exists_accessible_mapping_tests` | 246 | 0 |
| `HomotopicalAlgebra.Localization.AccessibleLocalEquivalences` | `HomotopicalAlgebra.Localization.LocalReplacementDetection`<br>`HomotopicalAlgebra.Smith.AccessibleWeakEquivalenceInverseImage` | 間接 | 143 | 0 |
| `HomotopicalAlgebra.Localization.AccessibleLocalObjects` | `HomotopicalAlgebra.Localization.AccessibleSmallLocalObjects`<br>`HomotopicalAlgebra.Localization.ChoiceIndependence` | 間接 | 175 | 0 |
| `HomotopicalAlgebra.Localization.AccessibleLocalReplacement` | `HomotopicalAlgebra.Localization.LocalBoundaryEquivalences`<br>`HomotopicalAlgebra.Localization.AccessibleLocalEquivalences` | 間接 | 275 | 0 |
| `HomotopicalAlgebra.Localization.AccessibleSmallLocalObjects` | `HomotopicalAlgebra.Localization.SmallHomTests`<br>`HomotopicalAlgebra.Localization.MappingTestDiagram`<br>`HomotopicalAlgebra.HomotopyFunctionComplex.SmallHomAccessible`<br>`HomotopicalAlgebra.Smith.AccessibleWeakEquivalenceInverseImage`<br>`HomotopicalAlgebra.Diagram.WeightedCones`<br>`HomotopicalAlgebra.Simplicial.ModelCompatibility` | `SmallHomComparison.chosenHom`<br>`SmallHomComparison.exists_accessible_mapping_tests` | 173 | 0 |
| `HomotopicalAlgebra.Localization.ArrowFrameFibrations` | `HomotopicalAlgebra.Localization.ArrowFrameTests`<br>`HomotopicalAlgebra.HomotopyFunctionComplex.RelativeSubcomplexTensor` | 間接 | 120 | 0 |
| `HomotopicalAlgebra.Localization.ArrowFrameTests` | `HomotopicalAlgebra.Localization.ArrowFrames`<br>`HomotopicalAlgebra.Localization.Basic` | `chosenResolutionHom` | 115 | 0 |
| `HomotopicalAlgebra.Localization.ArrowFrames` | `HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionComparison`<br>`HomotopicalAlgebra.HomotopyFunctionComplex.FramePreservation` | `ResolutionComparison.diagramCofFactorization` | 109 | 0 |
| `HomotopicalAlgebra.Localization.Basic` | `HomotopicalAlgebra.Localization.MappingTests`<br>`HomotopicalAlgebra.HomotopyFunctionComplex.ChosenComparison` | `chosenResolutionHom`<br>`chosenResolutionHom_map_source_weakEquivalence`<br>`chosenResolutionHom_map_target_weakEquivalence` | 108 | 0 |
| `HomotopicalAlgebra.Localization.Bifunctor` | `HomotopicalAlgebra.Localization.Endofunctor`<br>`HomotopicalAlgebra.Monoidal.BifunctorChangeModel` | 間接 | 170 | 0 |
| `HomotopicalAlgebra.Localization.ChoiceIndependence` | `HomotopicalAlgebra.Localization.Basic` | `ChosenComparison.left`<br>`ChosenComparison.left_weakEquivalence`<br>`ChosenComparison.right`<br>`ChosenComparison.right_weakEquivalence`<br>`chosenResolutionHom` | 109 | 0 |
| `HomotopicalAlgebra.Localization.Conditional` | `HomotopicalAlgebra.Localization.Detection`<br>`HomotopicalAlgebra.Quillen.Adjunction` | 間接 | 118 | 0 |
| `HomotopicalAlgebra.Localization.ContinuousLocalEquivalences` | `HomotopicalAlgebra.Localization.SpanLocalEquivalences`<br>`HomotopicalAlgebra.Diagram.RelativeHomotopyColimit`<br>`HomotopicalAlgebra.Diagram.LimitPrefix` | 間接 | 232 | 0 |
| `HomotopicalAlgebra.Localization.CovariantDetection` | `HomotopicalAlgebra.Localization.Detection`<br>`HomotopicalAlgebra.HomotopyFunctionComplex.SmallHomComparison` | `chosenResolutionHom`<br>`chosenResolutionHomPiZeroEquiv`<br>`chosenResolutionHomPiZeroEquiv_naturality_target`<br>`resolutionHom` | 143 | 0 |
| `HomotopicalAlgebra.Localization.Detection` | `HomotopicalAlgebra.Localization.Basic`<br>`HomotopicalAlgebra.Quillen.Saturation`<br>`HomotopicalAlgebra.Simplicial.PiZeroWeakEquivalence`<br>`HomotopicalAlgebra.HomotopyFunctionComplex.PiZero` | `chosenResolutionHom`<br>`chosenResolutionHomPiZeroEquiv`<br>`chosenResolutionHomPiZeroEquiv_naturality_source`<br>`chosenResolutionHom_kanComplex` | 116 | 0 |
| `HomotopicalAlgebra.Localization.Endofunctor` | `HomotopicalAlgebra.Localization.UniversalProperty` | 間接 | 165 | 0 |
| `HomotopicalAlgebra.Localization.Enriched` | `HomotopicalAlgebra.Localization.Bifunctor`<br>`HomotopicalAlgebra.Enriched.TensorCotensor` | 間接 | 171 | 0 |
| `HomotopicalAlgebra.Localization.EnrichedDetection` | `HomotopicalAlgebra.Localization.EnrichedLocalObjects`<br>`HomotopicalAlgebra.Localization.EnrichedTestComparison` | 間接 | 180 | 0 |
| `HomotopicalAlgebra.Localization.EnrichedExistence` | `HomotopicalAlgebra.Localization.ModelExistence`<br>`HomotopicalAlgebra.Localization.EnrichedDetection`<br>`HomotopicalAlgebra.Enriched.UnitChangeModel` | 間接 | 320 | 0 |
| `HomotopicalAlgebra.Localization.EnrichedLocalObjects` | `HomotopicalAlgebra.Localization.Enriched`<br>`HomotopicalAlgebra.Enriched.DerivedMapping` | 間接 | 174 | 0 |
| `HomotopicalAlgebra.Localization.EnrichedTestComparison` | `HomotopicalAlgebra.Enriched.UnitFrame`<br>`HomotopicalAlgebra.Enriched.DerivedMapping`<br>`HomotopicalAlgebra.Localization.FrameTests` | 間接 | 152 | 0 |
| `HomotopicalAlgebra.Localization.FibrantMappingTests` | `HomotopicalAlgebra.Localization.Basic`<br>`HomotopicalAlgebra.HomotopyFunctionComplex.TargetInvariance` | 間接 | 109 | 0 |
| `HomotopicalAlgebra.Localization.Fibrations` | `HomotopicalAlgebra.Localization.Conditional`<br>`HomotopicalAlgebra.Localization.LocalReplacementDetection`<br>`HomotopicalAlgebra.Localization.ReplacementData` | 間接 | 121 | 0 |
| `HomotopicalAlgebra.Localization.FilteredLocalEquivalences` | `HomotopicalAlgebra.Localization.HocolimLocalEquivalences`<br>`HomotopicalAlgebra.Diagram.FilteredHomotopyColimit` | 間接 | 230 | 0 |
| `HomotopicalAlgebra.Localization.FilteredMappingGenerators` | `HomotopicalAlgebra.Localization.HocolimMappingTests`<br>`HomotopicalAlgebra.Diagram.FilteredHomotopyColimit` | `SmallHomComparison.chosenHom` | 223 | 0 |
| `HomotopicalAlgebra.Localization.FrameArrowTests` | `HomotopicalAlgebra.Localization.Basic`<br>`HomotopicalAlgebra.HomotopyFunctionComplex.FrameOverFunctor`<br>`Mathlib.CategoryTheory.Limits.Shapes.Equalizers` | 間接 | 112 | 0 |
| `HomotopicalAlgebra.Localization.FrameTargetTests` | `HomotopicalAlgebra.Localization.FrameArrowTests`<br>`HomotopicalAlgebra.HomotopyFunctionComplex.FrameRightQuillen` | `chosenResolutionHom`<br>`chosenResolutionHom_map_iff` | 117 | 0 |
| `HomotopicalAlgebra.Localization.FrameTests` | `HomotopicalAlgebra.Localization.Basic`<br>`HomotopicalAlgebra.HomotopyFunctionComplex.FrameComparison` | `FrameComparison.homLeft`<br>`FrameComparison.homLeft_weakEquivalence`<br>`FrameComparison.homRight`<br>`FrameComparison.homRight_weakEquivalence`<br>`chosenResolutionHom`<br>`resolutionHom` | 111 | 0 |
| `HomotopicalAlgebra.Localization.HocolimLocalEquivalences` | `HomotopicalAlgebra.Localization.HocolimMappingTests`<br>`HomotopicalAlgebra.Localization.SmallHomTests` | `SmallHomComparison.chosenHom` | 205 | 0 |
| `HomotopicalAlgebra.Localization.HocolimMappingTests` | `HomotopicalAlgebra.Diagram.HocolimRMapFormula`<br>`HomotopicalAlgebra.Quillen.Saturation` | `SmallHomComparison.chosenHom`<br>`SmallHomComparison.chosenHom_map_source_weakEquivalence` | 198 | 0 |
| `HomotopicalAlgebra.Localization.HomotopyGenerators` | `HomotopicalAlgebra.Localization.FilteredMappingGenerators`<br>`HomotopicalAlgebra.Localization.CovariantDetection` | `SmallHomComparison.chosenHom`<br>`SmallHomComparison.chosenHom_map_target_weakEquivalence`<br>`SmallHomComparison.targetArrowIso` | 236 | 0 |
| `HomotopicalAlgebra.Localization.IteratedExistence` | `HomotopicalAlgebra.Localization.ModelExistence`<br>`HomotopicalAlgebra.Localization.Iteration` | 間接 | 306 | 0 |
| `HomotopicalAlgebra.Localization.Iteration` | `HomotopicalAlgebra.Localization.Minimality` | 間接 | 167 | 0 |
| `HomotopicalAlgebra.Localization.LeftProperPushout` | `HomotopicalAlgebra.Localization.SpanLocalEquivalences`<br>`Mathlib.CategoryTheory.Category.ULift` | 間接 | 217 | 0 |
| `HomotopicalAlgebra.Localization.LeftProperTransfinite` | `HomotopicalAlgebra.Localization.ContinuousLocalEquivalences`<br>`HomotopicalAlgebra.Localization.LeftProperPushout` | 間接 | 234 | 0 |
| `HomotopicalAlgebra.Localization.LocalBoundaryCharacterization` | `HomotopicalAlgebra.Localization.LocalBoundaryGenerators`<br>`HomotopicalAlgebra.Localization.LocalFibrantApproximation`<br>`HomotopicalAlgebra.Localization.ArrowFrameFibrations`<br>`HomotopicalAlgebra.HomotopyFunctionComplex.PresentationSourceLiftingConverse` | 間接 | 134 | 0 |
| `HomotopicalAlgebra.Localization.LocalBoundaryEquivalences` | `HomotopicalAlgebra.Localization.LeftProperTransfinite`<br>`HomotopicalAlgebra.Localization.LocalFibrantApproximation`<br>`HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ClosedObjectwise` | 間接 | 251 | 0 |
| `HomotopicalAlgebra.Localization.LocalBoundaryGenerators` | `HomotopicalAlgebra.Localization.ArrowFrameTests`<br>`HomotopicalAlgebra.Smith.Smallness` | 間接 | 117 | 0 |
| `HomotopicalAlgebra.Localization.LocalFibrantApproximation` | `HomotopicalAlgebra.Localization.LocalBoundaryGenerators`<br>`HomotopicalAlgebra.Smith.AccessibleGeneratedPair`<br>`HomotopicalAlgebra.Smith.AccessibleFactorization` | 間接 | 127 | 0 |
| `HomotopicalAlgebra.Localization.LocalLeftProper` | `HomotopicalAlgebra.Localization.SpanLocalEquivalences`<br>`Mathlib.CategoryTheory.Category.ULift` | 間接 | 217 | 0 |
| `HomotopicalAlgebra.Localization.LocalReplacementDetection` | `HomotopicalAlgebra.Localization.Detection` | `chosenResolutionHom`<br>`chosenResolutionHomPiZeroEquiv`<br>`chosenResolutionHomPiZeroEquiv_naturality_source` | 117 | 0 |
| `HomotopicalAlgebra.Localization.MappingTestDiagram` | `HomotopicalAlgebra.HomotopyFunctionComplex.Accessible` | 間接 | 8 | 0 |
| `HomotopicalAlgebra.Localization.MappingTests` | `Mathlib.CategoryTheory.MorphismProperty.Composition`<br>`Mathlib.CategoryTheory.MorphismProperty.Retract`<br>`Mathlib.CategoryTheory.Functor.Currying` | 間接 | 1 | 0 |
| `HomotopicalAlgebra.Localization.Minimality` | `HomotopicalAlgebra.Localization.UniversalProperty`<br>`HomotopicalAlgebra.Quillen.ModelOrder` | 間接 | 166 | 0 |
| `HomotopicalAlgebra.Localization.ModelComparison` | `HomotopicalAlgebra.Localization.Conditional`<br>`HomotopicalAlgebra.Localization.ChoiceIndependence` | 間接 | 120 | 0 |
| `HomotopicalAlgebra.Localization.ModelExistence` | `HomotopicalAlgebra.Localization.AccessibleLocalReplacement`<br>`HomotopicalAlgebra.Localization.Conditional`<br>`HomotopicalAlgebra.Localization.LocalLeftProper`<br>`HomotopicalAlgebra.Smith.Existence` | 間接 | 281 | 0 |
| `HomotopicalAlgebra.Localization.Monoidal` | `HomotopicalAlgebra.Localization.Bifunctor`<br>`HomotopicalAlgebra.Localization.MonoidalUnit`<br>`HomotopicalAlgebra.Monoidal.BifunctorSymmetrize`<br>`HomotopicalAlgebra.Monoidal.CofibrantTensor`<br>`CategoryTheory.ParametrizedAdjunctionTransport` | 間接 | 178 | 0 |
| `HomotopicalAlgebra.Localization.MonoidalExistence` | `HomotopicalAlgebra.Localization.ModelExistence`<br>`HomotopicalAlgebra.Localization.Monoidal` | 間接 | 315 | 0 |
| `HomotopicalAlgebra.Localization.MonoidalUnit` | `HomotopicalAlgebra.Localization.Conditional`<br>`HomotopicalAlgebra.Monoidal.UnitChangeModel` | 間接 | 122 | 0 |
| `HomotopicalAlgebra.Localization.QuillenCriterion` | `HomotopicalAlgebra.Localization.Fibrations`<br>`HomotopicalAlgebra.Quillen.FibrantCriterion` | 間接 | 124 | 0 |
| `HomotopicalAlgebra.Localization.QuillenLocalObjects` | `HomotopicalAlgebra.Localization.FibrantMappingTests`<br>`HomotopicalAlgebra.HomotopyFunctionComplex.AdjunctionWeakEquivalence`<br>`HomotopicalAlgebra.HomotopyFunctionComplex.FramePreservation`<br>`HomotopicalAlgebra.HomotopyFunctionComplex.SourceInvariance`<br>`HomotopicalAlgebra.HomotopyFunctionComplex.ChosenMapComparison`<br>`HomotopicalAlgebra.Quillen.FibrantCriterion` | 間接 | 148 | 0 |
| `HomotopicalAlgebra.Localization.Replacement` | `HomotopicalAlgebra.Localization.ReplacementData`<br>`HomotopicalAlgebra.Localization.AccessibleLocalReplacement` | 間接 | 277 | 0 |
| `HomotopicalAlgebra.Localization.ReplacementComparison` | `HomotopicalAlgebra.Localization.ReplacementData`<br>`HomotopicalAlgebra.Localization.ChoiceIndependence` | 間接 | 120 | 0 |
| `HomotopicalAlgebra.Localization.ReplacementData` | `HomotopicalAlgebra.Localization.LocalReplacementDetection` | 間接 | 118 | 0 |
| `HomotopicalAlgebra.Localization.ReplacementHomotopy` | `HomotopicalAlgebra.Localization.ReplacementData` | `chosenResolutionHom`<br>`chosenResolutionHomPiZeroEquiv`<br>`chosenResolutionHomPiZeroEquiv_naturality_source` | 119 | 0 |
| `HomotopicalAlgebra.Localization.Representatives` | `HomotopicalAlgebra.Localization.Basic` | 間接 | 109 | 0 |
| `HomotopicalAlgebra.Localization.ResolutionHomGenerators` | `HomotopicalAlgebra.Localization.HomotopyGenerators`<br>`HomotopicalAlgebra.Localization.FrameTargetTests` | `SmallHomComparison.chosenHom`<br>`SmallHomComparison.targetArrowIso`<br>`chosenResolutionHom_map_iff` | 239 | 0 |
| `HomotopicalAlgebra.Localization.SmallHomTests` | `HomotopicalAlgebra.Localization.Basic`<br>`HomotopicalAlgebra.HomotopyFunctionComplex.SmallHomComparison` | `SmallHomComparison.chosenHom`<br>`SmallHomComparison.sourceArrowIso` | 135 | 0 |
| `HomotopicalAlgebra.Localization.SpanLocalEquivalences` | `HomotopicalAlgebra.Localization.HocolimLocalEquivalences`<br>`HomotopicalAlgebra.Diagram.SpanHomotopyColimit` | 間接 | 216 | 0 |
| `HomotopicalAlgebra.Localization.UniversalProperty` | `HomotopicalAlgebra.Localization.QuillenCriterion`<br>`HomotopicalAlgebra.Localization.QuillenLocalObjects`<br>`HomotopicalAlgebra.Localization.ModelComparison`<br>`HomotopicalAlgebra.Quillen.DerivedMapTest` | 間接 | 164 | 0 |
| `Spectra.Stable.CofibrantLocalizingMaps` | `Spectra.Stable.LocalizingMaps`<br>`HomotopicalAlgebra.Monoidal.CofibrantTensor`<br>`HomotopicalAlgebra.HomotopyFunctionComplex.ChosenMapComparison` | 間接 | 176 | 0 |
| `Spectra.Stable.DerivedTensorInverse` | `Spectra.Stable.TensorInverseMap`<br>`Spectra.Stable.EnrichedModel`<br>`HomotopicalAlgebra.Monoidal.DerivedTensorInverse` | 間接 | 491 | 0 |
| `Spectra.Stable.EnrichedModel` | `Spectra.Stable.TensorCompatibility`<br>`Spectra.ModelCategory.GeneralLevelEnriched`<br>`HomotopicalAlgebra.Localization.Enriched`<br>`HomotopicalAlgebra.Localization.Monoidal`<br>`HomotopicalAlgebra.Enriched.UnitChangeModel` | 間接 | 484 | 0 |
| `Spectra.Stable.FrameLocality` | `Spectra.Stable.CofibrantLocalizingMaps`<br>`Spectra.Stable.LocalizingHom`<br>`HomotopicalAlgebra.Localization.FrameArrowTests`<br>`HomotopicalAlgebra.HomotopyFunctionComplex.FramePreservation` | 間接 | 188 | 0 |
| `Spectra.Stable.InternalHomOmega` | `Spectra.General.ShiftedHomAdjoint`<br>`Spectra.General.Cotensor`<br>`Spectra.Stable.Omega`<br>`HomotopicalAlgebra.Quillen.FibrantCriterion`<br>`Mathlib.AlgebraicTopology.ModelCategory.Instances` | 間接 | 129 | 0 |
| `Spectra.Stable.LocalizingHom` | `Spectra.Stable.LocalizingMaps`<br>`HomotopicalAlgebra.HomotopyFunctionComplex.AdjunctionHom`<br>`Mathlib.CategoryTheory.Monoidal.Closed.Braided` | 間接 | 56 | 0 |
| `Spectra.Stable.LocalizingMaps` | `Spectra.General.Suspension`<br>`Spectra.General.Evaluation`<br>`Mathlib.CategoryTheory.MorphismProperty.IsSmall` | 間接 | 53 | 0 |
| `Spectra.Stable.ModelCategory` | `Spectra.Stable.OmegaLocalObjects`<br>`Spectra.ModelCategory.Combinatorial`<br>`HomotopicalAlgebra.Localization.ModelExistence` | 間接 | 373 | 0 |
| `Spectra.Stable.Omega` | `Spectra.General.Suspension`<br>`HomotopicalAlgebra.Monoidal.CofibrantTensor`<br>`HomotopicalAlgebra.Quillen.Brown` | 間接 | 54 | 0 |
| `Spectra.Stable.OmegaDetection` | `Spectra.Stable.FrameLocality`<br>`Spectra.Stable.Omega`<br>`HomotopicalAlgebra.Localization.ResolutionHomGenerators`<br>`HomotopicalAlgebra.Quillen.FibrantCriterion` | 間接 | 307 | 0 |
| `Spectra.Stable.OmegaLocalObjects` | `Spectra.Stable.OmegaDetection`<br>`Spectra.ModelCategory.LevelFacts` | 間接 | 310 | 0 |
| `Spectra.Stable.OrdinarySuspension` | `Spectra.General.DerivedSuspensionComparison`<br>`Spectra.General.SimplicialSuspensionComparison`<br>`HomotopicalAlgebra.Quillen.DerivedAdjunction` | 間接 | 393 | 0 |
| `Spectra.Stable.Replacement` | `Spectra.Stable.ModelCategory`<br>`HomotopicalAlgebra.Localization.Replacement` | 間接 | 376 | 0 |
| `Spectra.Stable.SimplicialStability` | `Spectra.Stable.OrdinarySuspension`<br>`Spectra.ModelCategory.PointedPresentability`<br>`Spectra.Stable.DerivedTensorInverse` | 間接 | 622 | 0 |
| `Spectra.Stable.TensorCompatibility` | `Spectra.Stable.ModelCategory`<br>`Spectra.Stable.InternalHomOmega`<br>`Spectra.General.EnrichedModel`<br>`HomotopicalAlgebra.Localization.Endofunctor` | 間接 | 467 | 0 |
| `Spectra.Stable.TensorInverseMap` | `Spectra.Stable.UniversalLocalizingMaps`<br>`Spectra.General.TensorFreeAtSum`<br>`Spectra.SymmetricSequence.FreeZeroModuleUnit` | 間接 | 419 | 0 |
| `Spectra.Stable.UniversalLocalizingMaps` | `Spectra.Stable.ModelCategory`<br>`HomotopicalAlgebra.HomotopyFunctionComplex.FrameRightQuillen` | 間接 | 374 | 0 |
| `Spectra.ModelCategory.Combinatorial` | `Spectra.General.Limits`<br>`HomotopicalAlgebra.Smith.AccessibleLimits`<br>`HomotopicalAlgebra.Monoidal.ModulePresentability`<br>`Spectra.ModelCategory.LevelAcyclicity`<br>`Spectra.ModelCategory.LevelSmallness` | 間接 | 77 | 0 |
| `Spectra.ModelCategory.LeftProper` | `Spectra.ModelCategory.FreeLevelCofibrations`<br>`Spectra.ModelCategory.LevelFromGenerators`<br>`HomotopicalAlgebra.Transfer.EvaluationLeftProper`<br>`Spectra.ModelCategory.Combinatorial` | 間接 | 95 | 0 |
