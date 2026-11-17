# Codex 作業指示書 BS-W8：André と Semiperfectoid/RootEnvelope を数学的な話題ごとにまとめる（530 本 → 52 本、監査 4 本の移動、31 本の削除）

作成：2026-10-26（BS 作業チャット）。宛先：Codex。**BS-W8b（`efc1dc638`、転送スタブ 29 本の削除）の後に行う。**
ユーザーの決定（10-26）：
(1) 主経路（Thm 7.14）は `Andre/{OrdinaryRoots,Envelope,Perfection,Transfinite}` と `Andre/AndreFlatness` にまとめる。
(2) `Andre/Remark715` は Rem 7.15 の結論（mod p で ind-syntomic）を証明していないので、`Andre/PowerRootEnvelope` に改名してまとめる
（中身は原典どおりの一元拡大 S = R⟨Y^{1/p^∞}⟩/f(Y) と prismatic envelope の初期性、Rem 7.15 の途中の pd 比較）。
(3) `Andre/Variants` は残してまとめる。(4) `Andre/RootedExtension/Supplement` は、再利用できる部分（p で割る δ 除算、δ 関係の Koszul 計算、
根の関係の生の包）を `Andre/Envelope` に残し、残り 31 本（δ 完全化の重複と旧 B4 経路のつなぎ）を削除する。ディレクトリ Supplement はなくなる。
(5) `Semiperfectoid/RootEnvelope`（Thm 7.4 の別証明）は残してまとめる。転送スタブは作らない（10-25 の決定）。

## 0. 前提と全体の方針

- 前提は BS-W1 の §0 と同じ（所有範囲、他レーンの並行作業、root ビルドの禁止、`git add -A`・`git commit -a` の禁止）。
- **公開の宣言名・名前空間・型・証明は変えない**。例外は、同じ統合先に同名の `private` 宣言が二つ入る 2 件だけ。スクリプトが元ファイルの本文の中で
  単語単位に付け替える（`DeltaDivisionEvaluationFiniteSupportColimit` の `finite_le_ker` → `finiteSupport_le_ker`、
  `VarpiComparison/UnconditionalPD` の `transport_isDPMorphism` → `unconditional_transport_isDPMorphism`。後者は `PDCompatibility` の同名と中身が同一）。
- スクリプトは W8 用に三点を足した（このコミットに含まれる）：`deletes`（削除。所有範囲の監査 scripts/ の import 行だけは外し、それ以外の
  import 元があれば止まる）、`private_renames`、集約 `SerrePositivity/BhattScholze.lean` を書き換えの対象に加えた。
  また、元ファイルの本文の中で開いたまま終わる無名の section（`Transfinite/ResidueTensorColimit` の `noncomputable section`）は、
  名前付き section を閉じる前に `end` を補う。section 行より前に書かれた `open`・`universe`（Transfinite の 13 本）は、
  section の中の先頭へ移す（BS 作業チャットの試験で、これがないと `Transfinite/Colimit` が落ちることを確認して直した）。
- **まとめないもの**：`Andre/AndreFlatness`（公開入口）、`Andre/MonicRelationRegularSequence`（**KST の `KST/DerivedBlowup/UniversalRegularSequence` が
  import しているので名前を変えない**）、`Andre/Variants/MonicRootedExtension`（import だけの集約。BS の集約が読む）。三つとも import 行だけが書き換わる。
- Remark715 の専用監査 4 本（`noncomputable section`・`meta section` を閉じずに使うので統合できない）は、統合の後に移動用スクリプトで
  `Andre/PowerRootEnvelope/Audit/` へ 1 本ずつ移す。
- 統合後の import に循環がないこと、各統合先の連結順が依存に沿っていること、`private` 宣言とインスタンス名の衝突が上の 2 件だけであること、
  名前付きの scope が開いたまま終わる元ファイルがないことは確認済み。所有範囲外の import 元はない（CLMST の 2 本と `audit_clmst` は所有範囲）。
- 新しい sorry・axiom を加えない。

## 1. 作業 A：統合と削除（スクリプト）

計画は [bhatt-scholze-codex-w8-merges.json](../../../evidence/bhatt-scholze/bhatt-scholze-codex-w8-merges.json)（話題の説明は各統合先の docstring）、スクリプトは
[bhatt-scholze-merge-modules.py](../../../evidence/bhatt-scholze/bhatt-scholze-merge-modules.py)。表の元ファイル名は `Andre/` と `Semiperfectoid/RootEnvelope/`（RE/）を省いた。

| 統合後 | 本数 | 元（この順に連結） |
| --- | --- | --- |
| `Andre/Envelope/MonicCandidate` | 9 | DivisionPerfectoidCandidate, PolynomialPerfectoidCandidate, MonicPrismaticCandidateComparison, MonicPrismaticFirstResidueKoszul, MonicPrismaticFiniteResidueKoszul, MonicPrismaticSourceResidue, MonicPrismaticCoefficientReduction, MonicPrismaticQuotientDerived, MonicPrismaticPrismBaseMap |
| `Andre/OrdinaryRoots/Adjoin` | 10 | MonicRelation, RootedExtension/MonicPowerFamilyCover, RootedExtension/MonicPowerFamilyUniversal, RootedExtension/MonicPowerFamilyPresentation, RootedExtension/MonicPowerFamilyBaseQuotient, MonicRelationResidue, OrdinaryMonicRoot, RootedExtension/MonicPowerFamilyRelationRegularity, RootedExtension/MonicPowerFamilyPolynomialFlat, RootedExtension/Supplement/MonicPowerFamilyCompleteFlat |
| `Andre/OrdinaryRoots/Family` | 10 | MonicFamilyPartialQuotient, MonicFamilySubsetRegular, MonicFamilyQuotientUniversal, MonicFamilyFiniteSystem, MonicFamilyColimit, MonicFamilyOptionQuotient, MonicFamilyQuotientReindex, MonicFiniteFamilyFlat, MonicFamilyFaithfullyFlat, MonicFamilyCoefficientQuotient |
| `Andre/Transfinite/Colimit` | 12 | Transfinite/FaithfullyFlatColimit, Transfinite/BoundedCompletion, Transfinite/Composition, Transfinite/CompleteFlatColimit, Transfinite/ResidueTensorColimit, Transfinite/CountableDescent, Transfinite/CountableCompletion, Transfinite/PerfectoidLimitCompleteness, Transfinite/PrismaticCompletion, Transfinite/CompletionUniversal, Transfinite/ResidueFrobenius, Transfinite/FrobeniusKernelColimit |
| `Andre/Perfection/DeltaAlgebra` | 18 | RootedExtension/DeltaAlgebra/DeltaAlgebraFrobeniusStages, RootedExtension/DeltaAlgebra/DeltaAlgebraPerfectionCocone, RootedExtension/PerfectDeltaPrismaticDerivedFlat, RootedExtension/PerfectDeltaFrobeniusStageFlat, RootedExtension/DeltaAlgebra/DeltaAlgebraFrobeniusStageFlat, RootedExtension/DeltaAlgebra/DeltaAlgebraPerfectionTor, RootedExtension/DeltaAlgebra/DeltaAlgebraPerfectionResidueFlat, RootedExtension/DeltaAlgebra/DeltaAlgebraPerfectionResidueFaithful, RootedExtension/DeltaAlgebra/DeltaAlgebraPerfectionResidue, RootedExtension/DeltaAlgebra/DeltaAlgebraPerfectionCompletionResidue, RootedExtension/DeltaAlgebra/PerfectPrismDeltaAlgebraCompletionInputs, RootedExtension/DeltaAlgebra/DeltaAlgebraPerfectionPowerComplete, RootedExtension/DeltaAlgebra/PerfectPrismDeltaAlgebraPowerInputs, RootedExtension/DeltaAlgebra/PerfectPrismDeltaAlgebraDiscrete, RootedExtension/DeltaAlgebra/DeltaAlgebraPerfectionCompletionRestriction, RootedExtension/DeltaAlgebra/DeltaAlgebraPerfectionPDCompletionMap, RootedExtension/DeltaAlgebra/DeltaAlgebraPerfectionPDH0Comparison, RootedExtension/DeltaAlgebra/PerfectPrismDeltaAlgebraPDCompletelyFlat |
| `Andre/Envelope/Normalized` | 18 | RootedExtension/Division/DeltaDivisionFiniteNormalizedPowerEquiv, RootedExtension/Division/DeltaDivisionFiniteNormalizedStepFlat, RootedExtension/Division/DeltaDivisionFiniteNormalizedTowerMaps, RootedExtension/Division/DeltaDivisionFiniteNormalizedTowerFlat, RootedExtension/Division/DeltaDivisionFirstCoefficientPowerEquiv, RootedExtension/Division/DeltaDivisionFiniteNormalizedInitialPowerEquiv, RootedExtension/Division/DeltaDivisionFiniteNormalizedInitialFlat, RootedExtension/Division/DeltaDivisionFiniteNormalizedBaseFlat, RootedExtension/Division/DeltaDivisionFiniteNormalizedDirectLimit, RootedExtension/Division/DeltaDivisionFiniteNormalizedDirectLimitAlgebra, RootedExtension/Division/DeltaDivisionNormalizedDirectLimitEvaluation, RootedExtension/Division/DeltaDivisionNormalizedDirectLimitKernel, RootedExtension/Division/DeltaDivisionInfiniteWittNormalization, RootedExtension/Division/DeltaDivisionInfiniteWittNormalizationAlgebra, RootedExtension/Division/DeltaDivisionNormalizedDirectLimitModule, RootedExtension/Division/DeltaDivisionNormalizedDirectLimitFlat, RootedExtension/Division/DeltaDivisionNormalizedTensorTransition, RootedExtension/Division/DeltaDivisionNormalizedDirectLimitFaithfullyFlat |
| `Andre/Envelope/DivisionResidue` | 4 | RootedExtension/Division/DeltaAdjoinDivisionResiduePresentation, RootedExtension/Division/DeltaAdjoinDivisionResidueFlat, RootedExtension/Division/DeltaDivisionSourceResidueTensor, RootedExtension/Division/DeltaAdjoinDivisionResidueRegular |
| `Andre/Envelope/RootRelation` | 16 | RootedExtension/DeltaRoot/DeltaRootRelationCoefficientQuotient, RootedExtension/DeltaRoot/DeltaRootRelationKoszul, RootedExtension/DeltaRoot/DeltaRootPartialQuotient, RootedExtension/DeltaRoot/DeltaRootSubsetQuotient, RootedExtension/DeltaRoot/DeltaRootFiniteRegularSequence, RootedExtension/DeltaRoot/DeltaRootSubsetFlat, RootedExtension/DeltaRoot/DeltaRootFiniteTor, RootedExtension/DeltaRoot/DeltaRootFiniteKoszulCoefficients, RootedExtension/DeltaRoot/DeltaRootFiniteKoszulAugmentation, RootedExtension/DeltaRoot/DeltaRootRelativeKoszul, RootedExtension/DeltaRoot/DeltaRootRelationCoefficientFlat, RootedExtension/DeltaRoot/DeltaRootAdjoinDivisionResidue, RootedExtension/DeltaRoot/DeltaRootAdjoinDivisionVariables, RootedExtension/Supplement/DeltaRoot/DeltaRootPowerSubsetRegular, RootedExtension/Supplement/DeltaRoot/DeltaRootPowerSubsetBaseQuotient, RootedExtension/Supplement/DeltaRoot/DeltaRootPairInputRegular |
| `Andre/Envelope/JetRegularity` | 7 | RootedExtension/Division/DeltaDivisionFirstJetResidueRegular, RootedExtension/Division/DeltaDivisionFirstJetResidueKoszul, RootedExtension/Division/DeltaDivisionFiniteEvaluationRegular, RootedExtension/Division/DeltaDivisionMappedEvaluationKoszul, RootedExtension/Supplement/Division/DeltaDivisionFiniteStageTailQuotient, RootedExtension/Supplement/Division/DeltaDivisionFiniteRelationsRegular, RootedExtension/Supplement/Division/DeltaPDivisionNextInput |
| `Andre/Envelope/NormalizedStep` | 6 | RootedExtension/Division/DeltaDivisionNormalizedStepKoszul, RootedExtension/Division/DeltaDivisionNormalizedStepSourceQuotient, RootedExtension/Division/DeltaDivisionNormalizedAmbientSource, RootedExtension/Supplement/Division/DeltaDivisionNormalizedStepQuotientComparison, RootedExtension/Supplement/Division/DeltaDivisionNormalizedStepResolution, RootedExtension/Supplement/Division/DeltaDivisionNormalizedStepTor |
| `Andre/Envelope/JetKoszul` | 10 | RootedExtension/Division/DeltaDivisionFiniteJetRegularity, RootedExtension/Division/DeltaDivisionFiniteResidueKoszul, RootedExtension/Division/DeltaDivisionFiniteWittFamilyKoszul, RootedExtension/Division/DeltaDivisionFiniteJetFamilyKoszul, RootedExtension/Supplement/Division/DeltaDivisionFiniteJetSubset, RootedExtension/Supplement/Division/DeltaDivisionFiniteJetFamilyRegularity, RootedExtension/Supplement/Division/DeltaDivisionFiniteJetStepResolution, RootedExtension/Supplement/Division/DeltaDivisionFiniteJetStepComparison, RootedExtension/Supplement/Division/DeltaDivisionFiniteJetStepScalarTower, RootedExtension/Supplement/Division/DeltaDivisionFiniteJetStepTor |
| `Andre/Envelope/SourceEvaluation` | 7 | RootedExtension/Division/DeltaDivisionSourceGraphKoszul, RootedExtension/Division/DeltaDivisionSourceFiniteTor, RootedExtension/Division/DeltaDivisionSourceEvaluationColimit, RootedExtension/Division/DeltaDivisionSourceEvaluationColimitTor, RootedExtension/Supplement/Division/DeltaDivisionEvaluationFiniteSupport, RootedExtension/Supplement/Division/DeltaDivisionEvaluationFiniteSupportColimit, RootedExtension/Supplement/Division/DeltaDivisionBoundedSupportColimit |
| `Andre/Envelope/RootResidueKoszul` | 6 | RootedExtension/DeltaRoot/DeltaRootFirstEvaluationKoszul, RootedExtension/DeltaRoot/DeltaRootFiniteResidueKoszul, RootedExtension/DeltaRoot/DeltaRootFirstResidueFamilyKoszul, RootedExtension/DeltaRoot/DeltaRootFiniteResidueSourceTor, RootedExtension/Supplement/DeltaRoot/DeltaRootFiniteFamilyRegular, RootedExtension/Supplement/DeltaRoot/DeltaRootPairRawRegular |
| `Andre/Envelope/FamilyEvaluation` | 6 | RootedExtension/Division/DeltaDivisionFiniteFamilyResidueKoszul, RootedExtension/Division/DeltaDivisionFiniteFamilyEvaluation, RootedExtension/Division/DeltaDivisionFamilySourceEvaluationColimit, RootedExtension/Supplement/Division/DeltaDivisionFiniteSubfamilyRegular, RootedExtension/Supplement/Division/DeltaDivisionFiniteSubfamilyTor, RootedExtension/Supplement/Division/DeltaDivisionSourceFiniteColimit |
| `Andre/Envelope/RootFamilySource` | 9 | RootedExtension/DeltaRoot/DeltaRootFamilySourceColimitTor, RootedExtension/DeltaRoot/DeltaRootFamilyResidueSourceDerived, RootedExtension/DeltaRoot/DeltaRootFamilySourceCoefficientResidue, RootedExtension/DeltaRoot/DeltaRootFamilySourceQuotientFlat, RootedExtension/DeltaRoot/DeltaRootFamilySourcePDResidue, RootedExtension/DeltaRoot/DeltaRootFamilySourceIteratedResidue, RootedExtension/PerfectPrismRootFamilySourceInputs, RootedExtension/Supplement/DeltaRoot/DeltaRootFamilyRegularGhost, RootedExtension/Supplement/DeltaRoot/DeltaRootFamilyRawCompletelyFlat |
| `Andre/Envelope/MonicSource` | 14 | MonicPrismaticCoefficient, MonicPrismaticRawResidue, MonicPrismaticQuotientFlat, MonicPrismaticPDReduction, MonicPrismaticIteratedResidue, MonicPrismaticSourceComplete, MonicPrismaticCanonicalPowerResidue, MonicPrismaticRawSourceComparison, MonicPrismaticRawCoefficients, MonicPrismaticSourceNonpositive, MonicPrismaticSourceCompletionH0, MonicPrismaticRawCompletionRestriction, MonicPrismaticRawPDComparison, MonicPrismaticSourcePowerInputs |
| `Andre/Envelope/RootSource` | 16 | RootedExtension/DeltaRoot/DeltaRootResidueSourceColimitTor, RootedExtension/DeltaRoot/DeltaRootResidueSourceDerived, RootedExtension/DeltaRoot/DeltaRootSourceCoefficientResidue, RootedExtension/DeltaRoot/DeltaRootSourceQuotientDerived, RootedExtension/DeltaRoot/DeltaRootSourceQuotientFlat, RootedExtension/DeltaRoot/DeltaRootSourceQuotientSingle, RootedExtension/DeltaRoot/DeltaRootSourceCoefficientModels, RootedExtension/DeltaRoot/DeltaRootSourceCoefficientSquare, RootedExtension/DeltaRoot/DeltaRootSourcePDReduction, RootedExtension/DeltaRoot/DeltaRootSourcePDResidue, RootedExtension/DeltaRoot/DeltaRootSourceIteratedCompletionResidue, RootedExtension/DeltaRoot/DeltaRootSourcePowerResidue, RootedExtension/DeltaRoot/DeltaRootSourceCanonicalPowerResidue, RootedExtension/DeltaRoot/DeltaRootSourceRegularGhost, RootedExtension/IteratedPDH0Reflection, RootedExtension/DeltaRoot/DeltaRootSourceIteratedCompletionComplete |
| `Andre/Perfection/PerfectPrismMonic` | 9 | PerfectPrismMonicCandidate, PerfectPrismMonicSourceDiscrete, PerfectPrismMonicRawPDCompletelyFlat, PerfectPrismMonicPDPerfectionInputs, PerfectPrismMonicPrismCompletelyFlat, PerfectPrismMonicPrismResidue, PerfectPrismMonicQuotientReduction, PerfectPrismMonicPerfectoidCompletelyFlat, PerfectPrismMonicRootedExtension |
| `Andre/PowerRootEnvelope/InputCategory` | 2 | Remark715/BoundedPrismInputCategory, Remark715/Unoriented/Category |
| `Andre/PowerRootEnvelope/Completion` | 9 | Remark715/CompletelyFlatRegularReduction, Remark715/CompletelyFlatRegularAlgebraReduction, Remark715/CompletelyFaithfulPairReduction, Remark715/PDCompletionCoordinateEquiv, Remark715/PDCompletionKilledCoordinates, Remark715/PDCompletionPairResidue, Remark715/PrimeAdicCompletionUniversal, Remark715/PrimeAdicCompletionPrincipalQuotient, Remark715/PrimeAdicCompletionQuotientExchange |
| `Andre/PowerRootEnvelope/Varpi` | 6 | Remark715/PerfectPrismVarpi, Remark715/MonicModPrimePDEnvelope, Remark715/PerfectPrismMonicModPrimePDEnvelope, Remark715/MonicPDFlat, Remark715/PerfectPrismVarpiFrobeniusQuotient, Remark715/PerfectPrismFrobeniusPairToVarpi |
| `Andre/PowerRootEnvelope/DeltaDivisionWitt` | 11 | Remark715/DeltaDivisionCoefficientAut, Remark715/DeltaDivisionCoefficientPDCompletion, Remark715/DeltaDivisionWittEvaluation, Remark715/DeltaDivisionPairResidueWitt, Remark715/DistinguishedWittDenominator, Remark715/DistinguishedWittDenominatorNaturality, Remark715/DeltaDivisionFrobeniusPResidueEquiv, Remark715/DeltaPDivisionIdealPDComparison, Remark715/DeltaDivisionFiniteModPrimeTail, Remark715/RawDeltaDivisionPDUniversal, Remark715/RawDeltaDivisionPDTorsionComparison |
| `Andre/PowerRootEnvelope/DeltaDivisionResidue` | 11 | Remark715/DeltaDivisionFrobeniusCompletedResidue, Remark715/DeltaDivisionFrobeniusCompletionToRaw, Remark715/DeltaDivisionCompletionPResidue, Remark715/DeltaDivisionCompletionPrincipalPD, Remark715/DeltaDivisionFiniteModPrimeRegularity, Remark715/DeltaDivisionFinitePrimeQuotients, Remark715/DeltaDivisionFiniteRegularStep, Remark715/DeltaDivisionFrobeniusResidue, Remark715/DeltaDivisionUnaryFiniteInitialRegular, Remark715/DeltaDivisionUnaryRawRegular, Remark715/DeltaDivisionUnaryRawPairRegular |
| `Andre/Envelope/PDivision` | 23 | RootedExtension/Supplement/Division/DeltaPDivisionSecondRelationRegular, RootedExtension/Supplement/Division/DeltaPDivisionFiniteStageRegular, RootedExtension/Supplement/Division/DeltaPDivisionRawRegular, RootedExtension/Supplement/Division/DeltaPDivisionRawEmbedding, RootedExtension/Supplement/Division/DeltaPDivisionFactorialEquiv, RootedExtension/Supplement/Division/DeltaPDivisionRawPrincipal, RootedExtension/Supplement/Division/DeltaPDivisionFamilyStep, RootedExtension/Supplement/Division/DeltaPDivisionTwoStep, RootedExtension/Supplement/Division/DeltaPDivisionPairRegular, RootedExtension/Supplement/Division/DeltaPDivisionFiniteRelationsRegular, RootedExtension/Supplement/Division/DeltaPDivisionFiniteEvaluationRegular, RootedExtension/Supplement/Division/DeltaPDivisionSourceFiniteTor, RootedExtension/Supplement/Division/DeltaPDivisionDividedPowers, RootedExtension/Supplement/Division/DeltaPDivisionFiniteKoszulComparison, RootedExtension/Supplement/Division/DeltaPDivisionFiniteKoszulTransitions, RootedExtension/Supplement/Division/DeltaPDivisionFiniteKoszulHomologyDiagram, RootedExtension/Supplement/Division/DeltaPDivisionSequentialKoszul, RootedExtension/Supplement/Division/DeltaPDivisionFiniteQuotientColimit, RootedExtension/Supplement/Division/DeltaPDivisionRawRelativeModP, RootedExtension/Supplement/Division/DeltaPDivisionRawResidueFlat, RootedExtension/Supplement/Division/DeltaPDivisionResidueMap, RootedExtension/Supplement/Division/DeltaPDivisionSequentialKoszulAugmentation, RootedExtension/Supplement/Division/DeltaPDivisionSequentialKoszulUnit |
| `Andre/PowerRootEnvelope/DividedPowerPrime` | 14 | Remark715/PrincipalDPRingEquiv, Remark715/PrimeDividedPowerQuotient, Remark715/FactorialModPrimeDividedPowers, Remark715/DividedPowerPrimeShift, Remark715/DividedPowerPrimeTensor, Remark715/DividedPowerPrimeFiniteTensor, Remark715/DividedPowerPrimeFiniteUniversal, Remark715/DividedPowerPrimeGenerators, Remark715/DividedPowerPrimeFinitePresentation, Remark715/DividedPowerPrimePresentation, Remark715/DividedPowerPrimeUniversal, Remark715/PrincipalDPFree, Remark715/DividedPowerRegularQuotient, Remark715/DividedPowerProjectiveCoefficientQuotient |
| `Andre/PowerRootEnvelope/PrincipalDP` | 9 | Remark715/RankOneDPCoefficientQuotient, Remark715/PrincipalDPCoefficientQuotient, Remark715/PrincipalDPIdealQuotient, Remark715/RegularPrincipalModPrimeDividedPowers, Remark715/PrincipalDPPositiveUniversal, Remark715/PrincipalDPTransport, Remark715/RegularPrincipalModPrimeUniversal, Remark715/PrincipalDPTruncatedPresentation, Remark715/PrincipalDPPositiveQuotient |
| `Andre/PowerRootEnvelope/PowerRootPolynomial` | 12 | Remark715/PowerRootExponents, Remark715/PowerRootPolynomial, Remark715/PowerRootPolynomialDelta, Remark715/PowerRootPolynomialCoordinates, Remark715/PowerRootPolynomialFractionBasis, Remark715/PowerRootMonicQuotient, Remark715/PowerRootPolynomialModPrime, Remark715/PowerRootCoefficientQuotient, Remark715/PowerRootPolynomialPerfectDelta, Remark715/PowerRootCoefficientIdealQuotient, Remark715/PowerRootExponentEvaluation, Remark715/PowerRootPolynomialModScalar |
| `Andre/PowerRootEnvelope/PowerRootInput` | 15 | Remark715/PowerRootMonicModPrimePDEnvelope, Remark715/PowerRootMonicPDFlat, Remark715/PowerRootCoefficientPDEnvelope, Remark715/PowerRootCoefficientPDRegularReduction, Remark715/PowerRootFrobeniusPairVarpiInput, Remark715/PowerRootCoefficientPDProjectiveReduction, Remark715/PowerRootFrobeniusFactors, Remark715/PowerRootPolynomialUniversal, Remark715/PowerRootEquationQuotient, Remark715/PowerRootEquationCompletionUniversal, Remark715/PowerRootMonicCompletedInput, Remark715/PowerRootMonicCompletedInputExt, Remark715/PowerRootPolynomialDeltaUniversal, Remark715/PowerRootPolynomialBoundedPrismLift, Remark715/PowerRootPolynomialPrismLift |
| `Andre/PowerRootEnvelope/VarpiPD` | 5 | Remark715/PerfectPrismVarpiRegular, Remark715/PerfectPrismVarpiRootInput, Remark715/PerfectPrismVarpiPDComparison, Remark715/PerfectPrismVarpiNativePDEnvelope, Remark715/PerfectPrismVarpiNativePDFlat |
| `Andre/PowerRootEnvelope/PrincipalPair` | 5 | Remark715/RegularTripleQuotientStep, Remark715/PrincipalPairPowerRegular, Remark715/PrincipalPairCompletionRegular, Remark715/PrincipalCompletionResidue, Remark715/PrincipalPairCompletionFirstRegular |
| `Andre/PowerRootEnvelope/CompletionPD` | 8 | Remark715/PowerRootPrismFrobeniusResidue, Remark715/PowerRootPrismMonicCompletionPD, Remark715/PowerRootPrismMonicVarpiPDComparison, Remark715/PowerRootPrismMonicVarpiFlat, Remark715/PowerRootVarpiPrimeFrobeniusPD, Remark715/PowerRootPrimeFrobeniusPDEnvelope, Remark715/PowerRootMonicModPairRegular, Remark715/PowerRootPrismMonicRawRegular |
| `Andre/PowerRootEnvelope/Unconditional/Residue` | 12 | Remark715/Unconditional/MonicPDEnvelope, Remark715/Unconditional/VarpiPDReduction, Remark715/Unconditional/PowerRootResidueKoszul, Remark715/Unconditional/PowerRootResidueSource, Remark715/Unconditional/PowerRootCoefficientReduction, Remark715/Unconditional/PowerRootQuotientDerived, Remark715/Unconditional/PowerRootAResidue, Remark715/Unconditional/InitialCoefficient/Comparison, Remark715/Unconditional/InitialCoefficient/RawResidue, Remark715/Unconditional/RegularityBoundary, Remark715/Unconditional/MonicPDFlat, Remark715/Unconditional/RawInitialRegular |
| `Andre/PowerRootEnvelope/Initiality` | 9 | Remark715/PerfectPrismVarpiNativePDFormula, Remark715/PerfectPrismVarpiPDUniversalUnconditional, Remark715/PerfectPrismVarpiPDUniversal, Remark715/PowerRootPrismMonicSourceInitiality, Remark715/PowerRootPrismMonicAbsoluteUniversal, Remark715/Unoriented/Initial, Remark715/Unoriented/SourceInitiality, Remark715/Unoriented, Remark715/PowerRootPrismMonicCoefficientComparison |
| `Andre/Variants/Auxiliary` | 15 | Variants/PrincipalDPQuotientUniversal, Variants/DeltaDivisionCoefficientAutComposition, Variants/SemilinearTensorBaseChange, Variants/PrincipalPDSourceTransport, Variants/MonicPerfectPrismPDEnvelope, Variants/RegularQuotientCompleteFaithful, Variants/PerfectedDeltaAlgebraQuotientFaithful, Variants/MonicPrismaticFiniteSubfamilyTor, Variants/MonicPrismaticBoundedSupportTor, Variants/BoundedPrismInputRigidity, Variants/FaithfullyFlatNilpotentSquare, Variants/CompletelyFaithfullyFlatPrincipalPower, Variants/MonicRootedBaseEquiv, Variants/FiniteMonicRootedExtension, Variants/MonicFrobeniusCoefficient |
| `Andre/PowerRootEnvelope/Unconditional/Localization` | 16 | Remark715/PowerRootDivisionFrobeniusFactors, Remark715/Unconditional/FreeCoefficientSquare, Remark715/Unconditional/UnitNumeratorRawRegular, Remark715/Unconditional/LocalizedScalarModule, Remark715/Unconditional/LocalizedEvaluationModule, Remark715/Unconditional/SourceUnitDenominator, Remark715/Unconditional/LocalizedDeltaSourceTarget, Remark715/Unconditional/LocalizedDeltaSourceEvaluation, Remark715/Unconditional/SourceUnitPurity, Remark715/Unconditional/LocalizedDeltaSourceTensor, Remark715/Unconditional/SourceUnitSingle, Remark715/Unconditional/LocalizedDeltaSourcePrimeCone, Remark715/Unconditional/CompletionTorsionDetection, Remark715/Unconditional/SaturatedLocalizationTorsion, Remark715/Unconditional/SourcePrimeConeTorsion, Remark715/Unconditional/ScalarConeRestriction |
| `Andre/PowerRootEnvelope/Unconditional/Source` | 11 | Remark715/Unconditional/PowerRootSourceComplete, Remark715/Unconditional/PowerRootSourcePurity, Remark715/Unconditional/PowerRootRawSourceComparison, Remark715/Unconditional/PowerRootSourceNonpositive, Remark715/Unconditional/PowerRootSourceCompletionH0, Remark715/Unconditional/PowerRootRawCoefficients, Remark715/Unconditional/PowerRootRawCompletionRestriction, Remark715/Unconditional/PowerRootRawPDComparison, Remark715/Unconditional/PowerRootRawPDCompletelyFlat, Remark715/Unconditional/PrimeReductionPurity, Remark715/Unconditional/PowerRootRawPrimeConeCompletion |
| `Andre/PowerRootEnvelope/Unconditional/RawRegular` | 5 | Remark715/Unconditional/PowerRootRawPrimeRegular, Remark715/Unconditional/RawPrimeRegularAllMonic, Remark715/Unconditional/PrincipalSourceRegularity, Remark715/Unconditional/RawPrincipalH0Comparison, Remark715/Unconditional/RawPAdicPairRegular |
| `Andre/PowerRootEnvelope/CompletionPrism` | 15 | Remark715/PowerRootPrismMonicRawPairRegular, Remark715/PowerRootPrismMonicCompletionRegular, Remark715/PowerRootPrismMonicHodgeTateBase, Remark715/PowerRootPrismMonicHodgeTateRoot, Remark715/PowerRootPrismMonicCompletionPrism, Remark715/PowerRootPrismMonicRegularSource, Remark715/PowerRootPrismMonicCompletionUniversal, Remark715/PowerRootPrismMonicRootUniversal, Remark715/PowerRootPrismMonicBoundedResidueRootUniversal, Remark715/PowerRootPrismMonicBasePrismUniversal, Remark715/PowerRootPrismMonicEquationInput, Remark715/PowerRootPrismMonicCompletedEquationInput, Remark715/PowerRootPrismMonicOriginalCompletedInput, Remark715/PowerRootPrismMonicHodgeTateVarpiFlat, Remark715/PowerRootPrismMonicHodgeTateCompletelyFlat |
| `Andre/PowerRootEnvelope/InputUniversal` | 7 | Remark715/PowerRootPrismMonicStandardEquationInput, Remark715/PowerRootPrismMonicStandardCompletedInput, Remark715/PowerRootPrismMonicEquationInputSquare, Remark715/PowerRootPrismMonicOriginalInputSquare, Remark715/PowerRootPrismMonicSourcePrismUniversal, Remark715/PowerRootPrismMonicEnvelopeInitial, Remark715/PowerRootPrismMonicResidueRootUniversal |
| `Andre/PowerRootEnvelope/Unconditional/FrobeniusPD` | 3 | Remark715/Unconditional/PowerRootHodgeTateReduction, Remark715/Unconditional/FrobeniusTensorPD, Remark715/Unconditional/FullFrobeniusPD |
| `Andre/PowerRootEnvelope/PerfectionFaithful` | 7 | Remark715/PowerRootPrismMonicHodgeTateCompletelyFaithfullyFlat, Remark715/PowerRootPrismMonicCompletionPairFlat, Remark715/PowerRootPrismMonicCompletionPairFaithful, Remark715/PowerRootPrismMonicCompletedPerfection, Remark715/PowerRootPrismMonicHodgeTateComplete, Remark715/PowerRootPrismMonicPerfectionPairFaithful, Remark715/PowerRootPrismMonicPerfectionQuotientFaithful |
| `Andre/PowerRootEnvelope/VarpiComparison` | 8 | Remark715/Unconditional/PowerRootCompletionPairFlat, Remark715/VarpiComparison/Flatness, Remark715/VarpiComparison/PDBaseChange, Remark715/VarpiComparison/Candidate, Remark715/VarpiComparison/UnconditionalPD, Remark715/VarpiComparison/UnconditionalCandidate, Remark715/VarpiComparison/PDCompatibility, Remark715/VarpiComparison/PrimeReduction |
| `Andre/Variants/RootedExtension` | 12 | Variants/RawDivisionPDPerfectionComparison, Variants/AutomorphismTensorPullback, Variants/ArbitraryPerfectPrismMonicRootedExtension, Variants/MonicFamilyPowerResidue, Variants/MonicRawPDivision, Variants/MonicFamilyRawRegular, Variants/MonicRawModPFlat, Variants/MonicRawCompletelyFlat, Variants/MonicRawDerivedReduction, Variants/MonicRawPerfectionFlat, Variants/MonicRawPCompletionFlat, Variants/MonicRootedPerfectoidExtension |
| `Andre/PowerRootEnvelope/FrobeniusPullback` | 7 | Remark715/PowerRootPrismMonicFrobeniusBaseChange, Remark715/PowerRootPrismMonicFrobeniusRootAction, Remark715/PowerRootPrismMonicFrobeniusTensorAlgebra, Remark715/PowerRootPrismMonicFrobeniusTensorPD, Remark715/PowerRootPrismMonicFullFrobeniusPullback, Remark715/PowerRootPrismMonicFullFrobeniusPD, Remark715/PowerRootPrismMonicFullFrobeniusPDOfMonic |
| `Andre/Envelope/RootFamilyRaw` | 10 | RootedExtension/Supplement/DeltaRoot/DeltaRootFiniteRawRegular, RootedExtension/Supplement/DeltaRoot/DeltaRootFamilyRawRegular, RootedExtension/Supplement/DeltaRoot/DeltaRootFrobeniusCoefficient, RootedExtension/Supplement/DeltaRoot/DeltaRootRawModPFlat, RootedExtension/Supplement/DeltaRoot/DeltaRootRawCoefficientBaseChange, RootedExtension/Supplement/DeltaRoot/DeltaRootRawRelativeModPKoszul, RootedExtension/Supplement/DeltaRoot/DeltaRootRawRelativeDerivedModP, RootedExtension/Supplement/DeltaRoot/DeltaRootRawRelativeCompletionModP, RootedExtension/Supplement/DeltaRoot/DeltaRootFamilyRelativeModP, RootedExtension/Supplement/DeltaRoot/DeltaRootFamilyCompletedModPFlat |
| `Andre/Envelope/PDivisionSource` | 8 | RootedExtension/Supplement/Division/DeltaPDivisionSourceColimitTor, RootedExtension/Supplement/Division/DeltaPDivisionSourceTensor, RootedExtension/Supplement/Division/DeltaPDivisionSourcePrincipal, RootedExtension/Supplement/Division/DeltaPDivisionSourceDerivedPrincipal, RootedExtension/Supplement/Division/DeltaPDivisionSourceTensorRegular, RootedExtension/Supplement/Division/DeltaPDivisionSourceTensorCompletion, RootedExtension/Supplement/Division/DeltaPDivisionSourceTensorDelta, RootedExtension/Supplement/Division/DeltaPDivisionSourceTensorCompletionDelta |
| `Andre/Transfinite/Limit` | 6 | Transfinite/TorsionBound, Transfinite/CompletedMaps, Transfinite/PresentationColimit, Transfinite/PerfectoidCompletionColimit, Transfinite/RootClosure, Transfinite/OmegaOne |
| `Andre/Transfinite/Tower` | 11 | Transfinite/AlgebraColimit, Transfinite/CountableRelations, Transfinite/Terminal, Transfinite/AlgebraCategory, Transfinite/Existence, Transfinite/SingleRoot, Transfinite/FamilySaturation, Transfinite/FamilyExtension, Transfinite/Theorem714, Transfinite/DirectedCompletion, Transfinite/Basic |
| `Andre/Variants/ArbitraryFamily` | 14 | Variants/MonicPrismaticArbitraryResidue, Variants/ArbitraryMonicPrismaticCoefficientReduction, Variants/ArbitraryMonicPrismaticQuotientDerived, Variants/ArbitraryMonicPrismaticQuotientFlat, Variants/ArbitraryMonicPrismaticPDReduction, Variants/ArbitraryMonicPrismaticIteratedResidue, Variants/ArbitraryMonicPrismaticCanonicalPowerResidue, Variants/ArbitraryMonicPrismaticSourcePowerInputs, Variants/ArbitraryPerfectPrismMonicSourceDiscrete, Variants/ArbitraryPerfectPrismMonicRawPDCompletelyFlat, Variants/ArbitraryPerfectPrismMonicPDPerfectionInputs, Variants/ArbitraryPerfectPrismMonicPrismCompletelyFlat, Variants/ArbitraryPerfectPrismMonicPrismResidue, Variants/ArbitraryPerfectPrismMonicPerfectoidCompletelyFlat |
| `Semiperfectoid/RootEnvelope/Source` | 19 | RE/BoundedSupport/DeltaDivisionBoundedSupportTor, RE/BoundedSupport/DeltaRootBoundedSupportResidueDerived, RE/BoundedSupport/DeltaRootBoundedSupportQuotientFlat, RE/BoundedSupport/DeltaRootBoundedSupportPDResidue, RE/BoundedSupport/DeltaRootBoundedSupportIteratedResidue, RE/BoundedSupport/DeltaRootBoundedSupportTorInputs, RE/Source/DeltaRootSourceGeneratorPowerReduction, RE/Source/DeltaRootSourceGeneratorPowerComplete, RE/PerfectDeltaRankOneRoots, RE/Source/DeltaRootAdjoinCompatibleRoots, RE/DeltaRootPerfectoidCandidate, RE/DeltaRootPrismBaseMap, RE/Source/DeltaRootDirectPDCompletionComparison, RE/DeltaRootPDCompletedPerfectionComparison, RE/Source/DeltaRootSourceRawComparison, RE/Source/DeltaRootSourceNonpositive, RE/Source/DeltaRootSourceCompletionH0, RE/RootedPresentationSurjectivity, RE/RootedFamilyPerfectoidSurjectivityDescent |
| `Semiperfectoid/RootEnvelope/PerfectPrism` | 10 | RE/BoundedSupport/PerfectPrismRootBoundedSupportPowerInputs, RE/PerfectPrismRootPowerDiscrete, RE/PerfectPrismRootSourceDiscrete, RE/PerfectPrismRootPDCompletelyFlat, RE/PerfectPrismRootPDPerfectionInputs, RE/PerfectPrismRootPrismCompletelyFlat, RE/PerfectPrismRootQuotientReduction, RE/PerfectPrismRootPerfectoidCompletelyFlat, RE/PerfectPrismRootedPerfectoidExtension, RE/RootEnvelopeSurjectivity |
| `Semiperfectoid/RootEnvelope/RawCompletion` | 4 | RE/Source/DeltaRootSourceRawCoefficients, RE/Source/DeltaRootRawCompletionRestriction, RE/Source/DeltaRootRawCompletionReflection, RE/Source/DeltaRootRawCompletedH0Ring |

削除する 31 本（`Andre/RootedExtension/Supplement/` の下）：
AndreCompatibleRootsConditional, DeltaRoot/DeltaRootFamilySourceCanonicalPowerResidue, DeltaRoot/DeltaRootFamilySourcePowerInputs, DeltaRoot/DeltaRootFiniteRelativeModP, DeltaRoot/DeltaRootFirstEvaluationQuotient, DeltaRoot/DeltaRootFirstTwoEvaluationKoszul, DeltaRoot/DeltaRootPCompletedPerfectionFlat, DeltaRoot/DeltaRootPerfectionFaithful, DeltaRoot/DeltaRootPerfectionModuleLimit, DeltaRoot/DeltaRootPerfectionResidueFlat, DeltaRoot/DeltaRootPerfectionStageFlat, DeltaRoot/DeltaRootPerfectionStages, DeltaRoot/DeltaRootSecondRelationRegular, DeltaRoot/DeltaRootSourceCandidateCompletion, DeltaRoot/DeltaRootSourceCandidateFactorization, DeltaRoot/DeltaRootSourceGeneratorPowerModPFlat, DeltaRoot/DeltaRootSourceH0Candidate, DeltaRoot/DeltaRootSourcePerfectionCandidate, DeltaRoot/DeltaRootSourcePerfectionCandidateCompletion, DeltaRoot/DeltaRootSourcePowerResidueDiscrete, DeltaRoot/DeltaRootSourcePowerResidueFaithful, DeltaRoot/DeltaRootSourceRawH0Algebra, DeltaRoot/DeltaRootSourceRawH0Delta, DeltaRoot/DeltaRootSourceSequentialTor, Division/DeltaDivisionFirstResidueFlat, Division/DeltaDivisionResiduePowerCover, Division/DeltaDivisionSecondCoefficientPowerEquiv, Division/DeltaDivisionSecondResidueFlat, PerfectPrismRootFamilySourcePowerInputs, PerfectPrismRootRawFlat, PerfectPrismRootSourcePowerInputs

```bash
set -o pipefail
git log --oneline -1 efc1dc638   # BS-W8b があること
git status --short SerrePositivity/BhattScholze SerrePositivity/BhattScholze.lean SerrePositivity/CLMST scripts/audit_bhatt* scripts/audit_clmst* scripts/audit_andre_* scripts/audit/   # 空であること
DECLS() { git grep -hoE '^(private )?(noncomputable )?(theorem|lemma|def|abbrev|structure|instance|class) [^ ]+' \
  -- 'SerrePositivity/BhattScholze/Andre/*.lean' 'SerrePositivity/BhattScholze/Semiperfectoid/RootEnvelope/*.lean' | sort; }
DECLS > /tmp/bs_w8_decls_before.txt
python3 - <<'PY' > /tmp/bs_w8_decls_deleted.txt
import json, re, pathlib
for m in json.load(open('evidence/bhatt-scholze/bhatt-scholze-codex-w8-merges.json'))['deletes']:
    s = pathlib.Path(m.replace('.', '/') + '.lean').read_text()
    for d in re.findall(r'^(?:@\[[^\]]*\]\s*)?((?:private |local |protected )?(?:noncomputable )?(?:theorem|lemma|def|abbrev|structure|instance|class) \S+)', s, re.M):
        print(d)
PY
python3 evidence/bhatt-scholze/bhatt-scholze-merge-modules.py evidence/bhatt-scholze/bhatt-scholze-codex-w8-merges.json
# 期待値（W8b の作業ツリーで確認）："removed_files": 557, "owned_files_rewritten": 13, "deleted": 31,
#   "audits_unimporting_deleted": {"scripts/audit/bhatt_scholze.lean": 31, "scripts/audit_bhatt_scholze_andre_conditional.lean": 1,
#     "scripts/audit_bhatt_scholze_b4.lean": 30, "scripts/audit_bhatt_scholze_refactoring.lean": 2},
#   "private_renames": 2, "foreign_importers": [], "foreign_imports_without_stub": []、新しいモジュール 52 本（最長 2263 行）
# （BS 作業チャットが efc1dc638 と同じ状態の使い捨て worktree で、作業 A・B と下の重複除去まで適用し、
#   André・RootEnvelope の全モジュール、BS の集約、CLMST の 2 本、KST の 1 本、専用監査 4 本のビルドが通ることを確認済み）
python3 evidence/bhatt-scholze/bhatt-scholze-merge-modules.py evidence/bhatt-scholze/bhatt-scholze-codex-w8-merges.json --apply
```

件数が違う場合は `--apply` せずに報告する。

## 2. 作業 B：専用監査 4 本の移動（スクリプト）

計画は [bhatt-scholze-codex-w8-moves.json](../../../evidence/bhatt-scholze/bhatt-scholze-codex-w8-moves.json)、スクリプトは [bhatt-scholze-move-modules.py](../../../evidence/bhatt-scholze/bhatt-scholze-move-modules.py)。

| 移動元（`Andre/Remark715/`） | 移動先（`Andre/PowerRootEnvelope/Audit/`） |
| --- | --- |
| `Unconditional/InitialCoefficient/Audit` | `InitialCoefficient` |
| `Unoriented/Audit` | `Unoriented` |
| `VarpiComparison/Audit` | `VarpiComparison` |
| `VarpiComparison/UnconditionalAudit` | `VarpiComparisonUnconditional` |

```bash
python3 evidence/bhatt-scholze/bhatt-scholze-move-modules.py evidence/bhatt-scholze/bhatt-scholze-codex-w8-moves.json
# 期待値："moves": 4, "stubs": 0, "foreign_imports_without_stub": []
python3 evidence/bhatt-scholze/bhatt-scholze-move-modules.py evidence/bhatt-scholze/bhatt-scholze-codex-w8-moves.json --apply
find SerrePositivity/BhattScholze -type d -empty -print -delete
# 統合で専用監査の `let modules` 配列の名前が同じ統合先の名前に重なったので、重複を除く（除かないと「対象モジュールの監査漏れ」で落ちる）
python3 evidence/bhatt-scholze/bhatt-scholze-dedupe-audit-modules.py SerrePositivity/BhattScholze/Andre/PowerRootEnvelope/Audit/*.lean
# 期待値：InitialCoefficient・VarpiComparison・VarpiComparisonUnconditional が changed、Unoriented が unchanged
ls SerrePositivity/BhattScholze/Andre/Remark715 SerrePositivity/BhattScholze/Andre/RootedExtension 2>&1 | head -2   # どちらも存在しないこと
```

各監査ファイルの docstring にある実行コマンドのパス（`lake env lean SerrePositivity/BhattScholze/Andre/...`）が古ければ、新しいパスに直す（この 4 本の docstring のこの行だけ）。

## 3. 作業 C：削除した宣言を参照する監査の行を外す（スクリプト）

作業 A は削除した 31 本の import 行を監査から外したが、`let mods` の名前一覧と、その宣言名を調べる行は残っている（領域監査は
`let mods` の名前からソースを読むので、残っていると「no such file」で落ちる）。補助スクリプト
[bhatt-scholze-drop-deleted-audit-lines.py](../../../evidence/bhatt-scholze/bhatt-scholze-drop-deleted-audit-lines.py) が、名前一覧から削除したモジュール名を外し、
`lake env lean -DmaxErrors=100000` で `Unknown constant`・`Unknown identifier` になった名前の `assert_no_sorry`・`#print axioms`・`#print sorries`
の行だけを消す（未知名がなくなるまでくり返す。未知名以外のエラーがあれば止まる）。**作業 A・B の後、BS の全モジュールをビルドしてから**実行する。

```bash
rm -f /tmp/bs_w8_removed_names.txt
python3 evidence/bhatt-scholze/bhatt-scholze-drop-deleted-audit-lines.py evidence/bhatt-scholze/bhatt-scholze-codex-w8-merges.json \
  scripts/audit_bhatt_scholze_refactoring.lean scripts/audit_bhatt_scholze_b4.lean \
  scripts/audit_bhatt_scholze_andre_conditional.lean scripts/audit/bhatt_scholze.lean
# 消した名前がすべて削除した 31 本の宣言であること（出力が空）
sort -u /tmp/bs_w8_removed_names.txt | sed 's/.*\.//' > /tmp/bs_w8_removed_short.txt
grep -oE '[^ .]+$' /tmp/bs_w8_decls_deleted.txt | sort -u > /tmp/bs_w8_deleted_names.txt
comm -23 /tmp/bs_w8_removed_short.txt /tmp/bs_w8_deleted_names.txt
```

`comm` の出力が空でなければ（削除していない宣言の行を消していれば）、その監査の変更を戻して止まり、報告する。

## 4. 禁止事項と受入条件

禁止：公開の宣言名・証明の変更（`private` の 2 件の付け替えはスクリプトが行う）、上の表にないファイルの統合・移動・削除、所有範囲外のファイルの変更
（KST・`scripts/refactor/audit_targets.txt` を含む）、転送スタブの作成。ビルドが失敗した場合は、直さずにエラーをそのまま報告する。

受入条件：BS-W1 §5「作業 3 の後」と同じコマンド一式（BS・CLMST の全モジュールのビルド、全 BS・CLMST 監査、`audit_f5`・`audit_f7`、
`scripts/audit_andre_*.lean`、構造監査、CommutativeAlgebra の 4 モジュール）に加え、次を実行し、すべてエラーなし・終了 0。
ログの全体を `grep -nE "^error|error:|sorryAx"` で確かめてから報告する（`audit_bhatt_scholze_andre_conditional` などの sorryAx の表示は作業前と同じであること）。

```bash
lake build SerrePositivity.BhattScholze SerrePositivity.EInfinity.Perfectoidization.Comparison \
  SerrePositivity.KST.DerivedBlowup.UniversalRegularSequence 2>&1 | tail -2
# KST のモジュールは他レーンの未コミットの変更で失敗することがある。その場合は BS 由来でないことをエラーで確かめて報告する
for d in Andre Andre/OrdinaryRoots Andre/Envelope Andre/Perfection Andre/Transfinite Andre/PowerRootEnvelope \
  Andre/PowerRootEnvelope/Unconditional Andre/PowerRootEnvelope/Audit Andre/Variants Semiperfectoid/RootEnvelope; do
  echo "$d $(ls SerrePositivity/BhattScholze/$d/*.lean | wc -l)"; done
# 期待値は下の注
DECLS > /tmp/bs_w8_decls_after.txt
diff /tmp/bs_w8_decls_before.txt /tmp/bs_w8_decls_after.txt > /tmp/bs_w8_decls.diff
grep '^>' /tmp/bs_w8_decls.diff   # 付け替えた private の 2 行だけ
grep '^<' /tmp/bs_w8_decls.diff | sed 's/^< //' | grep -vxFf /tmp/bs_w8_decls_deleted.txt   # 付け替え前の private の 2 行だけ
lake env lean scripts/audit/bhatt_scholze.lean 2>&1 | tail -1
```

ディレクトリごとの本数の期待値：`Andre` 2（`AndreFlatness`・`MonicRelationRegularSequence`）、`OrdinaryRoots` 2、`Envelope` 16、`Perfection` 2、
`Transfinite` 3、`PowerRootEnvelope` 18、`PowerRootEnvelope/Unconditional` 5、`PowerRootEnvelope/Audit` 4、`Variants` 4（`MonicRootedExtension` を含む）、
`Semiperfectoid/RootEnvelope` 3。

## 5. コミット

三つに分ける（作業 A、作業 B、作業 C）。所有範囲だけを `--only` で渡す。

```bash
set -o pipefail
OWN="SerrePositivity/BhattScholze SerrePositivity/BhattScholze.lean SerrePositivity/CLMST \
  scripts/audit_bhatt_scholze*.lean scripts/audit_clmst*.lean scripts/audit_andre_*.lean scripts/audit/bhatt_scholze.lean scripts/audit/clmst.lean \
  evidence/bhatt-scholze/bhatt-scholze-merge-modules.py evidence/bhatt-scholze/bhatt-scholze-codex-w8-merges.json \
  evidence/bhatt-scholze/bhatt-scholze-codex-w8-moves.json formalization-plans/bhatt-scholze/instructions/bhatt-scholze-codex-w8.md \
  evidence/bhatt-scholze/bhatt-scholze-dedupe-audit-modules.py evidence/bhatt-scholze/bhatt-scholze-drop-deleted-audit-lines.py"
# コミット 1（作業 A の --apply の後。ビルドは作業 C の後にまとめて行う）
git add evidence/bhatt-scholze/bhatt-scholze-codex-w8-merges.json evidence/bhatt-scholze/bhatt-scholze-codex-w8-moves.json formalization-plans/bhatt-scholze/instructions/bhatt-scholze-codex-w8.md \
  evidence/bhatt-scholze/bhatt-scholze-dedupe-audit-modules.py evidence/bhatt-scholze/bhatt-scholze-drop-deleted-audit-lines.py
git commit --only $OWN -m "$(cat <<'EOF'
refactor(bs): merge André and the root-envelope proof by topic and drop the unused Supplement glue

The Thm 7.14 path becomes Andre/{OrdinaryRoots,Envelope,Perfection,Transfinite}. Remark715,
which does not prove the ind-syntomic statement of Rem 7.15, becomes Andre/PowerRootEnvelope
(the original one-root construction and the pd comparison mod varpi). Variants and
Semiperfectoid/RootEnvelope are merged by topic. Supplement keeps its reusable p-division,
Koszul and raw-envelope parts under Andre/Envelope; 31 modules (a duplicate δ-perfection
route and old B4 glue) are deleted. 530 modules become 52. Public declarations and proofs are
unchanged; two duplicate private helpers are renamed. Plan:
formalization-plans/bhatt-scholze-codex-w8-merges.json.

Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>
EOF
)"
# コミット 2（作業 B と重複除去の後）
git commit --only $OWN -m "$(cat <<'EOF'
refactor(bs): move the PowerRootEnvelope audits under Andre/PowerRootEnvelope/Audit

Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>
EOF
)"
# コミット 3（作業 C とビルド・受入確認の後）
git commit --only scripts/audit_bhatt_scholze_b4.lean scripts/audit_bhatt_scholze_andre_conditional.lean \
  scripts/audit_bhatt_scholze_refactoring.lean scripts/audit/bhatt_scholze.lean -m "$(cat <<'EOF'
chore(bs): drop audit lines for declarations of the deleted Supplement modules

Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>
EOF
)"
```

## 6. 報告してほしいこと

三つのコミットハッシュ、二つの dry-run の出力、作業 C で消した名前の数と §3 の `comm` の出力、ビルドのジョブ数・所要時間・grep の結果、
§4 の追加確認の出力、想定と違ったこと。失敗したときは直さずにエラーをそのまま報告する。
進捗確認チャットへの連絡事項（`scripts/refactor/audit_targets.txt` の旧名）は BS 作業チャットがまとめて伝えるので、Codex は報告に含めるだけでよい。
