# R2-B：Derived・DG・HomologicalAlgebra の処置案（2026-10-27）

概要：R2 正本 §2 の読み取り専用調査。コードの移動・統合・削除・集約変更は実施していない。
方針：import 辺・宣言本体・検査入口・休止文書・旧互換入口を分け、停止窓での処置を提案する。
規約：数学的内容・公開名・型を保持。候補の実施は R2-A の層順序と R2-C/D の所有・監査再編の合意後。
使われ方：[R2 正本](refactoring-infinity-r2.md) への D 側報告。全件・利用元・SHA256 は [機械可読分類表](../r2-b-classification-2026-10-27.json)。
調査開始 HEAD：`54b1a41a6`。正本付録の 555／123／41 本を固定母集団とし、本文ハッシュを全件保存。

## 1. 結論と集計上の補正

- 対象の逆向き import は指定どおり209辺：Derived→SConstruction84・Localizing24・NonConnective19、DG→SConstruction13、Derived→EInfinity5、HA→CA63・Localizing1。独立の141 import先に処置案を付けた。指定127はKST三系統の小計で、別にDerived→Spectra3・Comparison1がある（JSONに補足、R2-Cと連携）。
- 「未登録」は他の project module から直接 import されないという意味。未追跡・未監査・未完成とは区別する。
- DG555中552は既存 `scripts/audit/dg.lean` から直接import済み。89本のtop-level監査だけを見ると落ちる。R2-Dは再帰的監査集合と実行対象を分けて是正する。静的被覆は監査実行成功の証拠ではない。
- HA→CAは単純なディレクトリ全体の並べ替えでは解けない。KoszulはHA.Basic/BaseChange、KoszulResolutionはHA.Tor等を使う。CA.Basic < HA と、CA.Derived応用 > HAを分ける。
- 41本の凍結候補に一般coherent bar計算5本が混ざる。機械抽出のまま全件archiveしない。B1・D-8 covers・I/P/Z・対象別swindleを保持する。

| 母集団 | 登録 | archive | 削除候補 | 診断集約 | 主経路保持/II再利用 |
|---|---:|---:|---:|---:|---:|
| DG 555 | 488 | 67 | 0 | 登録先の検査集約に含む | — |
| HomotopicalAlgebra 123 | 1 | 1 | 121 | — | — |
| 凍結候補41 | — | 20 | 0 | 14 | 5 / 2 |

## 2. 未登録葉の全件分類の基準と処置

- DG登録488 = 既存監査内の検査485 + 一般葉3。検査を本番集約に入れて import 数だけ減らすことはしない。診断/検査manifestで登録と実行を明示する。
- 一般葉3：`DifferentialGraded.Functor.Small`、`Module.MaurerCartanTargetHomDifferential`、`Morita.ScalarExtensionKernelOutputComponents`。前二者は正本集約・厳密公理監査へ。最後は未追跡の所有者作業なので、完成・検証後の登録候補とする。
- DG archive67は本文に `U12e-general（中断）` と明記された検査入口。10本には名前付き定理もあるため削除せず、任意の旧一般経路の検査として保持する。
- HA削除候補121は全件、宣言・example・#commandなし、単一のpublic importでRectification正本を再公開する旧互換入口。正本は残す。直接監査参照15本を正本へ切替し、生成manifest・文書・ツール文字列も検査してから停止窓で削除する。
- `HomotopicalAlgebra.Rectification.Foundations` は既存の任意集約として保持（archive）。未追跡 `Simplicial.RelativeFillerComparison` は一般道具への登録候補で、所有者の検証前には取り込まない。
- 全555＋123本の各行に action・destination・reason・imports・consumers・監査参照・宣言/検査数・SHA256を記録した。将来の追加WIPは母集団と別に再調査する。

## 3. 凍結候補41本と巻き込み防止

- 診断14：CellZeroObstruction、NativeDiskPair、EpsilonPathPrefix／TensorRetraction／TensorSeparation／WordRigidity、EpsilonCellHomotopy／CellRigidity、NativeActionRequirement／EpsilonDiskObstruction／EpsilonRequirement／RepresentableRequirement／UnitRequirement、ResolvedZeroObstruction。
- 主経路保持5＋第II段再利用2：CoherentStages、CoherentStageColimit／HomologyDescent／HomologySupport／KernelDescentの5本は一般bar計算として正本に残す。SuspensionConeComparisonCore・SuspensionCompositionConeComparisonは対象別の全Hom比較として保持する。
- archive20：QuotientEpsilon*の8本、SuspensionFixedCoherenceTypes、DerivedのCoherentActionInput／SquareInput、SuspensionActionのEpsilonSimplexLift／NativeTarget／QuotientNative、NonConnectiveのCoherent*／EdgeIsoTransportの6本。条件付き定理・型は正しい成果として任意の旧経路集約へ保持する。
- 抽出外にも依存する葉がある。SphereClosureQuotientEdge／EdgeIsoAdapter・SuspensionFixedStrictLaws・DGSuspensionSuppliedNativeComparisons／EdgeIsoInvertibility等は旧経路の同伴候補。CellZeroNativeSeparation・NativeActionNonemptinessBoundaryは診断側。正本付録の41本だけで分離完了とはしない。
- 外部の直接利用元20本（集約・一般bar利用を含む）をJSONへ記録。逆依存閉包を点検し、主集約から外した後も再流入しないgateを設ける。一般bar側とB1の依存を切らない。
- archive/診断を主層順序の外に置く場合、その例外境界と専用依存gateをR2-A/Dで明示する。集約から外すだけでは静的import辺の解消に数えない。

## 4. 近接複製・既存候補の対応表

| 候補 | 正本・対応先 | 処置・残る比較 | 利用元・検証・工数 |
|---|---|---|---|
| R28 NativePreservationPosetReduction ↔ Universe | F2/Ind の共通cofinal-poset帰着 | v=uだけではULiftの源/標的一致を保証しない。宇宙移送の保存・反映を証明して特殊化するか、cocone再索引の共通補題を抽出 | JSONの利用元＋F2/Derived compact監査、1–2日 |
| R31 FilteredSpaceBridgeInput ↔ F2/PiCriterion | F2/FilteredExchange/SpacePiData（候補） | DGBarCompactSpacePiData・基点移送・coherent脚の型はdg非依存。定義をF2へ移しBridgeComponents/BridgeStageKernel等の逆importを切る。同型データの再定義は作らない | R27のKanHomotopyGroup基盤の下位化と同時。compact/π監査、1–2日＋基盤 |
| R32 CellZeroObstruction ↔ CellZeroNativeSeparation | 専用診断集約 | zero例のdg豊穣作用の障害と、そのnative比較を区別。定理を同一視しない | 診断build・標準公理監査、R33と合わせ1–2日 |
| R32 NativeDiskPair ↔ NativeEpsilonDiskObstruction | 専用診断集約 | disk例の同値/非同型とε core剛性による全単体作用の障害を分け、共通disk計算だけ共有候補 | 全仮定と反例の終点を保存。同上 |
| R32 EpsilonWordRigidity → CellRigidity → CellHomotopy | 一般ε単語分離＋cell特殊化＋H⁰/native帰結 | 同じ名前の複製ではなく異なる段階。共通係数分離を下位へ、帰結は診断へ | 逆律・負次数・null評価を含める。同上 |
| R34 ExtendTruncationHom → CochainConnectiveLift | HA/ComplexLimits/ConnectiveLift（候補） | lift/inclusion/uniqueを切断の一般論へ。DG単位・tensor非正性は別葉。旧namespaceを保存 | HA/EInfinity/KSTの利用元・型監査、0.5–1日 |
| augmentation旧53組 | DGCommaAug* ↔ DGModuleAugmentation* | 現在49組が両方存在。19組はデータ比較を先行して保持、30組はProp側の照合対象（既共有化分を二重計上しない）。旧4組は既に本文がなく新規統合に数えない | 全53組をJSONへ。型・全Hom射影・augmentation照合を先に、2–5日/族 |

- R28/R31はR2-Aと、R32のD-S所有葉はD-Sと、R34はE2-Sと調整する。DGObjectImage（DGFunctor.Basicのみをimport）をDG/Functor/ObjectImageへ下げる追加候補も記録した。これによりDG.Presentation→Derivedの別の1逆辺を解消できる。

## 5. import先ごとの処置案（209辺、141 import先）

以下の工数は依存族単位であり、各行を単純合算しない。全利用元と各辺の個別処置はJSONを正本とする。移動先は候補パッケージで、R2-A確定後にファイル名を決める。

| 現import先 | 対象辺/利用元 | 処置先 | 工数 |
|---|---:|---|---|
| `CommutativeAlgebra.AdicBoundedTorsion` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.AdicCompletionAlgebraUniversal` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.AdicFaithfulDescent` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.AdicRecurrence` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.AdicRecurrenceInversion` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.Almost.Zero` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.BoundedPowerTorsionQuotient` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.CompatibleRootFamilyIdeal` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.CompatibleRootIdealTensor` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.CompatibleRootPerfectQuotient` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.CompletelyFaithfullyFlatPowers` | 1/1 | split: CA.Basic below HA + CA.Derived applications above HA | 2–4日/族 |
| `CommutativeAlgebra.CompletelyFaithfullyFlatTensor` | 1/1 | split: CA.Basic below HA + CA.Derived applications above HA | 2–4日/族 |
| `CommutativeAlgebra.CompletelyFlatNilpotent` | 2/2 | split: CA.Basic below HA + CA.Derived applications above HA | 2–4日/族 |
| `CommutativeAlgebra.ConormalIdempotentImage` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.FiniteFreeScalarFactorization` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.FiniteLength` | 4/4 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.FiniteLengthSmulSubquotient` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.FiniteParameters` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.FlatPowerQuotientTorsion` | 2/2 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.FlatPowerTorsion` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.IdempotentImageAnnihilator` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.IdempotentImageBaseChange` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.Koszul` | 10/10 | move-target: HomologicalAlgebra.Koszul | 1–2日/族 |
| `CommutativeAlgebra.KoszulResolution` | 4/4 | move-target: HomologicalAlgebra.Koszul | 1–2日/族 |
| `CommutativeAlgebra.LocalizationLattice` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.LocalizationTelescope` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.MappedPrincipalQuotient` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.MinimalGenerators` | 1/1 | split: CA.Basic below HA + CA.Derived applications above HA | 2–4日/族 |
| `CommutativeAlgebra.ModulePowerTorsionBound` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.ParameterRadicalImage` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.PerfectCoefficientTensor` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.PerfectPolynomialFlat` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.PerfectPowerReduced` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.PerfectRadicalIdeal` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.PowTorsion` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.PrincipalAdicFaithfulDescent` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.PrincipalAdicReductionAlgebra` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.PrincipalAdicReductionEquiv` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.PrincipalCoverNumerators` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.QuotientScalarExtension` | 1/1 | split: CA.Basic below HA + CA.Derived applications above HA | 2–4日/族 |
| `CommutativeAlgebra.RegularParameters` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.RegularSequence` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.RegularSequencePowers` | 2/2 | split: CA.Basic below HA + CA.Derived applications above HA | 2–4日/族 |
| `CommutativeAlgebra.ScalarIsogenyInverse` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `CommutativeAlgebra.TensorRingEquiv` | 1/1 | move-target-or-layer: CommutativeAlgebra.Basic below HA | 0.5–1日/族 |
| `EInfinity.BarrattEccles.ShuffleEdges` | 1/1 | move-target: HomologicalAlgebra.Shuffle finite-combinatorics base | 1–3日/族 |
| `EInfinity.BarrattEccles.ShuffleZeroPaths` | 1/1 | move-target: HomologicalAlgebra.Shuffle finite-combinatorics base | 1–3日/族 |
| `EInfinity.BarrattEccles.TripleShuffleCoordinates` | 1/1 | move-target: HomologicalAlgebra.Shuffle finite-combinatorics base | 1–3日/族 |
| `EInfinity.BarrattEccles.TripleShufflePermutation` | 1/1 | move-target: HomologicalAlgebra.Shuffle finite-combinatorics base | 1–3日/族 |
| `EInfinity.Shuffle.SignInversions` | 1/1 | move-target: HomologicalAlgebra.Shuffle finite-combinatorics base | 1–3日/族 |
| `KST.LocalizingInvariants.ArrowStableExact` | 2/2 | move-target: InfinityCategories.Stable.NativeCategories / Lax / Verdier | 2–5日/族 |
| `KST.LocalizingInvariants.CochainConnectiveLift` | 1/1 | split: HomologicalAlgebra.ComplexLimits.ConnectiveLift + DG.Complexes tensor bounds | 0.5–1日 |
| `KST.LocalizingInvariants.CofiberFamilyExactComparison` | 2/2 | move-target: InfinityCategories.Stable.NativeCategories / Lax / Verdier | 2–5日/族 |
| `KST.LocalizingInvariants.CofiberFamilyPrecomposition` | 3/3 | move-target: InfinityCategories.Stable.NativeCategories / Lax / Verdier | 2–5日/族 |
| `KST.LocalizingInvariants.CofiberZeroSourceComparison` | 1/1 | move-target: InfinityCategories.Stable.NativeCategories / Lax / Verdier | 2–5日/族 |
| `KST.LocalizingInvariants.DGAlgebraHomotopyPullbackCoconeIso` | 1/1 | move-target: DifferentialGraded.Algebra.HomotopyPullback | 1–2日/族 |
| `KST.LocalizingInvariants.EquivalenceArrowFamily` | 1/1 | move-target: InfinityCategories.Stable.NativeCategories / Lax / Verdier | 2–5日/族 |
| `KST.LocalizingInvariants.ExactMapPinchedPath` | 1/1 | move-target: InfinityCategories.Stable.NativeCategories / Lax / Verdier | 2–5日/族 |
| `KST.LocalizingInvariants.IdentityLaxVerdier` | 2/2 | move-target: InfinityCategories.Stable.NativeCategories / Lax / Verdier | 2–5日/族 |
| `KST.LocalizingInvariants.LaxDifferenceDComparison` | 1/1 | move-target: InfinityCategories.Stable.NativeCategories / Lax / Verdier | 2–5日/族 |
| `KST.LocalizingInvariants.LaxDifferenceExact` | 1/1 | move-target: InfinityCategories.Stable.NativeCategories / Lax / Verdier | 2–5日/族 |
| `KST.LocalizingInvariants.LaxDifferenceFunctor` | 1/1 | move-target: InfinityCategories.Stable.NativeCategories / Lax / Verdier | 2–5日/族 |
| `KST.LocalizingInvariants.LaxInclusionExact` | 1/1 | move-target: InfinityCategories.Stable.NativeCategories / Lax / Verdier | 2–5日/族 |
| `KST.LocalizingInvariants.LaxSecondProjectionKernel` | 1/1 | move-target: InfinityCategories.Stable.NativeCategories / Lax / Verdier | 2–5日/族 |
| `KST.LocalizingInvariants.LaxSemiorthogonal` | 1/1 | move-target: InfinityCategories.Stable.NativeCategories / Lax / Verdier | 2–5日/族 |
| `KST.LocalizingInvariants.StableCategories` | 1/1 | move-target: InfinityCategories.Stable.NativeCategories / Lax / Verdier | 2–5日/族 |
| `KST.LocalizingInvariants.TammeProjectionEquivalence` | 1/1 | move-source-split: KST.LocalizingInvariants.DerivedGluingComparison | 1–2日 |
| `KST.LocalizingInvariants.VerdierDiagrams` | 1/1 | move-target: InfinityCategories.Stable.NativeCategories / Lax / Verdier | 2–5日/族 |
| `KST.LocalizingInvariants.VerdierSequence` | 2/2 | move-target: InfinityCategories.Stable.NativeCategories / Lax / Verdier | 2–5日/族 |
| `KST.NonConnective.DGKappaConeInput` | 5/5 | move-target: InfinityCategories.Derived.KappaPerfect (DG sums → DG.Module) | 2–4日/族 |
| `KST.NonConnective.DGKappaPerfectInput` | 2/2 | move-target: InfinityCategories.Derived.KappaPerfect (DG sums → DG.Module) | 2–4日/族 |
| `KST.NonConnective.DGKappaResolvedRelativeRoof` | 1/1 | split: Derived.KappaPerfect objectwise data + KST.NonConnective application | 2–4日/族 |
| `KST.NonConnective.DGKappaResolvedYonedaEvaluation` | 1/1 | move-target: InfinityCategories.Derived.KappaPerfect (DG sums → DG.Module) | 2–4日/族 |
| `KST.NonConnective.DGKappaSuspensionInputLaws` | 1/1 | split: Derived.KappaPerfect objectwise data + KST.NonConnective application | 2–4日/族 |
| `KST.NonConnective.DGKappaSuspensionKMap` | 1/1 | split: Derived.KappaPerfect objectwise data + KST.NonConnective application | 2–4日/族 |
| `KST.NonConnective.DGKappaSuspensionProjectionNaturality` | 1/1 | split: Derived.KappaPerfect objectwise data + KST.NonConnective application | 2–4日/族 |
| `KST.NonConnective.DGKappaSwindleInfinity` | 1/1 | move-target: InfinityCategories.Derived.KappaPerfect (DG sums → DG.Module) | 2–4日/族 |
| `KST.NonConnective.DGKappaUnconditionalStageSupply` | 2/2 | split: Derived.KappaPerfect objectwise data + KST.NonConnective application | 2–4日/族 |
| `KST.NonConnective.DGSuspensionEnrichedAction` | 1/1 | archive-consumer: optional legacy suspension adapters | R33内 |
| `KST.NonConnective.DGSuspensionNativeActionInput` | 1/1 | archive-consumer: optional legacy suspension adapters | R33内 |
| `KST.NonConnective.DGSuspensionNativeSquareFamily` | 2/2 | archive-consumer: optional legacy suspension adapters | R33内 |
| `KST.SConstruction.DGAlgebraEnvelopeGenerator` | 1/1 | split: DG.Perfect/Morita base + Derived.Perfect comparisons | 2–4日/族 |
| `KST.SConstruction.DGCellResolvedGraphPerfect` | 1/1 | move-target: InfinityCategories.Derived.CoherentBar.Graph | 1–2日 |
| `KST.SConstruction.DGClosedComparisonIso` | 1/1 | move-target: DifferentialGraded.Functor.Enrichment / Module.Extension | 2–4日/族 |
| `KST.SConstruction.DGClosedIsoConjugation` | 3/3 | move-target: DifferentialGraded.Functor.Enrichment / Module.Extension | 2–4日/族 |
| `KST.SConstruction.DGClosedIsoConjugationLaws` | 3/3 | move-target: DifferentialGraded.Functor.Enrichment / Module.Extension | 2–4日/族 |
| `KST.SConstruction.DGClosedWhiskerComponents` | 1/1 | move-target: DifferentialGraded.Functor.Enrichment / Module.Extension | 2–4日/族 |
| `KST.SConstruction.DGConjugationNaturality` | 2/2 | move-target: DifferentialGraded.Functor.Enrichment / Module.Extension | 2–4日/族 |
| `KST.SConstruction.DGFunctorClosedFamilyIso` | 1/1 | move-target: DifferentialGraded.Functor.Enrichment / Module.Extension | 2–4日/族 |
| `KST.SConstruction.DGFunctorClosedNaturality` | 1/1 | move-target: DifferentialGraded.Functor.Enrichment / Module.Extension | 2–4日/族 |
| `KST.SConstruction.DGFunctorCoherence` | 4/4 | move-target: DifferentialGraded.Functor.Enrichment / Module.Extension | 2–4日/族 |
| `KST.SConstruction.DGFunctorEnrichment` | 5/5 | move-target: DifferentialGraded.Functor.Enrichment / Module.Extension | 2–4日/族 |
| `KST.SConstruction.DGFunctorHomConjugation` | 3/3 | move-target: DifferentialGraded.Functor.Enrichment / Module.Extension | 2–4日/族 |
| `KST.SConstruction.DGFunctorHomElements` | 2/2 | move-target: DifferentialGraded.Functor.Enrichment / Module.Extension | 2–4日/族 |
| `KST.SConstruction.DGFunctorHomPostcomposition` | 1/1 | move-target: DifferentialGraded.Functor.Enrichment / Module.Extension | 2–4日/族 |
| `KST.SConstruction.DGFunctorHomPrecomposition` | 2/2 | move-target: DifferentialGraded.Functor.Enrichment / Module.Extension | 2–4日/族 |
| `KST.SConstruction.DGFunctorHorizontalDG` | 1/1 | move-target: DifferentialGraded.Functor.Enrichment / Module.Extension | 2–4日/族 |
| `KST.SConstruction.DGFunctorNativeComposition` | 4/4 | move-target: InfinityCategories.DoldKanComparison.FunctorEnrichment | 1–3日/族 |
| `KST.SConstruction.DGFunctorNativeCompositionCoherence` | 1/1 | move-target: InfinityCategories.DoldKanComparison.FunctorEnrichment | 1–3日/族 |
| `KST.SConstruction.DGFunctorWhiskering` | 2/2 | move-target: DifferentialGraded.Functor.Enrichment / Module.Extension | 2–4日/族 |
| `KST.SConstruction.DGGluingCellRightAxisPerfectArrow` | 1/1 | move-target: InfinityCategories.Derived.Gluing foundational interface | 2–4日/族 |
| `KST.SConstruction.DGGluingRightAxis` | 1/1 | move-target: InfinityCategories.Derived.Gluing foundational interface | 2–4日/族 |
| `KST.SConstruction.DGGluingRightAxisHom` | 1/1 | move-target: InfinityCategories.Derived.Gluing foundational interface | 2–4日/族 |
| `KST.SConstruction.DGGraphCompositionInputLeft` | 1/1 | move-target: DifferentialGraded.Functor.Enrichment / Module.Extension | 2–4日/族 |
| `KST.SConstruction.DGHomGluingActions` | 1/1 | move-target: InfinityCategories.Derived.Gluing foundational interface | 2–4日/族 |
| `KST.SConstruction.DGHomGluingBimodule` | 2/2 | move-target: InfinityCategories.Derived.Gluing foundational interface | 2–4日/族 |
| `KST.SConstruction.DGHomGluingConeConnectingComparison` | 1/1 | move-target: InfinityCategories.Derived.Gluing foundational interface | 2–4日/族 |
| `KST.SConstruction.DGHomGluingConeFunctor` | 2/2 | move-target: InfinityCategories.Derived.Gluing foundational interface | 2–4日/族 |
| `KST.SConstruction.DGHomGluingConeRightRestriction` | 1/1 | move-target: InfinityCategories.Derived.Gluing foundational interface | 2–4日/族 |
| `KST.SConstruction.DGHomGluingFunctor` | 1/1 | move-target: InfinityCategories.Derived.Gluing foundational interface | 2–4日/族 |
| `KST.SConstruction.DGHomGluingPrimitiveComposition` | 1/1 | move-target: InfinityCategories.Derived.Gluing foundational interface | 2–4日/族 |
| `KST.SConstruction.DGHomGluingStrictSquare` | 1/1 | move-target: InfinityCategories.Derived.Gluing foundational interface | 2–4日/族 |
| `KST.SConstruction.DGHomGluingTargetCone` | 2/2 | move-target: InfinityCategories.Derived.Gluing foundational interface | 2–4日/族 |
| `KST.SConstruction.DGHomGluingTargetContraction` | 1/1 | move-target: InfinityCategories.Derived.Gluing foundational interface | 2–4日/族 |
| `KST.SConstruction.DGKFixedInterface` | 1/1 | split: PerfDGInput/native Hom base → Derived.Input; K-value → KST | 2–4日 |
| `KST.SConstruction.DGKUniverseQuasiEquivalence` | 1/1 | split: DG.Perfect/Morita base + Derived.Perfect comparisons | 2–4日/族 |
| `KST.SConstruction.DGModuleExtensionComposition` | 4/4 | move-target: DifferentialGraded.Functor.Enrichment / Module.Extension | 2–4日/族 |
| `KST.SConstruction.DGModuleExtensionEvaluationTransport` | 1/1 | move-target: DifferentialGraded.Functor.Enrichment / Module.Extension | 2–4日/族 |
| `KST.SConstruction.DGModuleExtensionIdentity` | 1/1 | move-target: DifferentialGraded.Functor.Enrichment / Module.Extension | 2–4日/族 |
| `KST.SConstruction.DGModuleExtensionInputHomComposition` | 3/3 | move-target: DifferentialGraded.Functor.Enrichment / Module.Extension | 2–4日/族 |
| `KST.SConstruction.DGModuleExtensionInputTransport` | 1/1 | move-target: DifferentialGraded.Functor.Enrichment / Module.Extension | 2–4日/族 |
| `KST.SConstruction.DGModuleExtensionParameter` | 2/2 | move-target: DifferentialGraded.Functor.Enrichment / Module.Extension | 2–4日/族 |
| `KST.SConstruction.DGModuleExtensionRightUnitEvaluation` | 1/1 | move-target: DifferentialGraded.Functor.Enrichment / Module.Extension | 2–4日/族 |
| `KST.SConstruction.DGModuleExtensionTripleEvaluation` | 1/1 | move-target: DifferentialGraded.Functor.Enrichment / Module.Extension | 2–4日/族 |
| `KST.SConstruction.DGOdotInput` | 1/1 | move-target: InfinityCategories.Derived.Gluing foundational interface | 2–4日/族 |
| `KST.SConstruction.DGOdotMilnorCornerEvaluation` | 1/1 | move-target: InfinityCategories.Derived.Gluing foundational interface | 2–4日/族 |
| `KST.SConstruction.DGOdotMilnorIdentityValueEquivalences` | 2/2 | move-target: InfinityCategories.Derived.Gluing foundational interface | 2–4日/族 |
| `KST.SConstruction.DGOdotMilnorLaxComparisonRequest` | 1/1 | move-target: InfinityCategories.Derived.Gluing foundational interface | 2–4日/族 |
| `KST.SConstruction.DGOdotVerdierInput` | 1/1 | move-target: InfinityCategories.Derived.Gluing foundational interface | 2–4日/族 |
| `KST.SConstruction.DGParameterConjugation` | 2/2 | move-target: DifferentialGraded.Functor.Enrichment / Module.Extension | 2–4日/族 |
| `KST.SConstruction.DGPerfectRealization` | 3/3 | move-target: DifferentialGraded.Functor.Enrichment / Module.Extension | 2–4日/族 |
| `KST.SConstruction.DGSmallPerfectEnvelopeEquivalence` | 1/1 | split: DG.Perfect/Morita base + Derived.Perfect comparisons | 2–4日/族 |
| `KST.SConstruction.DGSmallPerfectEnvelopeZero` | 1/1 | split: DG.Perfect/Morita base + Derived.Perfect comparisons | 2–4日/族 |
| `KST.SConstruction.DGSmallPerfectFunctorImage` | 1/1 | split: DG.Perfect/Morita base + Derived.Perfect comparisons | 2–4日/族 |
| `KST.SConstruction.DGStandardClosedComparisonIso` | 2/2 | move-target: InfinityCategories.DoldKanComparison.FunctorEnrichment | 1–3日/族 |
| `KST.SConstruction.DGStandardCoherentMap` | 1/1 | move-target: InfinityCategories.DoldKanComparison.FunctorEnrichment | 1–3日/族 |
| `KST.SConstruction.DGStandardFunctorIsoReflection` | 2/2 | move-target: InfinityCategories.DoldKanComparison.FunctorEnrichment | 1–3日/族 |
| `KST.SConstruction.FunctorIsoEquivalenceReflection` | 2/2 | move-target: InfinityCategories.Core.FunctorIsoReflection | 0.5日 |
| `KST.SConstruction.PerfectDGExtensionComposition` | 1/1 | split: DG.Perfect/Morita base + Derived.Perfect comparisons | 2–4日/族 |
| `KST.SConstruction.PerfectDGFullyFaithful` | 2/2 | split: DG.Perfect/Morita base + Derived.Perfect comparisons | 2–4日/族 |
| `KST.SConstruction.PresentedPerfectDGEvaluationNaturality` | 1/1 | split: DG.Perfect/Morita base + Derived.Perfect comparisons | 2–4日/族 |

## 6. 実施順・受入条件

1. R2-Aの層順序（特にCA.Basic・Stable/native関手圏）とR2-Cの移動先を合意。R34・DGObjectImage・DG end/graph/tensor基盤から移す。
2. Stable/lax/Verdier一般論、I/P/Z・可算和、gluingの模型部分を分離。Φ依存のTamme比較は利用側を上げる。S/ν/Kの公開型を保存し、型に現れる基盤とK値を分ける。
3. R28/R31の共有化、shuffle有限組合せの抽出、HA/CAの基礎と導来応用の分離を行う。旧public importだけの入口を残して逆辺が消えたとはしない。
4. R32/R33の診断・archive集約を作り、主経路への再流入gateと専用公理監査を用意。R36の旧互換入口を監査/設定/文書の参照切替後に削除する。
5. R2-Dで下位ディレクトリ監査も含む実行manifestを確定。型のfingerprint・宣言namespace/本文保存・import DAG・元の公開入口の全利用先を検査し、停止窓でmove_module.pyとverify.shを実行する。

- 今回の検証：対象209辺の再計数、555/123/41の全件・分類の排他性・総数、121互換入口の単一import/宣言なし、SHA256、JSON整合、diffチェック。Leanソース変更なしのためlake buildや全verifyは実行しない。
- D側の先行B1は54b1a41a6で完了。D-Sの工程1の結論と旧経路凍結を前提にした調査であり、D-S側の移動を先行実施しない。
- 工数の目安：分類のレビュー0.5–1日、移動/分割は上表の依存族単位。大口のDG/Stable/gluing/HA-CAを直列に全実施する場合は概ね2–4人週＋全体検証窓。R2-A/Cとの分担後に再見積りする。
