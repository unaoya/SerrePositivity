# D レーン：D7 → β3 → β5 → β4

> **v2 の位置づけ（2026-10-19）**：foundations.md §6 の D。D7 の後、β3（Drinfeld 商 = Verdier 商）、β5（D(A)・⊗_A）、β4（gluing = lax pullback）。

## 引き継ぎ（2026-10-21）

### 現在地

- S1〜S7（D7）完了。実境界から Q・A と二微分式を構成し、coslice の直接充填で cofiber の普遍性、任意四角形の双カルテジアン判定、全 fiber/cofiber と有限極限余極限、D(S) の実安定性を証明した。
- 実 suspension・複体シフト・接続射の符号を照合。D3 の標準 cone 三角形との比較、全 distinguished triangle の保存・反映、逆関手・単位・余単位の全整数シフト整合性を持つ三角同値を公開済み。
- β3 完了。実 Verdier over の反転の filtered 性、有限対の全境界・全時刻を保つ実 roof 比較の cofinality と弱ホモトピー同値、任意反転標的への coherent な降下を証明した。
- `dgQuotientNerveProjection_isLocalization` は任意 quasicategory 標的に対する全前合成の充満忠実性・本質的全射性を与える。局所 K-flat 性を元の Hom に仮定しない平坦分解後の商についても `resolvedDGQuotientFunctor_isLocalization` を証明した。
- 全零化完全関手 ∞ 圏との同値、実安定閉包の完全充満包含、商の零化・完全性・実安定性、局所 K-flat 商と平坦分解後の商の実 Verdier 列まで統合・公理監査済み。H⁰ の Verdier 商の同値で代用していない。
- β5：非可換 `Mon (Complex R)` の `D(A)=N_dg(Semifree(A))`、一般小 dg 圏の半自由／射影的模型の実同値と安定性、Perf の実安定性と Perf→D の完全充満包含を公開済み。
- D・Perf の実 graph tensor、単位・合成の全関手比較、包含との比較四角形、graph Morita 不変性、dg 代数の quasi-isomorphism 不変性まで統合・監査済み。H⁰ の同値に加え、全 source shift から全 Hom の準同型性を検証した。
- 二変数の実空間値 Hom と同じ全 Hom 複体の pinched 模型の比較、固定入力ごとの複体値 Hom を構成。`dgNerveOppositeIso` は全 HA 方程式・任意の単体作用を保持する厳密な反対圏比較であり、dg 関手に厳密自然。実反対 ∞ 圏からの反変 Hom も統合・監査済み。
- Morita tensor の同じ逆関手を h Fun 内の三角式付き ∞ 右随伴に昇格。Perf→D の包含との逆関手比較も公開済み。一般 RHom の構成・同定とは区別する。
- 出力の射影性を仮定しない分解の実対象、実比較差、全 Hom の mapping cocone、全パラメータ複体からの指定二射と比較 cochain の実持ち上げ・一意性、cocone の実比較写像を監査済み。実短完全列の次数別分裂から入力 Hom 射影の全準同型性まで個別・集約ビルド成功。最後の4モジュールも統合・公理監査済み。
- 入口：D7 は `Derived/StableTriangulatedEquivalence.lean`、β3 は `DGQuotientLocalization`・`ResolvedDGQuotientVerdierSequence`、β5 は `DGAlgebraDerivedInfinity`・`DGAlgebraPerfectMoritaInfinity`・`DGModuleHomSpaceInfinity`・`DGSemifreeContravariantHomInfinity`・`DGModuleFunctorResolutionProjection`（すべて `Derived/`）。

### 残り（依存順、時間は推定）

- β3 完了（2026-10-21）：局所 K-flat 商と平坦分解後の商の全局所化、全零化完全関手 ∞ 圏の普遍性、実安定閉包の包含を左項とする Verdier 列まで証明・監査済み。次は β5。
- β5：非可換 dg 代数の D(A)、相対 tensor・Hom の ∞ 関手化、Morita 不変性。L4 §26、HA §7.1.2。1〜3 万行、複数日。
- β4：dg gluing の nerve と安定 ∞ 圏の lax pullback の同値。α2b の提供済み lax pullback を読み取り専用で使う。Tamme §1、Kuznetsov–Lunts。1〜2 万行、複数日。

### 主要宣言（名前のみ。正確な型は Lean）

- `IsStable`・`suspensionEquivalence`・`pretriangulated_ho`・`isTriangulated_ho`・`exactFunctor_isTriangulated`。
- `cofiberBoundaryLiftQ_differential`・`cofiberBoundaryLiftA_differential`・`standardCofiberCocone_isColimit`・`derivedInfinityCategory_isStable`。
- `derivedStableHomotopyEquivalenceCommShift`・`derivedStableHomotopyEquivalenceIsTriangulated`。
- `dgModuleNerve_isStable`・`dgRoofCorrespondenceMap`・`dgRoofCorrespondenceFiberIso`・`dgQuotientRoofCorrespondenceProjection_leftFibration`。
- `dgQuotientFixedHomRoofMap_isRightCofinal`・`dgQuotientFixedHomRoofMap_isWeakHomotopyEquivalence`・`dgRoofCorrespondenceMap_piZero_surjective`。
- `dgGeneralLastHornTopResidual_differential`・`dgGeneralLastHornConeResidual_closed`・`dgGeneralLastHornSolution_nonempty_iff_coneResidual_boundary`。
- `dgVerdierTruncatedConeSuccessor_nonempty`・`dgVerdierTruncatedConeData_nonempty`。
- `dgVerdierFiniteJoinCone_nonempty`・`finiteSimplicialOpposite`・`dgVerdierOver_op_isFilteredInfinity`。
- `dgActualRoofFiberReduction_nonempty`・`dgActualRoofClosedCoefficient_square`・`dgActualRoofReducedFiller_exists`。
- `roofRelativeCompositionTriangle_exists`・`roofCompatibleTransportComposite_nonempty`・`RoofCompatibleTransportComposite.boundary`。
- `RoofHomotopyRelativeFiller`・`dgActualRoofHomotopyRelativeFiller_nonempty`。
- `dgQuotientFinite_exists_coefficientFillers`・`dgCoefficientSkeletalStep_nonempty`・`finiteRelativeSkeleton_exists_top`。
- `dgCoefficientSkeletalStage_nonempty`・`dgCoefficientFinitePairs_nonempty`・`dgClosedRoofFinitePairs_nonempty`・`dgActualRoofFinitePairs_nonempty`。
- `HasFiniteHomotopyRelativeFillers.isLeftCofinal`・`isWeaklyContractible_of_finiteNullSpans`。
- `dgRoofCorrespondenceMap_isLeftCofinal`・`dgRoofCorrespondenceMap_isWeakHomotopyEquivalence`・`dgRoofCorrespondenceMap_precompose_kan`。
- `dgInvertingFixedHomRoofMap_isRightCofinal`・`dgInvertingHomDescent_nonempty`・`DGInvertingHomDescent.homMap_restriction`。
- `dgInvertingHomMap_postcomp`・`dgInvertingHomDescentSpace_isContractibleKan`・`dgInvertingHomActionFamilyRestrictionIso`。
- `dgActualRoofVertexSpan_rightInverse`・`dgActualRoofComposition_nonempty`・`actualRoofEvaluation_compositionTriangle_nonempty`。
- `dgActualRoofEvaluationTargetEdge`・`dgQuotientHomFinite_actualRoofLift`・`dgInvertingHomActionFamilyRoofEvaluationIso`。
- `dgFiniteHomotopyDescent_nonempty`・`pinchedClosedPostcomposition_precomposition`・`dgFiniteOreRefinement_nonempty`・`dgFiniteRoofPresentation_nonempty`・`dgFiniteRoofOreData_nonempty`・`pinchedHomCompositionFamily_assoc`・`DGFiniteRoofOreData.compositeDiagram_projection`・`pinchedHomCompositionFamily_closed_post`・`pinchedHomCompositionHomotopy_fixed`・`DGFiniteOreRefinement.compositionHomotopy_h`。
- `dgCoherentHomComparison_slice`・`dgPinchedCompositionPrism_projection`・`dgPinchedCompositionFamilyPrism_precomp`。
- `homotopyCompositionRelativeOver_fixedLeft_exists`・`dgFiniteOreTrianglePrisms_relative_exists`・`dgFiniteRoofCompositionPrisms_exists`。
- `roofLeftFibration_terminalEvaluation_nonempty`・`dgInvertingHomActionFamilyEvaluationIso`・`dgInvertingHomFamilyEvaluation_nonempty`。
- `pinchedFamilyHom_eq_iff_homotopy`・`dgInvertingFamilyDenominator_isIso`・`dgInvertingFiniteRoofComposition_nonempty`・`dgFiniteRoofOreDataPrecomp_compositeDiagram`。
- `dgNerveOppositeIso`・`dgNerveOppositeIso_naturality`・`dgSemifreeContravariantHomInfinity`・`dgModuleFunctorResolutionHomComplex`・`dgModuleFunctorResolutionHom_ext`・`dgModuleFunctorResolutionSourceHomMap_quasiIso`・`complexMappingCoconeMap`・`complexShortExact_quasiIso_projection`・`dgModuleHomSpaceInfinity`・`dgModuleHomSpaceValueEquivalence`・`dgSemifreeHomTargetInfinity`・`dgSemifreeHomSourceInfinity`・`dgMoritaAdjunctionInfinity`・`dgPerfectMoritaRightAdjointInclusionIso`・`dgAlgebraPerfectExtensionInfinity_isQCatEquivalence_of_morita`・`dgPerfectExtensionInclusionIso`・`dgAlgebraPerfectInfinityCategory_isStable`・`dgAlgebraExtensionInfinity_isQCatEquivalence_of_morita`・`dgAlgebraExtensionInfinity_isQCatEquivalence_of_quasiIso`・`dgModuleDerivedFunctor_isQCatEquivalence_of_classical`・`dgAlgebraExtensionInfinity_isExactFunctor`・`dgModuleDerivedFunctor_comparisonIso`・`dgModuleDerivedFunctor_id_iso`・`dgModuleDerivedFunctor_comp_iso`・`dgAlgebraDerivedInfinityCategory_isStable`・`dgModuleDerivedInfinityCategory_isStable`・`dgSemifreeToProjectiveNerve_isQCatEquivalence`・`dgQuotientNerveProjection_isLocalization`・`dgVerdierExactPrecomposition_isQCatEquivalence`・`dgStableClosureNerve_isStable`・`dgStableClosureInclusion_isExactFunctor`・`dgQuotient_isStableVerdierSequence`・`resolvedDGQuotientFunctor_isLocalization`・`resolvedDGVerdierExactPrecomposition_isQCatEquivalence`・`resolvedDGQuotient_isStableVerdierSequence`。

### 依存と提供

- Core・F1・F1B・F2・DGNerve・DoldKanComparison・HomotopyLimits・DifferentialGraded・KST は読み取り専用。
- 提供：Stable の S1〜S6、D(S) の安定性、任意四角形の双カルテジアン判定、D3 の三角同値。
- 編集対象：Stable/・Derived/、両集約と両監査、本計画。明示指示により Derived 計画の D7 状態も更新する。
- **Sp から D への判定補題要求（2026-10-21、未提供）**：[HA Cor. 1.4.2.27](https://www.math.ias.edu/~lurie/papers/HA.pdf) の (3) ⇒ (1) を F3 の定義で使いたい。正確な要求は、`X : SSet.{u}`、`[Quasicategory X] [HasZeroVertex X] [HasFiniteLimits X]`、実関手 `s : X ⟶ loopDiagrams X`、`hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X`、`hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0)` から `IsStable X` を得る一般補題。s は実際の普遍 loop 四角形の全単体族であり、安定性を先取りする既存 loopFunctor の使用は避ける。有限余極限・cofiber の存在と任意 ZeroTriangle の fiber/cofiber 同値を結論として証明し、それらを追加仮定にしない。現存の isStable_of_finite_limits_colimits は有限余極限と全四角形の双カルテジアン判定も要求するので代用できない。Sp が自前で証明する場合は Spectra 配下に置き、Stable/ は編集せず後で D が取り込む。Sp への適用には有限極限の包装と実 loop 関手の同値性がなお必要で、要求の記載を証明済みとは数えない。

### 未コミット

- なし。今回の4モジュールは、実二成分 cocone の短複体・次数別の三分裂式・短完全性・一般の cocone 第一射影の準同型性と、実出力分解 Hom の入力射影の全準同型性を証明し、統合・監査後に保存した。

### 既知の問題

- D7・β3 の零化・平坦模型の対象・集約ビルド成功（9243 jobs）。公理監査は Derived 11823 宣言／1319 モジュール、Stable 12938／1589。許容三公理のみ。今回までの保存対象250新規モジュールは警告なし。Hom 降下・実合成・全選択空間の評価比較の主経路に `ModelCategory SSet` の追加 instance 仮定なし。
- Stable のシフトは実 suspension に由来する。D3 の二切断の誘導シフトとの混同を避け、通常の h の比較同値で三角同値を公開した。
- β3 は H⁰ の Verdier 商の同値や dg 関手の延長だけでは完成しない。実零化・平坦模型との比較、前三角性の cell 分解への反映、平坦分解後の商の実安定性と商関手の完全性は完成。局所 K-flat 商の全 ∞ 関手圏の局所化普遍性は完成。零化完全関手圏の普遍性・実安定閉包の Verdier 列まで完成。平坦分解後の元の Hom の平坦性を仮定しない局所化・全零化完全関手 ∞ 圏の同値・Verdier 列も統合・監査完了。
- import 閉包が壊れたら他レーンを変更して迂回せず停止して報告する。

### 次の一手

- β5：出力分解 Hom の入力射影の準同型性を閉じた。次は `DGModuleFunctorResolutionHomComplex` 上の実 dg 合成・単位・結合律を構成する。全 Hom 複体の tensor をパラメータとし、元・半自由出力の eComp と実比較 cochain を `mappingCocone.lift` に渡す。比較 cochain の二項は既存 `DifferentialGraded/Complexes/TensorEnriched.lean` の `tensorLeftHom` と対応する `tensorRightHom` で片側ずつ tensor し、実 eComp へ後合成する。微分式は `complexMappingCocone_snd_boundary` と cochain の δ_comp、一意性は `dgModuleFunctorResolutionHom_ext` を使う。次数零の自然性だけで全 dg 合成を済ませない。
- 実分解 dg 圏から入力への射影を dg 関手とし、既証明の全 Hom 準同型性と実対象の全射性から dg nerve の同値を得る。同じ逆比較と出力射影を使い、任意 dg 関手の実出力を半自由模型へ運ぶ。対象宇宙が異なる場合は `DGUniverseLift` を使い、全加群型の Small.{u} を仮定しない。
- その後 D(R) 値の Hom、一般 tensor–Hom 随伴・全 coherence、一般双加群の作用と Morita 不変性、Perf の冪等完備性を閉じて β4 へ進む。β4 は提供済み F2 の実 lax pullback を読み取り専用で使う。β3 は局所化・Verdier 列とも完了しており、再実装や承認待ちは不要。

作成日：2026-10-18。状態：S1〜S7（D7）・β3 完了。β5 に進む。
全体の正本は [foundations.md](foundations.md) §1（F3）・§4。
担当は旧 α の A4・A5 と D7。実施経緯・検証結果は各保存単位のコミットメッセージに記す。

## 目標と原典

| 主張 | 原典 | 完成の条件 |
| --- | --- | --- |
| 安定 ∞ 圏の定義 | HA Definition 1.1.1.9 | 零対象、全射の fiber/cofiber の存在、零角の fiber/cofiber 列の同値 |
| 有限極限・余極限による判定 | HA Proposition 1.1.3.4 | S1・S2 以降で実際に使う向きを証明し、未証明の逆向きを主張しない |
| h C の三角構造 | HA Theorem 1.1.2.14 | cofiber 列の像による distinguished triangle、TR1〜TR4、Mathlib Pretriangulated instance |
| 完全関手と自然変換 | HA §1.1.4 | 零・fiber/cofiber 四角形の保存、h の三角関手、完全関手間の自然変換 |
| 四角形の貼り合わせ | HTT Lemma 4.4.2.1 | A2 の join・slice による証明。A6 待ちの箇所が生じれば正確に特定 |
| D(S) の安定性と三角構造の一致 | 上記と D3・N7 | cofiber 四角形の押し出し性も coslice で直接証明し、D3 を三角比較へ昇格 |

HA §1.1 に対応する Kerodon の章はない。原典は定義と命題の照合に用い、引用公理にはしない。

## 工程

| 工程 | ファイル | 必須の到達点 | 状態 |
| --- | --- | --- | --- |
| S1 | `Stable/Pointed.lean` | 零対象、coslice の始対象としての IsColimitCone、IsPushoutSquare、fiber/cofiber 四角形 | 完了 |
| S2 | `Stable/Definition.lean` | HA 1.1.1.9 の安定性、HA 1.1.3.4 の必要な向き | 完了 |
| S3 | `Stable/Suspension.lean` | h C の Σ・Ω 関手、選択の比較、安定な場合の自己同値 | 完了 |
| S4 | `Stable/Pasting.lean`、`Stable/Triangulated.lean` | 四角形の貼り合わせ、cofiber 三角形、TR1〜TR4、Pretriangulated | 完了（貼り合わせ、TR1〜TR4、Pretriangulated・IsTriangulated instance） |
| S5 | `Stable/LongExactSequence.lean` | fiber 列に Hom を適用した長完全列 | 完了（共変・反変、全整数次数、六項部分列の完全性、接続準同型の評価式） |
| S6 | `Stable/ExactFunctor.lean` と関連モジュール | 完全関手、h の三角関手、完全関手間の自然変換 | 完了。零対象・cofiber/fiber 列・全押し出し／引き戻しの保存、CommShift ℤ、IsTriangulated、加法性、自然変換の全整数シフトとの両立・三角形の像の自然変換まで公開 |
| S7（D7） | `Derived/StableTriangulatedEquivalence.lean` | D(S) の安定性と D3 による通常の導来圏の三角構造との一致 | 完了。cofiber の普遍性、任意四角形の双カルテジアン判定、IsStable、実 suspension 由来の全整数シフト、標準 cofiber 三角形の像の同型、全 distinguished triangle の保存・反映、単位・余単位と整合する三角同値 |

## 設計上の決定

- namespace は `SerrePositivity.InfinityCategories`。SSet の実際の頂点・辺・単体的四角形を用いる。
- 零対象は A2e の `IsInitialVertex` と `IsTerminalVertex` の両方を満たす頂点。
- 余極限錐は `sliceUnder`・`sliceUnderEquiv` による coslice の始対象で定義する。
  押し出しは A2g の双対と照合し、単に h C の押し出しへ置き換えない。
- 安定性の定義に三角圏の公理や Σ の自己同値性を入力として追加しない。
- Σ・Ω は極限・余極限の選択から h C 上に構成し、A2f・A3d で選択の比較を証明する。
- distinguished triangle は cofiber 列の像を条件にする。TR4 も独立に受入基準へ含める。
- N7f を既提供とせず、S7 の coslice の直接充填で標準 cofiber の押し出し性を証明した。
- D3 の同値だけで安定性を定義したり、通常の導来圏の三角構造を無条件に移したりしない。
  実際の fiber/cofiber 列との一致を証明し、D2f の CommShift と照合する。
- 公理監査は `scripts/audit_infinity_stable.lean`。許されるのは propext・Classical.choice・Quot.sound。
- 集約 `InfinityCategories/Stable.lean` を作り、共有ルートへの追記はその public import 一行だけ。
  他チャットの変更・既存の未保存差分をコミットに含めない。


## β3：Drinfeld 商と ∞ 圏的 Verdier 商

D7 の後に完了。実零化、平坦模型、Hom 準同型による充満忠実性、Yoneda 模型との同値、前三角 dg 圏と平坦分解後の商の実 dg nerve の安定性、商関手の完全性まで実装。原典は Drinfeld Thm 3.4・Lemma 13.5、HA §1.1.4、Kerodon §6.3。
F1b の `Localization.lean` の `IsLocalization` を入口とし、局所 K-flat な場合は同じ宇宙の任意 quasicategory 標的への
`localizationPrecomposition` が反転関手の全部分 ∞ 圏との同値になることを証明済み。

- L4 §26（archive に移管）の半自由 dg 圏分解・Hom の K-flat 性・商の H⁰ 比較を読むだけで使う。
- 必要な平坦分解を先行し、未分解の path 商が無条件に Verdier 商であるとはしない。
- 前三角 dg 圏の平坦分解後の商の実安定性と商関手の完全性は完成。
  局所 K-flat 商と平坦分解後の商の零化完全関手 ∞ 圏の同値・実安定閉包の Verdier 列まで完成・監査済み。
- H⁰ の Verdier 商の同値だけで ∞ 関手圏の普遍性を済ませない。

## β5：非可換 dg 代数の導来 ∞ 圏

着手済み。非可換 `Mon (Complex R)` の D(A)・Perf(A) の実安定性、graph tensor・Morita 不変性、実二変数 Hom 空間と反変 Hom、一般出力分解の全 Hom 比較まで完成。一般 RHom 随伴は未完。L4 §26 の dg 圏分解と dg 加群の半自由分解を区別し、
一般化は `InfinityCategories/Derived/` に置く（見積もり 1〜3 万行）。

- 非可換 dg 代数 A の半自由 dg 加群から `D(A) := N_dg(Semifree(A))` と Perf(A) を構成する。
- 双加群による相対テンソル・Hom に必要な分解と閉性を証明し、dg 関手を dg nerve に移す。
- 単位・合成・随伴の整合性、Morita 同値による D(A)・Perf(A) の同値を証明する。
- 単体環の Dold–Kan による dg 代数化を確認する。HA §7.1.2 は比較目標であり引用公理にしない。

## β4：dg gluing と lax pullback

β5 の後、提供済みの α2b の Cat_∞ の極限・安定な lax pullback に接続する。
原典は Tamme 2018 §1、Kuznetsov–Lunts。見積もり 1〜2 万行。

- 双加群に沿う gluing の対象・写像複体・合成・微分を具体的に構成する。
- dg nerve から二射影と構造変換を作り、α2b の Fun(Δ¹,−) による lax pullback への比較を作る。
- 比較の完全忠実性・本質的全射性と ∞ 圏的普遍性を証明し、安定性・完全射影を供給する。
- α2b の未提供の極限や h の通常の pullback を完成済みの ∞ lax pullback と扱わない。

## 記録の所在

実施記録・現在地の詳細・型一覧は [archive/infinity-core-stable-log.md](archive/infinity-core-stable-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
