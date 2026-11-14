# §8 perfectoid 化（一般の場合）：リファクタの提案と、形式化の計画の提案（2026-11-12）

作成：ノートのチャット（形式化の調整役ではない）。§2〜§6・§10 と同じ形。**扱いは調整役が判断する。** 事実に推奨を添える。

- 基準：main 22150d511。読み取りだけのエージェントがノートの加筆 2 本、コードの見直し 1 本（件数を含む）。件数のスクリプトはノートのチャットの作業用の場所にある。正規表現で数えたものは「下限」と書く。規模の見立ては推測。
- 原典（pp.63–70）の項目は Not 8.1、Def 8.2、Ex 8.3、Lemma 8.4、Prop 8.5、Lemma 8.6、Def 8.7、Lemma 8.8、Rem 8.9、Prop 8.10、Cor 8.11、Cor 8.12、Prop 8.13、Cor 8.14 の 14 個。
- 二種類の提案：**A. リファクタ（R8-1〜R8-13）**、**B. 形式化の計画（§3 の表と §3.1 の計画上の点）**。

## 0. 規模と中身の分かれ方（確認済み）

- **本体の対象は 45 本・12,240 行。**
  - BS/Perfectoidization 直下 13 本・3,828 行
  - Derived/ 25 本・7,593 行
  - Perfectoid/FiniteProduct 278 行
  - BS/Inputs/PerfectoidizationInterface 58 行
  - EInfinity/Perfectoidization 4 本・453 行
  - SerrePositivity/Inputs/Perfectoidization 30 行
- **本体の sorry は 1 か所だけ**：E3 の `exists_perfectoidizationInterfaceE3`（Inputs/PerfectoidizationInterface:56）。
- **主定理（Paper.Statement）の閉包に入るのは 18 本・5,441 行。**
  - 入る：Interface、IntegralExistence、Derived/Excision、Inputs 2 本、FiniteProduct、CompletedTensor、CompletedBaseChange、CompletedTensorComparison、TensorPerfectoidization、WittPushout、Cone、Finite、RootTower、Excision、ExcisionComparison、ExcisionTor、FiniteComparisonExcision。
  - 入らない：Arc* の 16 本、RootAdjunction、§10 の 5 本、TensorCompatibility、EInfinity/Perfectoidization の 4 本すべて。
  - 今の閉包に EInfinity は 0 本。A9 で E3 を置き換えると、TheoryInterface・BE の模型・KST（台帳 §9）が閉包に入る。
- **drafts の A4〜A7・A9 は 20 本・4,892 行・480 宣言。** sorry を含む宣言は 276（A4 38/71、A5 105/174、A6 83/150、A7 50/82、A9 0/3）。drafts の import 89 本はすべて今の本体に解決する。

## 1. A. リファクタの提案（今あるコードを直す）

### R8-1 E3 界面が三つの型に重なり、共通基盤から BS への逆向きの import がある【推奨：B3（新しい台帳項目、BR26′ に追加）】

- **三つの型**
  - D(R) 版 `PerfectoidizationInterfaceE3`（Derived/Interface:671）
  - CAlg_R 版 `PerfectoidizationInterfaceCAlg`（EInfinity/Perfectoidization/Interface:62、→ DerivedCorollary の `nonempty_e3_of_cAlg`:58）
  - EInfinityTheory 版 `TheoryPerfectoidizationInterface`（TheoryInterface:138、→ `nonempty_e3_of_theory`:194）
- **CAlg_R 版の 3 本（Interface・DerivedCorollary・Comparison、255 行）は、Theory 版（198 行）をほぼ逐語に写したもの。**
  - コードとして使う側は 0（集約だけ）。drafts の A9/Assembly:42 は Theory 版で組み立てている。
  - Theory 版の docstring は CAlg_R 版の写しのまま：「G1 の結論を既存の CAlg_R で述べた BS 界面」（TheoryInterface:134、:102）、冒頭の「Lemma 8.4」（:8。欄は 10-26 に削除済み）。
- **層の逆向き**：`EInfinity/Perfectoidization/Comparison:5`・`TheoryInterface:4` が `BhattScholze.Perfectoidization.Derived.Interface` を import している。共通基盤から BS への逆向きの import は BR26′ の 2 本のほかにこの 2 本がある。
- **推奨**
  - TheoryInterface を `BhattScholze/Perfectoidization/Interface/` へ移す。
  - CAlg_R 版の 3 本は消す（BE の模型を E として渡せば同じものが出る。推測）。
  - 追従が要る記述：設計書（a4-design:12・82・129、a9-design:4・7・27〜31）と、drafts の 10 本・26 行（`PerfectoidizationInterfaceCAlg`・`nonempty_e3_of_cAlg`・`IsDiscrete（Comparison）`。A4/InterfaceFields 8、A5/InterfaceLimitCone 7 ほか）。

### R8-2 Derived/Interface の環の部分を切り出す【推奨：B3（効果が大きい）】

- **Interface.lean の前半は環の話。**
  - Setup の節（:42〜100：`A_R`・`ofAlgebra`・`C_R`・`PerfUnder_u`）
  - Completion の節（:186〜約 376：`completionRing`・`completionUnit`・`completionLift`・`completion_hom_ext`・`ringCompletionFunctor`・`completionFunctor`・`completionTargetEquivalence`）
  - ∞ を使い始めるのは :379 の `restrictCone` から。ファイルの import には InfinityCategories が 5 本ある。
- **環の 7 本が、この前半のためだけに Interface を import している（確認済み）。** ArcPerfectoidBase・RootAdjunction・ArcSite・ArcValuationTilt・IntegralClosureCompletion・IntegralApproximation・PerfectoidFilteredColimit。どれも ∞ の宣言は使っていない。
- **Interface を外したときの閉包**：ArcPerfectoidBase は 586 → 247 本、ArcSite は 679 → 340 本、RootAdjunction は 631 → 292 本になり、どれも InfinityCategories を含まなくなる。
- **§6 にも効く**：BR50 の `Prismatic/CrystallineWittCoefficients` も、この経路だけで ∞ に依存している（605 → 266 本）。
- **推奨**：Setup と Completion の節を環の模块（例 `Perfectoidization/Completion` か `HomologicalAlgebra/DerivedCompletion/PrincipalRing`）に分ける。BR50（`arcPadicIntMap` の移動）と同じ回にする。

### R8-3 IntegralExistence を三つに分けてから動かす【推奨：B3 の配置案を直す】

- B3 の配置案（kerodon-layout 枝の module-paths.csv）は、ファイル全体を `IntegralPerfectoidization/Existence/`（§10）へ移す。
- **中身は三つに分かれる。**
  - :32〜239 InitialLimit：一般の ∞ の補題。`sliceIdentityCone_terminal`:51、`initialValueCone_isLimit`:109 など。外の利用者 0。
  - :240〜407 InitialBridge：Prop 8.5 と Cor 8.14 から「指定の環の perfectoid 化があれば S_perfd は離散でそれに一致する」。`specified_disc`:372。§8 の Derived/Excision（Cor 8.12 の環版）が使う。
  - :408〜509：Thm 1.17(1)・10.11 の存在。
- **丸ごと移すと §8 の Excision が §10 を import することになる。**
- **推奨**：InitialLimit は `InfinityCategories/Kerodon/…/Cofinality` の近くへ、InitialBridge は §8（Interface の隣）へ、存在の部分だけ §10 へ。

### R8-4 同じ名前の宣言（BR39）【推奨：A9（5∞-9）で整理。小さい部分は B3】

| 名前 | 二つの版 | 使う側 |
| --- | --- | --- |
| `exists_perfectoidization_of_integral` | `PerfectoidizationInterface.…`（IntegralExistence:422、F を引数に取る）と `BhattScholze.Inputs.…`（:467、`Classical.choice` で包む） | 包む版は 7 か所（Almost/SupportedQuotient:232、FiniteComparisonExcision:98・148、CLMST 4）。F 版は包む版だけ |
| `perfectoidization_excision_isPullback` | Derived/Excision:499 と :555 | 同じ形。:555 の版は Perfectoidization/Excision:218 と監査だけ |
| `exists_perfectoidization_of_finite` | `BhattScholze.…`（IntegralExistence:491、有限表示を仮定しない）と `SerrePositivity.Inputs.…`（Inputs/Perfectoidization.lean:23、有限表示を仮定する一行の包み） | 包みは Finite.lean:40〜53 の 4 か所だけ |

- 名前空間 `Inputs` が二つある（`SerrePositivity.Inputs` と `SerrePositivity.BhattScholze.Inputs`）。`Inputs.x` がどちらを指すかは、書いた場所の名前空間で変わる。
- `BhattScholze.Inputs` の宣言は今は証明済みの定理で、「入力」ではない。
- **推奨**
  - B3：`SerrePositivity/Inputs/Perfectoidization.lean` を消す。Finite.lean は BS 版を直接呼ぶ（`Perfectoidization` の型の引数はそのまま）。scripts/audit/shared の import も直す。
  - A9：E3 を外すとき、`BhattScholze.Inputs` の定理を `BhattScholze` に移し、互換の alias を残す（CLMST の 6 か所）。F 版は `…_of_interface` に改名する。
  - 外の利用者 0 の宣言：`exists_perfectoidization_of_completed_integral`（:499）と `perfectoidization_excision_difference_surjective`（:510）。

### R8-5 IsPerfectoidization の API（BR21）【推奨：保守（優先）のまま。新しい重複を一つ足す】

- 変化なし：`hom_ext` はまだない（CommutativeAlgebra/Perfectoid/Defs）。CompletedTensor:362〜395 と :475〜500 の逐語の重複（普遍性の証明）も残っている。
- `hf.2 T hT g` と普遍性を手で展開している箇所：8 ファイル・14 か所（正規表現での下限）。TensorCompatibility 4、TensorPerfectoidization 2、CompletedTensor:539、Semiperfectoid/Surjectivity 2 など。
- **新しく見つけた重複**：`IsPerfectoidization.comp_ringEquiv`（Defs:63、旧 CLMST TensorOrder）と `precomp_ringEquiv`（Defs:173）は同じ主張。
  - comp_ringEquiv の利用者は監査（audit_clmst:152）だけ。precomp は本体 6 か所。
  - 前者を消すか、後者の alias にする。

### R8-6 底変換とテンソルの二つの模型（BR22）：調べた結果【推奨：保守のまま】

- **底変換に当たる構成が四つ**：`perfectoidizationTensorBaseChangeMap`（TensorPerfectoidization:391）、`perfectoidizationTensorDiagramMap`（TensorCompatibility:51）、`perfectoidizationCompletedBaseChangeMap`（CompletedBaseChange:304）、`prop813BaseChangeMap`（TensorCompatibility:358）。外延性の補題を共通にする案は変わらない。
- **Witt の余積の模型を何が使っているか（確認済み）。**
  - 外へ出ているのは mod p の全単射だけ：`exists_perfectoidTensorPerfectoidization_modP` → `exists_perfectoidizationTensorBaseChange`:465 → Semiperfectoid/Surjectivity と RootEnvelope/Source。
  - `exists_perfectoidTensorPerfectoidization`:363 は未使用。`completedTensorPerfectoidizationMap_modP_bijective`（CompletedTensor:421）も未使用。
  - CompletedTensor の離散性が使うのは WittPushout の Fontaine 表示（`fontaineBaseWittQuotientEquiv`）で、余積 `WittCoefficientPushout`（:314〜526）は使わない。
- **余積の模型を外す見込み**：完備テンソル H⁰ の単位の mod p 全単射を直接示せばよい（離散性から (S⊗̂T)/p ≅ S/p⊗T/p。推測）。外せるのは WittPushout:314〜526 と TensorPerfectoidization:27〜375 の約 560 行。

### R8-7 Prop 8.13 の環版（BR23・BR31）【推奨：BR23 の公開は B3、BR31 は計画のまま範囲を狭める】

- TensorCompatibility（543 行・24 宣言）は importer が 0。集約からも届かず、既定のビルドに入らない（読むのは監査 2 本だけ）。24 宣言とも外の利用者 0。
- docstring の「使われ方：CLMST、Lemma 10.3」（:21）は古い。Lemma103 が import するのは CompletedTensor。
- 旧 4 本のうち CompletedTensorPerfectoidUniversal は CompletedTensor の節になり、閉包に入っている。
- `isIntegralPerfectoid_of_ringEquiv` は Prism/Perfectoid/PerfectPrismPerfectoid:167 のまま（21 ファイル）。互換の alias 5 本は WittPushout:35〜39 に残っている。
- **推奨**
  - B3 で集約に足して公開する（BR23）。
  - BR31 は、使う側がないので「導来版と Cor 8.14 から同じ主張が出ることを確かめる。証明の置き換えは任意」に狭める（意見）。

### R8-8 置き場所・名前空間（B3）【推奨：B3 の配置案に足す】

- **`Derived/` という名前が中身に合わない。**
  - Derived/ の 25 本のうち導来なのは Interface の後半と Excision だけ。名前空間 `…Perfectoidization.Derived` を使う 20 本（Arc* 14、§10 5、RootAdjunction）はすべて環の話。
  - B3 の案では、移動のあと Derived/ に Interface・Excision・RootAdjunction が残る。
  - 推奨：Derived/ を `Interface/`（E3 の型、Excision の橋、R8-1 で移す TheoryInterface）にする。RootAdjunction（Prop 8.5 の弱始対象と Lemma 8.8 の前段）は `Construction/` か `Arc/Site/` へ。名前空間は改名表で直す。
- **drafts の行き先の欄が B3 の案と合わない。** 20 本すべての「将来の置き場所」が `Perfectoidization.Derived.*`。案：A4・A7 → `Construction/`、A5 → `Descent/`（報告の §163 の区分）、A6 → `Arc/`、A9 → `Interface/`。
- **CLMST のための応用の 8 本**（Cone、Finite、RootTower、Excision、ExcisionComparison、ExcisionTor、FiniteComparisonExcision、CompletedTensorComparison、約 1,300 行）。
  - 使う側は CLMST と Paper だけ。refactor-plan:2169〜2173（2a）の決定で BS に置いた。
  - 推奨：下の階層（例 `Perfectoidization/Applications/`）にまとめるに留める（弱い）。
- **ファイル一本だけのディレクトリ**：`Perfectoid/`（FiniteProduct だけ。Prism の Thm 3.10 に依存）。R3-3 の `Prism/Perfectoid/` と一緒にする。
- **名前空間の例外**：ArcCechUltraproduct・Finite が `SerrePositivity`、ArcPerfectCech が `SerrePositivity.Cech`、RootTower が `Section2`（意図的、そのまま）。

### R8-9 docstring【推奨：B3 の docstring の回（BR25・BR34）】

- **工程ラベル：65 行・19 ファイル。**
  - Π2-5/6/7/7′ が 11 行（Derived/Excision・IntegralExistence・Interface・Inputs）
  - B4-5 が 8 行（TensorPerfectoidization・WittPushout の節の見出し）
  - G1 9、G2 4、D3・D5b・D4・D6a 8 行（Interface・Excision）
  - A5-3・A5-4・A6-1・A1-5・D51（RootAdjunction）、G-A6-11（ArcPerfectoidBase:60・457）、G-A6-12・G-A6-2（FiniteProduct:13・30）、G-A8-6
  - CLMST-D・KL-T（Excision:169・245・290、Derived/Excision:553）、「同計画 §」3 行、「工程」5 行
- **「（旧 …）」：44 行・16 ファイル。** 合併前のファイル名を節の見出しに残している。
- **古い記述**
  - Inputs/PerfectoidizationInterface:51：`Inputs/ArcExcision.lean` はもうない（Derived/Excision:521〜581 の節になった）。`Inputs/Perfectoidization.lean` は界面を取り出していない。:12 に Cor 8.11 を根拠として挙げている（D55 で不要）。
  - Perfectoidization/Excision:16（「PerfectoidizationInterface/Excision」）、:166・185・288（「ArcExcision」）。
  - Finite:19「BS セッションと調整する」（BS の別チャットは段階 II からない）。
  - TensorCompatibility:21（R8-7）。TheoryInterface（R8-1）。
  - FiniteComparisonExcision:25「CLMST の `finiteComparison_excision` は別証明」：その名前の宣言は本体にない（確認済み）。
  - CompletedTensorComparison:20：`.choose` でデータを作っている点が未処理のまま。
- ノートを引く記述は 0。設計書を引く記述は 2 か所（Inputs:27、Derived/Excision:548 の perfectoidization-interface.md）。

### R8-10 drafts と本体の重なり、drafts の古い記述【推奨：5∞-0】

- **本体と同じ名前で中身が違うもの（移すときに改名が要る）**
  - A6/Excision `perfectoidization_excision`:281（導来）と本体 Derived/Excision:481（環）
  - A5/InterfaceLimitCone `perfectoidizationCone`:46 と本体 Cone:49（CLMST の錐）
  - A4/InterfaceFields `completionFunctor`:80 は本体をそのまま包むだけ
- **drafts 同士の重複**：A6/ArcRouteB:31〜51 と ArcSheafProperty:72〜104 に `ValuativeCoverFamily`・`IsVCoverFamily`・`IsArcCoverFamilyCharP`・`affineFamilyCech` が二重にある。
- **drafts と本体の重複**：ArcSheafProperty の `AugmentedRingCechExact`:96 は本体 HomologicalAlgebra/Cech/Basic:92 と同じ。
- **本体に置き換えられるもの**
  - A4/Perfectoidization の Not 8.1（:59〜105、sorry 5）は、本体の `exists_boundedPerfectPrismPresentation`（Semiperfectoid/PerfectoidPrismPresentation:47、Thm 3.10）から作れる。
  - A5/RootAdjunction に残るのは 2 宣言だけ（残りは本体）。
- **古い記述**
  - A6/ArcSite:9〜11 と ArcSheafProperty:28：W9-III-08（CompletedTensor が E3 を import する）と G-A6-12 は BS-W10 作業 A で解決済み。CompletedTensor の閉包に E3 はない（確認済み）。
  - ArcSheafProperty:1〜3・41〜43：三つの引用を sorry として置く、のまま。11-05 夜の改訂（経路 B、1b は主経路から外す）に追従していない。design-status:18 にも「（未）」とある。
  - A7/DiscreteCore:30 は `IsDiscrete（Comparison）` と書くが、コードは `IsTheoryDiscrete` を使う。
  - A9/Assembly:13 は「CAlg 版」と書くが、コードは Theory 版。
  - 18/20 本の冒頭が「基準コミット 972bb7f53」のまま。

### R8-11 設計書の古い記述【推奨：調整役が直す】

- a4-design:12・82・129、a9-design:4・7・27〜31：CAlg_R 版の `nonempty_e3_of_cAlg`。drafts は Theory 版。
- a9-design §7（:70〜99）：W9-III-08 を「致命」と書いたままで、解決済み（design-status:308）の注記がない。:100 の「drafts 49 本」は古い。
- a6-design:79・180：G-A6-12 の骨組みを `drafts/A6/PerfectoidFiniteProduct.lean`（削除済み）とし、「`isIntegralPerfectoid_finPi` は E3 を使う」としている（BR20 で解決）。
- a6-design :175〜177・:200〜201・:220・:233：G-A6-1a/1b/1c を引用の sorry、D56 を旧の形で書いたまま。11-05 夜の改訂も BS-W12 の経路 B も書かれていない（a9-design:39 にだけある）。
- design-status:155（A6-2「E′（G-A6-1a・1b sorry）」）、:164（A9 の前提「W9-III-08」）も古い。
- a7-design:76：`IsDiscrete` を使っている（drafts は `IsTheoryDiscrete`）。

### R8-12 閉包・葉・未使用【推奨：消さない（R3-7 と同じ）。CAlg_R 版の 3 本と R8-4 の 2 宣言は例外】

- **葉は 11 本**（集約以外に importer がない）：ArcCechOverlap、ArcCechUltraproduct、ArcSite、ArcValuationProduct、ArcValuationUntilt、FiniteEtalePerfectoid、IntegralClosureApproximation、PerfectoidFilteredColimit、DerivedCorollary、TheoryInterface、TensorCompatibility（これは集約にも入っていない）。
- **公開の宣言 440 件のうち、自分のファイルの外（本体・drafts。監査は除く）で名前が出ないもの 203 件**（名前の一致で数えた下限。instance は除いた）。自分のファイルの中でも使われないものは 60 件。
  - 群ごと：環 82、E3 界面 63、arc 34、RootAdjunction 22、§10 2。
  - 全部未使用のファイル：TensorCompatibility 24/24。Derived/Excision は 14/17 が外に出ない（内部の鎖）。
- 未使用が多いのは、∞ の組み立て（A4〜A7）が drafts にあり、その入力がまだ使われていないため。

### R8-13 原典の形との違い（記録）

- `IsPerfectoidization`（Defs:50）は環の普遍性で、原典の S_perfd（導来対象）と一致するのは離散の場合だけ（Cor 8.14）。本体の環の定理（Thm 1.17(1)、Cor 8.12 の環版）は E3 から出した系。
- Prop 8.13 の環版は、指定済みの環の perfectoid 化を仮定する。
- Def 8.7 と Lemma 8.8 は affine で濃度 ≤ κ の版（D53・D54）。
- E3 の六点の差は Inputs:40〜46 に記録されている。

## 2. 台帳の項目の今の状態

| 項目 | 状態 |
| --- | --- |
| BR20 | 閉で正しい（FiniteProduct の閉包に E3 はない、確認済み） |
| BR21 | 変化なし。新しい重複 comp_ringEquiv/precomp_ringEquiv（R8-5）を足す |
| BR22 | 変化なし。R8-6 の結果を足す |
| BR23 | 変化なし（TensorCompatibility は importer 0、`isIntegralPerfectoid_of_ringEquiv`:167、alias 5） |
| BR31 | 計画（5∞-8）のまま。drafts の `perfectoidization_relativeTensor`（A7/AnimatedPerfectoidization:273）は sorry |
| BR39 | 変化なし（R8-4） |
| BR26′ | EInfinity → BS の 2 本を足す（R8-1） |
| BR50 | R8-2 と同じ回にすると、§6 → ∞ の閉包も切れる |

台帳にない新しい事実：R8-1、R8-2、R8-3、R8-4 の包み、R8-5 の重複、R8-8、R8-10、R8-11。

## 3. B. 形式化の計画の提案（新しく形式化する項目）

**E3 の欄と ⑤∞ の段の対応（確認済み）**

| E3 の欄 | 原典 | drafts | 段 |
| --- | --- | --- | --- |
| perfd・unit・h0 | Def 8.2 | A4/InterfaceFields | 5∞-5 |
| （欄なし） | Lemma 8.4 | A4 | 5∞-5（Cor 8.14・Prop 8.5・Thm 10.11 が内部で使う） |
| limitCone・limit_isLimit | Prop 8.5 | A5/InterfaceLimitCone | 5∞-6 |
| excision | Cor 8.12 | A6/Excision | 5∞-7 |
| universal | Cor 8.14 | A7/UniversalProperty | 5∞-8 |
| integral | Thm 10.11 | A8 | 5∞-8 |
| 組み立て | — | A9 | 5∞-9 |

**項目ごと**

| 項目 | 今あるもの・要るもの | 規模（推測） | 依存 | 推奨 |
| --- | --- | --- | --- | --- |
| Not 8.1 | drafts A4:59〜105（sorry 5）。本体の Thm 3.10 と `exists_boundedPerfectPrismPresentation` で足りる | 小 | — | 5∞-0 で本体に寄せる |
| Def 8.2 | A4/Perfectoidization・InterfaceFields（Frobenius の塔の余極限、(p,d) 完備化、mod d）。A2 の Frobenius、DerivedGeneral（ScalarRestriction・CompletionFunctor）、G12 が要る。原典の定義域（animated）は A7/AnimatedDomain | 中 | 5∞-4、5a-7 | 入れる（5∞-5） |
| Ex 8.3 | A4/AfterComparison:76（sorry）。A6 の tilt の段で要るかは未確認（a4 §5） | 小 | 5∞-6 | 後回し（補完） |
| Lemma 8.4 | A4:282〜330。D79 に追従済み（P⁰ は Sp 値） | 中 | 5a-8（M14） | 入れる（5∞-5） |
| Prop 8.5 | A5 の 7 本・1,815 行・105 宣言。Rem 4.6（5∞-0）、Lemma 4.8（本体）、S3、A0 の RΓ、Cor 7.3（本体）、A7 の DiscreteCore・AnimatedDomain、Lemma 8.6 が要る | 大 | 5∞-1・2・4、5∞-4b | 入れる（5∞-6） |
| Lemma 8.6 | A5/StrongDescent（28 宣言・18 sorry）、Shared/Descendable（313 行。`IsDescendableOver := sorry`:96、`True` の仮置き 3）。Thm 6.4 mod p（5∞-4b）。M15 は本体に 0 件。thick ⊗-ideal は K の R53（`IsThick`）と重なる | 中〜大 | 5a-9、5∞-4b | 入れる。M15 の thick の定義を R53 と一本にする |
| Def 8.7・Lemma 8.8 | affine 版は本体（ArcSite:126・138・147・435・506）。一般形は形式スキームが要る | — | — | 一般形は入れない |
| Rem 8.9 | 原典の §9 用 | — | — | 入れない |
| Prop 8.10 | (i) 経路 B の B1〜B5 は本体（Arc* 8 本・848 行と CommutativeAlgebra の 8 本・1,000 行、Cech/ 1,550 行）。B6 は drafts/ArcRouteB（sorry 0 だが `ArcRouteBGoal` は未証明。残りは「積射の正次数の各 Čech 項上での完全性と、有限族から一射への縮約」、report-codex-w12:61）。(ii) ⑥ BS17 Thm 4.1 (i)。(iii) tilt への帰着（ArcSheafProperty の古典の部分、sorry 42 行。1b は外し、1c は初等的）。(iv) CAlg 値の層の主張（sorry 17 行） | (i) 小〜中、(iii) 中、(iv) 中 | (i) 6-4、(iv) 5∞-1 | 入れる。5∞-7 を分ける（§3.1 の 3） |
| Cor 8.11 | A6:480 に記録だけ（D55） | — | — | 入れない |
| Cor 8.12 | 環版は本体（E3 から導出）。導来版は A6/Excision・SheafOfSetsExcision（S8 `sectionsOf_pushout` 待ち） | 中 | 5∞-1、5∞-5・6 | 入れる（5∞-7b） |
| Prop 8.13 導来版 | A7/AnimatedPerfectoidization（37 宣言・21 sorry）。A2 の Construction 7.6 (5) の相対版、G-A7-1・2・4 が要る。使うのは Cor 8.14 の S₁=S₂=S_perfd、S₃=S だけ | 大 | 5∞-4、5a-3 | 入れる。Cor 8.14 に要る特別な場合だけでよいか確かめる（規模が減る見込み） |
| Cor 8.14 | DiscreteCore（3 宣言とも sorry）、UniversalProperty（24 宣言・16 sorry） | 中 | 5∞-5・6 | 入れる（5∞-8） |

### 3.1 計画の上で気づいた点（確認済み）

1. **段の表の依存が足りない。**
   - A5（5∞-6）は A7/DiscreteCore と AnimatedDomain を import するのに、5∞-8 は 5∞-6 の後にある。DiscreteCore・AnimatedDomain は A2・A4・DerivedGeneral だけに依存するので、5∞-5 に移すとよい。
   - A6/Excision・SheafOfSetsExcision は A4/InterfaceFields と A5/PerfectSiteComparison を、ArcSheafProperty は A0/PrismaticSite を import する。5∞-7 に 5∞-2・5∞-5・5∞-6 を足す。
   - A7/UniversalProperty は A5 を import するので、5∞-8 に 5∞-6 を足す。
2. **A3（§7）が段の表にない。** A4/Perfectoidization・A5/PerfectSite が drafts/A3/DiscreteCase を import している。
3. **5∞-7 を二つに分けられる。**
   - 7a（古典）：B6 の残り、tilt への帰着、`cech_exact_of_arcCover_perfectoid`。B6 の最後だけが 6-4 を待つ。tilt の部分は B3 の後にすぐ始められる（5∞-3a と同じ考え方）。
   - 7b（∞）：CAlg 値の arc 層、Cor 8.12。
   - 同時に ArcSheafProperty を経路 B に書き直す（R8-10）。
4. **5∞-9 に 5a-6 を足す。** A9 の `exists_perfectoidizationInterfaceE3'` は EInfinityTheory の具体的な E（BE の組み立ての完成）を要る。
5. **5∞-0 に足すもの**：Not 8.1 を本体に寄せる、R8-10 の重複と古い記述、R8-1 に合わせた drafts の追従。

## 4. 件数（スクリプトで数えた）

- **本体**：45 本・12,240 行。sorry 1。閉包に入るのは 18 本・5,441 行。葉 11。
- **宣言**：公開 440 件のうち外の利用者 0 が 203 件（下限）、ファイルの中でも未使用 60 件。
- **docstring**：工程ラベル 65 行・19 ファイル、「（旧 …）」44 行・16 ファイル。
- **IsPerfectoidization の手展開**：8 ファイル・14 か所（下限）。
- **E3 の型**：三つ。CAlg_R 版 255 行は使う側 0。
- **層の逆向き**：EInfinity → BS の import 2 本（BR26′ にない）。
- **Interface の環の部分を切り出したときの効果**：環の 7 本と §6 の 1 本の閉包から ∞ が消える（約 340 本ずつ減る）。
- **drafts（A4〜A7・A9）**：20 本・4,892 行・480 宣言・sorry を含む宣言 276。
  - CAlg_R 版の名前の古い記述：10 本・26 行
  - 古い基準コミット：18 本
  - 「将来の置き場所 Derived.*」：20 本
  - 本体と同じ名前で中身が違うもの：3
  - drafts 同士の重複：4 定義

## 5. ノートの側（参考）

1. ノート：§8 の全 14 項目を見出しと主張・Lean・証明の囲みにした（08 章、番号 8.1.n〜8.4.n）。章末の項目の表と D 表は外し、D 番号は各項目の「原典との差」に引いた（D41・D60・D35 は Def 8.2、D44・D43 は Lemma 8.4、D45〜D47・D51・D52 は Prop 8.5、D49・D50・D69 は Lemma 8.6、D53・D54 は Def 8.7・Lemma 8.8、D56・D59 は Prop 8.10、D55 は Cor 8.11、D57・D58 は Cor 8.12、D15 は Prop 8.13、D61 は Cor 8.14）。評価の段落を付けたのは旧い D 表に行のあった D15・D51・D56/D59 だけ。D56/D59 の方針の「経路 B を保つ」と D15 の方針の言い換えは加筆の担当が書き入れたので、違えば直す。
2. 確かめていない所：Notation 8.1 の「\(d\) が自動的に \(I\) を生成する」の補った筋（剛性 Lemma 3.5 による）、Ex 8.3 の filtration の議論、Lemma 8.6 の「\(R\) は標数 p の完全環としてよい」の読み（\(A/(p,\varphi^{-1}(d))\cong R/p\) は一般に完全でない。本文は原典の文のまま）、[BM18] の番号の対応（旧ノートから引き継いだ）。
3. Inputs の docstring の不整合（ノートには書いていない）：`Inputs/PerfectoidizationInterface` は「Lemma 8.4 は欄から読まれない」としつつ根拠の列に Lemma 8.4 を挙げ、`perfd` 欄の docstring は「Lemma 8.4 とあわせて引用」と書く（D44 と噛み合わない）。drafts/A4/Perfectoidization の冒頭の方針文は D79 以前の「Shared/EInfinityPowerOperation」のまま。
4. 地図 items.csv：8.4（P⁰ は Sp 値の欄 `powerOp0` が本体にある、D79）、8.6（設計の列に D69）、8.10（drafts の `structurePresheaf_isArcSheaf`・`homPresheaf_isArcSheaf`）を 56decc02b で直した。行のずれは check_locations で直した。
