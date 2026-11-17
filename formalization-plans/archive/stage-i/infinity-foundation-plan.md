# ∞ 圏基盤の整備計画（2026-10-28 新設。10-28 に内部 3 件・外部 6 件のレビューを反映。10-29〜30 に IF-W0-3 の判断と CategoryTheory の引き継ぎを反映）

概要：
- InfinityCategories の**中核**（§2）を、KST・DifferentialGraded・EInfinity・モデル圏に依存しない自立した ∞ 圏ライブラリにする。dg 側の応用層（DGNerve・DoldKanComparison・Derived）→ KST の辺（Derived → KST 133 辺、R44 など）は範囲外（§7）。
- ∞ 層の外にある一般論を取り込み、ルートのビルドに完成品をすべて含める。
- その上で、安定 ∞ 圏の Verdier 商を一般に構成する。

方針：
- 数学的内容・宣言の型・公開名は変えない。行うのは移動・分割・入口の修正だけ。
- 一般化や統合のように型が変わる作業、比較の証明、新しい数学は段 G（§5）に分け、移動とは混ぜない。
- 全レーンを止める期間は短くする。止めずにできることは先に行い、大口は領域ごとに順番に止めて行う（§6）。

規約：
- 用語は §2 の表に従う。候補の番号は R 計画の通し番号（R1〜R79）。
- **本書が正本**である。層の名前・段・前提・規模・工数（10-28 のレビューで再計測した値）は本書の値を使う。
  [refactoring-infinity-r2.md](refactoring-infinity-r2.md)・[refactoring-verdier.md](refactoring-verdier.md) は、各候補の詳しい記述と、調査時点の記録として残す。
- 数値は HEAD `cbb891432`〜`bf573b627`（10-28）の時点のもの。IF-W0-3 での再計測（10-29〜30）は各窓の `scripts/refactor/targets/w*.md` にある。実施の直前に計測し直す。移す対象は、ファイル名の一括指定ではなく、W0 で作る段ごとの対象 JSON（確定リスト）で決める。

使われ方：
- コーディネータは、本書で分担と順序を決める。
- 実施するエージェントは、自分の段の表と §6 の検証手順を読めば作業を始められるようにする。
- 索引は [refactoring-infinity.md](refactoring-infinity.md) §0。調査の根拠は §10。

## 1. 目標と完了条件

| # | 完了条件 | いま | 対応する候補 |
| --- | --- | --- | --- |
| 1 | ∞ 中核（Simplicial〜F2・Stable）の import 閉包に、KST・DifferentialGraded・EInfinity と**モデル圏のコード**が入らない | 中核の葉の閉包に外部のモジュールが 1,817 本入っている（DG 660、Derived 391、DGNerve 207、DoldKan 154、KST 115、HA 207、Spectra 29）。入口になっている辺の一覧は §4 | R39・R66・R71・R27・R64・R31・R72・R73 |
| 2 | ∞ 層の外にある一般論が ∞ 層に置かれている | 一般論（G 群）が約 2,800 本、KST・EInfinity・HA にある。段 D・E で約 2,000 本を移す。残りは、移さない HA の部分（Rectification とモデル圏の節。R72 で ModelBridge へ出す分を含む）と、群の境界が重なっている分で、R60 の台帳で行ごとに確定する | R64・R65・R52・R68〜R70 |
| 3 | ∞ 層の完成品がルートからすべてビルドされる。ただし、R60 の台帳で休止・診断とした領域は監査の閉包からビルドする | ルートから届かないものが 5,503 本ある（HEAD bf573b627）。R59 の後も 2,638 本が残る（FilteredExchange 1,749、F1 598、Derived 290）。これは R60 で処置する | R59・R60・R41 |
| 4 | ∞ 層の内外に重複がない | 一致率の高い重複が数組、内容の違う同名・類似の組が約 10 組ある | R61a・R61b・M10 |
| 5 | 層の順序が文書化され、検査で固定されている | ディレクトリ単位の循環がある（F1 → F2・HL・Stable、Stable → F2・Derived など） | R40・R37・R38・R26・R39 |
| 6 | Verdier 列の定義が一つに決まり、商の構成に必要な部品が Stable/ にそろっている | 定義が二つあり、部品は KST・Derived・F2 に分かれている | R48〜R50・R53・R56a・R52・M1〜M9 |

## 2. 用語

| 用語 | 意味 |
| --- | --- |
| 層 | §3 の順序の一段（Simplicial・Core・Kan…）。ディレクトリにほぼ対応する |
| 段 | 本書の作業区分 A〜G |
| 窓 | 全レーン（または一部の領域）を止めて行う作業期間。W0（止めない）・W1（短い全停止）・W2（領域ごとの順次停止） |
| 中核 | Simplicial・Core・Kan・Coherent・F1・F1B・HomotopyLimits・Stable・F2・StablePresentable |
| HL・DK | HomotopyLimits、Dwyer–Kan |
| 9 人論文 | Calmès ほか 9 名『Hermitian K-theory for stable ∞-categories』II（付録 A が Verdier 列） |
| G・M・S 群 | [外部調査](../infinity-outside-survey-2026-10-28.md) の分類：一般論・混在・固有 |
| L1〜L7・F1〜F3・Sp-S1〜S6・SC-C1〜C5 | 外部調査 §2 の群の番号（L＝LocalizingInvariants、F＝Fibration、Sp-S＝KST/Spectra、SC-C＝SConstruction）。**層の F1 とは別物** |
| Sp レーン | KST/Spectra・KST/LocalizingInvariants を担当するレーン。スペクトラムの ∞ 圏 `Sp` とは区別する |

## 3. 決定事項と目標とする構成

| 日付 | 決定 |
| --- | --- |
| 10-28 | 当面の目標は ∞ 基盤の整備。論文の層の切り出しは別の計画（[paper-layer-extraction.md](../paper-layer-extraction.md)、10-30 に [refactor-plan.md](../../refactor-plan.md) へ統合）とし、着手しない |
| 10-28 | 局所化・分数・Verdier 商の API の正本を、Sp レーン（KST/LocalizingInvariants）から ∞ 層へ移す |
| 10-28 | Kan 複体と pointed 単体的集合の層は InfinityCategories の中に作る |
| 10-28 | F1・F1B・F2 の改名は後で行う |
| 10-28 | 名前空間の付け替えは最後（R54）にまとめて行う |
| 10-28 | Verdier 列は束ねた `IsVerdierSequence` を残し、束ねない形を包む定義として加える（R50） |
| 10-28 | モデル圏はできるだけ避け、∞ 中核の下にモデル圏が入らないようにする。モデル圏 → ∞ の比較は、中核の上の橋の層（ModelBridge）に出す（R72） |
| 10-30 | CategoryTheory の下位ディレクトリ（104 本）と Nerve まわり 9 本の整理は、本計画に含めて行う（[伝達文](handover-ct-to-infinity-2026-10-30.md)、論文の層の側では触らない）。削除は IF-W0-3 の後（IF-W0-4）、Nerve の移動と統合は W2a、Mathlib への置き換えと private 化は段 G |
| 10-30 | W2a では SConstruction のレーン（K-S•）も止める（R64 が SConstruction の約 400 本を移し、R76 の利用者にも SConstruction があるため） |
| 10-28 | 層の名前は本書の §3 に統一する。R2 計画の旧名との対応：Foundation∞ ＝ {Core, Kan, Coherent, F1, F1B, HL}、Stable.Base ＝ Stable、Stable.F2Applications ＝ StablePresentable |

層の順序（下から上へ。各層は自分以下の層だけを import する。`{…}` の中は同じ層で、その内部では循環のない依存（DAG）であればよい）：

```
Simplicial < Core < Kan < Coherent < {F1, F1B, HomotopyLimits} < Stable < F2 < StablePresentable < **Sheaves**（11-02 予約、M12a。最初のファイルが入るときに `layers.json` に登録） < ModelBridge < {DGNerve, DoldKanComparison} < Derived

不変条件（11-03 確認）：**F1B（α2b：随伴・局所化・cofinality・Kan 拡張）の入口の閉包は straightening を含まない**（`audit_infinity_f1b` が検査。F2・Stable・HomotopyLimits はもともと straightening に依存してよい）。straightening に依存する一般補題は F1 に置く（IF-W2b §18）。
```

**Kan を Core の上に置く理由**（レビューで判明、10-28 修正）：
- いまの Kan の道具は、quasicategory の理論（同値の道・outer horn の双対など）を使って書かれている。例：`Core/KanFibrationTools` は `Core.EquivalencePath` を import している。
- KST/Spectra 1,622 本のうち、∞ 層に依存しないものは 242 本しかない。

そこで、quasicategory と Kan 複体の基本的な接続（写像空間が Kan であること、Joyal、Kan fibration の道具）は Core に残す。
Kan/ には、Core を使ってよい「空間の理論」を置く（π_n、長完全列、Whitehead、塔と lim¹、Kan 置換、基本亜群）。
数学的にも、Kan 複体は「すべての辺が可逆な quasicategory」なので、この順序で自然である。

外部レビュー（4 件、改訂前の版を読んだもの）は、Kerodon の順序（第 3 章 Kan 複体 → 第 4 章 ∞ 圏）に従って Kan < Core を支持し、quasicategory との比較を Core に置く案を出した。
数学的にはこちらも標準である。ただし、いまのコードで Kan < Core にするには、Core を使っている Kan の証明（KST/Spectra の 368 本など）の書き換えが要り、本計画の「移動だけ」の原則を越える。
そこで本計画は Core < Kan を採る。純粋な Kan 理論を Core の下へ下ろすことは、段 G の後の候補として §9-5 に残す。

```
InfinityCategories/
  Simplicial/          単体的集合の組合せ論：horn・prism・inner anodyne・anodyne・宇宙持ち上げ・Ex∞・necklace・fat realization
  Core/                quasicategory：写像空間（PinchedHom を吸収）・join と slice・極限・同値・充満忠実・左右 fibration・Joyal・Kan fibration の道具
    Roof/              slice の中の屋根（roof）の一般論のうち Core で書ける部分（R39 で Derived から下ろす。F1B/Roof・Stable/Roof も同じ）
  Kan/                 空間の理論：π_n・長完全列・Whitehead・塔と lim¹・Kan 置換・基本亜群・ホモトピーの整合性の道具
    Pointed/           基点付き：Σ ⊣ Ω・smash・基点付き内部 Hom・道空間 fibration
  Coherent/            単体的圏と coherent nerve（coherent nerve の計算も含む）
  F1/                  fibration・cocartesian・straightening・Yoneda・𝒮 と Cat∞
  F1B/                 随伴・Kan 拡張・cofinality
    Localization/      IsLocalization・局所化の存在・DwyerKan/
  HomotopyLimits/      ホモトピー極限 = ∞ 極限・Bousfield–Kan・重み付き極限
  Stable/              Exact/・Verdier/（Basic・Bundled・Adjoint・Thick・Comparison・Fractions）・Roof/・Lax/・Semiorthogonal/・Infinity/（Cat^ex_∞）
  F2/                  Cat∞ の極限・Ind・compact・冪等完備化・presentable
  StablePresentable/   安定 presentable（新しい数学の置き場）
  ModelBridge/         モデル圏 → ∞ の比較（HL の Quillen 系 42 本など）。中核はこれを import しない
  DGNerve/・DoldKanComparison/・Derived/   dg 側の応用層
```

- **モデル圏の扱い（10-28 決定、R72）**：中核の閉包にモデル圏のコードを入れない。いま閉包にモデル圏のコード（HA の Quillen・HomotopyFunctionComplex・Generated・Transfer・Monoidal の各ディレクトリと、`ModelCategory` に言及する HA のファイル）を含む中核のモジュールは、F1 1,287 本、HL 727 本、Stable 124 本、F2 3,426 本ある。しかし調査の結果、**ほとんどは付随的な依存**だった。
  - HA の 12 本のファイルの末尾にある「Model」の節を切り離し、使っていない import を外す。純粋な部分は Simplicial・Kan へ移す。12 本を切った後の試算（第 2 回レビューで再現済み、ビルドは未検証）：F1・F2 は 0 本。Stable は Derived を経由する DG.Module.Cylinder の 1 本で、R39 の範囲。HL は Quillen 系の 42 本を ModelBridge へ出して初めて 0 本になる（出す前は HFC 28・Quillen 7・Generated 2 本が残る）。
  - Quillen 系の 42 本（`quillenCfDerivedAdjunction_exists` など、モデル圏 → ∞ の比較）は ModelBridge へ出す。中核の主な結果（Detection、Bousfield–Kan の holim = ∞ 極限、Ind・Presentable）は、これを使っていない。
  - Mathlib の SSet の Kan・anodyne の API と、HA の純粋な単体的部分（small object argument による Kan 置換、mono 分解、対角、宇宙の持ち上げ）は中核で使ってよい。
- **CategoryTheory（1 圏論）の扱い（10-30）**：`SerrePositivity/CategoryTheory/` の一般部分（Monoidal・Enriched・Limits・Quiver・Simplex・Under）は、Mathlib や HA/Simplicial と同じく**中核より下の基盤**として import を許す（中核の閉包に 34 本入っている。直接の辺は 1 本）。`layers.json` の許可する基盤に加える（10-30 の追加の伝達で、トップ階層の 12 本と GroupTheory/Coxeter も同じ扱い）。殻が再エクスポートしている HA/Rectification は禁止対象なので、殻は R75 で消す。
- Sp（スペクトラムの ∞ 圏）は、安定性が無条件になるまで KST/Spectra に置く。
- PiCriterion（F2/FilteredExchange/PiCriterion）とその橋 `FilteredSpaceBridgeInput` は、閉包に KST・DG を含む。そのため中核の外（Derived、または StablePresentable より上の応用層）に置く。これで R31 との食い違いを解消する。
- **FilteredExchange の処置（R73）**：HTT 5.3.3.3（filtered 余極限と有限極限の交換）を直接示そうとした場所である。10-25 に Ind 側の厳密な経路 d′ が先に完成したため、直接経路 X は停止した。全 2,129 本を、重ならないように次の三つに分ける（第 2 回レビューで訂正：PiCriterion 33 本のうち 26 本が「使われている」側、7 本が「集約からだけ」の側に重複して数えられていた）。
  - 外のコードが実際に使っている 369 本（PiCriterion を除く）：filtered の定義、filtered な図式の弱可縮性、余錐の付け替え、各点の余極限の判定、空間値の余極限の道具など。正しい層へ移す。filtered の定義は F2/Filtered/ にまとめる。
  - 集約からしか参照されない 1,727 本（PiCriterion を除く）：直接経路 X の本体。集約から外して archive へ移す。archive の後に `audit_infinity_f2_exchange` をどう扱うかは R60 で決める。
  - PiCriterion の 33 本：中核の外へ出す。
  - 対象 JSON では移し先を一意に決め、archive する対象に利用者が残っていないことを検査する。

## 4. 中核の閉包に外部が入り込む辺と、その担当（完了条件 1 の内訳）

| 入口になっている辺 | 重さ（閉包に入る外部モジュール） | 担当 |
| --- | --- | --- |
| Stable → Derived.SliceEvaluationPinched・RightFibrationTerminalRepresentation・RoofTargetFunctor | DG・DGNerve 各 866 本 | R39 |
| `Stable.lean` → Derived.CoherentBar.Compact.All | 大 | R39 |
| HL → KST.SConstruction.EnrichedFunctorCollageNerve（HL/QuillenCfCollage） | DG 84・KST 55 | **R71（新設）** |
| F2/FilteredExchange/PiCriterion → Derived.CoherentBar.Compact.FilteredSpaceBridgeInput | DG 84・KST 68 | R31（中核の外へ） |
| HL → DoldKanComparison.UniverseHomotopy（→ DGNerve.Simplex → DG） | DG 83 | R66 |
| F1 → DoldKanComparison.UniverseKan（2 辺） | DoldKan 154 本を F1 の閉包に引き込む | R66 |
| F1 → DGNerve.JoinSimplexInclusions（1 本）、HL → DGNerve の 3 辺（RightAnodyneJoinPrefix → JoinSimplexFaces、FullSubcomplexColimitReflection・FullSubcomplexLimitReflection → JoinVertexSurjectivity） | DG なし（層の逆転だけ） | R66 |
| F1 → Derived（4 辺）・HL → Derived（3 辺） | 小 | **R71** |
| F2/CatInfinity → KST.SConstruction.ContractibleKanProducts（2 辺） | KST | **R71** |
| HL・F1 → KST.Spectra（27 辺）、中核の閉包にある KST 115 本 | KST | R27・R64 |
| 中核 → HA（Kan 置換・anodyne・対角・宇宙の持ち上げ・frame）の約 12 の入口。主な入口は `HL.KanEquivalencePaths` → `HA.Simplicial.AnodyneIntervalEndpoints` → `FixedBoundaryExtensions`（末尾に `[ModelCategory SSet]` の節がある）で、モデル圏が入り込む経路のほぼすべてがここを通る | モデル圏のコード（F1 1,287・HL 727・Stable 124・F2 3,426 本に入る） | R72 |
| HL の Quillen 系 42 本 | モデル圏そのもの | R72（ModelBridge へ出す） |
| F2.Ind・Presentable・Compact・HL → FilteredExchange（実際に使われているのは 369 本＋PiCriterion の一部） | KST 68・DG 10（PiCriterion 経由） | R73・R31 |

## 5. 段と候補

各表の「前提」は、その候補より先に終わっていなければならない候補。
「検証」は §6 の共通検証に加えて行う検査。工数の h は 1 人の作業時間の目安。

### 段 0 関門と準備（W0、レーンを止めずに行う）

| 番号 | 内容 | 前提 | 検証 | 工数 |
| --- | --- | --- | --- | --- |
| R41 | verify.sh を合否の関門にする。<br>・監査を固定の一覧ではなく自動で列挙する（基準コミットで 99 本）。<br>・scripts/audit の閉包もビルドする。<br>・ビルド・全監査・sorry 監査の失敗を集め、一つでもあれば非零で終了する（いまは失敗しても最後の `echo` で正常終了する）。<br>・まず基準状態で全緑になることを確かめる | なし | 故意に失敗させた監査で非零終了すること | 4〜8h |
| R40a | 層検査（Python の import グラフ検査）を報告だけのモードで作る。§3 の層の表、禁止するディレクトリの組（KST・DG・EInfinity・ModelBridge・モデル圏の HA を中核から禁止）、例外の一覧を持つ。規則に「Core が import してよいのは Simplicial だけ。Kan は Core まで。Core の Kan の道具を増やさない」を含める。違反の数を記録し、§6 の段階的な強制で使う | なし | 現状の違反を全件出すこと | 8〜16h |
| R74 | **新設**：段ごとの対象 JSON と、保存検査の道具を作る。<br>**JSON の項目**（書式の正本は `scripts/refactor/targets/README.md`）：`module`、`action`（move／split／archive／**reimport**＝移動せず import だけ置き換える）、`dest`、`keep`、`moved`、`attributes`、`note`、任意の `imports`（移動・分割後の import の一覧。prune の証拠から写す）と `downstream_imports`（再公開に頼っていた下流へ足す直接 import）。対象は R26（SpecifiedHomotopyLift・SpecifiedFunctorEdgeLift を含む）・R49b・R56a・R56b・R61・R64・R52・R69・R70・R72・R73。<br>**分割の手順**：move_module.py は移動（moves・redirects・symbols）だけで、ファイルの分割はできない。分割は、新しいファイルに宣言をそのまま写し、元から削り、import を張り替える小さな道具を作って行う。<br>**保存検査**：移動・分割の前後で、公開宣言ごとに (1) 名前（名前の変更は対応表で正規化して比べる）、(2) 型のハッシュ、(3) 定義の本体のハッシュ（定理以外の公開定義すべて。例：Bool の定義の値が変わったら検出できること）、(4) `#print axioms`、(5) 属性（instance・simp・reducibility など）が一致することを確かめる。<br>止めたレーンが未追跡ファイルを付け替える補助も作る | R40a | 対象 JSON から試算した移動後の層検査が通ること。故意に定義の本体を変えた試験で保存検査が失敗すること | 24〜40h |
| R64a | Simplicial/・Kan/・Kan/Pointed/・ModelBridge/・Stable/Verdier/ などの骨組み（空の入口と監査）を新しいファイルとして作る。段 C の移し先がないという順序の穴を埋める | なし | ビルド | 1〜2h |
| R75 | **新設（10-30、伝達文 §3.1）**：死んだファイルと殻の削除。CategoryTheory/Presentation の 15 本、Quiver/WeightedPaths・WeightedPathMaps、トップ階層の殻 8 本（AnchoredChain* 5・ArrowContext・LabelledChain・SimplexChainParameter）、Spectra/SymmetricSequence の殻 4 本（TensorPowers・TensorPermutations・AdjacentTranspositions・AdjacentBraid）、計 29 本。利用者は監査スクリプトだけ（`scripts/audit/shared.lean`・`audit_homotopical_foundations.lean`・`homotopical_generalization_manifest.json`）なので、それらの登録も直す。**W0 で行える**（IF-W0-4） | なし | 監査の登録の更新、verify | 2〜4h |

### 段 A 入口と小口

| 番号 | 内容 | 前提 | 検証 | 工数 |
| --- | --- | --- | --- | --- |
| R59 | ルートと F2 の入口を正す。`F2.lean` の `#check` 1,497 行を監査ファイルへ移す。Ind・Presentable・Compact・Idempotent・HomotopyLimits をルートに登録する（Coherent と DoldKan はすでにほぼ届いているので、登録すれば足りる）。<br>注意：FilteredExchange は Ind・Presentable・HL の閉包から引き込まれるので、入口から外しても消えない。処置は R60・R31 で行う | R41 | ルート閉包の本数とビルド時間を記録する | 4〜8h |
| R61a | 本文がほぼ一致する重複だけを除き、原本を ∞ 層側に残す。対象は PinchedHom の対（45 行中 39 行が一致）と RelativeInitialExtension（50 行中 43 行）、ほかに対象 JSON で一致率の高いもの。組ごとに残す宣言・証明・instance 属性を対象 JSON で指定する。決定（10-29）：PinchedHom は `F1/Universe/PinchedHom` を残し、import は閉包の小さい F1B 側のものに揃える。RelativeInitialExtension は F1B を残す | R41・R74 | `check_duplicates.py`・保存検査 | 4〜8h |
| R61b | 内容が違う組は、読解して「特殊化」か「比較の定理が要る」かに分ける。比較の定理が要るものは段 G へ。<br>対象：CoreTrivialFibration（一致 9/38 行。∞ 側には instance と追加の宣言がある）、TrivialFibrationStability（5/70）、PushoutTranspose ↔ SquareTranspose（14/47）、SuspensionExactFunctor ↔ Stable/Suspension（2/33。前者は ∞ 関手 X ⟶ X、後者はホモトピー圏の関手 ho X ⥤ ho X で、置き換えると高次の情報が失われる）、Ex∞・MappingCylinder（モジュールとしては KST/Comparison の 1 か所）、CoherentTrianglePathMinimum（2 か所。補題名が違う） | R74 | 読解の記録 | 8〜16h |
| R62 | `fraction_ho_localization` を**公開するだけ**にする（Stable/Verdier へ移すのは R52 の後。閉包に KST.Spectra 57 本と DG 10 本がある） | なし | 公理監査 | 1h |
| R63 | HA/ComplexLimits の 3 本（直接 import しているのは `ExtendTruncationHom` の 1 本で、KST の CochainConnectiveLift を import している）を EInfinity/ComplexLimits へ戻す（同名の再エクスポートの殻 `fcc305646` を実体で置き換える。名前空間はすでに `EInfinity.ComplexLimits`）。CochainConnectiveLift を HA へ下ろすと HA → DG の辺ができるので、その案は採らない。R34 と統合する。`scripts/audit/shared.lean` が import しているので、移したら `python3 scripts/make_area_audits.py` で監査を再生成する（伝達文 §5） | なし | 監査の再生成、ビルド | 1〜2h |
| R79 | **新設（10-30、論文の層のコーディネータからの依頼）**：Lean の docstring が参照している旧計画の案内 4 本の片づけ（1,165 本。追補 10-30 で CategoryTheory の ArrowFactorization・ArrowFactorizationCategory・ArrowFactorizationTransport の 3 本を加えた。importer は HA/GeneralTools・Rectification の AnchoredChain*・scripts/audit/shared.lean だけ）。<br>・`k-theory.md`：`[plan]: …/formalization-plans/k-theory.md` を `…/formalization-plans/archive/k-theory-v1.md#<§396 のアンカー>` に（618 件。アンカーは GitHub の規則で生成して確かめる）。本文中のパスの 1 件は手で直す。<br>・`k-theory-generalization-inventory.md`：`[inventory]: …` のパスを `archive/k-theory-generalization-inventory.md` に（アンカー `#mNNNN`・`layout-execution` はそのまま。618＋16 件）。<br>・`dg-theory-u12e-general-inventory.md`（DG 521 本）・`dg-theory-m5-status.md`（DG 9 本）：**本計画の範囲から外し、[DG の整理計画](dg-cleanup-plan.md) の D5 で行う**（10-30 ユーザー決定。DG の統合 D4 と同じ窓で、docstring を写すときに書き換える）。<br>規則：相対パスの深さ（`../../../` など）は保ち、`formalization-plans/<名前>.md` の部分だけを替える。宣言には触れない。文書ごとに 1 コミット（本計画の分は 2 本。DG の 2 本は DG 計画）にし、ハッシュを論文の層のコーディネータへ知らせる。案内の削除と README の表の更新は先方が行う。ArrowFactorization* 3 本も本計画の担当（追補で移管）。<br>docstring だけでも olean が変わり依存先が再ビルドされるので、**W1 の最初**（IF-W1-1 の冒頭）に行い、W1 の最初の verify に含める | なし | 置換の件数の照合（618／618＋16。DG の 521／9 は DG 計画）、ビルド、verify | 1〜2h＋再ビルド |

### 段 B Verdier の土台（すぐ移せるものだけ）

| 番号 | 内容 | 前提 | 検証 | 工数 |
| --- | --- | --- | --- | --- |
| R48 | Verdier の基礎ブロック 7 本を移す。StableCategories・ExactEnrichment・StableInfinity・VerdierSequence・VerdierDiagrams・AdjointVerdier を Stable/Verdier・Stable/Infinity へ、AdjointLocalization を F1B/Localization へ。閉包は Core・Stable・F1・F1B・Coherent だけで、層を破らない（確認済み）。直接 import している 38〜43 本（数え方による）の import 行が変わる | なし | audit_localizing_invariants・audit_kst_s_construction | 2〜4h |
| R49a | Derived の一般 3 本（ExactFunctorCategory・ExactFunctorCategoryEquivalence・StableVerdierSequence）を Stable/Exact・Stable/Verdier へ移す | なし | audit_derived_infinity・audit_infinity_stable | 1〜2h |
| R49b | ExactFunctorDescent と RestrictedDeformationLocalization を、依存先の Derived 4 本（CofiberBottomIsoTransport・FullSubcomplexHomotopyLift・HomotopyPrecompVertex・RestrictedDeformationHomotopy。いずれも DG に依存しない）と一緒に移す。CofiberBottomIsoTransport は F2.CatInfinity.SpecifiedHomotopyLift → SpecifiedFunctorEdgeLift に依存するので、この 2 本を R26 の対象に加え、R26 の後に行う | R39・R26 | 同上 | 4〜8h |
| R50 | 束ねない形を、既存の定義を包む定義として加える（10-28 決定）。<br>・束ねた `IsVerdierSequence`（9 人論文の Verdier 列の特徴づけ A.1.1・A.1.5・A.1.9 にあたる）は**そのまま残し**、約 277 本の利用元は変えない。三つの条件はどれも `i.hom`・`q.hom` しか使わないので、二つの形は包み方が違うだけで中身は同じ。<br>・Stable/Verdier/Basic に、束ねない形 `IsVerdierPair (i : X ⟶ Y) (q : Y ⟶ Z) [IsExactFunctor i] [IsExactFunctor q]`（仮の名前）を、インスタンスから StableCategory・ExactMap を組み立てて既存の定義に渡す定義として置く。同値補題 `isVerdierSequence_iff` も置く。<br>・`IsStableVerdierSequence` は Comparison に置く。新しく書くコードと M1〜M8 は束ねない形を使う | R48 | 同値補題がほぼ rfl で通ること。既存の利用元に差分がないこと | 2〜4h |
| R53 | 厚い部分圏の一般述語 `IsThick`・`thickClosure` を新しいファイルとして作る（定義だけ）。使う `retractClosure` は F2/Idempotent/Retracts.lean:73 にあるので、先にそれを Core へ下ろす（そのまま使うと Stable → F2 の辺ができる）。dg 版 `dgThickClosureProperty`（triaRepresentable の retract 閉包）との一致は比較の証明が要るので段 G（M9）に分け、既存の定義を置き換えるのはその後にする | retractClosure の移動（W1） | — | 0.5〜1 人日 |

### 段 C 層の順序と、閉包を切る作業

| 番号 | 内容 | 前提 | 検証 | 工数 |
| --- | --- | --- | --- | --- |
| R40 | 層検査の強制を三段階で行う（§6）。W1 の終わり：中核の閉包に DG・EInfinity を禁止し、層の違反の数を増やさない。W2a の終わり：KST とモデル圏のコードも禁止。W2b の終わり：中核の層の順序の違反を 0 にする（例外一覧を除く） | R40a と各段の切断 | 各段階の条件 | 各 1〜2h |
| R39 | Stable → Derived の 10 辺と F2 → Derived の 7 辺を解消する。§4 の重い 3 本を含む。一般の随伴・right fibration・slice を下の層へ抽出し、`Stable.lean` の逆転も直す（reimport）。<br>決定（10-30）：重い 3 本は Derived の roof の一般論に本当に依存している。import を縮めた後に必要な roof の 15 本（DG・KST・モデル圏の汚染 0）を `Core.Roof`・`F1B.Roof`・`Stable.Roof` へ下ろす。残りの 8 本と `SpanSuffixIndex` の分割案は W2c（R52）へ | R40a | 中核の閉包検査 | 24〜48h |
| R26 | F1 → F2 の 28 辺を解消する。F2.CatInfinity の Core*（CoreIsofibration など）と、R49b のための SpecifiedHomotopyLift・SpecifiedFunctorEdgeLift を Core・F1B へ下ろす。R56a・R49b の前提でもある。<br>W1 の一覧（10-30）：move 12 本・split 3 本。`CoreIsofibration`・`CorePullbackIso`（CoreRightFibration・CorePullbackMap の基礎が要る）と `SpaceLimitShapes`・`FunctorPointwiseColimitCriterion`（Stable の一般部分、R37）は保留 | R40a | 同上 | 16〜28h |
| R66 | 二つに分けて書く。<br>(a) 配置の逆転：`DoldKanComparison.UniverseKan`（閉包は Mathlib だけ）は Simplicial へ move。`DoldKanComparison.UniverseHomotopy`（2 宣言とも純粋。型 `IsSimplicialHomotopyEquivalence` は Core）は **Core** へ move し、過大な import を縮める（`imports`・`downstream_imports` で指定）。`DGNerve.JoinSimplexInclusions`・`JoinSimplexFaces`・`JoinVertexSurjectivity`（DG には依存しないが Core の join・pullback の補題を使う）は **Core** へ move（10-29 に Simplicial から変更）。<br>(b) DG 依存の除去：UniverseHomotopy → ResolutionComparisonEquivalence → … → DGNerve.Simplex → DG の経路を (a) で切る。<br>完了条件 1 の全体には R39 も必要 | R40a | 中核の閉包に DG・EInfinity が入らないこと | 16〜32h |
| R71 | **新設**：§4 で担当がなかった辺を切る。HL/QuillenCfCollage → KST.EnrichedFunctorCollageNerve、F2/CatInfinity → KST.ContractibleKanProducts（2 辺）、F1 → Derived（4 辺）、HL → Derived（3 辺）。r2-a 調査の 170 行目に既出 | R40a | 中核の閉包検査 | 16〜32h |
| R72 | **新設**：モデル圏を中核から切り離す。<br>(1) HA の 12 本（HA/Simplicial の Generators・FixedBoundaryExtensions・LargeParameterExtension・UniverseLiftAnodyne・BisimplicialCofibrancy、HA/Generated の Basic・FunctorClosure、HA/Transfer の FullyFaithfulLifting、HA/HomotopyFunctionComplex の BoundaryOne・DiagonalFrame・QuillenStandardFrame・StandardCosimplicial）から、末尾の Model の節と使っていない import を切り離す。<br>(2) 純粋な部分（Kan 置換、mono 分解、anodyne の端点、Kan による判定、対角、宇宙の持ち上げ、Reedy の分解系）を Simplicial・Kan へ移す（同じファイルに二つの分割を作用させない規約のため、W2a では (1) の切り出しだけを行い、(2) の移動は W2b 以降）。<br>(3) HL の Quillen 系 42 本と、切り離した Model の節を ModelBridge へ出す。利用者（EInfinity の約 63 本、KST.SConstruction.EnrichedFunctorCollageNerve）は ModelBridge を import する | R40a・R64a・R74 | F1・F2 のモデル圏モジュール 0、Stable は R39 の範囲の 1 本だけ、HL は Quillen 系 42 本を ModelBridge へ出した後に 0 | 16〜32h |
| R73 | **新設**：FilteredExchange を三つに分ける。使われている 369 本は正しい層へ（filtered の定義は F2/Filtered/）、直接経路 X の 1,727 本は archive へ、PiCriterion は中核の外へ（R31） | R40a・R74 | ルート閉包の本数、監査 audit_infinity_f2_exchange の扱い | 16〜32h |
| R37 | 中核へ戻ってくる逆向きの辺（F1B → Stable 54、HL → Stable 50、F1 → Stable 23、計 127）の参照先を下の層へ移す。Stable < F2 としたので、F2 → Stable の 193 辺は順方向になり、対象から外れる | R40a・R64a | 層検査 | 16〜32h（再見積り） |
| R38 | HL → F2 の 84 辺と Stable → F2 の 42 辺を解消する。一般補題は下の層へ移し、sifted・PΣ は F2 に残す | R40a・R64a | 層検査 | 24〜48h |

### 段 D 外にある一般論の取り込み

| 番号 | 内容 | 前提 | 検証 | 工数 |
| --- | --- | --- | --- | --- |
| R64 | Simplicial・Kan・Kan/Pointed 層に中身を移す。ファイル単位の一括移動にはしない。<br>**規則**：宣言の内容と証明の依存で、対象 JSON（R74）に振り分ける。<br>・単体的集合だけで書ける部分は Simplicial へ。<br>・空間の理論（Core を使ってよい）は Kan へ。<br>・quasicategory との比較（`KanCharacterization` の Joyal の外 horn の充填、`KanFibrationTools`:58 の同値を使う補題、`F1/KanModels/KanAnodyneLocalization` の `IsQCatEquivalence` など）は Core に残す。<br>・豊穣の比較は Coherent・F1 に残す。<br>・閉包が Kan より上に出るものは F1・HL に置くか分割する。<br>出所：F1/Simplicial、F1/KanModels、F1B/KanComplex、HA/Simplicial の一般部分（Rectification を import しないもの）、KST/Spectra の Sp-S1・S2・S3・S5、SConstruction の SC-C3〜C5、KST/Comparison の Ex∞ と単体的ホモトピー、SerrePositivity/Spectra の PointedSimplicialSet・Pointed | R74・R64a・R27 | 層検査、保存検査 | 40〜80h |
| R27 | HL・F1 → KST.Spectra の 27 辺を解消する。汎用の参照先は R64 の Kan 層へ移し、Spectrum* の 5 本は KST/Spectra/Limits へ移す | R40a | 中核の閉包に KST が入らないこと | 24〜48h（R64 と重なる） |
| R65 | Dwyer–Kan 局所化（EInfinity/SimplicialLocalization・Hammock・FrameHom の一般部分）を F1B/Localization/DwyerKan と HL へ移す。<br>注意：この三つ全体（1,423 本）には、Derived への辺が約 30 本、KST への辺が約 8 本ある。移す G 部分集合を、閉包を基準に対象 JSON で選び直す。相対圏の hammock 局所化そのもの（モデル圏を使わない部分）は F1B/Localization/DwyerKan へ移す。一般のモデル圏の ∞ 局所化 `modelHammock_isLocalization` とその周辺は、モデル圏を仮定するので ModelBridge へ出す（10-28 追記） | R74・R26 | 層検査 | 32〜64h（再見積り） |
| R56a | 局所化の存在の周辺を F1B/Localization へ移す。対象は確定リスト（R74）で、少なくとも LocalizationResolution・GeneralLocalization・LocalizationFactorization・LocalizationUniqueness・InverseAttachment*・WalkingEquivalence*・ParametricDiagramGluing・CoreAnodyneLifting を含む。<br>注意：いまの閉包には F2（CoreAnodyneLifting → F2.CatInfinity.CoreIsofibration）、HL 146 本、HA/Simplicial（WalkingEquivalence → AnodyneKanReplacement）、straightening 9 本が入っており、このままでは F1B の straightening 禁止監査（scripts/audit_infinity_f1b.lean:24）に落ちる。そこで R26・R72 の後に行い、straightening を使う部分は F1 側に残す。注意（10-30）：R26 で `CoreIsofibration` が保留になったので、w2a.json の検査（w1 を前提）で F2 への辺が残るか確かめ、残れば CoreIsofibration の pull-down 集合を W2a に加えるか R56a を W2b へ回す | R26・R72・R74 | audit_infinity_f1b | 8〜16h |
| R76 | **新設（10-30、伝達文 §2-1）**：CategoryTheory の Nerve まわり 9 本（NerveHomotopy・NerveHomotopyUniverse・NerveSimplexEndpoint・NerveSimplexStart・NerveSimplexFirstFunctor・NerveVertices・SimplexChainVertices・ElementsChainLifting・ElementsNaturalPrecomp）を HomotopicalAlgebra/Simplicial へ移す。CategoryTheory と HA の相互依存が消える。利用者は HA 26・EInfinity 12・KST 6（SConstruction 3・ProExcision 2・Comparison 1）・CategoryTheory 4。R64 の閉包の規則で、後に InfinityCategories/Simplicial へ移るものがあってよい | R74 | 層検査 | 4〜8h |
| R77 | **新設（10-30、伝達文 §3.2・§7）**：CategoryTheory の下位ディレクトリ 104 本と、∞ 側だけが使うトップ階層の 12 本（AdjunctionHomLaws・CommaIdentities・FiniteBijection*4・FiniteBlockEquiv・FunctorTransport・ParametrizedAdjunctionTransport・PointwiseAdjunction・RelativeArrow）を約 38 本に統合する（Monoidal/Mod・TensorPower・Action・Braided、Enriched/*、Adjunction/Comparison（AdjunctionHomLaws・PointwiseAdjunction・ParametrizedAdjunctionTransport を含む）、Quiver/*、Simplex/*、Under、Limits（FiniteBijection*・FiniteBlockEquiv・CommaIdentities・RelativeArrow を含む）。最終的な対応は W2a の対象 JSON で確定）。宣言・名前空間・証明は変えない（BS 方式で section に包む）。統合の道具は BS の `bhatt-scholze-merge-modules.py` を `scripts/refactor/merge_modules.py` に一般化して使う（IF-W0-4 で用意し、保存検査と組み合わせる）。利用者は Spectra 89・HA 50・EInfinity 25・KST 18 本の import の書き換え | R75・道具 | 保存検査・層検査 | 16〜32h |
| R56b | 比較・適用の部分（GroupoidCompletion*・SimplexAttachment*）は段 E で扱う。GroupoidCompletionFiniteFactorization は F2 を import し、SimplexAttachmentQuotientComparison の閉包は VerdierSequence に届く。いずれも閉包に DG と KST.Fibration を含む | R70・R66・R48 | 層検査 | 8〜16h |

### 段 E KST の一般部分の取り込み

| 番号 | 内容 | 前提 | 検証 | 工数 |
| --- | --- | --- | --- | --- |
| R51 | 一般の安定 span pushout（SConstruction/StableSpanPushout）を Stable へ移す。閉包は小さい（SConstruction 2 本と Core・Stable・F1） | R48 | 層検査 | 2〜4h |
| R52 | Verdier 分数の機構を Stable/Verdier/Fractions へ**移すだけ**にする。対象は LocalizingInvariants の Verdier* 131 本、Fibration の W 分数 90 本、Tamme* 23 本（内容による分類。接頭辞で数えると Verdier* 93・Weak* 160・Tamme* 27）。あわせて `fraction_ho_localization` も移す | R48・R51・R27 | 層検査 | 24〜48h |
| R68 | lax pullback と半直交分解（L1、56 本）を Stable/Lax・Semiorthogonal へ移す。Derived/Gluing → KST の import がこれで消える | R48 | 層検査 | 8〜16h |
| R69 | 安定の cofiber・完全関手の補題（L6）と quasicategory の道具（L7）を、Stable・Core・F1B へ移す。BF fiber を使う約 20 本は KST に残す | R48 | 層検査 | 16〜32h |
| R70 | straightening と Kan の補助（F3）と CoreFlag（L5）を F1 へ移す | R64 | 層検査 | 16〜32h |
| R45 | 段 E の後で、LocalizingInvariants と NonConnective の残りの辺を計測し直して処置する（いまの 24 辺と 19 辺は古い値） | 段 E | — | 再見積り |

### 段 F 整理と固定

| 番号 | 内容 | 工数 |
| --- | --- | --- |
| R60 | 孤立したモジュールと休止領域の台帳を作り、各行で「主経路／診断／archive／一般論を抽出」を決める。対象は FilteredExchange、F1/Cocartesian、HA/Rectification、ClosureFunctoriality、KST/Comparison・ProExcision、Spectra など。古くなった記述も直す | 8〜16h |
| R32・R33・R36・R42・R43 | 反例と凍結候補、未登録・監査で被覆されない・転送入口のモジュールの処置 | 16〜32h |
| R67 | 基盤の層だけが使っているものの分類し直し（伝達文 §6）。<br>・GroupTheory/Coxeter（TypeA・FirstToLast・PermutationInduction・InvolutionRelations。利用者は CategoryTheory/Monoidal・EInfinity/Operad・IntervalCuts・Spectra/SymmetricSequence）：**動かさず**、CategoryTheory と同じく中核より下の基盤として `layers.json` に登録する。Mathlib の `Equiv.Perm.mclosure_swap_castSucc_succ` などへの置き換え（TypeA 955 行が不要になりうる）は R78 へ。<br>・Inputs/Homotopy（KanQuillen＝引用の sorry、ResolutionHom・SimplicialLevel）：主定理の閉包の外で、scripts の check 3 本しか import していない。`InfinityCategories/ModelBridge/Inputs/` へ移し（モデル圏の存在の引用なので ModelBridge が置き場）、`make_area_audits.py` の sorry の許可リストと check のパスを直す。削除するかどうかは R60 の台帳で決める。W2a（R72 と同じ窓） | 4〜8h |
| R54 | **決定（11-04、ユーザー）：範囲は KST から移した宣言だけ、F1・F1B・F2 は改名しない、deprecated alias は段 G の最初の区切りまで残す**（[IF-F §5](../infinity-codex-f.md)）。名前空間の付け替え（旧名は deprecated alias で残し、名前対応表を作る）。F1・F1B・F2 の改名もここで判断する。<br>移した宣言には KST の名前空間が残る（Fibration 747 ブロック、LocalizingInvariants 519、Spectra 333 以上）。§9-3 で、段ごとに行うか最後にまとめるかを決める | 16〜40h（再見積り） |

### 段 G 型が変わる作業・比較の証明・新しい数学（窓の外）

| 番号 | 内容 |
| --- | --- |
| R57 | Weak* と Tamme* の 4 対を、一つの一般版にまとめる。必要な条件は pullback での安定性だけでは足りない。たとえば `WeakSpanBaseChangeLift`:45 は二つのうち三つの性質の合成の向きを使うので、少なくとも合成で閉じていることも要る。4 対それぞれの必要条件を列挙してから一般版の仮定を決める。旧名は deprecated alias で残す |
| M1 | `IsVerdierSequence` ⇒ `IsStableVerdierSequence` |
| M2 | 安定 ∞ 圏 B の**安定な充満部分圏の cofiber 辺**による局所化は安定で、局所化関手は完全である（任意の局所化については言えない）。いまの分数の比較（`VerdierSpanCoherentContraction` など）は、商が安定であることと `IsVerdierSequence` を仮定している。M2 の証明に使うなら、それらの仮定を使わない部分を先に切り出す |
| M3〜M6 | Ind_ω の余極限と presentable 性、安定な Bousfield 局所化、Thomason–Neeman（核が compact 生成されるなどの仮定を明記する）、Karoubi 列 |
| M7 | 商の存在を二つに分ける。(a) 一般の安定な充満部分圏 A ⊂ B に対する商の存在。核は A の厚い閉包（像の retract 閉包）になる（R53 の `thickClosure` を使うので M9 の後に行う）。(b) A の像が厚いとき、核と像が一致し、`IsVerdierSequence` になる。宇宙の段に注意する（`exists_quasicategory_localization` は同じ宇宙 `SSet.{u}`、Ind_κ は一つ上の宇宙） |
| M8 | **新設**：商の関手性。(a) 安定 ∞ 圏とその安定な部分圏の組 (B, A) と、部分圏を保つ完全関手のなす ∞ 圏の上で、(B, A) ↦ B/A が関手的であること。(b) その Calkin 懸垂への応用（非連結 K の再設計、Sp-3 の見積りで 9〜18 人日）。見通し（10-28）：存在定理の構成（J の貼り付け・Kan 置換・inner anodyne 置換）は、small object argument で関手的な分解を選べば (X, W) について厳密に関手的にできる見込みがあり、厳密な豊穣関手から coherent nerve の写像として ∞ 関手を得られる可能性がある。着手時の最初の検討事項（解説 infinity-foundation 第 5 章 §5） |
| M9 | **新設**：一般の `thickClosure`（R53）と dg 版 `dgThickClosureProperty` の比較。証明の後に dg 版を置き換える |
| M10 | **新設**：R61b で「比較の定理が要る」とした組の比較（例：∞ 関手としての Σ とホモトピー圏の関手 Σ） |
| R78 | **新設（10-30、伝達文 §3.3〜3.4・§6.1・§7）**：CategoryTheory の下位ディレクトリとトップ階層の 12 本、GroupTheory/Coxeter について、Mathlib と重なる宣言の置き換え（`Functor.copyObj`・`isoCopyObj`（FunctorTransport はファイルごと）、`Adjunction.homEquiv_naturality_*`（AdjunctionHomLaws）、`Equiv.Perm.mclosure_swap_castSucc_succ`（Coxeter の帰納法）、`Paths.liftNatTrans`・`Paths.ext_functor`・`Quiv.adj.toComonad`・`MorphismProperty.naturalityProperty`・`rightAdjointUniq`・`MonoidalRightAction`・`TransportEnrichment` など）、未使用の宣言の削除、ファイルの中だけで使う約 120 の名前の private 化、ファイル名由来の名前空間の付け替え（R54 と一緒に）。証明と公開 API が変わるので窓の外。論文の層の計画と同じく、群ごとに「提案 → 承認 → 実装」で進める。Mathlib にない部分（`SimplexCategoryGenRel ≌ SimplexCategory` など）は提出候補として [mathlib-upstream.md](../../mathlib-upstream.md) へ |
| M11 | **新設（10-28）**：一般の相対圏 (C, W) について、hammock 局所化の nerve への関手 `hammockLocalizationNerveMap : nerve C.category ⟶ kanHammockNerve C` が `IsLocalization` を満たすこと。いまはモデル圏の場合（`modelHammock_isLocalization`、ModelBridge へ出す）しか証明がなく、一般には `hammockLocalizationNerveMap_inverts` だけがある。数学的には知られた定理（Hinich, "Dwyer–Kan localization revisited", 2016 など。参照は要確認）。これがあれば、局所化の写像空間を、モデル圏を使わずに中核（F1B/Localization/DwyerKan）で計算できる。Verdier 商の写像空間（分数）との比較にも使える |
| M12 | **新設（11-02、BS 発）**：∞ 層の一般論。小さい site 上の D(A) 値前層の層条件・層化 F ↦ F^♯・大域切断・RΓ(J, F) := lim F^♯（層である前層にだけ lim で定義する案は採らない）、層化の左完全性（HTT 6.2.2.7、A6＝Cor 8.12 で要る見込み）。大きい site は基数 κ（既定 (#A + #R + ℵ₀)^{ℵ₀}）で切り落とした小さい site に取り替え、κ 不変性は定理（宇宙は上げない）。前提：D(A) の presentable 性（StablePresentable は空の骨組み）、小さい 𝒞 について Fun(𝒞^op, D(A)) の presentable 性（HTT 5.5.3.6）、presentable 圏での小さい射の集合に関する局所置換の存在（HTT 5.5.4.15 前半。F2/Presentable の `LocalReplacementReflection` は後半まで）。使う部品：F2/Presentable の accessible・随伴関手定理・反射、Core/Limit の `JoinCone`・`IsLimitCone`、HomotopyLimits の Bousfield–Kan、Derived の `CofinalLimitTransfer`。設計書 `bhatt-scholze/design/infinity-sheaves-design.md` と骨組み（`bhatt-scholze/drafts/`）は BS セッションが書く。**置き場所（11-02 決定、設計書 [infinity-sheaves-design.md](../../bhatt-scholze/design/infinity-sheaves-design.md) §4・§9 への回答）**：(M12a) 一般論 S1〜S6（E は任意の安定 presentable ∞ 圏）は新しい層 `InfinityCategories/Sheaves/`、順序は StablePresentable の上・ModelBridge の下（§3。モデル圏と dg を要しないため）。(M12b) F2 の一般論：G4（Fun(N(𝒞)^op, E) の presentable 性、HTT 5.5.3.6）・G6（局所置換の存在、HTT 5.5.4.15 前半）・G8（空間との tensor と Map(X ⊗ M, F) ≃ Map(M, lim F)、HTT 5.1.5／4.2.4）は `F2/Presentable/`（G8 は `F2/` か `HomotopyLimits/`）。(M12c) G3（D(A) の presentable 性）と S7（D(A) への適用、G10 の Tot）は `Derived/`（`Derived/Sheaves/`）、StablePresentable の一般論を使う。(M12d) G9（効果的エピの Čech 脈体、Bousfield–Kan との比較）は `HomotopyLimits/`（または `F1B/`）、G7 は `Stable/`。BS 固有の site は `BhattScholze/`。**時期**：いずれも新しい数学なので段 G（窓の外）。開始は **W2b が main に入った後**（F2・HL・Stable の移動が終わってから。見込み 11-05〜06）で、W2c（KST/Spectra 側）と並行してよい。条件：新しいファイルだけ（既存の移動と混ぜない）、ビルドは新しいファイルとその閉包だけ（Lake キャッシュで数分）、全ビルドは暦で一つずつ。**担当（11-03 決定、同日夜に BS の入口表 [foundation-entry-points.md](../../bhatt-scholze/design/foundation-entry-points.md) §4 で補正）**：**BS 側**（Codex、BS-Wn）：M12a の S1〜S5・S8（層条件、Γ・RΓ、脚注 10 の補題、**層化の存在 S4 と完全性 S5**（G4・G6・G8・G7 を使う側）、空間値の層）を `Sheaves/` に、M13（D(A) の t 構造と完備化）を `Derived/` に。**∞ レーン**（W2b 取り込み後に IF の指示書で依頼）：G3（D(A) の presentable 性、`Derived/`）、G4・G6・G8（`F2/Presentable/`）、G7（安定 ∞ 圏の間の左随伴は完全、`Stable/`）、G9・G10（`HomotopyLimits/`・`DoldKanComparison/`）、**G13**（空間の ∞ 圏は既存の `SpaceInfinity`（`F1/Categories/CatInfinity.lean`）、presentable 性も既存の `space_isPresentable`（`F2/Presentable/SpacePresentable`）を使う（BS の訂正 11-03 夜、入口表 §4）。残る依頼は `Type u → 𝒮` の離散埋め込みと、0 切り捨ての公開名の照合だけ）、**⊗^L の ∞ 関手**（少なくとも固定対象とのテンソル `tensorWith M : D(A) ⟶ D(A)` と対称性。計画 v2 の β5 の一部。`Derived/`。既存の `dgSemifreeDerivedHomTensorInfinity` を起点に）、G12（`IsPresentable (CAlg_R A)`、EInfinity 側、A2 以降で要る）、Core の小補題（`uliftFunctor.obj (nerve (SmallModel C)) ⟶ nerve C` の比較、存在確認のうえ必要なら）。時期は W2b 後の段 G、新規ファイルのみ。それまで BS は骨組みを `drafts/` に書く（S1・S2・S6 は既存の基盤だけで書ける。W2b・W2c の改名表は BS へ回す）。**(M12e、11-02 夜追加、BS 発 S8 `drafts/Sheaves/SpaceValued.lean`)** 空間値の層と E 値の層の局所性：(1) 空間値前層の層化（HTT 6.2.2.7。S4 を IsStable なしの presentable E に一般化し E = 𝒮 に適用）、(2) 離散な前層の層化は離散で Mathlib の 1 圏の層化に一致（HTT 5.5.6.28）、(3) 単射に沿う離散な押し出しの離散性、(4) Γ(F, O) := lim_{el(F)} O と前層の余極限を極限に送ること（HTT 5.1.5.6）、(5) O が層なら Γ(−, O) は局所同値を同値に送る（HTT 5.5.4.20）、(6) Γ(h_c, O) = O(c)。Cor 8.12 の原典の証明と A8 で使う。**置き場所（11-02 決定）**：(1)(5)(6) は `Sheaves/SpaceValued/`、(2)(3) は `Sheaves/Discrete/`（Mathlib の Sites との比較）、(4) の一般部分（前層 ∞ 圏の普遍性、el(F) 上の極限）は M12b と同じ `F2/`。前提に **G13：𝒮 が presentable ∞ 圏であること**（計画の F2 後半「𝒮 の普遍性」）と **S4 の非安定版**を加える。時期・担当は M12 と同じ |
| M13 | **新設（11-02 夕、BS 発、`bhatt-scholze/drafts/DerivedGeneral/`）**：(a) D(A) の標準 t 構造と Postnikov 切り捨て（`Truncation.lean`）。(b) 導来 (p, d) 完備化の ∞ 関手（`CompletionFunctor.lean`、HA/DerivedCompletion の dg nerve 版）。A2（Construction 7.6 の HT filtration、Kan 延長の値の完備化）で要る。**置き場所（11-02 決定）**：どちらも `InfinityCategories/Derived/`（D(A) 固有。Derived は既に HA を import しているので (b) の `HomologicalAlgebra.DerivedCompletion` への依存は層の規則に反しない）。一般の安定 ∞ 圏の t 構造の定義を切り出す場合だけ `Stable/`（新設）。dg 側に既存の t 構造・Postnikov 切り捨てはない（11-02 確認）。**時期**：M12 と同じ段 G、開始は W2b の後。(b) は 2b（HA の DerivedCompletion の整理）の後に、改名表を受けてから |
| M14 | **新設（11-02 夕、BS 発 G-A4-1、`bhatt-scholze/drafts/Shared/EInfinityPowerOperation.lean`）**：E∞-F_p 代数の冪作用 P⁰（[Lur11, §2.2]、Berger–Fresse／May）。(i) π₀ で Frobenius、(ii) 正次数のホモトピーで零（Rem 2.2.7）、(iii) 余単体的可換 F_p 代数の levelwise Frobenius が Tot_{E∞} の P⁰ を誘導する。現行の EInfinity に冪作用はない（11-02 確認）。Lemma 8.4（Δ_perf の coconnectivity）の唯一の経路で、A4 の一般項目で最も重い。**置き場所（11-02 決定）**：`EInfinity/PowerOperation/`（新設、`BarrattEccles/`・`Operad/` の隣。Barratt–Eccles の作用の型はそこで確認）。**時期・担当**：段 G。A4 の中身を書く段階まで不要。担当は E2 レーン（EInfinity）か BS かをそのときに決める |
| M15 | **新設（11-02 夜、BS 発 G-A5-1、`bhatt-scholze/drafts/Shared/Descendable.lean`）**：Mathew の descendability（[Mat16, Def 3.18]、[BS17, §11.2]）。E∞-A 代数 B の生成する thick ⊗-ideal が単位を含むことを定義とし、index による判定、底変換・合成・テンソルでの安定性、降下 M ≃ Tot(M ⊗ B^{⊗•+1})、RHom(F^{⊗2}, A) ∈ D^{<0} ⇒ index ≤ 2、[BS17, Lemma 11.22]、完備版。Lemma 8.6・Prop 8.5 の降下の唯一の経路で、BS 固有ではない。**置き場所（11-02 決定）**：`EInfinity/Descendable/`（新設。`BarrattEccles/CAlg` と Derived の D(A) の両方を使うため。EInfinity は既に Derived を 44 本で import している）。E∞ 構造を使わない部分（D(A) の対象の生成する thick ⊗-ideal、index、安定性）は `Derived/`（`Derived/Gluing/*ThickClosure*` の隣）へ下ろしてよい。**時期・担当**：段 G、M14 と同じ（A5 の中身を書く段階まで不要。担当は E2 レーンか BS かをそのときに決める） |
| M16 | **新設（11-04、W2c 停止点 1′）**：中核の閉包に残るモデル圏の HA（66 本）と ModelBridge（8 本）の最後の入口。`F1` の `CosliceTwistedHomEquivalence` が Reedy の定理を実際に使い、その利用者（`SourceInitial`・`RightRepresentableTwistedArrowEquivalence`・`TwistedHomFunctorMap`）が中核にある。処置：Reedy 非依存の証明（Kerodon の twisted arrow の議論）に書き直すか、F1 の twisted arrow の該当部分を再編する。終われば完了条件 1（中核の閉包にモデル圏のコードが入らない）が完全に成る。入力：`targets/w2c-section5-ha.md` |

置き場所は Stable/Verdier と StablePresentable（R55）。M1〜M7 の詳細は [refactoring-verdier.md](refactoring-verdier.md) §5。
2 件目の外部レビューが M2 の参照として挙げた「Drew, 定理 1.3」は、まだ確かめていない。

## 6. 進め方と検証

**窓の分け方**（10-25 以降、移す元の領域は活発に更新されている。SConstruction 636、LocalizingInvariants 328、KST/Spectra 215、Fibration 200 ファイルが変更された）：

| 窓 | 止める範囲 | 行うこと（この順に直列。同じ集約ファイルを触る作業は並列にしない） | 工数の目安 | 終わりの条件（R40 の強制の段階） |
| --- | --- | --- | --- | --- |
| W0 | 止めない（新しいファイル・scripts・別ブランチだけ） | 段 0（R41 → R40a → R74・R64a → 対象 JSON → R75・統合の道具）、R61b の読解 | 40〜80h（実績は指示書の報告を参照。IF-W0-3 は道具の規則を足しながら進めたため数日かかった） | W1 に入る条件：R41 で基準状態が PASS、既知の失敗の一覧を Claude が承認済み、対象 JSON がそろっている |
| **W1＋W2a（一つの束、10-31 決定）** | 全停止（HA・∞・KST・EInfinity への他セッションの取り込みも約 1 日止める） | 一つの束で：R79（docstring の書き換え HA 約 600・CT 12・ArrowFactorization 3）＋ R75（削除 29 本）＋ W1 の対象（move 62・split 3・reimport 3）＋ W2a の対象（move 1,197・split 9・reimport 2：R72 → R64 → R27 → R56a → R65）→ 下流の一回ビルド（約 20,000 本、単独で 6〜8 時間）→ 保存検査 → verify。R76・R77・R67 は束の後、同じ窓の中で道具（DG 側の `merge_modules.py`）がそろってから | 束の適用と検証で 1〜2 日、R76・R77 で数日 | 中核の閉包に DG・EInfinity・KST・モデル圏のコードなし。層の違反の数が開始時より増えていない。CategoryTheory と HA の相互依存なし |
| W2b | F2・HL・Stable の担当 | R73 → R37 → R38 | 56〜112h、2〜3 日 | 中核の層の順序の違反 0（例外一覧を除く）。**ここで中核の完了条件 1・5 がそろう** |
| W2c | LocalizingInvariants と Fibration のレーン | 段 E（R51 → R52 → R68 → R69 → R70 → R56b）、最後に R45 | 75〜150h、3〜4 日 | 違反が増えていない。移した一般部分の層検査 |

- 各窓の再開の条件は共通：verify 全緑（PASS）、その窓の終わりの条件、保存検査の一致、付け替えの補助の配布。
- 段 F は W2c の後に領域ごとに行う。段 G は窓の外。
- 工数は依存の順に沿って足し直した。合計は約 400〜800h（段 F・G を除く）。止める期間は合わせて 13〜19 日になるので、W2a・W2b・W2c は止める範囲を絞り、他のレーンは動かし続ける。

**指示書の単位**（10-28 ユーザー指示：Codex への指示は大きなまとまりで出す）。一つの指示書の中に「止めて報告する」点を置き、判断が要るところで Claude が検収する。

| 指示書 | 内容 | 窓 |
| --- | --- | --- |
| IF-W0-1 | R41（verify.sh を関門にする） | W0（**完了** 10-28、main `88c477612`。基準実行は全 99 監査 PASS、既知の失敗なし。通しの実行は約 69 分） |
| IF-W0-2 | 道具一式：R40a（層検査）、R74 の道具（分割・import の最小化・保存検査・付け替えの補助）、R64a（骨組み 12 本）、verify.sh の短縮（並列 `VERIFY_JOBS`・キャッシュ `VERIFY_CACHE`・絞り込み `VERIFY_ONLY_AUDITS`） | W0（**完了** 10-29、main `8ff0012d8`。監査の段は 3,782 秒 → 1,551 秒。FixedBoundaryExtensions 1 本の分割試験では、閉包のモデル圏モジュールは 1 本しか減らなかった。他の 11 本の経路が残るためで、R72 で 12 本すべてを切る必要があることを裏づけた） |
| IF-W0-3 | 対象 JSON の作成（w1〜w2c、閉包の規則で move／split／archive／保留を決める）と R61b の読解記録（15 組） | W0（発行 10-29、[指示書](../infinity-codex-w0-3.md)。**w1.json 承認 10-30**：move 62・split 3・reimport 3、保留 13。手作業込みの模擬で W1 の終了条件（中核の閉包に DG・EInfinity なし）を達成。全体 verify PASS（8e6e75d8e）。w2a 以降は作業中） |
| IF-W0-4 | `layers.json` への CategoryTheory の一般部分・トップ階層 12 本・GroupTheory/Coxeter の基盤としての登録、verify runner のメモリ予算つき並列化（監査ごとの RSS の記録、長い順、予算 45 GB）。**R75 は W1＋W2a の束へ、`merge_modules.py`・build lock・warm-up の道具は DG の Codex（DG-W2(a)）へ移管（10-31）** | W0（IF-W0-3 の後） |
| IF-W1W2a | 一つの束：R79（2 コミット）＋ R75 ＋ w1.json ＋ w2a.json を適用 → DG-W1 後の main を取り込み、`.lake/build` を複製 → 下流の一回ビルド → 保存検査 → verify（§10.12〜10.14 の規則）。段 A・B・閉包の切断（R26・R39・R66・R71・R49b・R50）は w1.json の中身として同じ束に含まれる | W1＋W2a |
| IF-W2a-2 | R76 → R77 → R67（Inputs/Homotopy）。`merge_modules.py` がそろってから | W1＋W2a の後半 **完了（11-02、5c909058e）** |
| IF-W2b | R73 → R37 → R38 | W2b | **完了（11-03、3e27dda00）**。指示書 [infinity-codex-w2b.md](../infinity-codex-w2b.md) §1〜§18。中核層間の順序違反 0、F1B の straightening 非依存を保持。W2c への入力：180 本と 6 根の経路（`targets/w2b-section18-stop3.json`） |
| IF-W2c | 群 A（R27・R64・R72 の残り：直接の禁止辺 18 を切り、中核の閉包から KST・モデル圏の HA を消す）→ 群 B（段 E：R51 → R68 → R52 → R69 → R70 → R56b）→ R45 | W2c | 指示書 [infinity-codex-w2c.md](../infinity-codex-w2c.md)（11-03 深夜）。草案は今すぐ、下流は 2a・2b の後 |
| IF-F | 段 F（台帳と整理、最後に R54 の名前空間の付け替え） | W2c の後 |
| IF-G1 | 段 G の最初の束：BS 発の一般論の ∞ 側（M12b・M12c・M12d・β5 の一部） | 窓の外（新規ファイルのみ、別チャット） | 依頼書 [infinity-codex-g1.md](infinity-codex-g1.md)（11-03 深夜） |

**各回の検証**（すべて通るまで次へ進まない）：
- `scripts/refactor/verify.sh`（R41 の強化版）：全体ビルド、自動で列挙した全監査、`main_statement` の sorry 閉包。失敗が一つでもあれば非零で終了する。
- `scripts/check_duplicates.py`。
- R40 の層検査（Python の import グラフ検査で、ビルドは要らない）と、中核の閉包検査。実施の前には対象 JSON の検査（`validate_targets.py`。前の窓の JSON を前提に渡す）。
- 宣言ごとの保存検査（R74 の道具）：移した公開宣言について、名前（対応表で正規化）、型のハッシュ、定義の本体のハッシュ、`#print axioms`、属性が一致すること。ラッパーを作った場合（R50 など）は、定義上の等しさも検査する。
- ビルド時間：窓の前に olean のキャッシュを保存し、回の間は閉包を限ったビルドを使う。第 1 窓の実測は、verify 1,669 秒と監査対象のビルド 3,097 秒。R59 と R41 でビルド対象が増えるので、予算を立てる。

**コミット**：`set -o pipefail` のうえ `git commit --only` で、自分の変更だけを保存する。並行セッションの未コミットの作業（KST/Spectra の PointedUncurry* など）を巻き込まない。

**所有**：移したものの持ち主はコーディネータが割り当て、ユーザーが承認する。局所化と Verdier の API は Sp レーンから移る（決定済み）。

**実施の管理（10-28 ユーザー決定）**：実作業は Claude が管理し、Codex に依頼して進める。
- Claude は、指示書 `infinity-codex-wN-k.md`（IF-WN-k）の作成と、検収（受入条件の確認）、main への取り込みを行う。
- Codex は、使い捨ての worktree で指示書どおりに実施する。
- 指示書の共通の前提は [IF-W0-1](../infinity-codex-w0-1.md) の §0 に置く。

## 7. 範囲外

- KST の内部だけで閉じる整理：R28・R29・R30・R46・R47（R2 計画のまま）。R44（DG → KST/SConstruction の層の逆転）は [DG の整理計画](dg-cleanup-plan.md) の D3 が担う。
- DifferentialGraded/ の整理（検査の処置、入口、層の逆転、1,592 → 126 の統合、R79 の DG 分）：[DG の整理計画](dg-cleanup-plan.md)（10-30 新設。∞ 基盤とは独立に、別の Codex セッションで進める。干渉の取り決めは同 §5）。
- 論文の層の整理と一般論の切り出し（[refactor-plan.md](../../refactor-plan.md)）。ただし CategoryTheory の下位ディレクトリ・Nerve まわり・殻は本計画の R75〜R78（10-30 の伝達）。CategoryTheory のトップ階層の残り（Karoubi・三角圏・t 構造・K₀ など）は論文の層の側。伝達文 §7 の追加で、両側の対象の間の import はなくなった（10-30 時点）。
- BS 側（R35、別セッション）。
- ∞ 層の一般論（M12、BS 発、11-02）：設計書は BS セッション、置き場所と時期は未定。本計画の窓（W0〜W2c）の範囲外。
- 第 II 段の perfect 複体と K₀ の橋（[全体調査](../repository-survey-2026-10-28.md) §7 の #4・#5）。

- **R80（11-01 新設、窓の外・段 G）：巨大な項と重いモジュールの整理。** 計測は [build-profile-2026-10-31](../build-profile-2026-10-31.md)（120 秒超は 7 本、ビルド時間は本数で決まる）と、snapshot で見つかる巨大な項の一覧（`targets/huge-terms-2026-11.md`、例：`KST.SConstruction` の `dgOdotMilnorActualOuterKernelFrameComparison._proof_17`、木に展開して 56 GB）、監査ごとの RSS（IF-W0-4）。対象は KST/SConstruction・IC/Derived・EInfinity/BarrattEccles の定義で、反復する部分項を `abbrev`／補題に切り出す、定義の中の `by` の証明義務を名前つき定理にする、`@[simps]` の自動生成を抑える、など**証明と定義を変える**作業なので窓の外。群ごとに「計測 → 提案 → 承認 → 実装」。目標：モジュールの最大 60 秒、監査の最大 RSS 10 GB、snapshot の木の展開 1 GB 未満。

## 8. 10-28 のレビューで変えた点

レビューは三つの観点で行った：正確さ、実行可能性と順序、読みやすさ。

- 層の順序を Kan < Core から **Core < Kan** に改めた（§3）。
- R56 と R49 の一部は層を破るので、段 B から外して前提を付けた（R56 は段 D、R49b）。R50 の影響は約 277 本に改めた。
- 完了条件 1 を、閉包に入り込む辺の一覧（§4）として具体化した。担当のなかった辺のために R71 を新設した。
- R57 の統合は型が変わるので、窓の外（段 G）へ移した。R62 は公開だけにし、移動は R52 で行う。R63 は EInfinity へ戻す案にした。
- 窓を W0・W1・W2 に分けた。R41 を最初に行う。検証に、層検査・型ハッシュ・ビルド時間の予算を加えた。
- R37・R38・R54・R65 を再見積りした。R31 の置き場所を、中核の外に決めた。
- 用語の表を加えた（§2）。層の名前を統一した。表に前提と検証の列を加えた。
- （同日の追加調査）モデル圏の入り込みはほとんどが付随的だと分かったので、R72 と ModelBridge 層を新設した。FilteredExchange の中身を数え直し、R73（三分割）を新設した。
- （外部レビュー 4 件。いずれも改訂前の版を読んだもの）全体の評価は、どれも「層の順序と Verdier 列の正本の選び方は妥当。ただし、移動の範囲・検証の関門・新しい証明の境界を確定してから実施する」でそろっていた。反映した点：
  - 関門：verify.sh が失敗しても正常終了することを確かめ、R41 を段 0 の関門に書き直した。監査は自動で列挙する（99 本）。
  - 確定リスト：段ごとの対象 JSON（R74）を新設した。R56 を R56a・R56b に、R61 を R61a・R61b に分けた。R49b には依存先の 4 本を加えた。
  - 順序：移し先の骨組み（R64a）を先に作る。R53 の前に retractClosure を Core へ下ろす。
  - 移動以上の変更：R50 の試作（R50p）を窓の前提にした（その後 10-28 に、R50 を「束ねた定義を包む定義」に変えたため、R50p は削除した）。R53 の比較と R57 の条件を段 G に分けた。
  - 数学的な仮定：M2・M5・M7 の仮定を明記した。M8（商の関手性）・M9・M10 を新設した。
  - 窓：W2 を W2a・W2b に分け、上限と再開の条件を付けた。概要で、自立させるのは中核に限ることを明記した。
  - 数値：R48・R52・R63・R66 の数値を直した。
- （第 2 回外部レビュー 2 件。どちらも「段 0 には着手してよい。W1 は窓の割り当てと監査の抜け道を直してから」）反映した点：
  - 窓：R37・R38 が窓に入っていなかったので W2b に入れた。R40 の強制を三段階にした。R39 の前提を R40a に直して循環を解消した。W1 を直列にして 4〜6 日とし、R72 は W2a へ移した。工数を依存の順に足し直した。
  - R49b：SpecifiedHomotopyLift・SpecifiedFunctorEdgeLift を R26 の対象に加えた（第 1 回で直っていなかった点）。
  - R74：JSON の項目、分割の手順、保存検査（定義の本体のハッシュと属性）を具体的にした。
  - §4：HL → DGNerve の 3 辺を加えた。R72：12 本の所在と受入条件を直した。R73：三群を重ならない 369＋1,727＋33 本に直した。
  - M7 と M9 の順序を付けた。M8 の定義域（部分圏の組と、それを保つ完全関手）を明確にした。モデル圏の数値の定義を書いた。
  - IF-W0-1：既知の失敗を「監査ファイル＋失敗の署名」で照合するようにした。監査の一覧を追跡ファイルと比べ、本数が減ったら FAIL にした。ビルドを飛ばした実行は検収に使えないようにした。一覧は Claude の承認の後に確定させ、その後で PASS を確かめる手順にした。故意の失敗の試験を増やした。
- （10-29〜30、IF-W0-3 の実施中の判断。詳細は [指示書 §10](../infinity-codex-w0-3.md)）
  - 入口の辺の切り方を三案（下ろす／上げる／分ける）で比べる規則、pull-down 集合の上限 60 本、手作業の辺を含めた模擬、対象 JSON の拡張（`imports`・`downstream_imports`・`reimport`）。
  - R66 の移し先を Simplicial から Core に変更。R39 は roof の 15 本を `<層>.Roof` へ下ろす（残りは W2c）。R61a の残す側を決定。
  - 道具の規則：空になる側の保存検査、prune で壊れた下流への直接 import の補充、生成補題の帰属（位置 → 接頭辞 → 接尾辞 → 外部定義は transient）、attribute コマンドと無名 instance の扱い、環境の失敗の直列再試行。
  - w1.json を承認（move 62・split 3・reimport 3、保留 13。全体 verify PASS）。
  - CategoryTheory の下位ディレクトリと Nerve まわりの整理を引き継ぎ（R75〜R78）。W2a で K-S• も止める。
- （10-30）DifferentialGraded/ の整理を独立した計画 [dg-cleanup-plan.md](dg-cleanup-plan.md) に分けた。R79 の DG 分（530 本）と R44 の DG 側はそちらへ。
- （10-31）再ビルドの費用の実測（土台の import 行の書き換えで約 9,000〜20,000 本、[verify-build-costs]）から、W1 と W2a を一つの束にし R79・R75 も含めて下流の全ビルドを一回にした。R72 の preflight は 8 本 PASS で止め、9 本目は束へ。分割先の import は使う利用元にだけ足す（IF-W0-3 §10.12〜10.14）。`merge_modules.py` と build lock・warm-up の道具は DG 側へ移管。

## 9. 未決の点（ユーザーまたはコーディネータの判断が要る）

1. **（10-28 決定済み）モデル圏**：中核の下に入れない（R72）。ModelBridge の骨組みは IF-W0-2 で作成済み。R72 は W2a。
2. **（10-28 方針決定、11-02 決定済み）FilteredExchange**：R73 の三分割で処置する。集約からしか届かない約 1,727 本は **`SerrePositivity/Archive/InfinityCategories/FilteredExchange/` へ archive**（追跡するがビルドしない）。`audit_infinity_f2_exchange` は area ごと削除し、使われている側は移った先の層の監査に入る（IF-W2b §1）。
3. **（10-28 決定済み）名前空間**：R54 で最後にまとめて付け替える。新しく作る正本は最初から正しい名前空間で書き、移動のたびに名前空間の対応表を記録する。
4. **（10-28 決定済み）R50**：束ねた定義を残し、束ねない形はそれを包む定義と同値補題として加える。試作（旧 R50p）は不要になった。
5. **Kan と Core の順序**：本計画は、移動だけで済む Core < Kan を採る。外部レビューが支持する Kerodon の順序（Kan < Core）に揃えるには、Kan の証明から Core への依存を外す書き換えが要る。段 G の後で改めて判断する。
6. **（10-31 決定済み）W1 の時期と形**：W1 と W2a を一つの束にし、R79・R75 も含める。DG-W1 の取り込み（10-31）の後、∞ 側の静的検査が PASS したら束を適用し、下流の一回ビルド（6〜8 時間、機械を独占）と verify を通す。その約 1 日は論文の層のコーディネータに HA・∞・KST・EInfinity への取り込みを止めてもらう。（旧記述：対象一覧は確定した。全レーンを止める 4〜6 日の時期を、他のレーン（KST 各レーン・BS・論文の層の整理）の区切りと合わせて決める。
7. **R26 の保留（CoreIsofibration・CorePullbackIso）**：W2a の検査で R56a に影響が出れば、pull-down 集合を加えるか R56a を W2b へ回す（R56a の行の注意）。

## 10. 根拠となる調査

| 文書 | 内容 |
| --- | --- |
| [archive/repository-survey-2026-10-28.md](../repository-survey-2026-10-28.md) | 全体の地図、状態、依存行列、問題点、論文の層との重複 |
| [archive/infinity-outside-survey-2026-10-28.md](../infinity-outside-survey-2026-10-28.md) | ∞ 層の外にある一般論の群（L・F・Sp-S・SC-C の番号）、移し先、重複 |
| [refactoring-verdier.md](refactoring-verdier.md) | Verdier 列の二つの定義、R48〜R57 の詳細、M1〜M7 |
| [refactoring-infinity-r2.md](refactoring-infinity-r2.md)・[archive/r2-a-layers-2026-10-27.md](../r2-a-layers-2026-10-27.md) | R26〜R47・R59〜R67 の詳細、層の逆辺の全件 |
| [refactoring-infinity.md](refactoring-infinity.md) | 第 1 窓（R1〜R25）の記録、旧所在→新所在の対応表、索引 |
| [infinity-foundation-plan-review-request.md](../infinity-foundation-plan-review-request.md)・[同 第 2 回](../infinity-foundation-plan-review-request-2.md) | 外部レビューへの依頼文 |
| [infinity-codex-w0-1.md](../infinity-codex-w0-1.md) | Codex 指示書 IF-W0-1（R41、共通の前提 §0） |
| [infinity-codex-w0-2.md](../infinity-codex-w0-2.md) | Codex 指示書 IF-W0-2（R40a・R74・R64a・verify.sh の短縮） |
| [infinity-codex-w0-3.md](../infinity-codex-w0-3.md) | Codex 指示書 IF-W0-3（対象 JSON と R61b の読解） |
| [handover-ct-to-infinity-2026-10-30.md](handover-ct-to-infinity-2026-10-30.md) | 論文の層の側からの伝達：CategoryTheory の下位ディレクトリと Nerve まわりの調査結果（R75〜R78 の出典） |
