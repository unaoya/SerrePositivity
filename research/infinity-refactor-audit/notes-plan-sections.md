# ∞ 圏ノート第 II 部（f-00〜f-05）の計画の記述の原文（2026-11-12）

`exposition/ja/infinity/f-0*.html`（基準 91d8dc9cd、2026-10-28）のうち、整備の計画そのもの（窓の工程、進める順序、R 番号による処置、移し先の表）を、ノートから外す前に写したもの。文は変えていない。計画と状態の正本は `formalization-plans/infinity-foundation-plan.md` と台帳 `formalization-plans/refactor-ledger.md`。ここにある記述の状態は確かめていない（11-12 の照合は `README.md`）。

## f-00-map.html:117（§4 の表（「いまの入り込み」「処置」の列を含む））

4. 中核に入れないもの

入れないもの | 理由 | いまの入り込み | 処置

KST（K 理論の形式化） | ∞ 圏論は K 理論に依存すべきでない。依存の向きが逆 | 中核の閉包に KST が 115 本。主に HL・F1 → KST/Spectra（Kan 複体の道具） | Kan 複体の道具を Kan 層へ移す（R64・R27）

dg（DifferentialGraded・Derived・DGNerve・DoldKan） | dg は ∞ 圏の一つの模型で、応用側にある | DG 約 660 本・Derived 391 本など。入口は Stable → Derived の 3 本、HL → DoldKan など | 一般の補題を下の層へ抽出して切る（R39・R66・R71）

モデル圏 | ∞ 圏論はモデル圏なしで展開できる。モデル圏はできるだけ避ける（10-28 決定） | F1 1,287 本・HL 727 本・Stable 124 本・F2 3,426 本の閉包に入る | 付随的な依存を切り、本当に要る Quillen 系 42 本を ModelBridge へ（R72）

## f-00-map.html:194（§7 整備の工程）

7. 整備の工程（いまどこか）

窓 | 内容 | 終わったときの状態

W0（止めない） | 検証の関門、層検査、対象リスト、保存検査の道具 | 検証が信頼できる。**いまここ（IF-W0-1 実行中）**

W1 | 入口・重複・Verdier の土台、dg への入口の切断 | 中核から DG・EInfinity が消える

W2a | モデル圏の切り離し、Kan・Pointed 層、局所化の存在、hammock 局所化 | 中核から KST・モデル圏が消える

W2b | FilteredExchange の三分割、層の逆辺の解消 | 中核の層の違反が 0 になり、**中核が完成する**

W2c | KST の一般部分（分数・lax・安定の補題）の取り込み | Verdier 商の部品が Stable/ にそろう

## f-02-model-free.html:132（§7 付随的な依存とその切り方）

7. いまの状態：付随的な依存とその切り方（R72）

§2〜§5 の結果は、内容はモデル構造を使っていない。それでも、中核の多くのモジュールの import 閉包にモデル圏のコードが入っている。

層 | 閉包にモデル圏のコードを含むモジュール

Core・Coherent・F1B | 0

F1 | 1,287 / 2,626

HomotopyLimits | 727 / 1,096

Stable | 124 / 702

F2 | 3,426 / 4,629

原因は三種類しかない。

- **使っていない import**：例えば `HA/Simplicial/Generators.lean` は `Transfer.EvaluationSmallness` を import しているが使っておらず、そこから Quillen 随伴やモノイダルモデル圏まで引き込んでいる。

- **純粋なファイルの末尾にある Model の節**：例えば `HA/Simplicial/FixedBoundaryExtensions.lean` は、128 行目から `[ModelCategory SSet]` を仮定する節を持つ。
HL の `KanEquivalencePaths` → `AnodyneIntervalEndpoints`（§3.1）→ `FixedBoundaryExtensions` という一本の経路で、入り込みのほぼすべてが起きている。

- **ディレクトリの置き場所**：純粋な内容のファイルが HomotopyFunctionComplex や Transfer の下にあり、「モデル圏のディレクトリ」として数えられている（例：`Transfer/FullyFaithfulLifting` は純粋な圏論）。

計画の R72 では、HA の 12 本から Model の節と使っていない import を切り離し、純粋な部分を Simplicial・Kan へ移す。12 本の内訳は次のとおり。

- HA/Simplicial：Generators、FixedBoundaryExtensions、LargeParameterExtension、UniverseLiftAnodyne、BisimplicialCofibrancy

- HA/Generated：Basic、FunctorClosure

- HA/Transfer：FullyFaithfulLifting

- HA/HomotopyFunctionComplex：BoundaryOne、DiagonalFrame、QuillenStandardFrame、StandardCosimplicial

import の構造からの試算（ビルドは未検証）では、切り離した後は次のようになる。

- F1・F2：0 本。

- Stable：Derived を経由する 1 本だけ（R39 で切る）。

- HL：Quillen 系の 42 本を ModelBridge へ出した後に 0 本。

最初の試験として、IF-W0-2 で `FixedBoundaryExtensions` の分割を試すことにしている。

この章の内容の所在と移し先

内容 | 今の所在（SerrePositivity/ から）・代表的な宣言 | 状態

small object argument による Kan 置換、`generatedLeft_map` | `HomotopicalAlgebra/Simplicial`。`AnodyneKanReplacement.functor`（AnodyneKanReplacement:79）、`generatedLeft_map`（GeneratedLeftClassFunctor:70） | 済

端点の包含が anodyne、anodyne 局所化 | `HomotopicalAlgebra/Simplicial`。`delta_anodyne`（AnodyneIntervalEndpoints:43）、`map_homotopy_eq`（AnodyneHomotopyLocalization:82） | 済

弱同値の三つの見方の一致（KanTestDetection） | `HomotopicalAlgebra/Simplicial`。`map_isIso_of_tests`（KanTestDetection:83） | 済

bisimplicial 集合の対角 | `HomotopicalAlgebra/Simplicial`、`HomotopicalAlgebra/HomotopyFunctionComplex`、`InfinityCategories/HA/ModelCategoryComparison`。`diagonal_map_anodyne`（DiagonalAnodyne:117）。`HomotopicalAlgebra/Simplicial` の Diagonal{Cofibrations,Quillen,LocalizedEquivalence,Anodyne} はモデル圏を使う | 済

Quillen 随伴 → ∞ 随伴、frame、モデル圏の ∞ 局所化、モデル構造との比較 | `InfinityCategories/HTT/ModelCategoryAdjunctions`、`InfinityCategories/Kerodon/AdjointFunctors/AdjointFunctorsBetweenInfinityCategories`、`InfinityCategories/Project/ModelCategoryComparison`、`InfinityCategories/HA/ModelCategoryComparison`、`EInfinity/SimplicialLocalization`。`quillenCfDerivedAdjunction_exists`（QuillenCfDerivedAdjunction:103）、`StandardFrame.homIso`（StandardFrame:94）、`modelHammock_isLocalization`（ModelHammockLocalization:84） | 済

Kan–Quillen モデル構造の存在 | `InfinityCategories/Project/ModelCategoryComparison/Inputs`。`kanQuillen_model_exists`（KanQuillen:36）。global instance ではない。中核では使わない | 引用（sorry）

## f-04-stable-verdier.html:139（§3.3 二つの形をどう整理するか）

3.3 二つの形をどう整理するか（R50、10-28 決定）
束ねた定義の三つの条件は、どれも \(i\) と \(q\) の下の単体的集合の射（`i.hom`・`q.hom`）しか使わない。`essentialImage i` も「`i.hom` の像と同型な頂点」である。
つまり、束ねた形と束ねない形は、包み方が違うだけで中身は同じである。そこで次のように整理する。

- 束ねた `IsVerdierSequence` は**そのまま残し**、約 277 本の利用元は変えない。

- Stable/Verdier/Basic に、束ねない形 `IsVerdierPair (i : X ⟶ Y) (q : Y ⟶ Z) [IsExactFunctor i] [IsExactFunctor q]`（仮の名前）を置く。インスタンスから `StableCategory`・`ExactMap` を組み立てて、既存の定義に渡すだけの定義にする。同値補題 `isVerdierSequence_iff` も置く。

- 新しく書くコード（M1〜M8）は束ねない形を使う。

## f-04-stable-verdier.html:157（§4 の R53 の段落）

計画の R53：`retractClosure` を Core へ下ろした後、Stable/Verdier に `IsThick` と `thickClosure` を定義だけ置く。dg 版との一致は比較の証明が要るので、段 G（M9）に分ける。

## f-05-verdier-quotient.html:159（§6 進める順序（案））

6. 進める順序（案）

- 整備：R48・R49・R50・R53・R56a・R52（材料を Stable/Verdier と F1B/Localization に集める）。

- M9（厚い閉包の比較）と、分数の機構から安定性の仮定を外す切り出し。

- M2（局所化の安定性）→ M7（商の存在。一般の場合と厚い場合）→ M1（二つの定義の比較）。

- M8（関手性）。§5 の見通しを最初に検討する。

- 必要に応じて道 (B)：M3 → M4 → M5 → M6。M2 が分数で示しにくければ、こちらを主路にする。

- M11（一般の hammock 局所化）は独立していて、写像空間の計算の別の道具として、いつでも進められる。

