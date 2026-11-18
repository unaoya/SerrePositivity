# 段階 II の計画：主定理の残り 3 つの sorry を消す

作成：2026-11-05（調整役）。状態：**確定（11-05 夜、段階 II の調整役とユーザー）**。本書が段階 II の正本で、整理の期間の指示書（`infinity-codex-*`・`dg-codex-*`）は参照しない。ファイル名は他の文書のリンクを保つため `-draft` のまま。

## 0. 目標

主定理 `SerrePositivity.main_statement` の閉包に残る sorry は 3 つ：

| sorry | 意味 | 消す道筋 |
| --- | --- | --- |
| `BhattScholze.Inputs.exists_perfectoidizationInterfaceE3` | BS の引用（Def 8.2、Lemma 8.4、Prop 8.5、Cor 8.11–8.12、8.14、Thm 10.11）を束ねた界面 | 目標 A：原典の対象を作って E3 の各欄を満たす（stage2 の A 案、設計 A0〜A9） |
| `theorem_3_1_K0` | 論文 Thm 3.1（台つき有理 K 理論の降下） | 目標 B：計画 v2（基盤優先、Land–Tamme の dg 増強形） |
| `Section4.supportedRankK0_descent` | 論文 Lemma 4.6 | 目標 B（同上） |

段階 II の終わりの条件：**主定理の閉包の sorry が 0**（11-05 夜、ユーザー決定）。BS の設計で「恒久の引用」とした 3 件（結晶の de Rham D68 `crystalline_deRham_polynomial_Zp`、BS17 Thm 4.1 (i) `cech_exact_of_vCover_perfect`、BM18 Thm 1.7 `arcSheaf_of_vSheaf_of_valuationSquares`）も証明する。K 理論側も引用なし（公理 (3) の経路も引用を使わない）。監査の許可一覧に sorry は入れない。

## 1. 目標 A：E3 を消す

設計は揃っている：`bhatt-scholze/design/design-status.md`、設計書 A0〜A9、`foundation-entry-points.md`（基盤の入口表）、drafts（`bhatt-scholze/drafts/`）。

### 1.0 出発点：BS の形式化の下書き（drafts）

`formalization-plans/bhatt-scholze/drafts/` に、設計 A0〜A9 に沿って主張の型と骨組みを書いた Lean が **51 本・約 12,900 行**ある（11-05 時点。sorry 893 か所）。`SerrePositivity/` の外なのでルートからも監査からも届かず、ビルドされない。内訳：Sheaves 7（S1〜S8）、DerivedGeneral 3（M13）、Shared 6（cup 積・Bockstein・de Rham・P⁰・descendability など）、A0〜A9 35。置き場所の表とファイルの順序（DAG）は `drafts/README.md`。

**目標 A は drafts を本体へ移しながら sorry を証明に置き換える作業である**：
1. BS 実装（Codex）が、drafts のファイルを決まった置き場所（`InfinityCategories/Sheaves/`・`Derived/`・`EInfinity/`・`BhattScholze/`・`CommutativeAlgebra/` など、`drafts/README.md` と計画の M12〜M15）へ**新規ファイルとして**移し、sorry を証明に置き換える。sorry が 0 になったものから main に入れる（調整役が取り込む）。移したら drafts 側のファイルは消す。
2. 順序は `drafts/README.md` の DAG と下の A-1〜A-6。∞ に頼んでいる一般論（G8 の四角形、G14、G9、G10、G12、M14、M15）が main に入ったところから、それを待つ drafts の sorry が閉じられる。
3. drafts の型は基盤の実際の名前で書かれている（F-2 の改名表の旧名の使用は 0、11-05 確認）。基盤の名前が変わったら調整役が drafts を追従する。
4. 進み具合は「drafts の残り本数と sorry の数」で測る（調整役が design-status.md に記録）。

| 段 | 内容 | 前提 |
| --- | --- | --- |
| A-1 | ∞ 層の一般論 S1〜S8（`InfinityCategories/Sheaves/`）：層条件、Γ・RΓ、脚注 10（Quillen A による余終性）、層化の存在 S4・完全性 S5、空間値の層 S8 | ∞ 供給：G8 の四角形（C4）、G14、G9 の小補題 3 つ、G8 の一般の φ・一般形。G7・G3・G4・G6 は済 |
| A-2 | D(A) の t 構造・Postnikov、導来完備化の ∞ 関手（M13、`Derived/`） | G3（済） |
| A-3 | 古典的単位：根添加、付値環、arc site の 1 圏部分、A0 の site（BS-W11）。Lemma 10.12 は済 | なし |
| A-4 | A0（prismatic site、Čech–Alexander）、A1（Hodge–Tate 比較）、A2（Construction 7.6、CAlg 値の Δ） | A-1・A-2、G10、G12 |
| A-5 | A3〜A8（Lemma 8.4、Prop 8.5、Cor 8.12、Thm 10.11 ほか） | A-4、M14（P⁰）、M15（descendability）、⊗ᴸ（済） |
| A-6 | A9：E3 の組み立て → `Inputs` の証明の置き換え | A-5 |
| A-7 | 恒久の引用としていた 3 件の証明（11-05 夜、ユーザー決定。調査 `bhatt-scholze/notes/citations-survey-2026-11-05.md`）：D68 は対象ごとの HT の命題に置き換えて直接（0.8〜1.5 万行、∞ 不要）、BM18 は G-A6-1 を O の場合に 1 圏で直接（0.3〜0.6 万行、∞ 不要、入力に BS17）、BS17 Thm 4.1 (i) は原典どおり（§1.5 のスキーム論の土台の上） | D68・BM18 は A-3 と並行に先行できる。BS17 は §1.5 |

∞ 側から供給するもの（新しい「∞ 供給」レーンの最初の仕事）：G8 の四角形（篩包含）の残り：IF-G2-finish の段 2 の②の完成（切断の制限と G8 の選択された比較を結ぶ錐の族の同型）、続いて①と四角形（`archive/stage-i/infinity-codex-g2-finish.md`、`archive/stage-i/infinity-g2-progress.md` の末尾。段 1 と段 2 の途中は main にある）。G2 から引き継ぐ IF-G2 の残り（G9 の小補題 3 つ、G8 の一般の φ、G10、G8 の一般形、G12 とその前提 2 つ）、M14（P⁰、`EInfinity/PowerOperation/`）、M15（descendability、`EInfinity/Descendable/`）。

### 1.5 共通の段：スキーム論の土台（A と B の両方が使う、11-05 夜）

BS17 Thm 4.1 (i)（完全環の v 降下）を原典どおり証明するのに要る代数幾何の多くは、K の B-5（Perf(X)、Thomason の局所化、ブローアップ、平坦化）と共通なので、一つの段として独立させる（ユーザー：「どうせ K でもスキーム論は要る」）。担当は⑥（§5.1）。

| 部品 | K | BS17 |
| --- | --- | --- |
| 準連接層・準連接コホモロジー（affine での消滅、Čech） | 要る（L4） | 要る |
| ブローアップ（L7a 済）、Raynaud–Gruson 型の平坦化、Noether 近似、generic flatness | 要る（L7b・L7c） | 要る（BS17 Lemma 2.6） |
| 射影束の公式 | 要る（L5f） | — |
| 固有射のコホモロジーの有限性、コホモロジー版 Artin–Rees（Stacks 02O7）、Stein 分解 | 要確認 | 要る（BST13 Lemma 3.9） |
| Rydh の v 被覆の構造定理（Ryd10 Thm 3.12）、h 層・v 層の判定法（BS17 Thm 2.9・Cor 2.14、Lemma 2.12） | — | 要る |
| 完全環の弱正規性（または Kollár の商）、完全化と平坦性（BS17 Lemma 3.4） | — | 要る |

置き場所：共通の新しい部品は新設の `SerrePositivity/AlgebraicGeometry/`（BS と KST の両方から import できる、KST に依存しない層）。既存の `KST/SchemeLemmas/` は動かさない（移動は保守の束で）。BS17 の定理そのものも一般の主張として `AlgebraicGeometry/` に置き、⑤が drafts の `cech_exact_of_vCover_perfect` をそれで閉じる。

## 2. 目標 B：K 理論の 2 つを消す

計画 v2（`archive/stage-i/infinity-lanes/foundations.md`）と K の経路（`archive/stage-i/kst-lanes/k-theory-kst-route.md`）。引用する文献は Land–Tamme・Tamme・BGT・Waldhausen／Barwick・KST（Thm 3.7 と §3・§5 だけ）・Thomason–Trobaugh・Drinfeld・Kuznetsov–Lunts（KST §4 の群ホモロジーは使わない）。

| 段 | 内容 | 前提 |
| --- | --- | --- |
| B-1 | ∞ 中核の M1〜M11（Verdier 列、安定な局所化、商の存在と関手性、Ind・presentable、Thomason–Neeman、Karoubi 列、hammock 局所化）。置き場所は `Stable/Verdier`・`StablePresentable` | 整理の完了 |
| B-2 | 分数の一般版（L4、R57）、M16（L3） | B-1 と並行可 |
| B-3 | K 基盤 1：Cat^perf、Verdier 列、半直交分解、∞-S• と加法性、fibration・局所化定理、非連結 K（BGT） | B-1 |
| B-4 | K 基盤 2：Tamme の lax pullback の分裂、Land–Tamme の ⊙ と主定理、pro 切除。dg の gluing（β4）と Drinfeld 商（β3） | B-3 |
| B-5 | 八公理と降下の本体（KST Thm 3.7、スキーム補題、有限平坦 transfer など） | B-4。**公理 (3)（冪零不変性）の供給経路を先に再確認**（計画 v2 の未決） |
| B-6 | Thm 3.1・Lemma 4.6 の証明 → 2 つの sorry を置き換える。PC の K₀ のモデルの一本化（論文の層の段階 3 の残り）もここで判断 | B-5 |

**外部の資産（11-05 調査）**：別プロジェクト `../arxiv_formalization`（Lean v4.32.0）に、B-5 のスキーム側で移植を検討できるものがある：Grothendieck アーベル圏の複体の K-injective 解消の存在（Stacks 079P、`Algebra/DerivedCategory/Grothendieck/`、sorry 0）、三角圏の recollement（BBD 1.4.10、`Algebra/Triangulated/`、sorry 0）、スキーム上の加群層の基盤（`AlgebraicGeometry/VecBundle/`、大きく版差の影響が大きい）。Koszul 複体は SerrePositivity 側に既にある。prismatic などは axiom のスタブで使えない。版差（v4.32 → v4.35）の手直しが要るので、L4（Perf(X)・Thomason の局所化）を始めるときに改めて判断する。

## 3. 保守（急がない）

`archive/stage-i/cleanup-list-2026-11.md` §2 の L1〜L6（alias の一括削除、旧 G8 の削除、M16、分数の一般版、台帳の大きな処置、DG の D6〜D8）。L3・L4 は B-2 に含める。

## 4. 規則（整理の期間から引き継ぐもの）

`coordination.md` §2 のうち次だけを本書の規則とする（細目は coordination.md の該当節を参照）：
1. 全ビルド（下流・verify）は機械で一つずつ、暦と合図で。小さなビルド（変更したファイルと直接 importer、数百本以下）は鍵と `ps` を確かめれば合図なしでよい（§2-4a）。
2. main の作業木では編集もビルドもしない。main に直接コミットするときは `git commit --only`（§2-4b）。
3. 新しい数学は新規ファイルだけ。既存の宣言の本文・型・名前を変えるときは、判断表（補充の import、完全修飾、宇宙・名前付き引数・束縛子の型の明示、局所 instance・heartbeat）の範囲で、保存比較 v3b で一致を示す。
4. sorry・公理・新しい引用は残さない。終えられないものは止めて報告。引用を入れるときは監査の許可一覧を更新する。
5. 長く走る枝は、大きな束が main に入るたびに main を取り込む。
6. worktree は `LEAN_Projects.nosync/` の下に、一つのレーンに一つ。
7. Lake キャッシュを全レーンで共有（`~/.zshenv` の 3 変数）。

## 5. レーンの構成（11-05 夜に確定）

### 5.1 決定

ユーザーの決定（11-05）：
1. 調整役は新しいチャット（段階 II の調整役）。BS の二つ（設計の Claude Code、実装の Codex）も新しいチャット。
2. 最初に開く Codex レーンは 4 本：**① ∞ 中核（Verdier）、③ ∞ 供給（層の一般論）、⑤ BS 実装、⑥ スキーム論（A と B の共通の土台、§1.5。当初の「K の古典的な準備」を 11-05 夜に広げた）**。
3. ⑥は Codex だけで、調整役が検収する（公理 (3) の再確認の設計判断も調整役が受け、ユーザーと決める）。
4. ∞ の Codex レーン（①③、のちの②④）の検収は調整役。
5. **BS 設計のチャットは置かない（11-05 夜、ユーザー）**。目標 A の設計・drafts の追従・BS 実装の指示書と検収・design-status の記録も調整役が行う。管理はすべて調整役のチャットに集める。

| レーン | 道具 | 担当 | 最初の仕事 | 検収 | worktree・枝 |
| --- | --- | --- | --- | --- | --- |
| 調整役 | Claude Code | 暦・合図・取り込み・計画の正本、∞ と K の検収、BS の設計と検収（drafts・指示書・design-status） | 本書の確定、各レーンの開始文 | — | main（編集とビルドはしない） |
| ① ∞ 中核 | Codex | B-1 の Verdier 部分（M1・M2・M7・M8）、L4（分数の一般版） | M1・M2・M7（Verdier 商、K 基盤の入口） | 調整役 | `SerrePositivity-inf-core`・`math/inf-core` |
| ③ ∞ 供給 | Codex | 目標 A の基盤：G8 の四角形、G14、G9 の小補題 3 つ、G8 の一般の φ・一般形、G10 | G8 の四角形（IF-G2-finish の②の完成 → ① → 四角形、`archive/stage-i/infinity-g2-progress.md` の末尾） | 調整役（使う側の drafts の型と照らす） | `SerrePositivity-inf-supply`・`math/inf-supply` |
| ⑤ BS 実装 | Codex | A-1〜A-6 の Lean（drafts を本体へ移しながら sorry を証明に置き換える、§1.0） | BS-W11（A-3）→ A-1 の S1・S2・S6、A-2 | 調整役 | `SerrePositivity-bs-impl`・`math/bs-impl`（一度に一つ） |
| ⑥ スキーム論 | Codex | §1.5 のスキーム論の土台（A と B の共通）と B-5 の古典的な部分（KST §5 のスキーム補題）。BS17 Thm 4.1 (i) まで | **公理 (3)（冪零不変性、経路の D9）の供給経路の再確認の報告**（Lean は書かない）→ 平坦化（L7 の残り）→ §1.5 の部品 | 調整役 | `SerrePositivity-scheme`・`math/scheme` |

後から足すレーン：

| レーン | 中身 | 開く条件 |
| --- | --- | --- |
| ④ ∞ 供給：E∞ | M14（P⁰）、M15（descendability）、G12 | ③の G8 の四角形が main に入った後（使うのは A-4・A-5） |
| ② ∞ 中核：その他 | M3〜M6、M11、M16（L3） | ①が軌道に乗ってから（③と同じ `F2/`・`HomotopyLimits` を触るので、③の区切りと暦を合わせる） |
| ⑦ K の dg 側 | K-10 d（gluing 商から Verdier 列の供給。β4 本体は 10-25 に完了）、β6 f・h | ①⑤が軌道に乗ってから |
| K 理論（B-3〜B-6） | K 基盤 1・2、八公理と降下、Thm 3.1・Lemma 4.6 | B-1 の目処（M1・M2・M7 が main に入る）。⑥の結論を引き継ぐ |

触る場所の重なり：⑤と⑥はどちらも `CommutativeAlgebra/` に新規ファイルを置きうる。ディレクトリを分け（⑥は KST §5 用の新しい下位ディレクトリ）、入口ファイル・監査の登録の衝突は取り込みのときに調整役が main 側を正にして解く。

### 5.1.2 追記（11-07、ユーザー）：K を後回しにし、Kerodon・∞・BS に集中

- **K 理論（目標 B）は後回し**。① ∞ 中核（Verdier 商 M1・M2・M7、K 基盤の入口）は止める。K の計画は、対応表 `research/k-coverage/`（問題 10 件）をもとに、改めて相談して見直す。
- **⑥ スキーム論は BS17 Thm 4.1 (i) の経路に絞る**（`stage-ii/scheme/scheme-w1.md` §6）。
- **KL-W1 を先に**（(a)）。③ ∞ 供給は KL-W1 が main に入ってから始める。
- **⑤ BS 実装は二本**：⑤a（BS-DOC1 → BS-W11 → BM18 の経路 B、枝 `math/bs-impl`）、⑤b（D68 の直接証明、`bhatt-scholze/instructions/bhatt-scholze-codex-d68.md`、枝 `math/bs-d68`）。
- 今すぐ始めるもの：⑤a・⑤b・⑥。Kerodon の確認は続け、終わったら KL-W1、その後に ③。
- **⑤a の順（11-07）**：BS-DOC1 → BS-W11 → BS-W12（BM18 の経路 B、G-A6-1。組み立ては ⑥ の BS17 待ち）→ BS-W13（A8-1・A8-2、論文 §10 の古典的な部分）。これで §10 の目標に必要な項目は Thm 10.11 以外が埋まる。
- **⑤b の順（11-07）**：BS-D68（段 1〜3、§5 の Lemma 5.4・Cor 5.5、§4 の Rem 4.19 と模型の上の η）→ 結晶 site と D69 の古典的な部分（a1-design §10.5・§11）→ 段 2 で D69・Thm 5.2・A1-4 の組み立て（∞ 層と ④ の後）。§5 は Thm 5.2 だけが段 2 に残る。§4 は site・RΓ の部分が段 2。

### 5.1.1 追記（11-07、ユーザー）：∞ の配置を Kerodon の構成に合わせる束を先に

Kerodon の対応表の確認（`research/kerodon-coverage/`）が終わったら、`InfinityCategories/` の配置を Kerodon の章・節に合わせ、宣言に `@[kerodon TAG]` を付ける束を出す（指示書 [stage-ii/kerodon-layout-w1.md](stage-ii/bulk/kerodon-layout-w1.md)、KL-W1）。**③ ∞ 供給と① ∞ 中核は、この束が main に入ってから始める**（新しいファイルを積む前の方が安い）。⑤ BS 実装と⑥ スキーム論は並行してよく、束が入ったら改名表で追従する。

### 5.2 並列の上限の検討（11-05、前の調整役）

同時に始められる流れ（依存・触る場所・検収の手で判断）：

| 流れ | 中身 | 触る場所 |
| --- | --- | --- |
| ① ∞ 中核：Verdier | M1・M2・M7・M8、分数の一般版（L4） | `Stable/Verdier`・`StablePresentable` |
| ② ∞ 中核：その他 | M3〜M6、M11、M16（L3） | `F2/`・`F1/`・`HomotopyLimits` |
| ③ ∞ 供給：層の一般論 | G9 の小補題 3 つ、G8 の一般形、G10 | `F2/`・`HomotopyLimits`・`Derived` |
| ④ ∞ 供給：E∞ | M14、M15、G12 | `EInfinity/`・`ModelBridge` |
| ⑤ BS 実装 | BS-W11、A-2、A-1 の S1・S2・S6 | `BhattScholze/`・`CA/`・`Sheaves/`・`Derived/` |
| ⑥ K の古典的な準備（11-05 夜に⑥ スキーム論へ広げた、§1.5） | KST §5 のスキーム補題、可換環論、公理 (3) の再確認 | `CommutativeAlgebra/`・`KST/` |
| ⑦ K の dg 側 | β4（dg の gluing）、β5 の残り（11-05 の調査：β4・β5 は完了済み、残りは K-10 d と β6 f・h。§5.1 で直した） | `DifferentialGraded/`・`Derived/` |

上限は 7 本。律速は検収（前の調整役の想定は BS 設計一本・調整役一本。11-05 夜に調整役一本に集めた）。前の調整役の推奨は 5 本（①③④⑤⑥）だったが、④は A-4・A-5 まで要らないので、③の最初の区切りの後に回した（§5.1）。

## 6. 暦の目安

| 時期 | 内容 |
| --- | --- |
| 11-05 夕 | F-2 の取り込み、整理（段階 I）の完了 |
| 11-05 夜 | 片付け（`archive/stage-i/cleanup-list-2026-11.md` §1）の完了、本書の確定 |
| 11-06〜 | ①③⑤⑥の開始（開始文は調整役） |
| ③の G8 の四角形の取り込み | ④の開始、BS の S4 の生成辺 |
| 段 G の最初の区切り（〜12 月上旬） | 保守 L1・L2（alias・旧 G8 の削除） |
| B-1 の目処 | K 理論レーンの開始 |
