# BS 作業チャットへの引き継ぎ（2026-10-25）

作成：コーディネータ（進捗確認チャット）。宛先：Bhatt–Scholze（以下 BS）側を担当する、この VS Code 上の新しい Claude Code セッション。
作業の性格は「今回の引用（E3）に必要な範囲に絞って原典を最初から学びながら、勉強ノートを HTML で書き、
既存コードをリファクタしつつ、必要な形式化を進める」。∞ 圏基盤の 8 レーンのような自律運転ではなく、ユーザーと対話しながら進める。
役割分担：このセッションは学習・ノート執筆・コードの読解と設計・リファクタと形式化の作業指示書の作成・結果の検収を担い、
**Lean のコーディングはこれまでどおり Codex に依頼する**（指示書はユーザーが Codex へ渡す）。§7 の規約は Codex の成果物にも適用する。

## 1. 文脈

- 主定理 `SerrePositivity.main_statement` の未証明依存は 3 件だけ（`scripts/refactor/audit_sorries.lean`、最終確認 2026-10-24 17:29）：
  `BhattScholze.Inputs.exists_perfectoidizationInterfaceE3`（BS 側）、`theorem_3_1_K0`・`Section4.supportedRankK0_descent`（K 理論側）。
  K 側は ∞ 圏基盤の 8 レーン（Ind・P・D・D2・Sp・K-S•・K-B と完了した E2）が並行作業中で、BS 側とは独立。
- BS 側の sorry は `SerrePositivity/BhattScholze/Inputs/PerfectoidizationInterface.lean:54` の一件。
  型は `Nonempty (PerfectoidizationInterfaceE3 R p hR)`（`BhattScholze/PerfectoidizationInterface/Interface.lean`）。
  欄は perfd（通常代数を D(R) へ送る関手）・unit・H⁰ の環構造・coconnective（Lemma 8.4）・universal（Cor 8.14）・
  limitCone／limit_isLimit（Prop 8.5）・integral（Thm 10.11＝Thm 1.17(1)）・excision（Cor 8.12）。
- 2026-10-25 05:35 に E2 レーンが G1′ を完了し、同じ界面を E∞ 代数の ∞ 圏 CAlg_R で述べ直した
  （`EInfinity/Perfectoidization/Interface.lean` の `PerfectoidizationInterfaceCAlg`、`DerivedCorollary.lean` の
  `PerfectoidizationInterfaceCAlg.toE3`・`nonempty_e3_of_cAlg`）。従って目標は
  「`PerfectoidizationInterfaceCAlg R p hR` を構成する」と言い換えられる。原典の S_perfd（Def 8.2）は p 完備 E∞-S 代数なので、この形が原典に近い。

## 2. 到達点（2026-10-25 09:00 に `#print axioms` で再確認）

| 内容 | 公開名 | 公理 |
| --- | --- | --- |
| B0〜B2：δ 環、prism、完全 prism と perfectoid 環の対応（§2・§3、Thm 3.10） | `BhattScholze/DeltaRing.lean`、`PerfectOrientedPrism.lean`、`PerfectPrismQuotientPerfectoid.lean` ほか | 標準三公理 |
| B3：Cor 7.3 semiperfectoid 商の perfectoid 化の存在と普遍性 | `BhattScholze.exists_perfectoidization_of_semiperfectoid_quotient` | 標準三公理 |
| B4：Thm 7.4 導来 p 完備な全射商の perfectoid 化は全射（André を使わない経路） | `BhattScholze.surjective_of_isPerfectoidization_of_semiperfectoid_quotient` | 標準三公理 |
| B5：Lemma 10.3、Remark 10.7 の冪等性 | `BhattScholze.lemma103_perfectoidTensor`、`perfectoidIdeal_isAlmostZero_extension` | 標準三公理 |
| André：Thm 7.14（Remark 7.15 の pd 包計算と ω₁ 反復による別証明） | `BhattScholze.Andre.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed` | 標準三公理 |
| Prop 8.13 環版 | `BhattScholze.prop813CompletedTensorMap_isPerfectoidization` | 標準三公理 |
| Thm 1.17(1) 有限代数版 | `BhattScholze.exists_perfectoidization_of_finite` | **sorryAx**（E3 経由） |

CLMST の Prop 2.4.7・Cor 4.0.4 はこれらと E3 から証明済み（10-17）。CLMST Prop 4.0.10 は Thm 1.17(1) の代わりに Cor 7.3 へ付け替え済み。
原典のコホモロジー（§4〜§6）と Construction 7.6 は一切使っていない。E3 の消費は主定理の経路で二箇所：
`Inputs.exists_perfectoidization_of_finite`（`CommutativeAlgebra/Perfectoidization.lean` → `CLMST/Algebra.lean` の `RPerfd`）と
`perfectoidization_excision_isPullback`（`BhattScholze/Inputs/ArcExcision.lean` → CLMST Prop 2.4.7 の excision）。
詳しい利用経路は `bhatt-scholze-stage2.md` §1。

## 3. 原典の節と形式化状況

著者版 [paper/refs/BS-prisms-author.pdf](../../../paper/refs/BS-prisms-author.pdf)（arXiv v3 とは §1・§2・§7.3 以降・§8・§9 の番号がずれる。コードの引用番号は著者版）。

| 節 | 内容 | 状況 |
| --- | --- | --- |
| 2 δ 環 | δ 環、Frobenius 持ち上げ、perfection、完備化 | 必要部分は証明済み。docstring から 142 箇所が参照 |
| 3 prism | 剛性、完全 prism ↔ perfectoid 環（Thm 3.10）、prismatic envelope（Prop 3.13） | Thm 3.10・Lemma 3.5・3.9 済み。Prop 3.13 は向き付きの特殊形のみ |
| 4 prismatic site と HT 比較の定式化 | Δ_{R/A}、Lemma 4.8、Thm 4.11 | 未形式化（Lemma 4.8 の特殊形のみ） |
| 5・6 HT 比較と結晶比較 | Thm 5.2、Cartier、Thm 6.3 | 未形式化 |
| 7 semiperfectoid と混標数の perfection | Prop 7.2、Cor 7.3、Thm 7.4、Construction 7.6、Prop 7.11、Thm 7.14 | Cor 7.3・Thm 7.4・Thm 7.14 済み（別経路）。Construction 7.6 は未 |
| 8 一般の perfection | Def 8.2、Lemma 8.4、Prop 8.5、Prop 8.10、Cor 8.11・8.12、Prop 8.13、Cor 8.14 | Prop 8.13 環版のみ。他は界面 E3 の欄として引用 |
| 10 almost purity | Lemma 10.3、Prop 10.2・10.4、Remark 10.7、Thm 10.9、Thm 10.11 | Lemma 10.3・Remark 10.7 冪等部分済み。Thm 10.11 は E3 の integral 欄 |
| 9、11〜18 | étale 比較、Nygaard、q-de Rham、AΩ ほか | 主定理に不要、対象外 |

## 4. BS-0 調査の結論（`bhatt-scholze-stage2.md`、2026-10-25 05:48）

- **B（既証部品だけの迂回）は閉じない**。主定理が使う S = R ⊗_A D（有限、一般に全射商でも有限エタールでもない）の perfectoid 化の存在と、
  Prop 2.4.7 の有限比較・rank 四角形の excision は、Cor 8.12／Thm 10.9 の「almost 比較」そのもの。
- **A（原典経路）を推奨**。最小部分集合は A0〜A9（prismatic site と Čech 計算 → 結晶・HT 比較 → Construction 7.6 → Def 8.2・Lemma 8.4 →
  Prop 8.5 → arc 降下と Cor 8.12 → Prop 8.13 導来版・Cor 8.14 → §10 の almost-connective 部分 → E3 への代入）、概算 35〜85 人週。
  外部文献の最小採用集合は BS17・BM18・Mat16・Lur11 の切片（新規引用にせず形式化対象）。
- 最初の実装単位は「固定完全 prism (A,(d)) 上の一変数多項式の Čech 模型と HT 比較」。単位・乗法・Frobenius・mod (p,d) が一致してから多変数・左 Kan 延長へ。
- **C（外部引用の受容）**は方針変更になるのでユーザー判断。現時点の完了条件（入力を消す・新規引用なし）は満たさない。

## 5. コードと文書の所在

- `SerrePositivity/BhattScholze/`：976 ファイル・約 10.5 万行。`Andre/`（342、André の補題）、`PerfectoidizationInterface/`（11、界面の型と導出）、
  `Inputs/`（5、唯一の sorry と界面からの二入口）。残りは δ 環・prism・perfectoid・compatible roots・semiperfectoid の本体。
- `SerrePositivity/CLMST/`（146）、`SerrePositivity/CommutativeAlgebra/`（465、完備化・平坦性・AIC など BS と CLMST が共有する基盤）、
  `SerrePositivity/Inputs/Perfectoidization.lean`。
- `SerrePositivity/EInfinity/Perfectoidization/`（E2 所有、CAlg_R 版の界面）。
- 文書：[bhatt-scholze.md](bhatt-scholze.md)（正本。§0「二入力」は旧状態で、現在は E3 一件）、
  [perfectoidization-interface.md](../perfectoidization-interface.md)（界面の原典照合と型）、
  [bhatt-scholze-refactoring.md](bhatt-scholze-refactoring.md)（§13 の共通抽出 Q10・Q1・Q8、既知の問題）、
  [bhatt-scholze-stage2.md](bhatt-scholze-stage2.md)（BS-0）、`archive/bhatt-scholze-*.md`（旧計画と実行記録）。
- 解説：`exposition/ja/exposition-ja.tex` 付録 A の `par:bs-thm74`・`par:bs-andre`・`par:bs-andre-envelope`・`par:bs-lemma103`・`par:bs-cor812`。
- 監査：`scripts/audit_bhatt_scholze*.lean`（本体・b4・b5・prop813・arc_excision・andre_conditional・refactoring）、`scripts/audit_clmst*.lean`、
  `scripts/audit_axioms.lean`、`scripts/refactor/audit_sorries.lean`。実行は `lake env lean scripts/<name>.lean`。
- 既知の問題：`scripts/audit_bhatt_scholze_refactoring.lean:838` が `Ideal.Quotient.mk` の環 instance 不一致で失敗（10-24 記録、BS 側で修正する）。
- 参照：`paper/refs/BS-prisms-author.pdf`、`paper/refs/CLMST-2209.04046v4.pdf`。

## 6. 所有範囲と境界

- 所有（編集可）：`BhattScholze/`、`CLMST/`、`Inputs/Perfectoidization.lean`、`CommutativeAlgebra/` のうち BS・CLMST だけが使う部分、
  `formalization-plans/bhatt-scholze*.md`・`perfectoidization-interface.md`、解説付録 A の BS 段落、`scripts/audit_bhatt_scholze*`・`audit_clmst*`。
- 読み取り専用：`EInfinity/`（E2 は完了・停止中。変更が必要なら進捗確認チャット経由で依頼）、`InfinityCategories/`、`KST/`、`DifferentialGraded/`、
  `HomologicalAlgebra/`。`CommutativeAlgebra/` の一般部分を変えるときは、`grep -rl` で BS・CLMST 以外の利用先がないことを確認してから。
- モジュールの移動・改名は BhattScholze/・CLMST/ 内に限り可。ただし外から import されるモジュール
  （`grep -rln 'BhattScholze\.' SerrePositivity --include='*.lean' | grep -v '^SerrePositivity/BhattScholze/'` で確認。
  `EInfinity/Perfectoidization/`、`CommutativeAlgebra/Perfectoidization.lean`、`CLMST/`、`Inputs/`、root 集約）は公開名・型を保つ。
  移動には `scripts/move_module.py`（JSON 計画）が使える。
- ビルドは自分の対象だけ：`lake build SerrePositivity.BhattScholze.<Module>` と監査スクリプト。root の `lake build SerrePositivity` は
  8 レーンが並走中は実行しない（oleans の競合）。全体監査が必要なときは進捗確認チャットに相談。

## 7. 規約（他レーンと共通）

- 新規 sorry・公理・引用を加えない。E3 の sorry を分割して複数の入力にしない（分割するなら明示入力として `bhatt-scholze.md` の表に登録し、完成扱いにしない）。
- docstring は 概要／方針／規約／使われ方（README「Conventions」）。原典番号は著者版。
- コミットは所有ファイルのみ `set -o pipefail` のうえ `git commit --only`。実施記録はコミットメッセージ、計画本文は 300 行以内。
  末尾に `Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>`。
- 決定と設計変更は `bhatt-scholze.md` の変更記録に日時付きで残す。他レーンの API に関わる変更は進捗確認チャットへ（ユーザー経由）。

## 8. 勉強ノート（HTML）と Codex への依頼

- ノートは `exposition/ja/bs/` に置き、形式は `exposition/ja/infinity/` に合わせる：`index.html`（目標・章・読書ルート・リファクタ記録・各章の書き方）、
  章ごとの HTML、共通 `style.css`（infinity のものを複製）、KaTeX は CDN、Lean のファイルへは `../../../SerrePositivity/...` の相対リンク、
  宣言名は `<code>`。`build_artifact.py` を複製すれば claude.ai Artifact 用の 1 ページにまとめられる。
- 各章の書き方（infinity と同じ）：冒頭に基準コミット。数学の定義・定理を述べ、対応する Lean の宣言名とファイルを添える。
  証明は方針・鍵になる補題・Lean での組み立て方まで追う。原典との差（経路・規約・一般性）は独立した囲み。
  リファクタ候補は赤い囲みで番号を全章で通す（∞ 圏側の R 番号と衝突しないよう **BR1、BR2、…**）。末尾に「この章で押さえること」。
  BS 固有に加える節：「形式化の状況」（証明済み／界面で引用／未着手を宣言名付きで）と「形式化の課題」（Codex へ渡せる粒度の作業項目）。
- 章立て（今回の引用に必要な範囲に絞る。原典の番号は著者版）：
  第 0 章 全体地図（E3 とは何か、主定理までの経路、A0〜A9）／第 1 章 §1 の Def 1.1〜1.6 と主結果の読み方／第 2 章 §2 δ 環／
  第 3 章 §3 prism と完全 prism（Thm 3.10、Prop 3.13）／第 4 章 §4.1 prismatic site の定義と Lemma 4.8（A0 に必要な範囲）／
  第 5 章 §7 semiperfectoid と perfection（Cor 7.3、Thm 7.4、Construction 7.6 の概要、Thm 7.14 と別証明）／
  第 6 章 §8 一般の perfection（Def 8.2〜Cor 8.14）／第 7 章 §10 almost purity のうち Lemma 10.3・Thm 10.9 の主張・Thm 10.11／
  第 8 章 §5〜§6 Hodge–Tate 比較（A1 に着手する段階で書く）。
- Codex への依頼は作業指示書の形にする：対象ファイル（所有範囲内）、追加・変更する宣言とその型、使ってよい既存の公開名、禁止事項
  （新規 sorry・公理・引用、他レーンのファイルの変更、root ビルド）、受入条件（対象ビルドのコマンド、該当監査のコマンド、docstring 規約、
  `git commit --only` と帰属行）。結果は `#print axioms` と監査の再実行で検収し、ノートの「形式化の状況」を更新する。

## 9. 推奨する進め方

1. **読む**（半日）：本書 → `bhatt-scholze.md` §0〜§4 → `bhatt-scholze-stage2.md` → 解説付録 A の五段落 → `exposition/ja/infinity/index.html` と第 0 章（ノートの型を知るため）。
   `#print axioms` で §2 の表を自分でも再現する（既存 olean を import する一時ファイルで `lake env lean`、ビルドはしない）。
2. **ノートの骨格**：`exposition/ja/bs/index.html` と第 0 章を書く（基準コミット、章立て、読書ルート、BR 番号の空の記録）。
3. **章ごとに三本立て**：原典の節を読む → その章のノートを書く（数学・Lean 対応・原典との差・BR 候補・形式化の課題）→
   その章で見つけた BR 候補のうち小さいものと、形式化の課題を Codex の作業指示書にして渡す → 検収してノートと `bhatt-scholze.md` の変更記録を更新。
   最初の章（§2・§3）では `bhatt-scholze-refactoring.md` §13 の Q10 → Q1 → Q8 と監査 838 行の修正を合わせて扱う。
4. **A0 の設計**（第 4 章の後）：固定完全 prism (A,(d)) 上の affine prismatic site と一変数多項式の Čech 模型。紙上の設計
   （対象・射・位相・Čech 複体・Frobenius・mod (p,d) の各主張と既存宣言の対応）を第 4 章と `bhatt-scholze-stage2.md` に書き、
   ユーザーの了承後に Codex へ。E∞／animated 環が要る部分は EInfinity の `CAlg_R`・`cAlgForgetDerived` と P の P_Σ を読み取り専用で使い、
   dg 可換代数を全 E∞ 代数と同一視しない。
5. 以後は A1（HT 比較、第 8 章）→ A2（Construction 7.6）… の順。各単位の着手時に三段目（3〜8 個）を決め、区切りごとに進捗確認チャットへ報告する。

## 10. 連絡

- 進捗の報告・供給依頼・設計変更の採否はユーザー経由で進捗確認チャットへ。8 レーンの進捗表 `foundations-progress.md` には BS ブロックを新設する予定なので、
  最初の報告で一段目・二段目の案（A0〜A9 を基に）を提示する。
