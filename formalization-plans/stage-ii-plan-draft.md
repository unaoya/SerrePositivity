# 段階 II の計画（下書き）：主定理の残り 3 つの sorry を消す

作成：2026-11-05（調整役）。状態：**下書き**（ユーザーがレーン構成を決めてから確定）。確定したら本書が段階 II の正本になり、整理の期間の指示書（`infinity-codex-*`・`dg-codex-*`）は参照しない。

## 0. 目標

主定理 `SerrePositivity.main_statement` の閉包に残る sorry は 3 つ：

| sorry | 意味 | 消す道筋 |
| --- | --- | --- |
| `BhattScholze.Inputs.exists_perfectoidizationInterfaceE3` | BS の引用（Def 8.2、Lemma 8.4、Prop 8.5、Cor 8.11–8.12、8.14、Thm 10.11）を束ねた界面 | 目標 A：原典の対象を作って E3 の各欄を満たす（stage2 の A 案、設計 A0〜A9） |
| `theorem_3_1_K0` | 論文 Thm 3.1（台つき有理 K 理論の降下） | 目標 B：計画 v2（基盤優先、Land–Tamme の dg 増強形） |
| `Section4.supportedRankK0_descent` | 論文 Lemma 4.6 | 目標 B（同上） |

段階 II の終わりの条件：主定理の閉包の sorry が、BS の恒久の引用 3 件（結晶の de Rham D68、BS17 Thm 4.1、BM18 Thm 1.7）だけになり、それらが監査の許可一覧に入っていること。K 理論側は引用なし。

## 1. 目標 A：E3 を消す

設計は揃っている：`bhatt-scholze/design-status.md`、設計書 A0〜A9、`foundation-entry-points.md`（基盤の入口表）、drafts（`bhatt-scholze/drafts/`）。

| 段 | 内容 | 前提 |
| --- | --- | --- |
| A-1 | ∞ 層の一般論 S1〜S8（`InfinityCategories/Sheaves/`）：層条件、Γ・RΓ、脚注 10（Quillen A による余終性）、層化の存在 S4・完全性 S5、空間値の層 S8 | ∞ 供給：G8 の四角形（C4）、G14、G9 の小補題 3 つ、G8 の一般の φ・一般形。G7・G3・G4・G6 は済 |
| A-2 | D(A) の t 構造・Postnikov、導来完備化の ∞ 関手（M13、`Derived/`） | G3（済） |
| A-3 | 古典的単位：根添加、付値環、arc site の 1 圏部分、A0 の site（BS-W11）。Lemma 10.12 は済 | なし |
| A-4 | A0（prismatic site、Čech–Alexander）、A1（Hodge–Tate 比較）、A2（Construction 7.6、CAlg 値の Δ） | A-1・A-2、G10、G12 |
| A-5 | A3〜A8（Lemma 8.4、Prop 8.5、Cor 8.12、Thm 10.11 ほか） | A-4、M14（P⁰）、M15（descendability）、⊗ᴸ（済） |
| A-6 | A9：E3 の組み立て → `Inputs` の証明の置き換え | A-5 |
| A-7 | 恒久の引用 3 件を監査の許可一覧へ | A-6 |

∞ 側から供給するもの（新しい「∞ 供給」レーンの最初の仕事）：G2 から引き継ぐ IF-G2 の残り（G9 の小補題 3 つ、G8 の一般の φ、G10、G8 の一般形、G12 とその前提 2 つ）、M14（P⁰、`EInfinity/PowerOperation/`）、M15（descendability、`EInfinity/Descendable/`）。

## 2. 目標 B：K 理論の 2 つを消す

計画 v2（`infinity-lanes/foundations.md`）と K の経路（`kst-lanes/k-theory-kst-route.md`）。引用する文献は Land–Tamme・Tamme・BGT・Waldhausen／Barwick・KST（Thm 3.7 と §3・§5 だけ）・Thomason–Trobaugh・Drinfeld・Kuznetsov–Lunts（KST §4 の群ホモロジーは使わない）。

| 段 | 内容 | 前提 |
| --- | --- | --- |
| B-1 | ∞ 中核の M1〜M11（Verdier 列、安定な局所化、商の存在と関手性、Ind・presentable、Thomason–Neeman、Karoubi 列、hammock 局所化）。置き場所は `Stable/Verdier`・`StablePresentable` | 整理の完了 |
| B-2 | 分数の一般版（L4、R57）、M16（L3） | B-1 と並行可 |
| B-3 | K 基盤 1：Cat^perf、Verdier 列、半直交分解、∞-S• と加法性、fibration・局所化定理、非連結 K（BGT） | B-1 |
| B-4 | K 基盤 2：Tamme の lax pullback の分裂、Land–Tamme の ⊙ と主定理、pro 切除。dg の gluing（β4）と Drinfeld 商（β3） | B-3 |
| B-5 | 八公理と降下の本体（KST Thm 3.7、スキーム補題、有限平坦 transfer など） | B-4。**公理 (3)（冪零不変性）の供給経路を先に再確認**（計画 v2 の未決） |
| B-6 | Thm 3.1・Lemma 4.6 の証明 → 2 つの sorry を置き換える。PC の K₀ のモデルの一本化（論文の層の段階 3 の残り）もここで判断 | B-5 |

## 3. 保守（急がない）

`cleanup-list-2026-11.md` §2 の L1〜L6（alias の一括削除、旧 G8 の削除、M16、分数の一般版、台帳の大きな処置、DG の D6〜D8）。L3・L4 は B-2 に含める。

## 4. 規則（整理の期間から引き継ぐもの）

`coordination.md` §2 のうち次だけを本書の規則とする（細目は coordination.md の該当節を参照）：
1. 全ビルド（下流・verify）は機械で一つずつ、暦と合図で。小さなビルド（変更したファイルと直接 importer、数百本以下）は鍵と `ps` を確かめれば合図なしでよい（§2-4a）。
2. main の作業木では編集もビルドもしない。main に直接コミットするときは `git commit --only`（§2-4b）。
3. 新しい数学は新規ファイルだけ。既存の宣言の本文・型・名前を変えるときは、判断表（補充の import、完全修飾、宇宙・名前付き引数・束縛子の型の明示、局所 instance・heartbeat）の範囲で、保存比較 v3b で一致を示す。
4. sorry・公理・新しい引用は残さない。終えられないものは止めて報告。引用を入れるときは監査の許可一覧を更新する。
5. 長く走る枝は、大きな束が main に入るたびに main を取り込む。
6. worktree は `LEAN_Projects.nosync/` の下に、一つのレーンに一つ。
7. Lake キャッシュを全レーンで共有（`~/.zshenv` の 3 変数）。

## 5. レーンの構成（案。ユーザーが決める）

| レーン | 道具 | 担当 | 最初の仕事 |
| --- | --- | --- | --- |
| 調整役 | Claude Code | 暦・合図・取り込み・レーン間の窓口・計画の正本 | 本書の確定、新しいレーンの開始文 |
| ∞ 中核 | Codex | B-1・B-2（M1〜M11、M16、分数の一般版）、保守 L1・L2 | M1・M2・M7（Verdier 商、K 基盤の入口） |
| ∞ 供給 | Codex | 目標 A の基盤（IF-G2 の残り、M14・M15） | G9 の小補題 3 つ（S3 用）、G10 |
| BS 設計 | Claude Code | 目標 A の設計・検収・∞ への依頼 | （いまの BS セッションを続けるか新しくするかを決める） |
| BS 実装 | Codex | A-1〜A-6 の Lean | BS-W11（A-3）→ S1〜S8 |
| K 理論 | Codex（＋設計の Claude Code） | B-3〜B-6 | **B-1 の目処が立ってから開始** |

決めること：
1. このレーン構成でよいか（本数、道具、∞ を中核と供給の二本に分けるか）。
2. 調整役をこのチャットで続けるか、新しいチャットにするか（このチャットは長いので新しくすることを推奨。引き継ぎは本書・`coordination.md` §4・メモリで足りるようにする）。
3. BS の二つ（設計の Claude Code、実装の Codex）は、いまのチャットを続けるか新しくするか。
4. K 理論レーンの開始の時期（推奨：M1・M2・M7 の後）。


### 5.1 並列の上限の検討（11-05）と決定

**決定（11-05、ユーザー）**：調整役は新しいチャットにする。BS（設計の Claude Code、実装の Codex）も新しいチャットにする。レーンの数は「どこまで並列にできるか」で決める。

同時に始められる流れ（依存・触る場所・検収の手で判断）：

| 流れ | 中身 | 触る場所 |
| --- | --- | --- |
| ① ∞ 中核：Verdier | M1・M2・M7・M8、分数の一般版（L4） | `Stable/Verdier`・`StablePresentable` |
| ② ∞ 中核：その他 | M3〜M6、M11、M16（L3） | `F2/`・`F1/`・`HomotopyLimits` |
| ③ ∞ 供給：層の一般論 | G9 の小補題 3 つ、G8 の一般形、G10 | `F2/`・`HomotopyLimits`・`Derived` |
| ④ ∞ 供給：E∞ | M14、M15、G12 | `EInfinity/`・`ModelBridge` |
| ⑤ BS 実装 | BS-W11、A-2、A-1 の S1・S2・S6 | `BhattScholze/`・`CA/`・`Sheaves/`・`Derived/` |
| ⑥ K の古典的な準備 | KST §5 のスキーム補題、可換環論、公理 (3) の再確認 | `CommutativeAlgebra/`・`KST/` |
| ⑦ K の dg 側 | β4（dg の gluing）、β5 の残り | `DifferentialGraded/`・`Derived/` |

上限は 7 本。律速は検収（BS 設計一本、調整役一本）。**推奨は 5 本から（①③④⑤⑥）**、②⑦は①⑤が軌道に乗ってから足す。ユーザーが本数を決める。

## 6. 暦の目安

| 時期 | 内容 |
| --- | --- |
| 11-05 夕 | F-2 の取り込み、整理（段階 I）の完了 |
| 11-05〜08 | 片付け（`cleanup-list-2026-11.md` §1）。並行して本書の確定と新しいレーンの開始 |
| 11-08〜 | 目標 A（BS 実装・∞ 供給）と目標 B の B-1（∞ 中核）を並行 |
| 段 G の最初の区切り（〜12 月上旬） | 保守 L1・L2（alias・旧 G8 の削除） |
| B-1 の目処 | K 理論レーンの開始 |
