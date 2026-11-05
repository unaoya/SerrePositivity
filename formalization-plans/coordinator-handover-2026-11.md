# 調整役の引き継ぎ（2026-11、整理の期間から段階 II へ）

作成：2026-11-05（前の調整役）。宛先：新しい調整役（Claude Code の新しいチャット）。**F-2 の取り込みの後に §2 を最新にしてから切り替える。**

## 1. 最初に読むもの（この順）

1. 本書。
2. [段階 II の計画（下書き）](stage-ii-plan-draft.md)：目標 A（E3）・目標 B（K の 2 つ）、規則、レーンの構成の案と並列の検討（§5.1）。**ユーザーと相談して確定するのが最初の仕事**。
3. [片付けの一覧](cleanup-list-2026-11.md)：いまのレーンが今週中に行う片付け（C1〜C10）と、段階 II で出す後回しの片付け（L1〜L6）。
4. [coordination.md](coordination.md) §2（ビルドの規則。段階 II に引き継ぐのは計画の §4 の 7 項目）と §4（各レーンの現状）。
5. メモリ（`~/.claude/projects/.../memory/MEMORY.md` から）：特に `elaboration-drift-lessons`（判断表の由来）、`main-worktree-shared-index`、`lake-artifact-cache`、`verify-build-costs`、`bs-session-separate`。
6. 必要に応じて：∞ の計画 [infinity-foundation-plan.md](infinity-foundation-plan.md) 段 G（M1〜M16）、BS の [design-status.md](bhatt-scholze/design-status.md)・[foundation-entry-points.md](bhatt-scholze/foundation-entry-points.md)、K の [kst-lanes/k-theory-kst-route.md](kst-lanes/k-theory-kst-route.md)・[infinity-lanes/foundations.md](infinity-lanes/foundations.md)。整理の期間の指示書（`infinity-codex-*`・`dg-codex-*`）は**読まなくてよい**（結論は計画と一覧に移した）。

## 2. 引き継ぎの時点の状態（11-05 09:30 時点。切り替え前に更新する）

- **主定理の閉包の sorry**：3 つ（E3、`theorem_3_1_K0`、`Section4.supportedRankK0_descent`）。
- **整理（段階 I）**：DG・論文の層・∞ の W0〜W2c・段 F の F-1 は完了。**F-2（KST から移した宣言の名前空間の付け替え、逆依存 11,538 本）を 11-05 09:20 に合図、実行中**。方針は決定済み（移した宣言だけ、F1・F1B・F2 は改名しない、deprecated alias は段 G の最初の区切りまで残す）。停止点 4 の報告を受けて取り込み、改名表を BS・G2・KST へ配る。
- **いまのレーン**（片付けの後に閉じる）：

| レーン | worktree・枝 | 状態 |
| --- | --- | --- |
| ∞ 整理（Codex） | `SerrePositivity-ifw0-3`・`infra/if-f` | F-2 実行中 → 片付け C1〜C3 → 閉じる |
| ∞ 数学 G2（Codex） | `SerrePositivity-ig1`・`math/g2` | F-2 待ち。G8 の四角形（篩包含）と G14 を仕上げて（C4）、IF-G2 の残りを引き継ぎ（C5）→ 閉じる。先行分 f2b665682 は main に入っている |
| BS 設計（Claude Code） | なし（main に記録を直接） | 新しいチャットに移る（ユーザー決定）。**引き継ぎの入口は `bhatt-scholze/design-status.md` §0（29ab2ba87）**。BS-W11 は新しいチャットで、F-2 の取り込みと改名表の後に開始 |
| BS 実装（Codex） | なし（worktree 0 本） | 新しいチャットに移る。BS-W10 は終了（Lemma 10.12 は main） |
| DG（Codex） | `dgw1` | 待機。worktree の削除（C6）で閉じる |
| 論文の層（Claude Code） | なし | **閉じた（11-05）**。refactor-plan.md の状態の節を最終に（8310a7fa7） |

- **main**：作業木はクリーン。直近の取り込みは F-1（9ebbe8e8a）、G2 先行分（55b419a24）、Lemma 10.12（4019014a1）。

## 3. 調整役の仕事のやり方（整理の期間に固まったもの）

- **合図と取り込み**：全ビルド（下流・verify）の開始は調整役が合図する。取り込みは調整役が main で `git merge --no-ff`、衝突は main 側を正に、その後に温め（`lake build SerrePositivity` と、verify の監査対象の一覧のモジュール。監査が import するモジュールは直接ビルドしてから監査を流す）。
- **報告の受け方**：Codex は停止点ごとに報告する。判断が要るものは指示書の末尾に「追記 §n」として書き、短い文面をユーザー経由で渡す。条件付きの事前承認（「下流が通り、保存比較の未説明 0、処置が判断表の範囲なら verify まで進んでよい」）を使うと、夜間に止まらない。
- **確認のたびに見るもの**：`ps` の `lake build`・`verify.sh`（cwd で worktree を特定）、main の作業木がクリーンか、各 worktree の最新コミットと未コミットの数、**BS の main への直接コミット**（BS の決定や ∞ への依頼が書かれる。前の調整役は 11-04 に S3 の経路の決定を見落とした）。
- **よくある停止の型**：import の和による名前の隠蔽・宇宙メタ変数の捕捉・束縛子の型の捕捉・section 変数の脱落・private 参照・データの instance 経路の差。処置は判断表（メモリ `elaboration-drift-lessons`）。保存比較は v3b（証明を標識に置き換え、`_proof_N` を親に束ねる）。
- **別プロジェクト**：`arxiv_formalization` のビルドがときどき走り、CPU を取り合う。止めるかはユーザーに尋ねる。
