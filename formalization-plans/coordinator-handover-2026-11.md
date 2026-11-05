# 調整役の引き継ぎ（2026-11、整理の期間から段階 II へ）

作成：2026-11-05（前の調整役）。宛先：新しい調整役（Claude Code の新しいチャット）。**11-05 09:40 に切り替え（ユーザー決定）。F-2 は実行中のまま引き継ぐ。**

## 1. 最初に読むもの（この順）

1. 本書。
2. [段階 II の計画（下書き）](stage-ii-plan-draft.md)：目標 A（E3）・目標 B（K の 2 つ）、規則、レーンの構成の案と並列の検討（§5.1）。**ユーザーと相談して確定するのが最初の仕事**。
3. [片付けの一覧](cleanup-list-2026-11.md)：いまのレーンが今週中に行う片付け（C1〜C10）と、段階 II で出す後回しの片付け（L1〜L6）。
4. [coordination.md](coordination.md) §2（ビルドの規則。段階 II に引き継ぐのは計画の §4 の 7 項目）と §4（各レーンの現状）。
5. メモリ（`~/.claude/projects/.../memory/MEMORY.md` から）：特に `elaboration-drift-lessons`（判断表の由来）、`main-worktree-shared-index`、`lake-artifact-cache`、`verify-build-costs`、`bs-session-separate`。
6. 必要に応じて：∞ の計画 [infinity-foundation-plan.md](infinity-foundation-plan.md) 段 G（M1〜M16）、BS の [design-status.md](bhatt-scholze/design-status.md)・[foundation-entry-points.md](bhatt-scholze/foundation-entry-points.md)、K の [kst-lanes/k-theory-kst-route.md](kst-lanes/k-theory-kst-route.md)・[infinity-lanes/foundations.md](infinity-lanes/foundations.md)。整理の期間の指示書（`infinity-codex-*`・`dg-codex-*`）は**読まなくてよい**（結論は計画と一覧に移した）。

## 2. 引き継ぎの時点の状態（11-05 09:40）

- **主定理の閉包の sorry**：3 つ（E3、`theorem_3_1_K0`、`Section4.supportedRankK0_descent`）。
- **整理（段階 I）**：DG・論文の層・∞ の W0〜W2c・段 F の F-1 は完了。**F-2（KST から移した宣言の名前空間の付け替え、逆依存 11,538 本）を 11-05 09:20 に合図、実行中**。方針は決定済み（移した宣言だけ、F1・F1B・F2 は改名しない、deprecated alias は段 G の最初の区切りまで残す）。停止点 4 の報告を受けて取り込み、改名表を BS・G2・KST へ配る。
- **いまのレーン**（片付けの後に閉じる）：

| レーン | worktree・枝 | 状態 |
| --- | --- | --- |
| ∞ 整理（Codex） | `SerrePositivity-ifw0-3`・`infra/if-f` | F-2 実行中 → 片付け C1〜C3 → 閉じる |
| ∞ 数学 G2（Codex） | `SerrePositivity-ig1`・`math/g2` | **閉じた（11-05、ユーザー決定。分担は新しく考える）**。未完の作業は枝 `math/g2` の b60279c26（WIP：篩包含の G8 比較の補助、未検証）と、その枝にだけある `formalization-plans/infinity-g2-progress.md` に残っている。**枝 `math/g2` は消さない**。G8 の四角形（篩包含、始対象 (U, 𝟙) による直接比較を推奨）・G14・IF-G2 の残りは、段階 II の新しいレーンの最初の仕事として割り当てる（`infinity-codex-g2.md` §1〜§4）。先行分 f2b665682 は main に入っている |
| BS 設計（Claude Code） | なし（main に記録を直接） | 新しいチャットに移る（ユーザー決定）。**引き継ぎの入口は `bhatt-scholze/design-status.md` §0（29ab2ba87）**。BS-W11 は新しいチャットで、F-2 の取り込みと改名表の後に開始 |
| BS 実装（Codex） | なし（worktree 0 本） | 新しいチャットに移る。BS-W10 は終了（Lemma 10.12 は main） |
| DG（Codex） | なし | **閉じた（11-05）**。worktree・`.lake`・枝 `infra/dg-w3` とも削除済み |
| 論文の層（Claude Code） | なし | **閉じた（11-05）**。refactor-plan.md の状態の節を最終に（8310a7fa7） |

- **main**：作業木はクリーン。直近の取り込みは F-1（9ebbe8e8a）、G2 先行分（55b419a24）、Lemma 10.12（4019014a1）。


### 2.1 新しい調整役が最初にすること（順に）

1. **F-2 の停止点 4 を待つ**（∞ 整理のチャットが報告する。下流 11,538 本＋verify、11-05 の夕方の見込み）。∞ 整理のチャットは F-2 と C1〜C3 が終わるまで閉じない。報告が来たら `IF-F §5〜§7` の条件で判断し、`infra/if-f` を main に取り込む（`git merge --no-ff`、温めは `lake build SerrePositivity` と、監査が import するモジュールを直接ビルドしてから監査）。改名表（`targets/f-namespace-map.json` の確定版）を新しい BS・G2・KST へ配る。
2. ∞ 整理に片付け C1〜C3（`cleanup-list-2026-11.md`）を指示し、取り込んで閉じる。
3. G2 は閉じた。G8 の四角形（篩包含）・G14・IF-G2 の残りを、段階 II の新しいレーンに割り当てる（`math/g2` の WIP と `infinity-g2-progress.md` から再開）。四角形が main に入れば BS の S4 の生成辺が閉じるので、新しいレーンの中で優先度を高くする。
4. 前の調整役が残した片付け C8〜C10：枝の整理（main に入った `infra/*`・`refactor/*`・`math/g1`・`codex/bs-w10-b` など）、整理の期間の指示書の archive、`coordination.md` の段階 II 化、メモリの統合。
5. 段階 II の計画（`stage-ii-plan-draft.md`）をユーザーと確定し、新しいレーンの開始文を書く。新しい BS（設計の Claude Code は `bhatt-scholze/design-status.md` §0 から、実装の Codex は BS-W11 から、F-2 の改名表の後）。

## 3. 調整役の仕事のやり方（整理の期間に固まったもの）

- **合図と取り込み**：全ビルド（下流・verify）の開始は調整役が合図する。取り込みは調整役が main で `git merge --no-ff`、衝突は main 側を正に、その後に温め（`lake build SerrePositivity` と、verify の監査対象の一覧のモジュール。監査が import するモジュールは直接ビルドしてから監査を流す）。
- **報告の受け方**：Codex は停止点ごとに報告する。判断が要るものは指示書の末尾に「追記 §n」として書き、短い文面をユーザー経由で渡す。条件付きの事前承認（「下流が通り、保存比較の未説明 0、処置が判断表の範囲なら verify まで進んでよい」）を使うと、夜間に止まらない。
- **確認のたびに見るもの**：`ps` の `lake build`・`verify.sh`（cwd で worktree を特定）、main の作業木がクリーンか、各 worktree の最新コミットと未コミットの数、**BS の main への直接コミット**（BS の決定や ∞ への依頼が書かれる。前の調整役は 11-04 に S3 の経路の決定を見落とした）。
- **よくある停止の型**：import の和による名前の隠蔽・宇宙メタ変数の捕捉・束縛子の型の捕捉・section 変数の脱落・private 参照・データの instance 経路の差。処置は判断表（メモリ `elaboration-drift-lessons`）。保存比較は v3b（証明を標識に置き換え、`_proof_N` を親に束ねる）。
- **別プロジェクト**：`arxiv_formalization` のビルドがときどき走り、CPU を取り合う。止めるかはユーザーに尋ねる。
