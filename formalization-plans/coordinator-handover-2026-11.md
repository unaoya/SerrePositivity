# 調整役の引き継ぎ（2026-11、整理の期間から段階 II へ）

作成：2026-11-05（前の調整役）。宛先：新しい調整役（Claude Code の新しいチャット）。**切り替えは片付けの後（11-05 夕のユーザー決定）：F-2 の取り込み・改名表の配置・片付け C1〜C3 と C8〜C10 は前の調整役が済ませる。新しい調整役は段階 II の計画の確定から始める。**

## 1. 最初に読むもの（この順）

1. 本書。
2. [段階 II の計画（下書き）](stage-ii-plan-draft.md)：目標 A（E3）・目標 B（K の 2 つ）、規則、レーンの構成の案と並列の検討（§5.1）。**ユーザーと相談して確定するのが最初の仕事**。
3. [片付けの一覧](archive/stage-i/cleanup-list-2026-11.md)：いまのレーンが今週中に行う片付け（C1〜C10）と、段階 II で出す後回しの片付け（L1〜L6）。
4. [coordination.md](coordination.md) §2（ビルドの規則。段階 II に引き継ぐのは計画の §4 の 7 項目）と §4（各レーンの現状）。
5. メモリ（`~/.claude/projects/.../memory/MEMORY.md` から）：特に `elaboration-drift-lessons`（判断表の由来）、`main-worktree-shared-index`、`lake-artifact-cache`、`verify-build-costs`、`bs-session-separate`。
6. 必要に応じて：∞ の計画 [infinity-foundation-plan.md](archive/stage-i/infinity-foundation-plan.md) 段 G（M1〜M16）、BS の [design-status.md](bhatt-scholze/design/design-status.md)・[foundation-entry-points.md](bhatt-scholze/design/foundation-entry-points.md)、K の [kst-lanes/k-theory-kst-route.md](archive/stage-i/kst-lanes/k-theory-kst-route.md)・[infinity-lanes/foundations.md](archive/stage-i/infinity-lanes/foundations.md)。整理の期間の指示書（`infinity-codex-*`・`dg-codex-*`）は**読まなくてよい**（結論は計画と一覧に移した）。

## 2. 引き継ぎの時点の状態（11-05 21:45、片付けの完了後）

- **主定理の閉包の sorry**：3 つ（E3、`theorem_3_1_K0`、`Section4.supportedRankK0_descent`）。
- **整理（段階 I）**：**完了**。DG・論文の層・∞ の W0〜W2c・段 F（F-1、F-2：d0845720b）と片付け C1〜C3（05c33bfc0）・C8〜C10 まで main に入った。改名表は `scripts/refactor/targets/f-namespace-map.json`（旧名は deprecated alias で残る）。README は段階 I の終わりの状態に更新済み（7e7fb944a）。
- **G2-finish（11-05 夜）**：段 1 と段 2 の途中を main に取り込んだ（6f35a986f。ルートのビルド・F2 の監査とも通過、sorry なし）。ここで区切り、②の完成（錐の族の同型）・①・四角形は ∞ 供給レーンの最初の仕事にする。残りの接続は `archive/stage-i/infinity-g2-progress.md` の末尾。
- **レーン**：整理の期間のレーンはすべて閉じた（∞ 整理・G2・DG・論文の層・BS 設計・BS 実装）。worktree は main だけ。枝は `main` だけ（`math/g2` は取り込み後に削除）。古い枝は `archive/*` のタグ。
- **main**：作業木はクリーン。最後の verify は F-2（gate:true）。その後の C1〜C3 は対象のビルドと F2・Derived の監査で確認。


### 2.1 新しい調整役が最初にすること（順に）

1. **段階 II の計画（`stage-ii-plan-draft.md`）をユーザーと確定する**。レーンの構成は §5.1 の並列の検討（7 本が上限、5 本から推奨）を叩き台にする。計画書の状態の表（`archive/stage-i/infinity-lanes/foundations.md` §2 は 10-19 のまま）も今の状態に直す。
2. 各レーンの開始文を書く。どれにも「F-2 の改名表の場所」「main を取り込んでから始める」「coordination.md §2 の規則」を入れる。∞ 供給は `archive/stage-i/infinity-codex-g2-finish.md` と `archive/stage-i/infinity-g2-progress.md` の末尾（G8 の四角形の残り）と `archive/stage-i/infinity-codex-g2.md` から、BS 設計は `bhatt-scholze/design/design-status.md` §0 から、BS 実装は BS-W11 から（旧 G8 ではなく `tensorSpaceFunctor_setWeightHomNatural` を使う）。
3. coordination.md §1・§3 にレーンと暦を書く。
4. 後回しの片付け（`archive/stage-i/cleanup-list-2026-11.md` §2 の L1〜L6）を段階 II の保守として暦に入れる。

### 2.2 段階 II の目標 A の出発点（BS の drafts）

BS の形式化の下書きが `formalization-plans/bhatt-scholze/drafts/` に 51 本・約 12,900 行（sorry 893）ある。ビルドされない設計段階の Lean で、**目標 A は、これを BS 実装（Codex）が本体の決まった置き場所へ新規ファイルとして移しながら sorry を証明に置き換え、sorry 0 のものから main に入れる作業**である（計画 §1.0）。新しい BS のチャットの開始文と、BS 実装の最初の指示書（BS-W11 以降）には、この進め方と `drafts/README.md`（置き場所と DAG）を明記する。∞ の供給（G8 の四角形など）が main に入るたびに BS に知らせる。

## 3. 調整役の仕事のやり方（整理の期間に固まったもの）

- **合図と取り込み**：全ビルド（下流・verify）の開始は調整役が合図する。取り込みは調整役が main で `git merge --no-ff`、衝突は main 側を正に、その後に温め（`lake build SerrePositivity` と、verify の監査対象の一覧のモジュール。監査が import するモジュールは直接ビルドしてから監査を流す）。
- **報告の受け方**：Codex は停止点ごとに報告する。判断が要るものは指示書の末尾に「追記 §n」として書き、短い文面をユーザー経由で渡す。条件付きの事前承認（「下流が通り、保存比較の未説明 0、処置が判断表の範囲なら verify まで進んでよい」）を使うと、夜間に止まらない。
- **確認のたびに見るもの**：`ps` の `lake build`・`verify.sh`（cwd で worktree を特定）、main の作業木がクリーンか、各 worktree の最新コミットと未コミットの数、**BS の main への直接コミット**（BS の決定や ∞ への依頼が書かれる。前の調整役は 11-04 に S3 の経路の決定を見落とした）。
- **よくある停止の型**：import の和による名前の隠蔽・宇宙メタ変数の捕捉・束縛子の型の捕捉・section 変数の脱落・private 参照・データの instance 経路の差。処置は判断表（メモリ `elaboration-drift-lessons`）。保存比較は v3b（証明を標識に置き換え、`_proof_N` を親に束ねる）。
- **別プロジェクト**：`arxiv_formalization` のビルドがときどき走り、CPU を取り合う。止めるかはユーザーに尋ねる。
