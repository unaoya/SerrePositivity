# 片付けの一覧（整理の完了から段階 II の開始まで）

作成：2026-11-05（調整役）。状態：**§1 は完了（11-05 21:45）**。§2（後回しの片付け L1〜L6）は段階 II の保守として残る。
方針（11-05、ユーザー）：片付けはいまのレーンにさせ、新しい課題は新しいレーンで始める。片付けが済んだレーンからチャットを閉じ、worktree と枝を消す。
前提：段 F の F-2（名前空間の付け替え）が main に入った時点で整理（段階 I）は完了とする。

## 1. すぐできる片付け（今週中、いまのレーンで）

| # | レーン | 内容 | 規模 | 終わりの条件 |
| --- | --- | --- | --- | --- |
| C1| C1 | ∞ 整理（段 F） | **完了（05c33bfc0）**。F-2 の取り込み後の後始末：停止点 4 の指摘の処理、改名表の確定版を `scripts/refactor/targets/` に置く、`InfinityCategories/README.md` の層ごとの中身の表（F1・F1B・F2 は改名しない代わり、IF-F §5） | 小 | README の表が main に入る |
| C2| C2 | ∞ 整理 | **完了（05c33bfc0、診断モジュール 4 本を移動）**。台帳 R60 の小さな処置：診断・archive の候補のうち、利用者 0 で移動だけで済むもの（ビルドは小さい範囲に限る）。大きな処置（未被覆の監査登録候補 145 本、HA/Simplicial の孤立入口 121 本など）は記録のまま段階 II の保守へ | 小〜中 | 台帳の処置済みの行に印 |
| C3| C3 | ∞ 整理 | **完了（05c33bfc0、旧 G8 の 5 宣言を deprecated）**。既存の G8（`tensorSpaceFunctor_setWeightHom` 系）に deprecated を付け、G2 の別版 `tensorSpaceFunctor_setWeightHomNatural` を正本とする（BS が別版へ移った後。BS の確認を取ってから） | 小 | deprecated が付く |
| C4 | ∞ 数学（G2） | **区切りまで完了（11-05、6f35a986f）**：IF-G2-finish の段 1（比較の補助 3 本）と段 2 の途中（評価三角形の Ho 等式）を main に取り込んだ。②の完成・①・四角形は段階 II の ∞ 供給レーンへ。枝 `math/g2` と worktree は削除。G8 の四角形（篩包含の場合）と G14 を仕上げる（BS の S4 が待つ。文脈を持つ G2 が仕上げる方が速い） | 中 | main に入り、BS が S4 の生成辺を閉じる |
| C5 | ∞ 数学（G2） | **完了（11-05）**：`archive/stage-i/infinity-g2-progress.md` は main にあり、末尾の節に残りの接続が書いてある。`archive/stage-i/infinity-g2-progress.md` に、IF-G2 の残り（G9 の小補題 3 つ、G8 の一般の φ、G10、G8 の一般形、G12 とその前提 2 つ）の引き継ぎを書く（新しいレーンへ渡すため） | 小 | 引き継ぎの節がある |
| C6 | DG | **完了（11-05、worktree・枝とも削除、レーンを閉じた）**。worktree `SerrePositivity-dgw1` と枝 `infra/dg-w3` の削除（main に入っている）。D6〜D8 の調査結果（`targets/dg-survey-d6d7-2026-11-01.md`）は残す | 小 | worktree なし |
| C7 | 論文の層 | **完了（11-05、8310a7fa7。レーンを閉じた）**。worktree `SerrePositivity-refactor-2b` の削除。段階 3 の残り 3 項目（テンソル冪、Asymptotic の商、PC の K₀）を、段階 II の計画の保守・K 理論の節へ移す | 小 | worktree なし |
| C8 | 調整役 | **完了（11-05）**：main に入った枝 16 本を削除、入っていない古い枝 6 本は `archive/<枝名>` のタグにして削除、残る枝は main・`math/g2`（WIP）・`codex/if-cleanup-c1-c3`（∞ 整理が使用中）。`/private/tmp/SerrePositivity-if-f2-baseline`（∞ の F-2 の比較用）は ∞ 整理が閉じるときに消す。Lake キャッシュ 29 GB、空き 321 GB。終わった枝の整理（main に入った `refactor/*`・`infra/*`・`math/g1`・`codex/bs-w10-b` などを消すか残すかの一覧）、`/private/tmp` に worktree がないことの確認、Lake キャッシュの状態（`~/.cache/lake` の大きさと空き） | 小 | 一覧を本書に追記 |
| C9 | 調整役 | **完了（11-05、2a66260bb）**：整理の期間の指示書 12 本と段階 I の coordination.md を archive へ、新しい coordination.md は規則（§2）と各レーンの現状だけ。リンクは修復（以前からのリンク切れ 55 件は `kst-lanes/` などにあり、段階 II の保守へ）。文書の整理：整理用の指示書（`infinity-codex-w*`・`infinity-codex-f`・`dg-codex-w*`・`infinity-codex-g1/g2`）、`refactor-plan.md`・`archive/stage-i/dg-cleanup-plan.md` の「状態」節を最終にし、`formalization-plans/archive/` へ移すものを決める。`coordination.md` を段階 II 用に書き直す（規則だけ残す） | 中 | 段階 II の計画が正本になる |
| C10 | 調整役 | **完了（11-05）**：重複していた記憶（main の作業木の 3 件、調整のやり方の 3 件）をそれぞれ一つに統合、段階 I の目標の記憶に完了を記入、方向の記憶に段階 II の正本を記入。メモリの整理：整理の期間の記憶（三レーンの調整、各窓の教訓）を、段階 II で効くものだけ残して統合 | 小 | MEMORY.md が短くなる |

## 2. 後でしかできない片付け（段階 II の中で一つの束として出す）

| # | 内容 | 時期 | 担当（予定） |
| --- | --- | --- | --- |
| L1 | deprecated alias（F-2 の旧名）の一括削除 | 段 G の最初の区切り（BS・G2 の後継レーン・KST が新しい名前へ移った後。目安 1 か月） | ∞ 中核レーン |
| L2 | 既存 G8 の旧版の削除 | L1 と同じ束 | ∞ 中核レーン |
| L3 | M16：中核の閉包に残るモデル圏の HA 66・ModelBridge 8（`CosliceTwistedHomEquivalence` の Reedy 依存） | 段階 II の ∞ 中核 | ∞ 中核レーン |
| L4 | W2c で Stable に置けなかった分数の一般版への統合（R57、`w2c-stage-g-input.json`） | M1〜M11 の Verdier 商と一緒に | ∞ 中核レーン |
| L5 | 台帳 R60 の大きな処置（未被覆 145 本、孤立入口 121 本）、R78（CategoryTheory の Mathlib との重複） | 余裕のあるとき | 保守（その都度） |
| L6 | DG の D6〜D8、Asymptotic の商の一本化 | 該当部分を数学で触るとき | その時の担当 |

## 3. 閉じる順（見込み）

1. DG・論文の層：C6・C7 が済めば閉じる（今日〜明日）。
2. ∞ 整理：F-2 の停止点 4 → C1〜C3 → 閉じる（明日〜明後日）。
3. G2：C4・C5 → 閉じる（2〜3 日）。**新しい調整役のもとで行う（11-05 ユーザー決定）**。新しい ∞ 供給レーンへ引き継ぐ。
4. BS（Claude Code・Codex）：片付けはなし。段階 II の BS レーンとしてそのまま続けるか、新しいチャットにするかはユーザーが決める（計画の下書き §5）。
