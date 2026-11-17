# ∞ の Codex：新しいチャットの再開文（IF-W2b の途中から、2026-11-03）

作成：2026-11-03（管理は Claude）。宛先：∞ の Codex の**新しいチャット**。前のチャットは IF-W2b の停止点 2 の報告を出した時点で閉じる（報告が出せないほど長い場合は、作業木と `.lake/verify/ifw2b-post-dgw3/` の記録から再開する）。

## 1. あなたの役割と場所

- ∞ 基盤の整備レーン（[infinity-foundation-plan.md](stage-i/infinity-foundation-plan.md)）の Codex。管理は Claude（暦・合図・取り込みは Claude が行う）。
- worktree：`../SerrePositivity-ifw0-3`、ブランチ `infra/if-w2b`（main の d135a715f を取り込み済み）。**main の作業木では作業もビルドもしない。**
- 共通の前提：[IF-W0-1 §0](infinity-codex-w0-1.md)、[coordination.md §2](../coordination.md)（ビルドの規則：全ビルドは暦と合図、小さなビルドは §2-4a、Lake キャッシュ、鍵 `with_build_lock.sh`）。

## 2. 最初に読むもの（この順）

1. [IF-W2b](infinity-codex-w2b.md) の全部（§1〜§15。§7〜§15 は途中の判断で、判断表・配置の規則・停止条件の最終形が入っている）。
2. [IF-W2a-2 §7〜§9](infinity-codex-w2a-2.md)（宇宙の明示、保存比較 v3b、`_proof_N` の束ね）、[DG-W3 §9・§11](dg-codex-w3.md)（束縛子の型の明示、局所 instance の束縛）。
3. 作業木の記録：`scripts/refactor/targets/w2b-*.json`（草案 r73／r37／r38、配置と補充の記録、監査計画、enforcement の基準）、`.lake/verify/ifw2b-post-dgw3/`（内部 round の群ログ、`resume-build.py`、after snapshot と比較の準備 `capture-after.py`・`compare.py`）。前のチャットの最後の報告（停止点 2 か、その直前の状態）。

## 3. いまの状態（11-03 13:20）

- R73・R37・R38 は適用済み（4d02ee532・d12e85d0e・9c38c984e）。§14 の配置修正 40 本（e1d2b7183）、補充（2b01641ef・9a1723f2c）、ratchet 基準の設定ハッシュ更新（11e7c8644）、`snapshot_batch.py` の v3b 対応（df6790351）。
- 内部ビルド：round 2 失敗 51 → round 3 失敗 12 → **round 4 実行中**（13:17 開始、失敗 0 の見込み）。
- 残り：round 4 の完走 → after snapshot v3b（補充先の追加取得を含む）→ 保存比較 → **停止点 2 の報告**（round の表、A/B/C の最終本数、配置修正・補充・修飾の件数と一覧、`layer_check.py --report` の前後、ratchet の 12 指標とその経路、W2c への入力 180 本）。
- **下流ビルド（13,149 本）と verify は Claude の合図（11-04）を待つ。** 合図の前にもう一度 main を merge してから下流に入る（§13-3）。

## 4. 規則の要点（新しいチャットでも同じ）

- 判断表（止めずに当ててよい処置、各々 v3b で一致を証明、別コミット）：補充の import（置き先と同じ層以下・Foundation・Mathlib だけ）／完全修飾／宇宙の明示／名前付き引数の明示／束縛子の型の明示／局所 instance の束縛・heartbeat の引き上げ（section 内または `in`）。
- 配置の規則：置き先は、宣言が使う定数の定義元モジュール全部の層の最大値以上で最も低い層（§14-3）。上の層が要るなら置き先を上げる。Core・Kan には閉包が許可集合の外へ出るものを置かない。
- 止める条件（§5 の最終形）：禁止領域（KST・DG・EInfinity・モデル圏の HA・Derived・ModelBridge）が要る補充／宣言の本文・型・名前を変えないと直らない／保存比較 v3b で未説明の不一致（データの差）／補充だけの round で失敗モジュール数が減らない／`layers.json` に例外を足さないと通らない。
- `--enforce W2b` の合否は 3 条件（§12-2）：中核の層どうしの順序の直接違反 0、直接の禁止辺が既存の 21 本から増えない、全体の禁止モジュール数と affected core が増えない。root ごとの指標は診断扱い。
- 報告は短く、停止点ごとに 1 回。経過の記録は `scripts/refactor/targets/w2b-*.md/json` に残し、コミットは `git commit --only`。

## 5. その後の予定（参考）

停止点 2 → 11-04 に下流と verify → 停止点 3 → Claude が取り込み → W2c（段 E）の指示書 → 段 F。BS 発の一般論 G3・G4・G6（M12b・M12c）の依頼は W2b の取り込み後に別の指示書で来る。
