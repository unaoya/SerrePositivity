# IF-F F-2 — 停止点 4

**PASS**。検証コミットは `10437c5de`（`infra/if-f`）、適用前の基点は main `640288f33`。IF-F §5〜§9（最新の承認 `ab6b296b4`）に従った。報告のコミットは記録のみ。main 作業木での変更・ビルド、他レーンの枝の変更はない。

## 適用と確定改名表

KST 由来の 730 モジュール、ソース宣言 3,871 個（明示名 3,849、匿名 instance 22）を現在のディレクトリに対応する名前空間へ付け替えた。由来は W2c 415 モジュールと、先行 W1/W2a 315 モジュール。InfinityCategories 全体の付け直しではない。F1・F1B・F2 のディレクトリ名は維持し、README の役割表を更新した。

[確定改名表](f-namespace-map.json) は旧名・新名・生成宣言・alias の種類・利用者を含む。環境レコード 8,684 件のうち、deprecated alias は 7,526 件、private は 1,157 件、重複のため alias を作らないものは 1 件。ソース宣言と生成宣言の数は別に数えている。

| alias の種類 | 数 |
| --- | ---: |
| theorem | 4,932 |
| abbrev | 2,225 |
| constructor（match_pattern） | 106 |
| instance 登録なし | 182 |
| recursor（elab_as_elim） | 81 |
| 合計 | 7,526 |

旧名の重複 `KST.Comparison.doubleMappingCylinder_hom_ext` は利用者が多い `Kan.DoubleMappingCylinderDesc` に alias を置いた。`Kan.DoubleMappingCylinderMap` は alias なしとし、その利用者と監査を新名へ追従した。alias は段 G の最初の区切りまで保持し、一括削除は別の束とする。

## 旧名の一掃と利用者側の件数

§9 の LoopOfCylinder の 2 参照を含め、型・本体・戦術・監査の旧名を改名表に従って新名へ置き換えた。旧名の完全修飾参照は全ソースの静的走査で 0。下流 10,520 本（補助モジュール 1 本を含む）の `.ilean` に残る旧 alias 参照も 0、欠けた `.ilean` も 0。監査の短名は下記の追加追従と正式 verify の警告で確認した。import の実モジュール名、移動対象外の namespace、alias 宣言そのものを宣言の使用と取り違えていない。

基点 `640288f33` との差分。行数は git の追加／削除行であり、意味を変えた宣言数や一意な参照数ではない。

| 区分 | ファイル数 | 追加行 | 削除行 |
| --- | ---: | ---: | ---: |
| 改名対象の定義元 | 730 | 42,163 | 13,457 |
| ∞ 内の利用者 | 466 | 1,460 | 1,460 |
| KST 内の利用者 | 2,837 | 17,962 | 17,962 |
| Archive（静的な追従のみ） | 4 | 62 | 62 |
| 監査 | 5 | 1,928 | 1,928 |
| 互換 alias 補助モジュール | 1 | 105 | 0 |

通常の利用者側の変更は合計 3,303 ファイル・19,422 行。Archive の 4 本は 79 参照を静的に追従し、ビルド・snapshot の対象外とした。BS・DG・HA のソースを直接変更していない。別の BS・KST・G2 ブランチは触っていない。対応する全ファイル一覧は改名表と [検証前記録](f-section9-preverify.json) にある。

## 検証結果

| 検査 | 結果 |
| --- | --- |
| 親 namespace 補充候補 21 本の小さなビルド | PASS、62.802 秒 |
| 内部 round 9 | PASS、6.822 秒 |
| 下流 10,519 本＋補助 1 本、23 根 | PASS、6,129.204 秒 |
| private 込み v3b、4,034 モジュール・345 バッチ | PASS |
| alias の型・本体・公理・属性等 | 7,526 件 PASS、失敗 0 |
| 保存比較 | 生差分 21、個別説明 21、未説明 0 |
| 層検査 3 条件 | PASS、直接禁止辺 0 |
| ratchet（merge 済み before との比較） | 増加 0 |
| 正式 verify | PASS、監査 102 本、対象 5155 本、37.2 分 |

`VERIFY_JOBS=6 VERIFY_MEMORY_GB=40`、共有鍵の下で正式 verify を実行。初回 `5c72d9a56` は全監査をキャッシュなしで実行し、40.0 分で PASS。終了後の警告集計で SConstruction 監査の短い旧名 2 個（#check/#print axioms 計 4 行）が残っていたため、`10437c5de` で新名に完全修飾した。検査数と対象集合は保持。102 監査の 81,936 コマンドを namespace の文脈付きで補助走査しても該当 0。

中間の再検証では内容ハッシュが一致する成功監査 101 本を既存キャッシュから再利用し、変更した SConstruction 監査と sorry 閉包を新たに実行して、旧名警告 0 を確認した。ただし既存 runner がキャッシュ利用時を `non-gate` と判定するため、最終 HEAD で全 102 監査をキャッシュなしで再実行し、正式な `gate=true` を確認した。選択実行・ビルド省略はしていない。本番ソースは初回 PASS から変更していない。初回の summary・全ログ・警告 2 件は `.lake/verify/if-f2/verify-first/`、中間再検証は `verify-cached-followup/` に保存した。

```
PASS build(success=2,failure=0,known=0) audit(success=102,failure=0,known=0) sorry(success=1,failure=0,known=0) preparation(success=1,failure=0,known=0) retried=0
```

summary は [f-stop4-verify-summary.json](f-stop4-verify-summary.json)、実行記録は [f-stop4.json](f-stop4.json)。全ログは `.lake/verify/if-f2/verify/` と各 summary の stage log に記録。

## 保存比較の個別説明

一般の v3b 比較器・ハッシュ計算は変更していない。生差分 21 件と元の snapshot を保存し、IF-W2b §17-3 の個別説明として [f-section9-preservation.json](f-section9-preservation.json) に次を記録した。

1. **private の局所 notation parser 18 件の body**：名前空間変更に伴い `ParserDescr.node` 内の自分自身の構文ノード名が変わる。before と after の実環境で各値を取り出し、その名前が当該 private 宣言自身であること、承認された旧名→新名の対応であることを検査。型・宇宙・node の head・優先順位・parser 本体の各式が一致することを照合した。行や hash を除外して差分を隠してはいない。
2. **axioms 1 件と auxiliaries 2 件**：Lean の既存公理収集キャッシュは inductive と constructor の循環で途中の集合を保存し、探索順によって `propext` が欠ける。この差分に現れた 4 宣言は型・本体の hash が一致し、before/after の実環境で依存グラフを完全探索すると公理集合も一致、参照不明 0。auxiliary の他のフィールドと宣言集合も一致する。

alias 検査にも同じキャッシュの影響で最初の 6 件に差が出た。従来の比較で不一致の場合だけ型・本体・constructor を含む依存グラフを完全探索し、不明参照や公理集合の差を拒否する検査を加えた。6 件すべてで alias と新名の完全な公理集合が一致。循環と追加公理を含む独立回帰試験、既存の型展開 59 件、誤った改名表を拒否する負例も PASS。元の失敗ログは保存している。

互換 alias の生成では再帰補助 `_unsafe_rec` のコード生成が二重登録される問題を修正した。対応する親 alias の登録と既存 LCNF を確認した場合だけ二重生成を避け、計算可能性を保持した。実行結果・IR 名の一意性・旧 helper での失敗を回帰試験で確認。型照合の alias 展開は、実際の kernel 本体が改名表どおりの新名定数である alias に限定した。

## 層と監査

W1 の禁止モジュール／affected core は 0。W2a/W2b の禁止モジュールは 74（HA 66、ModelBridge 8）、affected core は 1,733。段 G の既存 M16 残件を保持し、例外や上限を増やしていない。直接禁止辺は 0。

古い F-1 基準 `392ddcc88` からは `F2.Tensor.SetSectionsNaturality` の W2a/W2b 指標 2 件が 0→74 となるが、main `f2b665682` で導入され、F-2 適用前 `640288f33` でも既に 74。F-2 でこのファイルは変更していない。merge 済み before からの増加は 0。[f-layer-baseline.json](f-layer-baseline.json) を実測値へ取り直した。

監査の実コマンドをコメント除去後に数えた。対象集合も前後一致。`audit_localizing_invariants` は動的検査を保持している。

| 監査 | #check 前→後 | #print axioms 前→後 | project 対象 前→後 |
| --- | ---: | ---: | ---: |
| infinity_f1 | 9,100→9,100 | 182→182 | 466→466 |
| infinity_stable | 391→391 | 2,360→2,360 | 2,169→2,169 |
| kst_cofinality | 90→90 | 1→1 | 1→1 |
| kst_comparison | 1,499→1,499 | 1,499→1,499 | 1→1 |
| kst_s_construction | 14,395→14,395 | 14,395→14,395 | 3→3 |
| localizing_invariants | 0→0 | 0→0 | 2→2 |

## 残る deprecated 警告

今回移した旧名による deprecated 警告は **0**。既存の Lean/Mathlib 等による警告は残るため、全 deprecated 警告が 0 とは報告しない。

| ステージ | 生の警告行 | 一意な警告 | 今回の旧 alias |
| --- | ---: | ---: | ---: |
| 内部 round 9 | 41 | 41 | 0 |
| 下流 | 52 | 52 | 0 |
| 正式 verify | 104 | 52 | 0 |

名前別・ログ別の実数は [f-section9-deprecations.json](f-section9-deprecations.json)。下流の内訳：`if_pos` 18、`if_neg` 16、`Set.mem_setOf_eq` 5、`TensorProduct.induction_on` 1、`dif_pos` 4、`Fin.coe_castSucc` 1、`Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts` 1、`push_neg` 1、`dif_neg` 5。

警告行と Hint 行を分け、Lake の replay を含む生の行数と一意な警告を別々に記録した。ステージ間の重複を単純合算しない。今回の改名表にない既存ライブラリ名の置き換えは IF-F §4 の R78 禁止の対象なので行っていない。

## 引き継ぎ

確定改名表を後続レーンの新名への移行に使う。deprecated alias の削除と段 G の M16 は別の束。`infra/if-f` と worktree `SerrePositivity-ifw0-3` を保持し、取り込みは Claude に引き継ぐ。以前からの W2b 未追跡 5 ファイルは変更していない。
