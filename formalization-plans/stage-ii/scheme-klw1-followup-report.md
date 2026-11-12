# ⑥ KL-W1 追従：検証済み本体だけでの再収集

2026-11-12。**追従は未完。採取器自身の Lean エラーで collect が止まったため、rewrite と main の取り込みには進んでいない。** 本体の検証は数学 `69ace8712` まで済んでいる。停止点 2e ではない。

## 0. 追従前の検証の区切り

数学 `69ace8712`、記録 `44651feab`。局所化と指定次数の Frobenius、半線形な Čech H の入口の三本をコミット済み。対象と直接 importer `SerrePositivity.AlgebraicGeometry` のビルドは成功（4,332 jobs）、別実行の標準監査は **7,204 宣言・標準三公理のみ**。共有鍵 `--wait 3600` を各実行の間だけ持った。

## 1. 今回の対象

午後の指示に従い、[対象一覧](scheme-klw1-followup-files.json) を **検証済み本体 68 本**に絞った。従前の 117 本から、`scheme-drafts/` の 48 本と未検証の `SerrePositivity/AlgebraicGeometry/ProjectiveCechFrobenius.lean` を除外した。下書きのソースは削除せず、作業木に残している。

68 本の全ソースについて、収集開始前と停止後の両方で `git show 69ace8712:<path>` とバイト単位で一致することを確認した。配布元は次である。

`/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout/formalization-plans/stage-ii/kerodon-layout-stop-3/scheme-files.json`

## 2. 新しい出力先での collect と停止原因

追従前 HEAD `ac81963eb` で、共有鍵 `with_build_lock.sh --wait 3600` と 1,700 秒の時間制限を通し、一回の collect を実行した。新しい出力先は `scheme-drafts/klw1-followup-1112/before_index_verified/`。旧来の未完成 index は再利用していない。

```sh
klw1=/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout
files="$PWD/formalization-plans/stage-ii/scheme-klw1-followup-files.json"
before_index="$PWD/formalization-plans/stage-ii/scheme-drafts/klw1-followup-1112/before_index_verified"
python3 "$klw1/scripts/refactor/klw1_namespace.py" collect \
  --root "$PWD" --files "$files" --output "$before_index"
```

**50 本の capture が成功**した。51 本目 `ReesClosedThickeningNaturality.lean` を採取しようとした時点で、外部の `klw1_collect_refs.lean` 自身のコンパイルが次の二箇所で失敗した。

```text
klw1_collect_refs.lean:101:22:
  failed to synthesize GetElem? (List String) Nat System.FilePath ...
  (args[3]?).mapM ModuleSetup.load
klw1_collect_refs.lean:116:24:
  loadDynlib : System.FilePath → IO Unit
  expected System.FilePath → Language.ProcessingT IO PUnit
  config.dynlibs.forM Lean.loadDynlib
```

収集実行中に、共有の Python と Lean 採取器が未コミットの更新を受けていた。停止時の Lean 採取器には新しい任意引数 `SETUP.json` の処理が加わっていた。これは対象の本体に出たエラーではない。外部の作業木の道具は変更していない。鍵は終了時に返却済み。

collect の終了コードは 2、内部 Lean は 1。成功 50 本の capture は実ソースと再照合済み。失敗した一本と後続 17 本は未収集。全体の `files.json` は生成されていないため、部分 index を完成扱いにしていない。

## 3. review・差分・取り込み・ビルドの状態

| 項目 | 状態 |
|---|---|
| 対象 | 検証済み本体 68 本。未検証 49 本は対象外として作業木に保存。 |
| 新しい collect | 50 本成功、採取器のエラーで停止。完全な index は未生成。 |
| rewrite | 未実行。 |
| `review.json` | 未生成。保留件数は未判定であり、0 とはしていない。 |
| 書き換えた Lean ソース | 0 本・0 行。 |
| main `19f081dcb` 以降の取り込み | 未実行。 |
| 追従後の対象・直接 importer のビルド | 未実行。追従前の結果は §0。 |

## 4. 証拠と次の手順

作業木の `formalization-plans/stage-ii/scheme-drafts/klw1-followup-1112/` に保存した。

- `verified-only-provenance.json`：68 本のソースハッシュと除外した 49 本。
- `collect-verified.log`：今回の実行ログと採取器のエラー。
- `before_index_verified/`：成功した実際の capture 50 本。
- `collect-verified-failure.json`：成功・失敗・未実行の一覧、終了コード、停止後の道具と改名表のハッシュ。収集中の道具更新があったため、これを全 capture 共通の道具版とは主張しない。

採取器の修正後、検証済みの同じ 68 本を新しい出力先へ一貫した道具版で収集する。その後、rewrite → `review.json` とソース差分の確認へ進む。保留が出れば書き換えずに報告する。保留がなければ main（`19f081dcb` 以降）を取り込み、プレビューを反映し、対象と直接 importer を共有鍵 `--wait 3600` でビルドする。未検証の下書きは、この取り込み後に検証するときに改名表で追従させる。

従前の 117 本による収集停止の報告は `ac81963eb` に残っている。今回の対象は午後の指示に従った 68 本であり、旧来の下書きエラーは今回の停止原因ではない。
