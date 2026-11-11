# HA照合の保存済み証拠の監査

`audit.py`はLean・lake・ビルド鍵を起動しない。Python標準ライブラリとgitだけで保存済みの照合表・証拠を確認する。

## 再実行

対象worktreeで実行する。

```sh
python3 research/ha-coverage/review/check/audit.py --root "$PWD"
```

記録当時のソース内容も確かめる場合、対応するgitオブジェクトを持つMathlib checkoutを渡す。

```sh
python3 research/ha-coverage/review/check/audit.py \
  --root "$PWD" \
  --mathlib /path/to/pinned/mathlib \
  --pdf /path/to/HA-2017-09-18.pdf
```

`--mathlib`と`--pdf`は独立した任意引数。ソース版まで検査した最終結果を`audit-result.json`に保存した。`--mathlib`なしではソースハッシュの実値の検証を省き、`verified_source_hash_records`は0になる。`--pdf`なしでも各証拠のPDFハッシュが段0の採用版と一致することは確認する。Leanの再実行は別の作業であり、この監査の成功は再ビルドの成功を意味しない。

## 検査すること

- 全10表の番号が目録2,866件と一対一対応し、重複・欠番・unsureがない。
- status・check・partial_kind・理由と宣言名の対応。
- 各肯定/partial行に、表と同じ順序の宣言の型・行番号・標準公理だけの証拠がある。
- 各none行に、同じ理由、両ソースの検索、引用と隣節の確認、実読ソースのハッシュがある。
- 引用番号が目録または節に存在し、目録のlean_citations/plan_citationsが採取済みCSVの件数と一致する。
- 第1章の分割証拠の目次と実際の件数が一致し、各JSONが2 MB未満。
- `--mathlib`あり：記録したgitコミットの全ソースハッシュが一致する。段4の証拠は現在のworktree/Mathlibのソースとも一致する。
- `--pdf`あり：渡されたPDFのSHA-256が2017-09-18採用版に一致する。

本文と宣言の数学的対応やnoneの探索の十分性は、各行の理由・保存した型・実読ソースを人が検討する。監査スクリプトは数学的な対応そのものを判定しない。

## 証拠の形式

- `ch<N>-kernel-evidence.json`：項目ごとの宣言名・原典ページ、宣言ごとの`#check @...`の型、`#print axioms`の公理、元ソースのpath/line/SHA-256、LeanとMathlibとworktreeの版。
- 第1章は2 MB上限に合わせて`ch1-1.<section>-kernel-evidence.json`に分割し、`ch1-kernel-evidence.json`から参照する。段4で差し替えた1.2.3.21の証拠は`ch1-stage4-kernel-evidence.json`に分離した。
- `ch<N>-none-search.json`：原典ページ、exact/同節/隣節の引用数、両ソースの検索パターン・一致件数・候補パス、実読ソースのハッシュ、項目固有の不足理由。
- 第1章の旧none89件は記録時のgitオブジェクトから241のパス参照にハッシュを補完した。`source_hash_completion`に方法を記した。段4で旧partialから変更した35件は`ch1-stage4-none-search.json`へ分離し、元の証拠の版を混在させない。
- 複数段の証拠はそれぞれのworktree_commitを維持する。全表を最新mainのソースで検証し直したという記録ではない。

## 型検査時の条件

各候補の実ソースを読み、完全修飾名と型を比べた上で、対応モジュールを読み込んだLeanに`#check @<declaration>`と`#print axioms <declaration>`を渡した。kernelエラー・終了コードの異常・型または公理出力の欠落は失敗として扱った。結果はコンパクトなJSONに保存し、生の出力とscratchの生成物はコミットしない。

段4では共有の整理券を同時に1枚だけ発行し、`with_build_lock.sh --wait 3600`を通した。鍵の保持時間は各回580秒に制限した。待ち時間切れの場合は前の整理券が終了してから再登録した。
