# B2 準備の付表（検証継続中）

この段階で確定した対応の付与計画と、場所の照合を保存する。移動後の全対象ビルド・全保存比較は継続中であり、B2 の停止点ではない。

- `location-refresh-ledger-187.json`：main fd50804df の元の187行を順序・元の六項目ごと保持。29行の宣言と場所を元環境の Lean で解決、82行は Kerodon partial の見直し待ち、76行は重複する旧K表・E3入力・対象外などの理由で記録のみ。
- `location-refresh-crosscheck.json`：元の台帳と当初の再構成候補の照合。延べ187件と異なる組187候補を混同しない。
- `attribute-rows.jsonl.gz`：正本26 CSVの全9,048行。none・Mathlib・既存ネイティブ属性の維持も含む。
- `attribute-declarations.jsonl.gz`：2,387参照の付与・除外・保留。1,860件の本体候補について元の import 環境のコンパイル済み宣言を Lake 設定とともに確認した。1,835件を付与、537件を除外（外部・対象外527、明示 ModelCategory SSet 仮定10）、15件を保留する案。私有1、出典の曖昧さ1、番号の束12、Stacks partial方針1が保留。Kerodon partial831行は別途見直しまで新しい Tag を付けない。
- `attribute-name-corrections.json`：BS表の8件の記述を、元の行番号を含むコンパイラ宣言範囲と Lean の型・所有元で確認し、実在する完全名に正規化した記録。

圧縮した全件表は Python 標準ライブラリだけで読める：

```python
import gzip, json
with gzip.open("attribute-declarations.jsonl.gz", "rt") as source:
    rows = [json.loads(line) for line in source]
```

本文の続きは `../report-bulk-w1.md`。独自属性の版は `research/bibliography.json` が正本。属性は数学的対応の新しい証明ではなく、既存レビューの結論を記録する。
