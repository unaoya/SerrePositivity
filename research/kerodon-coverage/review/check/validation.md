# 段1スクリプトの検証記録（2026-11-07 JST）

作業枝 `research/kerodon-review-a`、分岐元 main `cd1339097`。
このコミットは段1の検査基盤の受け渡し。全件の Lean 検査完了や数学的対応の承認を意味しない。

## 全件の収録

`runs/stage1-validated/` は `items.csv` 全体から作った計画と実行途中の記録。
元表との比較で、番号の順序・全記載の出現回数・記載 ID・ジョブへの分配を確認した。

| 対象 | 件数 |
| --- | ---: |
| 項目 | 3,553 |
| 宣言欄が空でない項目 | 1,672 |
| 宣言欄の記載（出現回数） | 2,880 |
| 重複を除いた記載 | 2,108 |
| 実行可能な形式の記載 | 1,997 |
| 手動で名前・出典を解決する記載 | 111 |
| 実行対象モジュール | 1,144 |

`none` の1,947項目中66項目にも宣言の記載があるため、status による足切りはしていない。
略記、匿名 instance の説明、`IC/…` などの略したパスは unresolved に残す。
これらの status が誤りかどうかは段2・段3で判断する。

## スクリプトと実出力の検証

Python の回帰テスト13件が成功。
型と公理を取り違えないこと、標準3公理、`sorryAx` と追加公理、宇宙引数、
名前不明、型推論失敗、import 失敗、不正・欠落出力、記載の解析を検査した。
`sorryAx` と追加公理の検査には合成した出力を使った。新しい Lean の数学宣言は追加していない。

`fixtures/real-lean/` は改修中の試走から保存した、以下の3モジュールの生の Lean 出力。
元の実行情報は `provenance.json` と各 `execution.json` に残した。
当時の runner の hash は最終版とは異なる。Lean の入力は末尾の空行だけを除去し、
コマンドの行番号・Lean の生出力・終了コードは変更していない。
ps の保存内容は、最終版と同じくビルドに関係する行だけに絞った。

- `Mathlib.AlgebraicTopology.SimplexCategory.Defs`
- `Mathlib.AlgebraicTopology.SimplicialObject.Basic`
- `Mathlib.AlgebraicTopology.SimplicialSet.Basic`

現在の解析器で、この実出力18記載を `found` 8件、`not_found` 10件に区別できる。
found の8件の公理に標準3公理以外はなかった。未知名の例は名前空間のない
`SimplicialObject`、`CosimplicialObject` と、`SSet.coskAdj.reflective` など。
not_found は「記載された名前がその import では解決しない」という意味に限り、数学的な不存在ではない。

修正した公理解析を含む実行 `runs/stage1-validated/` では SimplicialObject.Basic の準備と検査に成功。
次のモジュールの前に、別プロジェクトの `lake build ArxivFormalization` を検出して
§3どおり停止した。集計は found 2、not_found 8、build_busy 7、not_run 1,980、unresolved 111。
検査したものだけの数字と、全件計画の未実行分を区別している。
この実行の後、CSV の改行を LF にし、生成 Lean の末尾空行を除く保存形式の修正を加えた。

## 後続の実行

README の手順で新しい run-dir を prepare する。今回のコミットで HEAD が変わるため、
保存済み計画をそのまま resume すると provenance の不一致として拒否される。
ほかの大きなビルドが動いていない時に、章別の計画を作成し、対象モジュールだけを準備する。
段2・段3の `review/ch<N>.csv` はまだ作成していない。
