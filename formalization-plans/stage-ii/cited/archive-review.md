# 指示書 AR-W1：Archive の数学的な内容の確認（紙）

作成：2026-11-17（調整役）。決定：ユーザー（11-17「数学的な内容をきちんと確認して残すべきかどうかを検討したい」）。レーン：⑧（worktree `../SerrePositivity-cited`、枝 `research/cited-coverage`。`pwd` を確かめてから始める）。

## 0. 目的

`SerrePositivity/Archive/`（1,871 本・約 11 万行、ビルドしない）を消すか残すかを、**数学の中身**で判断できるようにする。行数や参照の有無だけでは決めない。各部分について、何の数学が入っているか、文献のどの項目か、今の本体に同じもの・より良いものがあるか、これからの目標（P⁰ の項目の閉包、BS、K）に要るか、を紙にする。判断は調整役とユーザーがこの紙で行う（このレーンは推奨を書くだけ）。

## 1. 対象

| 部分 | 規模 | 経緯 |
| --- | --- | --- |
| `Archive/InfinityCategories/FilteredExchange/` | 1,726 本・約 9.5 万行 | 11-02 の 4d02ee532「archive old exchange path and place retained foundations」で退避。主題は CoherentColimit 359・CoherentCospan 108・FunctorTriangle 56・RelativeExtension 49・FunctorIso 41・SpaceComposition 39 など |
| `Archive/InfinityCategories/DGKappaDiagnostics/` | 4 本 | 診断。`scripts/refactor/check_cleanup_c2.lean` が import |
| `Archive/KST/DescentConditional/` | 67 本・約 7,000 行 | 条件付きの降下（Augmented Čech 系）。`scripts/archive/audit_kst_descent_conditional.lean` が import |
| `Archive/DifferentialGraded/` | 68 本・約 5,700 行 | 中断した dg の一般論 U12e-general（DG-W1）。`DifferentialGraded.lean` の docstring が言及 |
| `Archive/WIP/` | 6 本 | 止まったレーンの未追跡ファイル（10-31 ユーザー決定で保存、由来は `WIP/README.md`） |

## 2. 紙の形

`research/archive-review/` に置く。
- `groups.csv`：**主題の群**ごとに一行（ファイル名の接頭辞・名前空間・相互の import で群を作る。FilteredExchange は 30〜80 群が目安）。列：`group`、`files`、`lines`、`main_declarations`（群の主な定理・定義を 3〜10 個、名前）、`statement_ja`（それらの主張を日本語で。docstring とソースから。数学として何を言っているか）、`literature`（Kerodon・HTT・HA などの番号。docstring の引用と対応表の照合から。推測の番号は書かない、無ければ空）、`live_counterpart`（今の本体にある同じ主張・より一般の主張の宣言 `名前 @ パス:行`、型の差を一言。無ければ空）、`targets`（P⁰ の項目の閉包 `research/p0-lurie/item-closure/items.csv`・BS・K のどれに要るか、根拠の項目番号）、`sorry`（群の中の sorry の数）、`imports_live`（群が import する本体のモジュールが今もその名前であるか：全部ある／改名済みで追従が要る／消えたもの、の件数）、`recommendation`、`reason`。
- `recommendation` は四つから：**戻す**（本体に足りない数学で、目標に要る。戻すときの置き場所の案も）、**材料として残す**（今は要らないが、文献の項目の証明として再利用の見込みがある。どの項目か）、**消してよい**（本体に同じかより良いものがある、または旧経路だけの補助で数学的な価値が残らない）、**判断できない**（理由）。
- `kerodon-rows.md`：Archive の宣言を指している対応表の行（`research/kerodon-coverage/review/ch9.csv` の 9.1.1.18・9.1.1.20・9.1.5.7、`ch4.csv` の 4.3.6.12、ほか見つかったもの）について、その宣言の数学が原典の項目と一致するか、今の本体に代わりがあるか、表の状態をどうすべきか（ビルドしない場所の宣言は own にできない。対応表は書き換えず、案だけ）。
- `README.md`：集計（推奨ごとの群・本数・行数）、判断の要点、調べ方、限界（ソースを読むだけで、コンパイル・kernel の確認はしていない）。

## 3. 規則

- 紙だけ。Lean の変更・ビルド・`lake env lean` はしない。Archive・本体・対応表は書き換えない。
- 主張は docstring の言い換えで済ませず、型（宣言の仮定と結論）を読んで書く。docstring と型が食い違うものは `reason` に書く。
- 「本体に同じものがある」は、名前の一致ではなく**主張の一致**で判断する（型を並べて比べる）。
- FilteredExchange は大きいので、まず群分けと各群の主な宣言の一覧をコミットして**途中報告**（停止しない）、その後に主張・対応・推奨を埋める。
- 証拠（大きい抽出結果）は git の外 `~/serre-evidence/cited/archive-review/`、目録だけをコミット。
- 報告は `report-clmst-coverage.md` に節「AR-W1」を続け、先頭の現在地を更新。全部をコミットしたら止まる。
