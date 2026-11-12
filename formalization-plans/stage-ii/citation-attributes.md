# 文献の属性 `@[cite …]` と略号（設計と一括レーンの計画）

作成：2026-11-11（段階 II の調整役）。決定：ユーザー（11-11、「属性まで、上の例で、KL-W1 の後の一括で ok」）。

## 1. 目的

宣言と文献の番号の対応を、docstring の地の文だけでなく、Lean の環境から引けるようにする。文献ごとの地図（HTT・HA・Prisms・Kerodon・K）は、手で書いた「名前 @ パス:行」をやめて、属性から作る。docstring にも、今までどおり番号を文章で書く（属性は機械のため、文章は人のため）。

## 2. 属性

- Kerodon と Stacks は Mathlib の `@[kerodon TAG]`・`@[stacks TAG]` を使う（Mathlib `Tactic/StacksAttribute`）。
- それ以外の文献は、同じ作りの `@[cite KEY "番号"]` を本体に置く。例：`@[cite HTT "5.5.2.9"]`、`@[cite BS19 "Prop 7.10"]`。照会のコマンド（`#cite_tags KEY` のように、番号・宣言・モジュール・行を出すもの）も置く。Mathlib の作りを手本にする。
- partial の対応には種類を付けられるようにする（`special`・`direction`・`stronger-hyp`・`component`、Kerodon の確認 §8.1 の基準）。書き方は実装のときに決める。

## 3. 略号と版

| 略号 | 文献 | 版 |
| --- | --- | --- |
| BS19 | Bhatt–Scholze, Prisms and prismatic cohomology | 著者版（`paper/refs/BS-prisms-author.pdf`） |
| BS17 | Bhatt–Scholze, Projectivity of the Witt vector affine Grassmannian | arXiv:1507.06490 |
| HTT | Lurie, Higher Topos Theory | 2017-04-09 版 |
| HA | Lurie, Higher Algebra | 2017-09-18 版 |
| Kerodon | Lurie, Kerodon | Tag（Mathlib の属性） |
| Stacks | The Stacks project | Tag（Mathlib の属性） |
| LT | Land–Tamme | 引用している版を README に書く |
| KST | Kerz–Strunk–Tamme | 同上 |
| BGT | Blumberg–Gepner–Tabuada | 同上 |
| TT | Thomason–Trobaugh | 同上 |
| BST13 | Bhatt–Schnell–Scholze | arXiv:1307.3763 |
| Rydh | Rydh, Submersions and effective descent | arXiv:0710.2488 |

一覧は README の「Conventions」にも置き、文献が増えたら足す。

## 4. 時期と一括レーン

1. KL-W1 の停止点 3 の取り込み → 対応表の宣言の場所の書き直し（coordination.md の暦）。
2. その後に一括レーンを開く。属性と照会のコマンドの実装、README の略号表、既存の対応表（HTT 896 件、HA 645 件、Prisms 287 件、K の地図）の own・partial から属性を自動で付ける。多くのファイルを書き換えるので、夜の bulk として流す。
3. 付け終わったら、地図を属性から作り直す。
4. 以後、すべての指示書の規則に「新しい宣言には文献の属性を付ける」を足す。

## 5. 同じ回に行う：InfinityCategories/Project の整理（11-11 夜、ユーザー決定）

KL-W1 の最終配置で `InfinityCategories/Project/` は 13 のディレクトリ・約 5,735 本になる。最大の `DerivedCategories/`（約 3,687 本）は、2,322 本が一つのディレクトリに平らに並ぶ。ファイルの移動は各レーンにもう一度の追従を求めるので、文献の属性の一括レーンと同じ回にまとめる。

1. **文献に当たるものは文献の場所へ**：HTT・HA・Kerodon の対応表（11-11 にすべて完了）で own・partial に当たる宣言を含むファイルは、`Kerodon/`・`HTT/`・`HA/` の対応する節へ移す。K の文献に沿うもの（Verdier 商・gluing など）は、K の文献ごとの置き場を作るか、K の再開まで `Project/` の中で K の話題として分ける。
2. **残りは話題ごとの下のディレクトリへ**：`DerivedCategories/` なら、写像空間と安定性・擬同型の逆転（roof）・Verdier 商・gluing・コンパクト性と presentable・テンソル・Kan 模型の 7 つ程度。補助の補題は、使う主定理の近くに置けるなら移す。
3. **使われていないものの片付け**：利用者のない試作（`Derived/Diagnostics` など）や主定理の経路から外れたものは、archive に移すか消すかを決める。ModelCategory SSet の 54 本の片付けと同じ回に行う。
4. **段 0**：Codex が 13 のディレクトリごとに行き先の案（文献の節・話題の下のディレクトリ・archive）を、対応表を根拠に出す。行き先は昼にユーザーと調整役が決める。道具は KL-W1 のもの（移動・改名・保存比較・追従）を使う。

## 6. 同じ回に行う：BhattScholze の整理（11-12、ユーザー決定）

`SerrePositivity/BhattScholze/`（542 本）を論文の節に合わせる。KL-W1 の Kerodon 配置と同じ考え方。

- 今の対応：§2 → `Delta/`、§3 → `Prism/`、§3 の site・§4・§5・§6 → `Prismatic/`（270 本が平ら）、§7 → `Semiperfectoid/`・`Andre/`、§8 → `Perfectoidization/`・`Inputs/`、§10 → `Almost/`・`PerfectoidIdeal/`。
- 直すところ：`Prismatic/` を節ごとの下のディレクトリ（site §3.12・§4.1、Čech–Alexander §4.3、結晶 §5、HT §4.2・§6 など）に分ける。節をまたいだファイル（`Prism/Basic/` の Construction 6.1、`Semiperfectoid/` の Ex 7.9 の lci、`Perfectoidization/Derived/` の §10 の部分）を節へ移す。行き先の案は段 0（B1）で、文献の属性の番号と Prisms の地図を根拠に出す。

## 7. 他のレーンとの干渉の避け方（11-12）

1. **移動は「凍結の一晩」に行う（B3）**：その日の夕方までに各レーンの検証済みの分を main に取り込み、夜に一括レーンが移動し、翌朝各レーンが追従する（B4）。移動の夜は各レーンにコミットを控えてもらう（下書きは作業木に置いたまま）。
2. **③-b の新しいファイルの置き場所は B1 の最初に決める**：`Project/DerivedCategories/` の分け方を先に決め、③-b はその新しいパスに置く。決まるまでは `Project/DerivedCategories/` の直下に置き、移動の計画に含める。
3. **⑤∞ は B3 の後に開く**：⑤∞ は drafts を `BhattScholze/` に移すので、BS の整理の後にする（`stage-ii-second-half.md` の 5∞-1 の依存）。
4. 今 BS の本体を触るレーンはない（⑤b・⑤c は ③ に移る）ので、BS の整理は早いほど安全。

## 8. 追記（2026-11-12 夜、調整役）：段 0（B1）の承認

一括レーンの段 0 の報告（`report-bulk-w1.md`、kerodon-layout の 400624b0d）の案 1〜4 をユーザーが承認した（11-12 夜）。

1. 属性：プロジェクト側の独立した `@[cite KEY "番号"]`（Mathlib の `CrossRefAttribute` を手本、Mathlib は改変しない）。partial は `(partial := special|direction|stronger-hyp|component) "理由"` で理由は必須。略号と版の正本は `research/bibliography.json`（新設、K の地図の略号も登録）。照会は `#cite_tags KEY`、場所と行は Lean の環境から。未解決 187 件は台帳で管理し、理由を一件ずつ記録。Kerodon の partial は -c の見直しまで属性を付けない。
2. Project：文献に当たる 51 本のうち HTT・HA の 41 本を文献の節へ、K 系 10 本は Project の話題別へ。`DerivedCategories/` の直下 2,322 本を七つの話題に分け、大きい群はさらに下に分ける。`DiagramComparison/` は維持。Entrypoints・Compatibility・SetWeightedTensors・PointedSpaces は維持。
3. BhattScholze：大分類は維持し、`Prismatic/` を Site・Envelopes・CechAlexander・Crystalline・HodgeTate/{Affine,Comparison} に分ける。越境群は報告 §3.1 のとおり（Construction 6.1 → HodgeTate/Comparison/CrystallineCover、lci 19 本 → Semiperfectoid/Lci、有限包絡 → Semiperfectoid/FiniteEnvelopes、§10 の 6 本 → IntegralPerfectoidization）。
4. 片付け：KST/Descent の 54 本と逆向きの閉包 13 本（計 67 本）を `Archive/KST/DescentConditional/` へ（`audit_kst_descent_main` は維持）。`ScalarTensorView` → `CommutativeAlgebra/Module/`（互換名を残す）。Diagnostics 4 本は Archive へ。

進め方（B2 の準備、凍結の一晩の時期）は別に相談して決める。B2 の準備（全表、静的検査、隔離したプレビュー）は始めてよい。

## 9. 追記（2026-11-12 夜、調整役）：凍結の一晩の決め方（ユーザー：他のレーンの進み具合次第）

日付は決めず、次の四つがそろった日の夕方に「今夜凍結」と各レーンに伝える（前日に予告）。
1. B2 が終わり、隔離したプレビューで移動先のビルドと保存比較が通っている。
2. ⑥ の検証済みの分が途中の取り込み点として main に入っている（11-12 午後の改定：2e の残りが 8,000〜19,000 行で数日以上かかる見込みのため、停止点 2e は待たない）。
3. ⑤a の a が閉じて main に入っている。
4. ③-a・③-b は段の途中でよい（検証済みの分をコミットしてあれば追従は import の書き換えだけ）。
凍結の日：夕方までに各レーンが検証済みをコミット → 調整役が main へ → 夜はコミットを控える → 翌朝 B4 の追従。一晩で足りなければ二晩（B2 の実測で判断）。

## 10. 追記（2026-11-12 夕、調整役）：リファクタの台帳から B3 に入るもの

`refactor-ledger.md` で「B3」とした候補を、凍結の一晩の範囲に足す（B2 の全表に含める）。
- BR26′：共通基盤から BS への新しい逆向きの import 2 本を解消（5 層の静的検査の層違反として）。
- BR14：`Andre/PowerRootEnvelope/Audit/` の監査 4 本を scripts/ へ（配置案の「保持」を改める）。
- BR19：`Prism/Residue/PrismaticResidue` を使う側の節へ。
- BR32：`Delta/DividedPower/` を原典の項目ごとに下位分割、分冪代数の一般部分を CommutativeAlgebra へ（配置案の「Delta は保持」を改める）。
- BR25・R21：docstring の工程ラベルを原典の番号へ、書式の欠け（文献の属性の付与と同じ回）。
- BR8：使われないモジュールの調査（削除は保守）。
- （11-12 夜、追加）BR34（古い docstring 6 件）、BR41（BS の内側の層の逆向き：Delta/DividedPower → Prismatic・Andre）、BR42（`Semiperfectoid/QuotientPerfectoidization` のファイル名）、R84（空の名前空間）も B3 に含める（`refactor-ledger.md` §5・§6）。
