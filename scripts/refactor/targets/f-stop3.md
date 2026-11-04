# IF-F F-2 草案 — 停止点 3

**草案のみ。名前空間・ディレクトリ・宣言は未変更。** `65c321e1f` §5：KST から移した宣言だけ、F1/F1B/F2 は改名しない。deprecated alias は段 G の最初の区切りまで保持する。

## 計数と対応表

[f-namespace-map.json](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/scripts/refactor/targets/f-namespace-map.json)：**730 モジュール、811 namespace ブロック、明示名3,849＋匿名 instance 22＝3,871 宣言コマンド**。明示名のうち private 176。これは生成補題・constructor・projection を含まないソースの計数。匿名22件は現行ソースと完全一致する既存 v3b から全件の名前を復元した（Lean実行0）。
730本すべてにソース一致の保存済み環境があり、KST 名の記録は 8,418 件、source-parent に従う生成名 4,476 件を補助一覧に収録。古い環境の依存先は変わりうるので、適用前 snapshot で再照合する。これを現行ビルド済みの保証とは扱わない。

| 由来 | モジュール |
| --- | ---: |
| w1.json | 8 |
| w2a.json | 307 |
| w2c-combined-plan.json | 415 |

「KST から移した宣言だけ」を730本として計数し、先行 W1/W2a の315本と W2c の415本を明示的に分けた。W2b の計画には KST 発の直接移動はない。§5の「W2b・W2c」を時期の厳密な限定として扱う場合は、対応表の provenance で W2c 415本だけを選べる。KST 以外の旧名前空間をこの対応表へ混ぜていない。

対応は `SerrePositivity.KST.<area>` を現ディレクトリの namespace へ替え、下位 namespace を保つ。新名の衝突候補2組はファイル名の子 namespace を使う案にし、新名同士・既存の明示 public 名との衝突0。

## alias の判断点

定理は deprecated alias、定義は宇宙・暗黙引数を保った abbreviation。instance は旧名側へ二重の instance 属性を付けない。構造体・inductive の型だけでなく生成名も互換対象として照合する。private を一括公開せず、公開化は F-1 の19補助定理だけ。
**旧 public 名の重複が1組**：`SerrePositivity.KST.Comparison.doubleMappingCylinder_hom_ext`（Kan.DoubleMappingCylinderDesc / Map）。新名を分けるだけでは旧 alias が二重定義になる。IF-F §6（main 9f59541d3）の回答に従い、旧名の deprecated alias は宣言の利用者が多い方にだけ付け、他方は alias なしで利用者を新名へ書き換える。共通互換入口案は採用しない。適用前に所有宣言と実参照を照合して多い方を確定する（モジュール直接利用者は両方3、逆閉包は Desc 1,449 / Map 1,473 だが、これは宣言の利用者数ではない）。Map側の同名はソース一致キャッシュに所有宣言として現れない点も記録した。草案で自動解消・適用はしない。

## 利用者と下流

| 領域 | 完全修飾名のソース出現元 | 直接 import 利用元 | 逆 import 利用元 |
| --- | ---: | ---: | ---: |
| BS | 0 | 0 | 0 |
| KST | 16 | 664 | 6373 |
| 論文の層 | 0 | 0 | 0 |
| G1 | 0 | 1 | 5 |
| EInfinity | 0 | 0 | 136 |
| DG | 0 | 0 | 0 |

完全修飾名の列は字句上の出現であり、open や短い名前による参照は未解決。0 は「利用なし」の証明ではない。import の列を保守的な影響上界として併記し、全モジュール名を JSON に収録した。G1 は取り込み7bda72c3cで追加された9ファイルを集合として追跡。論文の層は Paper/CLMST/IntersectionMultiplicity/Asymptotic を数える。
本番BSの逆importは0だが、追跡中のBS draftsには **22 本**の影響がある。草稿と本番を分けて記録した。
名前空間だけ替える場合でもモジュールの逆依存は **11,538 本**（種730本を含む）。W2cの温まった木からの線形参考値は約 38.7 分。名前付け替え・alias の内部照合とcold cacheを考慮して下流に2–4時間の予備枠、verifyは別枠を見込む。ディレクトリ改名はしないので、その試算・案は作っていない。

## 次の手順

G2・BS の区切りで合図を受けた後、対象範囲と旧名重複の正本を確定し、before v3b → 名前だけの付け替えと alias → 保存比較 → 下流・verify。README の F1・F1B・F2 の内容表も適用時に更新する。alias 削除は BS・G2・KST の移行確認後、段 G の最初の区切りに別束で行う。

F-1 は [f-stop1.md](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/scripts/refactor/targets/f-stop1.md)。本報告は停止点3の判断資料であり、適用の合図を代替しない。
