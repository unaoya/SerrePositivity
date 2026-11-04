# IF-W2c 停止点 2

**内部検証・保存比較 PASS。未説明差分 0。** 作業木 `/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3`、ブランチ `infra/if-w2c`、実装 HEAD `af0b57c8a`。

群 A・A′ は 345/345 根、群 B 最終 round 8 は 1,086/1,086 根が PASS。直接禁止辺は 0。禁止 74 本は承認済み M16 の HA 66・ModelBridge 8 と集合まで一致。

## 適用と補充

| 段 | コミット | move | split |
| --- | --- | ---: | ---: |
| A | `d9941f412` | 27 | 16 |
| Aprime | `cd4b4aa53` | 0 | 8 |
| R51 | `eb9e22101` | 3 | 0 |
| R68 | `a7604cfdd` | 34 | 17 |
| R52 | `e805ace85` | 138 | 8 |
| R69 | `866218b0e` | 52 | 25 |
| R70 | `55a630c81` | 58 | 42 |
| R56b | `ed53aeacb` | 13 | 0 |

承認済みの move 325・split 116・reimport 42 を適用。群 B は R51 → R68 → R52 → R69 → R70 → R56b の順。後の群を支える 26 本は停止点 1′ の段階順で先行取り込み、R52 の split 8 本もこの支えに含む。

| 補充の処置 | 件数 |
| --- | ---: |
| 通常の import 追加辺 | 72 |
| 既存依存先への import all 追加 | 15 |
| 元の局所 instance の再登録名 | 9 |
| 匿名 instance の元名の明示 | 8 |
| 完全修飾の出現 | 2 |
| split スコープの調整記録 | 29 |
| 補充コミット / 対象ファイルの異なり | 12 / 106 |

各対象と置換内容は JSON の repair_records に収録。匿名 instance 8 件は、衝突した生成名を before v3b と承認済み split の元の宣言名へ復元した。局所 instance 監査は抽出条件を訂正して 9 ファイルを診断対象とし、9 本とも内部ビルドと before/after v3b が一致した。

## 内部 round

対象根は補充の直接利用者を加えると増える。秒数は鍵の待ちを含む。

| 群 | round | 検証済み | 対象根 | 未検証根 | 失敗モジュール | 秒 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| A | 1 | 155 | 342 | 187 | 15 | 329 |
| A | 2 | 228 | 342 | 114 | 8 | 262 |
| A | 3 | 297 | 342 | 45 | 4 | 1577 |
| A | 4 | 322 | 343 | 21 | 3 | 6021 |
| A | 5 | 343 | 345 | 2 | 1 | 1336 |
| A | 6 | 345 | 345 | 0 | 0 | 753 |
| B | 1 | 600 | 1083 | 483 | 38 | 5100 |
| B | 2 | 812 | 1083 | 271 | 14 | 860 |
| B | 3 | 859 | 1083 | 224 | 5 | 424 |
| B | 4 | 869 | 1084 | 215 | 4 | 40 |
| B | 5 | 989 | 1084 | 95 | 6 | 736 |
| B | 6 | 1001 | 1085 | 84 | 3 | 1133 |
| B | 7 | 1014 | 1086 | 72 | 1 | 113 |
| B | 8 | 1086 | 1086 | 0 | 0 | 2066 |

群 B round 7 は ScaffoldBaseChangeLeftPoint の補充漏れによる同型再発で §16 の停止を記録した。停止記録 df60b4d55、監査訂正 0a340e47f の後、ユーザーがこの 1 件の再開を承認。ScaffoldReconstructionCoefficientPoint の 1 import を補い、当該モジュールの小さなビルド → 補充コミット af0b57c8a → round 8 の順に完了した。

## 保存比較 v3b

before は主対象 964 本と追加利用者 11 本、after は 1091 本。private 補足は before 28 本、after 45 本。基準コミットは 11eacaa39。

| 比較 | before 宣言記録数 | after 宣言記録数 | 生の差 | 未説明 |
| --- | ---: | ---: | ---: | ---: |
| 通常 | 5,456 | 5,454 | 58 | 0 |
| private 補足込み | 5,506 | 5,504 | 58 | 0 |

生の FAIL は保持し、IF-W0-3 §10.34 C・D / §10.35 の個別照合で全 58 件を説明した。宣言記録数の差は、下記の匿名 instance と生成方程式補題の列挙に対応する。

| 生の差 | 件数 | 個別照合 |
| --- | ---: | --- |
| 型 | 45 | 通常の #check・#print・公理が一致。暗黙引数の差は quiver の経路のみ |
| 本体 | 9 | 通常の型・本体・公理が一致。暗黙表示の差は同じ経路のみ |
| 削除扱いの匿名 instance | 3 | 共通 import 環境・型 v3b・公理・属性・元の宣言位置で対応を確認 |
| 追加扱いの pullbackSigma.eq_1 | 1 | 親の v3b が一致。親の表示後の両環境に同じ生成証明補助が存在し、型・公理が一致 |

暗黙表示の差は ReflQuiver.toQuiver(catToReflQuiver inst) と CategoryStruct.toQuiver(Category.toCategoryStruct inst) の対応。全出現の入れ子を検査し、この対応だけを写すと表示全体が一致した。一般の圏について経路の等式を Lean の rfl で検証した。生成証明補助 7 件も直接表示して照合。全判定、型ハッシュ、表示の SHA-256、所有元の対応は preservation-decision.json に保存。

比較スクリプトの補助変数名の衝突は修正し、取得済みスナップショットで比較を再実行した。指紋アルゴリズムと本体の比較器に変更は 0。

## 層検査

| 時点 | 直接禁止辺 | W2a/W2b 禁止 | affected core |
| --- | ---: | ---: | ---: |
| 適用前 | 18 | 150 | 2,531 |
| A・A′ 内部 PASS | 0 | 74 | 1,723 |
| 最終内部 PASS | 0 | 74 | 1,730 |

layer_check --enforce W2b は PASS。個別 ratchet 増加 14 指標は §12 の承認済み診断内。M16 の残余は HA 66・ModelBridge 8。層の例外・ratchet 基準は変更 0。群 B の保留 98 本、K 固有 211 本、一般補助の置き先は既存の段 G 入力を維持した。

## 次の区切り

下流と verify はユーザーの合図待ち。下流前に main（08a2997fd の 2b 取り込みを含む）を merge し、HA の import 行が衝突した場合は両方を残す。下流の 11,152 本は取込前の見積もりで、取込後の実際の木に追従して対象を確定する。verify の指定は VERIFY_JOBS=6 / VERIFY_MEMORY_GB=40。

## 証跡

- [機械可読の停止点 2](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/scripts/refactor/targets/w2c-section6-stop2.json)
- [個別保存比較の全判定](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/.lake/verify/ifw2c-internal/preservation-decision.json)
- [quiver 経路の rfl 検証](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/.lake/verify/ifw2c-internal/individual/quiver-path.lean)
- ログ・スナップショット・再現スクリプトは `/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/.lake/verify/ifw2c-internal`。
- §10.34 に従い、照合済みの一時復元コピーは削除した。全証跡と共有パッケージは保存。main 作業木での変更・ビルド実行は 0。以前からの未追跡 W2b 停止記録 5 本を保持。
