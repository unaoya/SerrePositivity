# IF-W2c §6 内部検証の停止記録

**§16 の再発停止。停止点 2 は未到達。** infra/if-w2c の適用・補充 HEAD は `377713b67`。作業木は `/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3`。群 A・A′ と群 B 全 6 項目を適用済み。

## 停止理由

群 B round 7 で `SerrePositivity.KST.Fibration.ScaffoldBaseChangeLeftPoint` が再び Unknown identifier になった。round 5・6 の一覧に既にあった smallUnstraighteningPointedImage の定義元を、私の round 7 の補充束から落としていた。現在は同名と scaffoldPointedReconstruction_coefficient_pointHom の 2 件。IF-W2b §16 の「補充したモジュールが次の round でも同じ型で落ちる」に従って停止した。

群 A は 345/345 根 PASS。群 B は 1,014/1,086 根が検証済みで、未検証 72 根、失敗モジュール 1 本。after snapshot v3b と保存比較は内部検証の完了後に行う。

## 適用コミット

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

合計は move 325・split 116。R52 の split 8 本など、後の群を支える 26 本の先行取り込みは停止点 1′ の段階順に従う。宣言の名前空間は保持。

## 内部 round

根の集合は、補充先の直接利用者が増えると増える。時間には共有鍵の待ちを含む。

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

群 B round 2 は個別検査済み 35 本を先に補充し、依存先の補充を待つ 3 本は未補充として記録。round 6 も同様に 5 本を先に補充し、ScaffoldBaseChangeLeftPoint を保留した。round 7 でこのファイルに補充した後、同じ型の失敗が再発した。

## 静的検査と保存

| 時点 | 直接禁止辺 | W2a/W2b 禁止 | affected core |
| --- | ---: | ---: | ---: |
| 適用前 | 18 | 150 | 2,531 |
| A・A′ 内部 PASS 後 | 0 | 74 | 1,723 |
| 今回停止時 | 0 | 74 | 1,730 |

layer_check --enforce W2b は PASS。禁止 74 本は HA 66・ModelBridge 8 で、承認済み M16 の残余と集合まで一致。個別 ratchet 増加 14 指標は §12 の承認済み診断内。基準と例外の変更は 0。

fresh before v3b は主対象 964 本、追加利用者 11 本、private 補足 28 本を取得済み。匿名 instance 8 件は、分割後に変わった自動生成名を before v3b と承認済み split の元名へ明示的に復元した。最後に全 split の kept→moved private 宣言依存と局所 instance 依存を照合し、参照復旧の残りはいずれも 0 件。after v3b の一致判定は保留。

## 再開候補

ScaffoldBaseChangeLeftPoint に次の 1 import を補充する案。

```lean
public import SerrePositivity.KST.Fibration.ScaffoldReconstructionCoefficientPoint
```

この閉包は上の未解決 2 宣言の定義元を両方含む。未適用の静的模擬は循環 0・直接禁止辺 0・禁止 74・affected core 1,730・enforce PASS。候補のコンパイルは承認後に行う。

§16 の再発停止からの再開承認後、候補の小さなビルドと補充コミット、内部 round 8、内部 PASS 後の after snapshot v3b と保存比較を行い、停止点 2 を報告する。

main 08a2997fd の merge は、ユーザー指示どおり下流の前に行う。HA import 行の衝突は両方を残す。下流 11,152 本と verify は停止点 2 後の合図待ち。

## 証跡

- 機械可読の停止記録は [w2c-section6-internal-stop.json](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/scripts/refactor/targets/w2c-section6-internal-stop.json)。全未検証根、各補充の一覧、残余 74 本、14 指標、元名復元の根拠を含む。
- 実行ログと before v3b は `/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/.lake/verify/ifw2c-internal`。
- 再現用スクリプトは `/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/.lake/verify/ifw2c-internal/runners`。一時 baseline は /private/tmp/ifw2c-before-11eacaa39。
- 以前からの未追跡 W2b 停止記録 5 本を保持。main 作業木での変更・ビルド実行は 0。
