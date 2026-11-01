# §10.17：DG-W1後のW1ルートimport更新

main `bdf6da770` の指示を読み取り、現mainのルート664件と承認済みの∞入口5本の和集合へ更新した。**785 → 669件**。W1/W2aの移動・分割元を直接importする行は0件で、除去対象なし。他のW1項目、非ルートreimport、downstream_imports、w2a.jsonは不変。数学ソースは未変更。

| 検査 | 秒 | 終了コード | status | 増加指標 |
| --- | ---: | ---: | --- | ---: |
| w1 | 34.822 | 0 | PASS | 0 |
| w1-w2a | 32.388 | 0 | PASS | 0 |

§10.14後とのafter指標は完全一致（層別直接違反・tier別禁止閉包・入口辺）。W1は直接違反325、閉包W1=1/W2a=257/W2b=257。累積は直接違反296、閉包W1=1/W2a=178/W2b=178。12splitに保存済みsnapshotを指定し、全12本の保存ソースが現ソースと一致することを確認した。Lean実行なし。新しい保存証拠のbefore snapshotはrsync後に採る。

全コマンド・時間：`.lake/verify/ifw0-3-addendum17/cli-results.json`。変更の全内訳：同 `root-refresh.json`。前回の停止診断は履歴として保存する。次は全ビルド不在確認 → 指定rsyncを前景で直接実行 → before snapshot → 束の適用 → 停止点1。
