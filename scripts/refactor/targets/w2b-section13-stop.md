# IF-W2b §13：内部ビルドの停止報告

§5-3（補充が禁止辺）により停止。成功の停止点 2 には未到達。

`Core.FilteredExchange.SpecifiedApexConeRestrictions` の `SpecifiedApexLimitConeTransport.apex` と `.diagram` は、型に `F1.FilteredExchange.SpecifiedApexLimitConeTransport` の構造を使う。before snapshot の `uses_modules` とソースの両方で確認した。現在は import が空で、補うと **Core → F1** の順序違反・restricted 違反になる（直接違反 18 → 19）。import と配置は変更していない。草案の Core 配置・import 削除と実際の宣言依存が一致していない。

|工程|結果・所要時間|
|---|---|
|main merge|408b0f05a、衝突なし|
|Lake キャッシュ復元|PASS、110 根、14.216 秒、Built 1 本|
|before snapshot v3b|PASS、3,616 本、1,687.627 秒（28 分 7.6 秒）|
|R73|4d02ee532|
|R37|d12e85d0e|
|R38|9c38c984e|
|適用後静的検査|承認済み模擬との差 0、archive 利用者 0、enforce PASS|
|内部ビルド|途中停止。188 群・1,128 / 1,899 対象、最後の終了群まで 2,382.286 秒（39 分 42.3 秒）|
|after snapshot・v3b 保存比較|未実施|
|下流ビルド・verify|未実施|

内部ビルドの全群ログを走査し、失敗モジュール 57 本、Built 表示の異なるモジュール 1,156 本を確認した（対象外の依存ビルドを含む）。全 1,899 対象の完走結果ではない。停止時の実行プロセスは終了し共有鍵は解放された。生の runner state は中断により RUNNING のままなので JSON 記録に停止状態を補記した。

|層指標|merge 後 before|適用後・補充前|
|---|---:|---:|
|直接違反|294|18|
|中核の順序違反|—|0|
|W1 禁止モジュール / affected core|1 / 11|0 / 0|
|W2a・W2b 各禁止モジュール / affected core|166 / 3,379|150 / 2,528|

承認済み個別 12 指標と経路は JSON の `accepted_ratchet_paths` に保持。ratchet 基準と例外は変更していない。A/C の適用後 405 モジュールの監査収録漏れは 0。

追加のソース検査は、3,605 本の import 以外のテキスト、分割した宣言 50 件が保持されていることを確認した。これは未実施の v3b 保存比較を代替しない。

全失敗の先頭 3 エラー、停止を生む補充の模擬、未適用の補充候補、宣言単位の参照根拠、自己作成 runner の修正は [JSON](w2b-section13-stop.json) に記録した。補助ソース検査の一時 FAIL は複数行 import と削除後の改行差の扱いによるもので、検査を修正して PASS を確認済み。

この報告と前回の復元停止記録は未コミット。適用コミット後の Lean ソースの追加変更はない。
