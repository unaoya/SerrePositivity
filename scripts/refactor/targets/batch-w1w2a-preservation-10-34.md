# IF-W0-3 停止点2′：§10.34 の保存比較（2026-11-01）

**STOP_POINT_2_PRIME。Aの本体ハッシュ差28組と、before未復元の4件を残して停止。コミット・verifyは未実行。** scratch worktreeは削除済み。mainと数学的宣言の本文は変更していない。

## A：生成名の規則と試験

`compare_snapshots.py` に `_aux_<encoded module>___macroRules_…` / `___unexpand_…` を対応表で正規化する規則を追加。macro名内の `_private_<encoded module>_<number>_` も同じ対応で写す。splitは宣言ごとの移し先を使い、通常の識別子・似た接頭辞は変更しない。型・本体・公理・属性の比較は維持。

試験1件を追加（move形式の埋込名、splitの宣言別配置、似た名前の非一致、本体ハッシュが違うとFAIL）。Python全171件PASS、4.803秒。自作比較処理で通常名にも不要な照合をしていたため、生成名の形式の抽出と完全一致の辞書検索に修正した。

56件のremoved/addedは28組に対応したが、**28組ともbody hashが不一致**。ppでも宣言名を対応させただけでは本文が異なる。例：

```text
before: Name.anonymous.mkStr "_private" ... .mkStr "HomotopyLimits" ...
after:  Name.anonymous.mkStr "_private" ... .mkStr "ModelBridge" ...
```

本文中で引用されたprivate名を`Name.mkStr`で組み立てる箇所にも、旧/新モジュールが埋め込まれている。現行のDAGハッシュはこの式中の文字列を通常の値として数えるため、宣言名だけの正規化では解消しない。§10.34-Aの「型・本体のハッシュが一致しなければ一覧に残す」に従い、body hashを上書きしたり文字列一般の正規化を足したりしていない。4ファイルの28組の詳細はJSONのA一覧と`macro-body-diff-*.txt`。

## B〜D：元の残り13件の表

Bの削除/追加を各1行として13件を列挙する。結果は一致9件、未照合4件。Dの補助宣言は本体と補助そのものを#printし、通常表示の型・本体で照合。`pp.explicit true`の差も保存した。linterメッセージの診断ファイルパスはppではないので分離した。

| # | 対象 | 判定 | 処置・根拠 |
|---:|---|---|---|
| 1 | `doubleMappingCylinder_hom_ext（旧配置から削除）` | 一致（B） | 型/本体ハッシュ・kind・公理・属性が一致。宣言別対応表をMap→Descの実際の配置に合わせた。 |
| 2 | `doubleMappingCylinder_hom_ext（新配置に追加）` | 一致（B） | 型/本体ハッシュ・kind・公理・属性が一致。宣言別対応表をMap→Descの実際の配置に合わせた。 |
| 3 | `instIsDGPretriangulatedDGOdotGluing_5` | 未照合 | beforeの同名接頭辞候補0。型ハッシュ一致のnamed theorem 2件は位置が異なり番号変更と同定できず。対象のbefore成果物は未復元。 |
| 4 | `initial_left` | 一致（D） | 通常型pp・公理一致。明示#printの証明内にはinstance経路差。 |
| 5 | `Direction` | 一致（D） | noConfusion/noConfusionType：生成宇宙名 v._@.<module> のモジュール部分だけの差。対応表で一致。 |
| 6 | `FiniteSpanVertex` | 一致（D） | noConfusion/noConfusionType：同じ生成宇宙名のモジュール部分だけの差。 |
| 7 | `kanTensorReplacement_isCofibrant` | 未照合 | before KanTensorFrameAdjunctionの成果物未復元。after出力は取得済み。 |
| 8 | `kanTensorReplacement_isFibrant` | 未照合 | 同上。 |
| 9 | `kanTensorReplacement_left_isFibrant` | 未照合 | 同上。 |
| 10 | `detected_inf` | 一致（D） | 通常型pp・公理一致。明示表示でCompleteLatticeからLatticeへのinstance経路差。 |
| 11 | `generators` | 一致（D） | 通常・明示表示とも型と本体が一致。 |
| 12 | `emptyMatchingTerminal` | 一致（D） | 本体と_proof_1の通常型/本体pp一致。明示証明内のSmall instanceはCountable.toSmall経由→small_subsingleton経由。 |
| 13 | `pointMatchingTerminal` | 一致（D） | 本体と_proof_1の通常型/本体pp一致。明示証明内のSmall instance経路が異なる。 |

Cの型ハッシュ（1026712898231884901）でbefore全行を検索すると、`outerMiddle_pretriangulated`（DGOdotMilnorOuterInclusionComparison）と`outerProjection_middle_pretriangulated`（DGOdotMilnorOuterProjectionComparison）が見つかった。ただし`instIsDGPretriangulatedDGOdotGluing_*`の候補は0で、local instanceのソース位置（DGOdotMilnorProjectionRectangle 22–23行）と同一の親だと同定できない。そのため単に型が同じnamed theoremへ付け替えていない。

定理のpp一致を認めたものはbefore/afterの公理一覧も一致。Direction/FiniteSpanVertexはnoConfusion/noConfusionTypeの生成宇宙名を対応させると、通常・明示の型と本体が一致。MatchingTerminalの親と補助_proof_1は通常型/本体ppが一致するが、明示証明項にはSmall instanceの経路差がある。この差を隠さず、全diffを保存した。

## scratch復元の前提との食い違い

指定どおり `git worktree add --detach ../SerrePositivity-ifw0-3-before aacd82f41` で作成し、依存パッケージはAPFS複製。mainは変更もビルドもしていない。Lakeの3変数はtrue/true/共有cache directory、他のlake buildがないことと排他lockを確認し、対象11モジュールに絞って`lake build`を実行した。

**キャッシュからの復元だけでなく、実際の再コンパイルが発生した。** §10.34-D-1の「キャッシュに当たるので再コンパイルなし」という前提と異なるため、今回のscratchビルドだけをSIGTERMで停止。停止時までに165プロジェクトモジュールのBuiltを記録、コンパイルエラー0。最初の新規はEInfinity.Hammock.Word（3.7秒）、HomotopicalAlgebra.Generated.Basic（3.5秒）。11対象中9本のoleanは存在し、KanTensorFrameAdjunctionとDGOdotMilnorProjectionRectangleの2本は未復元だった。

再ビルドを再開せず、復元済み9モジュールとafterで診断のみを実施した。診断完了後にscratchをgit worktree removeで削除済み。beforeソース、入力コマンド、pp出力、diff、Lakeログは主worktreeの`.lake/verify/batch-w1w2a/stop2/addendum34/`に保持（scratch内にしかない証拠はなし）。

自作のpp採取では、未対応pp.widthを削除し、private補助名のためmodule/import allと環境実名の参照に修正。CommandElabMのオプションAPIの誤りはset_option構文で直した。これらは診断スクリプトの修正で、ライブラリの宣言を変更していない。最終pp採取は対象の全実行が終了コード0（未復元のbefore2本は未実行）で、失敗した初回診断ログも保持した。

## 保存比較と未実施事項

機械比較：A正規化後41件、B配置記録の修正後39件（added1・type5・body29・auxiliaries4）。Dのpp基準で7件を一致扱いにしたため、未解決は32件＝A28組＋C1件＋Kan3定理。元の69件の結果は履歴として保持し、hashを改ざんしてPASSにしていない。

transient・重複宣言の扱いは§10.21〜10.22のまま。before17,180件／after17,181件、transient前後323名・335行、生成private衝突12名、Hammockの本物の重複2行を維持。

未解決があるので「downstream imports」「監査の追従」「保存比較の規則」はまだコミットしていない。verifyは未実行で今回のsummaryはない。監査7本の追従、下流補充75モジュール・83 import、既承認の層検査（直接違反294、禁止閉包166）を保持している。

今回の変更はcompare_snapshots.py、test_snapshot_identity.py、処置のJSON/本報告と停止記録。数学的Leanソース・verify本体は変更なし。次の判断が必要なのは、Aの引用Name値の正規化範囲と、beforeの残り2モジュールをキャッシュmiss時の再コンパイルも許して復元するか。
