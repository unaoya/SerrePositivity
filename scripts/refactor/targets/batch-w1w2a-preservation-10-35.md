# IF-W0-3：§10.35 保存比較の完了（2026-11-01）

**保存比較PASS、未解決0。** §10.35で承認された規則を適用し、残り4件も照合済み。scratch削除済み。「downstream imports」「監査の追従」「保存比較の規則」を別々にコミットし、停止せずverifyへ進む。この記録時点ではverify未実行。

## 記法の生成宣言

`_aux_<module>___macroRules_…` / `___unexpand_…` の生成名のガードを追加し、transientとして保存比較から除外。定義元のencoded moduleとの完全一致を要求し、ソースに同名の人手による宣言があれば除外しない。本文のName.mkStrやリテラルを写す正規化は作っていない。

この一般ガードに該当したのは769組。今回不一致だった28組と、以前から一致していた741組を区別し、全実名・定義元を同名JSONの`notation_transients`に記録。既存のprivate生成名12組のガード・実名記録と、Hammockの同名定理2行の保持は継続。

## 残り4件

| 対象 | 判定 | 根拠 |
|---|---|---|
| 無名instance | PASS | 同じモジュール、同じ型pp。ソース位置がlocal instanceであることを前後で確認 |
| kanTensorReplacement_isCofibrant | PASS | 通常型ppと公理一覧が一致 |
| kanTensorReplacement_isFibrant | PASS | 同上 |
| kanTensorReplacement_left_isFibrant | PASS | 同上 |

無名instanceの実際の対応：before `SerrePositivity.KST.SConstruction.instIsDGPretriangulatedDGOdotGluing_5` → after `SerrePositivity.KST.SConstruction.instIsDGPretriangulatedDGOdotGluing_5`、定義元 `SerrePositivity.KST.SConstruction.DGOdotMilnorProjectionRectangle`。番号を落として他モジュールの同型定理に合わせるのではなく、(モジュール, 型pp)と匿名のソース位置で同定した。照合の道具は型・モジュールの相違、名前付き宣言、複数候補を拒否する。

§10.34のB 2件・D 7件は§10.35で承認済み。Bはハッシュ一致に基づく配置表の修正、Dは通常型/本体pp、公理、および生成宇宙名の対応の証拠を保持した。承認済み7件のhash差分が同じままであることも照合した。

## 比較数と証拠

- ハッシュ比較の件数：before 16,411、after 16,412。beforeの統合snapshotに無かった無名instance 1件は復元環境から照合したため、照合済み総数は16,412件。
- transient名：before 1,092、after 1,092。既存323名＋今回の記法補助769名。
- 生の機械比較に残る差11件は、承認済みpp 7件と今回の4件。`raw_changes`を保持し、各項目に判定規則と証拠を結び付けた。hashを変更して一致させてはいない。
- 最終判定：PASS、`changes: []`。`.lake/verify/batch-w1w2a/stop2/addendum35/preservation-final.json`。

## scratchと試験

scratchはaacd82f41で再作成し、他のlake buildがないこと、共有ロックとLakeキャッシュ3変数を確認して対象2モジュールだけを復元。再コンパイルも許可された今回のビルドは4,642本・2605.365秒、終了コード0。前回の165本とは別の実行の件数。指定2モジュールの依存先を含むため「数百本・数分」の見込みを超えたが、対象を増やして全体ビルドに切り替えてはいない。

pp診断は136.904秒。`#print`・通常`#check`・`pp.explicit true`の出力、無名instanceの実名・ソース位置・型pp・公理を保存した。scratchは使用後に削除済み。

Python試験は173件PASS（7.606秒）。追加したガードと匿名instanceの照合の試験を含む。主worktreeの数学的Leanソースは今回変更していない。mainは変更もビルドもしていない。

## 束全体と次の関門

下流ビルドは承認済みPASS。補充75モジュール・83 import、監査7本の旧名325件の追従、split18件の両側列挙と監査の直接import8件を保持。層検査は停止点1→最終で直接違反296→294、W2a/W2b禁止閉包177→166。W1は1→1。

roundごとの時間・新規成功・失敗数は`batch-w1w2a-downstream-imports.json`。収束の尺度は失敗数22→3→1→0。verifyは`VERIFY_JOBS=3`・監査キャッシュなし・Lake成果物キャッシュ有効で実行する。
