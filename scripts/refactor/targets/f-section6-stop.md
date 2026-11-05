# IF-F §6 適用中の停止 — private 同名の衝突

基点 main 29d9ad0e7、草案 20b781f39、承認 main 9f59541d3。作業木 infra/if-f。main 作業木で変更・ビルドなし。

## 実行済み

- 適用前ビルド PASS（30,898 jobs）。private を含めた144本の before snapshot v3b PASS（482.7秒）。
- 承認された19補助定理を定義元で公開、15辺を通常 import へ置換。型・証明のソースは変更していない。
- R67 check 2本の所有モジュール名を追従。sorryAx の許可は正確な3所有モジュールだけ、HT-KQ直接引用1件の検査は維持。
- ArrowFactorization 3本を Foundation に分類。分類だけで変わった config SHA に enforcement 基準を追従し、既存の許容辺・数値上限は維持。現行 ratchet は f-layer-baseline.json。
- F-2 の旧名 alias 方針のみ記録。F-2 の名前空間・alias・利用者の書換え、および台帳のその他の処置は未適用。

## 停止理由と未適用案

内部ビルドで **1モジュール**失敗：SerrePositivity.KST.Fibration.FirstVertexOppositeChart:24:14

> a non-private declaration SerrePositivity.KST.Fibration.mapNormalizeCompositionWithEq has already been declared

草案は別モジュールの private 内部名が異なることから衝突しないと推定した。しかし公開名が入った環境では同じユーザー名の private 宣言自体が拒否された。公開宣言同士の衝突ではないが、草案の判断は不十分だった。

**未適用案**：このファイル内の private 定理を firstVertexOppositeChart_mapNormalizeCompositionWithEq にし、参照1か所を同じ名前へ追従する。変更は2か所だけ。公開した19個の名前は維持し、private 定理の型・証明本文・配置も保持する。

具体的な差分：[f-section6-private-collision-proposal.patch](f-section6-private-collision-proposal.patch)。この差分は作業木に適用していない。

停止の根拠は IF-W2c §4 が継承する IF-W2b §5-4：「**宣言の本文・型・名前を変えないと直らない。**」および §6 の名前変更禁止。今回の事前承認は import・修飾等の判断表の範囲内なので、private の改名も自動適用しない。

## 静的検査と残作業

- 層検査3条件 PASS、直接禁止辺0、F1B入口・監査の straightening 0、例外追加0。
- 禁止74本（M16）・affected core 1,732本は適用前後で同じ。全ratchet数値も同一。
- W2c報告時の1,730からの既存+2は F2.Tensor.SetSections / Space（mainからの取り込み済み部分）。W2a/W2bそれぞれの閉包指標4件を f-section6-stop.json に記録。F-1による増加ではない。
- R67 checkの実行、下流144本、after snapshot・保存比較、verifyは**未実行**。内部ビルド失敗時点で進行を止めた。
- before snapshot・全ログ・runners は .lake/verify/if-f-apply/ に保存。

改名が承認されたら、候補の小さなビルド → 内部検証（R67を含む）→ 下流144本 → after snapshotと個別保存比較 → 層検査 → 正式verify（6 jobs / 40 GB）→ 停止点2。比較器・監査は弱めない。
