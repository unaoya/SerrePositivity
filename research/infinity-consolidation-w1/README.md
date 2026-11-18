# IC-1 段0の静的な資料（2026-11-17）

以下は段0提出時に凍結した静的資料。現在の適用・検査の状況は [IC-W1報告](../../formalization-plans/stage-ii/consolidation/report-infinity-consolidation.md) を参照。IC-1は2,264本・26単位の移動を完了し、原参照3,858本、数学対象ビルド・v3b各4,314本、追従文書4章、引用・タグ118件の欠落/余分0、通常rootの検査が成功した。正式全監査とverifyは調整役が実施する。正式なnative所有元・改名案・修復証拠は [外部証拠の目録](../../evidence/ic-w1/ic-1/manifest.json) の領域に保持する（IC-1完了時の目録）。`source-name-hints.csv` は段0のソース候補のままで、正式な宣言の改名表として使わない。

|資料|内容|
|---|---|
|moves.csv|残り2,264本の旧→新パス/module、namespace案、ソースSHA|
|source-name-hints.csv|ソース上の7,414行の名前候補、旧名→新名。native所有元ではない|
|namespace-prefix-proposal.json|所有元ごとの接頭辞の案。一括文字列置換の入力には使わない|
|branch-impact.json|他枝の最終観測。head/head_after、作業木の影響、対象path集合と内容索引hash|
|layer-preview.json|既存checkerによる仮の層metadata移送、新規0（既存172は保持）|
|concrete-boundary-imports.csv|一般分類から具体BE部品への41ファイル/50辺|
|infinity-files.csv / infinity-content.csv|InfinityCategoriesの全15,972本の内容別ソース索引とディレクトリ集計|
|dg-classification.csv|DG全473本の主用途分類。Checks309を含め据置|
|choose-inherited.json|③-aの255行の元判定を保持（raw source全文だけ省略）|
|choose-new-candidates.json|255外の選択語の全699候補。証明内・数値chooseも種別を保持|
|choose-additional.md / choose-additional-review.json|データ候補の全行表、両立判定、利用側ソース参照、推移importer|
|b1-chapter-candidates.csv / b1-leaf-candidates.csv|80行以下の内容別全候補と、全importer0という狭義の葉の別表|
|root-outside-audit.csv|正式106監査の静的閉包からroot閉包を引いた4,332本|
|summary.json / supplement-summary.json|件数・継承元とのSHA/存在差分等|

研究用スクリプトはソースだけを読み、研究資料を生成する。LeanやLakeを起動せず、本体・設定・他worktreeは変更しない。再実行は新しい作業木/枝の内容を読み直すため、同じ過去の観測の再現とは区別する。

1. `python3 research/infinity-consolidation-w1/stage0.py`：基本の表とgit外のsource graph cache（内容hashで照合）。
2. `python3 research/infinity-consolidation-w1/layer-preview.py`：既存checkerによるmetadata移送の仮照合。
3. `python3 research/infinity-consolidation-w1/supplement.py`：B1/境界/③-a継承範囲の補助集計。
4. `python3 research/infinity-consolidation-w1/final-branches.py`：他レーンの最後の観測を固定。
5. `python3 research/infinity-consolidation-w1/review-choices.py`：固定した他枝のpath集合と追加候補を照合し、ソースの利用箇所索引と紙の判定を生成。
6. `python3 research/infinity-consolidation-w1/verify-paper.py`：表と報告の整合・元ソースSHA・件数を確認。

`review-choices.py`の6件の「要らない」は利用側を読んだ紙の判断を収録したもの。他は「不明」を保ち、自動でcanonicalと判定しない。すべてソースの宣言境界と短名による索引であり、private・生成宣言・open等の束縛は明朝以降のnative採取が必要。新しい判定・指定構成の実装はこの紙の適用に含めない。

大きいraw source captureとgraph cacheは `/private/tmp/ic-w1-choose-capture.json`、`/private/tmp/ic-w1-stage0-graph.pickle`。gitにはソース全文・olean・実行ログを加えず、再生成できる表・判定・目録だけを置いた。
