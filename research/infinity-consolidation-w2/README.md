# IC-2 の段 0 の調査表

基準は main `1522321e5b9670138fdde80272d53cacae756ebc`。判断と停止点は [IC-2 の段 0](../../formalization-plans/stage-ii/consolidation/report-infinity-consolidation.md#ic-2-の段-0) に記録した。すべてソース調査と配置案。

| 資料 | 読み方 |
| --- | --- |
| `moves.csv` | IC-1 と同じ列。旧→新パス・モジュール、単位、行数、元ソースSHA。既存の公開宣言名を保つ案。 |
| `inventory.csv` / `unreached.csv` | 旧分類の全候補と、三条件のどれからも届かない候補の部分集合。各列の `→` は明示 import の経路。正式監査、blueprint、draftは補足の列。 |
| `roots.json` | 主定理・sorry入力のファイル、root・各入口、対応表の根と根拠行、観測した枝の根、正式監査一覧。 |
| `placement.csv` / `classification-differences.csv` | 置き場所の番号と種類、旧番号、同名回避。分類が異なるファイルの一覧、型の抜粋と留保理由。 |
| `excluded-previous-moves.csv` | 旧表スナップショット後に OE-W1 または IC-1 で到着した対象域のパス。 |
| `source-names.csv` | 明示名のソース候補。旧名と新名は同じ案。件数には private・生成宣言を含めない。正式な採取は後続承認後。 |
| `import-followups.csv` / `branch-impact.json` | mainで移動範囲外から直接 import する行先と、別枝の直接・推移影響。 |
| `layer-preview.json` / `layer-holds.csv` | 模擬グラフの既存検査器との差分、保留案、旧層判定の変化。 |
| `b1-leaves.csv` | 80行以下で新配置の同一単位内に直接 importer がないファイル。全体では利用元があるので `importers` も併記した。 |
| `summary.json` | グラフ・到達範囲・配置・影響・B1の集計。 |

基準の作業木で `python3 research/infinity-consolidation-w2/stage0.py`、次に `python3 research/infinity-consolidation-w2/proposal.py` を実行すると再集計できる。中間グラフは `/private/tmp/ic2-stage0-intermediate.json` に置く。枝影響は実行時に観測できるローカルrefと作業木を読むため、当初の観測と同じになるには枝と作業木も一致する必要がある。後続の main へは基準コミットと対象を更新してから使う。PythonとGitで完結する。
