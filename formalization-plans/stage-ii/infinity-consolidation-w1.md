# 整理 IC-W1：∞ 圏のコードを InfinityCategories に集め、内容ごとにディレクトリを分ける

作成：2026-11-16 夜（調整役）。決定：ユーザー（11-16「内容に合わせてディレクトリ分けをしたいのと、無限圏は InfinityCategories に移したい」「模型は a で」「3b のチャットは不調なので別のチャットで」）。担当：新しいチャット（レーン ⑦、③-b の OE-W1 を引き継ぐ）。

## 0. 目的

1. ∞ 圏の一般論を `InfinityCategories/` に集め、Kerodon・HTT・HA の節に置く（`kerodon-layout` の規則、`InfinityCategories/<Kerodon|HTT|HA>/...`）。
2. それ以外も内容ごとに分ける：一般のホモトピー論・モデル圏は `HomotopicalAlgebra/` の主題ごと、K 理論に固有のものは `KST/` の中で K の文献ごと。
3. **模型は `InfinityCategories/Models/`**（ユーザー決定、案 a）：KST の Sp（BF の Ω スペクトル）は `Models/Spectra/OmegaSpectra/`、Spectra/ の対称スペクトルは `Models/Spectra/Symmetric/`、厳密な dg 圏の模型は `Models/DGCategories/`、BE の模型は `Models/EInfinity/BarrattEccles/`（名前は段 0 で決める）。docstring に「模型。文献の定義との比較は後で」（`p0-plan-draft.md` §6）と一行。
4. 主張・証明は変えない（移動・改名・docstring・import だけ）。

## 1. 範囲と順序

| 束 | 中身 | 資料 |
| --- | --- | --- |
| IC-0 | **OE-W1 の段 1 を引き継いで完成させる**（`refactor/organize-einfinity`、d216f410b、作業木 `SerrePositivity-bs-d68`。456 本の移動、目録） | `organize-einfinity-general.md`、`report-organize-einfinity.md` |
| IC-1 | EInfinity の残り（OE-W1 の段 2：一般 1,247 本、BE 固有 1,047 本 → Models、E∞ の一般論 327 本） | OE-W1 の `stage2-classification.csv` |
| IC-2 | KST・HomotopicalAlgebra・Spectra の一般の ∞ 圏論 1,725 本 | `research/infinity-outside-map/files.csv`（738be1c06） |
| IC-3 | 同じく模型 3,776 本 → `InfinityCategories/Models/` | 同上 |
| IC-4 | 同じく一般のホモトピー論・モデル圏 2,415 本 → `HomotopicalAlgebra/` の主題ごと、K 固有 912 本 → `KST/` の中で | 同上 |
| 後回し | 未定 1,243 本（一般の補題と K の構成が一つのファイルに混ざるもの）。ファイルを分けてから分類し直す。IC-W1 では動かさない | 同上 |

IC-0 の完成を最初の停止点とし、取り込みの後に IC-1 以降の段 0 へ。

## 2. 規則（B3・OE-W1 と同じ）

- 検査：静的な import・層・衝突 → 対象ビルド → 保存比較（v3b、未説明 0）→ 引用・タグの再照合（欠落・余分 0）→ root → 正式な全監査 → verify。直せない移動は取り下げて元の場所に残し、記録して進む。
- 置き場所は対応表（`research/kerodon-coverage`・`htt-coverage`・`ha-coverage`）の番号に合わせる。番号が付かない補助は、それを使う項目の節へ。
- 文献の属性（`@[cite …]`・`@[kerodon …]`）は対応表で own・partial に当たるものに付ける（Kerodon の partial は付けない）。docstring の出典の番号は概要か方針の側に。**略号表（`Util/Citation.lean`）は変えない**（変えると全体の再ビルド、BR54）。
- 他のレーン：③-a（`InfinityCategories/Sheaves/`、枝のみ）、⑥（`AlgebraicGeometry/`、KST を import しているか段 0 で確かめる）、一括（`BhattScholze/Prismatic/HodgeTate/`）、`blueprint/kerodon`（枝 `docs/kerodon-blueprint`）。動かす宣言を他の枝が使っていれば影響の一覧と改名表に入れる（B4 の資料）。
- ビルドは共有の鍵 `--class bulk`。昼は 3〜5 分の塊、適用と全体の再ビルド・全監査・verify は夜。
- 凍結は短く：適用の直前に調整役に一行で知らせ、調整役はその間、動かす範囲に触る取り込みを止める。

## 3. 止め方

- 各束の段 0（紙）：移動・改名の表、層の検査の見込み、他のレーンへの影響、所要時間。**条件付きの事前承認**：束が §1 の範囲に収まり、他のレーンの枝への影響が 30 ファイル以下なら、報告して止まらずに準備・適用へ。超えるか範囲の外が要るときは止まって報告。
- 各束の完成が停止点。完了の報告（結果の表、取り下げ、B4 の資料）をコミットし、調整役が取り込む。取り込みの後、次の束の段 0 へ止まらずに進む。
- 報告は `report-infinity-consolidation.md`（新設）に。区切りごとに「一覧：済み n／全体 m（うち追加 k）」（束と、その中の移動の単位を ID に）。
