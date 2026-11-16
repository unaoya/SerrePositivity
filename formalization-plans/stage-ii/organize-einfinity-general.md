# 整理 OE-W1：EInfinity の一般の部分を外へ、D81 で止めた BE の道をまとめる（③-b）

作成：2026-11-16（調整役）。決定：ユーザー（11-16「取り込んでコードの整理をしたい」「案通りでok」）。担当：③-b（IS-W2 のチャット、3b-4 は D81 で停止）。

## 0. 目標と理由

D81（CAlg は HA 流）で `EInfinity/` は「BE の模型」の意味になった。ところが `EInfinity/` には BE と無関係な一般の ∞ 圏論・ホモトピー論（`HomotopyWeight`・`FrameHom`・`SimplicialLocalization`・`Hammock` など）が多く、台帳の R83 で「保守」として残していた。後で参照しやすいように：
1. 一般の部分を `InfinityCategories/`（Kerodon・HTT・HA の配置、`kerodon-layout` の規則）か `HomotopicalAlgebra/`・`HomologicalAlgebra/` へ移す。
2. D81 で止めた BE の道（3b-4 の 99 本 `EInfinity/BarrattEccles/` の Tot の比較、⑤d の `InfinityCategories/HA/Monads/` の BE への適用の部分）を、止めた道と分かる形にまとめる（ディレクトリと docstring の状態の一行）。
3. 目録を書く（⑤d の `research/g12-monad-route/README.md` と同じ形）。

## 1. 範囲

- **段 1（先に適用）**：3b-4 で入った 274 本（main 49967c102）と、その周りで同じ話題の既存のファイル（`EInfinity/HomotopyWeight`・`FrameHom`・`SimplicialLocalization` の全体）。⑤d の `HA/Monads/` は置き場所の検討だけ（一般の部分は HA 4.7・Riehl–Verity の節へ移すか、そのままか）。
- **段 2（紙だけ、適用は後で決める）**：`EInfinity/` の残り全体（BarrattEccles・Interface・PowerOperation・Modules を除く約 2,600 本）を、一般／BE 固有／E∞ の一般論（HA の道でも残るもの）に分けた表。
- 入れないもの：主張・証明の変更、宣言の削除、⑤a の界面 `EInfinity/Interface/` の型の変更、BS の本体、drafts。

## 2. 作業場所と規則

- main（49967c102 以降）から枝 `refactor/organize-einfinity` を切る。基準の main を報告に書く。
- 他のレーン：③-a（`InfinityCategories/Sheaves/`、枝のみ）、一括（BS の HT、`BhattScholze/Prismatic/HodgeTate/`）、⑥（`AlgebraicGeometry/`）。移す宣言を他のレーンの枝が使っていれば影響の一覧と改名表に入れる（B4 の資料）。
- 検査は B3 と同じ：静的な import・層・衝突 → 対象ビルド → 保存比較（v3b、未説明 0）→ 引用・タグの再照合（欠落・余分 0）→ root → 正式な全監査 → verify。直せない移動は取り下げて元の場所に残し、記録して進む。
- 移す宣言には、対応表で own・partial に当たるものに文献の属性（`@[cite …]`・`@[kerodon …]`、`citation-attributes.md`）を付ける。docstring の出典の番号は概要か方針の側に。
- ビルドは共有の鍵 `--class bulk`。昼は 3〜5 分の塊、verify・全監査は夜。

## 3. 進め方と止め方

1. **段 0（紙）**：段 1 の移動・改名の表（元のパス → 新しいパス、旧名 → 新名、件数）、層の検査の見込み、他のレーンへの影響、所要時間。段 2 の分類表。目録の構成案。**条件付きの事前承認**：段 1 が §1 の範囲に収まり、他のレーンの枝への影響（文字列一致）が 30 ファイル以下なら、報告して止まらずに準備・適用へ。超えるか範囲の外が要るときは止まって報告。
2. 段 1 の準備 → 適用 → 検査（§2 の順）→ 目録。**段 1 の完成が停止点**（完了の報告：結果の表、取り下げ、B4 の資料、目録）。調整役が取り込む。
3. 段 2 は段 0 の表を見てユーザーと決める。

## 4. 報告

`report-organize-einfinity.md` を新設して自分の枝にコミット。区切りごとに「一覧：済み n／全体 m（うち追加 k）」（段 1 の移動の束を ID にする）。

## 追記（2026-11-16 夜、調整役）：新しいチャットへ引き継ぐ

③-b のチャットが不調なので、OE-W1 は新しいチャット（レーン ⑦）が `infinity-consolidation-w1.md` の IC-0 として引き継ぐ（ユーザー 11-16）。枝 `refactor/organize-einfinity`（d216f410b）と作業木 `SerrePositivity-bs-d68` をそのまま使う。③-b のチャットはここで止める。
