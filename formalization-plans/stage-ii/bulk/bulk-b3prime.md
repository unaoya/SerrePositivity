# 一括レーン B3′：BS の本体に限った二度目の移動・改名

作成：2026-11-14 夜（調整役）。決定：ユーザー（11-14「B3′ の指示を出してください」）。順序は B3′ → 5∞-3a → 5∞-7a → 5∞-8c → B5 → B6 → 保守の束（`stage-ii-second-half.md` §7 の後の相談）。

## 0. 目標と理由

`refactor-ledger.md` §7 の §7・§8・§10 の見直しで「B3′」とした移動・改名・docstring を、BS の本体の上で行い、取り込める枝として出す。⑤∞ の古典の段（5∞-3a・5∞-7a・5∞-8c）が BS の本体にファイルを置き始める前に済ませ、⑤∞ に B4 を要らなくする。動くのはほぼ BS の本体（Semiperfectoid・Perfectoidization・Almost・Prismatic・Andre）と、その少数の一般の部品の行き先（CommutativeAlgebra・HomologicalAlgebra・Kerodon）。

## 1. 範囲（承認済み。ここに書いたことは確認なしで進めてよい）

`refactor-ledger.md` §7 の表で扱いが「B3′」のもの：
1. **§7（semiperfectoid）**：R7-3 (a)（`MonicRelation` と OrdinaryRoots/Family の多項式の補題を `CommutativeAlgebra/KoszulRegular` へ。BR26′ の一件も解く）、R7-3 (b)（§7.2 → André の内部の 8 辺の汎用の宣言を CompletelyFlat・DerivedCompletion・Delta/Division へ）、R7-3 (c)（`PowerRootPolynomial` を CommutativeAlgebra か Semiperfectoid/RootFamilies へ）、R7-3 (d)（`exists_boundedPerfectPrismPresentation` を Prism/Perfectoid へ）、R7-4（Semiperfectoid を Discrete・Lci・Quasiregular・Perfection・Surjectivity に分ける。`Cotangent/` は作らない）、R7-5（名前空間）、R7-6 (c)（root から届かない 9 本：Audit 4 本は BR14 で scripts/ へ、残りは root に足すか archive か、理由を書いて決める）、R7-7 の残り（「（旧 パス）」の節見出し、存在しないパス 9 件、決まり文句）。
2. **§8（perfection）**：R8-1（`TheoryInterface` を `BhattScholze/Perfectoidization/Interface/` へ。EInfinity → BS の逆向きの import 2 本を解く。CAlg_R 版 3 本の削除はしない＝保守）、**R8-2（Derived/Interface の Setup・Completion の節を環のモジュールへ切り出す。B3′ の最初に）**、R8-3（IntegralExistence を InitialLimit・InitialBridge・存在の三つに分けて、それぞれの行き先へ）、R8-4 の B3′ の分（`SerrePositivity/Inputs/Perfectoidization.lean` を消し、Finite.lean は BS の版を直接呼ぶ）、R8-7（TensorCompatibility を集約に足して公開、BR23）、R8-8（`Derived/` を `Interface/` に、RootAdjunction を Construction か Arc/Site へ、drafts の「将来の置き場所」の欄の書き直し、FiniteProduct を Prism/Perfectoid へ）、R8-9（docstring の工程ラベル・旧・古い記述）。
3. **§10（almost）**：R10-3（名前の紛らわしさ、BR43 の改名）、R10-5 (a)（SupportedQuotient を ExcisionTor の隣へ）、(b)（`mul_eq_zero_of_pow_mul_eq_zero_of_reduced` を CommutativeAlgebra へ）、(d)（`Perfectoidization/CompletedTensor` の §10 の芯を Almost/ へ切り出すか docstring に明記）、(f)(g)（名前空間、配置案への意見の反映）、R10-7 の残り。
4. **B3 で入れるはずだった項目の残り**：台帳で扱いが「B3」なのに B3 で行われなかったもの（B3 の完了報告の「維持・保留の一覧」と照らす）。BS の逆向き 34 辺のうち、上の移動で解けるもの。

**入れないもの**：保守の項目（BR21・BR22・BR24・BR39 の A9 の分・BR49・BR51・BR53、CAlg_R 版 3 本の削除、未使用の宣言の削除）、R83（Spectrum）、R21 の広い案、数学の主張・証明の変更。

## 2. 作業場所と規則

- 枝 `bulk/b3prime` を main から切る。基準の main を報告に書く。
- **他のレーンの持ち分**：⑤a・⑤d の `EInfinity/`（R8-1 で動かす `EInfinity/Perfectoidization/TheoryInterface` と、それを import する所は除く）、③ の `InfinityCategories/`（R7-3 などで Kerodon に置く一般の部品の新しいファイルは可）、⑥ の `AlgebraicGeometry/`、drafts の ⑤a の P⁰ の部分。動かす宣言を他のレーンの枝が使っていれば、B4 の資料（改名表と影響の一覧）に入れる。
- B3 と同じ検査：静的な import・層・衝突 → 対象ビルド → 保存比較（v3b、未説明 0）→ 引用・タグの再照合（欠落・余分 0）→ root → 正式な全監査 → verify。比較を弱めない。直せない移動は取り下げて元の場所に残し、記録して進む。
- ビルドは共有の鍵 `--class bulk`。昼は 3〜5 分の塊、verify・全監査は夜。
- **凍結は短く**：準備（表・束・プレビュー・対象ビルド・保存比較）は基準の main の上で進める。適用の直前に調整役に「適用に入る」と一行で知らせ、調整役はそこから取り込みまで BS の本体に触る取り込みを止める（BS に触らないレーンの取り込みは続ける。その増分は B3 と同じく採取し直す）。

## 3. 進め方

1. **段 0（紙）**：§1 の各項目の移動・改名の表（元のパス → 新しいパス、旧名 → 新名、件数）、層の検査の見込み、他のレーンへの影響の一覧、所要時間の見込み。**条件付きの事前承認**：§1 の範囲に収まり、他のレーンの枝への影響（文字列一致）が合計 30 ファイル以下なら、報告して止まらずに準備へ。超えるか範囲の外が要るときは止まって報告。
2. 準備 → 適用 → 検査（§2 の順）。
3. **B3′ の完成が停止点**：完了の報告（B3 と同じ形：結果の表、取り下げ、B4 の資料）を書き、調整役が取り込む。その後、止まらずに 5∞-3a の段 0（紙）へ。

## 4. 報告

`report-bulk-w1.md` に節を足して自分の枝にコミットする。区切りごとに「一覧：済み n／全体 m（うち追加 k）」（§1 の項目を ID にする）。

## 5. 追記（2026-11-14 夜、調整役）：R8-1 の保護例外を広げる

`bulk-b3prime/r8-1-scope-decision.json`（1d8e96aab）を受けて。EInfinity → BS の二本目の辺を解くため、`EInfinity/Perfectoidization` の CAlg_R 版の三本（Comparison・Interface・DerivedCorollary、計 255 行）も保護の例外に含め、**削除せずに BS の側へ機械的に移す**（宣言名・型・証明を保つ、保存比較で未説明 0）。削除は保守のまま（R8-1）。⑤a・⑤d の枝が三本を使っていれば B4 の影響一覧に入れる。
