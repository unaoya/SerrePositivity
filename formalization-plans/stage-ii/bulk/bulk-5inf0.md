# 一括レーン：5∞-0（⑤∞ の準備）の指示

作成：2026-11-14（調整役）。決定：ユーザー（11-14「案通りでok」：KL-W1 は B4 の支援をしながら 5∞-0、その後 B5、時機を見て B3′。⑤∞ の数学の段は 5∞-0 の後に新しいチャットで）。

## 0. 目標

⑤∞（BS の ∞ 側、`stage-ii-second-half.md` の 5∞-1 以降）が古い drafts の上に積まないように、drafts を本体の宣言を指す形に整え、⑤∞ の前提になる小さな定義・補題を本体に入れる。完成したら単独で main に取り込む。

## 1. 作業場所と規則

- 枝 `bulk/5inf-0` を main（7a3640cb9 以降）から切る。worktree は今の一括レーンのもの（`SerrePositivity-kerodon-layout`）を使ってよい。
- **B4 の支援を優先**：各レーンから B4 の採取・保留の問い合わせが来たら先に答える。
- ビルドは共有の鍵 `--class bulk`（B3 の鍵免除はこの回は使わない）。昼は 3〜5 分の塊、夜は 30 分以内。
- 他のレーンの持ち分に触れない：⑤a の `drafts/Shared/EInfinityPowerOperation.lean`・`drafts/A4` の P⁰ の部分（D79 の改訂、⑤a の M14 が使う）、⑤a・⑤d の `EInfinity/` のファイル、③ の `InfinityCategories/`、⑥ の `AlgebraicGeometry/`。
- 原典どおり（定義は変えない）。docstring は README の Conventions（原典の番号を引く、ノートを引かない）。
- **型つきの一覧で止める**（`coordination.md` §2、11-14）：既存の構成の法則の補題と証明の分割は数を決めない。止まって報告するのは、新しい構成・新しい定理（下の §2 の B に挙げたもの以外）、範囲の外、外枠に届くとき。報告のたびに「一覧：済み n／全体 m（うち追加 k）」。

## 2. 範囲（`refactor-ledger.md` §7・§8 で「5∞-0」としたもの）

**A. drafts の整理（数学を増やさない）**
1. R4-1・R5-1：drafts/A0・A1（CrystallineInput・CrystallineSite・DeRhamComparisonPoly・HodgeTateComparison）の古典的な部分を、本体の宣言を指す形に書き換え、重なる宣言を drafts から外す。
2. R7-1：drafts/A3（DiscreteCase・LciAndQuasiregular）を本体に寄せ（約 26 の sorry）、`EInfinityTheory` に移す（D71〜D73）。A1 の `prismaticCohomology_lci_universal` を A3 へ。
3. A2 の `Poly` を本体の `Prismatic.Poly` に。
4. R8-10・R8-1：drafts/A4〜A7・A9 の重複・同名・古い記述、Theory 版の界面への追従（`PerfectoidizationInterfaceCAlg`・`nonempty_e3_of_cAlg`・`IsDiscrete（Comparison）` の記述）。drafts/A4 の Not 8.1 を本体の Thm 3.10（`exists_boundedPerfectPrismPresentation`）から作る。⑤a の P⁰ の部分は触らない。
5. R10-4：drafts/A8 を本体を指す形に（同名 40）。
6. BR40・R5-4 (e)：Tor 振幅の定義と名前の重なりを本体の `HasCochainCompleteTorAmplitude` に一本化（drafts の側を寄せる）。
7. 各 drafts の冒頭の「基準コミット 972bb7f53」などの古い記述を今の main に。

**B. 本体に入れる小さな定義・補題（原典の項目）**
1. Def 3.2 の prism の圏（`Category` の instance）と平坦な射（`OrientedPrism.Hom.IsFlat`・`IsFaithfullyFlat`、site の定義をその略記に）。
2. Lemma 3.8 (1)(2) の名前つきの補題（`isBoundedPrism_of_perfect` など）。Lemma 3.5 後半の向き付きの構成子は既存の `OrientedPrism.ofDiscreteDelta` の向きを確かめ、足りなければ足す（R7-2 (c)）。
3. prismatic site の本質的小ささ（結晶 site の `CrystallineSiteSmall` と同じ証明。本体の `[EssentiallySmall …]` の仮定を外す）。
4. Rem 4.6 の定義（完全 prism の充満部分圏と誘導位相）。
5. 名前つきの述語：semiperfectoid、有界な p 冪ねじれ（R7-2 (b)、定義と基本の補題だけ。展開形の置き換えは保守）。
6. R5-2：Prop 6.2 (b) と Cor 5.5 の一般の結晶 prism（drafts の二つの sorry）を `hodgeTate_iso` の系に（入らなければ 5∞-3a に回して記録）。
7. R10-5 (c)：`InfinityCategories.Derived.IsConnectiveAt`（AlmostTensor:67）・`Perfectoidization.Derived.isPCompleteVertex`（AlmostConnectivity:138）を drafts と衝突しない一般の場所へ（名前の衝突の解消）。

## 3. 進め方

1. **段 0（紙、短く）**：A・B の各項目を型つきの一覧（ID つき）にし、見込みを出す。drafts の書き換えは対象ファイルと消す宣言の数、B は Lean の主張の型。**条件付きの事前承認**：見込みの上端が 6,000 行（drafts の書き換えを含む）以下なら、報告して止まらずに進む。超えるときは止まって報告。外枠は段 0 の上端の 2 倍。
2. 実装：A と B を並べて進めてよい。drafts の変更は drafts の型検査（既存の手順があればそれで、なければ一時ファイルで import して確かめる）を通す。本体の追加は対象ビルドと小さい監査（BS の stage II の監査の一覧への登録案を報告に）。
3. **5∞-0 の完成が停止点**：報告して単独で取り込む。その後は B5（属性から地図の生成）の段 0 へ。

## 4. 報告

`report-bulk-w1.md` に節を足して自分の枝にコミットする。区切りごとに一覧の進み、drafts の sorry の数の増減、本体に足した宣言、ビルドと監査の結果。

## 5. 追記（2026-11-14 午後、調整役）：drafts の import・改名の追従

B3・B4 は drafts を対象から外したので、drafts の古い import・名前は誰も追従していない。5∞-0 の範囲に **drafts 全体の import と B3 の改名への追従**を入れる（`bulk-w1-b3` の module-map・namespace-rewrite-map を使う、数学は変えない）。**例外**：⑤a の持ち分の `drafts/Shared/EInfinityPowerOperation.lean`・`drafts/A4` の P⁰ の部分も、**import 行と改名された完全名の機械的な書き換えだけ**はしてよい（例：存在しない `…Project.DerivedCategories.Homology` の import）。主張・証明・型は触らない。変えた行は報告に書き、⑤a に知らせる。
