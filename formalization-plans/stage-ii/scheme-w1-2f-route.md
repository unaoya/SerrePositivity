# SC-W1 段 2f：実装前の段取り

2026-11-12、2e の停止点前。調整役の依頼による紙の計画であり、以下の新しい宣言名・型は案。2e の検収も、2f の実装完了も主張しない。ビルド・監査の停止中に作成した。

## 1. 原典と今回の範囲

[BST13 v3 §3, Lemmas 3.5–3.9](https://arxiv.org/pdf/1307.3763v3#page=12) を確認した。3.5 は O_perf の普遍同相に関する不変性、3.6 は幾何学的連結なファイバーを持つ固有全射の場合、3.7 は有限全射に付随する関係の商、3.8 は有限射の補集合四角形、3.9 は固有射の四角形を述べる。3.9 の原文は Nisnevich コホモロジーの導来大域切断であり、その証明は正次数の比較と次数零の短完全列に分かれる。原典の 3.6 と 3.9 の次数零の証明は Stein 分解を使う。

このレーンでは、承認済みの `scheme-w1.md` §8–§9 に従う。射影の場合の **Čech 版**を構成し、一般の固有射の有限性・Stein 分解・代数空間の商は追加しない。3.6 の一般形と 3.7 の商の存在を別に完成させる計画ではない。有限射の部分は代数的な導手と Frobenius の計算で処理し、射影版 3.9 の次数零へ直接渡す。

[BS17 v3 Lemma 4.6(i)](https://arxiv.org/pdf/1507.06490#page=16) の原文は fppf の導来大域切断。今回の出口は、その証明で必要な構造層の四角形の Čech 版で、2g の射影的な細分の経路へ渡す。Nisnevich・fppf の導来コホモロジーとの比較を作ったとは言わない。最終出力 `SerrePositivity.Cech.AugmentedRingCechExact` は変えない。

## 2. 記号と型の入口

p は素数、A は Noether な F_p 代数、I は A のイデアル。Y→Spec A は射影的な全射で、V(I) の外で同型。E は I による実際の閉厚化（底変換）。有限な標準アフィン被覆 U の構造層の全タプル Čech 複体を C(Y)、E の誘導被覆を C(E) と書く。実装では 2e の `fullCechComplex` と実際の閉厚化の図式を使う。被覆の変更は §9 の比較を通す。

Frobenius は A 線形とは限らないので、Frobenius の順極限はまず加法群とその複体の圏で取る。`PerfAdd(A)` は加法群としての A の p 乗写像の順極限、`Cperf(Y)` は実際の Čech Frobenius による C(Y) の順極限を表す仮の記号。d=0 なら Frobenius は同じ捻りを保つ。一般の捻りも必要なら、段 n の捻りを p^n*d とする。

**`Perfection A p` は使わない。** Mathlib の `RingTheory/Perfection.lean` の `Perfection` は Frobenius の逆極限。`FieldTheory/PerfectClosure.lean` の `PerfectClosure` が順方向の構成を供給する。既存の `SerrePositivity.perfectionRootHom` と `perfectionRootHom_apply` は後者への入口。ただし Mathlib の `PerfectClosure` の標数の型クラスは零環の場合にそのまま使えない。空の標準開・空の E を除外せず、`(p:A)=0` から作る冪の環準同型の順極限を基本とし、非自明な標数 p の場合に `PerfectClosure` と同定して再利用する。

## 3. 主張の型の案と実装順

以下の `PerfAdd`・`Cperf`・`H` は上の意味の仕様記法で、未定義の Lean 定数を本体へ追加したものではない。実際の宣言では、環準同型・加法群の射・余鎖写像を引数から構成し、任意の「比較同型がある」という仮定を結論の代わりに置かない。

| 順番・宣言名の案 | 型・主張の案 | 入力を作る道 |
|---|---|---|
| F0 `frobeniusColimit_eq_zero_iff` | 段 n の元の像が順極限で零であることと、ある先の Frobenius 反復で零になることの同値。 | 加法群の filtered colimit の元の表示と零判定。環でも同じ表示と乗法を照合する。 |
| F1 `operf_nilThickening_bijective` | 冪零イデアル J に対し、実際の A→A/J が誘導する `PerfAdd(A)→PerfAdd(A/J)` の全単射。 | 十分高い p 冪が J を消すこと。指数は元ごとのものから始め、有限性がある箇所だけ一様化。 |
| F2 `operf_universalHomeomorphism_bijective` | 普遍同相な環準同型 f による順極限の写像が全単射。 | 既存の `isUniversalHomeomorphism_iff_charP` の nil な核と p 冪の像による判定を使用。スキーム版はアフィン開と共通細分から貼る。 |
| F3 `finite_modification_perfect_exact` | 有限な A→B が Spec 上全射で I の外で同型なら、`PerfAdd(A)→PerfAdd(B)×PerfAdd(A/I)→PerfAdd(B/IB)` は、最初が単射、真ん中で完全、最後が全射。後の射は二つの制限の差。 | 下記の導手の計算。Kollár の商は作らない。 |
| F4 `projectiveCechH0Ring_equiv` | 実際のアフィン標準開の切断の equalizer 部分環 B_Y の加法群と `H⁰(C(Y))` の自然な同型。 | 次数零の cycles と H⁰ の比較。元の各標準開環から乗法を入れ、単に H⁰ に任意の環構造を載せない。 |
| F5 `projectiveCechSupport_power_annihilates` | q>0 に対して、ある N が存在し `I^N • H^q(C(Y))=0`。また B_Y/im(A) も I の冪で消える。 | 2e の有限性・flat な主開への底変換、I の外で同型であること、有限加群の台と零化イデアルの比較。 |
| F6 `projectivePerfCech_closedRestriction_bijective` | q>0 に対し、実際の制限 `H^q(Cperf(Y))→H^q(Cperf(E))` は全単射。 | 2e の核の評価・像の安定化と、実際の Frobenius が厚化を経由する式。 |
| F7 `projectivePerfCechH0_square_exact` | `PerfAdd(A)→H⁰(Cperf(Y))×PerfAdd(A/I)→H⁰(Cperf(E))` の短完全性。 | F3–F4 と 2e の次数零の比較。Stein 分解は使わない。 |
| F8 `projectivePerfCech_blowupSquare_acyclic` | 上の可換四角形から作る明示的な増大全複体の acyclicity。 | F6・F7 と affine の正次数の消滅。2g が各 Čech ファイバー冪へ適用できる、射に自然な形で出す。 |

### 有限射の導手による計算（F3）

A→B の核は nil なので順極限で消える。B/im(A) は有限で I の外で零だから、ある m について I^m B⊆im(A)。さらに Spec 上の全射性から、IB の根基の A への逆像は I の根基である。

B と A/I の元が B/IB で一致する場合、有限段へ戻して代表をそろえる。十分高い p 冪を取ると差は I^m B に入り、A に持ち上がる。その持ち上げが I に属することを直ちに仮定してはいけない。上の根基の逆像の等式を使い、さらに Frobenius の反復を取って I に入れる。この追加の反復まで含めて真ん中の完全性を示す。最後の全射性は B→B/IB の全射性と順極限、最初の単射性は nil な核の零判定から得る。

`SerrePositivity.CommutativeAlgebra.UniversalHomeomorphism.Basic` の p 冪による普遍同相判定と `PowerClosure` の導手の定義を調べて再利用する。完全環の弱正規性の一般理論を別に作る必要があるかは、この有限射の四角形で不足が出たときだけ検討する。

### 正次数の計算（F6）

2e の核の評価と F5 を合わせ、十分厚い段への制限を単射にする。固定した厚化 n について、Frobenius の高い反復は n→p^e*n の厚化を経由し、2e の像の安定化から元の Y のコホモロジーの像へ入る。この二つの式で、順極限上の制限を単射かつ全射にする。厚化 n と 1 の順極限の一致は F1 の複体版と整合させる。

Rees 次数 i→i+r の作用と、固定した H^q(I^i O_Y) の A 加群の作用を区別する。高い I の作用が零であることだけから H^q(I^n O_Y) 自体の消滅は導かない。2e の実際の次数移動の API と核・像の評価を使う。

### 次数零の計算（F7）

B_Y=H⁰ の equalizer 部分環は 2e の射影有限性により A 上有限。F5 により中心外で A と同じで、Y→Spec A の全射性から A→B_Y の核は nil。2e の核の評価・像の安定化を q=0 で使い、B_Y/IB_Y と E の Čech H⁰ の Frobenius 順極限を、実際の制限の写像で比較する。この比較と F3 の有限射の四角形を合わせる。

具体的には D=H⁰(E) とし、u_n:B_Y→H⁰(Y/IⁿO_Y) を実際の制限とする。u_1 は IB_Y を消すので φ:B_Y/IB_Y→D を誘導する。

- 核：b∈ker(u_1) なら、Frobenius と厚化の自然性から b^(p^e)∈ker(u_(p^e))。核の評価の定数を c とし、p^e≥c+1 と選べば、この元は IB_Y に入る。したがって ker(φ) は nil。
- 像：像の安定化を n=1 に適用し、ある m について im(H⁰(Y/I^mO_Y)→D)=im(u_1)。p^e≥m を選べば D の e 回の Frobenius は H⁰(Y/I^mO_Y) を経由するため、任意の y∈D の y^(p^e) が im(u_1) に入る。

この二条件から、既存の p 冪による判定で φ は普遍同相となり、F2 でその Frobenius 順極限の写像は全単射になる。H⁰(Y) 自体が I の冪で消えるとは仮定していない。必要なのは quotient B_Y/IB_Y での核の零化である。

これは証明案であり、Frobenius の因子分解と環としての H⁰ の照合はまだ形式化していない。ここは重要な実装ゲートで、単に I 進完備化の同型を Frobenius 順極限の同型と読み替えない。必要な評価を実際の 2e の出力へつなげられなければ、その時点で報告する。

## 4. 2e から使う宣言と不足する接続

| 2e の既存宣言／作業中の入口 | 2f での用途 | まだ必要な接続 |
|---|---|---|
| `projectiveNatGradedFullCechHomology_finite` | F5 の有限生成性、H⁰ の有限性。 | 構造層の次数付き環と equalizer 部分環への同定。 |
| `projectiveCechFlatBaseChangeIso`、作業中の実際の標準開との比較 | I の外への局所化とコホモロジーの照合。 | 主開での幾何学的同型から実際の Čech 複体の縮約、台から I 冪による零化。 |
| `reesAdicProjectiveClosedCechProjection_shifted_kernel_bound` | F6 の十分厚い商への単射性。 | F5 と `formalFunctions_eventually_injective_of_kernel_bound` の適用。 |
| `reesAdicProjectiveClosedCechTransition_range_stabilizes` | F6 の Frobenius の像を元の像へ戻す。 | n→p^e*n の実際の厚化の因子分解。 |
| `reesAdicProjectiveClosedCechCompletionLinearEquiv` | 必要な形式関数の canonical map、q=0 の完備化比較。 | 順極限との交換を仮定せず、Frobenius の別の評価を供給する。 |
| `reesClosedCoefficientAdicCechIso_module_naturality`、`reesClosedCoefficientAdicCechFormalFunctions_module_naturality` | R/J の係数表示、商と遷移の写像の照合。 | 新しい Frobenius の実際の商写像との可換性。 |
| §9 の共通アフィン細分・filtered colimit | Cperf と各段 H の交換、被覆によらない出力。 | 2e 停止点で具体的な宣言と検証結果を確定する。 |

## 5. 束と規模の見込み

2e の検収後、F0–F3 の加法群・環の計算から始める。F4–F5 の幾何学との接続を次の束とし、その後 F6、最後に F7–F8。各束で触った対象と直接 importer のビルド、別実行の監査を通し、`math/scheme` にコミットする。新しいファイルは `AlgebraicGeometry/`、必要な alias は `deprecated_alias_util`。KST・BhattScholze・∞ の側は import しない。

| 束 | 主要な新規補題の概数 | Lean の概算行数 |
|---|---:|---:|
| Frobenius 順極限・nil 不変性・普遍同相 | 10–20 | 400–1,200 |
| 有限射の導手・完全な四角形 | 10–20 | 500–1,500 |
| H⁰ の環と台・零化の幾何学的接続 | 10–25 | 700–2,000 |
| 正次数の Frobenius 順極限の比較 | 8–18 | 500–1,500 |
| H⁰ の四角形・複体の出力・自然性 | 12–25 | 900–2,800 |
| 合計 | 約 50–110 | 約 3,000–9,000 |

前の 2d 報告の概算 2,000–7,000 行より幅を増やした。H⁰ の実際の環、空の E を含む順極限の入口、2e の出力を幾何学の台へ接続する部分を明示したため。2e で作る Frobenius・共通細分・filtered colimit の比較は、この数に二重計上しない。一般の固有射・Stein 分解・代数空間の商はこの見積もりに含めない。

## 6. 2f 停止点の検収項目

- F6・F7 を、実際の射影的な中心の四角形とその基底変更へ適用できること。
- 共通細分、R/J 表示、Frobenius 順極限と写像の自然性が、2e の既存の比較と一致すること。
- Nil な核を単に零と置かず、空の標準開・空の中心も落とさないこと。
- 原典の H_Nis、H_fppf の代わりに途中で使うものが Čech 版であると名前と docstring で示すこと。導来関手との比較を形式化したとは記さないこと。
- 2g の二重 Čech の判定には B1 を再利用し、最終出力の `AugmentedRingCechExact` を変えないこと。
- 各宣言と主張の一覧、対象ビルドと監査、未完の一般化を報告すること。


## 11-13 夜：F0〜F2 と F3 の有限段の入口

2e の数学 `bf9767cdc` と停止点報告 `6a9625b10` をコミットし、夜の指示どおり取り込みを待たずに 2f を開始した。今回の数学コミットは `be62984ff`。

F0 は有限段の元の零判定を構成し、その像が零であることと元の冪零性の同値を証明した。実際の環準同型が誘導する順極限の射について、有限段の評価、恒等射・合成の保存、nil な核による単射性、p 冪の像による全射性を示した。F1 は nil イデアルによる商の不変性、F2 は既存の普遍同相の p 冪の判定を使う環の不変性まで通った。零環を除外せず、Mathlib の逆極限 Perfection は使わない。

**F3 は未完。** `conductorSquare_lift` は導手に含まれるイデアルを入力して商の四角形の有限段の持ち上げを供給し、`conductorSquare_kernel` は左の核を同定する。有限射の中心外の同型から I の冪を導手に入れる段、Spec 全射性による根基の逆像の照合、Frobenius 順極限の四角形の完全性への接続は続ける。条件付きの有限段の持ち上げを、有限射の完全な降下の完成とは数えない。数学的な行き詰まり・型や範囲の変更の判断は今のところない。

- 新規 4 モジュール・22 件の名前付き数学宣言・284 行、入口込み 288 行。
- 対象と直接 importer `SerrePositivity.AlgebraicGeometry`：**4,550 jobs 成功**。
- 別実行の監査：**8,654 宣言・標準三公理のみ**。
- 共有鍵 `--wait 3600` は一回のビルド・監査の実行中のみ。重複の整理券なし。既存の宣言の変更、sorry・admit・新規公理・計算量上限の引き上げなし。
- 累計 284 行は報告点 4,500 行・停止基準 18,000 行より小さい。2e の本体や文書・下書きは 2f に二重計上しない。

| 宣言 | 主張 |
| --- | --- |
| `frobeniusDirectSystemMap` | 自然数段の間の、実際の Frobenius の反復。 |
| `frobeniusDirectSystem` | Frobenius の反復の有向系の法則。 |
| `frobeniusDirectSystemMap_apply` | Frobenius の反復の値は p の冪乗である。 |
| `FrobeniusDirectLimit` | Frobenius 順極限の環。零環でも同じ構成を使う。 |
| `frobeniusDirectLimitOf` | 有限段から Frobenius 順極限への環準同型。 |
| `frobeniusDirectLimitOf_eq_zero_iff` | 有限段の元が零になるのは、ある先の p 乗反復で零になる場合に限る。 |
| `frobeniusDirectLimitOf_eq_iff` | 有限段の二つの元の像は、Frobenius を十分反復して一致する場合に限り等しい。 |
| `frobeniusDirectLimitOf_eq_zero_iff_nilpotent` | 有限段の元は、その元が冪零である場合に限って Frobenius 順極限で零になる。 |
| `frobeniusDirectSystemMap_naturality` | 環の射は各段の Frobenius の反復と可換。 |
| `frobeniusDirectLimitMap` | 実際の環の射が誘導する Frobenius 順極限の環準同型。 |
| `frobeniusDirectLimitMap_of` | 順極限の射を有限段の元で評価する公式。 |
| `frobeniusDirectLimitMap_injective` | 核が nil である環の射は、Frobenius 順極限上で単射になる。 |
| `frobeniusDirectLimitMap_surjective` | 各元のある p 冪が像にある環の射は、Frobenius 順極限上で全射になる。 |
| `frobeniusDirectLimitMap_comp` | Frobenius 順極限の射は環準同型の合成を保つ。 |
| `frobeniusDirectLimitMap_id` | Frobenius 順極限の射は恒等射を保つ。 |
| `frobeniusQuotientPrimeCast` | p が零であることは、零環になる商にも保たれる。 |
| `frobeniusDirectLimitQuotient_bijective` | nil イデアルによる商の実際の射は Frobenius 順極限上で全単射。 |
| `frobeniusDirectLimitQuotientEquiv` | nil イデアルによる商と元の環の Frobenius 順極限の canonical な環同型。 |
| `frobeniusDirectLimitUniversalHomeomorphism_bijective` | 普遍同相な環準同型は Frobenius 順極限上で全単射。 |
| `frobeniusDirectLimitUniversalHomeomorphismEquiv` | 普遍同相が誘導する Frobenius 順極限の canonical な環同型。 |
| `conductorSquare_lift` | 導手に含まれるイデアルの商で一致する元は、元の環の同じ元から来る。 |
| `conductorSquare_kernel` | 導手の四角形の左の射の核は、元の環準同型の核と同じ。 |


## F3 途中：順極限の四角形の持ち上げ（e69c7065f）

新規 `FrobeniusSquareLift`、2 宣言・78 行。2f 累計 5 本・362 行（入口込み 367 行）。対象と直接 importer は 4,551 jobs 成功、別実行の監査は 8,656 宣言・標準三公理のみ。共有鍵 `--wait 3600` を各実行中だけ取得した。

| 宣言 | 主張 |
| --- | --- |
| `frobeniusSquare_lift_same_stage` | 同じ段の元の順極限での一致を後続段の一致へ戻し、有限段の持ち上げから順極限での持ち上げを得る。 |
| `frobeniusSquare_lift` | 任意の二つの順極限の元を共通有限段へ移し、環の四角形の持ち上げ可能性を Frobenius 順極限へ移す。 |

F3 全体は未完。有限段の持ち上げを入力する一般補題までであり、導手の具体的な商の四角形への適用、有限射の中心外の同型からの導手の冪の評価、根基の逆像を使った中心の商との比較を続ける。数学的な行き詰まりや範囲変更はない。
