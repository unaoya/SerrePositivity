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


## F3 途中：具体的な導手の四角形（03c26aea2）

新規 `FrobeniusConductorSquare`、2 宣言・49 行。2f 累計 6 本・411 行（入口込み 417 行）。対象と直接 importer は 4,552 jobs 成功、別実行の監査は 8,664 宣言・標準三公理のみ。共有鍵 `--wait 3600` を実行中だけ使用。

| 宣言 | 主張 |
| --- | --- |
| `frobeniusConductorSquare_lift` | 導手に含まれる K に対し、B と A/f⁻¹K の順極限で B/K 上一致する元は、A の順極限から同時に持ち上がる。 |
| `frobeniusConductorSquare_quotient_surjective` | B→B/K は Frobenius 順極限上で全射。 |

未完：有限射の中心外の同型から I の冪が導手に入る評価、根基の逆像との照合、F3 の指定した中心の四角形、F4〜F8。次の材料として Mathlib `Module.support_eq_zeroLocus`（有限加群の台と零化イデアル）を確認した。2f 全体の完成目標を維持し、この条件付きの四角形を停止点とはしない。


## F3・F5 途中：台から冪の評価（4403ddd9a）

新規 `FiniteSupportPower`、2 宣言・38 行。2f 累計 7 本・449 行（入口込み 456 行）。対象と直接 importer は 4,553 jobs 成功、別実行の監査は 8,666 宣言・標準三公理のみ。共有鍵 `--wait 3600` を各実行だけ取得した。

| 宣言 | 主張 |
| --- | --- |
| `finiteSupport_exists_pow_le_annihilator` | 有限加群の台が有限生成イデアル I の零点集合に含まれると、ある Iⁿ が加群を消す。 |
| `finiteQuotientSupport_exists_pow_smul_mem` | 有限加群 M の商 M/N の台が V(I) に含まれると、ある Iⁿ 倍の元はすべて N に入る。 |

次は N を有限環拡大の元の環の像として導手の冪の評価に接続する。中心外の同型から商加群の台の包含を供給する段と、根基の逆像、F4〜F8 は未完。2f 全体は完成扱いにしない。


## F3 途中：余核の台と導手（8fcd1ccaa）

新規 `FiniteSupportConductor`、2 宣言・43 行。2f 累計 8 本・492 行（入口込み 500 行）。対象と直接 importer は 4,554 jobs 成功、別実行の監査は 8,668 宣言・標準三公理のみ。共有鍵 `--wait 3600` を各実行中のみ取得。

| 宣言 | 主張 |
| --- | --- |
| `finiteSupport_exists_pow_map_le_conductor` | 有限環拡大の余核の台が V(I) に含まれれば、ある Iⁿ の拡大イデアルは元の環の像の導手に含まれる。 |
| `finiteSupport_exists_pow_map_lift` | その拡大イデアルの各元は元の環から来る。 |

次の接続は、中心外の同型から商加群の台の包含を供給すること、Spec 全射性から根基の逆像を照合すること。後者は各 I を含む素イデアルを Spec の全射性で持ち上げ、`Ideal.radical_eq_sInf` を使う道で進める。F3 全体と F4〜F8 は未完であり、2f の完成目標を維持する。

## F3 途中：局所化した余核と中心の根基（f15539df6）

新規 `SurjectiveSpectrumRadical`・`FrobeniusQuotientFactor`・`LocalizedCokernelSupport`、6 宣言・128 行。2f 累計 11 本・620 行（入口の import 込み 631 行）。対象と直接 importer は 4,557 jobs 成功、別実行の監査は 8,674 宣言・標準三公理のみ。共有鍵 `--wait 3600` を各実行中だけ取得した。

| 宣言 | 主張 |
| --- | --- |
| `surjectiveSpectrum_comap_radical_map` | Spec 上全射な環準同型では、拡大イデアルの根基の逆像は元のイデアルの根基。 |
| `surjectiveSpectrum_radical_comap_map` | 同じ仮定のもとで、拡大して戻したイデアルの根基は変わらない。 |
| `quotientFactor_kernel_nil` | I⊆J⊆√I なら、実際の商の因子写像 A/I→A/J の核は nil。 |
| `frobeniusQuotientFactor_bijective` | この因子写像が誘導する Frobenius 順極限の射は全単射。 |
| `cokernel_support_subset_of_localized_surjective` | V(I) の外で局所化した線形写像が全射なら、余核の台は V(I) に含まれる。 |
| `finiteLocalizedSurjective_exists_pow_map_lift` | 有限環拡大で上の局所全射性が成り立ち I が有限生成なら、ある IⁿB のすべての元は A から来る。 |

F3 はなお未完。次は導手の四角形を指定された中心 I の商の四角形へ移し、核の nil 性による左の単射性と合わせて短完全性をまとめる。局所化した線形写像の全射性を幾何学的な中心外の同型から供給する接続も、利用時に明示する。F4〜F8 の H⁰ の環、射影 Čech の台、厚化を経由する Frobenius、全複体への接続を引き続き行う。今回の条件付きの補題を有限変更の完全な定理または停止点 2f とは呼ばない。

## F3 途中：指定中心の四角形への移送（42d61a30b）

新規 4 本・7 宣言・221 行。2f 累計 15 本・841 行（入口の import 込み 856 行）。対象と直接 importer は 4,561 jobs 成功。別実行の監査は 8,681 宣言・標準三公理のみ。共有鍵 `--wait 3600` を実行ごとに取得して返却した。

| 宣言 | 主張 |
| --- | --- |
| `frobeniusPowerCenter_bijective` | 正の冪の商 A/Iⁿ→A/I は Frobenius 順極限で全単射。 |
| `surjectiveSpectrum_comap_map_pow_le_radical` | Spec 全射なら f⁻¹(IⁿB) は √(Iⁿ) に含まれる。 |
| `frobeniusContractedPowerCenter_bijective` | 実際の因子写像 A/Iⁿ→A/f⁻¹(IⁿB) は Frobenius 順極限で全単射。 |
| `squareLift_transport` | 共通対象からの単射・全射と右下の単射および可換性を使い、四角形の持ち上げを移送する。 |
| `frobeniusCenterSquare_lift` | Spec 全射かつ I の正の冪の拡大が像に入るなら、B と A/I の順極限で B/IB 上一致する元は A の順極限から同時に持ち上がる。 |
| `frobeniusDirectLimitMap_injective_of_surjectiveSpectrum` | Spec 全射な環準同型は、Frobenius 順極限で単射。 |
| `frobeniusFiniteModificationSquare_lift` | 有限環拡大で中心外の局所化した射が全射なら、導手の冪の存在を供給して指定中心の四角形での持ち上げを得る。 |

すべての辺は実際の環準同型・商の因子写像の誘導射である。A/Iⁿ を共通対象にし、B/IⁿB→B/IB の順極限での単射性で一致を反映する。これにより、持ち上げが直ちに I に入ると仮定する誤りを避け、根基の逆像との比較を明示した。

残り：F3 の加法群の短完全列としての取りまとめ、および利用側の幾何学的な中心外の同型との接続。F4〜F8（H⁰ の環、台、厚化を経由する Frobenius、全複体）は未完。停止点 2f ではない。

## F3：環の局所化の仮定のもとでの短完全列（5857eabc0）

新規 `FrobeniusFiniteModificationExact`、4 個の明示的宣言・79 行。2f 累計 16 本・920 行（入口の import 込み 936 行）。対象と直接 importer は 4,562 jobs 成功。別実行の監査は 8,714 宣言・標準三公理のみ（構造体の生成宣言も監査に含む）。共有鍵 `--wait 3600` を各実行中だけ使用。

| 宣言 | 主張 |
| --- | --- |
| `frobeniusCenterPair` | A の順極限から B と A/I の順極限への、二つの実際の制限を組にした加法写像。 |
| `frobeniusCenterDifference` | B と A/I の順極限から B/IB の順極限への、二つの実際の制限の差を取る加法写像。 |
| `frobeniusCenterDifference_pair` | この二つの加法写像の合成は零。 |
| `frobeniusFiniteModification_exact` | 有限環拡大で Spec 全射、I は有限生成、V(I) 外の局所化が全射なら、左が単射・真ん中で Function.Exact・右が全射。 |

F3 の環論の列は上の明示した局所化の仮定で閉じた。幾何学的な中心外の同型からこの仮定を供給する接続は、F4〜F5 の利用側と合わせて残る。F4 の入口として、通常の全タプル複体は次数 q に長さ q+1 のタプルを持つことを確認した。H⁰ の比較には `CochainComplex.isIso_homologyπ₀` と `ShortComplex.moduleCatCyclesIso` を使う下書きを `scheme-drafts/FullCechH0Kernel.lean` に置いた（未検証・未コミット）。空タプルの増大項との比較を H⁰ の比較と取り違えない。F4〜F8 は未完であり、停止点 2f ではない。

## F4 途中：H⁰ の核と適合する切断の部分環（6c18deb77）

新規 2 本・5 個の明示的宣言・83 行。2f 累計 18 本・1,003 行（入口の import 込み 1,021 行）。対象と直接 importer は 4,564 jobs 成功。別実行の監査は 8,734 宣言・標準三公理のみ。共有鍵 `--wait 3600` を実行ごとに取得・返却した。

| 宣言 | 主張 |
| --- | --- |
| `fullCechH0KernelIso` | 通常の全タプル Čech H⁰ は、長さ1の項から長さ2の項への実際の余境界の核と同型。 |
| `FullRingCechCochains` | 環係数の全タプルの切断族。 |
| `fullRingCechFace` | 二重点に対する片側の制限を、実際の制限から成る環準同型として構成。 |
| `fullRingCechEqualizer` | 二つの制限が一致する切断族を、成分ごとの乗法を持つ部分環として定義。 |
| `mem_fullRingCechEqualizer` | 部分環への所属と、各二重点での制限の一致の同値。 |

H⁰ の核の比較では、複体の next で決まる対象と長さ2の項を定義的に同じと仮定しない。`cyclesIsoSc' 0 0 1` で次数を明示し、余境界の等式が誘導する核の線形同型を合成した。docstring は Čech 版であることと未形式化の Stacks 30.2.6 の比較を明記する。

F4 は未完。部分環の加法群と上の核を同定し、実際の Proj の構造層の標準開に適用して有限性を移す。最初の余境界を二つの制限の差として計算する未検証下書きは `scheme-drafts/FullCechH0Compatible.lean` に置いた。F5〜F8 も残るため、停止点 2f ではない。

## F4 途中：切断の部分代数と Čech H⁰（2b58ad958）

新規 2 本・9 個の明示的宣言・107 行。2f 累計 20 本・1,110 行（入口の import 込み 1,130 行）。対象と直接 importer は 4,566 jobs 成功、別実行の監査は 8,755 宣言・標準三公理のみ。共有鍵 `--wait 3600` を各実行中のみ取得した。

| 宣言 | 主張 |
| --- | --- |
| `fullCechDifferential_one_apply` | 最初の実際の Čech 余境界の成分は二つの制限の差。 |
| `algebraCechRingDiagram` | 代数係数図式を元の環の図式として扱う。 |
| `algebraCechModuleDiagram` | 同じ代数係数図式を元の基底環上の加群の図式として扱う。 |
| `fullAlgebraCechCochainsAlgebra` | 全タプルの切断の代数構造は成分ごとの構造。 |
| `fullAlgebraCechFace` | 各面の制限を基底環上の代数準同型として扱う。 |
| `fullAlgebraCechEqualizer` | 二つの制限が一致する切断の部分代数。 |
| `fullAlgebraCechEqualizer_toSubmodule` | この部分代数の部分加群は、最初の実際の余境界の核。 |
| `fullAlgebraCechH0Equiv` | 切断の部分代数と通常の Čech H⁰ の線形同型。 |
| `fullAlgebraCechEqualizer_finite` | Čech H⁰ の有限性を実際の切断の部分代数へ移す。 |

環構造は成分ごとの切断の乗法を制限したものであり、H⁰ に任意の環構造を選んで載せていない。次はスキームの有限交叉の切断をこの CommAlgCat 図式に置き、既存の `schemeStructureCechPresheaf` とそのスカラー制限から来る加群図式を比較して、Proj の有限性を適用する。F4 のその接続、F5〜F8 は未完。停止点 2f ではない。

## F4：実際の構造層と Proj の切断代数の有限性（77b63fd80）

新規 2 本・7 個の明示的宣言・127 行。2f 累計 22 本・1,237 行（入口の import 込み 1,259 行）。対象と直接 importer は 4,568 jobs 成功。別実行の監査は 8,781 宣言・標準三公理のみ。共有鍵 `--wait 3600` を各実行中のみ取得。

| 宣言 | 主張 |
| --- | --- |
| `schemeSectionAlgebra` | 基底環から大域切断への写像を開集合へ制限した、実際の切断環の代数構造。 |
| `schemeSectionAlgebraPresheaf` | 構造層の実際の切断と制限を、基底環上の代数の前層にする。 |
| `schemeSectionAlgebraCechDiagram` | 有限交叉上の実際の切断代数の Čech 係数図式。 |
| `schemeSectionAlgebraCechModuleIso` | 代数図式から忘却した加群図式と、既存の構造層 Čech 加群図式の自然な比較。 |
| `schemeSectionAlgebraCechH0Equiv` | 実際の切断の部分代数と、既存の構造層の Čech H⁰ の線形同型。 |
| `projectiveCechSectionAlgebra` | Proj の実際の標準開の適合する切断の部分代数。 |
| `projectiveCechSectionAlgebra_finite` | Noether 基底上で次数付き環が多項式環上有限なら、その切断部分代数は基底環上有限。 |

これで F4 の等化部分環・Čech H⁰ の比較・2e からの有限性の移送を実際の Proj へ接続した。比較の自然性のカーネル検証は、関手全体を一度に展開せず切断の元ごとの等式で閉じた（heartbeat 等の上限は変更していない）。

次は F5：中心外の同型を平坦な局所化後の実際の Čech 複体へ渡し、正次数の消滅と次数零の余核の消滅を台の包含へ戻す。既存の `schemeStructureCechNativeFlatBaseChangeIso` は実際の底変換の構造層との比較を供給する。台からの冪の零化と有限余核からの導手は既に検証済みだが、この幾何学的な消滅の供給を仮定で隠さず接続する。F5〜F8 は未完、停止点 2f ではない。

## F5 途中：アフィン底変換の消滅と局所化テンソル積の台（59f812e07）

新規 3 本・4 宣言・122 行。2f 累計 25 本・1,359 行（入口の import 込み 1,384 行）。対象と直接 importer は 4,571 jobs 成功、別実行の監査は 8,785 宣言・標準三公理のみ。共有鍵 `--wait 3600` は各実行中だけ取得。

| 宣言 | 主張 |
| --- | --- |
| `affineSchemeCechHomology_isZero` | アフィンスキームの準連接係数と有限アフィン被覆では正次数の Čech H が零。任意の基底環へのスカラー制限を含む。 |
| `support_subset_of_localizedTensor_subsingleton` | V(I) 外の各素点で局所化環とのテンソル積が零なら、加群の台は V(I) に含まれる。 |
| `finiteLocalizedTensor_exists_pow_le_annihilator` | 上の加群が有限、I が有限生成なら、ある Iⁿ が加群を消す。 |
| `affineBaseChangeCechHomology_isZero` | 実際の flat 底変換がアフィンで、逆像の有限アフィン被覆が指定されているなら、元の構造層の正次数 Čech H のスカラー拡大が零。 |

アフィン消滅は全空間一つの被覆との共通細分比較で示した。単一被覆の狭義増加複体の長さによる消滅を、全タプルの複体へ戻す。導来関手のコホモロジーとの比較は導入していない。

F5 は未完。中心外の同型から各素点の底変換のアフィン性と逆像被覆の条件を供給し、今回の消滅と台の補題を実際の射影 Čech H について合成する。また次数零の切断代数の余核について、中心外の消滅を供給する必要がある。F6〜F8 の厚化を経由する Frobenius と全複体も残る。停止点 2f ではない。

## F5 正次数：中心外の同型から射影 Čech H の冪の零化（81397d992）

新規 4 本・6 宣言・207 行。2f 累計 29 本・1,566 行（入口の import 込み 1,595 行）。対象と直接 importer は 4,575 jobs 成功、別実行の監査は 8,791 宣言・標準三公理のみ。共有鍵 `--wait 3600` を各実行中のみ取得。

| 宣言 | 主張 |
| --- | --- |
| `isIso_of_restrict_top` | 全空間への制限が同型なら元の射は同型。 |
| `pullback_snd_isIso_of_open_preimage_top` | 同型な開部分の逆像が全空間なら、底変換した射全体が同型。 |
| `affineCenterComplement_localization_preimage_top` | V(I) 外の素点で局所化すると、中心の補開集合の逆像は全空間。 |
| `pullback_localization_isIso_of_centerComplement` | 中心外で同型な射は、中心外の各素点での局所化後も同型。 |
| `schemeCechSupport_subset_of_isoOffCenter` | 中心外で同型な射の有限アフィン被覆による正次数の構造層 Čech H の台は V(I) 内。 |
| `projectiveCechSupport_power_annihilates` | Noether 基底上の射影標準開の Čech H の正次数は、中心外で構造射が同型なら、ある Iⁿ で消える。 |

正次数側の接続では、局所化後のアフィン性・逆像のアフィン被覆・被覆性をすべて供給した。スカラー拡大の `Module.compHom` と通常の局所化加群のスカラー作用の違いは、明示的な恒等関数の線形同型とテンソル積の同型で照合した。射影の構造射は `schemeScalarMorphism` を用い、大域スカラーの一致を Γ–Spec の三角恒等式で移送した。

F5 の正次数の零化は閉じた。次数零の切断代数 B_Y/im(A) の台・零化はまだ残る。ここでは正次数の主張をそのまま次数零に適用しない。次は実際の増大写像と H⁰ の部分代数比較を照合し、中心外の同型から余核の局所化が零になることを供給する。F6〜F8 の厚化を経由する Frobenius と全複体も未完。停止点 2f ではない。

## F5 次数零途中：実際の増大写像と Čech 微分（070f128d2）

新規 `CechAlgebraAugmentation`、7 宣言・94 行。2f 累計 30 本・1,660 行（入口の import 込み 1,690 行）。対象と直接 importer は 4,576 jobs 成功。別実行の監査は 8,804 宣言・標準三公理のみ。共有鍵 `--wait 3600` を各実行中だけ使用した。

| 宣言 | 主張 |
| --- | --- |
| `fullAlgebraCechAugmentationCochains` | 空交叉の切断から、各長さ1の交叉への実際の制限を代数準同型として構成。 |
| `fullAlgebraCechAugmentation_mem` | その制限族は二つの面で一致する。 |
| `fullAlgebraCechAugmentation` | 適合する切断の部分代数への実際の増大写像。 |
| `fullAlgebraCechAugmentation_algebraMap` | 増大を経由した基底環からの写像は、部分代数のスカラー写像と一致。 |
| `fullAlgebraCechZeroEquiv_symm_apply` | 空タプルへの戻しは、その台への実際の制限。 |
| `fullAlgebraCechAugmentation_eq_differential` | 増大写像の各成分は、既存の増大 Čech 微分の次数零と一致。 |
| `fullAlgebraCechAugmentation_surjective_of_exact` | 次数零の Čech 完全性から、実際の増大写像の全射性を得る。 |

次数零の余核の消滅そのものは未完。次は `schemeModuleAffineOpenCech_acyclic` を全空間のアフィン開に適用し、`openCoverIntersectionPresheafTopIso` とスカラー制限で実際のアフィン被覆の増大完全性を供給する。その後、今回の全射性と底変換の比較を局所化後の余核に接続する。F6〜F8 も未完。停止点 2f ではない。

11-13 昼の凍結予告を受領：18 時の確定連絡までは検証済み成果を枝にコミットする。B3 の凍結が確定した後は翌朝まで枝へのコミットを控え、翌朝の B4 の手順に従って main と改名へ追従する。現時点では凍結の確定連絡はまだない。


## F5 次数零途中：アフィン被覆の代数の増大写像（e1aef1934）

新規 2 本・4 宣言・93 行。2f 累計 32 本・1,753 行（入口の import 込み 1,785 行）。対象と直接 importer は 4,578 jobs 成功。別実行の監査は 8,808 宣言・標準三公理のみ。共有鍵 `--wait 3600` は各実行中だけ使用した。

| 宣言 | 主張 |
| --- | --- |
| `fullAlgebraCechAugmentation_injective_of_differential` | 増大 Čech 微分の単射性から、実際の代数の増大写像の単射性を得る。 |
| `affineSchemeModuleCech_acyclic` | アフィンスキームの準連接係数のアフィン被覆は、任意の大域スカラーへの制限後も増大 Čech 完全。 |
| `affineSchemeSectionAlgebraAugmentation_surjective` | アフィン被覆の適合する切断への実際の代数の増大写像は全射。 |
| `affineSchemeSectionAlgebraAugmentation_bijective` | 同じ増大写像は全単射。 |

次は、基底環から大域切断への全射性を部分代数のスカラー写像へ渡し、局所化後の増大写像と底変換比較を照合する。これを次数零の余核の台・冪の零化へ戻す必要がある。F6〜F8 も未完で、停止点 2f ではない。

凍結前の検証済みの取り込み候補は `e1aef1934`。登録モジュールは `CechAlgebraAugmentationInjective` と `AffineSectionAlgebraAugmentation`（いずれも `SerrePositivity.AlgebraicGeometry` 下）。凍結の確定連絡後は枝へのコミットを控える。


## F5 次数零途中：同型な構造射のスカラーと flat な核（db1145a6e）

新規 3 本・6 個の明示的宣言・117 行。2f 累計 35 本・1,870 行（入口の import 込み 1,905 行）。対象と直接 importer は 4,581 jobs 成功。別実行の監査は 8,822 宣言・標準三公理のみ。共有鍵 `--wait 3600` はビルド・監査それぞれの実行中だけ使用し、待機は一つずつとした。

| 宣言 | 主張 |
| --- | --- |
| `schemeSectionAlgebraCech_empty_scalar_surjective` | 大域スカラーが全射なら、空交叉の実際の切断代数へのスカラーも全射。 |
| `affineSchemeSectionAlgebra_scalar_surjective` | アフィン被覆の適合する切断部分代数へのスカラーは、大域スカラーが全射なら全射。 |
| `schemeScalarHom_bijective_of_isIso` | アフィン基底への構造射が同型なら、それから定まる大域スカラーは全単射。 |
| `schemeSectionAlgebra_scalar_surjective_of_isIso` | 同型な構造射とアフィン被覆に対し、基底環から実際の切断部分代数へのスカラーは全射。 |
| `fullAlgebraCechTensorKernelEquiv` | 切断部分代数の flat なテンソル積は、テンソル化した最初の余境界の核と線形同型。 |
| `fullAlgebraCechTensorKernelEquiv_tmul` | その同型は純テンソルの実際の切断成分を保つ。 |

次の接続では、`schemeStructureCechNativeTensorComplexIso` の次数零・一次の同型を核へ制限し、今回の `fullAlgebraCechTensorKernelEquiv` と合成する。`schemeStructureCechNativeTensorComplexIso_unit_apply` により、純テンソルの像は実際の切断の引き戻しである。基底環の元にこの式を適用し、スカラー写像との可換性まで示す。`ModuleCat.extendScalars` の `Module.compHom` と通常の代数のスカラー作用には明示的な同型を入れ、黙って同一視しない。

これができれば、中心外の局所化後の同型に今回の全射性を適用し、元の余核の局所化の消滅へ戻せる。現時点ではその最後の比較と F5 の次数零の冪の零化は未完。F6 の厚化を経由する Frobenius、F7 の次数零の完全性、F8 の全複体への接続も残る。停止点 2f ではない。


## F5 次数零：実際の底変換、余核の台、冪による零化（c0f4298e4）

新規 10 本・20 公開宣言（ほか private 補題と local instance 各 1）・515 行。2f 累計 45 本・2,385 行（入口の import 込み 2,430 行）。対象と直接 importer は 4,591 jobs 成功。別実行の監査は 8,879 宣言・標準三公理のみ。共有鍵 `--wait 3600` はビルド・監査の各実行中だけ使用した。待機は一つずつ。

| 宣言 | 主張 |
| --- | --- |
| `linearKernelEquivOfCommute` | 可換な線形同型の正方形を、実際の核の同型へ制限する。 |
| `linearKernelEquivOfCommute_apply` | 核の順写像は元の線形同型そのもの。 |
| `linearKernelEquivOfCommute_symm_apply` | 核の逆写像は元の線形同型の逆そのもの。 |
| `fullAlgebraCechTensorComparison` | 余境界と可換な各項の同型から、切断部分代数の平坦テンソル比較を作る。 |
| `fullAlgebraCechTensorComparison_tmul` | 部分代数の比較の純テンソル上の値は、各項の比較の値。 |
| `tensorExtendScalarsEquiv` | 通常の代数のテンソル積と ModuleCat.extendScalars の作用の表示を比較する。 |
| `tensorExtendScalarsEquiv_tmul` | その比較は純テンソルの因子を保つ。 |
| `schemeAlgebraCechTensorTermEquiv` | 実際のスキームの底変換から、代数係数の各 Čech 項のテンソル比較を供給する。 |
| `schemeAlgebraCechTensorTermEquiv_differential` | 実際の各項の比較は最初の余境界と可換。 |
| `schemeAlgebraCechTensorEquiv` | 実際の平坦底変換に沿った切断部分代数の線形同型。 |
| `schemeStructureCechBaseChangeDiagramRestriction_one` | 実際の切断の引き戻しは単位元を保つ。 |
| `schemeAlgebraCechTensorEquiv_one` | 部分代数の底変換同型は 1 ⊗ 1 を 1 に送る。 |
| `schemeAlgebraCechTensorEquiv_scalar` | 部分代数の底変換同型は a ⊗ 1 を実際の algebraMap(a) に送る。 |
| `schemeCechScalarTensor_surjective` | 構造射が同型になる平坦底変換では、元のスカラー写像のテンソル化は全射。 |
| `tensorCokernel_subsingleton_of_surjective` | 写像のテンソル化が全射なら、実際の余核のテンソル積は零。 |
| `cokernel_support_subset_of_localizedTensor_surjective` | 中心外の各局所化テンソル積で全射なら、余核の台は中心内。 |
| `schemeCechScalarCokernel_support_subset_of_isoOffCenter` | 中心外で同型な射のアフィン被覆の切断部分代数のスカラー余核の台は中心内。 |
| `projectiveCechScalarCokernel_support` | 射影標準開の切断部分代数のスカラー余核の台は中心内。 |
| `projectiveCechScalarCokernel_power_annihilates` | その余核は中心のある冪で零化される。 |
| `projectiveCechSectionAlgebra_exists_pow_map_lift` | 中心の十分高い冪の拡大イデアルの元は基底環へ持ち上がる。 |

内部の `fullCechComplex_d_zero` は通常の Čech 複体の次数零の微分を明示する private 補題、`tensorExtendScalarTower` は制限加群と代数作用の整合性を与える local instance。heartbeat 等の上限は変更していない。

実際の底変換の同型を各項で取り、最初の余境界の核へ制限した。`ModuleCat.extendScalars` の作用の表示と通常の代数のテンソル積の違いは明示的な同型で照合した。純テンソルと単位元の計算でスカラー写像との可換性を示したため、中心外の局所化後の全射性を元のスカラー写像のテンソル化へ戻せる。テンソル積の右完全性で余核の消滅へ戻し、台の包含と射影有限性を合成した。底変換比較や余核の消滅を追加の仮定として隠していない。

F5 は正次数と次数零の両方が閉じた。F6〜F8 は未完で、停止点 2f ではない。主な残りは、F6 の正次数の Frobenius 順極限上の比較、F7 の次数零の完全性、F8 の全複体への接続の三つ。

次の F6 の入口：既存の `reesAdicProjectiveClosedCechFrobenius` は同じ厚さ n 上の Frobenius を定義し、射影・遷移との可換性を供給する。一方、F6 に要る n→p*n（反復で n→p^e*n）の厚化を経由する写像は別途構成する。`reesAdicProjectiveClosedCechProjection_shifted_kernel_bound` と `reesAdicProjectiveClosedCechTransition_range_stabilizes` は 2e の既存の評価として再利用する。H 自身の I 進商と、閉厚化の H を同一視せず、実際の商環と標準開の比較を経由する。


## F6 入口：厚化を経由する実際の商環の Frobenius（01cd34c8f）

新規 4 本・15 宣言・214 行。2f 累計 49 本・2,599 行（入口の import 込み 2,648 行）。対象と直接 importer は 4,595 jobs 成功。別実行の監査は 8,910 宣言・標準三公理のみ。共有鍵 `--wait 3600` を各実行中だけ使用し、待機は一つずつとした。

| 宣言 | 主張 |
| --- | --- |
| `frobeniusThickeningMap` | 商 A/Iⁿ から A/I^(p^e*n) への、反復 Frobenius による実際の環準同型。 |
| `frobeniusThickeningMap_mk` | 代表元を p^e 乗に送る公式。 |
| `frobeniusThickeningPower_le` | 厚い段から元の段へ戻すためのイデアルの包含。 |
| `frobeniusThickeningMap_factor` | 元の厚さへ戻す商写像との合成は、その商の反復 Frobenius。 |
| `frobeniusThickeningMap_projection` | 元の環から商への射影と、厚化を経由する反復 Frobenius の可換性。 |
| `frobeniusThickeningMap_transition` | 厚さを下げる遷移と、厚化を経由する反復 Frobenius の可換性。 |
| `reesClosedRingThickeningFrobenius` | 2e の実際の表示 A/(IⁿA) での、厚さ n→p^e*n の環準同型。 |
| `reesClosedRingThickeningFrobenius_mk` | Rees の商環表示でも、代表元の像は p^e 乗。 |
| `reesClosedRingThickeningFrobenius_projection` | 元の環から Rees の実際の商への射影と可換。 |
| `reesClosedRingThickeningFrobenius_preservesPiece` | 商の斉次次数 k を p^e*k に送る。 |
| `reesClosedRingThickeningFrobenius_scalar` | 係数環の反復 Frobenius と可換。 |
| `reesClosedRingThickeningFrobeniusSemilinear` | 実際の商環の厚化写像を、係数の反復 Frobenius に関する半線形写像にする。 |
| `reesClosedRingThickeningFrobeniusSemilinear_apply` | 半線形写像は元の環準同型と同じ値を持つ。 |
| `reesClosedRingThickeningFrobenius_factor` | Rees の商の厚さを戻すと、その商の反復 Frobenius になる。 |
| `reesClosedRingThickeningFrobenius_transition` | Rees の実際の商の厚さを下げる遷移と可換。 |

これらは p の像が零であることだけで定義し、商環・標準開の非自明性は仮定しない。反復の指数 e を直接扱う。`Ideal.map_pow` で 2e の A/(IⁿA) の表示にそろえた。商環の斉次部分は実際の商写像による像であり、その代表元を p^e 乗して次数を制御している。

F6 の完成はまだ主張しない。次は局所化へ移す。既存の `projectiveScalarLocalizationLinearEquiv` とその分数公式で、加群の局所化を環の Away 局所化へ移せる。`IsLocalization.Away.lift` を使い、分母の像が p^e 乗になることから可逆性を供給する。分子・分母の式を用いて指定次数部分へ制限し、Čech 図式へ渡した後、`reesClosedRingCechIso` で Rees 表示へ戻す。厚化の遷移と射影との可換性も同じ比較に通す。

F6 の核側は、十分厚い段への制限の単射性と今回の因子分解を組み合わせる。像側は、厚化間の像の安定化と因子分解で十分高い Frobenius の像を元の H の像へ入れる。これを Frobenius 順極限上の全単射性へ移す作業は未実装。F7 の次数零の商との比較、F8 の全複体も残る。停止点 2f ではない。

## F6 途中：厚化 Frobenius の標準開・Čech と遷移（f716a56b1）

新規 13 本・25 公開宣言（ほか local instance 1）・681 行。2f 累計 62 本・3,280 行（入口の import 込み 3,355 行）。対象と直接 importer は 4,608 jobs 成功。別実行の監査は 8,976 宣言・標準三公理のみ。各実行に共有鍵 `--wait 3600` を使い、待機は一つずつ。報告点 4,500 行、停止基準 18,000 行には達していない。

| 宣言 | 主張 |
| --- | --- |
| `awayPowerMap` | 分母を k 乗へ送る環準同型を Away 局所化へ延長する。 |
| `awayPowerMap_algebraMap` | 局所化の延長は元の環の写像を保つ。 |
| `awayPowerMap_fraction` | 分子を元の写像、分母の指数を k 倍へ送る。 |
| `awayPowerMap_scalar` | 局所化の延長は係数環の指定した写像と可換。 |
| `awayPowerMapSemilinear` | 局所化の延長を半線形写像としてまとめる。 |
| `awayPowerMapSemilinear_apply` | 半線形表示と元の環準同型の値は一致。 |
| `projectiveScalarLocalizationLinearEquiv_fraction` | 加群局所化と Away 局所化の比較の分数公式。 |
| `projectiveLocalizedPowerMap` | 分母を冪に送る写像を標準開の加群局所化へ移す。 |
| `projectiveLocalizedPowerMap_fraction` | 加群局所化でも分母の指数は k 倍になる。 |
| `projectiveGradedAwayPowerMap` | 次数を k 倍に送る条件で指定次数の部分へ制限する。 |
| `projectiveGradedAwayPowerMap_val` | 指定次数の写像は周囲の局所化の写像の制限。 |
| `projectiveNatGradingInt_map_mem_mul` | 自然数次数を k 倍に送る加法写像は整数への零延長でも次数を k 倍に送る。 |
| `projectiveNatGradingInt_chart_map_mem_mul` | 分母次数を含む標準開の指定次数を k 倍へ送る。 |
| `projectiveLocalizedPowerMap_restriction` | 分母を冪に送る写像は標準開を狭める制限と可換。 |
| `projectiveLocalizedPowerMap_naturality` | 係数の線形写像との可換四角形は局所化後も可換。 |
| `reesClosedRingThickeningFrobenius_algebraMap` | 実際の閉厚化の係数の像は p^e 乗へ送られる。 |
| `reesClosedLocalizedThickeningFrobenius` | 実際の閉厚化の局所化に厚さ n→p^e*n の半線形写像を構成する。 |
| `reesClosedLocalizedThickeningFrobenius_fraction` | 厚化の局所化の分子・分母の p^e 乗の公式。 |
| `reesClosedChartThickeningFrobenius` | 厚化の写像を実際の標準開の指定次数へ制限する。 |
| `reesClosedChartThickeningFrobenius_val` | 標準開の写像と周囲の局所化の写像の一致。 |
| `reesClosedChartThickeningFrobeniusNatTrans` | 標準開の写像を係数制限後の Čech 図式の自然変換にする。 |
| `reesClosedCechThickeningFrobenius` | 実際の閉厚化の Čech H 上の厚化を経由する反復 Frobenius。 |
| `reesClosedLocalizedThickeningFrobenius_transition` | 局所化の厚化 Frobenius は厚さを下げる遷移と可換。 |
| `reesClosedChartThickeningFrobeniusNatTrans_transition` | 厚化の遷移との四角形は実際の標準開図式で可換。 |
| `reesClosedCechThickeningFrobenius_transition` | 厚化の遷移との可換性は Čech H 上でも成り立つ。 |

標準開が空の場合を排除していない。商環にも局所化にも Nontrivial は課さず、p の像が零であることを使う。Čech H の定義と比較の docstring には原典の Hⁱ と Stacks 30.2.6 の非形式化の比較を明記した。新規モジュールの登録まで検証済みで、未検証の `ProjectiveLocalizedIteratedFrobenius.lean` は今回のコミットに含めていない。

F6 は未完。今回の反復 Frobenius は厚化先への実際の写像として構成できたが、厚さを戻した合成と既存の Frobenius の反復との比較、元の環からの射影との可換性を Čech H へ送る部分が残る。その後 `reesClosedRingCechIso` で既存の Rees 表示へ移し、2e の核の評価・像の安定化と F5 を接続して順極限の全単射性を出す。F7 の次数零の環としての比較と F8 の全複体も残る。停止点 2f ではない。

残りの見込み：主要な接続は F6 の因子分解・射影比較・順極限判定、F7 の H⁰ の環の比較と有限射の四角形、F8 の全複体の計 6 束。補助 API の規模がまだ動くため、現時点で完了時刻は確約しない。今夜の凍結は予告段階で、確定連絡後は枝へのコミットを控える。

## F6 途中：局所化の因子分解と実際の Čech H の反復系（bf7cbbd23）

新規 6 本・17 公開宣言（ほか private 補題 1、local instance 1、自然性の reassoc 生成宣言）・481 行。2f 累計 68 本・3,761 行（入口の import 込み 3,848 行）。対象と直接 importer は 4,614 jobs 成功。別実行の監査は 9,023 宣言・標準三公理のみ。ビルド・監査の実行ごとに共有鍵 `--wait 3600` を使い、同じ worktree の待機を一つに保った。報告点 4,500 行、停止基準 18,000 行の内側。

| 宣言 | 主張 |
| --- | --- |
| `projectiveLocalizedPowerMap_frobenius` | 局所化へ延長した反復 Frobenius は、実際の局所化環の p^e 乗。 |
| `reesClosedLocalizedThickeningFrobenius_factor` | 厚化を経由して元の厚さへ戻す合成は、実際の局所化の p^e 乗。 |
| `reesClosedLocalizedThickeningFrobenius_projection` | 射影後の厚化 Frobenius は、元の局所化の p^e 乗の射影。 |
| `projectiveCechIntRestrictionComplexIso` | Čech 複体は整数加群への係数制限と交換する。 |
| `projectiveCechIntRestrictionHomologyIso` | Čech H と整数への係数制限の同型。 |
| `projectiveCechIntRestrictionComplexIso_naturality` | 複体の整数係数比較は係数図式の射に自然。 |
| `projectiveCechIntRestrictionHomologyIso_naturality` | Čech H の整数係数比較は係数図式の射に自然。 |
| `projectiveChartIteratedFrobenius` | 捻り零の各標準開の反復 Frobenius の半線形自己写像。 |
| `projectiveChartIteratedFrobenius_val` | 各標準開の自己写像の値は周囲の局所化の p^e 乗。 |
| `projectiveCechIntFrobeniusDiagram` | 捻り零の標準開図式の整数線形な反復 Frobenius。 |
| `projectiveCechIntFrobeniusDiagram_zero` | 零回の反復は図式の恒等射。 |
| `projectiveCechIntFrobeniusDiagram_add` | 反復回数の加法は図式の射の合成に対応する。 |
| `ProjectiveCechIntHomology` | 捻り零の実際の標準開 Čech H を整数加群として読む。 |
| `projectiveCechIntFrobeniusHomology` | 実際の p^e 乗から誘導される Čech H の線形自己写像。 |
| `projectiveCechIntFrobeniusHomology_zero` | Čech H の零回の反復は恒等写像。 |
| `projectiveCechIntFrobeniusHomology_add` | Čech H の反復回数の加法は写像の合成に対応する。 |
| `projectiveCechIntFrobeniusHomology_directedSystem` | 段差 j−i の反復を遷移とする実際の Čech H の有向系。 |

整数への係数制限は内部の反復則を追うための比較であり、最終出力 `SerrePositivity.Cech.AugmentedRingCechExact` は変更しない。元の係数環は `Type u` のままで、整数環と同じ宇宙へ狭めていない。既存の一般の係数制限のファイルでは二つの環が同じ宇宙に置かれていたため、今回は整数環から任意の宇宙の係数環への専用比較を置いた。複体の比較は各項の恒等写像、H の比較は係数制限の完全性から作り、射への自然性も検証した。半線形写像を単に R 線形とみなしていない。

次の `ReesClosedCechIntThickening.lean` は未検証の下書きであり、今回のコミット・監査には含めない。局所化で検証した因子分解と射影比較を、実際の捻り零の標準開図式に渡す部分。その後 H 関手を適用して、上の検証済みの反復系と同じ写像の式にする。

F6 の適用順を具体化した。厚さ 1 への制限 u₁ の核の元 x について、十分大きい e を取り、u_(p^e)(F^e x)=0 を厚化 Frobenius の射影比較から得る。F5 と 2e の核の評価で u_(p^e) が単射になるため F^e x=0。像側は、厚化間の像の安定化の段 m 以上に p^e を取り、厚化の因子分解で F^e y を im(u₁) に入れる。この二条件で順極限上の単射性と全射性を証明する。まず厚さ 1 の比較を閉じればよく、各厚さの順極限を先に別々に構成する必要はない。これらの評価の実際の適用と順極限判定は未実装で、F6 の完成は主張しない。

残りの見込み：主要な接続は、F6 の図式・H 上の因子分解と射影比較、核・像評価から順極限への接続、F7 の H⁰ の環と有限射の四角形、F8 の全複体の計 4 束。停止点 2f ではない。凍結の予告は引き続き確定待ち。

## F6 途中：正次数の Frobenius 順極限の全単射性（0a00affc8、11-13）

検証済み 9 モジュール・32 公開宣言・701 行を登録した。対象と直接 importer のビルドは 4,623 jobs 成功。別実行の AlgebraicGeometry 監査は **9,142 宣言・標準三公理のみ**。各実行は共有鍵 `--wait 3600` を経由し、待ちは一つ。未検証の `LinearDirectLimitCocone.lean` は登録・コミットに含めない。

登録モジュール（すべて `SerrePositivity.AlgebraicGeometry.` の下）：

| モジュール | 到達点 |
| --- | --- |
| `LinearDirectLimitComparison` | 有向系間の写像と、核の eventual vanishing・像の eventual lifting による順極限の単射・全射判定。 |
| `ProjectiveCechFrobeniusDirectLimit` | 実際の Čech H の Frobenius 順極限と閉厚化への写像、その単射・全射。 |
| `ProjectiveCechFrobeniusPositive` | 中心の外で同型となる射影的構造射について、正次数の閉厚化への順極限制限は全単射。 |
| `ProjectiveCechSupportGradedPower` | F5 の台による冪消滅を標準開の次数付き加群表示の Čech H へ移す。 |
| `ReesClosedCechIntBounds` | 整数係数表示で、十分厚い閉厚化への単射性と遷移像の持ち上げ。 |
| `ReesClosedCechIntComparison` | 整数係数・Rees・商環の各 H の加法同型、射影と厚さの遷移への自然性。 |
| `ReesClosedCechIntFrobeniusBounds` | 制限の核は反復 Frobenius で消え、閉厚化側の元の反復は制限の像に入る。 |
| `ReesClosedCechIntMaps` | 実際の整数係数 Čech H の射影・遷移・厚化 Frobenius と因子分解。 |
| `ReesClosedCechIntThickening` | 同じ因子分解・射影比較を標準開の図式上で構成。 |

主宣言 `projectiveCechFrobeniusDirectLimit_closed_bijective` は、Noether 基底、有限生成の次数付き加群、標準開の生成条件、中心の外での構造射の同型、標数 p の条件から、正次数 q の実際の Čech H の Frobenius 順極限上の全単射性を示す。核の消滅や像の安定化を未証明の追加仮定として主宣言に残していない。F5 の消滅と 2e の核・像評価を適用した。

**半分の規模の報告**：2f 累計は 77 モジュール・4,462 行（登録を含め 4,567 行）。報告点 4,500 行に達する区切りとして記録する。残りは暫定で F6 の完成に 500〜1,500 行、F7 に 1,500〜3,500 行、F8 に 1,000〜2,500 行、計 3,000〜7,500 行。合計見込み 7,462〜11,962 行は停止基準 18,000 行以内。

F6 はまだ未完。今回の出力は H の順極限であり、完備化ではなく perfection の係数の Čech H との自然な比較を次に作る。代数的順極限の普遍性を圏論的余極限へ渡し、2e の filtered colimit の比較を使う。F7 の次数零の環の比較・有限射の四角形と、F8 の全複体も残る。最終出力 `SerrePositivity.Cech.AugmentedRingCechExact` は変更しない。

11-13 の凍結は予告段階。検証済みの上記コミットを途中の取り込み候補として用意した。18 時の確定連絡後は翌朝まで枝へのコミットを控え、未検証の下書きは作業木に残す。翌朝の main 取り込みと改名表による追従は、一括レーンの手順を受けて実施する。

## F6 途中：Frobenius の係数関手と順極限比較の自然性（d86327316、11-13）

新規 4 モジュール・13 公開宣言・278 行。対象ビルドは 3,087 jobs、入口への登録を含む直接 importer のビルドは 4,627 jobs 成功。別実行の公理監査は **9,196 宣言・標準三公理のみ**。ビルド・監査とも共有鍵 `--wait 3600` を使い、各時点の待ちは一つ。新規登録は `LinearDirectLimitCocone`、`LinearDirectLimitNaturality`、`ProjectiveCechFrobeniusFunctor`、`ReesClosedFrobeniusFunctor`。いずれも `SerrePositivity.AlgebraicGeometry` の下。

| 宣言 | 主張 |
| --- | --- |
| `linearDirectSystemFunctor` | 実際の線形有向系を自然数から加群圏への関手にする。 |
| `linearDirectSystemCocone` | 代数的な順極限への標準写像を余錐にする。 |
| `linearDirectSystemIsColimit` | この余錐は圏論的な余極限の普遍性を持つ。 |
| `linearDirectLimitColimitIso` | 代数的順極限と同じ系の圏論的余極限は同型。 |
| `linearDirectLimitColimitIso_ι` | 比較同型は各段からの標準写像を保つ。 |
| `linearDirectSystemNatTrans` | 有向系の可換な段ごとの写像を自然変換にする。 |
| `linearDirectLimitColimitIso_naturality` | 比較同型は有向系の射に自然。 |
| `projectiveCechFrobeniusCoefficientFunctor` | 標準開の実際の反復 Frobenius を遷移とする係数図式の関手。 |
| `projectiveCechFrobeniusHomologyDiagramIso` | 各段で Čech H を取った図式は、前の束の全単射判定に使った有向系と同型。 |
| `projectiveCechFrobeniusHomologyColimitIso` | 前の束の Frobenius 順極限を、この H の圏論的余極限へ移す。 |
| `reesClosedRingProjectionChartMap_transition` | 環の商への射影は厚さを下げる標準開の遷移と可換。 |
| `reesClosedCechIntProjectionDiagram_frobenius` | 閉厚化への制限は標準開の係数図式の反復 Frobenius と可換。 |
| `reesClosedFrobeniusCoefficientNatTrans` | 実際の閉厚化への制限を Frobenius 係数系の自然変換にする。 |

順極限の整数作用と加法群の標準整数作用の二つの表示には、恒等の加法同型を `AddEquiv.toIntLinearEquiv` で線形同型にする明示的な橋を置いた。加群の台集合や係数環の宇宙は縮小しない。厚化の因子分解と射影比較を合成して係数図式の可換性を証明したので、任意の H の写像を代わりに選んだものではない。

2f 累計は 81 モジュール・4,740 行（登録込み 4,853 行）。前回の半分の規模の報告から 278 行増加。残りの主要な接続は F6 の perfection 係数の Čech H との比較、F7 の次数零の環と有限射の四角形、F8 の全複体。残りの暫定見込みは 3,000〜7,500 行で、停止基準 18,000 行以内。

F6 は未完。次は 2e の `projectiveCechFilteredHomologyIso` とその自然性を再利用する。現在の定理は係数環と加群、添字圏の宇宙をそろえているため、整数係数を `ULift ℤ` の加群へ環同型に沿って移し、添字は `AsSmall ℕ` へ圏同値で移す道を使う。`scheme-drafts/ProjectiveCechIntLift.lean` はこの係数移送の未検証下書きで、今回の登録・コミットには含めない。perfection の係数図式の Čech H との同型および閉厚化への制限との可換性まで閉じる必要がある。F7・F8 も未完で、停止点 2f ではない。

## F6：係数順極限の Čech 複体の正次数の制限（4d779e247、11-13）

新規 7 モジュール・21 公開宣言・462 行。対象ビルドは 3,291 jobs、登録を含む直接 importer は 4,634 jobs 成功。別実行の公理監査は **9,268 宣言・標準三公理のみ**。ビルド・監査は共有鍵 `--wait 3600` を通し、同じ worktree の待ちは一つに保った。前の整数係数移送の下書きは本体に移して検証済みとした。登録は `ProjectiveCechIntLift`、`ProjectiveCechIntLiftNaturality`、`ProjectiveCechIntFiltered`、`ProjectiveCechIntSequential`、`LinearDirectLimitColimitMap`、`ProjectiveFrobeniusColimitCech`、`ProjectiveCechFrobeniusColimitPositive`（すべて `SerrePositivity.AlgebraicGeometry` の下）。

| 宣言 | 主張 |
| --- | --- |
| `projectiveIntCechLiftDiagram` | 整数加群の係数図式を同じ台集合の ULift ℤ 加群へ移す。 |
| `projectiveIntCechLiftRoundtripIso` | 整数へ係数制限して戻すと元の図式と同型。 |
| `projectiveIntCechLiftHomologyIso` | この係数移送は Čech H と交換する。 |
| `projectiveIntCechLiftFunctor` | 係数移送を係数図式間の関手にまとめる。 |
| `projectiveIntCechLiftRoundtripIso_inv_naturality` | 係数の往復同型は図式の射に自然。 |
| `projectiveIntCechLiftHomologyIso_naturality` | 移送の Čech H の比較は図式の射に自然。 |
| `projectiveIntCechLiftHomologyNatIso` | 係数移送と Čech H の比較を自然同型にまとめる。 |
| `projectiveCechFilteredHomologyNatIso` | 2e の既存の filtered 余極限比較を自然同型にまとめる。 |
| `projectiveIntCechFilteredHomologyNatIso` | ULift ℤ への移送を通じ、2e の比較を任意の宇宙の整数加群へ移す。 |
| `projectiveIntCechFilteredHomologyIso` | 各 filtered 図式の整数係数 Čech H と H の余極限の同型。 |
| `projectiveIntCechSequentialHomologyNatIso` | 添字を AsSmall ℕ へ圏同値で移し、自然数の順極限の自然同型を得る。 |
| `projectiveIntCechSequentialHomologyIso` | 自然数の係数図式ごとの Čech H と H の順極限の同型。 |
| `projectiveIntCechSequentialHomologyIso_naturality` | この同型は実際の係数系の射に自然。 |
| `linearDirectSystemColimitMap_bijective` | 代数的順極限の全単射判定を同じ圏論的余極限の射へ移す。 |
| `projectiveFrobeniusColimitCechComplex` | 実際の標準開の Frobenius 係数順極限から全タプル Čech 複体を作る。 |
| `reesClosedFrobeniusColimitCechMap` | 閉厚化への実際の制限から同じ複体の射を作る。 |
| `reesClosedFrobeniusColimitCechHomologyMap` | 同じ複体の射が誘導する各次数の Čech H の写像。 |
| `projectiveFrobeniusColimitCechHomologyIso` | この複体の Čech H は各段の Čech H の順極限と同型。 |
| `projectiveCechFrobeniusHomologyColimit_closed_bijective` | 正次数の H の圏論的順極限の閉厚化への制限は全単射。 |
| `projectiveFrobeniusColimitCech_closed_bijective` | Frobenius 係数順極限で作る Čech H の閉厚化への制限は正次数で全単射。 |
| `reesClosedFrobeniusColimitCechHomologyMap_bijective` | 上の同じ複体の射は正次数の H で全単射を誘導する。 |

中心外で同型な構造射、Noether 基底、有限な次数付き加群、標準開の生成条件、p が素数で係数環・次数付き環で零、という既存の幾何学的入力から正次数の制限の全単射性を得た。核・像評価は前の束で供給済みであり、今回の定理に追加仮定として残していない。係数順極限と H の交換は 2e の `projectiveCechFilteredHomologyIso` とその自然性を再利用し、証明を複製していない。加群の台集合の宇宙を小さくする制限はなく、同じ宇宙の ULift ℤ と同値な添字圏 AsSmall ℕ を通る。I 進完備化の同型を Frobenius 順極限の同型と読み替えていない。

大きな図式の定義展開による同一視は処理量の上限に当たったため、既存の `projectiveCechFrobeniusHomologyDiagramIso` と順極限比較の自然性を明示して移した。heartbeat・再帰深度の上限は変更していない。F6 の正次数の計算は、この実際の Frobenius 係数図式から作る複体のモデルで閉じた。F7・F8 へ渡すときは、標準開の環の `FrobeniusDirectLimit` の表示との項ごとの比較と、H⁰ の環構造との整合性をさらに接続する。この環の表示まで完成したとは主張しない。

2f 累計は **88 モジュール・5,202 行（登録込み 5,329 行）**。半分の規模の報告は前に行っており、停止基準 18,000 行以内。残りの主要な束は、標準開の環の Frobenius 順極限表示との比較、F7 の H⁰ の有限環の四角形、F8 の増大全複体。残りの暫定見込みは 3,000〜7,500 行。

### 次の F7 の接続

- F4 の適合する切断の部分代数を、大域切断へ環として貼る。Mathlib の `TopCat.Sheaf.existsUnique_gluing'` を使い、増大写像と基底のスカラーを保つ。`Scheme.toSpecΓ` を介した因子分解により、元のスキームの全射性から有限環の Spec の全射性を供給する。一般の Stein 分解は作らない。
- B_Y/IB_Y→B_E の核について、2e の評価で十分厚い段への制限の核を IB_Y に入れる。閉厚化を経由する反復 Frobenius の式で、厚さ 1 の核の元の十分高い p 冪が IB_Y に入る。像側は検証済みの像の安定化と同じ因子分解を使う。H⁰ の環の写像との照合が必要で、単に H の加群の式を環の式と呼ばない。
- F3 の有限変更の完全な四角形と合わせ、F7 の短完全性を同じ複体の H⁰ に移す。F8 では正次数と次数零を同じ制限写像の全複体へまとめる。停止点 2f はまだであり、最終出力 `SerrePositivity.Cech.AugmentedRingCechExact` は変更しない。
