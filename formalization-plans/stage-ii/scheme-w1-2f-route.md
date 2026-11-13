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

## F6 途中：標準開の環の Frobenius 順極限表示（991fa4a5b、11-13）

凍結前の途中の取り込み候補。新規 3 モジュール・10 公開宣言・213 行（登録込み 219 行）。対象ビルドは 3,240 jobs、登録した直接 importer `SerrePositivity.AlgebraicGeometry` は 4,637 jobs 成功。別実行の公理監査は **9,306 宣言・標準三公理のみ**。共有鍵は `--wait 3600`、同じ worktree の待ちは一つに保った。

登録モジュール（すべて `SerrePositivity.AlgebraicGeometry`）：`RingDirectLimitIntColimit`、`ProjectiveHomogeneousIteratedFrobenius`、`ProjectiveChartFrobeniusRingColimit`。

| 宣言 | 主張 |
| --- | --- |
| `ringDirectSystemIntMap` | 環の有向系の射を同じ加法写像の整数線形表示へ移す。 |
| `ringDirectSystemIntMap_directedSystem` | 整数線形表示でも有向系の法則が成り立つ。 |
| `ringDirectLimitIntColimitIso` | 環の代数的順極限の加法群と整数加群の圏論的余極限は同型。 |
| `ringDirectLimitIntColimitIso_of` | 同型は各有限段からの標準写像を保つ。 |
| `projectiveHomogeneousChartLinearEquiv_iteratedFrobenius` | 次数零チャートの反復 Frobenius は斉次局所化の実際の p^e 乗に一致する。 |
| `projectiveProjNativeChart_iteratedFrobenius` | 同じ反復 Frobenius は Proj の標準開の切断の p^e 乗に一致する。 |
| `projectiveHomogeneousChart_primeCast` | 基底環で零となる p は各標準開の斉次局所化でも零。 |
| `projectiveChartRingFrobeniusFunctor` | 標準開環の反復 Frobenius の系を整数加群の関手として表示する。 |
| `projectiveChartFrobeniusRingSystemIso` | 各標準開で、既存の係数関手と実際の環の Frobenius 系は自然数の添字に関して自然同型。 |
| `projectiveChartFrobeniusRingColimitIso` | 係数図式の余極限の各標準開は同じ標準開環の FrobeniusDirectLimit と同型。 |

環と加群の順極限の加法構造を、同じ有限段の代表元で明示的に照合した。斉次分数の分子・分母の p^e 乗の式から標準開の比較を示し、非零環や ExpChar の仮定は追加していない。heartbeat・再帰深度の上限も変更していない。

今回の同型は標準開ごとの整数加群の同型である。標準開の制限写像および閉厚化への写像との自然性、H⁰ の環構造との比較は次の接続として残る。各標準開の同型だけで F6〜F8 全体の完成とはしない。最終出力 `SerrePositivity.Cech.AugmentedRingCechExact` の型は変更しない。

2f 累計は **91 モジュール・5,415 行（登録込み 5,548 行）**。残りの主要な束は上記の自然性、F7 の H⁰ の有限環の四角形、F8 の増大全複体。暫定の残り見込み 3,000〜7,500 行、停止基準 18,000 行以内。18 時の凍結の確定連絡が来たら翌朝まで枝へのコミットを控え、下書きと紙の作業を作業木で進める。main への取り込みと全体ビルドは調整役に委ねる。

## F6 途中：標準開の制限に自然な環の順極限の Čech 比較（2b83fb1d2、11-13）

新規 4 モジュール・13 公開宣言・277 行（登録込み 285 行）。対象ビルドは 3,257 jobs 成功。登録した直接 importer は 4,641 jobs 成功。別実行の公理監査は **9,340 宣言・標準三公理のみ**。共有鍵 `--wait 3600` を通し、同じ worktree の待ちは一つに保った。

登録モジュール（すべて `SerrePositivity.AlgebraicGeometry`）：`RingDirectLimitIntNaturality`、`FrobeniusDirectLimitIntNaturality`、`ProjectiveChartFrobeniusRestriction`、`ProjectiveFrobeniusRingChartDiagram`。

| 宣言 | 主張 |
| --- | --- |
| `ringDirectLimitComparison` | 可換な環の有向系の射から実際の環の順極限の射を構成する。 |
| `ringDirectLimitComparison_of` | 同じ射は有限段で指定された環の射に一致する。 |
| `ringDirectLimitIntColimitIso_naturality` | 環の順極限と整数加群の余極限の比較は系の環の射に自然。 |
| `frobeniusIntDirectSystemNatTrans` | 実際の環の射が整数加群としての Frobenius 系の自然変換を誘導する。 |
| `frobeniusDirectLimitIntColimitIso_naturality` | 実際の Frobenius 順極限の環の射と同じ整数加群の余極限の射は比較を介して一致する。 |
| `projectiveChartRingFrobeniusRestriction` | 標準開の環の制限が誘導する反復 Frobenius 系の自然変換。 |
| `projectiveChartFrobeniusRingSystemIso_restriction` | 係数系と環の系との比較は標準開の制限に自然。 |
| `projectiveChartFrobeniusRingSystemColimit_restriction` | 同じ可換四角形は系の余極限でも成り立つ。 |
| `projectiveChartFrobeniusRingColimitIso_restriction` | 前の束の標準開ごとの余極限同型は実際の環の制限を保つ。 |
| `projectiveFrobeniusRingChartDiagram` | 各標準開の環の Frobenius 順極限を整数加群の係数図式にする。 |
| `projectiveFrobeniusRingChartDiagram_map` | この図式の写像は標準開の実際の環の制限から誘導される。 |
| `projectiveFrobeniusRingChartDiagramIso` | 係数順極限と標準開の環の順極限との比較を標準開について自然な同型にする。 |
| `projectiveFrobeniusRingChartCechIso` | 既存の Frobenius 係数 Čech 複体と、実際の標準開環の順極限の Čech 複体の同型。 |

余極限と標準開での評価との比較には Mathlib の `colimit_map_colimitObjIsoColimitCompEvaluation_hom` を再利用した。`colimMap` と `colim.map` の二つの表示は `colimMap_eq` で明示的にそろえ、heartbeat・再帰深度の上限は変更していない。係数図式の関手律は項ごとの同型で移し、さらにその写像が実際の環の制限から誘導されることを別の宣言で照合している。

残る接続を区別する：今回閉じたのは標準開を狭める制限に関する自然性。閉厚化への射に関する同じ自然性、H⁰ の環構造、F7 の有限環の四角形、F8 の増大全複体は未完。2f 累計は **95 モジュール・5,692 行（登録込み 5,833 行）**。残りの暫定見込みは 3,000〜7,500 行、停止基準 18,000 行以内。停止点 2f ではない。

次の実装の材料を確認した。
- 閉厚化への係数の射には、2e の `projectiveHomogeneousChartLinearEquiv_map`（`ProjectiveHomogeneousRingChartMap`）がある。次数付き環の写像と多項式環上の代数写像が同じ写像であることから、斉次局所化の実際の環の写像との比較を供給する。今回の一般の環の順極限の自然性と合成する。
- H⁰ の既存の `affineSchemeSectionAlgebraAugmentation_bijective` は全空間のアフィン性を要求するので、Proj 全体へはそのまま適用しない。`TopCat.Sheaf.existsUnique_gluing'` により、一般の開被覆の `fullAlgebraCechEqualizer` と大域切断を、増大写像を保つ環の同型でつなぐ。この段は高次コホモロジーの消滅や一般の Stein 分解を要求しない。F7 の Spec 全射性にはこの実際の環の比較を使う。

## F6：閉厚化への自然性と標準開環の Čech H の正次数（f8521262a・b24a8233c、11-13）

新規 5 モジュール・14 公開宣言・386 行（登録込み 396 行）。18 時前に対象検証済みの最初の二本を `f8521262a` にコミットした。その後、残る三本を含む対象ビルドは 3,311 jobs 成功。残る三本と登録は `b24a8233c`。直接 importer は 4,646 jobs 成功、別実行の公理監査は **9,398 宣言・標準三公理のみ**。共有鍵 `--wait 3600` を使い、待ちは一つに保った。

登録モジュール（すべて `SerrePositivity.AlgebraicGeometry`）：`ReesClosedRingGrading`、`ReesClosedHomogeneousProjection`、`ReesClosedFrobeniusRingColimit`、`ReesClosedFrobeniusRingCech`、`ProjectiveFrobeniusRingCechPositive`。

| 宣言 | 主張 |
| --- | --- |
| `reesClosedRingLinearEquiv_map_piece` | Rees の商の次数成分は、商の線形同型で実際の環の商の次数成分へ移る。 |
| `reesClosedRingGrade_isInternal` | 基底イデアルによる閉厚化の実際の環の次数成分は内部直和をなす。 |
| `reesClosedRingGradedRing` | 商環の積と内部直和分解を合わせた次数付き環構造。 |
| `reesClosedGradedRingProjection` | 閉厚化の構造環への実際の次数付き環の射影。 |
| `reesClosedHomogeneousChartProjection` | 各標準開で閉厚化への制限を与える、斉次局所化の実際の環準同型。 |
| `reesClosedHomogeneousChartProjection_compare` | 既存の加群の制限は、この斉次局所化の環の射影に一致する。 |
| `reesClosedChartRingFrobeniusNatTrans` | 実際の標準開の射影が誘導する反復 Frobenius 系の自然変換。 |
| `reesClosedChartFrobeniusRingSystemIso_projection` | 係数系と環の系の比較は、閉厚化への射影に自然。 |
| `reesClosedChartFrobeniusRingColimitIso_projection` | 同じ自然性は、各標準開の Frobenius 順極限の比較で成り立つ。 |
| `reesClosedFrobeniusRingChartMap` | 標準開環の順極限の係数図式上の閉厚化への制限。 |
| `reesClosedFrobeniusRingChartMap_app` | この射の各成分は、実際の環の射影が誘導する Frobenius 順極限の射。 |
| `reesClosedFrobeniusRingCechMap` | 同じ係数図式の制限が誘導する Čech 複体の射。 |
| `reesClosedFrobeniusRingCechIso_projection` | Čech 複体の二つの表示の同型は、閉厚化への同じ制限と可換。 |
| `reesClosedFrobeniusRingCechHomologyMap_bijective` | Noether 基底、有限な次数付き加群、標準開の生成条件、中心外での同型、p が素数で係数環・構造環で零、という入力から、標準開環の Frobenius 順極限の Čech H の閉厚化への制限は正次数で全単射。 |

商環の次数成分について、積を保つ構造だけでは斉次局所化の環の比較に足りず、直和分解の供給が必要だった。基底イデアルの作用が各次数射影で保たれることを使い、既存の `HilbertSerre.isInternal_quotientGrade` から商の内部直和を得て、実際の環の商へ移した。この構造は多項式環の添字型に依存しない。有限段の比較は 2e の `projectiveHomogeneousChartLinearEquiv_map`、余極限の比較は既存の環の順極限の自然性と Mathlib の `preservesColimitNatIso` を再利用する。

主定理の核の消滅・像の安定化は、前の F6 の幾何学的入力から得た結果を使い、追加仮定として残していない。原典 BST13 Lemma 3.9・BS17 Lemma 4.6(i) の Hⁱ に対応する途中の主張が Čech 版であることと、Stacks 30.2.6 の導来関手との比較を形式化しないことを docstring に記した。零環や空の中心を排除せず、heartbeat・再帰深度の上限も変えていない。

**到達点**：F6 の正次数の制限の全単射性を、標準開の実際の環の Frobenius 順極限を使う Čech 複体へ、同じ閉厚化への写像で接続した。H⁰ の環構造とその有限環の四角形（F7）、増大全複体（F8）、停止点の全体の自然性の検収は未完。2f 累計は **100 モジュール・6,078 行（登録込み 6,229 行）**。残りは暫定 3,000〜7,500 行、停止基準 18,000 行以内。最終出力 `SerrePositivity.Cech.AugmentedRingCechExact` の型は変更しない。

## F7 途中：一般の開被覆の Čech H⁰ の環と大域切断（611758146、11-13）

新規 4 モジュール・19 公開宣言・330 行（登録込み 338 行）。対象ビルドは 2,844 jobs 成功。直接 importer は 4,650 jobs 成功。別実行の公理監査は **9,452 宣言・標準三公理のみ**。すべて共有鍵 `--wait 3600` を通し、待ちは一つに保った。

登録モジュール：`SchemeCompatibleSections`、`SchemeCechSingletonSections`、`SchemeCechCompatibleSections`、`SchemeCechGlobalSections`（すべて `SerrePositivity.AlgebraicGeometry`）。

| 宣言 | 主張 |
| --- | --- |
| `schemeCompatibleSections` | 開被覆上の適合する切断族の部分環。 |
| `schemeGlobalToCompatibleSections` | 大域切断の実際の制限が定める環準同型。 |
| `schemeGlobalToCompatibleSections_apply` | その各成分は構造層の制限写像。 |
| `schemeGlobalToCompatibleSections_bijective` | 被覆条件のもとで制限写像は全単射。 |
| `schemeGlobalCompatibleSectionsEquiv` | 大域切断環と適合する切断族の環の同型。 |
| `cechOpenIntersection_tuple` | タプルの台の交叉とタプルで添字付けた交叉は一致する。 |
| `cechOpenIntersection_tuple_one` | 一項タプルの交叉は指定された開集合。 |
| `cechOpenIntersection_tuple_two` | 二項タプルの交叉は二つの開集合の交叉。 |
| `schemeCechSingletonSectionsEquiv` | Čech の零次切断族と開被覆上の切断族の環同型。 |
| `schemeCechSingletonSectionsEquiv_recover` | 同型を戻すと元の一項タプルの切断を回収する。 |
| `schemeCechSingletonSectionsEquiv_face_zero` | 零番目の面写像は交叉への第二成分の制限。 |
| `schemeCechSingletonSectionsEquiv_face_one` | 一番目の面写像は交叉への第一成分の制限。 |
| `schemeCechSingletonSectionsEquiv_mem_iff` | Čech の equalizer 条件と層の切断の適合条件は同値。 |
| `schemeCechCompatibleSectionsEquiv` | Čech の equalizer の環と適合切断環の同型。 |
| `schemeCechGlobalSectionsEquiv` | 一般の開被覆の Čech の equalizer の環と大域切断環の同型。 |
| `schemeCechGlobalSectionsEquiv_restrict` | 貼り合わせた大域切断の制限は指定された局所切断。 |
| `schemeCechGlobalSectionsEquiv_symm_apply` | 同型の逆は構造層の実際の制限写像。 |
| `schemeCechGlobalSectionsEquiv_symm_algebraMap` | 同型の逆は指定された基底環のスカラーを保つ。 |
| `schemeCechGlobalSectionsAlgEquiv` | 貼り合わせの同型を基底環上の代数同型にする。 |

全空間のアフィン性を仮定せず、層の一意貼り合わせから構成した。有限被覆や高次の消滅もこの同型には不要。導来関手の比較や Stein 分解は導入していない。最終出力の型は変更しない。

次はこの同型で元の構造射を有限切断環の Spec を介して分解し、元の射の全射性を有限環側に渡す。閉厚化の零次環の Frobenius 比較、F7 の短完全列、F8 の増大全複体は未完。2f 累計は **104 モジュール・6,408 行（登録込み 6,567 行）**。残りの暫定見込みは 3,000〜7,500 行、停止基準 18,000 行以内。停止点 2f ではない。

## F7 途中：射影の有限切断環の中心四角形（b20a37a23、11-13）

新規 3 モジュール・8 公開宣言・169 行（登録込み 175 行）。対象ビルドは 3,176 jobs、直接 importer は 4,653 jobs 成功。別実行の公理監査は **9,460 宣言・標準三公理のみ**。共有鍵 `--wait 3600` をビルド・監査の間だけ使い、待ちは一つに保った。

登録モジュール：`SchemeCechSectionSpectrum`、`ProjectiveCechSectionSpectrum`、`ProjectiveCechFiniteCenterExact`（すべて `SerrePositivity.AlgebraicGeometry`）。

| 宣言 | 主張 |
| --- | --- |
| `schemeToCechSectionSpectrum` | 元のスキームから適合切断環の Spec への標準射。 |
| `schemeToCechSectionSpectrum_comp` | 基底スカラーの Spec と合成すると元の構造射になる。 |
| `schemeCechSectionAlgebra_surjectiveSpectrum` | 元の構造射が全射なら、適合切断環の Spec から基底の Spec への射も全射。 |
| `projectiveCechSectionAlgebra_surjectiveSpectrum` | 標準開の生成条件のもとで、射影構造射の全射性を切断環の Spec に移す。 |
| `projectiveCechSectionAlgebra_primeCast` | 基底環で p が零なら切断環でも p は零。 |
| `projectiveCechSectionAlgebra_frobenius_injective` | 全射な射影構造射から、基底環から切断環への Frobenius 順極限の単射性を得る。 |
| `projectiveCechSectionAlgebra_localized_surjective` | 中心外の同型と既存の余核の台の評価から、スカラー写像の局所化の全射性を得る。 |
| `projectiveCechFiniteCenter_exact` | 射影有限性・構造射の全射性・中心外の同型から、基底・有限切断環 B・指定中心・B/IB の Frobenius 四角形の加法群の短完全性を得る。 |

構造射の分解には前の束の大域切断の環の同型と Γ–Spec の標準射を使った。Stein 分解は使わない。有限環の四角形の補題に必要な局所全射性は、`projectiveCechScalarCokernel_support` と Mathlib の局所余核の判定から供給した。追加仮定として残していない。

今回の短完全列の右下は **B/IB の Frobenius 順極限**。閉厚化 E の Čech H⁰ の順極限との比較はまだ必要であり、今回の定理を F7 全体の完成とはしない。次は実際の閉厚化への環の制限を H⁰ の比較へ接続し、2e の核の評価・像の安定化を使って B/IB と E の切断環の Frobenius 比較を得る。その後 F8 の増大全複体へ渡す。最終出力の型は変更しない。

2f 累計は **107 モジュール・6,577 行（登録込み 6,742 行）**。残りの暫定見込みは 3,000〜7,500 行、停止基準 18,000 行以内。停止点 2f ではない。

## F7 途中：適合切断環と Čech H⁰ の比較の自然性（40a140fb9、11-13）

新規 3 モジュール・10 公開宣言・181 行（登録込み 187 行）。対象ビルドは 2,015 jobs、直接 importer は 4,656 jobs 成功。別実行の公理監査は **9,487 宣言・標準三公理のみ**。共有鍵 `--wait 3600` をビルド・監査の間だけ使い、待ちは一つに保った。

登録モジュール：`CechAlgebraEqualizerMap`、`FullCechH0KernelNaturality`、`CechAlgebraH0Naturality`（すべて `SerrePositivity.AlgebraicGeometry`）。

| 宣言 | 主張 |
| --- | --- |
| `fullAlgebraCechCochainsMap` | 代数係数図式の射が、全タプルの切断族に誘導する成分ごとの代数写像。 |
| `fullAlgebraCechCochainsMap_face` | この写像は二つの面の制限と可換。 |
| `fullAlgebraCechEqualizerMap` | 適合切断の部分代数へ制限した実際の代数写像。 |
| `fullAlgebraCechEqualizerMap_apply` | 各成分は指定された係数図式の射そのもの。 |
| `fullAlgebraCechEqualizerMap_id` | 恒等係数写像は適合切断の恒等写像を誘導する。 |
| `fullAlgebraCechEqualizerMap_comp` | 適合切断の写像は係数図式の射の合成を保つ。 |
| `fullCechH0KernelIso_hom_subtype` | H⁰ と核の比較の後の包含は、homologyπ の逆と cycles の包含の合成。 |
| `fullCechH0KernelIso_naturality_subtype` | H⁰ の写像と核への比較は、実際の零次項の写像と可換。 |
| `fullAlgebraCechH0Equiv_kernel` | 適合切断から H⁰ を経て核へ戻すと元の切断族になる。 |
| `fullAlgebraCechH0Equiv_naturality` | 適合切断環と Čech H⁰ の線形比較は、実際の係数図式の代数写像に自然。 |

2e の核・像の評価は線形な H⁰ の写像に対する結果であり、F7 は環の制限と冪乗を使う。今回の自然性はこの二つを同じ比較の下で一致させるための補題。既存の `fullCechH0KernelIso` をそのまま使い、Mathlib の cycles の包含と homologyπ の自然性で証明した。導来関手との新しい比較や上限の引き上げは行っていない。

次は閉厚化の斉次局所化の射 `reesClosedHomogeneousChartProjection` を代数係数図式の射としてまとめる。既存の `projectiveHomogeneousChartDiagram_map` と `reesClosedHomogeneousChartProjection_compare` で、実際の環の制限と線形な係数写像を照合する。その後、今回の自然性を通して 2e の核の評価・像の安定化を適合切断環に移す。B/IB と閉厚化の切断環の Frobenius 比較、F7 の幾何学的四角形、F8 の増大全複体は未完。

2f 累計は **110 モジュール・6,758 行（登録込み 6,929 行）**。残りの暫定見込みは 3,000〜7,500 行、停止基準 18,000 行以内。停止点 2f ではなく、最終出力の型も変更していない。

## F7 途中：閉厚化の実際の切断代数と H⁰ の射（79caa299c、11-13）

新規 3 モジュール・14 公開宣言（局所インスタンスを除く）・253 行（登録込み 259 行）。対象ビルドは 3,256 jobs 成功。直接 importer で局所インスタンスの自動生成名と既存モジュールの名前が衝突したため、新規ファイル内の五つの局所インスタンスに固有名を付けた。修正後の直接 importer は 4,659 jobs 成功。別実行の公理監査は **9,539 宣言・標準三公理のみ**。すべて共有鍵 `--wait 3600` を通し、待ちは一つに保った。

登録モジュール：`ProjectiveHomogeneousChartAlgebra`、`ReesClosedHomogeneousAlgebraProjection`、`ReesClosedHomogeneousSections`（すべて `SerrePositivity.AlgebraicGeometry`）。

| 宣言 | 主張 |
| --- | --- |
| `projectiveHomogeneousAwayAlgebra` | 既存の斉次局所化の加群構造と整合する基底環上の代数構造。 |
| `projectiveHomogeneousChartRestrictionAlgHom` | 標準開の実際の環の制限を、既存の線形写像と同じ代数写像にする。 |
| `projectiveHomogeneousChartAlgebraDiagram` | 標準開の斉次局所化の代数係数図式。 |
| `projectiveHomogeneousChartAlgebraDiagram_forget` | 代数図式を加群へ忘却すると、既存の図式と定義的に一致する。 |
| `reesClosedHomogeneousModuleProjection` | 閉厚化への線形な係数の射を斉次局所化の図式に移す。 |
| `reesClosedHomogeneousModuleProjection_apply` | 移した線形写像の各成分は、実際の斉次局所化の環の射影。 |
| `reesClosedHomogeneousChartAlgProjection` | 同じ線形写像を持つ閉厚化への代数写像。 |
| `reesClosedHomogeneousAlgebraProjection` | 閉厚化への制限を斉次標準開の代数図式の自然変換にする。 |
| `projectiveHomogeneousSectionAlgebra` | 斉次標準開の実際の環の適合切断部分代数。 |
| `projectiveHomogeneousSectionH0Equiv` | 適合切断代数と既存の斉次標準開の Čech H⁰ の線形比較。 |
| `projectiveHomogeneousSectionAlgebra_finite` | 射影有限性から適合切断代数の有限性を得る。 |
| `reesClosedHomogeneousSectionProjection` | 閉厚化の適合切断代数への実際の代数写像。 |
| `reesClosedHomogeneousSectionProjection_apply` | その各成分は閉厚化への斉次局所化の環の射影。 |
| `reesClosedHomogeneousSectionH0Equiv_projection` | 適合切断環の制限と、同じ線形な係数写像が誘導する Čech H⁰ の写像は比較を介して可換。 |

基底の代数構造は既存の加群構造から `Algebra.ofModule` で作り、通常の局所化への単射で積とスカラーの整合性を示した。新しい代数図式の忘却が既存の加群図式と定義的に一致するため、前の束の自然性をそのまま閉厚化に適用できる。有限性と H⁰ の比較では Čech 版であることと、Stacks 30.2.6 の導来関手との比較を形式化しないことを明記した。

未完の接続：この斉次切断代数と Proj の構造層の切断代数との環同型、Rees 側の核・像の評価を今回の射へ移すこと、B/IB と閉厚化の切断環の Frobenius 比較、F7 の幾何学的四角形、F8 の増大全複体。今回の線形比較だけで環の Frobenius 比較の完成とはしない。

2f 累計は **113 モジュール・7,011 行（登録込み 7,188 行）**。残りの暫定見込みは 3,000〜7,500 行、停止基準 18,000 行以内。停止点 2f ではなく、最終出力の型も変更していない。

## F7 途中：Rees の核の評価を切断代数へ移す（98ba8c231、11-13）

新規 2 モジュール・7 公開宣言（局所インスタンスを除く）・158 行（登録込み 162 行）。対象ビルドは 3,258 jobs、直接 importer は 4,661 jobs 成功。別実行の公理監査は **9,574 宣言・標準三公理のみ**。共有鍵 `--wait 3600` をビルド・監査の間だけ使い、待ちは一つに保った。

登録モジュール：`ReesHomogeneousSectionH0Comparison`、`ReesHomogeneousSectionKernelBound`（ともに `SerrePositivity.AlgebraicGeometry`）。

| 宣言 | 主張 |
| --- | --- |
| `projectiveHomogeneousSectionNatH0Equiv` | 斉次標準開の切断代数を、元の次数付き加群で計算した Čech H⁰ と比較する。 |
| `projectiveHomogeneousSectionNatH0Equiv_projection` | この比較は閉厚化への実際の制限と可換。 |
| `reesClosedHomogeneousSectionH0Equiv` | 閉厚化の切断代数を、Rees の商加群の Čech H⁰ と比較する。 |
| `reesClosedHomogeneousSectionH0Equiv_reesProjection` | 切断代数の実際の制限を、Rees の核の評価で使った閉厚化への H⁰ の写像へ送る。 |
| `reesClosedHomogeneousSectionProjection_eq_zero_iff` | 切断の制限が零であることと、対応する Rees の H⁰ の制限が零であることは同値。 |
| `reesClosedHomogeneousSectionProjection_kernel_bound` | Noether 基底と有限生成性から、切断代数の制限の核は一様に I^(n-c) 倍の全加群に含まれる。 |
| `reesClosedHomogeneousSectionProjection_kernel_ideal_bound` | 同じ評価を、基底の I^(n-c) を切断環へ拡大したイデアルへの所属として表す。 |

核の評価は 2e の `reesAdicProjectiveClosedCechProjection_kernel_bound` をそのまま使う。比較同型によって核を移し、逆の線形同型がイデアルの作用を保つことから切断代数へ戻した。切断代数自身の I 冪による消滅や核の冪零性を入力仮定にはしていない。核の主張が原典 Stacks 30.20.4(1) の H⁰ に対応する Čech 版であることと、導来関手との比較を形式化しないことを docstring に記した。

残る接続は、像の安定化の切断代数への移送、Frobenius の閉厚化への因子分解と環の冪乗の照合、斉次切断代数と Proj の構造層の切断代数の環同型、それらを用いた F7 の四角形、F8 の増大全複体。今回の核の評価だけで Frobenius 比較の完成とはしない。

2f 累計は **115 モジュール・7,169 行（登録込み 7,350 行）**。残りの暫定見込みは 3,000〜7,500 行、停止基準 18,000 行以内。停止点 2f ではなく、最終出力の型も変更していない。

## F7 途中：切断代数の遷移と像の安定化（220fa8956、11-13）

新規 3 モジュール・11 公開宣言（局所インスタンスを除く）・270 行（登録込み 276 行）。対象ビルドは 3,260 jobs、直接 importer は 4,664 jobs 成功。別実行の公理監査は **9,616 宣言・標準三公理のみ**。共有鍵 `--wait 3600` をビルド・監査の間だけ使い、待ちは一つに保った。

登録モジュール：`ReesClosedHomogeneousTransition`、`ReesClosedHomogeneousSectionTransition`、`ReesHomogeneousSectionImageStabilization`（すべて `SerrePositivity.AlgebraicGeometry`）。

| 宣言 | 主張 |
| --- | --- |
| `reesClosedGradedRingTransition` | 閉厚化の商環の因子写像は次数を保つ環準同型。 |
| `reesClosedHomogeneousChartTransition` | 因子写像が標準開の斉次局所化に誘導する実際の環準同型。 |
| `reesClosedHomogeneousModuleTransition` | 既存の線形な遷移を斉次局所化の図式へ移す。 |
| `reesClosedHomogeneousModuleTransition_apply` | この線形写像は実際の斉次局所化の環の遷移と一致する。 |
| `reesClosedHomogeneousChartAlgTransition` | 同じ遷移を基底環上の代数写像にする。 |
| `reesClosedHomogeneousAlgebraTransition` | 閉厚化の遷移は斉次標準開の代数図式の自然変換。 |
| `reesClosedHomogeneousSectionTransition` | 閉厚化間の実際の適合切断代数の遷移。 |
| `reesClosedHomogeneousSectionTransition_apply` | 切断代数の遷移の各成分は標準開の環の遷移そのもの。 |
| `projectiveHomogeneousSectionNatH0Equiv_transition` | 切断代数と次数付き加群の Čech H⁰ の比較は遷移に自然。 |
| `reesClosedHomogeneousSectionH0Equiv_transition` | Rees の商の Čech H⁰ との比較も実際の遷移に自然。 |
| `reesClosedHomogeneousSectionTransition_range_stabilizes` | 十分遅らせた閉厚化間の遷移の像は、元の切断代数からの制限の像に等しい。一様な遅れを Noether 基底と有限生成性から得る。 |

像の評価は既存の `reesAdicProjectiveClosedCechTransition_range_stabilizes` を、制限と遷移に自然な比較同型で移した。安定した像を抽象的な部分加群で置き換えず、元の切断代数からの実際の制限の像と同定している。途中の H⁰ の比較で型の推論が heartbeat 上限に達した箇所は、曖昧な型推論を除き等式の合成を明示して解消した。上限は変更していない。

前の束の核の評価と今回の像の安定化により、F7 の Frobenius 比較に必要な二つの評価が実際の斉次切断代数で使える。未完：Frobenius の厚化への因子分解と環の冪乗の照合、Proj の構造層の切断代数との環同型、それらを使う F7 の幾何学的四角形と F8 の増大全複体。評価だけで Frobenius 比較や 2f 全体の完成とはしない。

2f 累計は **118 モジュール・7,439 行（登録込み 7,626 行）**。残りの暫定見込みは 3,000〜7,500 行、停止基準 18,000 行以内。停止点 2f ではなく、最終出力の型も変更していない。

## F7 途中：厚化を経由する切断の Frobenius と冪の持ち上げ（72cf663a0、11-13）

新規 3 モジュール・12 公開宣言（局所インスタンスを除く）・235 行（登録込み 241 行）。対象ビルドは 3,263 jobs、直接 importer は 4,667 jobs 成功。別実行の公理監査は **9,650 宣言・標準三公理のみ**。共有鍵 `--wait 3600` をビルド・監査の間だけ使い、待ちは一つに保った。

登録モジュール：`CechAlgebraEqualizerAddMap`、`ReesHomogeneousThickeningDiagram`、`ReesHomogeneousSectionPowerLift`（すべて `SerrePositivity.AlgebraicGeometry`）。

| 宣言 | 主張 |
| --- | --- |
| `algebraCechIntDiagram` | 代数係数図式の加法群を整数加群の図式として扱う。 |
| `fullAlgebraCechCochainsAddMap` | 整数線形な係数写像をタプルごとの加法写像にする。 |
| `fullAlgebraCechCochainsAddMap_face` | この写像は二つの面の制限と可換。 |
| `fullAlgebraCechEqualizerAddMap` | 整数線形な係数写像が適合切断の加法群に誘導する写像。 |
| `fullAlgebraCechEqualizerAddMap_apply` | その成分は指定した係数の射そのもの。 |
| `reesHomogeneousThickeningDiagram` | 厚化を経由する Frobenius を斉次標準開の整数加群図式の射にする。 |
| `reesHomogeneousThickeningDiagram_apply` | 各成分は既存の指定次数の写像を標準開の比較で移したもの。 |
| `reesHomogeneousThickeningDiagram_factor` | 厚化から制限で戻すと、標準開の環の実際の p^e 乗になる。 |
| `reesHomogeneousSectionThickening` | 厚化 Frobenius を適合切断の加法群へ送る。 |
| `reesHomogeneousSectionThickening_apply` | 切断の厚化写像の各成分は指定した標準開の写像。 |
| `reesHomogeneousSectionThickening_factor` | 切断の厚化写像を制限で戻すと、実際の切断環の p^e 乗になる。 |
| `reesClosedHomogeneousSectionProjection_power_lifts` | Noether 基底・有限生成性・素数 p が基底環と構造環で零という入力から、一様な e が存在し、閉厚化の任意の切断の p^e 乗が元の切断の制限に持ち上がる。 |

基底環上では半線形なので、厚化写像を基底上の代数写像とはしていない。整数加群図式の自然性で適合条件を保ち、制限後の写像が実際の環の冪乗であることを既存の斉次分数の比較で示した。像の安定化に必要な厚さを p^(1+c) で上回らせるため、指数は切断によらず一様。比較の展開が再帰深度に達した箇所は成分補題を分けて解消し、上限は変更していない。

残る単射側では `reesClosedCechIntThickeningDiagram_projection` を同じ標準開の比較で移し、射影後の厚化写像と p^e 乗後の射影を照合する。制限で消える元の p^e 乗を十分厚い制限の核に入れ、前の束のイデアル版の核の評価で IB に入れる。その後 B/IB と閉厚化の切断環の Frobenius 比較を閉じる。Proj の構造層の切断代数との環同型、F7 の幾何学的四角形、F8 の増大全複体は未完。

2f 累計は **121 モジュール・7,674 行（登録込み 7,867 行）**。残りの暫定見込みは 3,000〜7,500 行、停止基準 18,000 行以内。停止点 2f ではなく、最終出力の型も変更していない。

## F7：斉次切断代数の商と閉厚化の Frobenius 比較（12b131cd9、11-13）

新規 4 モジュール・12 公開宣言（局所インスタンスを除く）・287 行（登録込み 295 行）。対象ビルドは 3,268 jobs、直接 importer は 4,671 jobs 成功。別実行の公理監査は **9,682 宣言・標準三公理のみ**。共有鍵 `--wait 3600` をビルド・監査の間だけ使い、待ちは一つに保った。

登録モジュール：`ReesHomogeneousThickeningProjection`、`ReesHomogeneousSectionKernelPower`、`ReesHomogeneousSectionQuotient`、`ReesHomogeneousSectionFrobeniusComparison`（すべて `SerrePositivity.AlgebraicGeometry`）。

| 宣言 | 主張 |
| --- | --- |
| `reesHomogeneousThickeningDiagram_projection` | 標準開から射影した後の厚化写像は、実際の環の p^e 乗後の厚い閉厚化への射影に一致する。 |
| `reesHomogeneousSectionThickening_projection` | 同じ可換性が適合切断に成り立つ。 |
| `reesClosedHomogeneousSectionProjection_kernel_power` | Noether 基底と有限生成性から、制限の核の一様な Frobenius 冪が IB に入る。 |
| `projectiveHomogeneousAway_scalar_eq_zero` | 構造環で零になる基底スカラーは斉次局所化でも零になる。 |
| `projectiveHomogeneousSectionAlgebra_scalar_eq_zero` | 同じスカラーは適合切断代数でも零になる。 |
| `reesClosedHomogeneousSectionProjection_ideal_le_ker` | 閉厚化への制限は I^n の切断環への拡大を消す。 |
| `reesClosedHomogeneousSectionQuotientMap` | B/(I^n B) から実際の閉厚化の切断代数への比較環準同型。 |
| `reesClosedHomogeneousSectionQuotientMap_mk` | この比較写像は代表元上で元の切断の制限に一致する。 |
| `projectiveHomogeneousSectionAlgebra_primeCast` | 基底環で p が零なら適合切断代数でも p は零。 |
| `reesClosedHomogeneousSectionQuotientMap_kernel_nil` | B/IB から閉厚化の切断代数への比較写像の核は nil。 |
| `reesClosedHomogeneousSectionQuotientMap_power_lifts` | 閉厚化の切断のある Frobenius 冪は、この比較写像の像に入る。 |
| `reesClosedHomogeneousSectionQuotientMap_frobenius_bijective` | 実際の比較写像が誘導する Frobenius 順極限の環準同型は全単射。 |

核の評価の定数を c とし、p^(c+1) が c+1 以上であることから、制限の核のその冪を IB に入れた。商写像の核の元を代表元で取り、商の零判定で nil 性を得る。全射性は前の束の一様な冪の持ち上げを用いる。最後に既存の `frobeniusDirectLimitMap_injective`・`frobeniusDirectLimitMap_surjective` を適用した。核・像の条件を入力仮定に残していない。主定理が BST13 Lemma 3.9 の H⁰ に用いる Čech 版であり、Stacks 30.2.6 の比較を形式化しないことを明記している。再帰深度の展開は成分補題で分け、上限は変更していない。

**到達点**：斉次標準開の実際の環から作る切断代数 B について、B/IB と閉厚化の切断代数の Frobenius 比較が閉じた。未完は、Proj の構造層の切断代数との環同型、F7 の有限環の四角形への接続、F8 の増大全複体と停止点の自然性の検収。F7 全体や 2f の停止点とはしない。

2f 累計は **125 モジュール・7,961 行（登録込み 8,162 行）**。残りの暫定見込みは 3,000〜7,500 行、停止基準 18,000 行以内。最終出力の型も変更していない。

## F7：斉次局所化と Proj の切断代数の比較（ffbfb0c17、11-13）

新規 3 モジュール・11 公開宣言・201 行（登録込み 207 行）。対象ビルド 3,261 jobs、直接 importer 4,674 jobs 成功。別実行の監査は **9,720 宣言・標準三公理のみ**。共有鍵 `--wait 3600` を各ビルド・監査の間だけ取得し、待ちは一つ。main の全ビルドは行っていない。

登録モジュール：`CechAlgebraNonemptyEqualizerEquiv`、`ProjectiveProjCechSectionAlgebraEquiv`、`ProjectiveCechSectionComparison`（すべて `SerrePositivity.AlgebraicGeometry`）。

| 宣言 | 主張 |
| --- | --- |
| `fullAlgebraCechNonemptyCochainsEquiv` | 非空交叉の代数同型を正の長さのタプルの切断族に適用する代数同型。 |
| `fullAlgebraCechNonemptyCochainsEquiv_face` | その比較は二つの面の制限と可換。 |
| `fullAlgebraCechNonemptyCochainsEquiv_mem_iff` | その比較は適合条件を保ち、かつ反映する。 |
| `fullAlgebraCechNonemptyEqualizerEquiv` | 非空交叉だけの自然な代数同型から得る適合切断代数の同型。 |
| `fullAlgebraCechNonemptyEqualizerEquiv_apply` | 適合切断の比較は、各成分に指定した同型を適用する。 |
| `projectiveProjCechSectionAlgEquiv` | 非空の標準開の交叉上で、斉次局所化と実際の構造層の切断を基底上の代数として同定する。 |
| `projectiveProjCechSectionAlgEquiv_apply` | この代数同型の関数は既存の線形比較と一致する。 |
| `projectiveProjCechSectionAlgEquiv_naturality` | この比較は実際の標準開の制限写像と可換。 |
| `projectiveCechSectionAlgebraEquiv` | 斉次局所化と Proj の構造層から作る適合切断代数の基底上の同型。 |
| `projectiveCechSectionAlgebraEquiv_apply` | 適合切断の同型の成分は実際の標準開への比較。 |
| `projectiveCechSectionAlgebraEquiv_algebraMap` | この比較は四角形の増大写像である基底スカラーを保つ。 |

線形比較が実際の `Proj.awayToSection` と開集合の等式による制限の合成であることから、積と 1 を保つことを確認した。線形性と 1 の保存から基底スカラーの保存を得る。空交叉の係数を同一視せず、長さ一・二のタプルの非空性と制限の自然性だけで適合条件を移した。Čech 版と Stacks 30.2.6 の非形式化の範囲を主比較の docstring に明記。sorry・新しい公理・探索上限の引き上げはない。

**残り**：この同型で有限切断代数の Spec 全射性・中心外の局所全射性を斉次切断代数へ移し、前の閉厚化の Frobenius 比較と有限変更の四角形を合成する。さらに Frobenius 順極限と Čech H⁰ の比較を実際の写像について照合して F7 を閉じ、F8 の増大全複体と停止点の自然性を検収する。今回の代数同型だけを F7 または停止点 2f の完成とはしない。

2f 累計 **128 モジュール・8,162 行（登録込み 8,369 行）**。残りの暫定見込み 3,000〜7,500 行、停止基準 18,000 行以内。最終出力の型は変更していない。

## F7：閉厚化の切断環を右端とする短完全列（831f85f29、11-13）

新規 3 モジュール・9 公開宣言（局所インスタンス・private 補題を除く）・245 行（登録込み 251 行）。対象ビルド 3,352 jobs、直接 importer 4,677 jobs 成功。別実行の公理監査は **9,764 宣言・標準三公理のみ**。共有鍵 `--wait 3600` をビルド・監査の間だけ取り、一つの待ちを維持した。全プロジェクトのビルドは行っていない。

登録モジュール：`ProjectiveHomogeneousFiniteCenterExact`、`ProjectiveHomogeneousClosedCenterExact`、`ProjectiveHomogeneousClosedCenterMaps`（すべて `SerrePositivity.AlgebraicGeometry`）。

| 宣言 | 主張 |
| --- | --- |
| `projectiveHomogeneousSectionAlgebra_surjectiveSpectrum` | 全射な射影構造射の斉次切断代数の Spec は基底の Spec に全射する。 |
| `projectiveHomogeneousSectionAlgebra_localized_surjective` | 中心外で構造射が同型なら、基底から斉次切断代数への写像の素点での局所化は全射。 |
| `projectiveHomogeneousFiniteCenter_exact` | その有限切断代数 B と B/IB による中心の四角形は Frobenius 順極限で短完全。 |
| `projectiveHomogeneousClosedCenterComparison` | B/IB から閉厚化の適合切断環への実際の比較を Frobenius 順極限へ送る。 |
| `projectiveHomogeneousClosedCenterDifference` | 商環側の差写像にその比較を合成し、閉厚化の切断環を右端にする。 |
| `projectiveHomogeneousClosedCenter_exact` | 射影構造射が全射かつ中心外で同型なら、この切断の Frobenius 順極限の列は短完全。 |
| `projectiveHomogeneousClosedCenterBaseMap` | 基底の中心の環から閉厚化の適合切断への実際の環準同型。 |
| `projectiveHomogeneousClosedCenterBaseMap_mk` | 基底の中心の代表元は、閉厚化の切断の同じ基底スカラーへ送られる。 |
| `projectiveHomogeneousClosedCenterDifference_apply` | 完全列の差写像は、元の切断の閉厚化への制限と基底の中心からの射の差に一致する。 |

Spec 全射性は、実際の構造層の切断代数への全射性と、前の束の代数同型の comap の合成から得た。局所全射性は同じ同型の局所化の単射性と、基底スカラーとの可換性で移した。有限変更の完全列の右端に、既存の Rees の核の冪零性・冪の持ち上げから得た全単射を合成した。中心 I と厚化の指数 1 の I^1 は明示的な等式で移送した。差写像の照合は Frobenius 順極限の有限段で計算した。一般的な map_sub の型クラス探索が大きくなった箇所は、環準同型を明示した private 補題に分け、上限を変えずに通した。

**到達点と残り**：切断の Frobenius 順極限で、右端を閉厚化の実際の切断環とする短完全列が閉じた。F7 の指定された型 `H⁰(Cperf(Y))`・`H⁰(Cperf(E))` へは、切断代数の Frobenius 系と各段の Čech H⁰ の自然同型、filtered colimit 比較をつなぐ必要がある。次は整数線形の H⁰ 自然性を使って、`projectiveFrobeniusColimitCechHomologyIso`・`ringDirectLimitIntColimitIso` と同じ実際の写像について照合する。F8 の明示的な増大全複体と、共通細分・底変換等の停止点の自然性の検収も残る。今回を F7 全体または停止点 2f の完成とはしない。

2f 累計 **131 モジュール・8,407 行（登録込み 8,620 行）**。残りの暫定見込み 3,000〜7,500 行、停止基準 18,000 行以内。最終出力 `AugmentedRingCechExact` の型は変更していない。

## F7：切断の Frobenius 順極限と Čech H⁰ の比較（23afd482d、11-13）

新規 3 モジュール・12 公開宣言（private 補題・局所インスタンスを除く）・286 行（登録込み 292 行）。対象ビルド 2,094 jobs、直接 importer 4,680 jobs 成功。別実行の監査は **9,815 宣言・標準三公理のみ**。共有鍵 `--wait 3600` はビルド・監査の間だけ取り、待ちは一つ。探索上限を引き上げず、sorry・新しい公理を追加していない。

登録モジュール：`CechAlgebraIntH0Naturality`、`CechAlgebraFrobeniusSystem`、`CechAlgebraFrobeniusH0`（すべて `SerrePositivity.AlgebraicGeometry`）。

| 宣言 | 主張 |
| --- | --- |
| `fullAlgebraCechEqualizer_int_kernel_iff` | 適合条件は整数係数の Čech の最初の余境界の核に一致する。 |
| `fullAlgebraCechIntKernelEquiv` | 適合切断の整数加群とこの核との同型。 |
| `fullAlgebraCechIntH0Equiv` | 適合切断の加法群と整数係数 Čech H⁰ の同型。 |
| `fullAlgebraCechIntH0Equiv_kernel` | H⁰ から核へ戻すと元の切断族になる。 |
| `fullAlgebraCechIntH0Equiv_naturality` | この H⁰ 比較は整数線形な係数図式の射に自然。 |
| `algebraCech_primeCast` | 基底で p が零なら各交叉の代数で p は零。 |
| `algebraCechEqualizer_primeCast` | 同じ条件から適合切断代数で p は零。 |
| `algebraCechIntFrobeniusSystemMap` | 実際の環の Frobenius 遷移を整数線形な係数図式の射にする。 |
| `algebraCechFrobeniusCoefficientFunctor` | 交叉ごとの Frobenius 遷移を自然数の係数関手にまとめる。 |
| `fullAlgebraCechEqualizerAddMap_frobenius` | この係数 Frobenius が適合切断に誘導する射は、切断環自身の同じ Frobenius。 |
| `algebraCechFrobeniusH0SystemIso` | 切断環の Frobenius 系と、各段の整数係数 Čech H⁰ の系の自然同型。 |
| `algebraCechFrobeniusH0ColimitIso` | Frobenius 係数順極限の Čech H⁰ と、適合切断環の Frobenius 順極限の同型。 |

整数作用について、基底からのスカラー制限と標準の整数倍を明示的に照合した。既存の H⁰ の核の自然性補題には基底環と加群の宇宙を揃えた型があり、整数係数で大きい加群を扱うため、核の包含と homologyπ の自然性の証明を独立した宇宙で private 補題にした。既存の広い依存先は変更していない。各段の Frobenius との可換性を自然同型にまとめ、既存の `projectiveIntCechSequentialHomologyIso` と `ringDirectLimitIntColimitIso` に合成した。主比較は BST13 Lemma 3.8・3.9 の H⁰ に用いる Čech 版と明記し、Stacks 30.2.6 の比較を形式化したとはしていない。

**残り**：一般の代数係数図式について順極限の H⁰ 比較はできた。次はこの同型の係数図式の射に対する自然性を閉厚化の制限について接続し、斉次標準開の係数 Frobenius 系を F6 の `projectiveFrobeniusRingChartDiagram` と照合する。それにより前の短完全列を指定された実際の Čech H⁰ の四角形へ移す。F8 の増大全複体と、共通細分・底変換等の停止点の検収も残る。今回を F7 全体や停止点 2f の完成とはしない。

2f 累計 **134 モジュール・8,693 行（登録込み 8,912 行）**。残りの暫定見込み 3,000〜7,500 行、停止基準 18,000 行以内。最終出力 `AugmentedRingCechExact` の型は変更していない。

## F7：H⁰ 比較の自然性と F6 の環チャートへの接続（4ad55da21、11-13）

新規 3 モジュール・8 公開宣言（private 補題を除く）・211 行（登録込み 217 行）。対象ビルド 3,276 jobs、直接 importer 4,683 jobs 成功。別実行の監査は **9,840 宣言・標準三公理のみ**。共有鍵 `--wait 3600` をビルド・監査の間だけ取得し、待ちは一つ。探索上限の引き上げ・sorry・新しい公理はない。

登録モジュール：`CechAlgebraFrobeniusNaturality`、`CechAlgebraFrobeniusH0ColimitNaturality`、`ProjectiveHomogeneousFrobeniusH0`（すべて `SerrePositivity.AlgebraicGeometry`）。

| 宣言 | 主張 |
| --- | --- |
| `algebraCechIntMap` | 係数代数の実際の射を、スカラー制限した整数加群図式の射にする。 |
| `fullAlgebraCechEqualizerAddMap_intMap` | 整数線形として適合切断に誘導した写像は既存の代数写像と同じ関数。 |
| `algebraCechFrobeniusCoefficientNatTrans` | 係数代数の射が、実際の Frobenius 係数系の自然変換を誘導する。 |
| `algebraCechFrobeniusH0SystemIso_naturality` | 各段の H⁰ 同型は適合切断の実際の写像と係数系の射を比較する。 |
| `algebraCechFrobeniusH0ColimitIso_naturality` | 順極限の Čech H⁰ 比較は係数代数の射に自然で、比較後の射は適合切断環の実際の Frobenius 順極限の射。 |
| `projectiveHomogeneousFrobeniusCoefficientIso` | 多項式加群の標準開係数系と斉次局所化の代数係数系を、同じ Frobenius に沿って同定する。 |
| `projectiveHomogeneousFrobeniusRingCechIso` | F6 の標準開環の複体と、斉次代数係数の Frobenius 順極限の複体の同型。 |
| `projectiveHomogeneousFrobeniusRingCechH0Iso` | F6 と同じ `projectiveFrobeniusRingChartDiagram` の Čech H⁰ と、斉次切断環の Frobenius 順極限の同型。 |

各段の H⁰ の自然性、filtered 余極限の自然性、環の順極限と整数加群の余極限の自然性の三つを合成した。F6 への接続は既存の斉次チャートの線形同型を整数スカラーに制限し、実際の反復 Frobenius との可換性を使う。別の複体を F6 のものと呼んで済ませず、既存の `projectiveFrobeniusRingChartCechIso` を通した明示的な複体同型を作った。主 H⁰ 比較の docstring に Čech 版と Stacks 30.2.6 の非形式化を明記。

**残り**：係数代数図式の射に対する順極限の自然性は閉じた。次は `reesClosedFrobeniusCoefficientNatTrans` と `reesClosedHomogeneousAlgebraProjection` が、今回の `projectiveHomogeneousFrobeniusCoefficientIso` を介して同じ射になることを照合する。その可換性と既存の `reesClosedFrobeniusRingCechIso_projection` で、F6 の閉厚化の H⁰ の射と切断の制限を同定し、前の短完全列を移す。基底側の増大写像も同じ比較と揃える。F8 の増大全複体と、共通細分・底変換等の停止点の自然性の検収が引き続き残る。F7 全体または停止点 2f の完成とはしない。

2f 累計 **137 モジュール・8,904 行（登録込み 9,129 行）**。残りの暫定見込み 3,000〜7,500 行、停止基準 18,000 行以内。最終出力 `AugmentedRingCechExact` の型は変更していない。

## F7：閉厚化の実際の H⁰ の射の照合（a9dc69619、11-13）

新規 2 モジュール・4 公開宣言（局所インスタンスを除く）・137 行（登録込み 141 行）。対象ビルド 3,280 jobs、直接 importer 4,685 jobs 成功。別実行の公理監査は **9,849 宣言・標準三公理のみ**。共有鍵 `--wait 3600` をビルド・監査の間だけ取得し、待ちは一つ。探索上限・最終出力の型は変更せず、sorry・新しい公理を追加していない。

登録モジュール：`ReesHomogeneousFrobeniusCoefficientComparison`、`ReesHomogeneousFrobeniusH0Comparison`（ともに `SerrePositivity.AlgebraicGeometry`）。

| 宣言 | 主張 |
| --- | --- |
| `projectiveHomogeneousFrobeniusCoefficientIso_projection` | F6 の閉厚化の実際の係数射と斉次代数係数の射影は、Frobenius 系の比較を介して可換。 |
| `projectiveHomogeneousFrobeniusCoefficientColimitIso_projection` | 同じ可換性が係数系の順極限に成り立つ。 |
| `projectiveHomogeneousFrobeniusRingCechIso_projection` | F6 の標準開環の複体と斉次代数係数の複体の比較は、実際の閉厚化の射と可換。 |
| `projectiveHomogeneousFrobeniusRingCechH0Iso_projection` | F6 の閉厚化の射が Čech H⁰ に誘導する写像は、切断の実際の制限が誘導する Frobenius 順極限の写像と比較同型を介して一致する。 |

各段の各標準開で、既存の斉次チャートの比較とその逆を打ち消した。係数系の等式を余極限と全タプル複体に送り、F6 の環チャートの定義中の比較とその逆も打ち消した。H⁰ の段ではこの複体の等式と、前の束の一般の代数係数図式の自然性を合成した。表示の異なる homologyMap と homologyFunctor.map を無理に展開せず、等式の合成と結合則で接続した。

**残り**：F6 の正次数と F7 の H⁰ で使う閉厚化の射が同じであることが閉じた。次は `projectiveHomogeneousClosedCenter_exact` の短完全列をこの H⁰ 比較で移し、基底および基底の中心からの増大写像を同じ比較と揃える。続いて F8 の明示的な増大全複体と、共通細分・底変換等の停止点の自然性を検収する。F7 全体や停止点 2f の完成とはしない。

2f 累計 **139 モジュール・9,041 行（登録込み 9,270 行）**。残りの暫定見込み 3,000〜7,500 行、停止基準 18,000 行以内。

## 11-13 夜：H⁰ の差写像の保存則の分離（85a68fc72）

調整役の指示に従い、差写像を `ProjectivePerfCechH0SquareData` の関数の def に固定した。零保存は `ProjectivePerfCechH0SquareZero` の別宣言として単独の対象ビルドを通した（3,378 jobs）。探索上限・heartbeat は変更していない。main 凍結中の夜の指示に従い、大きい監査と AlgebraicGeometry 全体の importer ビルドは実行していない。ルートへの登録と監査は未実施。

検証済みの独立補題の型（変数・仮定は同ファイルの一般の射影標準開の設定）：
```lean
projectivePerfCechH0Difference_map_zero :
  projectivePerfCechH0Difference (ι := ι) G I p hp hR hA 0 = 0
```

加法保存は別の宣言として下書き `ProjectivePerfCechH0SquareLaws` に分離した。予定する型は次のとおりで、まだ検証を通っていない。
```lean
projectivePerfCechH0Difference_map_add
  (x y : projectivePerfCechH0 (ι := ι) G p hp hR hA ×
    FrobeniusDirectLimit (R ⧸ (I ^ 1)) p hp
      (frobeniusQuotientPrimeCast p hR (I ^ 1))) :
  projectivePerfCechH0Difference (ι := ι) G I p hp hR hA (x + y) =
    projectivePerfCechH0Difference (ι := ι) G I p hp hR hA x +
    projectivePerfCechH0Difference (ι := ι) G I p hp hR hA y
```

unfold は保存則の補題の中に限定。加法保存では中間の切断環の Frobenius 順極限の Add の推論が依然上限に達している。零保存の成功を加法保存や H⁰ の短完全列の成功とは扱わない。加法保存、短完全列への適用、F8 と自然性の検収は未完。未検証の三ファイルは作業木に残し、このコミットに含めていない。

## 11-13 夜：加法保存の中間補題の分離（af450ff55）

`ProjectiveHomogeneousClosedCenterAdd`（3,353 jobs）と `ProjectivePerfCechH0EquivLaws`（3,380 jobs）の独立対象ビルドが成功。大きい監査・ルート登録は夜の指示に従い保留。探索上限・heartbeat・再帰上限は変更していない。

以下で B は斉次切断代数、C は閉厚化の斉次切断代数、P は FrobeniusDirectLimit、H は F6 の複体の H⁰、e は既存の H⁰ 比較、g は既存の閉厚化の差写像とする。型を省略記法で記す（完全な Lean 型は各宣言にある）。

- `projectiveHomogeneousClosedCenterDifference_add (x y : P(B) × P(R/I)) : g (x+y) = g x + g y`。
- `projectivePerfCechH0Equiv_symm_apply (z : P(B)) : e.symm z = iso.inv.hom z`。逆加法同型と逆線形写像の関数としての一致。
- `projectivePerfCechH0Iso_inv_add (z w : P(B)) : iso.inv.hom (z+w) = iso.inv.hom z + iso.inv.hom w`。

H⁰ の差写像全体の `projectivePerfCechH0Difference_map_add` は未検証。中間補題の単独の成功を全体の成功とはしない。定義の等式による照合を三段に分け、さらに一般の逆比較の表示を独立補題にしたが、閉厚化へ代入した最後の型照合で最大再帰深度に達する。下書きは `ProjectivePerfCechH0SquareLaws` に保持し、未検証の Lean をコミットしていない。零保存の独立補題（85a68fc72）は引き続き検証済み。

## 11-13 夜：零・加法の独立保存則の検証完了（d7f39c479）

固定した関数の def `projectivePerfCechH0Difference`（85a68fc72）を変更せず、零保存と加法保存を別の宣言として検証した。零保存の対象ビルドは 3,378 jobs、今回の加法保存の対象ビルドは 3,381 jobs 成功。共有鍵 `--wait 3600` を使用。大きい監査・ルート登録・直接 importer 全体の検証は夜の指示に従い保留。

変数 R, A, ι, G, I, p, hp, hR, hA とインスタンスは `ProjectivePerfCechH0SquareData` と同じ。二つの独立宣言の完全な主張の型は以下。

```lean
projectivePerfCechH0Difference_map_zero :
  projectivePerfCechH0Difference (ι := ι) G I p hp hR hA 0 = 0

projectivePerfCechH0Difference_map_add
  (x y : projectivePerfCechH0 (ι := ι) G p hp hR hA ×
    FrobeniusDirectLimit (R ⧸ (I ^ 1)) p hp
      (frobeniusQuotientPrimeCast p hR (I ^ 1))) :
  projectivePerfCechH0Difference (ι := ι) G I p hp hR hA (x + y) =
    projectivePerfCechH0Difference (ι := ι) G I p hp hR hA x +
      projectivePerfCechH0Difference (ι := ι) G I p hp hR hA y
```

配置：零保存は `ProjectivePerfCechH0SquareZero`、加法保存は `ProjectivePerfCechH0SquareLaws`。いずれも関数の def の unfold は補題の証明内だけ。加法保存は中央項の比較の加法保存、単独検証済みの切断環側の加法保存、逆 H⁰ 比較の加法保存を合成した。最後の逆比較の補題にすべての引数を明示し、最後だけ `convert ... using 1` で型照合を分離すると通った。探索上限・heartbeat・再帰上限は一切引き上げていない。sorry・admit・新しい公理は追加していない。

これで調整役の「零・加法の保存を別宣言として検証し、型を報告する」依頼は完了。2f 全体は未完。次はこの二つの保存則で差の加法準同型を組み、H⁰ の短完全列の下書きへ適用する。基底の増大写像、F8 と停止点の自然性の検収も残る。未検証の `ProjectivePerfCechH0Square`・`ProjectivePerfCechH0SquareMaps` は作業木に保持している。

## 11-14：独立保存則から差の加法準同型へ（a0f516a1a）

`ProjectivePerfCechH0DifferenceHom` の小さい対象ビルド（3,382 jobs）成功。検証済みの零・加法保存をフィールドに指定し、固定した差写像を台の関数とする加法準同型を作った。二つの新しい宣言：

```lean
projectivePerfCechH0DifferenceHom :
  projectivePerfCechH0 (ι := ι) G p hp hR hA ×
    FrobeniusDirectLimit (R ⧸ (I ^ 1)) p hp
      (frobeniusQuotientPrimeCast p hR (I ^ 1)) →+
  projectivePerfCechH0 (ι := ι)
    (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
    (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A)))

projectivePerfCechH0DifferenceHom_apply (b : _) :
  projectivePerfCechH0DifferenceHom (ι := ι) G I p hp hR hA b =
    projectivePerfCechH0Difference (ι := ι) G I p hp hR hA b
```

保存則の再証明・探索上限の変更はない。共有鍵 --wait 3600 を対象ビルドの間だけ取得。大きい監査とルート登録は保留。2f は未完。H⁰ の短完全列の移送では、比較と逆比較の打ち消しに渡す元を明示して convert すると定義上の等式だけに分離できたが、その等式を一度に rfl で閉じると再帰上限に達する。独立の適用補題を使って照合をさらに小さくする。短完全列、増大写像、F8 と最終検収は引き続き必要。未検証の二ファイルは作業木に保持している。

## 11-14：F6 の複体の H⁰ における短完全列（e218ff2ea）

`ProjectivePerfCechH0Square` の対象ビルドが成功（3,383 jobs）。新規公開宣言は `projectivePerfCechH0_square_exact`：

```lean
Function.Injective (projectivePerfCechH0Pair (ι := ι) G I p hp hR hA) ∧
Function.Exact (projectivePerfCechH0Pair (ι := ι) G I p hp hR hA)
  (projectivePerfCechH0Difference (ι := ι) G I p hp hR hA) ∧
Function.Surjective (projectivePerfCechH0Difference (ι := ι) G I p hp hR hA)
```

仮定は Noether 基底、有限生成の斉次代数、標準開の被覆条件、構造射の全射性と中心外の同型、基底・構造環で p が零であること。切断環側の短完全列に、中央項の積の加法同型と閉厚化の H⁰ 比較を適用した。最後の比較の打ち消しは元をすべて指定して convert し、残った定義上の等式を固定定義および `AddMonoidHom.coe_mk`・`ZeroHom.coe_mk` のみで簡約すると閉じた。探索上限・heartbeat・再帰上限を引き上げていない。

共有鍵 --wait 3600 を対象ビルドの間だけ使用。大きい監査・ルート登録・下流ビルドは未実施。実際の差写像の表示の下書き `ProjectivePerfCechH0SquareMaps` は再帰上限に達し、まだ未検証。今回の短完全列では差写像は固定した切断比較を介して定義したものであり、F6 の H⁰ 制限との差の表示および基底側の増大写像との照合を完了したとはしない。

2f 全体は未完。残りは差写像の実際の制限との表示、基底と基底の中心の増大写像との照合、F8 の増大全複体、共通細分・底変換等の停止点の検収と最終報告。最後の型照合で使えなかった独立適用公式の試行は scheme-drafts に退避した。固定した差写像の def は変更していない。

## 11-14：H⁰ の差の表示に使う独立評価補題（49bbffe22）

`ProjectivePerfCechH0Evaluation` の対象ビルドが成功（3,381 jobs、追加補題を含む後続対象でも同モジュールは成功）。公開宣言と主張を記す。ここで e は `projectiveHomogeneousFrobeniusRingCechH0Iso`、P(B) は切断環の Frobenius 順極限、H は F6 の同じ複体の H⁰。

- `projectivePerfCechH0CenterEquiv_apply (b : H) (c : P(R/I)) : centerEquiv (b,c) = (e.hom.hom b,c)`。
- `projectivePerfCechH0Iso_inv_sub (z w : P(B)) : e.inv.hom (z-w) = e.inv.hom z - e.inv.hom w`。
- `projectivePerfCechH0Iso_inv_hom (b : H) : e.inv.hom (e.hom.hom b) = b`。
- `projectivePerfCechH0Iso_inv_congr (z w : P(B)) (h : z=w) : e.inv.hom z = e.inv.hom w`。
- `projectivePerfCechH0Iso_inv_eq (b : H) (z : P(B)) (h : e.hom.hom b=z) : e.inv.hom z=b`。

大きい監査・ルート登録は未実施。共有鍵 --wait 3600 を小さい対象ビルドの間だけ取得し、上限を一切引き上げていない。

差写像の表示の下書きは未検証。conv の最後の引数を選択して変換することで、中央項の評価、切断環側の差の公式、逆比較の差の保存が適用できた。自然性の合成射は `ModuleCat.hom_comp` と `LinearMap.comp_apply` で浅く正規化して、逆比較の評価補題に接続できた。最後の差の等式を作る箇所ではまだ isDefEq の上限に達する。旧証明は切断環側で比較していたが、新証明は H⁰ 側なので、基底の中心の項も逆 H⁰ 比較で移す必要があることを見つけ、その不足は下書きで修正済み。次はこの基底側の項を型を明示した写像に束ね、最終の差の照合を軽くする。

2f の未完範囲は、実際の差の表示、基底側の増大写像、F8 の増大全複体、自然性・最終検収。今回の評価補題を F7 全体または停止点 2f の完成とはしない。

## 11-14：H⁰ の差と実際の閉厚化の制限の一致（59cd5fa58）

新規 2 モジュール・2 公開宣言・99 行。対象ビルド 3,386 jobs 成功（非推奨の補題名を現行名へ直した後にも成功）。共有鍵 --wait 3600 を対象ビルドの間だけ使用。探索上限・heartbeat・再帰上限は変更していない。大きい監査・ルート登録は引き続き保留。

- `projectivePerfCechH0CenterClass`：基底の中心の Frobenius 順極限から、閉厚化の F6 の複体の H⁰ への写像。実際の `projectiveHomogeneousClosedCenterBaseMap` の Frobenius 順極限に既存の逆 H⁰ 比較を合成する。始域・終域を明示した def。
- `projectivePerfCechH0Difference_apply`：移送した差写像が、F6 の実際の `reesClosedFrobeniusRingCechMap` の H⁰ の射と基底側の上記の写像の差であること。

主張の型（変数・インスタンスは射影標準開の既存の設定）：
```lean
projectivePerfCechH0Difference_apply
  (b : projectivePerfCechH0 (ι := ι) G p hp hR hA)
  (c : FrobeniusDirectLimit (R ⧸ (I ^ 1)) p hp
    (frobeniusQuotientPrimeCast p hR (I ^ 1))) :
  projectivePerfCechH0Difference (ι := ι) G I p hp hR hA (b,c) =
    (HomologicalComplex.homologyMap
      (reesClosedFrobeniusRingCechMap (ι := ι) I G p hp hR hA 1) 0).hom b -
      projectivePerfCechH0CenterClass (ι := ι) G I p hp hR hA c
```

中央項と切断環側の差の書き換えは、conv の最後の引数を選択して内側だけで行った。自然性の合成射の評価を `ModuleCat.hom_comp`、`LinearMap.comp_apply`、`ModuleCat.hom_ofHom`、`AddMonoidHom.coe_toIntLinearMap`、`RingHom.toAddMonoidHom_eq_coe`、`AddMonoidHom.coe_ofClass` で正規化した。最後は名前と型を固定した基底側の項を使って等式の合同性を適用し、convert で残る表示差を分離して閉じた。固定した差写像の def は変更していない。

これで短完全列の右側の写像は F6 の実際の閉厚化の H⁰ の制限と揃った。2f は未完。残りは基底および基底の中心の増大写像を実際の零次コサイクルと照合すること、F8 の明示的な増大全複体、共通細分・底変換等の停止点の自然性の検収、登録・監査・最終報告。

## 11-14：増大写像の組と有限段の零次スカラー（78164dd73）

新規 2 モジュール・6 公開宣言・97 行。`ProjectivePerfCechH0PairEvaluation`（3,382 jobs）と `ProjectiveHomogeneousScalarCocycle`（3,383 jobs）の対象ビルド成功。共有鍵 --wait 3600 を各対象ビルドの間だけ使用。上限を変更せず、大きい監査・ルート登録は行っていない。

- `projectivePerfCechH0ScalarClass`：基底の Frobenius 順極限から、切断代数へのスカラー写像の順極限と逆比較を通して F6 の複体の H⁰ に送る写像。
- `projectivePerfCechH0Pair_apply`：左側の組は、このスカラーの H⁰ 類と基底の中心への実際の商写像の順極限の組。
- `projectivePerfCechH0ScalarClass_of`：有限段 n の基底の元 r は、同じ段 n の切断代数の algebraMap r の順極限の類を逆比較で H⁰ に送ったもの。
- `projectivePerfCechH0Pair_snd_of`：組の中心側の成分は、有限段で実際の商の元 Ideal.Quotient.mk (I^1) r を取る。
- `projectiveHomogeneousSectionAlgebra_algebraMap_apply`：切断代数の algebraMap r は各標準開で同じ algebraMap r を取る。
- `projectiveHomogeneousScalarCechIntH0_cocycle`：有限段のスカラーの Čech H⁰ 類を核表示に戻すと、各標準開で同じスカラーを取る実際の零次コサイクルとなる。

最後の主張の型：D = projectiveHomogeneousChartAlgebraDiagram G とすると、
```lean
((fullCechH0KernelIso (algebraCechIntDiagram D)).hom.hom
  (fullAlgebraCechIntH0Equiv D (algebraMap R
    (projectiveHomogeneousSectionAlgebra (ι := ι) G) r))).val t =
  algebraMap R (D.obj (cechTupleSupport t)) r
```

2f は未完。有限段での実際のスカラーのコサイクル表示は閉じたが、順極限の H⁰ 比較の有限段からの標準写像との可換性を明示し、今回の ScalarClass を順極限後の複体の増大写像と同定する必要がある。既存の `projectiveIntCechSequentialHomologyIso` と `ringDirectLimitIntColimitIso_of` を同じ標準写像に沿って照合する。基底の中心についても同じ接続が必要。F8 と共通細分・底変換等の最終検収、登録・監査・最終報告は引き続き残る。

## 11-14：filtered 比較と有限段の標準写像（c9430d14d）

新規 2 モジュール・6 公開宣言・105 行。`ProjectiveCechFilteredInclusions`（1,898 jobs）と `ProjectiveFilteredHomologyInclusions`（1,668 jobs）の対象ビルド成功。共有鍵 --wait 3600 を対象ビルドの間だけ取得。大きい監査・ルート登録は保留、探索上限は変更していない。

- `projectiveCechFilteredComplexIso_ι`：有限段の係数の標準写像が誘導する Čech 複体の射を canonical な filtered 比較に合成すると、複体の余極限の標準写像になる。
- `projectiveCechFilteredComplexIso_inv_ι`：逆比較も同じ標準写像と可換。
- `projectiveCechFilteredHomologyIso_ι_factor`：有限段の Čech H の射と比較の合成を、複体の余極限の H の標準写像と `projectiveFilteredComplexHomologyIso` の合成へ分離する。
- `projectiveFilteredColimitInclusion`：評価関手から余極限関手への自然変換。各成分は実際の colimit.ι。
- `projectiveFilteredShortComplexHomologyInclusion`：短複体の H の比較は、この評価から余極限への標準写像と可換。
- `projectiveFilteredShortComplexHomologyIso_ι`：短複体の図式の比較について、有限段の標準写像との整合性を示す。評価した短複体の H と図式の各段の H の既存の比較を型に明示している。

最後の型で S = projectiveFilteredShortComplexDiagram D とすると、
```lean
ShortComplex.homologyMap (S.mapNatTrans (projectiveFilteredColimitInclusion j)) ≫
  (projectiveFilteredShortComplexHomologyIso D).hom =
  (S.mapHomologyIso ((evaluation J (ModuleCat R)).obj j)).hom ≫
  (projectiveFilteredShortComplexHomologyDiagramIso D).hom.app j ≫
  colimit.ι (D ⋙ ShortComplex.homologyFunctor (ModuleCat R)) j
```

`ι_preservesColimitIso_hom/inv` と `ShortComplex.homologyMap_mapNatTrans` を再利用した。新たなコホモロジーや余極限を定義して置き換えていない。結合の表示と局所名は等式の合成および限定した dsimp で揃えた。

2f は未完。次は複体の sc 比較を有限段からの射と照合し、今回の短複体の結果を `projectiveFilteredComplexHomologyIso` へ通す。その後 ULift ℤ と AsSmall ℕ の比較の標準写像との可換性を合成し、Frobenius の各段からの H⁰ 比較を得る。F8・停止点の自然性の検収・登録・監査・最終報告も引き続き必要。

## 11-14：複体の H と Čech H の canonical な標準写像（6039dfe45）

新規 2 モジュール・5 公開宣言（private の逆四角形の補題を除く）・131 行。`ProjectiveFilteredComplexStage`（1,669 jobs）と `ProjectiveCechFilteredHomologyInclusions`（1,901 jobs）の対象ビルド成功。共有鍵 --wait 3600 をビルドの間だけ取得し、上限は変更していない。大きい監査・ルート登録は未実施。

- `projectiveFilteredComplexStageIso`：短複体の図式を有限段で評価したものと、その段の複体の短複体との明示的な同型。
- `projectiveFilteredComplexShortComplexIso_ι`：有限段からの短複体の標準写像と複体の標準写像は、既存の短複体の余極限比較を介して一致する。
- `projectiveFilteredComplexHomologyIso_ι`：この可換性を H へ送り、前の短複体の H の標準写像の結果を合成した公式。評価と H の比較を型に明示。
- `projectiveFilteredComplexHomologyIso_ι_canonical`：評価比較を打ち消して、複体の既存の filtered H 比較が有限段からの H の標準写像を保つことを示す。
- `projectiveCechFilteredHomologyIso_ι`：既存の Čech H の filtered 比較について、有限段からの標準写像の公式を得る。

最後の主張の型：
```lean
(HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℕ) q).map
    (fullCechComplexMap (colimit.ι D j)) ≫
  (projectiveCechFilteredHomologyIso D q).hom =
  colimit.ι (D ⋙ fullCechComplexFunctor ⋙
    HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℕ) q) j
```

各次数の評価関手の `ι_preservesColimitIso_inv`、短複体の H の自然性、前の束の標準写像の公式を使った。最後の表示差は逆同型の表記、関手の obj/map、結合則と限定した dsimp、および関手の恒等射の法則を等式として合成することで揃えた。既存の比較を別の任意の同型で置き換えていない。

2f は未完。この公式を整数係数への ULift ℤ の移送と自然数の添字の AsSmall ℕ の移送に通し、Frobenius 系の有限段の標準写像との H⁰ 比較へつなぐことが次の接続。その後、基底・基底の中心の実際の増大写像と同定し、F8 の全複体と停止点の自然性を検収する。登録・監査・最終報告も残る。

## 11-14：整数係数・自然数添字の標準写像と有限段のスカラー類

数学コミット **8f59dba31・19b4efa71・71230d717**。新規 7 モジュール・9 公開宣言・352 行。以下の対象ビルドが成功した。共有鍵 `--wait 3600` を各ビルドの間だけ使用し、待ちは一つ。heartbeat・再帰上限・探索上限は引き上げていない。

| モジュール | 検証 |
|---|---|
| `ColimitInclusionTransport` | 単独の対象ビルド 687 jobs 成功。 |
| `ProjectiveCechIntFilteredInclusions` | 単独の対象ビルド 1,917 jobs 成功。 |
| `ProjectiveCechIntSequentialInclusions` | 後続を含む対象ビルド 2,102 jobs、および 3,393 jobs の中で成功。 |
| `CechAlgebraFrobeniusH0Inclusions` | 対象ビルド 2,102 jobs、および未使用 simp 引数を除いた後の 3,393 jobs の中で成功。 |
| `CechAlgebraFrobeniusH0Stage` | 単独の対象ビルド 2,103 jobs、逆向きの公式を追加した後の 3,393 jobs の中で成功。 |
| `ProjectiveHomogeneousFrobeniusH0Stage` | 対象ビルド 3,393 jobs 成功。 |
| `ProjectivePerfCechH0CenterStage` | 対象ビルド 3,395 jobs 成功。 |

宣言と主張：

- `colimitInclusion_composition`：有限段の標準写像を保つ二つの比較を合成すると、合成関手についても標準写像を保つ。
- `colimitInclusion_natIso`：自然同型で移送した余極限比較も有限段の標準写像を保つ。
- `projectiveIntCechFilteredHomologyIso_ι`：既存の整数係数 Čech H の filtered 比較は、有限段からの H の射を同じ段の標準写像へ送る。
- `projectiveIntCechSequentialHomologyIso_ι`：AsSmall ℕ への添字移送を含む既存の順極限比較も、各自然数段の標準写像を保つ。
- `algebraCechFrobeniusH0ColimitIso_ι`：Frobenius 系の各段からの Čech H⁰ の射を、切断環の系の標準写像と各段の H⁰ 比較で表示する。
- `algebraCechFrobeniusH0ColimitIso_stage`：有限段の適合切断の Čech H⁰ の像は、切断環の Frobenius 順極限の同じ段の標準元になる。
- `algebraCechFrobeniusH0ColimitIso_inv_of`：同じ公式を比較の逆向きで述べ、標準元の逆像を有限段の Čech H⁰ の射で表示する。
- `projectivePerfCechH0ScalarClass_stage`：実際の標準開環の Čech H⁰ のスカラー類は、有限段の斉次標準開のスカラー類を順極限へ送り、F6 の実際の複体との比較で移したものである。
- `projectivePerfCechH0CenterClass_of_mk`：基底の中心の有限段の代表元の H⁰ 類は、閉厚化上の同じスカラーの H⁰ 類と一致する。

既存の比較同型を別の同型に置き換えていない。ULift ℤ への係数移送では、余極限を保つ関手の canonical な比較、前の束の Čech H の比較、係数の制限を合成し、既存の自然同型の成分と照合した。AsSmall ℕ では `Final.ι_colimitIso_inv/hom` を用いた。大きい同型全体の change は heartbeat に達したが、成分の hom を先に取り出し、必要な標準写像だけを change し、残りを等式の合成で結ぶと通常の上限で通った。中心側の深い change は再帰上限に達したが、関数へ渡す最後の元だけを conv で書き換えると通った。

`projectiveHomogeneousScalarCechIntH0_cocycle` と今回の `projectivePerfCechH0ScalarClass_stage` により、有限段の各標準開上のスカラーから、余極限の比較を経たスカラー類までの接続が得られた。中心の商の元は代表元を持つため、中心側も `projectivePerfCechH0CenterClass_of_mk` と閉厚化へ適用した同じ stage 公式で扱える。ただし、比較の逆を含むこの表示を、実際の標準開環の零次コサイクルの増大写像へ直接同定する最後の照合はまだ必要である。F8 の明示的な増大全複体、共通細分・底変換等の停止点の自然性の検収、登録・監査・最終報告も未完。**停止点 2f の完成ではない。**

規模：2e 数学停止点 `bf9767cdc` からの新規コミット済み本体を数え、**163 モジュール・10,250 行**。入口 `AlgebraicGeometry.lean` の既存の追加 263 行込みで **10,513 行**。未検証の下書きは含めない。残りの暫定見込みは **2,500〜6,500 行**（増大写像の最終照合、F8、射に自然な比較の検収と不足の補題）。停止基準 18,000 行以内を見込むが、上端へ近づく場合は再測定して報告する。大きい監査・ルート登録・ルートと下流の全ビルドは凍結中の指示に従い未実施。今回の宣言数を公理監査の宣言数とは扱わない。

## 11-14：実際のスカラー増大写像と、F8 の明示的な増大項付き cone

数学コミット **85375dd57・1fcfe80c2・e52d3c286**。前の報告から新規 10 モジュール・21 公開宣言・607 行。既存 2 ファイルでは基底環と加群の宇宙を分離しただけ（各 2 行変更）。新しい公理・sorry・admit を加えず、探索・heartbeat・再帰上限も変更していない。共有鍵 `--wait 3600` を対象ビルドの間だけ使用した。

宣言と主張：

- `fullCechH0KernelIso_naturality_apply`：既存の H⁰・核の自然性をタプルごとに評価すると、元の係数写像の式になる。
- `algebraCechFrobeniusH0ColimitIso_inv_of_cocycle`：各有限段の切断に対応する H⁰ 類の零次コサイクルは、各交叉の係数順極限への実際の標準像。
- `projectiveChartFrobeniusRingColimitIso_ι`：標準開の既存の余極限比較は、有限段からの射を環の系の標準写像へ送る。
- `projectiveChartFrobeniusRingColimitIso_stage`：有限段の元の像は、実際の斉次局所化の環の同じ段の Frobenius 標準元。
- `projectiveHomogeneousFrobeniusChartColimitIso`：実際の標準開環の図式と斉次代数係数の順極限の図式の、既存の比較からの合成同型。
- `projectiveHomogeneousFrobeniusRingCechIso_inv`：既存の複体比較の逆が、上の係数図式の比較の逆から誘導されることの等式。
- `projectiveHomogeneousFrobeniusChartColimitIso_stage`：斉次代数係数の有限段の元は実際の標準開環の同じ Frobenius 標準元へ移る。
- `projectivePerfCechH0ScalarClass_of_cocycle`：有限段のスカラー H⁰ 類の零次コサイクルは、各標準開の実際のスカラーの像。
- `projectivePerfCechH0ScalarClass_cocycle`：同じ公式を Frobenius 順極限の任意の元へ拡張したもの。
- `projectivePerfCechScalarAugmentation`：各標準開への実際のスカラー環準同型の Frobenius 順極限から作る零次コチェインへの線形写像。定義に H⁰ 比較やその逆を含めない。
- `projectivePerfCechH0ScalarClass_augmentation`：既存のスカラー H⁰ 類の零次コサイクルと、上の実際の増大写像の一致。
- `projectivePerfCechScalarAugmentation_cycle`：実際の増大写像の像は零次コサイクル。
- `cechCycles_lift_of_homology_surjective`：短複体の H の全射性から、目標のサイクルを境界を除いて持ち上げる。
- `cechCycles_boundary_of_homology_injective`：H の単射性から、境界へ移るサイクルを元の境界へ戻す。
- `cechRefinementCone_cycle_boundary_of_homology`：H⁰ の全射性と正次数の H の全単射性から、既存の cone の各正次数サイクルは境界。
- `cochainComplexOf_acyclic_of_injective_exact`：指定した微分の最初が単射で、隣り合う微分がすべて完全なら、`CochainComplex.of` の複体は Mathlib の `Acyclic`。
- `augmentedCechConeTerm`：増大項、元の複体の零次項、以後の二つの項の直積という、増大項付き cone の明示的な各項。
- `augmentedCechConeDifferential`：増大項では指定した写像、その先は既存の cone の微分という全微分。
- `augmentedCechConeDifferential_squared`：増大写像がサイクルへ入るなら、全微分の二乗は零。
- `augmentedCechCone`：上の項と微分で構成した増大項付き全複体。
- `augmentedCechCone_acyclic`：増大項の単射性・零次での完全性、H⁰ の全射性、正次数の H の同型性から、構成した全複体が `Acyclic`。

検証：`CechAlgebraFrobeniusH0Cocycle` 2,105 jobs、`ProjectiveChartFrobeniusRingStage` と既存の直接 importer `CechAlgebraH0Naturality` の束 3,248 jobs、`ProjectiveHomogeneousFrobeniusChartStage` 3,278 jobs、`ProjectivePerfCechH0ScalarCocycle` 3,397 jobs、任意の元への公式と `ProjectivePerfCechScalarAugmentation` の束 3,399 jobs の対象は成功。`CechHomologyCycleLifting` は修正後の独立対象 1,606 jobs 成功。`CechConeHomologyExactness` および変更した `CechRefinementCone` の既存の直接 importer 三本（`CechRefinementConeExactness`・`CechRefinementConeMap`・`CechRefinementConeHomology`）の束 1,871 jobs 成功。`AugmentedCechCone` 1,861 jobs 成功。FullCechH0KernelNaturality の直接 importer は新規 Evaluation と既存の IntH0Naturality・H0Naturality をすべて確認した。大きい監査・ルート登録・ルートと下流の全ビルドは未実施。

宇宙：`FullCechH0KernelNaturality` の二宣言と `CechRefinementCone` の既存の定義・補題について、環の宇宙を係数加群の宇宙から分離した。ℤ は Type 0 のまま、係数加群は任意の宇宙で扱える。主張や微分の式は変えていない。

**未完の接続**：基底側の増大写像は実際の各標準開の写像と同定できた。中心側は前の束の代表元の公式に今回のコサイクル公式を適用し、中心の実際の増大写像としてまとめる必要がある。その後 C(Y) の零次項に Perf(R/I) を付けた複体と C(E) の間の差の射を作る。今回の augmentedCechCone に Perf(R) を増大項として渡し、F7 の H⁰ の短完全列で単射性・最初の完全性・H⁰ の全射性を、F6 で正次数の同型性を供給する。**今回の一般判定を実際のブローアップ四角形の F8 の完成とは扱わない。** 共通細分・底変換等の停止点の自然性の検収、登録・監査・最終報告も必要で、停止点 2f は未到達。

2f のコミット済み新規本体は **173 モジュール・10,857 行**（2e 数学停止点 bf9767cdc からの新規本体、未検証の下書きを除く）。既存の入口の追加 263 行を含めて **11,120 行**。残りの暫定見込みは **2,000〜6,000 行**。上端でも 18,000 行以内だが、中心の増大写像・F8 の実際の適用・自然性の検収を追って再測定する。

## 11-14：F8 の実際の射影中心の四角形の全複体の acyclicity

数学コミット **aeff8eb47・c3a353de9・a6de086d4**。新規 13 モジュール・42 公開宣言・997 行。F8 の数学的な核となる **実際の全複体の acyclicity** が通った。停止点 2f 全体の検収はまだで、自然性の接続と登録・監査・最終報告を残す。

出口：
```lean
projectivePerfCech_blowupSquare_acyclic :
  (projectivePerfCechBlowupSquareTotalComplex (ι := ι) G I p hp hR hA hspan).Acyclic
```

仮定は Noether 基底 R、有限な変数の多項式環上の有限生成斉次代数 A、標準開が被覆する hspan、Proj G の構造射の全射性と中心外での同型、p の素数性と R・A での零化。F6 の正次数の同型性と F7 の H⁰ の短完全性を証明済みの宣言から供給しており、完全性・H の同型性・核の評価・像の安定化を追加仮定として残していない。零次は Perf(R)、一次は C(Y)⁰ × Perf(R/I)、以後は C(E) と C(Y) の項の直積。微分は各標準開の実際の環準同型からのスカラー、実際の商、実際の閉厚化への制限と差である。空の中心・空の標準開・零環を除外する仮定は加えていない。

宣言と主張（今回の全件）：

- `fullAlgebraCechSectionEvaluation`：適合切断の部分代数を指定した零次タプルの標準開で評価する代数準同型。
- `projectiveClosedCenterChartMap`：基底の中心の環から閉厚化の各標準開へ入る実際の環準同型。
- `projectiveClosedCenterChartMap_mk`：中心の代表元は各標準開で同じ基底スカラーになる。
- `projectivePerfCechCenterAugmentation`：上の環準同型の Frobenius 順極限から作る中心の零次増大写像。
- `projectivePerfCechH0CenterClass_of_mk_cocycle`：中心の有限段の代表元の H⁰ 類のコサイクルは実際の増大写像の値。
- `projectivePerfCechH0CenterClass_augmentation`：同じ一致を中心の順極限の任意の元について示す。
- `projectivePerfCechCenterAugmentation_cycle`：中心の実際の増大写像の像は零次コサイクル。
- `cechZeroTermExtensionTerm`：複体の零次項だけを C⁰ × Q にする明示的な項。
- `cechZeroTermExtensionDifferential`：零次は第一成分への射影と元の微分の合成、正次数は元の微分。
- `cechZeroTermExtensionDifferential_squared`：この微分の二乗は零。
- `cechZeroTermExtensionDMap`：同じ線形微分を元の束ねられた加群の間の射として指定する。
- `cechZeroTermExtension`：中心の零次項を加えた複体。
- `cechZeroTermExtension_d`：その隣り合う項の微分は指定した微分の射。
- `cechZeroTermProjectionComponent`：零次は第一成分、正次数は恒等という射影の成分。
- `cechZeroTermProjection`：元の複体への射影の余鎖写像。
- `cechZeroTermProjection_epi`：射影の各次数の成分は全射。
- `cechZeroTermProjection_positive_homology_isIso`：この射影は正次数の H に同型を誘導する。
- `cechZeroTermDifferenceComponent`：零次は二つの制限の差、正次数は元の射という成分。
- `cechZeroTermDifference`：中心の増大写像を零次で差し引く実際の余鎖写像。
- `cechZeroTermDifference_positive_homology`：正次数の H では元の射と射影の合成と同じ射を誘導する。
- `cechZeroTermDifference_positive_homology_isIso`：元の射が正次数の H で同型なら、差の射もそうなる。
- `fullCechComplex_d`：実際の通常の Čech 複体の微分は指定したコチェイン微分。
- `fullCechH0ZeroTermCochainMap`：H⁰ と中心の項の組を、実際の零次コサイクルと中心の項の組へ送る線形写像。
- `fullCechH0ZeroTermCochainMap_injective`：この写像は単射。
- `fullCechH0ZeroTermCochainMap_cycle`：その像は零次項拡張のコサイクル。
- `fullCechH0ZeroTermCochainMap_surjective_cycles`：零次項拡張の全てのコサイクルはこの写像から来る。
- `projectivePerfCechCenterAugmentation_d`：中心の増大写像は閉厚化の実際の Čech 複体の最初の微分で零になる。
- `projectivePerfCechSquareSource`：C(Y) の零次項に基底の中心の Frobenius 順極限を加えた実際の複体。
- `projectivePerfCechSquareDifferenceMap`：実際の閉厚化への制限と中心の増大写像の差の余鎖写像。
- `projectivePerfCechSquareAugmentation`：基底からスカラーコチェインと基底の中心の元の組への実際の増大写像。
- `projectivePerfCechSquareDifferenceMap_positive_homology_bijective`：F6 を適用し、実際の差の射が正次数の H に全単射を誘導する。
- `projectivePerfCechH0Difference_kernel`：固定した F7 の H⁰ の差写像を零次コサイクルへ移すと、実際の差の余鎖写像となる。
- `projectivePerfCechH0ToSquareCochains`：F7 の中央項を実際の四角形の零次コチェインへ送る加法準同型。
- `projectivePerfCechH0Pair_cochains`：F7 の組の写像をコサイクルへ移すと、実際の基底の増大写像となる。
- `projectivePerfCechSquareAugmentation_cycle`：基底の増大写像の像は中心の項を加えた複体のコサイクル。
- `projectivePerfCechSquareAugmentation_injective`：F7 から実際の基底の増大写像の単射性を得る。
- `projectivePerfCechSquareDifference_augmentation_zero`：実際の差の余鎖写像と基底の増大写像の合成は零。
- `projectivePerfCechSquareAugmentation_exact`：F7 の短完全性から、実際の増大写像と cone の最初の微分の完全性を得る。
- `projectivePerfCechSquareDifferenceMap_homology_zero_surjective`：F7 の全射性から、実際の差の余鎖写像の H⁰ の全射性を得る。
- `projectivePerfCechSquareAugmentation_cone_cycle`：実際の基底の増大写像は cone の零次サイクルへ入る。
- `projectivePerfCechBlowupSquareTotalComplex`：射影中心の実際の四角形の明示的な増大全複体。
- `projectivePerfCech_blowupSquare_acyclic`：F6・F7 を供給し、上の全複体が Mathlib の Acyclic であることを示す。

検証：中心の増大写像の構成は 3,402 jobs、中心のコサイクルの公式は次の対象の束の中で成功。零次項拡張は独立対象 1,857 jobs、差の射の構成と正次数の一般計算は 1,858 jobs 成功。実際の差の射の正次数と核の比較は 3,421 jobs の束で両方成功。H⁰ と零次コサイクルの橋を共有した後の同じ二対象の再ビルドも成功。F7 の増大写像への移送と最初の完全性は 3,418 jobs、実際の差の射の H⁰ の全射性は 3,419 jobs、最終の `ProjectivePerfCechBlowupSquareTotal` は **3,430 jobs 成功**。共有鍵 `--wait 3600` は各ビルドの間だけ取得し、待ちは一つ。heartbeat・再帰上限・探索上限は一切引き上げず、sorry・admit・新しい公理は追加していない。大きい監査・ルート登録・ルートと下流の全ビルドは引き続き未実施。

型の表示の調整：束ねた加群の零次項の直積を作る際は、元の加群の間の射を `hom'` で指定し、勝手に carrier を束ね直さない。実際の差の正次数の同型性への適用では C・E・中心の加群を全て明示すると上限内で通った。H⁰ からコチェインへの比較補助写像は加法準同型で十分であり、整数加群の canonical な構造と直積の構造を定義上同じと仮定していない。全複体とその微分は引き続き整数加群の複体として作っている。

**停止点 2f に残るもの**：全複体の射の自然性を揃え、共通細分・底変換・R/J 表示・閉厚化・Frobenius 順極限との比較を 2e の既存の射に沿って検収する。続いて登録・許された対象ビルドと監査・停止点報告。数学の核の acyclicity は今回完成したが、この検収前に停止点 2f の完成とはしない。最終出力 `SerrePositivity.Cech.AugmentedRingCechExact` は変えていない。

2f のコミット済み新規本体は **186 モジュール・11,854 行**（既存の入口の追加 263 行込み **12,117 行**）。残りの暫定見込みは **1,500〜5,000 行**（自然性の必要な接続と検収、登録）。上端でも停止基準 18,000 行以内を見込む。
