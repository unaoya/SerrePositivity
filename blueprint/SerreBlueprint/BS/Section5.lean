-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.FrobeniusCechComparison

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "§5 The characteristic p case: the Hodge-Tate and crystalline comparisons" =>
%%%
number := false
tag := "bs-5"
%%%

BS §5 の項目と、本体の宣言との対応。本文は対応表（`research/bs-coverage`）の照合の理由で、原典の本文の写しではない。

*導入*

HT 比較（Thm 4.11）の証明。§5 で標数 p（$`I=(p)` の結晶 prism）の場合を、結晶比較（Thm 5.2）と Cartier 同型から示し（Cor 5.5）、§6 で普遍向き付き prism を結晶 prism へ写す構成（Construction 6.1）を使って一般の場合に延ばす（Prop 6.2、Thm 6.3）。最後に de Rham 比較（Thm 6.4）を述べる。本体にあるのは、結晶基底 $`(\mathbb Z_p,(p))` の多項式代数の HT 比較（Lemma 5.4・結晶の橋・pd de Rham 双複体・有限変数の Cartier 同型からの直接の証明）、結晶 site の古典的な部分、Construction 6.1 の保存性と Tor 振幅、Thm 6.4 の部品（Witt の結晶 prism、大きい模型との比較）。一般の有界向き付き基底への帰着（Prop 6.2・Thm 6.3）と Thm 6.4 の関手としての同型は drafts にある。形式化の設計の決定は a1-design.md にあり、原典との差として各項目の下に引く。

HT 比較（Thm 4.11）の標数 p の場合。$`I=(p)` の結晶 prism について、結晶比較（Thm 5.2）と Cartier 同型から HT 比較を示す（Cor 5.5）。混標数の一般の場合への延長は第 6 章（§6）。本体にあるのは、結晶基底 $`(\mathbb Z_p,(p))` の多項式代数の HT 比較（Lemma 5.4・結晶の橋・pd de Rham 双複体・有限変数の Cartier 同型からの直接の証明）と、結晶 site の古典的な部分。形式化の設計の決定は a1-design.md にあり、原典との差として各項目の下に引く。

*5.1 標数 p：結晶比較と HT 比較*

この節では結晶 prism $`(A,(p))` 上で prismatic cohomology と結晶コホモロジーを比べる（定理 5.1.2）。鍵は「pd 包は δ 環で $`\varphi(f)/p` を添加したもの」という系 2.5.5（原典 Cor 2.39）で、これにより結晶側の Čech–Alexander 複体 $`D^\bullet` も prismatic envelope として書け、相対 Frobenius が比較写像 $`\eta` を与える。$`\eta` が擬同型であることの mod p の部分は、多項式代数の Čech 脈体と Frobenius 捻りについての計算（命題 5.1.4、原典 Lemma 5.4）に帰着する。最後に Cartier 同型と合わせて、結晶 prism 上の HT 比較（系 5.1.5）を得る。

:::definition "bs_5_1"
*記法 5.1*　標数 p の記法（結晶 site）。対応表の状態：なし。

本項は R\^(1)=R⊗\_\{A/I,ψ\}A/p の指定 Frobenius twist の記法。候補 CrysOver と結晶基底の構成だけでは、この同じ twist を構成する宣言にならない。

*定義 5.1.1（原典 Notation 5.1） — 主張*

$`(A,(p))` を結晶 prism（例 3.1.3）とし、$`I\subset A` を $`p\in I` となる pd イデアルとする。このとき $`A/p` の Frobenius は商 $`A/p\to A/I` を経由し、写像 $`\psi\colon A/I\to A/p` を誘導する。$`R` を smooth な $`A/I` 代数とし、$`R^{(1)}:=R\otimes_{A/I,\psi}A/p` とおく。

*定義 5.1.1（原典 Notation 5.1） — Lean*

結晶 prism の一般形は第 3 章の \`OrientedPrism.crystalline\`（OrientedPrism:308）。この節で本体が使う基底は $`(\mathbb Z_p,(p))` の \`crystallineBasePrism\`（CrystallineBase:83、Frobenius の持ち上げは恒等射）と、その剰余 \`cartierBase\`（:102、$`\cong\mathbb F_p`）。一般の pd イデアル $`I\ni p` は結晶 site の基底 $`(k,J,\gamma)` として \`CrysOver\`（CrystallineSiteBasic:41）の引数に現れる（定理 5.1.2 の Lean の囲み）。$`\psi` と $`R^{(1)}` を一般の $`(A,I)` で定める宣言は本体にない。$`A=\mathbb Z_p`、$`I=(p)` では $`\psi` は $`\mathbb F_p` の恒等射で $`R^{(1)}=R` なので、本体はこの区別を立てない。

*定義 5.1.1（原典 Notation 5.1） — 証明*

（補った）$`x\in I` について $`x^p=p!\,\gamma_p(x)\in pA`。よって $`A/p` の Frobenius $`\bar x\mapsto\bar x^p` は $`I/p` を零に送り、$`A/I` から $`A/p` への環準同型 $`\psi` が降りる。これは $`A/I` の元 $`\bar x` を $`\bar x^p\in A/p` に送る写像で、$`A/p\to A/I\xrightarrow{\psi}A/p` は $`A/p` の Frobenius に等しい。

宣言：`SerrePositivity.BhattScholze.Prismatic.CrysOver`、`SerrePositivity.BhattScholze.Prismatic.crysAlgebras`、`SerrePositivity.BhattScholze.Prismatic.crystallineBasePrism`

:::

:::theorem "bs_5_2"
*定理 5.2*　標数 p の結晶比較。対応表の状態：なし。

本体は指定した Čech/PD 模型間の bridge quasiIso。原文の二つの site の RΓ、E∞積と Frobenius への比較は未供給。通常の模型の cohomology 同型を同じ site 比較の component としない。

*定理 5.1.2（原典 Thm 5.2：標数 p の結晶比較） — 主張*

定義 5.1.1 の状況で、$`\mathrm{Spf}(A)` の pd 厚化 $`\mathrm{Spec}(A/I)\subset\mathrm{Spf}(A)` に対する $`\mathrm{Spf}(R)` の結晶コホモロジーを $`R\Gamma_{\mathrm{crys}}(R/A)` と書く。このとき E∞-$`A` 代数の標準的な同型
$$`\Delta_{R^{(1)}/A}\;\simeq\;R\Gamma_{\mathrm{crys}}(R/A)`
があり、Frobenius と両立する。

*定理 5.1.2（原典 Thm 5.2：標数 p の結晶比較） — Lean*

本体にあるのは、$`A=\mathbb Z_p`、$`I=(p)`、$`R=\mathbb F_p[X_1,\dots,X_r]`（有限変数）の場合の、Čech–Alexander 模型の比較写像 $`\eta` の *mod p のコホモロジー同型*と、それを pd de Rham 複体につないだ加法同型である。$`R\Gamma_{\mathrm{crys}}` との同型、E∞ 構造、Frobenius との両立は本体にない。

2. *mod p で擬同型*：結晶側模型の mod p が相対 Frobenius に沿う押し出しであること \`pdDelta\_modP\_frobeniusPushout\`（CrystallineBridgePushout:141）と命題 5.1.4（変数 $`\mathrm{Fin}\,r\times\mathbb N` の版）から、\`crystallineBridgeModP\_isCohomologyIso\`（:150）。

3. *余分な δ 座標の除去*：高次の δ 座標を零に評価する切断により、δ 変数なしの pd 模型からの包含が mod p でコホモロジー同型（\`pdInclusionModP\_isCohomologyIso\`、CrystallinePDInclusion:270）。整係数の pd 模型の mod p は標数 p の完備 pd Čech 模型（\`pdModel\_modP\`、PDModelReduction:161）。

4. *pd de Rham 双複体*：横に Čech、縦に pd 微分形式を並べた双複体の総複体から第 0 行と第 0 列への二つの射影を取る。正次数の行は切断付き Čech 余脈体のホモトピーで収縮し（\`pdRow\_contractible\`、PDDeRhamRow:220）、第 0 行への射影は擬同型（\`pdDeRhamRowZeroProjection\_quasiIso\`、PDDeRhamRowComparison:35）。各列は pd Poincaré 補題（分冪積分と内部積による収縮）で定数列に潰れ、第 0 列への射影も擬同型（\`pdDeRhamColumnZeroProjection\_quasiIso\`、PDDeRhamColumnComparison:202）。合わせて pd Čech 複体と多項式 de Rham 複体のコホモロジーの比較 \`pdDeRhamCechToPolynomial\`（PDDeRhamCohomology:35）。

5. *まとめ*：1.〜4. をつないだ加法同型 \`crystallineChain\`（CrystallineChain:39）$`H^i(\overline\Delta_{\mathbb F_p[X]/\mathbb Z_p})\cong H^i(\Omega^\bullet_{\mathbb F_p[X]/\mathbb F_p})`。ここで $`\overline\Delta` は注意 4.3.4 の模型を p で割ったもの。これが系 5.1.5 の入力になる。

*結晶 site*（主張の $`R\Gamma_{\mathrm{crys}}`）。affine な big site として本体にある。対象 \`CrysOver\`（CrystallineSiteBasic:41）は分冪基底 $`(k,J,\gamma)` 上の pd 厚化 $`(B,J_B,\delta)` で、$`k\to B` が pd 射、p が B で冪零、$`R\to B/J_B` を持ち、濃度 $`\le\kappa`。台の環を取る関手 \`crysAlgebras\`（:103）。小さい模型の site \`CrystallineSite\`（CrystallineSiteSmall:105）、Zariski 位相 \`zariskiTopology\`（CrystallineSmallSiteTopology:38）、構造環が層であること \`crystallineStructure\_isSheaf\`（CrystallineSmallStructureSheaf:64）。証明の第 1 段落の Čech–Alexander の結晶版として、全射な枠 $`S\to R` の分冪 Čech 脈体を p 冪で割った塔 \`pdCechTower\`（PDCechCrystallineTower:80）と、その小さい site での pro 弱終性 \`pdCechSmallTowerOfCutoff\_proWeaklyTerminal\`（CrystallineCechCutoff:62、枠の変数の数が $`\#k+\#R+\aleph_0` 以下）。部品の完備 pd 包は \`IsCompletedPDEnvelope\`・\`exists\_completedPDEnvelope\`（CompletedPDEnvelope:47・158）。「枠の選び方によらない」は枠の射の擬同型 \`pdCechNerveMap\_quasiIso\`（PDCechFrameHomotopy:326、混合頂点の鎖ホモトピー）。多項式の場合の Poincaré 補題の二脚は、総複体から分冪 Čech 複体への射影 \`crystallinePolynomialTotalToCech\_quasiIso\`（CrystallinePolynomialSpan:60）と完備形式への射影 \`pdDeRhamTotalToCompletedForms\_quasiIso\`（PDDeRhamCompletedColumnZero:142）。

*drafts*（drafts/A1/CrystallineSite）。$`R\Gamma_{\mathrm{crys}}` の定義 \`crystallineCohomology\`（:313）、塔がそれを計算すること \`crystallineCechIso\`（:491）、枠の射との両立 \`crystallineCohomology\_map\_frame\`（:506）、多項式の場合の de Rham 計算 \`crystallineCohomology\_polynomial\_deRham\`（:539）。一般の結晶 prism と $`I\ni p`、$`R=(A/I)[X_1,\dots,X_r]` の場合の比較は、原典の $`\eta` \`etaBridge\`（:608）、δ 変数の収縮 \`pdDeltaRetraction\`（:618）とその擬同型 \`pdDeltaRetraction\_quasiIso\`（:627）を合成した写像の可逆性 \`crystallineComparison\_polynomial\`（:667）で、Frobenius との両立は述べない。上の 1. の \`crystallineBridge\` がその $`(\mathbb Z_p,(p))` の場合であることは \`crystallineBridge\_eq\_eta\`（:690）。

*定理 5.1.2（原典 Thm 5.2：標数 p の結晶比較） — 証明*

原典はまず $`I=(p)` の場合を示し、一般の場合をそれに帰着する。

\*\*(1) $`I=(p)`：結晶側の Čech–Alexander 複体。\*\* 全射 $`B_0\to R`（$`B_0` は多項式 $`A` 代数の p 完備化）を取り、$`J_0=\ker(B_0\to R)`、$`B` を $`B_0` 上の p 完備自由 δ-$`A` 代数、$`R'=B/J_0B` とおく（$`R\to R'` は ind-smooth）。$`D_0`・$`D` を $`J_0\subset B_0`・$`J_0B\subset B` の p 完備 pd 包とする。これらは p ねじれなしで（命題 2.5.4）、$`D/p^n` は $`B/p^n\to R'` の pd 包（$`(p)` の標準的な分冪と両立）。よって $`\{(D/p^n\to R'\leftarrow R)\}_n` は big crystalline site $`(R/A)_{\mathrm{CRYS}}` の pro 対象で、弱始（任意の対象 $`(T\to U\leftarrow R)` に、$`B_0\to R\to U` を多項式環の自由性で $`B_0\to T` に持ち上げ、δ 環の自由性と pd 包の普遍性で $`D/p^n\to T` に延ばす。p は T で冪零なので十分大きい n で降りる（補った））。この構成は余積と可換なので、Čech 脈体は $`\{(D^\bullet/p^n\to(R')^\bullet\leftarrow R)\}_n` で、$`D^\bullet` は $`A\to B_0` の Čech 脈体に $`B_0\mapsto D` を施したもの。よって $`R\Gamma_{\mathrm{crys}}(R/A)` は余単体的環 $`D^\bullet` で計算される（big site と small site の比較は \[Ber06, Prop III.4.1.4\]）。全射 $`B_0\to R` の圏は sifted なので、この計算は選び方によらない。

*(2) prism 側と η。* 同じ $`B_0\to R` で第 4 章の Čech–Alexander 複体（命題 4.3.3）を作ると、$`C^\bullet=B^\bullet\{J_0^\bullet B^\bullet/p\}^\wedge` が $`\Delta_{R/A}` を計算する。Čech–Alexander 複体は底変換と両立するので、項ごとに $`\varphi_A` で底変換した $`\varphi_A^*C^\bullet` が $`\Delta_{R^{(1)}/A}` を計算する（$`\varphi_A^*` が Tot と可換とはまだ言わない）。一方 $`D^\bullet=D_{J_0^\bullet B^\bullet}(B^\bullet)` で、系 2.5.5 により $`D^\bullet=B^\bullet\{\varphi(J_0^\bullet)B^\bullet/p\}^\wedge`。$`A\to B^\bullet` の相対 Frobenius $`B^{\bullet,(1)}=\varphi_A^*B^\bullet\to B^\bullet`（$`b\otimes a\mapsto a\varphi(b)`）は $`J_0^\bullet` を $`\varphi(J_0^\bullet)` に送るので、envelope の普遍性から余単体的 δ-$`A` 代数の射
$$`\eta\colon\varphi_A^*C^\bullet=\varphi_A^*B^\bullet\{J_0^\bullet B^\bullet/p\}^\wedge\longrightarrow B^\bullet\{\varphi(J_0^\bullet)B^\bullet/p\}^\wedge=D^\bullet`
が出る。これが導来圏で比較写像 $`\Delta_{R^{(1)}/A}\to R\Gamma_{\mathrm{crys}}(R/A)` を与える。

*(3) η は擬同型。* 上の記述から、$`D^\bullet` は余単体的 $`B^{\bullet,(1)}` 加群 $`\varphi_A^*C^\bullet` を相対 Frobenius $`B^{\bullet,(1)}\to B^\bullet` で引き戻したもの（envelope の構成は平坦な底変換と可換で、自由 δ 代数の相対 Frobenius は p 完全平坦）。両辺は p ねじれなし（pd 包については標準的で、prismatic envelope については原典 Lemma 2.43・Cor 2.44 を $`A=\mathbb Z_p` で使う）。したがって η の導来 mod p は普通の mod p で、$`N=\varphi_A^*C^\bullet/p`、$`k=A/p`、多項式代数 $`B/p` として命題 5.1.4 を使うと、mod p の η は擬同型。両辺は導来 p 完備なので導来 Nakayama（\[Sta, Tag 0G1U\]）で η 自身が擬同型。

*(4) Frobenius との両立。* η は余単体的 δ-$`A` 代数の射なので δ 構造の Frobenius と可換。残るのは、$`R\Gamma_{\mathrm{crys}}(R/A)\simeq\lim D^\bullet` のもとで $`D^\bullet` の δ 構造の Frobenius が結晶コホモロジーの Frobenius と一致すること（結晶側だけの主張で、原典は文献がないとして概略を与える）。結晶コホモロジーの関手性：$`\alpha\colon A\to A'`、α 同変な $`\pi\colon X\to Y`、その上の PD スキームの単体的対象の射 $`f_\bullet\colon U_\bullet\to V_\bullet` から、$`R\Gamma_{\mathrm{crys}}(Y/A)\to R\Gamma_{\mathrm{crys}}(X/A')` と $`\lim\mathcal O(V_\bullet)\to\lim\mathcal O(U_\bullet)` の可換な四角形が出る。これを $`A=A'`、$`X=Y=\mathrm{Spec}\,R`、$`U_\bullet=V_\bullet=(D^\bullet/p^n\to(R')^\bullet\leftarrow R)`、α・π・$`f_\bullet` を Frobenius として各 n で使い、帰納系について同じ議論で逆極限を取る。

\*\*(5) 一般の $`I\ni p`。\*\* I は分冪を持つので $`A/p\to A/I` の核は局所冪零（各元は Frobenius で零）。ネーター近似で smooth な $`A/I` 代数 R を smooth な $`A/p` 代数 $`\tilde R` に持ち上げると、$`\tilde R` の Frobenius 底変換は $`R^{(1)}` に一致する（Frobenius が $`A/I` を経由するので）。よって (1)〜(4) が同型を与える。持ち上げによらないことを見るため、原典は標準的な比較写像を直接作る：δ 構造を持つ smooth な $`A` 代数 $`B_0` からの全射 $`B_0\to R` の pd 包の Čech 脈体 $`D^\bullet`（p 完全平坦な p 完備余単体的 δ-$`A` 代数で、核 $`K^\bullet` は I の分冪と両立する分冪を持ち、$`R\Gamma_{\mathrm{crys}}(R/A)\simeq\lim D^\bullet`）を取る。$`x\in K^\bullet` について $`\varphi(x)=x^p+p\delta(x)=p\big((p-1)!\gamma_p(x)+\delta(x)\big)\in pD^\bullet` なので（補った）、Frobenius が $`R\simeq D^\bullet/K^\bullet\to D^\bullet/p` を誘導し、ψ 上で線形化して $`(D^\bullet\to D^\bullet/p\leftarrow R^{(1)})\in(R^{(1)}/A)_\Delta` を得る。これが $`\Delta_{R^{(1)}/A}\to\lim D^\bullet\simeq R\Gamma_{\mathrm{crys}}(R/A)` を与え、$`B_0\to R` の選び方の圏が sifted なので可縮な曖昧さを除いて標準的。二つの構成の一致は原典が演習として残している。

*定理 5.1.2（原典 Thm 5.2：標数 p の結晶比較） — 原典との差（D68）*

原典は Thm 5.2（$`R\Gamma_{\mathrm{crys}}` との比較）を立ててから、Cor 5.5 を Thm 5.2 と Cartier 同型で導く。本体は $`R\Gamma_{\mathrm{crys}}` を経由せず、HT 比較に要る mod p のコホモロジー同型（$`(\mathbb Z_p,(p))`・多項式）だけを示す：命題 5.1.4、結晶の橋、δ 座標の除去、pd de Rham 双複体（上の Lean の 1.〜5.）と、系 5.1.5 の Cartier 同型・生成元の照合。mod p で閉じるので導来 Nakayama も使わない。

*定理 5.1.2（原典 Thm 5.2：標数 p の結晶比較） — 原典との差（D25）*

原典の $`R\Gamma_{\mathrm{crys}}` は big crystalline site $`(R/A)_{\mathrm{CRYS}}`（\[Ber06, §III.4\]）のコホモロジーで、small site との比較 \[Ber06, Prop III.4.1.4\] も使う。本体の結晶 site は affine な対象だけの big site（Zariski 位相、p 冪零、濃度の上限 κ）で、$`R\Gamma_{\mathrm{crys}}` はその構造環の大域切断として定め（drafts）、Čech–Alexander（pro 弱終性）・多項式の Poincaré 補題・関手性を定理にする。crystal と非 affine な対象は扱わない。

宣言：`SerrePositivity.BhattScholze.Prismatic.crystallineBridgeModP_isCohomologyIso`、`SerrePositivity.BhattScholze.Prismatic.crystallineBridge`、`SerrePositivity.BhattScholze.Prismatic.pdDeltaModel`、`SerrePositivity.BhattScholze.Prismatic.crystallineSmallBridgeCochainMap_quasiIso`、`SerrePositivity.BhattScholze.Prismatic.wittBigCompletedBridge_quasiIso`

:::

:::proposition "bs_5_3"
*注意 5.3*　Thm 5.2 についての注意。対応表の状態：なし。

Frobenius-pullback と crystalline RΓ の指定同型は未同定。5.2の模型だけではこの帰結を得ない。

*注意 5.1.3（原典 Rem 5.3） — 主張*

定理 5.1.2 は、smooth な $`A/p` 代数 $`\tilde R` について $`R=\tilde R\otimes_{A/p}A/I` の場合によく使う。このとき $`R^{(1)}` は $`\tilde R` の $`\varphi` による引き戻しで、prismatic cohomology の底変換との両立（系 4.2.4、系 5.1.5 の一部として再掲）により、定理は
$$`\varphi_A^*\Delta_{\tilde R/A}\;\cong\;R\Gamma_{\mathrm{crys}}(\tilde R/A)`
と言い換えられる。

*注意 5.1.3（原典 Rem 5.3） — Lean*

本体にない。底変換との両立（系 4.2.4）は drafts の \`prismaticCohomology\_baseChange'\`（drafts/A1/HodgeTateComparison:365、多項式代数の場合）。

*注意 5.1.3（原典 Rem 5.3） — 証明*

（補った）定義 5.1.1 の証明のとおり $`A/p\to A/I\xrightarrow{\psi}A/p` は $`A/p` の Frobenius なので、
$`R^{(1)}=(\tilde R\otimes_{A/p}A/I)\otimes_{A/I,\psi}A/p=\tilde R\otimes_{A/p,\varphi}A/p`。$`\varphi_A\colon(A,(p))\to(A,(p))` は prism の射で、$`\tilde R\otimes_{A/p,\varphi}A/p` はこの射に沿う $`\tilde R` の底変換だから、底変換との両立により $`\Delta_{R^{(1)}/A}\simeq(\varphi_A^*\Delta_{\tilde R/A})^\wedge`（p 完備化）。結晶コホモロジーは厚化の取り替え（$`A/I` と $`A/p` の核は分冪を持つ）で変わらないので $`R\Gamma_{\mathrm{crys}}(R/A)\simeq R\Gamma_{\mathrm{crys}}(\tilde R/A)`。これらを定理 5.1.2 に代入する。

:::

:::lemma_ "bs_5_4" (lean := "SerrePositivity.BhattScholze.Prismatic.frobeniusTwist_cech_quasiIso, SerrePositivity.BhattScholze.Prismatic.frobeniusTwist_cech_quasiIso_infinite")
*補題 5.4*　Frobenius 捻りと Čech 脈体の擬同型。対応表の状態：一部（special）。

*主張*　標数 $`p` の可換環 $`k` 上の多項式代数 $`B` の Čech nerve $`B^\bullet` とその Frobenius ひねり $`B^{\bullet,(1)}` をとる。任意の余単体的 $`B^{\bullet,(1)}` 加群 $`N` について、相対 Frobenius に沿う $`N\to N\otimes_{B^{\bullet,(1)}}B^\bullet` は非正規化複体上の擬同型を与える。

N が余単体的可換環から来る加群の場合、同じ polynomial Čech と relative Frobenius の pushout 射が unnormalized cochain cohomology の同型となる。任意の cosimplicial module は扱わない。

*命題 5.1.4（原典 Lemma 5.4） — 主張*

$`k` を標数 p の可換環、$`B` を多項式 $`k` 代数とする。$`B^\bullet` を $`k\to B` の Čech 脈体、$`B^{\bullet,(1)}` をその Frobenius 捻りとし、$`k` 上の相対 Frobenius $`B^{\bullet,(1)}\to B^\bullet` を考える。任意の余単体的 $`B^{\bullet,(1)}` 加群 $`N` について、自然な写像
$$`N\longrightarrow N\otimes_{B^{\bullet,(1)}}B^\bullet`
は、付随する（非正規化の）$`k` 加群の鎖複体の擬同型である。

*命題 5.1.4（原典 Lemma 5.4） — Lean*

\`frobeniusTwist\_cech\_quasiIso\_infinite\`（FrobeniusCechComparison:472）、有限変数版 \`frobeniusTwist\_cech\_quasiIso\`（:485）。$`p=0` の $`k`、任意の変数集合 σ について、多項式 Čech 脈体 \`polynomialCech\`（PolynomialFrobeniusCech:36、n 次の項は $`k[\sigma\times\mathrm{Fin}(n+1)]`）と変数を p 乗する相対 Frobenius \`relativeFrobeniusCech\`（:57）を取る。\`polynomialCech\` からの射 ι を持つ余単体的可換環 $`N` について、相対 Frobenius に沿う押し出しへの包含 \`pushout.inl\` が非正規化の交代余面複体のコホモロジー同型。主張は *N が余単体的可換環の場合*に限る（原典は任意の余単体的加群）。押し出しが $`N\otimes_{B^{\bullet,(1)}}B^\bullet` にあたる。Frobenius 捻り $`B^{\bullet,(1)}` は $`k[X]^{(1)}\cong k[X]` により \`polynomialCech\` 自身と同一視している。変数が無限個の版が要るのは、完備自由 δ 環の mod p が無限変数の多項式環になるから（定理 5.1.2 の Lean の 2.）。

*命題 5.1.4（原典 Lemma 5.4） — 証明*

フィルター余極限で有限変数に帰着し、$`B=k[M]`、$`M=\mathbb N^r` と書く。

*(i) 単項式による記述。* $`[n]\mapsto M^{\oplus[n]}` は可換 monoid の射 $`0\to M` の Čech 脈体 $`EM` で、余面写像は有限積の包含（M を 0 を基点とする集合としてしか使わない）、余退化写像は monoid の演算を使う。$`B^\bullet=k[EM]`、$`B^{\bullet,(1)}=k[E(pM)]` で、相対 Frobenius は包含 $`pM\subset M` が誘導する $`k[E(pM)]\to k[EM]`。

*(ii) semi-cosimplicial な基底。* $`S=\{0,\dots,p-1\}^r\subset M` を $`M^{\mathrm{grp}}/pM^{\mathrm{grp}}` の代表系（0 を基点）とすると $`\bigsqcup_{s\in S}(pM+s)\simeq M`（原典の式 (3) の添字 $`s\in M` は $`s\in S` の誤植）。積を取って $`S^{\oplus[n]}\subset M^{\oplus[n]}`。余面写像は置換を除き「始めの因子は恒等、残りは 0」なので $`0\in S` から $`S^{\oplus[n]}` を保ち、semi-cosimplicial 集合 $`ES\subset EM` と、余面写像と両立する分解 $`\bigsqcup_{s\in S^{\oplus[n]}}(pM^{\oplus[n]}+s)\simeq M^{\oplus[n]}` を得る。よって semi-cosimplicial $`k[E(pM)]` 加群として $`k[E(pM)]\otimes_kk[ES]\simeq k[EM]` で、構造写像 $`k[E(pM)]\to k[EM]` は $`\mathrm{id}\otimes\eta`（$`\eta\colon k\to k[ES]` は基点 0 が定める）にあたる。

*(iii) 帰着。* 非正規化の鎖複体は semi-cosimplicial 構造だけで決まるので、$`\alpha\colon N\to N\otimes_{k[E(pM)]}k[EM]` の代わりに $`\beta=\mathrm{id}_N\otimes\eta\colon N\to N\otimes_kk[ES]` が擬同型であることを示せばよい。基点つき全単射 $`S\simeq M^{\mathrm{grp}}/pM^{\mathrm{grp}}` により、semi-cosimplicial $`k` 加群 $`k[ES]` は $`k\to C^0:=k[M^{\mathrm{grp}}/pM^{\mathrm{grp}}]` の Čech 脈体 $`C^\bullet` の下にあるものと一致し（どちらも余面写像は基底の 0 を差し込む写像）、η は構造写像 $`\gamma\colon k\to C^\bullet` にあたる。したがって余単体的 $`k` 加群の写像 $`\mathrm{id}_N\otimes\gamma\colon N\to N\otimes_kC^\bullet` が擬同型であればよい。$`k\to C^0` は切断（$`M\to0` が誘導）を持つので、その Čech 脈体 γ は余単体的 $`k` 加群のホモトピー同値で、ホモトピー同値は任意の余単体的加群とのテンソルで保たれる。

原典は、この議論が「余退化写像を無視してよい」ことに強く依存する間接的なものであり、よりよい証明が望ましいと述べている（似た主張は \[Niz08, Lemma 3.28\]）。

*命題 5.1.4（原典 Lemma 5.4） — 原典との差*

主張は N が余単体的可換環の場合に限る（定理 5.1.2 で使う N はこの形）。証明は semi-cosimplicial な基底と Čech 脈体 $`C^\bullet` への帰着を経ず、余り指数の基底で各項を分解して、全零の添字の成分以外を余鎖収縮で直接潰す：全零でない添字では最初の非零頂点の直前の零頂点を削り、係数には対応する余退化を施す。原典と違い N の余退化写像を使う。各指数は有限台なので、フィルター余極限による有限変数への帰着も要らない。

:::

:::corollary "bs_5_5"
*系 5.5*　標数 p の HT 比較。対応表の状態：なし。

結晶基底 Zp の多項式の reducedModel の HodgeTateIsoStatement は本体にあるが、site Δ̄ の η との比較は未供給。arbitrary smooth S と site 底変換を含む原文とは未接続。

*系 5.1.5（原典 Cor 5.5：標数 p の HT 比較） — 主張*

結晶 prism $`(A,(p))` と smooth な $`A/p` 代数 $`S` について、定理 4.2.3（原典 Thm 4.11）の比較写像は同型
$$`H^i(\overline\Delta_{S/A})\;\cong\;\Omega^i_{S/(A/p)}\{-i\}`
を与える。特に、$`R\mapsto\Delta_{R/A}` は prism $`(A,(p))` の任意の p 完備な底変換と可換である。

*系 5.1.5（原典 Cor 5.5：標数 p の HT 比較） — Lean*

本体にあるのは $`A=\mathbb Z_p`、$`S=\mathbb F_p[X_1,\dots,X_r]`（有限変数）の場合：\`hodgeTate\_iso\_polynomial\_Zp\`（HodgeTateCartierAssembly:212）。主張の型 \`HodgeTateIsoStatement\`（HodgeTateCompletedMap:461）は、各 i で多項式の HT 写像 \`hodgeTateMap\`（:398、定義 4.2.1 の $`\eta^i` の模型での形）が全単射であること。証明は定理 5.1.2 の Lean の加法同型 \`crystallineChain\` に次の二段を足す。

1. *Cartier 同型*：\`finitePolynomialCartier\`（FinitePolynomialCartier:46）。型 \`PolynomialCartier\`（:35）は各次数の加法同型 $`\Omega^i\to H^i(\Omega^\bullet)` と、次数 0 で $`f\mapsto[f^p]`、次数 1 で $`dX_j\mapsto[X_j^{p-1}dX_j]`、外積との両立の組。加法同型は単項式基底で、指数と一次形式の重みがすべて p の倍数の単項式だけを残すホモトピー同値から作る（\`finiteCartierLinearEquiv\`、CartierFinite:213、\`cartierMonomialEquiv\`、CartierWeight:146）。

2. *生成元での照合*：\`crystallineChain\_generators\`（CrystallineGeneratorClasses:83）は、\`crystallineChain\` が $`\eta^0(X_j)` を $`[X_j^p]` に、$`\eta^1(dX_j)` を $`[X_j^{p-1}dX_j]` に送ることを示す。零次・一次の一致を加法と外積で全次数へ延ばし、HT 写像を二つの同型の合成と同一視して全単射性を得るのが \`hodgeTate\_of\_deRham\_cartier\`（:180）。

一般の結晶 prism 上の多項式代数（Lemma 4.20 で $`\mathbb Z_p` に帰着）は drafts の \`hodgeTate\_iso\_crystalline\`（drafts/A1/HodgeTateComparison:62）。smooth な S への étale 局所化（Lemma 4.21）と、後半の底変換の主張は本体にない（多項式の底変換は系 4.2.4 の drafts \`prismaticCohomology\_baseChange'\`、同 :365）。

*系 5.1.5（原典 Cor 5.5：標数 p の HT 比較） — 証明*

原典の筋：Lemma 4.21（命題 4.3.6）で S を多項式代数 $`A/p[X_1,\dots,X_n]` に帰着し、Lemma 4.20（命題 4.3.5）で $`A=\mathbb Z_p` に帰着する。すると $`S=R^{(1)}`（$`R=\mathbb F_p[X_1,\dots,X_n]`、$`\psi` は恒等）で、定理 5.1.2 と Cartier 同型から従う。

（補った）各段の中身。(a) $`A` は p ねじれなし（$`(p)` が prism のイデアル）なので $`\mathbb Z_p\to A` は p 完全平坦で、Lemma 4.20 により $`\overline\Delta_{S/A}\simeq\overline\Delta_{\mathbb F_p[X]/\mathbb Z_p}\widehat\otimes^L_{\mathbb Z_p}A`。$`\Omega^i` も底変換と可換で、$`\{-i\}` の捻りは生成元 p で自明化される。(b) $`A=\mathbb Z_p` では定理 5.1.2 と多項式の場合の結晶 Poincaré 補題により $`\Delta_{\mathbb F_p[X]/\mathbb Z_p}\simeq R\Gamma_{\mathrm{crys}}(\mathbb F_p[X]/\mathbb Z_p)\simeq\widehat\Omega^\bullet_{\mathbb Z_p[X]/\mathbb Z_p}` で、mod p で $`\overline\Delta\simeq\Omega^\bullet_{\mathbb F_p[X]/\mathbb F_p}`。(c) Cartier 同型 $`C^{-1}\colon\Omega^i_{\mathbb F_p[X]}\xrightarrow{\sim}H^i(\Omega^\bullet_{\mathbb F_p[X]})`（$`f\mapsto[f^p]`、$`df\mapsto[f^{p-1}df]`、外積と両立）と合わせて $`H^i(\overline\Delta)\cong\Omega^i`。(d) この同型が Thm 4.11 の比較写像 $`\eta^i` と一致すること（原典は述べない）：両辺とも外積と両立するので $`\eta^0(X_j)` と $`\eta^1(dX_j)` を見れば足りる。$`\eta^0(X_j)` は Frobenius 捻りを通って $`[X_j^p]`。$`\eta^1(dX_j)` は Bockstein の像で、整係数の総次数 0 の余鎖 $`X_j^p` の総微分の横成分 $`X_{j,1}^p-X_{j,0}^p` と縦成分 $`pX_j^{p-1}dX_j` がともに p で割れ、その商の mod p の二つの射影が Bockstein の代表と Cartier の代表 $`[X_j^{p-1}dX_j]` を与えるので一致する。

後半（補った）：prism の射 $`(A,(p))\to(B,(p))` と smooth な $`R` について、比較写像 $`(\Delta_{R/A}\widehat\otimes^L_AB)\to\Delta_{R_B/B}` は、両辺導来 p 完備なので導来 Nakayama で mod p を見ればよい。前半により $`H^i(\overline\Delta_{R/A})\cong\Omega^i_{R/(A/p)}` は射影的なので、底変換の $`H^i` は $`\Omega^i_{R/(A/p)}\otimes_{A/p}B/p\cong\Omega^i_{R_B/(B/p)}` で、比較写像はこの同型にあたる（系 4.2.4 と同じ議論）。

*系 5.1.5（原典 Cor 5.5：標数 p の HT 比較） — 原典との差（D68）*

原典は Thm 5.2 と Cartier 同型から導くが、本体は $`R\Gamma_{\mathrm{crys}}` を経由せず、mod p の Čech–Alexander 模型から直接示す（評価は定理 5.1.2 の「原典との差（D68）」）。上の (d) の生成元での照合を明示的な定理（\`crystallineChain\_generators\`）にしている。また本体は $`\mathbb Z_p` 上の多項式代数を直接扱い、Lemma 4.21・4.20 による帰着は通らない。

宣言：`SerrePositivity.BhattScholze.Prismatic.hodgeTate_iso_polynomial_Zp`、`SerrePositivity.BhattScholze.Prismatic.hodgeTate_of_deRham_cartier`

:::

