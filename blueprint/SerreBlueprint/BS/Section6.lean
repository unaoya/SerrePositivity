import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.Construction61Detection
import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.Construction61Frobenius
import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.Construction61Reflection
import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineCoverCompleteTor

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "§6 " =>
%%%
number := false
tag := "bs-6"
%%%

BS §6 の項目と、本体の宣言との対応。本文は対応表（`research/bs-coverage`）の照合の理由で、原典の本文の写しではない。

*導入*

HT 比較（Thm 4.11）の証明。§5 で標数 p（$`I=(p)` の結晶 prism）の場合を、結晶比較（Thm 5.2）と Cartier 同型から示し（Cor 5.5）、§6 で普遍向き付き prism を結晶 prism へ写す構成（Construction 6.1）を使って一般の場合に延ばす（Prop 6.2、Thm 6.3）。最後に de Rham 比較（Thm 6.4）を述べる。本体にあるのは、結晶基底 $`(\mathbb Z_p,(p))` の多項式代数の HT 比較（Lemma 5.4・結晶の橋・pd de Rham 双複体・有限変数の Cartier 同型からの直接の証明）、結晶 site の古典的な部分、Construction 6.1 の保存性と Tor 振幅、Thm 6.4 の部品（Witt の結晶 prism、大きい模型との比較）。一般の有界向き付き基底への帰着（Prop 6.2・Thm 6.3）と Thm 6.4 の関手としての同型は drafts にある。形式化の設計の決定は a1-design.md にあり、原典との差として各項目の下に引く。

HT 比較（Thm 4.11）の一般の場合。普遍向き付き prism を結晶 prism へ写す構成（Construction 6.1）で、一般の有界向き付き基底の affine 直線を第 5 章の標数 p の場合に帰着し（Prop 6.2）、多項式代数・smooth な代数へ延ばす（Thm 6.3）。最後に de Rham 比較（Thm 6.4）を述べる。本体にあるのは、Construction 6.1 の保存性と Tor 振幅、HT 写像と主張の型、結晶基底の場合の HT 比較（第 5 章）、Thm 6.4 の部品（Witt の結晶 prism、大きい模型との比較）。一般の基底への帰着（Prop 6.2・Thm 6.3）と Thm 6.4 の関手としての同型は drafts にある。形式化の設計の決定は a1-design.md にあり、原典との差として各項目の下に引く。

*6.1 混標数の HT 比較と de Rham 比較*

一般の有界 prism の上の HT 比較を、標数 p の場合（原典 Cor 5.5）に帰着する節。帰着の道具は、普遍向き付き prism から結晶 prism への射 $`\alpha`（定義 6.1.1）と、それに沿う完備底変換の保存性・有限 Tor 振幅。まず affine 直線で HT 比較を示して HT 写像の存在（原典 Lemma 4.10、命題 4.2.2）を確定させ（命題 6.1.2）、同じ議論で多項式代数、étale 局所化で一般の滑らかな形式スキームへ進む（定理 6.1.3）。最後に、底変換（原典 Cor 4.12）と結晶比較（原典 Thm 5.2）から、技術的な仮定のもとで de Rham 比較を出す（定理 6.1.4）。

:::definition "bs_6_1" (lean := "SerrePositivity.BhattScholze.Prismatic.Construction61.completelyFlat_of_flat, SerrePositivity.BhattScholze.Prismatic.Construction61.crystallineCoverMap_torAmplitude, SerrePositivity.BhattScholze.Prismatic.Construction61.quasiIso_of_completedCover_map_quasiIso, SerrePositivity.BhattScholze.Prismatic.Construction61.cochain_acyclic_of_completedCover_acyclic")
*構成 6.1*　普遍向き付き prism から結晶 prism へ。対応表の状態：一部（stronger-hyp）。

原文の同じ α の有限完全 Tor 振幅(2)を上界3で証明する。(1)の検出は具体的 K-flat cochain model とその底変換も K-flat とする入力で与える。Frobenius の flatness から完全平坦性への橋はあるが、site Δ の底変換(3)は drafts。

*定義 6.1.1（原典 Construction 6.1：普遍向き付き prism から結晶 prism へ） — 主張*

$`(A,(d))` を向き付き prism で、$`A/p` の Frobenius が平坦、かつ $`A/(d)` が p ねじれなしとする（例：原典 Ex 3.4 の普遍向き付き prism、例 3.1.4）。$`B:=A\{\varphi(d)/p\}^\wedge` を、$`A` に $`\varphi(d)/p` を自由に添加した p 完備な単体的可換 δ-$`A` 代数とする。原典 Lemma 2.24（命題 2.3.6）により $`\varphi(d)=pu`（$`u\in\pi_0(B)` は単元）なので $`B` は $`(p,\varphi(d))` 完備、したがって（$`d^p\in(p,\varphi(d))` なので）$`(p,d)` 完備。原典 Cor 2.39（系 2.5.5）により、標準射 $`A\to B` のもとで $`B` は $`(d)\subset A` の p 完備化した pd 包と同一視され、特に離散で p ねじれなし（$`d` は mod p で非零因子なので）。

$`\alpha:A\to B` を標準射と $`\varphi:A\to A` の合成とする。$`\alpha(d)\in pB` なので $`\alpha` は prism の射 $`(A,(d))\to(B,(p))` とみなせる。mod p で $`\alpha` は

$$`A/p\xrightarrow{\ \mathrm{can}\ }A/(p,d)\xrightarrow{\ \varphi\ }A/(p,d^p)\xrightarrow{\ \mathrm{can}\ }B/p\simeq D_{(d)}(A/p)\tag{6}`

と分解し、最初の射は有限 Tor 振幅、二番目は構成から忠実平坦、最後は pd 包の構造から忠実平坦（自由でさえある）。この記述から、導来 $`(p,d)` 完備な対象の上の底変換関手 $`\widehat\alpha^*:D_{\mathrm{comp}}(A)\to D_{\mathrm{comp}}(B)` について：

1. $`\widehat\alpha^*` は保存的。

2. $`\widehat\alpha^*` は有限の $`(p,d)` 完全 Tor 振幅を持つ。

3. 任意の p 完全に滑らかな $`A/I` 代数 $`R` とその $`B` への p 完備底変換 $`R_B` について、底変換同型 $`\widehat\alpha^*\Delta_{R/A}\simeq\Delta_{R_B/B}`（原典 Lemma 4.20、命題 4.3.5）。

*定義 6.1.1（原典 Construction 6.1：普遍向き付き prism から結晶 prism へ） — Lean*

*B と α.* 本体は単体的環を経由せず、δ 除算 $`A\{\varphi(d)/p\}` の p 冪ねじれを除いた商 \`coverDivision\`（CrystallineCover:40）の p 完備化の $`H^0` を $`B` とする：\`crystallineCoverRing\`（:52）、p 正則性 \`crystallineCover\_p\_regular\`（:69）、生成元 p の prism \`crystallineCover\`（:96）、有界性 \`crystallineCover\_bounded\`（:146）。$`\alpha(d)\in pB` は \`coverBase\_frobenius\_generator\_mem\`（:119）、prism の射 $`\alpha` は \`crystallineCoverMap\`（:133）。一般の向き付き prism について作り、原典の二つの仮定は以下の補題の引数として入る。

*仮定.* 本体の補題は「$`A/p` の Frobenius が平坦」の代わりに、Frobenius に沿う制限スカラー加群の $`(d)` 完全平坦性と $`A/d` の p 正則性を引数に取る。原典の仮定からこの入力を出すのが \`Construction61.completelyFlat\_of\_flat\`（Construction61Frobenius:52）、普遍の場合の入力は \`universalOrientedPrism\_frobenius\_isCompletelyFlat\`（UniversalOrientedFrobenius:309、原典 Ex 3.4 が示す形）。

*式 (6).* 分解 \`alphaModP\_factorization\`（CrystallineCoverFactorization:107）。中央の射の忠実平坦性 \`residueFrobenius\_faithfullyFlat\`（Construction61Frobenius:71）、最後の射の忠実平坦性 \`coverResidueFlatMap\_faithfullyFlat\`（CrystallineCoverFactorization:97、一元の分冪表示の切断基底から）。合わせて $`\alpha` mod p の通常の Tor 次元は 1 以下：\`torAmplitude\_modP\_le\_one\`（:125）。

*(1) 保存性.* 完備底変換の鎖複体の模型 \`completedCoverModelFunctor\`（Construction61Detection:35、係数拡大の後に標的で p について二度完備化）について、K-flat で $`(p,d)` 完備な複体 $`L` の底変換が非輪状なら $`L` も非輪状：\`cochain\_acyclic\_of\_completedCover\_acyclic\`（:46）。射の形：底変換した射が擬同型なら元の射も擬同型 \`quasiIso\_of\_completedCover\_map\_quasiIso\`（Construction61Reflection:36）、半自由模型の間では同値 \`completedCover\_semifree\_map\_quasiIso\_iff\`（:113）。∞ 圏の関手 $`\widehat\alpha^*` についての形 \`crystallineCoverMap\_conservative\` は drafts（drafts/A1/HodgeTateComparison.lean:199）。

*(2) Tor 振幅.* \`crystallineCoverMap\_torAmplitude\`（CrystallineCoverCompleteTor:39）：$`\alpha` は $`(p,d)` について Koszul 版の完全 Tor 振幅 3 を持つ（\`HasCochainCompleteTorAmplitude\`、上に有界でない複体を含め全ての半自由分解の上で検査）。部品は、mod p の底変換で下界を一つ下げる \`modPBaseChange\_homology\_isZero\_below\`（CrystallineCoverCochainTor:36）と、$`B/p` への射で二つ下げる \`coverMapToModP\_homology\_isZero\_below\`（CrystallineCoverPairTor:135）。

*(3).* 本体にない（drafts）。\`crystallineCoverMap\_prismaticCohomology\`（drafts/A1/HodgeTateComparison.lean:247）、限り方は $`R` が有限変数の完備多項式代数の場合（命題 4.3.5 の Lean の囲み）。drafts には原典どおりの仮定の組 \`Construction61Hypotheses\`（同 :163）も残る。

*定義 6.1.1（原典 Construction 6.1：普遍向き付き prism から結晶 prism へ） — 証明*

*B の性質*（補った）。$`\varphi(d)` は distinguished（$`\delta(\varphi(d))=\varphi(\delta(d))` は単元）で、$`B` の中で $`\varphi(d)=p\cdot(\varphi(d)/p)`。$`p\in\mathrm{rad}(\pi_0B)` なので命題 2.3.6 により $`u=\varphi(d)/p` は単元。よって $`(p,\varphi(d))=(p)` で、$`d^p=\varphi(d)-p\delta(d)\in(p)` なので $`(p,d)` と $`(p)` の根基は等しく、p 完備性から $`(p,d)` 完備性が出る。系 2.5.5 の仮定の確認：$`d` が $`A/p` で非零因子であること。$`dx=py` なら $`A/d` で $`p\bar y=0`、p ねじれなしから $`y=dy'`、$`d(x-py')=0` で $`d` は非零因子なので $`x=py'`。$`A` の p ねじれなしも、$`pa=0` から mod d で $`a\in dA` を繰り返し、$`A` の d 進分離性で $`a=0`。

*式 (6)*（補った）。mod p で $`\varphi(x)\equiv x^p` なので $`\alpha\bmod p` は $`x\mapsto\mathrm{can}(x^p)`。Frobenius は $`(d)` を $`(d^p)` に送るので $`A/(p,d)\to A/(p,d^p)` を誘導し、$`B` で $`d^p=pu-p\delta(d)\in pB` なので最後の射も定まる。中央の射は Frobenius $`A/p\to A/p` の $`A/p\to A/(p,d)` に沿う底変換（$`(A/p)\otimes_{\varphi,A/p}A/(p,d)=A/(p,d^p)`）なので平坦で、Frobenius は Spec の上で全単射なので忠実平坦。$`d` が $`A/p` で正則なので $`D_{(d)}(A/p)` は $`A/(p,d^p)` 上 $`\gamma_{p^k}(d)`（$`k\ge1`）の切断した単項式を基底とする自由加群。最初の射は正則元による商なので Tor 振幅 $`[-1,0]`。

*(1)*。導来 Nakayama（\[Sta, Tag 0G1U\]）により、導来 d 完備な対象の上で、$`A/p\to D_{(d)}(A/p)` に沿う導来 d 完備な底変換が保存的であることを言えばよい。これは (6) の各射について個別に成り立つ：最初は導来 Nakayama、残りは忠実平坦性から。

*(2)*。同様に (6) の合成に沿う導来 d 完備な底変換が有限の d 完全 Tor 振幅を持つことに帰着し、これは各射について成り立つ。

*(3)*。$`\alpha` は (2) により有限の $`(p,d)` 完全 Tor 振幅を持つので、命題 4.3.5 を適用する。

Lean の Tor 振幅の値 3 について（補った）。Lean は振幅を標的の Koszul 複体 $`\mathrm{Kos}(B;p,\alpha(d))` で測る。$`\alpha(d)=pu` なので $`\mathrm{Kos}(B;p,pu)\simeq\mathrm{Kos}(B;p)\otimes\mathrm{Kos}(B;0)` で、零元の Koszul 因子の分だけ一段増える。普遍例で $`K=A_0/(p,d)` とすると $`H^{-3}=B/p\ne0` なので 3 が最良。(6) の通常の Tor 次元 1 以下とは別の量。

*定義 6.1.1（原典 Construction 6.1：普遍向き付き prism から結晶 prism へ） — 原典との差（D77）*

本体の補題は原典の「$`A/p` の Frobenius が平坦」を仮定せず、Frobenius に沿う制限スカラー加群の $`(d)` 完全平坦性と $`A/d` の p 正則性を引数に取る。証明が使うのは式 (6) の中央の射の忠実平坦性だけで、それは $`(d)` 完全平坦性から出る。また $`B` は単体的環としてではなく、δ 除算の p 冪ねじれを除いた商の p 完備化として作る（原典が Cor 2.39 で示す離散性・p ねじれなしを、作り方の側に入れた形）。

:::

:::proposition "bs_6_2"
*命題 6.2*　affine 直線の HT 比較。対応表の状態：なし。

affine line の site 比較と高次消滅の組み立ては drafts。Construction6.1の保存性・Tor 振幅だけはこの結論の直接の部分ではない。

*命題 6.1.2（原典 Prop 6.2：affine 直線の HT 比較） — 主張*

$`R` を多項式環 $`A/I\langle X\rangle`（p 進完備化）とする。このとき原典 Construction 4.9（定義 4.2.1）から（ひねりで）得られる写像 $`\eta^0_R:R\to H^0(\overline\Delta_{R/A})` と $`\eta^1_R\{-1\}:\Omega^1_{R/(A/I)}\{-1\}\to H^1(\overline\Delta_{R/A})` は同型で、$`i\gt1` で $`H^i(\overline\Delta_{R/A})=0`。特に原典 Lemma 4.10（命題 4.2.2）は一般に成り立つ。

*命題 6.1.2（原典 Prop 6.2：affine 直線の HT 比較） — Lean*

本体にない（drafts）。主張そのものは \`affineLine\_moduleComparison\`（drafts/A1/HodgeTateComparison.lean:344）：一般の有界向き付き prism と $`r=1` について \`hodgeTateMapZero\`・\`hodgeTateMapOne\` が全単射で、$`i\gt1` の $`H^i` が零。$`H^i` は Čech–Alexander 模型（注意 4.3.4）の上のコホモロジー。証明の段：$`I=(p)` の場合 \`hodgeTate\_iso\_crystalline\`（同 :62）、Construction 6.1 の仮定を満たす prism の場合 \`hodgeTate\_iso\_of\_construction61\`（同 :262）、底変換関手 $`\widehat b^*`・$`\widehat c^*` \`baseChangeB\`・\`baseChangeC\`（同 :282・290）、$`\widehat b^*` の保存性 \`baseChangeB\_conservative\`（同 :298）、Tot との交換 \`baseChange\_preserves\_affineTot\`（同 :321）、Rem 4.19 の模型の一致 \`baseChange\_cechAlexanderAffine\_eq\`（同 :329）。Lemma 4.10 をここから出す形 \`bockstein\_sq\_zero'\`（同 :358）。

本体にある入力：$`\eta^0`・$`\eta^1` は \`hodgeTateMapZero\`（HodgeTateZero:70）・\`hodgeTateMapOne\`（HodgeTateOneDerivative:215）。結晶基底 $`(\mathbb Z_p,(p))` の HT 比較 \`hodgeTate\_iso\_polynomial\_Zp\`（HodgeTateCartierAssembly:212）。定義 6.1.1 の (1)(2)。本体の Lemma 4.10 \`bockstein\_sq\_zero\`（HodgeTateBocksteinSquare:65）はこの命題を経由しない直接の証明（命題 4.2.2）。

*命題 6.1.2（原典 Prop 6.2：affine 直線の HT 比較） — 証明*

最後の部分（Lemma 4.10）は関手性から（補った：$`f\in R` について $`X\mapsto f` の射 $`A/I\langle X\rangle\to R` を取ると、Bockstein と cup 積の自然性により $`\beta(\eta^0f)^2` は $`\beta(\eta^0X)^2\in H^2(\overline\Delta_{A/I\langle X\rangle/A})=0` の像）。

残りについて、$`D(R)` の射 $`\eta:R\oplus\Omega^1_{R/(A/d)}\{-1\}[-1]\to\overline\Delta_{R/A}` で、コホモロジーに $`\eta^i_R`（$`i=0,1`）を誘導するものを選ぶ。$`R` と $`\Omega^1_{R/(A/d)}` は $`R` 上有限自由なので選べる（補った：射影加群 $`M` について $`\mathrm{Hom}_{D(R)}(M[-i],K)=\mathrm{Hom}_R(M,H^i(K))`）。$`\eta` が同型であることを示す。これは主張と同値。

\*\*$`I=(p)` の場合\*\*：標数 p の HT 比較（原典 Cor 5.5）。

\*\*普遍向き付き prism $`(A_0,(d))` の場合\*\*：定義 6.1.1 の $`\alpha` で $`I=(p)` の場合に底変換し、性質 (1)(3) を使う。（補った）$`\eta` の両辺は p 完備で $`d` が零に働くので $`(p,d)` 完備。(3) を $`d` で割った形で $`\widehat\alpha^*\overline\Delta_{R/A_0}\simeq\overline\Delta_{R_B/B}`（$`R_B=(B/p)\langle X\rangle`）、HT 写像の関手性で $`\widehat\alpha^*\eta` は $`R_B/B` の $`\eta` に移る。後者は $`I=(p)` の場合で同型、(1) で $`\eta` も同型。

\*\*一般の有界向き付き prism $`(A,(d))`\*\*：生成元 $`d` の選択が $`A_0\to A` を定める。$`A_0\to A` が有限の $`(p,I)` 完全 Tor 振幅を持てば（または prismatic cohomology の底変換を一般に知っていれば）命題 4.3.5 で済むが、次のように進める。$`a:A_0\to D_0` を定義 6.1.1 の $`\alpha` とし、

$$`\begin{array}{ccccc}&&A_0&\longrightarrow&A\\&&{\scriptstyle a}\downarrow&&\downarrow{\scriptstyle b}\\ \mathbb Z_p&\longrightarrow&D_0&\longrightarrow&E:=A\widehat\otimes^L_{A_0}D_0\end{array}`

を $`(p,d)` 完備な単体的可換環の図式とする（正方形は押し出し）。左下の射は $`(p)=(a(d))` なので prism の射 $`(\mathbb Z_p,(p))\to(D_0,(a(d)))` に持ち上がる。合成 $`\mathbb Z_p\to E` を $`c` と書く。$`\widehat b^*` は $`(p,d)` 完備な対象の上で保存的（$`\widehat a^*` がそうなので。補った：$`\widehat b^*K=\widehat a^*(K|_{A_0})` で、制限は保存的で完備性を保つ）。よって $`\widehat b^*\eta` が同型であることを示せばよい。

$`\widehat b^*\overline\Delta_{R/A}\simeq\widehat c^*\overline\Delta_{\mathbb F_p[X]/\mathbb Z_p}` である。これは原典 Remark 4.19（注意 4.3.4）の複体の段階で明らか（補った：項ごとに $`C^n_{R/A}=C^n_{A_0}\widehat\otimes_{A_0}A` なので $`C^n_{R/A}\widehat\otimes_AE=C^n_{A_0}\widehat\otimes_{A_0}D_0\widehat\otimes_{D_0}E`、さらに $`C^n_{A_0}\widehat\otimes_{A_0}D_0=C^n_{D_0}=C^n_{\mathbb Z_p}\widehat\otimes_{\mathbb Z_p}D_0`）。Tot との交換は原典 Lemma 4.22（命題 4.3.7）と、$`b`（resp. $`c`）が有限の $`(p,d)` 完全（resp. p 完全）Tor 振幅を持つことから（補った：$`b` は $`a` の底変換で (2) から。$`\mathbb Z_p` 加群は Tor 振幅 $`[-1,0]` なので $`c` も）。この同一視で $`\widehat b^*\eta` が標的側の HT 比較写像を実現する写像に移ることは原典が読者に任せている（補った：$`\eta` はコホモロジーの $`\eta^0,\eta^1` で決まり、それらは関手的なので生成元 $`X`・$`dX` の行き先で照合できる）。こうして $`\overline\Delta_{\mathbb F_p[X]/\mathbb Z_p}` の HT 比較（原典 Cor 5.5）に帰着する。

*一般の有界 prism*：有界向き付き prism への忠実平坦な底変換（原典 Lemma 3.7(4)、命題 3.2.3）で前段に帰着する。

*命題 6.1.2（原典 Prop 6.2：affine 直線の HT 比較） — 原典との差（D30・D5）*

D30：単体的可換環 $`E=A\widehat\otimes^L_{A_0}D_0` は作らず、$`\widehat b^*:=\widehat a^*\circ\mathrm{Res}_{A_0}`、$`\widehat c^*:=\widehat a^*\circ\mathrm{Res}_{A_0}\circ(-\otimes^L_{\mathbb Z_p}A)` と通常の環の底変換と制限の合成で書く。D5：Lean の対象は向き付き prism だけなので、最後の段（Lemma 3.7(4) による帰着）は要らない。Lean の主張は Čech–Alexander 模型のコホモロジーについてのもの（定理 6.1.3 の D27）。

宣言：`hodgeTate_iso_of_construction61`、`affineLine_moduleComparison`、`hodgeTate_iso`、`bockstein_sq_zero'`

:::

:::theorem "bs_6_3"
*定理 6.3*　HT 比較。対応表の状態：なし。

本体は模型上の HodgeTateMap・HodgeTateIsoStatement と結晶基底の結果。一般の site の cohomology sheaf との比較と向き付き基底への帰着は drafts。

*定理 6.1.3（原典 Thm 6.3：HT 比較） — 主張*

$`X` を滑らかな p 進形式 $`A/I` スキームとする。原典 Construction 4.9（定義 4.2.1）の HT 比較写像

$$`\Omega^i_{X/(A/I)}\to H^i(\overline\Delta_{X/A})\{i\}`

は $`X_{\mathrm{\acute et}}` 上の層の同型である。

*定理 6.1.3（原典 Thm 6.3：HT 比較） — Lean*

主張の型は本体：\`HodgeTateIsoStatement\`（HodgeTateCompletedMap:461）は、HT 写像 \`hodgeTateMap\`（:398）の各次数の成分が全単射であること。\`hodgeTateMap\` は乗法的な写像の構造 \`HTAlgebraMap\`（:388：次数 0・1 で $`\eta^0,\eta^1` に一致し、外積を cup 積に、de Rham 微分を Bockstein に送る）の元で、一意性は \`hodgeTateMap\_unique\`（:408）。限り方：$`X=\mathrm{Spf}\,R`、$`R=(A/d)\langle X_1,\dots,X_r\rangle` の場合だけで、$`H^i` は Čech–Alexander 模型 \`reducedModel\`（HodgeTateAffineModel:93）のコホモロジー。

*定理 6.1.3（原典 Thm 6.3：HT 比較） — 証明*

比較写像は大域的に定義されているので affine の場合を示せば十分。すなわち任意の p 完全に滑らかな $`A/I` 代数 $`R` について、$`\Omega^i_{R/(A/I)}\to H^i(\overline\Delta_{R/A})\{i\}` が $`R` 加群の同型であることを示す。微分形式も prismatic cohomology も étale 位相で局所化する（原典 Lemma 4.21、命題 4.3.6）ので、$`R=A/I\langle X_1,\dots,X_n\rangle`（多項式環の p 進完備化）の場合を示せばよい（補った：$`R` は局所的に多項式代数上 p 完全 étale で、両辺は $`-\widehat\otimes^L_RS` と両立し、HT 写像も関手的）。この場合、コホモロジーで（ひねりを除いて）HT 比較写像を持ち上げる $`D(R)` の射

$$`\eta:\bigoplus_{i=0}^n\Omega^i_{R/(A/I)}\{-i\}[-i]\to\overline\Delta_{R/A}`

を選び（$`\Omega^i` は有限自由）、命題 6.1.2 で $`n=1` について説明したとおりに進める（補った：$`\widehat b^*\overline\Delta_{R/A}\simeq\widehat c^*\overline\Delta_{\mathbb F_p[X_1,\dots,X_n]/\mathbb Z_p}` も Rem 4.19 の $`n` 変数の複体で項ごとに同じ。$`\eta` の $`i\ge2` の成分が HT 写像に合うことは、$`\eta^*` が乗法的で $`\eta^1` で生成されることから）。HT 写像の存在（Lemma 4.10）は命題 6.1.2 で示してあるので循環しない。

*定理 6.1.3（原典 Thm 6.3：HT 比較） — 原典との差（D27・D29・D24）*

D29：主張は最初から $`r` 変数の完備多項式代数についてで、定理の範囲を多項式代数に絞る。D24：滑らかな代数・形式スキームへの延長（étale 局所化）は述べない。D27：$`H^*(\overline\Delta)` とその環構造は Čech–Alexander 模型の上で述べる（定義 4.2.1 から参照）。

宣言：`hodgeTate_iso`、`SerrePositivity.BhattScholze.Prismatic.HodgeTateIsoStatement`、`SerrePositivity.BhattScholze.Prismatic.hodgeTateMap`

:::

:::theorem "bs_6_4"
*定理 6.4*　de Rham 比較。対応表の状態：なし。

Witt の prism と模型間の completed derived quasiIso は本体にある。原文の site Δ の φ-pullback と de Rham の自然同型への比較は未供給で、部品を partial としない。

*定理 6.1.4（原典 Thm 6.4：de Rham 比較） — 主張*

（原典の前置き）prismatic cohomology の底変換（原典 Cor 4.12、Thm 6.3 を使って示した。系 4.2.4）を使うと、$`W(A/I)` が p ねじれなしという技術的な仮定のもとで de Rham 比較が示せる。この仮定は例えば $`A/I` が p ねじれなしのとき、または $`I=(p)` で $`A/p` が被約のとき満たされる。この仮定は後で外される（原典 Cor 15.4）。

$`X` を滑らかな形式 $`A/I` スキームとし、$`W(A/I)` が p ねじれなしと仮定する。このとき $`D(X_{\mathrm{\acute et}},A/I)` の可換代数の自然な同型

$$`\Delta_{X/A}\widehat\otimes^L_{A,\varphi}A/I\simeq\Omega^*_{X/(A/I)}`

がある（完備化は p 進）。

*定理 6.1.4（原典 Thm 6.4：de Rham 比較） — Lean*

*主張の形.* 本体にない（drafts）。\`deRham\_iso\_polynomial\_modP\`（drafts/A1/DeRhamComparisonPoly.lean:432）。限り方：基底は完全 prism、$`R` は有限変数の完備多項式代数、標的は mod p（$`\varphi^*\Delta\widehat\otimes A/(p,d)\simeq\Omega^*\otimes\mathbb F_p`）で、多項式代数の圏 Poly の上の関手（CAlg 値）の同型として述べる。普遍向き付き prism $`A_0` の上の同型 \`deRham\_iso\_polynomial\_universal\`（同 :399）、その組み立て \`bigZigzagIso\`（同 :356）、一般の基底への移送 \`transferWittComparison\`（同 :424）。根を添えた代数への延長 \`deRham\_iso\_rootAlgebra\_modP\`（同 :494）は第 8 章 Lemma 8.6 の入力。これらの drafts の同型は Tot の E∞ 構造を要する。

*模型と橋（本体）.* 大きい Čech–Alexander 模型 \`bigCechAlexander\`（BigCechAffineEnvelope:420）、$`W` 上の大きい pd Čech 模型 \`wittBigPdModel\`（BigPDModel:125）、その間の厳密な橋 \`wittBigBridge\`（WittBigBridge:378）と、$`\psi` に沿う完備係数変更の後の擬同型 \`wittBigCompletedBridge\_quasiIso\`（WittBigCompletedBridge:95）・Poly 上の自然性（:125）。$`w_0` に沿う第二の比較 \`wittToSmall\`（WittToSmall:283）、完備係数変更の後の擬同型 \`wittToSmallCompletedBridge\_quasiIso\`（WittToSmallCompletedBridge:68）、完備導来底変換の形 \`wittToSmallDerivedCompletedIso\`（WittPDCompletedDerivedModel:187）。橋はいずれも多項式代数の圏 Poly($`C`) 上で厳密に自然。pd Čech 複体と完備 de Rham 複体の二射影：\`crystallinePolynomialTotalToCech\_quasiIso\`（CrystallinePolynomialSpan:60）と \`pdDeRhamTotalToCompletedForms\_quasiIso\`（PDDeRhamCompletedColumnZero:142）。

*結晶 site（本体と drafts）.* affine big crystalline site \`CrystallineSite\`（CrystallineSiteSmall:105）、構造層の層性 \`crystallineStructure\_isSheaf\`（CrystallineSmallStructureSheaf:64）、pd Čech の塔 \`pdCechTower\`（PDCechCrystallineTower:80）とその pro 弱終性 \`pdCechSmallTowerOfCutoff\_proWeaklyTerminal\`（CrystallineCechCutoff:62）。$`R\Gamma_{\mathrm{crys}}` の定義 \`crystallineCohomology\` は drafts（drafts/A1/CrystallineSite.lean:313）。

*定理 6.1.4（原典 Thm 6.4：de Rham 比較） — 証明*

前と同じく affine の場合に帰着する。p 完全に滑らかな $`A/I` 代数 $`R` について、$`D(A/I)` の可換代数の関手的な同型 $`\Delta_{R/A}\widehat\otimes^L_{A,\varphi}A/I\simeq\Omega^*_{R/(A/I)}` を作る。両辺を結晶コホモロジーに結ぶ強い主張を示す。

*準備.* 標準的な全射の合成 $`W(A/I)\to A/I\to A/(I,p)` の核 $`J\subset W(A/I)` は pd イデアル（補った：$`J=VW(A/I)+pW(A/I)`。p を反転した環で $`\gamma_m(Vx)=\frac{p^{m-1}}{m!}V(x^m)`、$`\gamma_m(pa)=\frac{p^m}{m!}a^m` と計算でき、係数は p 局所整数なので $`J` に戻る。p ねじれなしで二つの式は重なりで一致する）。結晶コホモロジーの一般論により、可換代数 $`R\Gamma_{\mathrm{crys}}((R/p)/W(A/I))\in D(W(A/I))` は de Rham 複体 $`\Omega^*_{R/(A/I)}\in D(A/I)` を持ち上げる（補った：$`w_0:W(A/I)\to A/I` に沿う底変換が $`R\Gamma_{\mathrm{crys}}((R/p)/(A/I))` で、$`R` は $`R/p` の滑らかな持ち上げなので Poincaré 補題により $`\Omega^*_{R/(A/I)}`）。一方、$`A\to A/I` は原典 Remark 2.7（命題 2.1.9）により δ 射 $`A\to W(A/I)` に一意に持ち上がる。したがって $`\psi:A\to W(A/I)` を標準射と Frobenius の合成として、$`D(W(A/I))` の可換代数の関手的な同型

$$`\Delta_{R/A}\widehat\otimes^L_{A,\psi}W(A/I)\simeq R\Gamma_{\mathrm{crys}}((R/p)/W(A/I))`

を作れば十分（補った：$`w_0\circ F` は第一ゴースト成分なので、$`w_0\circ\psi` は $`\varphi_A` の後に $`A/I` へ射影する射。よって左辺の $`w_0` に沿う底変換は $`\Delta_{R/A}\widehat\otimes^L_{A,\varphi}A/I`）。これを結晶比較から導く。

*ψ は prism の射.* 標準射 $`A\to W(A/I)` は $`I` を $`VW(A/I)` に送る（第 0 成分が零）ので、$`\psi` は $`I` を $`FVW(A/I)=(p)` に送る。$`W(A/I)` の p ねじれなしの仮定により、$`\psi` は prism の射 $`(A,I)\to(W(A/I),(p))` に精密化される。prismatic cohomology の底変換（系 4.2.4）により

$$`\Delta_{R/A}\widehat\otimes^L_{A,\psi}W(A/I)\cong\Delta_{R'/W(A/I)},\qquad R'=R\widehat\otimes_{A/I,\psi}W(A/I)/p.`

あとは右辺を $`R\Gamma_{\mathrm{crys}}((R/p)/W(A/I))` と同一視すればよい。これは pd イデアル $`J\subset W(A/I)` に原典 Thm 5.2 を適用し、$`R'` が $`R/p` の $`W(A/I)/J\simeq A/(p,I)\to W(A/I)/p`（$`W(A/I)` の Frobenius が誘導する）に沿う底変換であることに注意すれば従う。

仮定の例について（補った）。$`S` が p ねじれなしならゴースト写像が単射で $`W(S)` も p ねじれなし。$`S` が被約な $`\mathbb F_p` 代数なら $`p=VF` で $`F`（被約性）と $`V` が単射なので $`W(S)` は p ねじれなし。

*定理 6.1.4（原典 Thm 6.4：de Rham 比較） — 原典との差（D69・D25・D68）*

D69：Lean は原典の証明を普遍向き付き prism $`A_0` の上で行い（$`A_0/d_0` は p ねじれなしなので $`W(A_0/d_0)` も p ねじれなしで、技術的な仮定が成り立つ）、完全 prism へは $`A_0\to A` に沿う底変換で移す。最後に $`w_0:W\to C=A_0/d_0` に沿う底変換を取って $`\varphi_0^*\Delta_{T_0/A_0}\widehat\otimes^L_{A_0}C\simeq\Omega^*_{T_0/C}` の形にする。本体の模型と橋は、$`A` と $`A/I` が p 正則な一般の有界向き付き prism について作ってある。D25：$`R\Gamma_{\mathrm{crys}}` の結晶 site は最小限（affine な対象、Zariski 位相、p 冪零、cutoff κ）で原典どおり定義する（5.1 節）。D68：結晶比較（原典 Thm 5.2）は一般形ではなく、ここで要る多項式の場合の比較として使う（5.1 節）。原典 Cor 15.4 による仮定の除去は要らない。

宣言：`SerrePositivity.BhattScholze.Prismatic.wittCrystallineDelta`、`SerrePositivity.BhattScholze.Prismatic.UniversalOrientedResidue`、`SerrePositivity.BhattScholze.Prismatic.psiPrism`、`SerrePositivity.BhattScholze.Prismatic.wittBigCompletedBridge_quasiIso`、`SerrePositivity.BhattScholze.Prismatic.wittToSmallCompletedBridge_quasiIso`、`SerrePositivity.BhattScholze.Prismatic.wittToSmallDerivedCompletedIso`

:::

