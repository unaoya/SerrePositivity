import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.BhattScholze.Inputs.PerfectoidizationInterface
import SerrePositivity.BhattScholze.Perfectoidization.Arc.Site.ArcSite
import SerrePositivity.BhattScholze.Perfectoidization.Interface.Derived
import SerrePositivity.BhattScholze.Perfectoidization.Interface.Excision
import SerrePositivity.BhattScholze.Perfectoidization.TensorCompatibility

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "§8 " =>
%%%
number := false
tag := "bs-8"
%%%

BS §8 の項目と、本体の宣言との対応。本文は対応表（`research/bs-coverage`）の照合の理由で、原典の本文の写しではない。

*1. E3 とは何か*

$`R` を perfectoid 環とする。原典 Def 8.2 は、$`R` 代数 $`S` に $`p` 完備な $`E_\infty`-$`S` 代数 $`S_{\mathrm{perfd}}` を対応させる（導来 prismatic コホモロジーの Frobenius 余極限を完備化し、$`\bmod d` したもの）。$`S` が perfectoid 環の商（semiperfectoid）なら離散で、$`S` から perfectoid 環への普遍写像になる。一般の $`S` では離散とは限らない。

*導入*

§8 は perfectoid 環 $`R=A/I` 上の任意の（導来 p 完備な単体的）代数 $`S` の perfectoid 化 $`S_{\mathrm{perfd}}` を導来対象として定義し（Def 8.2）、perfectoid 環への写像の極限として描き（Prop 8.5）、arc 位相での降下と excision（Cor 8.11・8.12）、テンソルとの両立（Prop 8.13）、離散な場合の普遍性（Cor 8.14）を示す。形式化では Def 8.2・Prop 8.5・Cor 8.12・Cor 8.14 を界面 \`PerfectoidizationInterfaceE3\`（Derived/Interface:671）の欄として受け取り、その存在 \`exists\_perfectoidizationInterfaceE3\`（Inputs/PerfectoidizationInterface:54）を引用して、そこから環の帰結を証明している。arc 位相のうち 1 圏で述べられる部分（arc 被覆と位相、Lemma 8.8 の affine 版、Prop 8.10 の BM18 の経路の部品）と、Prop 8.5 の証明で使う根添加は、界面に依らずに本体で証明されている。導来の定義と証明の骨組みは drafts にある。形式化の設計の決定は a4-design.md〜a7-design.md にあり、原典との差として各項目の下に引く。

*8.1 定義と coconnective 性*

perfectoid 環 $`R` 上の任意の（導来 p 完備な単体的）代数 $`S` に対し、導来 prismatic コホモロジー $`\Delta_{S/A}`（第 7 章）を Frobenius に沿って完全化し、$`A/I` に落としたものとして perfectoid 化 $`S_{\mathrm{perfd}}` を定める。この小節では定義と、二つの基本的な性質を見る：標数 p では通常の完全化に一致すること（例 8.1.3）と、$`\Delta_{S/A,\mathrm{perf}}`・$`S_{\mathrm{perfd}}` が coconnective であること（命題 8.1.4）。後者の鍵は E∞-$`\mathbb F_p` 代数のべき作用素 $`P^0` で、「Frobenius が可逆なら正次数のホモトピーが消える」という形で効く。定義が基底 $`A` によらないこと、semiperfectoid の場合に第 7 章の perfectoid 化（Cor 7.3）と一致することは、次の小節の命題 8.2.1 から出る。

*8.2 perfectoid 環への写像の極限*

$`S` を上のとおりとする。完全 prismatic site $`(S/A)^{\mathrm{perf}}_\Delta` を（原典 Rem 4.6 のように）$`(A,I)` 上の完全 prism $`(B,IB)` に $`A/I` 代数の写像 $`S\to B/IB` を添えたものの圏とする。$`B/IB` は離散なので $`(S/A)^{\mathrm{perf}}_\Delta=(\pi_0(S)/A)^{\mathrm{perf}}_\Delta`。さらに原典 Lemma 4.8 により、この site は「$`S\to T`、$`T` は perfectoid 環」の圏そのもの（$`(B,J)\mapsto B/J`）なので、$`(A,I)` にも構造写像 $`A/I\to S` にもよらない。原典 Lemma 7.7 により $`(B,J)\in(S/A)^{\mathrm{perf}}_\Delta` について関手的な写像 $`\Delta_{S/A}\to B` があり、左辺を完全化し（$`B` は完全なので写像は $`\Delta_{S/A,\mathrm{perf}}` を経由する）右辺で全ての $`B` の極限を取ると、比較写像
$$`\Delta_{S/A,\mathrm{perf}}\to R\Gamma\bigl((S/A)^{\mathrm{perf}}_\Delta,\mathcal O_\Delta\bigr)`
を得る。この小節の主定理はこれが同値であること（命題 8.2.1）で、とくに $`S_{\mathrm{perfd}}` は $`S` から perfectoid 環への写像全体の極限になる。

Lean（drafts、drafts/A5/PerfectSite）：site \`perfectSite\`（:65、濃度 $`\le\kappa` の完全 prism の圏）とその flat 位相 \`perfectFlatTopology\`（:80）、Lemma 4.8 の系の圏同値 \`perfectSiteEquivPerfectoidUnder\`（:267）、構造前層 \`perfectStructurePresheaf\`（:194）とその flat 層性 \`perfectStructurePresheaf\_isSheaf\`（:220）、Lemma 7.7 の関手的な写像の束 \`prismaticEvaluation\`（:349）、比較写像 \`perfectionComparison\`（:408）。

*8.3 arc 降下と excision*

Prop 8.5（perfectoid 標的の極限としての $`S_{\mathrm{perfd}}`）から、$`S\mapsto S_{\mathrm{perfd}}` の強い降下を導く。位相は \[BM18\] の arc 位相で、試験対象は p 完備な階数 1 の付値環。perfectoid 環は arc 位相の基底をなし（Lemma 8.8）、その上では構造層 $`\mathcal O` が高次コホモロジーをもたない arc 層になる（Prop 8.10）。両者を合わせると $`S_{\mathrm{perfd}}=R\Gamma_{\mathrm{arc}}(\mathrm{Spf}S,\mathcal O)`（Cor 8.11）で、帰結として excision（Cor 8.12）が出る。原典の脚注 13 のとおり、応用には少し弱い v 位相でも足りるが、原典は最適な形を目指して arc 位相を使う。

Prop 8.10 の証明の芯は、tilt による標数 p への帰着と、完全スキームの arc 被覆に対する Čech 複体の完全性である。後者を原典は \[BS17, Thm 4.1\]（v 降下）・\[BM18, Thm 1.6\]（arc 降下の判定）・\[BS17, Lemma 6.3\]（付値環の四角形）の引用で済ませる。

*8.4 テンソルとの両立と離散な場合の普遍性*

導来 prismatic コホモロジーによる $`S_{\mathrm{perfd}}` の定義の利点は、対称モノイダル性がそのまま従うことである（Prop 8.13）。これを使うと、$`S_{\mathrm{perfd}}` が離散のとき $`S\to S_{\mathrm{perfd}}` が perfectoid 環への普遍な写像であることがわかる（Cor 8.14）。

*導入*

自分用の読解ノート。Bhatt–Scholze『Prisms and prismatic cohomology』（著者版 paper/refs/BS-prisms-author.pdf、番号はすべて著者版）を、主定理が使う範囲に絞って最初から読み、\`SerrePositivity/BhattScholze/\` の形式化と照らし合わせる。

:::definition "bs_8_1"
*記法 8.1*　設定。対応表の状態：なし。

固定した Ainf(R)・ideal・distinguished 元を束ねる記法は drafts。本体には個々の perfect prism 表示があるが、この正本の構成としては未接続。

*定義 8.1.1（原典 Notation 8.1：基底の完全 prism） — 主張*

perfectoid 環 $`R` と、それに対応する完全 prism $`(A,I)`（$`A/I\cong R`、原典 Thm 3.10）を固定する。記法の便宜のため distinguished な元 $`d\in I` を一つ固定する（これは自動的に $`I` の生成元である）。

*定義 8.1.1（原典 Notation 8.1：基底の完全 prism） — Lean*

本体にあるのは対応の非零の枝（$`p` が $`R` の単元でない場合）：Fontaine の $`\theta` の核の distinguished な生成元 \`exists\_distinguished\_fontaine\_kernel\_generator\`（PerfectPrismPerfectoid:121）と、perfectoid 環から完全 prism と商の同型を作る \`exists\_perfectoidTrialPrism\`（:383）。

固定した基底としてまとめたものは drafts（drafts/A4/Perfectoidization）：係数環 \`perfectPrismCoefficients\`（:59、$`A=A_{\inf}(R)=W(R^\flat)`。$`p` が単元のとき $`R` は零環で、$`A=R`）とその台 \`perfectPrismRing\`（:65）、$`\theta\colon A\to R` \`perfectPrismTheta\`（:67）、δ 構造 \`perfectPrismDelta\`（:76）、$`\ker\theta` の distinguished な生成元を選んで向きを決める \`exists\_perfectPrismOverTheta\`（:84）、向き付き prism \`perfectPrism\`（:90）、完全性 \`perfectPrism\_isPerfect\`（:93）、有界性 \`perfectPrism\_bounded\`（:96）、$`A/(d)\cong R` \`perfectPrism\_quotientEquiv\`（:99）。Lean の prism は向き付き（\`OrientedPrism\`：生成元 $`d` をデータとして持つ）なので、「$`d` を一つ固定する」は型に入っている。

*定義 8.1.1（原典 Notation 8.1：基底の完全 prism） — 証明*

（補った）$`d` が $`I` を生成すること。$`A` は $`(p,I)` 完備で $`d\in I` なので $`(p,d)` 完備。$`d` は distinguished なので $`\varphi(d)=d^p+p\delta(d)` で $`\delta(d)` は単元、よって $`p=\delta(d)^{-1}(\varphi(d)-d^p)\in(d,\varphi(d))`。また完全で p 完備な δ 環では distinguished な元は非零因子（原典 Lemma 2.34）。したがって $`(A,(d))` も prism で、恒等写像は prism の射 $`(A,(d))\to(A,I)` になる。剛性（原典 Lemma 3.5）から $`I=dA`。

*定義 8.1.1（原典 Notation 8.1：基底の完全 prism） — 原典との差*

原典は $`R` に対応する完全 prism を一つ取るだけで、具体的な形を指定しない。Lean の drafts は $`A=W(R^\flat)` と $`\ker\theta` の生成元を選んで固定し、零環の場合を別の枝として含める。別の完全 prism を取っても結果が変わらないことは、命題 8.2.1 の系として述べる（そこの Lean の囲みの \`perfectoidization\_indep\`）。

宣言：`perfectPrism`、`perfectPrismRing`

:::

:::definition "bs_8_2" (lean := "SerrePositivity.BhattScholze.PerfectoidizationInterface.PerfectoidizationInterfaceE3, SerrePositivity.BhattScholze.Inputs.exists_perfectoidizationInterfaceE3")
*定義 8.2*　perfectoid 化 S\_perfd。対応表の状態：未証明の入力に依存。

通常の離散 R-代数上の底の D(R) 関手 perfd・unit・H⁰ を E3 の存在 sorry から受け取る。原文の animated 定義域、Δ の φ-perfection と底変換の式および E∞ 構造を実装したものではない。

*定義 8.1.2（原典 Def 8.2：perfectoid 化） — 主張*

導来 p 完備な単体的 $`R` 代数 $`S` を固定する。

(1) $`\Delta_{S/A}` の完全化 $`\Delta_{S/A,\mathrm{perf}}` を
$$`\Delta_{S/A,\mathrm{perf}}:=\Bigl(\mathrm{colim}\bigl(\Delta_{S/A}\xrightarrow{\varphi_S}\varphi_*\Delta_{S/A}\xrightarrow{\varphi_S}\varphi^2_*\Delta_{S/A}\to\cdots\bigr)\Bigr)^\wedge\in D(A)`
で定める（$`\wedge` は導来 $`(p,I)` 完備化）。これは導来 $`(p,I)` 完備な E∞-$`A` 代数で、$`\varphi_S` が誘導する $`\varphi_A` 半線形な自己同型を持つ。

(2) $`S` の perfectoid 化 $`S_{\mathrm{perfd}}` を
$$`S_{\mathrm{perfd}}:=\Delta_{S/A,\mathrm{perf}}\otimes^L_AA/I\in D(R)`
で定める。これは p 完備な E∞-$`S` 代数である。

$`S_{\mathrm{perfd}}` は一見 perfectoid な基底 $`A` の取り方によるが、命題 8.2.1 からよらないことが分かる。同じ命題から、定義 (2) は Cor 7.3 と両立する。

*定義 8.1.2（原典 Def 8.2：perfectoid 化） — Lean*

E3 の界面 \`PerfectoidizationInterfaceE3\`（Derived/Interface:671）の欄 \`perfd\`・\`unit\`・\`h0\`（:674・676・678）。\`perfd\` は（Type u の）離散 $`R` 代数の圏の nerve から $`D(R)` の ∞ 圏への関手で、値は $`S_{\mathrm{perfd}}` の $`D(R)` での台だけ（$`\Delta` の完全化と底変換の式、E∞ 構造は型に現れない）。\`unit\` は離散な埋め込みからのホモトピー整合的な自然変換 $`S\to S_{\mathrm{perfd}}`、\`h0\` は $`H^0(S_{\mathrm{perfd}})` の環構造と、射・単位との整合（\`H0RingData\`、:477）。界面の存在は \`exists\_perfectoidizationInterfaceE3\`（Inputs/PerfectoidizationInterface:54）として引用している（sorry）。

定義そのものは drafts（drafts/A4/Perfectoidization、離散で導来 p 完備な $`S`、値は $`\mathrm{CAlg}_A`・$`\mathrm{CAlg}_R`）：Frobenius の塔 $`\Delta_S\to\varphi_{A*}\Delta_S\to\varphi_{A*}^2\Delta_S\to\cdots` \`frobeniusTower\`（:150、遷移射は $`\varphi_{A*}^n(\varphi)`、塔の本体は \`directTower\`、:141）、(1) \`prismaticPerfection\`（:197）、$`\varphi_A` 半線形な自己同型 \`prismaticPerfectionFrobenius\`（:218）、(2) \`perfectoidization\`（:240）、その $`D(R)` への忘却 \`perfectoidizationDerived\`（:248）。E3 の欄への接続は drafts/A4/InterfaceFields の \`e3Perfd\`（:94、$`S\mapsto(S^\wedge)_{\mathrm{perfd}}`、$`S^\wedge` は導来 p 完備化の $`H^0` \`completionRing\`、Derived/Interface:206）、\`e3Unit\`（InterfaceFields:176）、\`e3H0RingData\`（:215）。原典の定義域（導来 p 完備な animated $`R` 代数）での版は \`prismaticPerfectionAnimated\`・\`perfectoidizationAnimated\`（drafts/A7/AnimatedPerfectoidization:173・181）で、離散版はその制限 \`perfectoidizationAnimated\_discrete\`（:189）。

*定義 8.1.2（原典 Def 8.2：perfectoid 化） — 証明*

（補った）定義に添えられた主張の確かめ。

*自己同型.* 塔の各遷移射は $`\varphi_S` で、余極限の上では「塔を一つずらす」写像 $`\mathrm{colim}_n\varphi^n_*\Delta\to\mathrm{colim}_n\varphi^{n+1}_*\Delta=\varphi_*(\mathrm{colim}_n\varphi^n_*\Delta)` が $`\varphi_S` から誘導される。添字を一つずらすのは共終なので、これは同値。$`\varphi_A` が自己同型（$`A` は完全）なので $`\varphi_*` は完備性を保ち、完備化の後も自己同型が残る。

\*\*E∞-$`S` 代数.\*\* Hodge–Tate の構造写像 $`S\to\overline\Delta_{S/A}=\Delta_{S/A}\otimes^L_AA/I`（多項式代数で作って左 Kan 拡張したもの）に、塔の第 0 脚 $`\Delta_{S/A}\to\Delta_{S/A,\mathrm{perf}}` を $`A/I` に落としたものを合成する。

*p 完備.* $`\otimes^L_AA/I` は $`d` の cofiber なので $`(p,I)` 完備性を保ち、$`I` で消える対象の $`(p,I)` 完備性は p 完備性と同じ。

*定義 8.1.2（原典 Def 8.2：perfectoid 化） — 原典との差（D41・D60・D35）*

定義域：原典は導来 p 完備な単体的 $`R` 代数。drafts の A4 の定義は離散で導来 p 完備な $`S` の場合で、原典の定義域での定義は A7 の animated 版に置き、離散版はその制限とする（D60）。E3 の欄 \`perfd\` は p 完備でない離散 $`S` にも値を持ち、$`S^\wedge`（導来 p 完備化の $`H^0`）を経由して $`(S^\wedge)_{\mathrm{perfd}}` と定める。$`S` 自身に原典の式を当てたものと一致することは定理として扱う（\`e3Perfd\_eq\_direct\`、drafts/A4/AfterComparison:49。導来完備化で $`\Delta` が変わらないことと、命題 8.2.1 の系「$`\pi_0` だけによる」の二段、D41）。値は E∞ 代数の ∞ 圏 $`\mathrm{CAlg}_A`・$`\mathrm{CAlg}_R` に取り、E3 の界面では $`D(R)` への忘却と $`H^0` の環構造だけを欄にする（D35）。

:::

:::proposition "bs_8_3"
*例 8.3*　標数 p の場合。対応表の状態：なし。

標数 p で指定した derived perfectoidization と通常の perfection が一致する宣言は drafts。通常環の perfection の存在だけでは同じ比較を示さない。

*例 8.1.3（原典 Ex 8.3：標数 p の環の perfectoid 化） — 主張*

$`S` を $`p=0` となる $`R` 代数とする。このとき $`S_{\mathrm{perfd}}` は通常の（順極限による）完全化 $`S_{\mathrm{perf}}=\mathrm{colim}_\varphi S` に一致する。

*例 8.1.3（原典 Ex 8.3：標数 p の環の perfectoid 化） — 証明*

$`S_{\mathrm{perfd}}` は基底によらない（命題 8.2.1）ので、$`A=\mathbb Z_p`、$`I=(p)`、$`R=\mathbb F_p` としてよい。このとき $`S_{\mathrm{perfd}}=\Delta_{S/A,\mathrm{perf}}/p` で、mod p では完備化は効かないので $`S_{\mathrm{perfd}}=\mathrm{colim}_\varphi(\Delta_{S/A}/p)`。導来 Hodge–Tate 比較から来る Frobenius 同変な写像 $`S\to\Delta_{S/A}/p` が完全化の上で同型になることを示せばよい。

（補った）$`\Delta_{S/A}/p=\overline\Delta_{S/A}` は網羅的な共役 filtration $`\mathrm{Fil}_\bullet` を持ち、$`\mathrm{gr}_i=\wedge^iL_{S/\mathbb F_p}[-i]`、$`\mathrm{Fil}_0=S`。$`\varphi` は filtration を保つ。原典は $`\mathrm{gr}_i` 上で $`\varphi` が誘導する自己準同型が $`S` の Frobenius から誘導されるものだと述べ、確かめは $`S=\mathbb F_p[x]` に帰着できるとする。$`S` の Frobenius は $`L_{S/\mathbb F_p}` 上で零（$`d(x^p)=px^{p-1}dx=0`）なので、$`\wedge^iL` 上で、したがって $`i\ne0` の $`\mathrm{gr}_i` 上で零。よって $`\mathrm{Fil}_n/\mathrm{Fil}_0`（$`\mathrm{gr}_1,\dots,\mathrm{gr}_n` の有限の拡大）上では $`\varphi^n` が零になり、$`\mathrm{colim}_\varphi(\mathrm{Fil}_n/\mathrm{Fil}_0)=0`。filtration は網羅的で余極限は可換なので $`\mathrm{colim}_\varphi(\overline\Delta/\mathrm{Fil}_0)=0`、すなわち $`S_{\mathrm{perf}}=\mathrm{colim}_\varphi\mathrm{Fil}_0\xrightarrow{\sim}\mathrm{colim}_\varphi\overline\Delta_{S/A}=S_{\mathrm{perfd}}`。

*例 8.1.3（原典 Ex 8.3：標数 p の環の perfectoid 化） — 原典との差*

原典の $`S` は（導来 p 完備な単体的）$`R` 代数で、$`R` は任意の perfectoid 環。drafts の主張は $`R` 自身が標数 p で $`S` が離散の場合。原典の $`S` が $`p=0` なら $`S` は $`R/p` 代数で、命題 8.2.1 で基底を取り替えれば同じ形になる。

宣言：`perfectoidization_charP`

:::

:::lemma_ "bs_8_4"
*補題 8.4*　coconnective。対応表の状態：なし。

本体の E3 から coconnective 欄は2026-10-26に削除済み。出典の参考記載だけを interface の根拠としない。補題自体の宣言は drafts。

*命題 8.1.4（原典 Lemma 8.4：perfectoid 化の coconnective 性） — 主張*

任意の導来 p 完備な単体的 $`R` 代数 $`S` について、$`\Delta_{S/A,\mathrm{perf}}` と $`S_{\mathrm{perfd}}` はどちらも $`D^{\ge0}` に入る。

*命題 8.1.4（原典 Lemma 8.4：perfectoid 化の coconnective 性） — Lean*

本体にない（E3 の界面にこの欄はない）。drafts に三つに分けて（drafts/A4/Perfectoidization、離散で導来 p 完備な $`S`）：(a) $`\Delta_{S/A,\mathrm{perf}}\in D^{\ge0}` \`prismaticPerfection\_coconnective\`（:282、\`IsCoconnectiveAt A 0\`）、(b) $`H^0(\Delta_{S/A,\mathrm{perf}})` は p ねじれなしで p 進完備、自己同型 $`\varphi_S` を Frobenius 持ち上げとする完全 δ 構造を持ち $`A\to H^0` は δ 射 \`prismaticPerfection\_h0\_perfectDelta\`（:298）、(c) $`d` は $`H^0` の非零因子で $`S_{\mathrm{perfd}}\in D^{\ge0}` \`perfectoidization\_coconnective\`（:316）。(b)(c) をまとめて $`(H^0(\Delta_{S/A,\mathrm{perf}}),(d))` が完全 prism であること \`prismaticPerfectionPrism\`（:327）。

証明で使う部品のうち本体にあるもの：$`P^0` は E∞ の界面 \`EInfinityTheory\`（Interface/Theory:106）の欄 \`powerOp0\`（:221、標数 p の環 $`k` 上の E∞ 代数の台のスペクトルの自己準同型）で、$`\pi_0` 上で p 乗 \`powerOp0\_zero\`（:223）、正の $`\pi_n` 上で零 \`powerOp0\_pos\`（:231）、離散な代数では Frobenius \`powerOp0\_discrete\`（:235）、余単体的な代数の実現では各項の Frobenius が誘導する写像 \`powerOp0\_tot\`（:245）。Lemma 2.34 は \`IsPerfect.distinguished\_mul\_injective\`（DistinguishedRegular:96）。

*命題 8.1.4（原典 Lemma 8.4：perfectoid 化の coconnective 性） — 証明*

$`X:=\Delta_{S/A,\mathrm{perf}}` とおく。

\*\*(a) $`X\in D^{\ge0}`.\*\* E∞-$`\mathbb F_p` 代数の $`P^0` 作用素を使う。単体的余単体的な $`\mathbb F_p` 代数の各項の Frobenius は、実現の上で $`P^0` を誘導する。$`\Delta_{S/A}/p` は多項式代数の Čech–Alexander 複体（余単体的な δ 環）の mod p から左 Kan 拡張で得られ、$`\varphi_S` は各項の Frobenius なので、$`\Delta_{S/A}/p` 上の $`\varphi_S` は $`P^0` である。$`X/p` では塔の余極限により $`\varphi_S` が可逆になるので、$`X/p` は $`P^0` が可逆に作用する E∞-$`\mathbb F_p` 代数。$`P^0` は正次数のホモトピー類をすべて殺す（\[Lur11, Rem 2.2.7\]）ので $`\pi_n(X/p)=H^{-n}(X/p)=0`（$`n>0`）、すなわち $`X/p\in D^{\ge0}`。

（補った）$`X/p` から $`X` へ：$`X\xrightarrow{p}X\to X/p` の長完全列で、$`n\ge1` では $`H^{-n}(X/p)=H^{-n-1}(X/p)=0` から $`p` は $`H^{-n}(X)` 上で全単射。$`X` は導来 p 完備なのでそのコホモロジーも導来 p 完備で、$`p` が可逆な導来 p 完備加群は零。よって $`X\in D^{\ge0}`。

\*\*(b) $`H^0(X)` は完全 δ 環.\*\* 同じ長完全列で $`H^{-1}(X/p)=0` から $`H^0(X)` は p ねじれなしで、$`H^0(X)/p\hookrightarrow H^0(X/p)`。$`P^0` は $`\pi_0` 上で p 乗写像なので、$`H^0(X)` 上の自己同型 $`\varphi_S` は $`H^0(X)/p` 上の Frobenius を持ち上げる。p ねじれなしの環の Frobenius 持ち上げは δ 構造を一つ定め（原典 Rem 2.2）、$`\varphi_S` が全単射なのでその δ 環は完全。p ねじれなしで導来 p 完備なので古典的にも p 進完備。完全で p 完備な δ 環の Frobenius 持ち上げは一意なので、$`A\to H^0(X)` は δ 射。

\*\*(c) $`S_{\mathrm{perfd}}\in D^{\ge0}`.\*\* $`S_{\mathrm{perfd}}=\mathrm{cofib}(d\colon X\to X)` で、(a) から $`H^{-n}(S_{\mathrm{perfd}})=0`（$`n\ge2`）、$`H^{-1}(S_{\mathrm{perfd}})=\ker(d\colon H^0(X)\to H^0(X))`。(b) より $`d` の像は distinguished で、Lemma 2.34 から $`H^0(X)` の非零因子。

*命題 8.1.4（原典 Lemma 8.4：perfectoid 化の coconnective 性） — 原典との差（D44・D43）*

E3 の界面にこの補題の欄は置かない。命題 8.2.1、Cor 8.14、Thm 10.11 の証明の中で使う定理として置く（D44）。原典は $`P^0` の性質を \[Lur11, Rem 2.2.7\] から引用する。Lean では $`P^0` を E∞ の界面の欄（Barratt–Eccles 模型で与える）とし、正の $`\pi_n` で零になることをその欄の主張として持つ（D43）。$`P^0` は原典どおり台のスペクトルの自己準同型で、$`D(k)` の射としては述べない。

宣言：`prismaticPerfection_coconnective`、`perfectoidization_coconnective`、`prismaticPerfection_h0_perfectDelta`

:::

:::proposition "bs_8_5" (lean := "SerrePositivity.BhattScholze.PerfectoidizationInterface.PerfectoidizationInterfaceE3, SerrePositivity.BhattScholze.Inputs.exists_perfectoidizationInterfaceE3")
*命題 8.5*　perfectoid 標的の極限。対応表の状態：未証明の入力に依存。

E3 存在 sorry から通常 R-代数と Type u の perfectoid 標的の指定 limitCone・極限性を受け取る。全 perfect site の RΓ 比較・全宇宙の巨大極限・A 非依存を構成済みとはしない。

*命題 8.2.1（原典 Prop 8.5：完全 prismatic site による記述） — 主張*

$`(S/A)^{\mathrm{perf}}_\Delta` 上の flat 位相と chaotic 位相の間の任意の位相について、写像
$$`\Delta_{S/A,\mathrm{perf}}\to R\Gamma\bigl((S/A)^{\mathrm{perf}}_\Delta,\mathcal O_\Delta\bigr)`
は同値である。とくに perfectoid 化
$$`S_{\mathrm{perfd}}\simeq R\Gamma\bigl((S/A)^{\mathrm{perf}}_\Delta,\overline{\mathcal O}_\Delta\bigr)\simeq\lim_{S\to R'}R'`
は、$`S` から perfectoid 環 $`R'` への全ての写像にわたる $`R'` の導来極限であり、$`A` の取り方によらない。

これから、$`S` が semiperfectoid なら $`S_{\mathrm{perfd}}` は Cor 7.3 の perfectoid 化と一致し、一般に $`\Delta_{S/A,\mathrm{perf}}` と $`S_{\mathrm{perfd}}` は $`\pi_0S` だけにより（$`A` にはよらない）。

*命題 8.2.1（原典 Prop 8.5：完全 prismatic site による記述） — Lean*

E3 の界面の欄 \`limitCone\`・\`limit\_isLimit\`（Derived/Interface:683・685）：各離散 $`S` について、Type u の perfectoid 標的の圏 \`PerfUnder\_u\`（:79）上の図式 $`T\mapsto T` \`targetDiagram\`（:178）の、頂点 $`S_{\mathrm{perfd}}` の錐のデータ \`BSLimitConeData\`（:510）とその極限性。錐のデータは、元の $`S\to T` の錐との単位による整合（\`overSource\`）と、$`H^0` 上の射影が環準同型で単位・標的と両立すること（\`projection\` とその整合）を含む。

主張と系は drafts（drafts/A5/PerfectSiteComparison）：比較写像が同値 \`perfectionComparison\_isIso\`（:61）、位相 $`\bot\le J\le` flat の任意の $`J` で \`perfectionComparison\_isIso\_topology\`（:72）、系 1 $`S_{\mathrm{perfd}}\simeq\lim_{S\to T}T`（濃度 $`\le\kappa` の標的） \`perfectoidization\_isLimit\`（:87）と Type u の標的 \`perfectoidization\_isLimit\_u\`（:97）、系 2 基底によらない \`perfectoidization\_indep\`（:122）、系 3 semiperfectoid なら Cor 7.3 の環と一致 \`perfectoidization\_semiperfectoid\`（:132）、animated 版 \`perfectionComparison\_isIso\_animated\`（:180）、系 4 $`\pi_0` だけによる \`perfectoidization\_piZero\`（:190）。E3 の欄への接続 \`e3LimitCone\`・\`e3LimitCone\_isLimit\`（drafts/A5/InterfaceLimitCone:67・75）。

*証明の部品.* (1) の $`\tilde S` を作る根添加は本体（Derived/RootAdjunction）：一段 \`rootAdjunctionStep\`（:52）は $`S` の全ての元 $`x` に同時に $`x-X^p-pY` の根を添加して完備化したもの、perfectoid 環への環射は一段ごとに延びる \`rootAdjunctionStep\_extends\`（:68）。一段を ℕ で積んだ塔 \`completedRootTower\`（:116）の余極限の完備化が \`rootClosure\`（:121）で、完備性 \`rootClosure\_isModuleComplete\`（:134）、perfectoid 環への射の延長 \`rootClosure\_extends\`（:143）、関手性 \`rootClosureMap\_id\`・\`rootClosureMap\_comp\`（:426・435）。濃度の評価 \`rootClosure\_cardinal\_le\`（ArcCardinality:67）。(2) で使う完備化前の関手版 \`algebraicRootFunctor\`（RootAdjunction:316）は「全ての元の p 冪根を関手的に取る」にあたり、mod p の Frobenius が全射 \`algebraicRootClosure\_frobenius\_surjective\`（:449）。(3) の $`\tilde S`：$`R\langle X_1^{1/p^\infty},\dots,X_r^{1/p^\infty}\rangle` が perfectoid \`polyRootAlgebra\_isIntegralPerfectoid\`（:861）と、評価による完備な底変換 \`rootCover\`（:896）。

drafts の部品：(1) $`\tilde S` は semiperfectoid \`rootClosure\_isSemiperfectoid\`（drafts/A5/WeaklyInitialAndDescent:58）、弱始対象 \`perfectoidTargetWeaklyInitial\`（:96）と \`perfectoidTargetWeaklyInitial\_isWeaklyInitial\`（:113）、site の弱終対象 \`weakPerfectSiteObj\_isWeaklyTerminal\`（:117）、極限 ＝ Čech 余脈体の Tot \`limit\_perfUnder\_eq\_tot\`（:140）、二つの添字での極限の一致 \`limit\_perfUnder\_eq\_limit\_perfectSite\`（:153）。(2) 一様に coconnective な Tot と filtered 余極限の交換 \`tot\_coconnective\_filteredColimit\`（:202）、右辺の filtered 余極限との可換性 \`limit\_perfectSite\_filteredColimit\`（:246）、左辺の可換性 \`prismaticPerfection\_filteredColimit\`（drafts/A4/Perfectoidization:358）、有限生成への帰着 \`perfectionComparison\_isIso\_of\_finiteType\_cases\`（WeaklyInitialAndDescent:255）、根添加と filtered 余極限の可換性 \`algebraicRootClosure\_filteredColimit\`（drafts/A5/RootAdjunction:43）。(3) $`R\langle X\rangle\to R\langle X^{1/p^\infty}\rangle` の p 完備忠実平坦性 \`polyAlgebraToRoot\_pCompletelyFaithfullyFlat\`（drafts/A5/RootAdjunction:52）、各 $`\tilde S^n` は semiperfectoid \`rootCover\_isSemiperfectoid\`（WeaklyInitialAndDescent:289）、左辺の降下 \`prismaticPerfection\_rootCover\_descent\`（:302）、右辺の降下 \`perfUnder\_leftAdjoint\_initial\`（:313）・\`limit\_perfectSite\_rootCover\_descent\`（:331）、有限生成の場合 \`perfectionComparison\_isIso\_of\_finiteType\`（:343）。(4)（drafts/A5/SemiperfectoidCase）：$`\Delta_{S/A,\mathrm{perf}}` は連結 \`prismaticPerfection\_connective\_of\_semiperfectoid\`（:156）で離散 \`prismaticPerfection\_discrete\_of\_semiperfectoid\`（:173）、$`S_{\mathrm{perfd}}\to R'` は分裂全射 \`perfectoidizationToUniversal\_splitSurjective\`（:269）、$`S\to S_{\mathrm{perfd}}` は全射 \`surjective\_unit\_of\_semiperfectoid\`（:428）、まとめて \`perfectoidization\_semiperfectoid\_iso\`（:437）。Thm 7.4・Thm 7.14 は本体で証明済み（第 7 章）。

*命題 8.2.1（原典 Prop 8.5：完全 prismatic site による記述） — 証明*

*(1) 位相によらないこと.* site $`(S/A)^{\mathrm{perf}}_\Delta` に弱終対象があることを示す。$`S` は離散としてよい。$`S\to\tilde S`（$`\tilde S` は semiperfectoid）で、$`S` から perfectoid 環 $`R'` への任意の写像が $`\tilde S` に延びるものを作れば、$`\tilde S_{\mathrm{perfd}}`（Cor 7.3）が求める弱始対象（site の側では弱終対象）になる。元 $`x\in S` を取り $`S_x=S\langle X,Y\rangle/(x-X^p-pY)` とおく。これは mod p で $`x` の p 乗根を添加し、perfectoid 環への写像 $`S\to R'` は $`S_x` に延びる（補った：$`R'/p` は semiperfect なので $`x` の像に $`y^p\equiv x\bmod p` となる $`y` があり、$`x-y^p=pz` として $`X\mapsto y`、$`Y\mapsto z`。$`R'` は p 完備）。これを超限的に繰り返して $`\tilde S` を得る。ここで、$`T/pT` が semiperfect な p 完備 $`R` 代数 $`T` は perfectoid 環 $`R\widehat\otimes_{\mathbb Z_p}W(T^\flat)` の商なので semiperfectoid であること（\[BMS19, Rem 4.22\]）を使う。

すると Čech–Alexander の議論と flat 降下により、$`R\Gamma((S/A)^{\mathrm{perf}}_\Delta,\mathcal O_\Delta)` は余単体的な perfectoid $`S` 代数 $`(\tilde S^\bullet)_{\mathrm{perfd}}` で計算される。ここで $`\tilde S^i=(\tilde S^{\otimes_S(i+1)})^\wedge` は $`\tilde S` の $`S` 上の $`i+1` 個の p 完備テンソル積。これは位相によらない。（補った：$`(\tilde S^{\otimes_S(i+1)})^\wedge_{\mathrm{perfd}}` は $`S` の下の perfectoid 環の圏での $`\tilde S_{\mathrm{perfd}}` の $`i+1` 個の余積で、弱終対象の Čech 脈体は極限について共終。$`\mathcal O_\Delta` は完全 site 上で flat 層なので、それより粗い位相の層でもあり、どの位相でも $`R\Gamma` は前層としての極限に等しい。）

*(2) 有限生成への帰着.* 以下 flat 位相で考える。$`S\mapsto S_{\mathrm{perfd}}` と $`S\mapsto R\Gamma((S/A)^{\mathrm{perf}}_\Delta,\mathcal O_\Delta)` が（$`D(A)` の $`(p,I)` 完備な対象に値を取るものとして）filtered 余極限と可換であることを示せば、$`\pi_0(S)` が $`A/I` 上位相的に有限生成の場合に帰着する。前者は導来 prismatic コホモロジーの同じ性質から明らか。後者は $`S` が離散としてよく（$`(S/A)^{\mathrm{perf}}_\Delta=(\pi_0(S)/A)^{\mathrm{perf}}_\Delta`）、任意の flat な semiperfectoid 被覆 $`S\to\tilde S` の同様の Čech–Alexander 複体でもコホモロジーが計算できる。とくに「$`S` の全ての元の全ての p 冪根を添加する」ことで $`\tilde S` を関手的に取れ、この関手的な Čech–Alexander 複体を使うと filtered 余極限との可換性が確かめられる。（補った：各項 $`(\tilde S^i)_{\mathrm{perfd}}` は perfectoid で離散なので、余単体的対象は一様に coconnective。そのような Tot は各次数で有限段の部分 Tot（有限極限）で決まり、filtered 余極限と交換する。）

*(3) semiperfectoid への帰着.* $`\pi_0` で全射な $`R\langle X_1,\dots,X_r\rangle\to S` を選び、$`\tilde S` を $`R[X_1^{1/p^\infty},\dots,X_r^{1/p^\infty}]\otimes_{R[X_1,\dots,X_r]}S` の p 完備化とする。$`\pi_0\tilde S` は semiperfectoid（補った：$`\tilde S/p` の元は $`X_i` の像の $`R/p` 係数の多項式で、それぞれ p 乗根を持つ）。$`\tilde S^\bullet` を $`\tilde S^{\otimes_S(i+1)}` の導来 p 完備化とする。補題 8.2.2 により $`\Delta_{S/A}`（と完全化）は $`\Delta_{\tilde S^\bullet/A}` の極限で計算される（補った：$`\Delta_{S}\to\Delta_{\tilde S}` は $`\Delta_T\to\Delta_{T_\infty}` の底変換で、descendable な写像は Amitsur 複体の Tot で元に戻る）。右辺も同様の降下（各 perfectoid $`R'` について $`R'` を $`(R'\widehat\otimes_S\tilde S^n)_{\mathrm{perfd}}` の Tot で表し、極限を交換する）で、$`\pi_0S` が semiperfectoid の場合に帰着する。

*(4) semiperfectoid の場合.* $`R'` を $`\pi_0S` の前章の意味の perfectoid 化（$`S` が写像を持つ普遍な perfectoid 環）とする。示すべきは $`\Delta_{S/A,\mathrm{perf}}\otimes^L_AA/I\to R'` が同型であること。左辺は命題 8.1.4 で coconnective。一方 $`S` は semiperfectoid なので $`L_{S/\mathbb Z_p}[-1]`、したがって全ての $`\wedge^iL_{S/\mathbb Z_p}[-i]` は連結で、Hodge–Tate 比較から $`\Delta_{S/A}` も $`\Delta_{S/A,\mathrm{perf}}` も連結。よって $`\Delta_{S/A,\mathrm{perf}}` は離散で完全 δ 環、$`S_{\mathrm{perfd}}=\Delta_{S/A,\mathrm{perf}}\otimes^L_AA/I` は perfectoid 環。写像 $`S\to S_{\mathrm{perfd}}\to R'` の合成は Thm 7.4 で全射。$`R'` の普遍性から第二の写像は分裂全射なので、$`S\to S_{\mathrm{perfd}}` の全射性を示せばよい（補った：すると $`S\to S_{\mathrm{perfd}}` が $`R'` を経由するので $`R'\to S_{\mathrm{perfd}}` も全射で、分裂単射でもあるから同型）。

$`S/p` は semiperfect なので、$`R` を $`R\langle Y_k^{1/p^\infty}\mid k\in K\rangle`（適当な添字集合 $`K`）に取り替えて $`R\to S` は全射としてよい。$`R\to S` の核の生成元 $`\{f_j\}_{j\in J}` を取る。$`S\mapsto S_{\mathrm{perfd}}` は $`R` の p 完備平坦な底変換と可換なので、Thm 7.14 により各 $`f_j` が $`R` の中で両立する p 冪根の系 $`\{f_j^{1/p^n}\}_{n\ge0}` を持つとしてよい。それを固定すると写像
$$`S':=R\langle X_j^{1/p^\infty}\mid j\in J\rangle/(X_j\mid j\in J)^\wedge\to S,\qquad X_j^{1/p^n}\mapsto f_j^{1/p^n}`
が得られ、これは $`\pi_0` で全射、$`\pi_1(L_{-/\mathbb Z_p}/p)` でも全射。Hodge–Tate 比較により $`S'_{\mathrm{perfd}}\to S_{\mathrm{perfd}}` も全射なので、$`S=S'` の場合に $`S\to S_{\mathrm{perfd}}` の全射性を示せばよい。filtered 余極限で $`J` は有限としてよく、そのとき Prop 7.10 と $`R'` の構成から $`S'_{\mathrm{perfd}}=R'`。

*命題 8.2.1（原典 Prop 8.5：完全 prismatic site による記述） — 原典との差（D45・D46・D47・D52・D51）*

定義域：原典の $`S` は導来 p 完備な animated $`R` 代数で、site は $`\pi_0S` で取る。drafts の主な宣言は離散な $`S` の場合で、animated 版を末尾に置く（D45）。「flat と chaotic の間の任意の位相」は Grothendieck 位相の順序 $`\bot\le J\le` flat で述べる（D46）。極限の添字：原典は「全ての perfectoid 環への写像」の（大きい）圏を使う。Lean では濃度 $`\le\kappa` の完全 site と Type u の perfectoid 標的 \`PerfUnder\_u\` の二つで述べ、どちらの極限も同じ弱始対象の Čech 余脈体の Tot に等しいことで一致させる（D47）。(1) の $`\tilde S` は u-small に取れるので、E3 の \`limitCone\` が添字を Type u の標的に限っても同じ極限になる。E3 の欄は極限性に加えて、単位と $`H^0` の射影の乗法的な整合を指定したデータとして持つ。Cor 7.3 との一致は、原典では主張の後の注意だが、Lean では証明の (4) そのものを系として述べる（D52）。

(1) の $`\tilde S` を、原典は「一つの元に根を添加する操作の超限的な繰り返し」で作る。Lean では各段で全ての元に同時に根を添加する ω 段の塔で作る（\`rootClosure\`）。できる対象の役割（弱始対象）は同じ。完備化を挟むので filtered 余極限は保たず、(2) の filtered 余極限との可換性は完備化前の \`algebraicRootFunctor\` で扱う。

:::

:::lemma_ "bs_8_6"
*補題 8.6*　強い降下（descendability）。対応表の状態：なし。

指定 prismatic cohomology とその perfection の rootMap の descendability は drafts。一般の降下基盤だけでは原文の同じ二つの射に未適用。

*命題 8.2.2（原典 Lemma 8.6：完全化への移行の強い降下） — 主張*

$`T=R[X_1,\dots,X_n]^\wedge`、$`T_\infty=R[X_1^{1/p^\infty},\dots,X_n^{1/p^\infty}]^\wedge` とする。自然な写像 $`\Delta_{T/A}\to\Delta_{T_\infty/A}` と $`\Delta_{T/A,\mathrm{perf}}\to\Delta_{T_\infty/A,\mathrm{perf}}` は、$`D_{\mathrm{comp}}(A)` の可換代数の写像として descendable（\[Mat16\]）である。ここで $`D_{\mathrm{comp}}(A)` は導来 $`(p,I)` 完備な対象が張る $`D(A)` の充満部分圏。

*命題 8.2.2（原典 Lemma 8.6：完全化への移行の強い降下） — Lean*

本体にない。drafts（drafts/A5/StrongDescent）：非完全化の版 \`prismaticCohomology\_rootMap\_descendable\`（:67）、完全化の版 \`prismaticPerfection\_rootMap\_descendable'\`（:75）、$`n=1` への帰着 \`rootMap\_descendable\_of\_one\`（:84）、$`F^{\otimes2}` の RHom の評価 \`rootMap\_fiber\_rhom\_coconnective\`（:108）、$`A/(p,\varphi^{-1}(d))` への底変換で確かめてよいこと \`coconnective\_of\_modBaseChange\`（:117）、de Rham 比較による言い換え \`rootMap\_modP\_eq\_deRham\`（:203）、一変数の Cartier 同型と形式性 \`deRhamOneVariable\_formal\`（:234）、(∗) の計算（任意の離散係数） \`squareZero\_rhom\_coconnective\`（:250）、$`n=1` の場合 \`rootMap\_descendable\_one\`（:265）。descendable の定義は $`\Delta_T` を底とする一般形 \`IsDescendableOver\`（drafts/Shared/Descendable:96、$`\mathrm{Mod}_{\Delta_T}` の thick ⊗-ideal）、\[BS17, Lemma 11.22\] にあたる \`hasDescentIndexLEOver\_frobeniusColimit\`（:205）。de Rham 側の入力は \`deRham\_iso\_rootAlgebra\_modP\`（drafts/A1/DeRhamComparisonPoly:494）。$`T`・$`T_\infty` と包含は本体の \`polyAlgebra\`・\`polyRootAlgebra\`・\`polyAlgebraToRoot\`（Derived/RootAdjunction:487・666・677）。

*命題 8.2.2（原典 Lemma 8.6：完全化への移行の強い降下） — 証明*

*完全化の版.* $`\Delta_{T/A}\to\Delta_{T_\infty/A}` の descendability と、次の一般的な圏論の事実から出る：可換代数の写像 $`B\to C` が index $`\le n` で descendable で、$`B`・$`C` が両立する自己準同型 $`\varphi` を持つなら、$`\mathrm{colim}_\varphi B\to\mathrm{colim}_\varphi C` は index $`\le2n` で descendable（\[BS17, Lemma 11.22\]）。完備化は対称モノイダルな局所化なので descendability を保つ。

\*\*$`n=1` への帰着.\*\* $`\Delta_{-/A}` は p 完備な単体的可換 $`R` 代数から $`D_{\mathrm{comp}}(A)` の可換代数への関手として余積と可換なので、$`\Delta_{T/A}\to\Delta_{T_\infty/A}` は一変数の場合の $`n` 個の完備テンソル積。descendable な写像のテンソル積は descendable なので $`n=1` としてよい。

\*\*$`n=1`.\*\* $`F\in D(\Delta_{T/A})` を $`\Delta_{T/A}\to\Delta_{T_\infty/A}` の fibre とする。$`D(\Delta_{T/A})` の中の写像 $`F^{\otimes2}\to\Delta_{T/A}` がすべて零ホモトピックであることを示せばよい（index $`\le2`）。そのためには
$$`\mathrm{RHom}_{\Delta_{T/A}}(F^{\otimes2},\Delta_{T/A})\in D^{\lt0}`
を示せば足りる（$`H^0` が写像のホモトピー類）。完備性により、$`A\to A/(p,\varphi^{-1}(d))` に沿って底変換した後に同じことを確かめればよい（補った：$`(p,\varphi^{-1}(d))` は $`(p,d)` と同じ根基を持ち、導来完備な対象の最高次のコホモロジーは Nakayama で検出される）。とくに $`R` は標数 p の完全環で、$`T=R[X]`、$`T_\infty=R[X^{1/p^\infty}]` はその完全化としてよい。de Rham 比較と Cartier 同型を使うと次に帰着する（補った：$`\Delta_{T/A}\otimes^L_AA/\varphi^{-1}(d)=\varphi_A^*\Delta_{T/A}\otimes^L_AA/d` は de Rham 比較で de Rham 複体 $`\Omega^\bullet_{T/R}` になり、$`T_\infty` では余接複体が p 完備に消えるので $`T_\infty` 自身。一変数の Cartier 同型で $`\Omega^\bullet_{T/R}` は分裂二乗零拡大と cdga として擬同型で、Frobenius の捻りで $`R[X^p]` を $`T` と同一視する）：

(∗) $`\Omega:=T\oplus\Omega^1_{T/R}[-1]` を、$`T` の $`\Omega^1_{T/R}[-1]` による分裂二乗零拡大である $`T`-cdga とみる。$`F` を標準写像 $`\Omega\to T\to T_\infty` の fibre とすると $`\mathrm{RHom}_\Omega(F^{\otimes2},\Omega)\in D^{\lt0}`（テンソル積は $`D(\Omega)` で取る）。

$`\Omega\to T` の fibre は $`\Omega^1_{T/R}[-1]` で、生成元 $`dX\in\Omega^1_{T/R}` を選ぶと dg 加群として $`T[-1]` に同型。また $`T_\infty` は $`T` 加群として自由で、生成元の一つを $`1\in T_\infty` に取れるので、$`T\to T_\infty` の fibre は $`T^{\oplus I}[-1]`（$`I` は集合）。合わせると $`\Omega\to T_\infty` の fibre $`F` は、ある集合 $`J` について $`T^{\oplus J}[-1]` の形の $`\Omega` 加群に同型。$`\mathrm{RHom}(-,-)` は第一変数の余積を積に変えるので、$`\mathrm{RHom}_\Omega((T[-1])^{\otimes2},\Omega)\in D^{\lt0}` を確かめればよい。これは、写像がすべて $`dX` で決まる dg 代数 $`\Omega` 上の dg 加群 $`T[-1]` の分解
$$`\cdots\to\Omega[-3]\to\Omega[-2]\to\Omega[-1]\xrightarrow{\sim}T[-1]`
を使う標準的な計算である。

（補った）計算の中身：$`\varepsilon=dX` は次数 1 で $`\varepsilon^2=0`、$`\Omega` の微分は 0。$`T` の $`\Omega` 上の半自由分解 $`P` は、次数 0 の生成元 $`e_0,e_1,\dots` で $`d(e_0)=0`、$`d(e_n)=\varepsilon e_{n-1}` としたもの（次数は $`\deg e_n+1=1+\deg e_{n-1}` から全て 0）。$`P\otimes_\Omega P` は次数 0 の生成元 $`e_m\otimes e_n` の半自由加群なので、$`\mathrm{Hom}_\Omega(P\otimes_\Omega P,\Omega)` の次数 $`k` の部分は生成元の値を $`\Omega^k` に取るもので、$`\Omega` が次数 0・1 にしかないので次数 0・1 に集中する。$`(T[-1])^{\otimes2}\simeq(P\otimes_\Omega P)[-2]` なので、$`\mathrm{RHom}_\Omega((T[-1])^{\otimes2},\Omega)` は次数 $`-2,-1` に集中し、$`D^{\lt0}` に入る。

*命題 8.2.2（原典 Lemma 8.6：完全化への移行の強い降下） — 原典との差（D49・D50・D69）*

descendable：原典は \[Mat16\] を引用する。Lean では \[Mat16, Def 3.18\] の thick ⊗-ideal で定義し、index の判定（\[BS17, Lemma 11.22\] を含む）は定理として置く（D49）。de Rham 比較：原典は一般の de Rham 比較（Thm 6.4）を使う。Lean では多項式・mod p の特別な場合を定理として置き（D50）、その証明は普遍向き付き prism 上で行って完全 prism へ底変換する（D69）。

宣言：`prismaticCohomology_rootMap_descendable`、`prismaticPerfection_rootMap_descendable'`、`rootMap_modP_eq_deRham`

:::

:::definition "bs_8_7" (lean := "SerrePositivity.BhattScholze.Perfectoidization.Arc.IsArcCoverFamily, SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTopology, SerrePositivity.BhattScholze.Perfectoidization.Arc.arcTopologyPerfd")
*定義 8.7*　p 進形式スキームの arc 位相。対応表の状態：一部（special）。

affine p 完備環・濃度 cutoff に限定した rank-one 付値環による同じ arc-cover 条件と生成位相。一般の形式的スキームの open cover との貼り合わせは未供給。

*定義 8.3.1（原典 Def 8.7） — 主張*

p 進形式スキームの圏 fSch を考える。qcqs な p 進形式スキームの射 $`Y\to X` が *arc 被覆*であるとは、p 進完備な階数 1 の付値環 $`V` と射 $`\mathrm{Spf}V\to X` のそれぞれについて、p 進完備な階数 1 の付値環の忠実平坦な拡大 $`V\subset W` と、持ち上げ $`\mathrm{Spf}W\to Y` があることをいう。arc 被覆と開被覆が生成する位相で fSch を site にし、これを fSch 上の *arc site* と呼ぶ。

$`\mathrm{Perfd}\subset\mathrm{fSch}` を、局所的に perfectoid 環 $`R` により $`\mathrm{Spf}R` と書ける p 進形式スキームの充満部分圏とし、誘導位相を入れる。

*定義 8.3.1（原典 Def 8.7） — Lean*

affine 版が本体にある。site の台は濃度 $`\le\kappa` の導来 p 完備環の圏 \`AffCompl\`（Derived/ArcSite:96）（その opposite が affine の p 進形式スキームにあたる）、その perfectoid 環の充満部分圏 \`AffPerfd\`（:112）。試験環の条件 \`IsRankOneCompleteValuationRing\`（Derived/ArcPerfectoidBase:437）は「整域・付値環・Krull 次元 1・p 進完備」。有限族の arc 被覆 \`IsArcCoverFamily\`（Derived/ArcSite:126）は、試験環 $`V` への任意の $`R\to V` が、忠実平坦な $`V\to W`（$`W` も試験環）とある $`R_i\to W` に持ち上がることで、これが生成する位相 \`arcTopology\`（:138）と、\`AffPerfd\` への誘導位相 \`arcTopologyPerfd\`（:147）を置く。被覆族は底変換・合成・有限積と両立する（\`isArcCoverFamily\_baseChange\`・\`isArcCoverFamily\_comp\`・\`isArcCoverFamily\_prod\_iff\`、:156, :193, :212）。

drafts には、arc 位相を一点 arc 被覆の coverage と有限直積の射影族（空族を含む）の coverage の上限として書く \`arcTopology\_eq\_sup\`（drafts/A6/ArcSite:170）と、層条件を「有限積を保つ」と「一点被覆の Čech 条件」に分ける \`isSheaf\_arc\_iff\_cech\`（:200）がある。

*定義 8.3.1（原典 Def 8.7） — 証明*

定義なので証明はない。affine の場合、$`\mathrm{Spf}` の有限族 $`\{\mathrm{Spf}R_i\to\mathrm{Spf}R\}` が arc 被覆であることは、$`\mathrm{Spf}\prod_iR_i=\bigsqcup_i\mathrm{Spf}R_i\to\mathrm{Spf}R` が arc 被覆であることと同じ（$`\mathrm{Spf}W` は連結なので、$`\prod_iR_i\to W` はある成分を通る）。affine な開被覆は有限族で、それ自身 arc 被覆なので、affine の上では開被覆を別に加える必要がない。

*定義 8.3.1（原典 Def 8.7） — 原典との差（D53・D54）*

D53：原典の site は p 進形式スキーム全体の fSch と $`\mathrm{Perfd}\subset\mathrm{fSch}`。Lean は affine の部分だけを、台の濃度 $`\le\kappa` で切った圏の上に定義し、非 affine の形式スキームは扱わない。D54：原典は一つの射の arc 被覆と開被覆で位相を生成する。Lean は \[BM18, Def 1.2\] の有限族の形で定義する。affine の上では上の証明の囲みのとおり同じ位相になる。

:::

:::lemma_ "bs_8_8" (lean := "SerrePositivity.BhattScholze.Perfectoidization.Arc.exists_perfectoid_arcCover, SerrePositivity.BhattScholze.Perfectoidization.Arc.affPerfdInclusion_isCoverDense")
*補題 8.8*　perfectoid による被覆。対応表の状態：一部（special）。

同じ p 完備 affine S の perfectoid 一点 arc-cover と cutoff 内の cover-density を証明する。非 affine 形式的スキームの大域被覆は扱わない。

*命題 8.3.2（原典 Lemma 8.8） — 主張*

任意の $`X\in\mathrm{fSch}` は、ある $`Y\in\mathrm{Perfd}` による arc 被覆 $`Y\to X` をもつ。すなわち perfectoid は arc 位相の基底をなす。

*命題 8.3.2（原典 Lemma 8.8） — Lean*

affine 版が本体にある：導来 p 完備な $`S` について、濃度 $`\le(\#S+\aleph_0)^{\aleph_0}` の perfectoid 環 $`T` と、一点の arc 被覆 $`S\to S_0\to T` がある \`exists\_perfectoid\_arcCover\`（Derived/ArcSite:435）。ここで $`S_0=` \`baseExtension\`（Derived/ArcPerfectoidBase:461）は $`S\otimes_{\mathbb Z_p}\mathbb Z_p[p^{1/p^\infty}]^\wedge` の導来 p 完備化の $`H^0` で、導来 p 完備（\`baseExtension\_isModuleComplete\`、:466）。帰結として、$`(\kappa+\aleph_0)^{\aleph_0}\le\kappa` のとき包含 $`\mathrm{AffPerfd}\to\mathrm{AffCompl}` は cover-dense（\`affPerfdInclusion\_isCoverDense\`、Derived/ArcSite:506）。部品は次のとおり。

- perfectoid な基底：$`\mathbb Z_p[p^{1/p^\infty}]^\wedge` を $`\mathbb Z_p[X_0,X_1,\dots]/(X_0-p,\ X_{n+1}^p-X_n)` の p 進完備化として作る \`perfectoidBaseRing\`（Derived/ArcPerfectoidBase:64）と、それが perfectoid であること \`perfectoidBaseRing\_isPerfectoid\`（:282）。

- 有限直積：perfectoid 環の有限直積は perfectoid \`isIntegralPerfectoid\_finPi\`（Perfectoid/FiniteProduct:250）。成分ごとに p 進完備性・mod p の Frobenius の全射性を示し、Fontaine 核の単項性は $`W(R^\flat)` が有限直積と可換であることから出す。site の上で有限積の層条件を扱うのに使う。

$`S\to S_0` の p 完全忠実平坦性 \`baseExtensionUnit\_pCompletelyFaithfullyFlat\` は drafts にある（drafts/A6/ArcSite:221）が、本体の証明では使わない。

*命題 8.3.2（原典 Lemma 8.8） — 証明*

$`X=\mathrm{Spf}R` が affine の場合に帰着してよい。p 完全忠実平坦な $`R\to\tilde R` で $`\tilde R` が semiperfectoid のものを選ぶ。p 完全忠実平坦なので $`\mathrm{Spf}\tilde R\to\mathrm{Spf}R` は arc 被覆。次に $`\mathrm{Spf}\tilde R_{\mathrm{perfd}}\to\mathrm{Spf}\tilde R` も arc 被覆である：p 進完備な付値環 $`V` への任意の $`\tilde R\to V` は、$`V` を絶対整閉包の p 進完備化に替えると $`V` は perfectoid にしてよく、すると $`\tilde R\to\tilde R_{\mathrm{perfd}}` の普遍性（semiperfectoid の場合、Prop 7.2・Cor 7.3）で $`\tilde R_{\mathrm{perfd}}\to V` に延びる。合成 $`\mathrm{Spf}\tilde R_{\mathrm{perfd}}\to\mathrm{Spf}R` が求める arc 被覆。

Lean の証明は同じ筋で、$`\tilde R` を二段で作る。まず $`S\to S_0` で perfectoid な基底 $`\mathbb Z_p[p^{1/p^\infty}]^\wedge` の上へ移り、その上で §2 の根添加 \`rootClosure\`（全ての元に同時に p 冪根を添加する ω 段の塔）と p 進完備化を施すと、mod p の Frobenius が全射になり、基底の Fontaine 核の distinguished 元による完全 prism の商からの全射ができるので semiperfectoid になる。その普遍 perfectoid 化が $`T`。基底を経ずに根を添加しただけでは semiperfectoid になるとは限らない（$`\mathbb Z_p` への retraction をもつ例がある）。持ち上げは、試験付値環 $`V` を perfectoid な $`W` に替え、$`S\to V\to W` を $`S_0` に延ばし、根添加の普遍性・完備化の普遍性・$`T` の普遍性で $`T\to W` に延ばす。忠実平坦性は $`V\to W` の側で使うので、$`S\to S_0` の忠実平坦性は要らない。

*命題 8.3.2（原典 Lemma 8.8） — 原典との差（D53）*

affine 版だけを、濃度の上界つきで述べる。原典の $`\tilde R` の選び方（任意の p 完全忠実平坦な semiperfectoid 被覆）を、perfectoid な基底への底変換と根添加という具体的な構成に固定する。

:::

:::proposition "bs_8_9"
*注意 8.9*　より簡単な基底。対応表の状態：なし。

全 rank-one 付値環の絶対整閉化の積による指定 arc-cover と非層性の説明を未同定。

*注意 8.3.3（原典 Rem 8.9） — 主張*

Lemma 8.8 よりさらに簡単な基底がある：任意の p 完備環 $`R` は、分数体が代数閉な p 完備で階数 1 の付値環の積 $`S` への p 完備な arc 被覆 $`R\to S` をもつ（したがって $`S` は perfectoid）。実際、$`R` の階数 1 の付値の代表の集合 $`X_R` を選び、$`S=\widehat{\prod_{x\in X_R}V_x^+}` とすればよい。ここで $`V_x\subset\kappa(\ker x)` は $`x` に付随する付値環、$`V_x\to V_x^+` はその絶対整閉包で、完備化は p 進。この被覆は §9 で使う。

*注意 8.3.3（原典 Rem 8.9） — Lean*

本体にない。近い形の補題として、任意の環 $`A` の v 被覆（試験付値環の階数を限らない）が本体にある：素点ごとに代数閉な分数体の付値環を代表に取り、絶対整閉な試験付値環への射は小さい代表を通り（\`exists\_valuationProbe\_factor\`、Derived/ArcValuationProduct:84）、代表の積への一射は affine の v 被覆（\`valuationProbeProduct\_vCover\`、:119）。これは命題 8.3.4 の証明（標数 p の段）の部品で、p 進完備化も階数 1 の制限もないので Rem 8.9 そのものではない。

*注意 8.3.3（原典 Rem 8.9） — 証明*

（補った）$`R\to V` を p 進完備な階数 1 の付値環への射とする。$`\mathfrak p=\ker(R\to V)` とすると、$`R\to V` は $`\kappa(\mathfrak p)` 上の階数 1 の付値 $`x` を定め、代表の選び方から同値な付値 $`x\in X_R` が取れる。$`V` の分数体の代数閉包の付値部分環 $`W'` は $`V` 上忠実平坦で（付値環の拡大は平坦、局所射なので忠実平坦）、$`\kappa(\mathfrak p)\subset\mathrm{Frac}(V)` の代数閉包どうしの埋め込みで $`V_x^+\to W'` を作れる。$`W` を $`W'` の p 進完備化とすると、$`S\to V_x^+\to W` が求める持ち上げになる（$`\widehat{\prod}` から一つの成分への射影は p 完備な相手への射）。各 $`V_x^+` は分数体が代数閉な付値環なので p 進完備化は perfectoid で、その積の p 進完備化も perfectoid。

:::

:::proposition "bs_8_10"
*命題 8.10*　arc 層性。対応表の状態：なし。

Milnor Čech 完全性・tilt・perfect Čech 項の部品は本体。原文の Perfd 上 O の arc 層条件・高次消滅・全 representable の層条件をまとめる定理は drafts。

*命題 8.3.4（原典 Prop 8.10） — 主張*

fSch 上の構造層は arc 層ではない（p 完備環の冪零元は付値環への写像で検出されない）。しかし基底 $`\mathrm{Perfd}` の上ではこの問題は消える：

1. $`\mathrm{Perfd}` 上の前層 $`\mathcal O` は層であり、$`X=\mathrm{Spf}R`（$`R` は perfectoid）が affine なら $`i\gt0` で $`H^i_{\mathrm{arc}}(X,\mathcal O)=0`。

2. 任意の p 進形式スキーム $`T` について、関手 $`X\mapsto\mathrm{Hom}(X,T)` は $`\mathrm{Perfd}` 上の arc 層。

*命題 8.3.4（原典 Prop 8.10） — Lean*

部品は本体にあり、組み立ては drafts にある。

*tilt と付値環.* tilt は零環を含めて定義し（\`tiltRing\`、Derived/ArcValuationTilt:34）、階数 1 の perfectoid 付値環の tilt と、完全な階数 1 の付値環の untilt は再び階数 1 の付値環（\`tilt\_rankOneValuationRing\`、:207、\`untilt\_rankOneValuationRing\`、Derived/ArcValuationUntilt:301）。\[BS17, Lemma 6.3\] の付値環の四角形は、任意の付値環 $`V` と素イデアル $`\mathfrak q` についての短完全列 $`0\to V\to V_{\mathfrak q}\times V/\mathfrak q\to\kappa(\mathfrak q)\to0` として示す（\`valuationRing\_milnorSquare\`、Derived/ArcValuationMilnor:43）。

*標数 p の Čech 完全性の部品*（\[BM18, Prop 4.8\] の議論を構造層の場合に 1 圏でたどる。次の B1〜B5）。

- *B1（増大 Čech 複体）.* 環の増大 Čech 余脈体の完全性 \`AugmentedRingCechExact\`（HomologicalAlgebra/Cech/Basic:92）と射の述語 \`IsCechExact\`（:99）。平坦な底変換で保たれ、忠実平坦な底変換で反映される（\`isCechExact\_baseChange\`・\`isCechExact\_baseChange\_iff\`、Cech/BaseChange:223, :233）。環として左逆があれば完全（\`isCechExact\_of\_retraction\`、Cech/Split:38）。filtered 余極限で保たれる（\`isCechExact\_colimit\`、Cech/Filtered:99）。二つの射の比較と合成からの消去（\`isCechExact\_iff\_of\_tensorCech\`・\`isCechExact\_of\_comp\`、Cech/Composition:137, :160、\[BM18, Lemma 3.4\]）は、第一象限の増大二重複体の零番の行と列の比較（\`exact\_zero\_row\_iff\_zero\_col\_of\_commute\`、Cech/Diagonal:310）による。

- *B2（Milnor 列による検出）.* 完全標数 p の付値環 $`V` と完全 $`V` 代数 $`D` について、上の短完全列は $`D` とのテンソルの後も短完全（\`milnorModuleComplex\_tensor\_shortExact\`、Derived/ArcMilnorTensor:116。完全環の Tor 消滅による）。完全環の射の Čech 余脈体の各項は完全環（\`cechConerve\_perfectRing\`、Derived/ArcPerfectCech:24）。これで完全性を局所化・商・剰余体の三つで（\`cechExact\_of\_milnorTensor\`、Derived/ArcCechMilnor:66）、また重なる二つの区間とその交わりで（\`cechExact\_of\_overlapTensor\`、Derived/ArcCechOverlap:25）検出する（\[BM18, Lemma 4.4、Prop 4.8 の証明の (5)〜(7)\]）。

- *B4（超積）.* 環の超積 \`RingUltraproduct\`（CommutativeAlgebra/Ultraproduct/Basic:37）は付値環・絶対整閉性を保ち（\`valuationRing\_ultraproduct\`・\`aic\_ultraproduct\`、:58, :95、\[BM18, Lemma 3.27\]）、積 $`\prod_tW_t` 上の完全性は各超積への底変換で検出される（\`cechExact\_of\_ultraproducts\`、Derived/ArcCechUltraproduct:61、\[BM18, Lemma 3.25\]）。

*組み立て（drafts）.* B1〜B5 と \[BS17, Thm 4.1 (i)\]（完全環の有限族の v 被覆の Čech 完全性）から標数 p の結論を出す段（B6）は、\[BS17, Thm 4.1 (i)\] を仮定 \`BS17VCechInput\` として受け取る形で drafts にある（drafts/A6/ArcRouteB:58）。目標の型は \`ArcRouteBGoal\`（:67）、最後の比較は \`cechExact\_of\_valuationProbeTests\`（:190）。\[BS17, Thm 4.1 (i)\] そのものは本体にない。tilt への帰着は drafts の \`tilt\_arcCoverFamily\`（drafts/A6/ArcSheafProperty:329。$`d` の像が単元／階数 1 で非零／階数 1 で零／階数 0 の四つに分ける）、Witt ベクトルへの移行 \`witt\_exact\_of\_perfect\`（:293）、d 進完備化で $`R^\flat[1/d]` の項が消えること \`cech\_completion\_kills\_inverted\`（:358）、perfectoid 環の arc 被覆の Čech 完全性 \`cech\_exact\_of\_arcCover\_perfectoid\`（:378）。(1) の層の主張は \`structurePresheaf\_isArcSheaf\`（:439）、(2) は affine な $`T` に限って \`homPresheaf\_isArcSheaf\`（:450）。非 affine な $`T` の (2) は Lean にない。

*命題 8.3.4（原典 Prop 8.10） — 証明*

*(1)* Zariski 降下で affine の場合に帰着する。示すべきは、perfectoid 環の射 $`R\to S` で $`\mathrm{Spf}S\to\mathrm{Spf}R` が arc 被覆のものについて、p 進完備な Čech 複体
$$`0\to R\to S\to S\widehat\otimes_RS\to\cdots`
が完全なこと（これで層であることと高次コホモロジーの消滅が同時に出る）。

*tilt への帰着.* $`d` を $`\ker(A_{\mathrm{inf}}(R)\to R)` の生成元とする。d 進完備な
$$`0\to R^\flat\to S^\flat\to S^\flat\widehat\otimes_{R^\flat}S^\flat\to\cdots`
が完全なら元の複体も完全である。実際、これに Witt ベクトルを当てても完全で（補った：完全環の d 進完備な複体に $`W` を当てると、Verschiebung のフィルトレーションの各段は Frobenius でねじった同じ複体で、極限を取っても完全。$`W` は完全環の完備テンソルと可換）、$`d` は各項 $`W(\cdot)` で非零因子なので（完全 prism、Lemma 2.34）、短完全列 $`0\to W\xrightarrow{d}W\to W/d\to0` の長完全列から mod $`d` の複体、すなわち元の複体も完全。

*arc 被覆の tilt.* $`\mathrm{Spec}(S^\flat)\sqcup\mathrm{Spec}(R^\flat[1/d])\to\mathrm{Spec}(R^\flat)` は \[BM18, Def 1.2\] の意味の arc 被覆である。階数 1 以下の付値環への $`R^\flat\to V` を取る。$`V` は完全としてよい。$`d` の像が $`V` で可逆なら $`R^\flat[1/d]\to V` に持ち上がる。そうでなければ $`V` をその d 進完備化に替えてよく、このとき $`R^\flat\to V` は tilt の対応で p 進完備な付値環 $`V^\sharp` への $`R\to V^\sharp` と同じものである。仮定から $`S\to W` へ持ち上がる（$`W` は $`V^\sharp` の p 進完備な拡大で、perfectoid にしてよい）ので、$`S^\flat\to W^\flat` が求める持ち上げ。

*完全スキームの arc 降下.* v 降下 \[BS17, Thm 4.1\] と、arc 降下を v 降下と付値環についての条件で特徴付ける \[BM18, Thm 1.6\]（その条件は今の場合 \[BS17, Lemma 6.3\] で与えられる）により、完全スキームの任意の arc 被覆 $`\mathrm{Spec}B\to\mathrm{Spec}A` について $`0\to A\to B\to B\otimes_AB\to\cdots` は完全。これを $`A=R^\flat`、$`B=S^\flat\times R^\flat[1/d]` に当て、（導来）d 進完備化に移ると、$`R^\flat[1/d]` を含む項は $`d` が可逆なので消え、求める d 進完備な複体の完全性を得る。

*Lean の経路（B1〜B6）.* 完全環の arc 被覆 $`A\to B` について、(i) 代表付値環の積 $`A\to\prod_tW_t` は v 被覆（B5）で、合成と比較の補題（B1、\[BM18, Lemma 3.4\]）により、問題は $`\prod_tW_t` への底変換の完全性に移る。その v 被覆の側の完全性に \[BS17, Thm 4.1 (i)\] を使う。(ii) 積の上の完全性は超積ごとに確かめればよく（B4）、超積は再び絶対整閉な付値環なので、一つの絶対整閉な付値環 $`V` の上の arc 被覆の完全性に帰着する。(iii) $`V` の上では、素イデアルの区間 $`V_{[\mathfrak p,\mathfrak q]}` で完全性が成り立つ区間の全体に Zorn を当て（B3）、区間を伸ばす段で Milnor 列（局所化・商・剰余体、および重なる二区間）で検出する（B2）。剰余体では arc 被覆の定義から切断があり（有限表示に降ろして有限段で切断を作る、B3）、左逆のある射は完全（B1）。

*(2)* $`T=\mathrm{Spf}S` が affine なら、(1) から $`R=\mathrm{eq}(S'\rightrightarrows S'\widehat\otimes_RS')`（$`R\to S'` は arc 被覆）が出るので、$`\mathrm{Hom}(S,-)` を当てて直ちに層である。一般には、arc 被覆 $`Y\to X` と、$`Y\times_XY` 上で二つの合成が一致する $`Y\to T` が与えられたとき、$`|Y|\to|T|` が連続写像 $`|X|\to|T|` を通ることを示せば、$`T` の上で局所化して affine に帰着する。位相空間は特殊ファイバーだけで決まるので $`T` は標数 p、$`X,Y` は完全スキームとしてよい。Zariski 降下で $`X,Y` は affine、$`T` は準コンパクトとしてよく、Gabber の議論（\[Bha16, Remark 4.6\]、\[Sta, Tag 03K0\]）で準分離としてよい。すると \[TT90, Appendix C\] により $`T` は affine な推移写像による有限型 $`\mathbb F_p` スキームの逆極限なので $`T` は有限型としてよく、そのとき $`X,Y` も有限型 $`\mathbb F_p` スキームの完全化としてよい。この場合 arc 被覆は h 被覆に限られ、$`|Y|\to|X|` は商写像なので、求める連続写像 $`|X|\to|T|` を得る。

*命題 8.3.4（原典 Prop 8.10） — 原典との差（D56・D59）*

原典は \[BS17, Thm 4.1\]・\[BM18, Thm 1.6\]・\[BS17, Lemma 6.3\] を引用する。Lean では \[BM18\] の一般の判定（任意の finitary 関手の arc 層性）を使わず、構造層 $`\mathcal O` の場合だけを \[BM18, Prop 4.8\] の議論で 1 圏の Čech 完全性として直接示す（Rydh の結果と hypercomplete 性は使わない）。\[BS17, Thm 4.1 (i)\] は原典どおりに証明する対象とし、\[BS17, Lemma 6.3\] は任意の付値環についての初等補題 \`valuationRing\_milnorSquare\` にする。site と被覆は affine・有限族の形で述べる（D53・D54）。

宣言：`SerrePositivity.BhattScholze.Perfectoidization.Arc.cechExact_of_milnorTensor`、`SerrePositivity.BhattScholze.Perfectoidization.Arc.tilt_rankOneValuationRing`、`SerrePositivity.Cech.cechConerve_perfectRing`、`structurePresheaf_isArcSheaf`、`homPresheaf_isArcSheaf`

:::

:::corollary "bs_8_11"
*系 8.11*　arc 降下の系。対応表の状態：なし。

E3 に対応する arc-RΓ 欄はない。同じ S\_perfd=RΓ\_arc と arc descent の宣言は drafts であり、8.5の制限付き極限と同一視しない。

*系 8.3.5（原典 Cor 8.11） — 主張*

任意の p 完備環 $`S` について
$$`S_{\mathrm{perfd}}=R\Gamma_{\mathrm{arc}}(\mathrm{Spf}S,\mathcal O).`
特に $`S\mapsto S_{\mathrm{perfd}}` は arc 位相について降下を満たす。

*系 8.3.5（原典 Cor 8.11） — Lean*

本体にない。drafts に affine 版 \`perfectoidization\_eq\_arcCohomology\`（drafts/A6/ArcSheafProperty:480）がある：$`S_{\mathrm{perfd}}` は $`\mathrm{AffPerfd}` の $`S` の下の部分圏（\`ArcPerfdUnder\`、:457）上の arc 位相（\`arcPerfdSliceTopology\`、:460）での $`\mathcal O` の $`R\Gamma` に一致する。\`PerfectoidizationInterfaceE3\` で使う $`S_{\mathrm{perfd}}` の表示は、この系ではなく Prop 8.5 の極限の形（欄 \`limitCone\`、Derived/Interface:683）。

*系 8.3.5（原典 Cor 8.11） — 証明*

$`\mathrm{affPerfd}\subset\mathrm{Perfd}` を $`R` perfectoid の $`\mathrm{Spf}R` のなす部分圏とする。Lemma 8.8 の証明により $`\mathrm{affPerfd}\subset\mathrm{fSch}` は基底なので
$$`R\Gamma_{\mathrm{arc}}(\mathrm{Spf}S,\mathcal O)=R\Gamma_{\mathrm{arc}}(\mathrm{affPerfd}_{/\mathrm{Spf}S},\mathcal O).`
一方、arc 位相の $`\mathrm{affPerfd}` から chaotic 位相（自明な位相）の $`\mathrm{affPerfd}` への射影は、Prop 8.10 により $`\mathcal O` について高次順像が消える。chaotic 位相の $`R\Gamma` は逆極限なので
$$`R\Gamma_{\mathrm{arc}}(\mathrm{Spf}S,\mathcal O)=\lim_{S\to R'}R'=S_{\mathrm{perfd}}`
で、最後の等号は Prop 8.5（$`R'` は $`S` の下の perfectoid 環を走る）。

*系 8.3.5（原典 Cor 8.11） — 原典との差（D55）*

原典は fSch 上の層コホモロジー $`R\Gamma_{\mathrm{arc}}(\mathrm{Spf}S,\mathcal O)` で述べる。Lean（drafts）は affine 版「$`S_{\mathrm{perfd}}\simeq R\Gamma_{\mathrm{arc}}(\mathrm{affPerfd}_\kappa/S,\mathcal O)`」だけを述べ、fSch や $`\mathrm{AffCompl}` 上の $`R\Gamma` との比較はしない。Lemma 8.8 の affine 版は cover-dense の形で証明の中で使う。

宣言：`perfectoidization_eq_arcCohomology`

:::

:::corollary "bs_8_12" (lean := "SerrePositivity.BhattScholze.PerfectoidizationInterface.PerfectoidizationInterfaceE3, SerrePositivity.BhattScholze.Inputs.exists_perfectoidizationInterfaceE3, SerrePositivity.BhattScholze.Inputs.perfectoidization_excision_isPullback")
*系 8.12*　excision。対応表の状態：未証明の入力に依存。

E3 存在 sorry の excision から、離散 S,S′ の底の D(R) の指定四辺の pullback と、環の普遍 perfectoid 化の pullback を導く。animated 入力・E∞積構造の全主張は含まない。

*系 8.3.6（原典 Cor 8.12） — 主張*

$`S\to S'` を導来 p 完備環の射とし、ある導来 p 完備なイデアル $`I\subset S` について、$`S\to S'` が $`I` の外で arc 層の同型を誘導すると仮定する。すなわち、p 完備な階数 1 の付値環 $`V` への射 $`S\to V` で $`I` を殺さないものは、ただ一つの $`S'\to V` に延びる（原典の脚注 14：たとえば $`S\to S'` が整で $`\mathrm{Spec}(S')\to\mathrm{Spec}(S)` が $`V(I)` の外で同型なら成り立つ）。このとき
$$`\begin{array}{ccc}S_{\mathrm{perfd}}&\longrightarrow&S'_{\mathrm{perfd}}\\ \downarrow&&\downarrow\\ (S/I)_{\mathrm{perfd}}&\longrightarrow&(S'/I)_{\mathrm{perfd}}\end{array}`
は $`E_\infty`-$`S` 代数の引き戻しの四角形（特に $`S` 加群の導来圏の引き戻し）。

$`S` と $`S'` が perfectoid の場合でも内容があり、特に $`S\to S'` の核と余核は $`\ker(S\to(S/I)_{\mathrm{perfd}})` で消える。

*系 8.3.6（原典 Cor 8.12） — Lean*

*界面の欄.* 主張は \`PerfectoidizationInterfaceE3\` の欄 \`excision\`（Derived/Interface:692）で、離散な $`R` 代数 $`S,T` と $`I` について、$`S,T,I` の導来 p 完備性と条件 \`ArcOutside\`（:645。上の付値環への一意延長条件）の下で、$`D(R)` の指定四角形 \`perfdSquare\` が引き戻し。証明ではなく欄（受け取る入力）である。

*界面から導く環の帰結（本体）.* 四つの環の普遍 perfectoid 化が指定されているとき、それぞれの導来対象が離散で指定環と同値になり、$`D(R)` の四角形の長完全列で $`H^{-1}`・$`H^1` の両端が消えて、環の引き戻しと差写像の全射性が出る（\`perfectoidization\_excision\`・\`perfectoidization\_excision\_isPullback\`・\`perfectoidization\_excision\_difference\_surjective\`、Derived/Excision:481, :499, :510）。閉側に標準の perfectoid 化を使う形 \`klCanonicalExcisionSquare\_of\_excision\`（Perfectoidization/Excision:194）。脚注 14 は主イデアル $`I=(a)` について本体にあり、整性と $`a` での局所化の全単射から付値環への一意延長を出す（\`klCanonicalExcisionSquare\_of\_integral\_away\`、:247。\`ArcOutside\` の形は \`arcOutside\_of\_integral\_of\_localization\_iso\`、Derived/IntegralClosureCompletion:47。付値環の側の補題は \`existsUnique\_valuation\_extension\_of\_integral\_away\_bijective\`、CommutativeAlgebra/Localization/Away:213）。

*原典の証明（drafts）.* $`S'\times S/I` への置き換え：$`S\to S'\times S/I` が arc 被覆 \`isArcCover\_of\_arcOutside\`（drafts/A6/SheafOfSetsExcision:75）、perfectoid 化が有限積を保つ \`perfectoidization\_prod\`（:154）、元の四角形へ戻す \`excision\_of\_excision\_prod\`（:201）。誘導位相の層から $`\mathrm{AffCompl}` 上の層への延長 \`extendArcSheaf\`（:230）、対角の被覆 \`isArcCover\_diagonal\_of\_arcOutside\`（:96）、集合の層の等式 \`sheafOfSets\_excision\`（:267）。空間値の層の押し出しと切断の比較は \`sections\_excision\_square\`（drafts/A6/Excision:264）で、まとめた形が \`perfectoidization\_excision\`（:281）と欄の形 \`e3Excision\`（:296）。集合値前層の切断と押し出しの一般論は \`sectionsOf\`（drafts/Sheaves/SetSections:61）・\`IsLocalEquivSet\`・\`presheafPushout\`（drafts/Sheaves/SpaceValued:123・139）。

*系 8.3.6（原典 Cor 8.12） — 証明*

*置き換え.* $`S'` を $`S'\times S/I` に替えてよい：$`V` への $`S\to V` は、$`I` を殺さなければ仮定で $`S'` へ、殺せば $`S/I` へ延びるので $`\mathrm{Spf}(S'\times S/I)\to\mathrm{Spf}S` は arc 被覆。仮定の一意延長も保たれ（$`I` を殺さない $`V` への射は $`S/I` 成分を通らない）、（補った）$`S\mapsto S_{\mathrm{perfd}}` は有限積を保ち $`(S'\times S/I)/I=S'/I\times S/I` なので、置き換えた四角形は元の四角形と $`S/I` の自明な四角形の積で、引き戻しであることは同値。

*層への言い換え.* 導来 p 完備環 $`T` について $`F_T` を $`\mathrm{Perfd}` 上の層 $`X\mapsto\mathrm{Hom}(X,\mathrm{Spf}T)`（Prop 8.10 (2)）とする。Cor 8.11 により $`T_{\mathrm{perfd}}=R\Gamma(F_T,\mathcal O)` で、$`R\Gamma(-,\mathcal O)` は層の余極限を極限に移すので、空間の層として
$$`F_S=F_{S'}\sqcup_{F_{S'/I}}F_{S/I}`
を示せばよい（\[BS17, Thm 2.9\]、\[Voe96, Lemma 3.6\] にならう）。$`F_{S'/I}\hookrightarrow F_{S'}` は単射なので、この押し出しは離散のままで、集合の層の圏で計算できる。米田により、$`\mathrm{fSch}` に降下で延ばした任意の集合の層 $`F` について
$$`F(S)=F(S')\times_{F(S'/I)}F(S/I)`
を示せばよい。

*降下.* $`\mathrm{Spf}S'\to\mathrm{Spf}S` に沿う降下で $`F(S)=\mathrm{eq}\bigl(F(S')\rightrightarrows F(S'\widehat\otimes_SS')\bigr)`。$`I` についての仮定から
$$`\mathrm{Spf}S'\sqcup\mathrm{Spf}(S'/I)\times_{\mathrm{Spf}(S/I)}\mathrm{Spf}(S'/I)\to\mathrm{Spf}S'\times_{\mathrm{Spf}S}\mathrm{Spf}S'`
（第 1 成分は対角）は arc 被覆である：$`S'\widehat\otimes_SS'\to V` は、$`I` を殺さなければ二つの $`S'\to V` が $`S\to V` の延長として一致するので対角を通り、殺せば $`S'/I\widehat\otimes_{S/I}S'/I` を通る。（補った）よって $`x\in F(S')` の二つの引き戻しが $`F(S'\widehat\otimes_SS')` で一致することは、対角への引き戻し（常に一致）と $`F(S'/I\widehat\otimes_{S/I}S'/I)` への引き戻しが一致すること、すなわち $`x` の $`F(S'/I)` での像が二つの引き戻しを一致させることと同値。置き換えにより $`S/I\to S'/I` は左逆をもつ（$`S/I` 成分への射影）ので arc 被覆で、降下により $`F(S/I)=\mathrm{eq}\bigl(F(S'/I)\rightrightarrows F(S'/I\widehat\otimes_{S/I}S'/I)\bigr)`、特に $`F(S/I)\hookrightarrow F(S'/I)`。二つを合わせると $`F(S)=F(S')\times_{F(S'/I)}F(S/I)`。

*脚注 14.*（補った）$`S\to S'` が整で $`V(I)` の外で同型、$`S\to V` が $`I` を殺さないとする。$`a\in I` で像が非零のものを取ると $`V\to\mathrm{Frac}(V)` は $`S_a\cong S'_a` からの射を与え、$`S'` の像は $`V` 上整なので、付値環の整閉性から $`V` に入る。一意性は $`S'\to S'_a` の像の上で決まることから出る。

*後半.* $`S,S'` が perfectoid なら $`S_{\mathrm{perfd}}=S`、$`S'_{\mathrm{perfd}}=S'` で、（補った）$`Q=(S/I)_{\mathrm{perfd}}`、$`E=(S'/I)_{\mathrm{perfd}}` とおくと、引き戻しから完全列 $`0\to S\to S'\oplus Q\to E\to0` を得る（$`S` は離散なので $`H^1` は消える）。よって $`\ker(S\to S')` は $`\ker(Q\to E)` に $`S` 線形に同型で、$`\mathrm{coker}(S\to S')` は $`\mathrm{coker}(Q\to E)` に同型。どちらも $`Q` 加群なので $`J=\ker(S\to Q)` で消える。

*系 8.3.6（原典 Cor 8.12） — 原典との差（D57・D58）*

原典の結論は $`E_\infty`-$`S` 代数の引き戻し。\`PerfectoidizationInterfaceE3\` の欄は離散な $`R` 代数の四角形を $`D(R)` の引き戻しとして受け取り（原典の括弧の「特に」の形）、本体の環の帰結はさらに四つの perfectoid 化が環として指定された場合に限る。D57：原典の $`\mathrm{Perfd}` 上の空間の層の議論は、空間値の層と $`E` 値の層の局所性の一般論を立てて行い、集合の層の等式は 1 圏（Mathlib の層）で示す。D58：原典が「$`S'` を $`S'\times S/I` に替える」で済ませる戻りの一歩を、perfectoid 化が有限積を保つこと（Prop 8.5 から）で補う。

:::

:::proposition "bs_8_13" (lean := "SerrePositivity.BhattScholze.prop813CompletedTensorMap_isPerfectoidization, SerrePositivity.BhattScholze.exists_prop813BaseChange_of_perfectoid_quotient, SerrePositivity.BhattScholze.prop813_perfectoidTensor_pure, SerrePositivity.BhattScholze.prop813ComparisonEquiv, SerrePositivity.BhattScholze.prop813ComparisonEquiv_comp")
*命題 8.13*　完備テンソルとの可換性。対応表の状態：一部（stronger-hyp）。

指定された環の普遍 perfectoid 化を入力すると、元の completed derived tensor の H⁰ の単位を保つ普遍性・比較環同型を証明する。perfectoid 側の元の derived tensor が離散という定理もあるが、任意 animated 入力の E∞ 対称モノイダル関手を構成したとはしない。

*命題 8.4.1（原典 Prop 8.13） — 主張*

perfectoid 環からの写像をもつ導来 p 完備な単体的環から、導来 p 完備な $`E_\infty` 環への関手 $`S\mapsto S_{\mathrm{perfd}}` は対称モノイダルである。すなわち任意の図式 $`S_1\leftarrow S_3\to S_2` について、誘導される写像
$$`S_{1,\mathrm{perfd}}\widehat\otimes^L_{S_{3,\mathrm{perfd}}}S_{2,\mathrm{perfd}}\to(S_1\widehat\otimes^L_{S_3}S_2)_{\mathrm{perfd}}`
は同値。

*命題 8.4.1（原典 Prop 8.13） — Lean*

本体にあるのは環版：図式 $`S_1\leftarrow S_3\to S_2` の各環に環としての普遍 perfectoid 化が指定されているとき、指定した perfectoid 化の完備テンソルの $`H^0` は、元の完備テンソルの $`H^0` の普遍 perfectoid 化である（\`prop813CompletedTensorMap\_isPerfectoidization\`、Perfectoidization/TensorCompatibility:248）。perfectoid な底変換の版 \`prop813BaseChange\_exists\_algEquiv\`（:431）と、perfectoid 環の全射商についての存在形 \`exists\_prop813BaseChange\_of\_perfectoid\_quotient\`（:506）。導来版は drafts の \`perfectoidization\_relativeTensor\`（drafts/A7/AnimatedPerfectoidization:273）。

*命題 8.4.1（原典 Prop 8.13） — 証明*

$`S_3` へ写る perfectoid 環 $`A`（完全 prism $`(A,I)` に対応）を選ぶ。導来 prismatic コホモロジー $`\Delta_{-/A}` は Hodge–Tate 比較により対称モノイダル（Construction 7.6 の性質 (5) にさらに一般の形がある）：（補った）$`\overline\Delta_{-/A}` の共役フィルトレーションの次数付きは $`\wedge^iL_{-/(A/I)}[-i]` で、余接複体は $`L_{S_1\otimes^L_{S_3}S_2}\simeq L_{S_1}\otimes S_2\oplus S_1\otimes L_{S_2}`（$`S_3` 上の相対形）を満たすので次数付きの段で同値になり、フィルトレーションの完備性と導来 Nakayama で $`\Delta` の同値が出る。この同値は完全化 $`\mathrm{colim}_\varphi` と $`(p,I)` 完備化に移り（どちらも完備テンソルと可換）、最後に mod $`I`（$`S_{\mathrm{perfd}}=\Delta_{S/A,\mathrm{perf}}\otimes^L_AA/I`）に移る。

Lean の環版は Hodge–Tate 比較を使わない：環の普遍性で $`S_1\otimes_{S_3}S_2\to C_1\otimes_{C_3}C_2`（$`C_i` は指定した perfectoid 化）を作り、perfectoid 環の完備テンソルの $`H^0` が perfectoid 化であること（Lemma 10.3 の一般形）と、$`H^0` の主元完備化の比較を合わせて、完備テンソルの $`H^0` の段で普遍性を確かめる。

*命題 8.4.1（原典 Prop 8.13） — 原典との差（D15）*

原典は導来版を Δ の対称モノイダル性から一行で示す。本体は環版で、Hodge–Tate 比較なしに示せるが、環として perfectoid 化が存在する場合（perfectoid 環の全射商など）に限る。

:::

:::corollary "bs_8_14" (lean := "SerrePositivity.BhattScholze.PerfectoidizationInterface.PerfectoidizationInterfaceE3, SerrePositivity.BhattScholze.Inputs.exists_perfectoidizationInterfaceE3")
*系 8.14*　離散なら普遍 perfectoid 環。対応表の状態：未証明の入力に依存。

E3 存在 sorry の universal 欄により、離散な通常 R-代数の perfd が離散なら H⁰ の指定単位が普遍 perfectoid 化となる。一般の animated S の原文全体には拡張しない。

*系 8.4.2（原典 Cor 8.14） — 主張*

$`S` を perfectoid 環からの写像をもつ導来 p 完備な単体的環とし、$`S_{\mathrm{perfd}}` が連結（Lemma 8.4 により、次数 0 に集中することと同値）と仮定する。このとき $`S_{\mathrm{perfd}}` は perfectoid 環で、$`S\to S_{\mathrm{perfd}}` は $`S` から perfectoid 環への普遍な写像である。

*系 8.4.2（原典 Cor 8.14） — Lean*

主張は \`PerfectoidizationInterfaceE3\` の欄 \`universal\`（Derived/Interface:680）で、固定した perfectoid 環 $`R` 上の離散な $`R` 代数 $`S` について、値が離散なら $`H^0` の単位が普遍 perfectoid 化（\`IsPerfectoidization\`）であることを受け取る。証明は本体にない。drafts に前半 \`perfectoidization\_isIntegralPerfectoid\_of\_discrete\`（drafts/A7/DiscreteCore:71）、普遍性 \`perfectoidization\_isPerfectoidization\_of\_discrete\`（drafts/A7/UniversalProperty:212）、欄の形 \`e3Universal\`（:224）がある。

*系 8.4.2（原典 Cor 8.14） — 証明*

*perfectoid であること.* $`S_{\mathrm{perfd}}=\Delta_{S/A,\mathrm{perf}}\otimes^L_AA/I` が離散なら、導来 Nakayama により $`\Delta_{S/A,\mathrm{perf}}` も離散（補った：$`\Delta_{S/A,\mathrm{perf}}` は導来 $`I` 完備で coconnective（Lemma 8.4）。$`H^i`（$`i\ge1`）では $`d` 倍が同型なので、導来 $`d` 完備性から 0）。すると Lemma 7.7 の証明の議論で $`\Delta_{S/A,\mathrm{perf}}` は完全で p 完備な δ-$`A` 代数であり、$`d` は distinguished なので非零因子（Lemma 2.34）、$`(\Delta_{S/A,\mathrm{perf}},I\Delta_{S/A,\mathrm{perf}})` は完全 prism。よって $`S_{\mathrm{perfd}}` は perfectoid 環（Thm 3.10）。

*普遍性.* perfectoid な $`S'` への任意の $`S_{\mathrm{perfd}}\to S'` が合成 $`S\to S_{\mathrm{perfd}}\to S'` で決まることを示す（存在は perfectoid な $`S'` について $`S'\simeq S'_{\mathrm{perfd}}` と関手性から）。同値な言い換えとして、perfectoid な $`S'` への任意の $`\eta\colon S_{\mathrm{perfd}}\widehat\otimes^L_SS_{\mathrm{perfd}}\to S'` が乗法 $`S_{\mathrm{perfd}}\widehat\otimes^L_SS_{\mathrm{perfd}}\to S_{\mathrm{perfd}}` を（必然的に一意に）通ることを確かめる（二つの写像の一致は、それらが定める $`\eta` が対角を通ることと同じ）。$`S'\simeq S'_{\mathrm{perfd}}` なので、$`(-)_{\mathrm{perfd}}` を当てると $`\eta` は $`S_{\mathrm{perfd}}\widehat\otimes^L_SS_{\mathrm{perfd}}\to(S_{\mathrm{perfd}}\widehat\otimes^L_SS_{\mathrm{perfd}})_{\mathrm{perfd}}` を通る。Prop 8.13 により $`(S_{\mathrm{perfd}}\widehat\otimes^L_SS_{\mathrm{perfd}})_{\mathrm{perfd}}\simeq S_{\mathrm{perfd}}\widehat\otimes^L_{S_{\mathrm{perfd}}}S_{\mathrm{perfd}}`（$`(S_{\mathrm{perfd}})_{\mathrm{perfd}}\simeq S_{\mathrm{perfd}}`）$`\simeq S_{\mathrm{perfd}}` で、これは乗法写像で与えられるので、主張を得る。

*系 8.4.2（原典 Cor 8.14） — 原典との差（D61）*

原典の「perfectoid 環からの写像をもつ単体的環」を、Lean は基底の perfectoid 環 $`R` を固定した $`R` 代数で述べ、\`PerfectoidizationInterfaceE3\` の欄では離散な $`S` に限る。$`A` の選び方によらないこと（Prop 8.5 の系）で一般の場合に戻る。普遍性は離散な場合の環準同型の普遍性として受け取る。

:::

