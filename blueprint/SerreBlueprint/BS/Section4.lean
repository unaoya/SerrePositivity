import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismHomLift
import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.AffineCechPrismBaseChange
import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.AffineCechSiteNerve
import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.CechAlexanderAssembly
import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.CechAlexanderSmall
import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Complexes.CechAlexanderComplex
import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.BaseChange.AffineEnvelopeDerivedBaseChange
import SerrePositivity.BhattScholze.Prismatic.Site.FlatCechDescent
import SerrePositivity.BhattScholze.Prismatic.Site.FlatCechSheaf
import SerrePositivity.BhattScholze.Prismatic.Site.FlatSiteSheaf
import SerrePositivity.BhattScholze.Prismatic.Site.PrismOver

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "§4 The prismatic site and formulation of the Hodge-Tate comparison" =>
%%%
number := false
tag := "bs-4"
%%%

BS §4 の項目と、本体の宣言との対応。本文は対応表（`research/bs-coverage`）の照合の理由で、原典の本文の写しではない。

*導入*

固定した有界 prism $`(A,I)` と p 完全 smooth な $`A/I` 代数 $`R` について、prismatic site $`(R/A)_\Delta` とその構造層のコホモロジー $`\Delta_{R/A}` を定義し（4.1）、HT 比較を定式化し（4.2）、Čech–Alexander 複体で $`\Delta_{R/A}` を具体的に計算する（4.3）。本体にあるのは、affine な $`R` の site の圏・平坦位相・構造層の層性、多項式代数の HT 写像 $`\eta^*` と Lemma 4.10、HT 比較の主張の型と結晶基底 $`(\mathbb Z_p,(p))` での証明、Čech–Alexander 模型の組み立て・弱始性・余積・底変換との項ごとの両立。$`\Delta_{R/A}` を site の $`R\Gamma` として定義すること、模型がそれを計算すること、Lemma 4.20・4.22 は drafts にある。形式化の設計の決定（site の大きさの切り落とし、$`R\Gamma` の意味など）は a0-design.md にあり、原典との差として各項目の下に引く。

*4.1 prismatic site*

有界 prism $`(A,I)` を固定し、$`A` 上の形式スキームには $`(p,I)` 進位相、$`A/I` 上の形式スキームには $`p` 進位相を入れる。この小節では $`p` 進形式 $`A/I` スキーム $`X` の prismatic site $`(X/A)_\Delta` を定め（定義 4.1.1）、その topos の見方（注意 4.1.3）、étale 位相との関係（定義 4.1.4）、位相の取り替え（注意 4.1.5）、完全 site と絶対 site（注意 4.1.6・4.1.7）を述べ、最後に完全 prism からの射の一意な持ち上げ（命題 4.1.8）を示す。本体にあるのは affine の場合の site・平坦位相・構造層が層であること（定義 4.1.1）と、標的が有界な場合の命題 4.1.8。注意 4.1.6 は drafts、他の注意と定義 4.1.4 は本体にない。

*4.2 HT 比較の定式化*

この小節では有界 prism $`(A,I)` と、$`A/I` 上の smooth な p 進形式スキーム $`X` を固定する。prismatic site の構造層を $`X_{\mathrm{\acute et}}` へ押し出して $`\Delta_{X/A}` と $`\overline\Delta_{X/A}` を作り、Bockstein で $`H^*(\overline\Delta_{X/A})\{*\}` を dg 代数にして、de Rham 複体からの HT 比較の写像 $`\eta^*_X` を構成する（4.2.1〜4.2.2）。それが同型であるという HT 比較（4.2.3）の証明は §5（標数 p）と §6（一般）で与えられ、ここではその帰結（4.2.4〜4.2.7）を述べる。

Lean の本体はこの小節を*多項式代数の場合*に限って持つ：基底は一般の有界向き付き prism $`(A,(d))`、$`X=\mathrm{Spf}\,R` で $`R=(A/d)\langle X_1,\dots,X_r\rangle`（\`affineAlgebra\`（HodgeTateAffineModel:38））。$`\overline\Delta_{R/A}` の代わりに Rem 4.19 の小さい Čech–Alexander 模型 \`cechAlexanderAffine\`（AffineEnvelopeConstruction:243）の各項を d で割った余単体的環 \`reducedModel\`（HodgeTateAffineModel:93）を使い、そのコホモロジーを \`hodgeTateCohomology'\`（HodgeTateZero:39）と書く。HT 比較が全単射であることが証明済みなのは結晶基底 $`(\mathbb Z_p,(p))` の場合。

*4.3 Čech–Alexander 複体*

prismatic cohomology を具体的な余単体的環で計算する一般論。affine の場合の記号を定め（4.3.1）、多項式代数からの全射の envelope で site の弱始対象を作り（4.3.2）、その Čech 脈体が $`\Delta_{R/A}` を計算することを示す（4.3.3）。affine 空間の場合には prism の底変換と両立する模型があり（4.3.4）、これを使って底変換（4.3.5）と étale 局所化（4.3.6）を示す。どちらも純代数の補題 4.3.7 に帰着する。

Lean では site の対象は、固定した向き付き有界 prism $`(A,(d))` の上の有界な向き付き prism $`(B,dB)` と $`R\to B/dB` の組で、台の濃度が $`\le\kappa` のもの（原典 Def 4.1 の affine の場合。D5・D16・D19）。剛性（命題 3.2.1、原典 Lemma 3.5）により $`IB=dB` なので、以下 $`I=(d)` と書く。

:::definition "bs_4_1" (lean := "SerrePositivity.BhattScholze.Prismatic.PrismOver, SerrePositivity.BhattScholze.Prismatic.PrismOver.flatTopology, SerrePositivity.BhattScholze.Prismatic.PrismOver.isSheaf_of_flatRingCechExact, SerrePositivity.BhattScholze.Prismatic.PrismOver.structureRing_isSheaf, SerrePositivity.BhattScholze.Prismatic.PrismOver.quotientStructureRing_isSheaf")
*定義 4.1*　prismatic site。対応表の状態：一部（special）。

*主張*　$`A/I` 上の $`p` 進形式スキーム $`X` の prismatic site は、基底有界 prism からの射 $`(A,I)\to(B,IB)` と $`A/I` 上の $`\operatorname{Spf}(B/IB)\to X` をもつ有界 prism を使って定める。形式スペクトル側の被覆は忠実平坦な prism の射から来て、$`B` および $`B/IB` を割り当てる前層は層である。

affine・向き付き有界基底・admissible cutoff の同じ PrismOver の flat topology と二つの構造環の層条件。一般の形式的スキームや cutoff を外した site の同定は含まない。

*定義 4.1.1（原典 Def 4.1：prismatic site と構造層） — 主張*

$`X` を $`A/I` 上の $`p` 進形式スキームとする。$`(X/A)_\Delta` を、有界 prism の射 $`(A,I)\to(B,IB)` と $`A/I` 上の射 $`\mathrm{Spf}(B/IB)\to X` の組の圏とする（射は自明なもの）。対象を
$$`(\mathrm{Spf}(B)\leftarrow\mathrm{Spf}(B/IB)\to X)\in(X/A)_\Delta`
と書く。すなわち対象は、δ-$`A` 代数 $`B` と、図式
$$`\begin{array}{ccc}\mathrm{Spf}(B/IB)&\longrightarrow&\mathrm{Spf}(B)\\ {\scriptstyle f}\downarrow&&\downarrow{\scriptstyle g}\\ X&&\\ \downarrow&&\\ \mathrm{Spf}(A/I)&\longrightarrow&\mathrm{Spf}(A)\end{array}`
の $`f`・$`g` を与えるデータである。射 $`(\mathrm{Spf}(C)\leftarrow\mathrm{Spf}(C/IC)\to X)\to(\mathrm{Spf}(B)\leftarrow\mathrm{Spf}(B/IB)\to X)` が*平坦被覆*であるとは、$`(B,IB)\to(C,IC)` が prism の忠実平坦な射、すなわち $`C` が $`B` 上 $`(p,IB)` 完全忠実平坦であること。この平坦被覆で位相を入れた $`(X/A)_\Delta` を $`X/A` の *prismatic site* と呼ぶ。

$`(\mathrm{Spf}(B)\leftarrow\mathrm{Spf}(B/IB)\to X)\mapsto B`（resp. $`B/IB`）は、可換 $`A` 代数（resp. $`\mathcal O(X)` 代数）の前層 $`\mathcal O_\Delta`（resp. $`\overline{\mathcal O}_\Delta`）を定める。系 3.4.3（原典 Cor 3.12）から、$`(X/A)_\Delta` はこの位相で site になり、$`\mathcal O_\Delta`・$`\overline{\mathcal O}_\Delta` は層である。$`\mathcal O_\Delta` を*構造層*と呼ぶ。

*定義 4.1.1（原典 Def 4.1：prismatic site と構造層） — Lean*

*構造層*：$`\mathcal O_\Delta`・$`\overline{\mathcal O}_\Delta` は環値の関手 \`structureRing\`・\`quotientStructureRing\`（FlatSiteSheaf:54・61）、$`A` 代数としての読み替えは \`prismSiteAlgebras\`（PrismOver:127、$`A` の下の環の圏への関手）。層であることは \`structureRing\_isSheaf\`・\`quotientStructureRing\_isSheaf\`（FlatCechDescent:179・184）で、増大 Čech 複体の完全性から層条件を出す一般の判定 \`isSheaf\_of\_flatRingCechExact\`（FlatCechSheaf:49）を経由する（系 3.4.3 の Lean の囲みを参照）。

小さい模型の上の site \`PrismaticSite\` とその位相・構造前層は drafts（drafts/A0/PrismaticSite:93・106・127）。一般の形式スキーム $`X` の site は本体にも drafts にもない。

*定義 4.1.1（原典 Def 4.1：prismatic site と構造層） — 証明*

主張の後半（site であること、$`\mathcal O_\Delta`・$`\overline{\mathcal O}_\Delta` が層であること）は系 3.4.3 そのもの。site の公理（同型・合成・押し出し）は、$`X` への射のデータが押し出しに沿って一意に引き継がれることを加えれば、有界 prism の圏の場合と同じ：忠実平坦な $`(B,IB)\to(C,IC)` と任意の $`(B,IB)\to(B',IB')` の押し出しは $`C\widehat\otimes_BB'`（導来 $`(p,I)` 完備化）で、その mod $`I` の $`\mathrm{Spf}` は $`\mathrm{Spf}(B'/IB')\to X` を通して $`X` の上にある。層条件は対象の $`X` への射に関係しないので、系 3.4.3 の Čech 余脈体の極限図式がそのまま使える。

*定義 4.1.1（原典 Def 4.1：prismatic site と構造層） — 原典との差（D5・D16・D19・D22）*

原典の一般の $`p` 進形式スキーム $`X` は扱わず、affine の $`X=\mathrm{Spf}(R)` に限る。基底は向き付き（D5）で、site の対象も向き付き（基底が向き付きなら剛性で自動、D19）。位相は忠実平坦な単一射の被覆が生成する位相として定義する（D22）。D19・D22 の評価は系 3.4.3 の下にある。台の濃度を $`\kappa` で切り落とす（D16）。

:::

:::proposition "bs_4_2"
*注意 4.2*　smooth の仮定についての注意。対応表の状態：なし。

一般 p-adic scheme への left Kan extension と derived site による回収の説明を本体で未同定。

*注意 4.1.2（原典 Rem 4.2：smooth の仮定） — 主張*

この論文では prismatic site $`(X/A)_\Delta` を、ほとんど常に $`X` が $`A/I` 上 smooth な $`p` 進形式スキームであるという仮定の下で使う。主定理（Hodge–Tate 比較など）はこの仮定なしには成り立たない。後に prismatic コホモロジーを、smooth な場合からの左 Kan 拡張ですべての $`p` 進形式 $`A/I` スキームに延ばす。ここではしないが、導来 prismatic site（単体的環を全体で使う）でも同じ定義が得られる。

以下この小節では、特に断らない限り $`X` は $`A/I` 上 smooth な $`p` 進形式スキームとする。

*注意 4.1.2（原典 Rem 4.2：smooth の仮定） — Lean*

本体にない（注意なので主張する宣言はない）。本体の site（定義 4.1.1）は $`R` に smooth の仮定を置かずに定義され、Hodge–Tate 比較は多項式代数の場合に述べる（第 4.2 節）。

*注意 4.1.2（原典 Rem 4.2：smooth の仮定） — 証明*

証明すべき主張はない。左 Kan 拡張による延長は原典 Construction 7.6、導来 prismatic site の方法は原典では扱わない。

:::

:::proposition "bs_4_3"
*注意 4.3*　prismatic topos の slice 表示と関手性。対応表の状態：なし。

同じ prismatic topos の slice 表示と形式的スキームの射による関手性を未同定。

*注意 4.1.3（原典 Rem 4.3：slice topos としての prismatic topos と関手性） — 主張*

$`(\ast/A)_\Delta` を $`(A,I)` 上の有界 prism 全体の圏に系 3.4.3 のように位相を入れた site とする（これは上の $`(\mathrm{Spf}(A/I)/A)_\Delta` と一致する）。smooth な $`p` 進形式スキーム $`X` は $`(\ast/A)_\Delta` 上の前層
$$`h_X(B,IB)=\mathrm{Hom}_{A/I}(\mathrm{Spf}(B/IB),X)`
を定め、系 3.4.3 の議論の変形で $`h_X` は層である。定義をほどくと、$`(X/A)_\Delta` は組 $`((B,IB)\in(\ast/A)_\Delta,\ \eta\in h_X(B,IB))` の圏に $`(\ast/A)_\Delta` からの位相を入れたものと一致し、特に
$$`\mathrm{Shv}((X/A)_\Delta)\simeq\mathrm{Shv}((\ast/A)_\Delta)_{/h_X}`
（slice topos）とみなせる。この見方で関手性が明らかになる：smooth な $`p` 進形式 $`A/I` スキームの射 $`f\colon X\to Y` は層の射 $`h_X\to h_Y` を与え、slice topos の射 $`\mathrm{Shv}((X/A)_\Delta)\to\mathrm{Shv}((Y/A)_\Delta)` を引き起こす。

*注意 4.1.3（原典 Rem 4.3：slice topos としての prismatic topos と関手性） — 証明*

（補った）\*\*$`h_X` が層であること.\*\* 忠実平坦な $`(B,IB)\to(C,IC)` について、$`h_X(B)\to h_X(C)\rightrightarrows h_X(C\widehat\otimes_BC)` が等化子であることを示す。$`\mathrm{Spf}(B/IB)=\mathrm{colim}_n\mathrm{Spec}(B/(I,p^n))` なので $`h_X(B)=\lim_n\mathrm{Hom}(\mathrm{Spec}(B/(I,p^n)),X)`（$`p^n=0` なので $`\mathrm{Spec}(B/(I,p^n))\to X` はスキーム $`X\otimes\mathbb Z/p^n` を経由する）。各 $`n` で $`B/(I,p^n)\to C/(I,p^n)` は（$`(p,I)` 完全忠実平坦性の定義から）通常の忠実平坦な環の射で、$`(C\widehat\otimes_BC)/(I,p^n)=C/(I,p^n)\otimes_{B/(I,p^n)}C/(I,p^n)`。スキーム $`X\otimes\mathbb Z/p^n` が表す関手は fpqc 層なので、各 $`n` で等化子。等化子は極限と交換するので $`n` について極限を取ればよい。

*slice の同一視.* 対象の対応は定義から。被覆の定義は $`X` への射に関係しないので、位相も $`(\ast/A)_\Delta` から誘導されたもの。site $`\mathcal C` と層 $`F` について、組 $`(U,\eta\in F(U))` の site（$`\mathcal C` の $`F` 上の slice）の層の topos は $`\mathrm{Shv}(\mathcal C)_{/F}` と同値（topos の局所化の一般論）なので、$`F=h_X` とおけばよい。関手性は、層の射 $`h_X\to h_Y` が slice topos の射を与えるという一般論から。

:::

:::definition "bs_4_4"
*構成 4.4*　prismatic 層と étale 層。対応表の状態：なし。

形式的 étale site への cocontinuous functor と ν\_\* の比較を未同定。

*定義 4.1.4（原典 Construction 4.4：prismatic 層と étale 層） — 主張*

$`f\mathrm{Sch}_{/X}` を、adic な射 $`U\to X` を持つ $`p` 進形式スキーム $`U` の圏に étale 位相を入れたものとする。$`(B,IB)` を $`\mathrm{Spf}(B/IB)\to X` に送る自然な関手 $`\mu\colon(X/A)_\Delta\to f\mathrm{Sch}_{/X}` がある。この関手は命題 2.2.4（原典 Lemma 2.18）により余連続である：有界 prism $`(B,IB)` と $`p` 完全エタールな射（resp. 被覆）$`B/IB\to C` に対し、これを mod $`IB` で持ち上げる δ 環の $`(p,I)` 完全エタールな射（resp. 被覆）$`B\to C` がただ一つある。したがって topos の射
$$`\mu_X\colon\mathrm{Shv}((X/A)_\Delta)\to\mathrm{Shv}(f\mathrm{Sch}_{/X})`
が定まる（\[Sta, Tag 00XO\]）。制限で定まる topos の射 $`\mathrm{Shv}(f\mathrm{Sch}_{/X})\to\mathrm{Shv}(X_{\mathrm{et}})` と合成して
$$`\nu_X\colon\mathrm{Shv}((X/A)_\Delta)\to\mathrm{Shv}(X_{\mathrm{et}})`
を得る（紛れなければ $`\mu`・$`\nu` と書く）。順像 $`\nu_*` は次のように書ける：エタールな $`U\to X` について $`(U/A)_\Delta` は被覆を保って $`(X/A)_\Delta` の slice になり、この関手に沿った制限は層を層に送る。定義をほどくと
$$`(\nu_*F)(U\to X)=H^0((U/A)_\Delta,F|_{(U/A)_\Delta}).`
すなわち $`\nu` で prismatic コホモロジーを $`X_{\mathrm{et}}` 上に局所化できる。

*定義 4.1.4（原典 Construction 4.4：prismatic 層と étale 層） — Lean*

本体にない。drafts にもない。本体の site は affine の $`R` だけなので、$`X_{\mathrm{et}}` 上の局所化は使わず、$`\Delta_{R/A}` は site の大域切断として直接定める（第 4.3 節）。

*定義 4.1.4（原典 Construction 4.4：prismatic 層と étale 層） — 証明*

（補った）*余連続性.* 示すのは：$`\mu(B,IB)=\mathrm{Spf}(B/IB)` の étale 被覆 $`\{U_i\to\mathrm{Spf}(B/IB)\}` は、site の被覆 $`(B,IB)\to(C,IC)` の像で細分される。$`\mathrm{Spf}(B/IB)` は quasi-compact なので、有限個の affine $`\mathrm{Spf}(C_j)\to U_{i_j}` で覆い、$`\bar C=\prod_jC_j` とすれば $`B/IB\to\bar C` は $`p` 完全エタールで $`p` 完全忠実平坦。命題 2.2.4 でこれを $`(p,I)` 完全エタールな δ 環の射 $`B\to C`（$`C/IC=\bar C`）に持ち上げる。$`C` は $`B` 上 $`(p,I)` 完全忠実平坦（mod $`(p,I)` で忠実平坦、完全平坦性は mod $`I` の判定と導来中山）なので、命題 3.2.3（原典 Lemma 3.7 (3)）から $`(C,IC)` は有界 prism で、$`(B,IB)\to(C,IC)` は忠実平坦な射。その像 $`\mathrm{Spf}(\bar C)\to\mathrm{Spf}(B/IB)` は各 $`U_{i_j}` を経由するので細分になる。余連続な関手は順像が層を層に送る関手 $`\mu_*` と、その左随伴として完全な $`\mu^{-1}` を持ち、topos の射を与える（Tag 00XO）。

\*\*$`\nu_*` の式.\*\* エタールな $`U\to X` について、$`(U/A)_\Delta\to(X/A)_\Delta` は $`\mathrm{Spf}(B/IB)\to U` を $`U\to X` と合成する関手で、$`(X/A)_\Delta` の $`h_U`（注意 4.1.3）上の slice と同一視される。被覆の定義は $`X`・$`U` への射によらないので被覆を保ち、slice への制限は層を層に送る。$`\nu_*F(U)=\mu_*F(U)=\mathrm{Hom}(h_U,F)`（$`\mu_*F(V)=\mathrm{Hom}(\mu^{-1}h_V,F)` で、$`\mu^{-1}h_U=h_U`）は slice 上の $`F` の大域切断 $`H^0((U/A)_\Delta,F|_{(U/A)_\Delta})` に等しい。

:::

:::proposition "bs_4_5"
*注意 4.5*　位相の取り替え。対応表の状態：なし。

比較の宣言は drafts の derivedGlobalSections\_of\_le にのみ存在。原文の各位相での O\_Δ・crystal の RΓ 比較を本体で未同定。

*注意 4.1.5（原典 Rem 4.5：位相の取り替え） — 主張*

定義 4.1.1 の平坦位相を Zariski・Nisnevich・étale 位相に取り替えても、同じ圏の上の site が得られ、topos の比較の射
$$`\mathrm{Shv}((X/A)_\Delta)\to\mathrm{Shv}((X/A)_{\Delta,\mathrm{et}})\to\mathrm{Shv}((X/A)_{\Delta,\mathrm{Nis}})\to\mathrm{Shv}((X/A)_{\Delta,\mathrm{Zar}})`
がある。系 3.4.3 と注意 4.1.3 の見方から、この合成の各射に沿った導来順像は $`\mathcal O_\Delta`（resp. $`\overline{\mathcal O}_\Delta`）をそれ自身に送る。特に、$`\mathcal O_\Delta`・$`\overline{\mathcal O}_\Delta` 係数の $`X` のコホモロジーはどの位相でも計算できる。より一般に、$`D_{(p,I)\text{-comp}}(-)` の $`(p,I)` 完全忠実平坦降下を使うと、同様のことが $`(p,I)` 完備な複体の crystal $`M` 係数のコホモロジーにも成り立つ。ここで crystal とは、底変換と両立する対応
$$`\eta:=(\mathrm{Spf}(B)\leftarrow\mathrm{Spf}(B/IB)\to X)\in(X/A)_\Delta\ \mapsto\ M(\eta)\in D_{(p,I)\text{-comp}}(B)`
のこと。正確には、$`D(\mathrm{PShv}((X/A)_\Delta,\mathcal O_\Delta))` のこの性質を持つ対象 $`M` の充満部分圏の対象として定める（crystal の概念は圏 $`(X/A)_\Delta` と前層 $`\mathcal O_\Delta` だけで決まり、位相によらない）。

コホモロジーと crystal の概念が位相によらないのに平坦位相を選ぶ理由は、自然さのほかに、「perfectoid」な状況からの quasisyntomic 降下による議論の余地を残すためである（役に立つ平坦被覆の例は原典 Ex 7.12・7.13。\[BS21\] では $`\mathcal O_K` の絶対 prismatic site の $`F` crystal の理解に使われる）。

*注意 4.1.5（原典 Rem 4.5：位相の取り替え） — 証明*

（補った）Zariski・Nisnevich・étale の被覆は（$`(p,I)` 完全な意味で）平坦被覆なので、位相は $`\tau_{\mathrm{Zar}}\le\tau_{\mathrm{Nis}}\le\tau_{\mathrm{et}}\le\tau_{\mathrm{fl}}` と並び、恒等関手が比較の topos の射を与える。その順像は層を（粗い位相の層として）そのまま見る関手。導来順像が $`\mathcal O_\Delta` を保つことは、$`\mathcal O_\Delta` の高次コホモロジーが各対象の上でどの位相でも消えることと同じ。系 3.4.3 は、平坦被覆の Čech 余脈体に沿って $`B\to C^\bullet` が極限図式（高次 Čech コホモロジーが消える）であることを示す。これは粗い位相の被覆（特別な平坦被覆）にも当てはまり、被覆の族は押し出しで閉じているので、Cartan の判定（全対象のすべての被覆で高次 Čech コホモロジーが消えれば層コホモロジーも消える）から、どの位相でも $`H^i(B,\mathcal O_\Delta)=0`（$`i>0`）。よって比較の射に沿った $`R\pi_*\mathcal O_\Delta=\mathcal O_\Delta`。$`\overline{\mathcal O}_\Delta` も同じ。crystal 係数の場合は、系 3.4.3 の証明の $`\mathrm{Kos}(-;p^n,I^n)` の忠実平坦降下を $`D_{(p,I)\text{-comp}}` の降下に置き換えて同じ議論をする。注意 4.1.3 の見方は、$`X` の site を $`(\ast/A)_\Delta` の slice とみて、$`(\ast/A)_\Delta` での主張から $`X` の場合を得るのに使う。

宣言：`derivedGlobalSections_of_le`

:::

:::proposition "bs_4_6"
*注意 4.6*　完全 prismatic site。対応表の状態：なし。

perfect prismatic site と perfectoid-under category の比較は drafts。通常の個別 prism の商の定理だけではこの site の同値を直接与えない。

*注意 4.1.6（原典 Rem 4.6：完全 prismatic site） — 主張*

任意の $`p` 進形式 $`A/I` スキーム $`Y` について、$`B` が完全である対象 $`(\mathrm{Spf}(B)\leftarrow\mathrm{Spf}(B/IB)\to Y)` の充満部分圏 $`(Y/A)_\Delta^{\mathrm{perf}}\subset(Y/A)_\Delta` に制限して、prismatic site（定義 4.1.1）の変種が定まる。これは同値に、$`A/I` 上の perfectoid 環 $`R` と射 $`\mathrm{Spf}(R)\to Y` の組の圏であり、prism の概念を使わない記述を持つ。完全 prismatic site のコホモロジーは prismatic site のそれとは趣が異なり、原典 §8 で調べる。

*注意 4.1.6（原典 Rem 4.6：完全 prismatic site） — 証明*

原典は「同値に」の理由を書いていない。（補った）\*\*基底 $`(A,I)` が完全な場合.\*\* 関手 $`(B,IB)\mapsto B/IB` を考える。対象：定理 3.4.1（原典 Thm 3.10）から $`B/IB` は perfectoid で、逆に $`A/I` 上の perfectoid 環 $`R` について $`(A_{\inf}(R),\ker\theta)` は完全 prism、構造射 $`A/I\to R` は命題 4.1.8 で prism の射 $`(A,I)\to(A_{\inf}(R),\ker\theta)` に一意に持ち上がる。射：完全 prism $`(B,IB)\to(B',IB')` の射は命題 4.1.8 で $`B/IB\to B'/IB'` と一対一に対応し、$`A` からの射と両立することも、$`A` が完全なので mod $`I` の両立から命題 4.1.8 の一意性で出る。$`Y` への射のデータは両辺で同じ $`\mathrm{Spf}(B/IB)\to Y`。

*一般の基底.* 命題 4.1.8 の後の注意（原典）が言うように、完全でない $`(A,I)` から完全 prism への射は mod $`I` の射で決まらない。そのとき、同じ $`B` と同じ $`A/I\to B/IB` で $`A\to B` だけが違う二つの対象は、恒等射 $`B/IB\to B/IB` の持ち上げが恒等射しかない（命題 4.1.8）ので同型でなく、関手 $`(B,IB)\mapsto B/IB` は同値にならない。したがって原典の「同値に」は、完全な基底の場合（§8 で使う場合）の主張として読む。

*注意 4.1.6（原典 Rem 4.6：完全 prismatic site） — 原典との差（D5・D16）*

drafts の完全 site は、定義 4.1.1 の Lean の site（affine・向き付き・濃度 $`\le\kappa`）の充満部分圏で、perfectoid 環の圏との同値は完全な基底の上でだけ述べる。原典は一般の $`Y` と一般の基底で述べる。

宣言：`PerfectPrismaticSite`、`perfectSite`、`perfectFlatTopology`、`perfectSiteEquivPerfectoidUnder`

:::

:::proposition "bs_4_7"
*注意 4.7*　絶対 prismatic site。対応表の状態：なし。

絶対 prismatic site の対応する本体の定義を未同定。

*注意 4.1.7（原典 Rem 4.7：絶対 prismatic site） — 主張*

任意の $`p` 進形式スキーム $`X` について、*絶対 prismatic site* $`(X)_\Delta` も考えられる。対象は、有界 prism $`(B,J)` と $`p` 進形式スキームの射 $`\mathrm{Spf}(B/J)\to X` の組。この論文ではこの概念を本格的には調べないが、次の観察（命題 4.1.8）は後で役に立つ。

*注意 4.1.7（原典 Rem 4.7：絶対 prismatic site） — 証明*

証明すべき主張はない。

:::

:::lemma_ "bs_4_8" (lean := "SerrePositivity.BhattScholze.existsUnique_perfectPrismHomLift_to_bounded, SerrePositivity.BhattScholze.perfectPrismHom_ext_to_bounded_target, SerrePositivity.BhattScholze.existsUnique_perfectPrismRingHomLift_to_bounded")
*補題 4.8*　完全 prism からの写像の一意持ち上げ。対応表の状態：一部（stronger-hyp）。

*主張*　$`(A,I)` が完全 prism なら、任意の prism $`(B,J)` への剰余環の射 $`A/I\to B/J` は、prism の射 $`(A,I)\to(B,J)` に一意に持ち上がる。

同じ perfect 向き付き源と bounded 向き付き標的に限定すると、指定商の射の prism 射への存在一意の持ち上げを証明する。一般の非有界・非主 ideal の標的は扱わない。

*命題 4.1.8（原典 Lemma 4.8：完全 prism からの射の一意な持ち上げ） — 主張*

$`(A,I)` を perfectoid 環 $`R=A/I` に対応する完全 prism とする。任意の prism $`(B,J)` について、可換環の射 $`A/I\to B/J` は prism の射 $`(A,I)\to(B,J)` にただ一つ持ち上がる。

示唆的な記法では、$`A\in(R)_\Delta` は始対象（site にするために反対圏に移るので、むしろ終対象）であり、$`(R)_\Delta=(R/A)_\Delta` となる。

「双対」は成り立たない：prism $`(A,I)` と完全 prism $`(B,J)` について、同じ $`A/I\to B/J` を引き起こす射 $`(A,I)\to(B,J)` が複数ありうる。

*命題 4.1.8（原典 Lemma 4.8：完全 prism からの射の一意な持ち上げ） — Lean*

標的が*有界*な向き付き prism の場合：\`existsUnique\_perfectPrismHomLift\_to\_bounded\`（PerfectPrismHomLift:749）。源は $`\varphi` が全単射な向き付き prism、射は生成元の保存を要求しない。部品：環の射としての一意な持ち上げ \`existsUnique\_perfectPrismRingHomLift\_to\_bounded\`（:712）、一意性 \`perfectPrismHom\_ext\_to\_bounded\_target\`（:199）と \`ringHom\_ext\_to\_boundedPrism\_of\_perfect\_source\`（:165）、その計算の核 \`ringHom\_ext\_of\_pow\_add\_natCast\_mul\`（:99）、δ 射であること \`perfectSource\_ringHom\_isDeltaHom\_to\_boundedPrism\`（:368）と一般の $`p` 進分離な δ 環への版 \`perfectSource\_ringHom\_isDeltaHom\`（:343）、Frobenius との可換性 \`perfectSource\_ringHom\_map\_frobenius\`（:271）、$`W_2` への二つの射の比較 \`wittTwoHom\_ext\_of\_perfectSource\_approximation\`（:293）。存在に使う tilt の比較 \`boundedPrism\_preTiltQuotientEquiv\`（Tilt:398）、Witt 持ち上げの一意性 \`wittLift\_unique\`（Lift:74）、$`W(A/p)\cong A` の \`perfectPrismWittRecoveryEquiv\`（PerfectPrismPerfectoid:240）。標的も完全な場合は定理 3.4.1 (c) の \`existsUnique\_perfectPrismHomLift\`（PerfectPrismHomLift:522）。「始対象」の言い換えと「双対」が成り立たないことは本体にない。

*命題 4.1.8（原典 Lemma 4.8：完全 prism からの射の一意な持ち上げ） — 証明*

*原典の証明.* $`A` は標数 $`p` の完全環の Witt 環なので、$`L_{A/\mathbb Z_p}` は導来 $`p` 完備化の後に消える。$`B`・$`B/J` はどちらも導来 $`p` 完備なので、変形理論により $`\mathrm{Hom}(A,B)\simeq\mathrm{Hom}(A,B/J)\simeq\mathrm{Hom}(A,B/(J,p))`。よって $`A\to A/I\to B/J` は環の射 $`\alpha\colon A\to B` にただ一つ持ち上がる。（補った）有界な場合、$`B` は $`J` 進完備（命題 3.2.3 (1)）なので $`B=\lim_nB/J^n` とし、平方零拡大 $`B/J^{n+1}\to B/J^n` ごとに持ち上げの障害と自由度が $`\mathrm{Ext}^i(L_{A/\mathbb Z_p},J^n/J^{n+1})`（$`i=1,0`）にあり、$`J^n/J^{n+1}` は導来 $`p` 完備なので $`L_{A/\mathbb Z_p}` の $`p` 完備化の消滅からこれらが消える。$`B/J\to B/(J,p)` も $`B/J` の導来 $`p` 完備性で同様。同じ論法で $`\alpha` は Frobenius 持ち上げと両立する：$`\varphi_B\circ\alpha` と $`\alpha\circ\varphi_A` はどちらも $`A\to B/p` の同じ射（$`\alpha` mod $`p` の Frobenius 合成）の持ち上げ。構成から $`\alpha(I)\subset J`。残るのは $`\alpha` が δ 射であること（$`B` に $`p` ねじれがありうるので自動ではない）。$`\varphi_A` は全単射なので、$`a\mapsto(\alpha(\varphi_A^{-n}(a)))_n` により $`\alpha` は $`B^{\mathrm{perf}}:=\lim_\varphi B\to B` を一意に経由する。$`B^{\mathrm{perf}}` は完全 δ 環なので $`p` ねじれなし（命題 2.4.3、原典 Lemma 2.28）で、$`\varphi` 同変な $`A\to B^{\mathrm{perf}}` は自動的に δ 射（命題 2.1.3 (2)）。$`B^{\mathrm{perf}}\to B` は構成から δ 射なので、合成 $`\alpha` も δ 射。

*Lean の証明*（標的は有界）。*存在*：有界 prism では、商写像が tilt の同型 $`B^\flat\cong(B/J)^\flat` を引き起こす。完全環 $`k=A/p` からの $`k\to(B/J)/p` を完全化の普遍性で $`k\to(B/J)^\flat\cong B^\flat` に延ばし、Witt 関手と Fontaine の $`\theta_B\colon W(B^\flat)\to B` で $`W(k)\to B` を作り、$`W(k)\cong A`（系 2.4.6）と合成する。これが mod $`J` で与えられた射になることは、両者が $`W(k)\to B/J` の mod $`p` で一致することと Witt 持ち上げの一意性から。*一意性*：$`A` が完全なので任意の $`a` は $`b^p+pc` と書ける。$`F\equiv G` mod $`(p,J)` なら、$`x\equiv y` mod $`\mathfrak a`（$`p\in\mathfrak a`）から $`x^p\equiv y^p` mod $`\mathfrak a\cdot(x-y)` となる幾何和の計算で、帰納的に $`F(a)-G(a)\in(p,J)^n` が全ての $`n` で成り立ち、$`(p,J)` 進分離性（命題 3.2.3 (1)）から $`F=G`。*δ 射であること*：$`B` は $`p` 進分離。$`\varphi_B\circ F` と $`F\circ\varphi_A` は mod $`p` で一致するので、同じ一意性の論法で等しい。二つの $`W_2` への射 $`w_B\circ F` と $`W_2(F)\circ w_A` は第 0 座標と ghost 成分が一致するので、第 1 座標の差は $`p` 倍で消える加法的な導分で、$`a=b^p+pc` の形から消える。原典の $`B^{\mathrm{perf}}` は使わない。零環の商（$`B/J=0`）は別に扱い、そのとき $`B=0`。

*「始対象」.* $`(R)_\Delta` の対象 $`(B,J)` と $`R\to B/J` に対し、射 $`(A,I)\to(B,J)` で mod の射が与えられたものはただ一つなので、各対象は $`A` の下に一意に置かれ、$`(R)_\Delta` と $`(R/A)_\Delta` が一致する（$`(R/A)_\Delta` の対象では $`J=IB` は剛性（命題 3.2.1）から自動）。

*命題 4.1.8（原典 Lemma 4.8：完全 prism からの射の一意な持ち上げ） — 原典との差（D5）*

原典の標的は任意の prism、Lean の標的は有界な向き付き prism（D5）。prismatic site の対象は有界なので site の議論にはこれで足りる。証明は原典の変形理論（$`L_{A/\mathbb Z_p}` の消滅）と $`B^{\mathrm{perf}}` ではなく、tilt の比較・Fontaine の $`\theta`・Witt 持ち上げの一意性と、$`p` 冪近似による直接の剛性・$`W_2` の比較による。変形理論と余接複体が要らず、δ 射の判定は $`p` ねじれのある標的にもそのまま効く。代わりに有界性（$`(p,J)` 進完備性）を全面的に使う。

:::

:::definition "bs_4_9"
*構成 4.9*　HT 比較の写像。対応表の状態：なし。

hodgeTateMap は多項式の reducedModel の cohomology への写像。原文の Rν\_\* O\_Δ に対する Bockstein・ηとの比較が未供給。一般の cup・de Rham 普遍性は証明部品で、同じ η の成分とは数えない。

*定義 4.2.1（原典 Construction 4.9） — 主張*

Construction 4.4 の $`\nu` を使って
$$`\Delta_{X/A}:=R\nu_*\mathcal O_\Delta\in D(X_{\mathrm{\acute et}},A),\qquad \overline\Delta_{X/A}:=R\nu_*\overline{\mathcal O}_\Delta\in D(X_{\mathrm{\acute et}},\mathcal O_X)`
と置く。これらはそれぞれの導来圏の可換代数対象で、$`\overline\Delta_{X/A}\simeq\Delta_{X/A}\otimes^L_AA/I` が成り立つ。$`A/I` 加群 M について $`M\{i\}:=M\otimes_{A/I}I^i/I^{i+1}` と書くと、三角形
$$`\overline\Delta_{X/A}\{i+1\}\to\Delta_{X/A}\otimes^L_AI^i/I^{i+2}\to\overline\Delta_{X/A}\{i\}`
から Bockstein 微分 $`\beta_I\colon H^i(\overline\Delta_{X/A})\{i\}\to H^{i+1}(\overline\Delta_{X/A})\{i+1\}` が得られる。i を動かすとこれらは次数付き環 $`H^*(\overline\Delta_{X/A})\{*\}` を dg $`A/I` 代数にし、その 0 次の項は $`\mathcal O_X` 代数である。構造写像を $`\eta^0_X\colon\mathcal O_X\to H^0(\overline\Delta_{X/A})` と書く。Kähler 微分の普遍性から、局所切断 $`f\,dg` を $`f\beta_I(g)` へ送る $`\mathcal O_X` 加群の写像 $`\eta^1_X\colon\Omega^1_{X/(A/I)}\to H^1(\overline\Delta_{X/A})\{1\}` が得られる。dg 代数 $`H^*(\overline\Delta_{X/A})\{*\}` は（topos の可換環対象のコホモロジーの一般論で）次数付き可換であり、さらに命題 4.2.2（Lemma 4.10）が成り立つので、de Rham 複体の普遍性により、微分と両立する次数付き $`\mathcal O_X` 加群の写像 $`\eta^0_X\oplus\eta^1_X\colon\mathcal O_X\oplus\Omega^1_{X/(A/I)}\to H^0(\overline\Delta_{X/A})\oplus H^1(\overline\Delta_{X/A})\{1\}` は、各項の $`\mathcal O_X` 加群の構造と両立する可換 dg 代数の写像
$$`\eta^*_X\colon\Omega^*_{X/(A/I)}\to H^*(\overline\Delta_{X/A})\{*\}`
に延びる。prism が distinguished な元 $`d\in I` で向き付けられていれば $`d^i` で $`A/I\simeq I^i/I^{i+1}` なので捻り $`\{i\}` は外せる（d = p のときは通常そうする）。

後のための注意：$`\eta^*_X` の構成は、可換代数対象 $`\Delta_{X/A}\in D(X_{\mathrm{\acute et}},A)` と $`\Delta_{X/A}\otimes^L_AA/I` の $`\mathcal O_X` 代数の構造の組について関手的である。

*定義 4.2.1（原典 Construction 4.9） — Lean*

多項式代数 $`R=(A/d)\langle X_1,\dots,X_r\rangle` の場合だけ本体にある（$`\overline\Delta` は上の模型、向きで捻りを外す）。

- *Bockstein の一般論*：余単体的環 $`C^\bullet` と各項で正則な d の短完全列 $`0\to C/d\to C/d^2\to C/d\to0`（係数は共通の基底環 k に固定した余単体的 k 加群として取る）が \`regularShortExact\`（PrincipalShortExact:161）、その連結写像が \`regularBockstein\`（:176）、平方零が \`bockstein\_sq\`（BocksteinClass:202）。加法的コホモロジーへ移したものが \`cupBockstein\`（Bockstein:69）とその平方零 \`cupBockstein\_sq\`（BocksteinClass:186）。模型の上の $`\beta` は \`bockstein\`（HodgeTateZero:42）。

- \*\*$`\eta^0` と $`\eta^1`\*\*：$`\eta^0` は環準同型 \`hodgeTateMapZero\`（HodgeTateZero:70）。$`g\mapsto\beta(\eta^0g)` は \`htBocksteinZero\`（HodgeTateZeroLeibniz:71）で、Leibniz 則 \`htBocksteinZero\_mul\`（:84）と、基底の剰余 $`A/d` の定数で零になること \`htBocksteinZero\_algebraMap\`（:104）を持つ。$`\eta^1` は完備一次形式の基底 $`dX_j` を $`\beta(X_j)` へ送る \`htOneOnGenerators\`（HodgeTateOneGenerators:64）として定め、\`hodgeTateMapOne\`（HodgeTateOneDerivative:215）と呼ぶ。原典の公式 $`f\,dg\mapsto f\beta(g)` は \`hodgeTateMapOne\_smul\_d\`（:219）。微分形式は p 完備多項式代数について $`dX_j` 上の自由加群として直接定義したもの \`affineForms\`（HodgeTateAffineForms:45、D26）。

- \*\*$`\eta^*` への延長\*\*：未完備の多項式 de Rham 代数の普遍性 \`SerrePositivity.DeRham.exists\_unique\_dgHom\`（UniversalProperty:449：次数 0 の環準同型と次数 1 の加法的写像が、線形性・$`\eta^1(df)=d\eta^0(f)`・$`\eta^1(\omega)^2=0` を満たせば、外積と微分を保つ写像に一意に延びる）を当て、係数の完備化への底変換で完備形式に移す。平方零の入力は \`hodgeTateMapOne\_square\_zero\`（HodgeTateOneSquare:89）。結果が \`hodgeTateMap\`（HodgeTateCompletedMap:398）で、その型 \`HTAlgebraMap\`（:388）は各次数の線形写像と、$`\eta^0`・$`\eta^1` との一致、外積と cup 積の両立、de Rham 微分と Bockstein の両立の組。一意性は \`hodgeTateMap\_unique\`（:408）。

- $`\Delta_{X/A}=R\nu_*\mathcal O_\Delta` と $`\overline\Delta_{X/A}\simeq\Delta_{X/A}\otimes^L_AA/I`、一般の X、および最後の関手性の注意は本体にない（模型と $`R\Gamma` の比較は §4.3 の Construction 4.18）。

*定義 4.2.1（原典 Construction 4.9） — 証明*

原典は構成の各段の確認を省いている。要点を補う（補った）。

(a) $`\overline\Delta_{X/A}\simeq\Delta_{X/A}\otimes^L_AA/I`：I は可逆な A 加群なので $`A/I=\mathrm{cone}(I\to A)` は完全 A 加群で、$`\otimes^L_AA/I` は $`R\nu_*` と交換する。各対象 $`(B,IB)` で IB は局所的に B の非零因子で生成されるので（Lemma 3.1）、$`\mathcal O_\Delta\otimes^L_AA/I\simeq\overline{\mathcal O}_\Delta`。

(b) 三角形：A 加群の完全列 $`0\to I^{i+1}/I^{i+2}\to I^i/I^{i+2}\to I^i/I^{i+1}\to0` に $`\Delta_{X/A}\otimes^L_A-` を施し、$`I^j/I^{j+1}` が可逆 $`A/I` 加群であることから $`\Delta_{X/A}\otimes^L_AI^j/I^{j+1}\simeq\overline\Delta_{X/A}\{j\}`。$`\beta_I` はこの三角形の連結写像。

(c) dg 代数：$`\beta_I\circ\beta_I=0` は、二つの連結写像の合成が $`\Delta\otimes^LI^i/I^{i+3}` のフィルトレーションの三角形から零になること。Leibniz 則は可換代数対象の平方零拡大 $`\Delta\otimes^LA/I^2\to\overline\Delta` に付随する Bockstein の一般的性質（模型では、正則な持ち上げで余鎖を計算すればよい）。

(d) $`\eta^1`：$`g\mapsto\beta_I(\eta^0g)` は Leibniz 則から $`\mathcal O_X` から $`H^1\{1\}` への導分で、$`A/I` の定数は $`A/I^2` へ持ち上がるので零になる。よって $`A/I` 上の導分で、Kähler 微分の普遍性（p 進完備な意味。値の $`H^1` は導来 p 完備）から $`\eta^1` が出る。

(e) $`\eta^*` への延長：$`\Omega^*_{X/(A/I)}` は「$`\mathcal O_X` 代数の写像 $`\eta^0` と、$`\eta^1(dg)=\beta\eta^0(g)` を満たす $`\eta^1` が与えられ、$`\eta^1` の像の平方が零」という条件のもとで可換 dg 代数への写像が一意に延びる対象である。次数付き可換性だけからは $`x^2=-x^2`、つまり $`2x^2=0` しか出ないので、平方零を命題 4.2.2 で補う。一次形式は局所的に $`\sum f_j\,dg_j` と書け、交差項は次数付き可換性で消えるので、$`\beta(g)^2=0` から $`\eta^1(\omega)^2=0` が出る。

(f) 捻りの除去：$`d^i` が $`I^i/I^{i+1}` の生成元なので $`M\{i\}\cong M`。

*定義 4.2.1（原典 Construction 4.9） — 原典との差（D26・D27）*

D26：原典の $`\Omega^1_{X/(A/I)}` は p 進形式スキームの（連続な）Kähler 微分。本体は p 完備多項式代数について $`dX_j` 上の自由加群として直接定義する。D27：原典の $`H^*(\overline\Delta_{X/A})` の環構造は topos の可換環対象のコホモロジーの環。本体は Čech–Alexander 模型の cup 積と Bockstein で与え、CAlg 値の $`\Delta` との一致は別の一般論に置く（D27 の評価は第 6 章の定理 6.1.3 の下）。また本体は $`\eta^*` の存在を、Kähler 微分の普遍性ではなく未完備の多項式 de Rham 代数の普遍性と完備化への底変換で示す。

宣言：`SerrePositivity.BhattScholze.Prismatic.hodgeTateMap`、`SerrePositivity.Cosimplicial.cohomologyCup_comm`、`SerrePositivity.DeRham.exists_unique_dgHom`

:::

:::lemma_ "bs_4_10"
*補題 4.10*　HT 写像の性質。対応表の状態：なし。

bockstein\_sq\_zero は同じ多項式 reducedModel 上の BetaSquareZero を証明するが、site Δ̄ とその β の同定を含まない。模型の定理を原文の局所切断にそのまま適用しない。

*命題 4.2.2（原典 Lemma 4.10） — 主張*

任意の局所切断 $`f\in\mathcal O_X(U)` について、f の $`H^0(\overline\Delta_{X/A})(U)` での像の微分 $`\beta_I(f)\in H^1(\overline\Delta_{X/A})\{1\}(U)` は平方が零である。

*命題 4.2.2（原典 Lemma 4.10） — Lean*

多項式代数の場合：述語 \`BetaSquareZero\`（HodgeTateBocksteinSquare:60、$`\beta(\eta^0f)` の cup 平方が零）と \`bockstein\_sq\_zero\`（:65）。p = 2 の場合の一般論は \`delta\_cochainDifferential\_eq\_cup\_sq\`・\`cupBockstein\_cup\_sq\_two\`（BocksteinCupSquare:67・99）、奇素数では \`SerrePositivity.Cosimplicial.cohomologyCup\_comm\`（CupCommutativity:846）。原典どおり Prop 6.2 から導く形 \`bockstein\_sq\_zero'\` は drafts（drafts/A1/HodgeTateComparison:358）。

*命題 4.2.2（原典 Lemma 4.10） — 証明*

*原典*：p が奇数なら自明（次数付き可換性で $`2\beta(f)^2=0`、2 は p 完備な環で単元）。p = 2 でだけ非自明で、Prop 6.2 から出るとして証明は後回しにする。Prop 6.2 からの導き方は（補った）：f は局所的に $`X\mapsto f` で定まる射 $`U\to\widehat{\mathbb A}^1_{A/I}` から来るので、関手性（Bockstein と cup 積の自然性）により $`\beta(f)^2` は $`\beta(X)^2\in H^2(\overline\Delta_{\mathbb A^1/A})\{2\}` の引き戻し。Prop 6.2 で $`H^2(\overline\Delta_{\mathbb A^1/A})\cong\Omega^2_{\mathbb A^1}=0`。

*本体の証明*（HT 比較を使わない）：模型の上で直接示す。p = 2 のとき、f の持ち上げ $`x\in C^0` をとると $`\partial x=d\,y` となる $`y\in C^1` があり、d が正則なので y は整係数の 1 余輪体で、$`\beta(f)` は y の類。1 余輪体 y について、余面 $`a=\delta^0y,\ b=\delta^1y,\ c=\delta^2y` は $`b=a+c` を満たし、p = 2 の δ 環で $`\delta(a+c)=\delta(a)+\delta(c)-ac` だから $`\partial(\delta y)=\delta(a)-\delta(b)+\delta(c)=ac=y\cup y`。よって $`y\cup y` は余境界で、d で割っても零。p が奇数のときは $`x\cup x=-x\cup x` と、2 が p 完備な $`R` で単元であることから。

*命題 4.2.2（原典 Lemma 4.10） — 原典との差*

原典は Lemma 4.10 を Prop 6.2（affine 直線の HT 比較）から導く。本体は Čech–Alexander 模型の上で直接示す（p = 2 は $`\delta` による余境界、奇素数は次数付き可換性）。HT 比較を先に要しないので、$`\eta^*` の構成が §6 の帰着に依存しない。主張は多項式代数の場合に限る。

宣言：`SerrePositivity.BhattScholze.Prismatic.bockstein_sq_zero`

:::

:::theorem "bs_4_11"
*定理 4.11*　HT 比較。対応表の状態：なし。

一般比較は drafts。本体は模型の写像と同型述語、および結晶基底での模型上の同型。site Δ̄ の ηとの比較がないため原文の同型の partial とはしない。

*定理 4.2.3（原典 Thm 4.11） — 主張*

（Hodge–Tate 比較）上で構成した写像 $`\eta^*_X\colon\Omega^*_{X/(A/I)}\to H^*(\overline\Delta_{X/A})\{*\}` は dg $`A/I` 代数の同型である。特に $`\overline\Delta_{X/A}\in D(X_{\mathrm{\acute et}},\mathcal O_X)` は完全複体で、$`H^i(\overline\Delta_{X/A})\cong\Omega^i_{X/(A/I)}\{-i\}`。

*定理 4.2.3（原典 Thm 4.11） — Lean*

主張の型は多項式代数の場合の \`HodgeTateIsoStatement\`（HodgeTateCompletedMap:461）：\`hodgeTateMap\` が全次数で全単射であること。原典の「dg 代数の同型」は、写像が dg 代数の射であること（\`HTAlgebraMap\` の組）と各次数の全単射性に分けて述べている。$`\overline\Delta` が完全複体であることは主張していない。

*本体で証明済みの場合*：結晶基底 $`(\mathbb Z_p,(p))`（\`crystallineBasePrism\`（CrystallineBase:83）、有界性 \`crystallineBaseBounded\`（:98））で、$`A/I=\mathbb F_p`、$`R=\mathbb F_p[X_1,\dots,X_r]`。\`hodgeTate\_of\_deRham\_cartier\`（HodgeTateCartierAssembly:180）と、原典 Cor 5.5 の名で呼ぶ \`hodgeTate\_iso\_polynomial\_Zp\`（:212）。証明は、模型のコホモロジーから多項式 de Rham コホモロジーへの加法同型 \`crystallineChain\`（CrystallineChain:39）、inverse Cartier 同型 \`finitePolynomialCartier\`（FinitePolynomialCartier:46）、完備形式と通常の形式の同一視 \`cartierFormsIso\`（CartierCompletedForms:76）を合成したものが $`\eta^*` に一致することを、cup 積との両立 \`crystallineChain\_cup\`（CrystallineChainProduct:54）と生成元 $`X_j`・$`dX_j` での一致 \`crystallineChain\_generators\`（CrystallineGeneratorClasses:83）から示す（詳細は第 5 章）。

一般の有界向き付き基底の多項式代数の場合 \`hodgeTate\_iso\` は drafts（drafts/A1/HodgeTateComparison:350）。一般の X は本体にない。

*定理 4.2.3（原典 Thm 4.11） — 証明*

原典はここでは証明せず、§5 で標数 p の場合（$`p\in I`、結晶比較 Thm 5.2 と Cartier 同型から Cor 5.5）、§6 で一般の場合（Construction 6.1 の図式で $`\mathbb F_p[X]/\mathbb Z_p` に帰着する Prop 6.2、étale 局所化で多項式代数に帰着する Thm 6.3）を示す。第 5 章（標数 p）と第 6 章（一般の場合）を見よ。

*定理 4.2.3（原典 Thm 4.11） — 原典との差（D27・D29）*

D27：$`H^*(\overline\Delta)` とその環構造は Čech–Alexander 模型の上で述べる。D29：原典は Prop 6.2（r = 1）から Lemma 4.21 で一般へ進むが、本体の主張は最初から一般の r の多項式代数で、定理の範囲を多項式代数に絞る。

宣言：`SerrePositivity.BhattScholze.Prismatic.HodgeTateIsoStatement`、`SerrePositivity.BhattScholze.Prismatic.hodgeTate_iso_polynomial_Zp`、`hodgeTate_iso`、`SerrePositivity.BhattScholze.Prismatic.hodgeTate_of_deRham_cartier`

:::

:::corollary "bs_4_12"
*系 4.12*　底変換。対応表の状態：なし。

同じ site prismatic cohomology の底変換同型は drafts。項ごとの envelope 底変換と Tot の交換・site 比較の組み立ては未供給。

*系 4.2.4（原典 Cor 4.12） — 主張*

$`\Delta_{X/A}\in D(X_{\mathrm{\acute et}},A)` の形成は有界 prism の射 $`(A,I)\to(B,IB)` に沿う底変換と可換である。すなわち $`g\colon X_B:=X\times_{\mathrm{Spf}(A/I)}\mathrm{Spf}(B/IB)\to X` を射影とすると $`(g^*\Delta_{X/A})^\wedge\cong\Delta_{X_B/B}`。ここで $`(-)^\wedge` は導来 $`(p,I)` 完備化。

*系 4.2.4（原典 Cor 4.12） — Lean*

本体にない。drafts に多項式代数の場合 \`prismaticCohomology\_baseChange'\`（drafts/A1/HodgeTateComparison:365）と主張の型 \`PrismaticCohomologyBaseChangeStatement\`（drafts/A1/HodgeTateMap:87）：向き付き prism の射 $`P\to P'` について、係数を延長して $`P'` で完備化した CAlg 値の $`\Delta` から $`P'` 上の $`\Delta` への比較の辺が同型であること。Tor 振幅の仮定つきの底変換は §4.3 の Lemma 4.20。

*系 4.2.4（原典 Cor 4.12） — 証明*

比較写像は、$`(X_B/B)_\Delta` の対象を $`X_B\to X` との合成で $`(X/A)_\Delta` の対象とみなす関手から得る $`g^*\Delta_{X/A}\to\Delta_{X_B/B}` を完備化したもの。両辺は導来 $`(p,I)` 完備なので、導来 Nakayama（\[Sta, Tag 0G1U\]）により mod I で同型を示せば足りる。定義 4.2.1 の証明の (a) により mod I の主張は $`(g^*\overline\Delta_{X/A})^\wedge\cong\overline\Delta_{X_B/B}`（完備化は導来 p 完備化）。これは HT 比較と、微分形式 $`\Omega^*` が底変換と可換であることから出る。

省かれた点の要点（補った）：Thm 4.11 により $`\overline\Delta_{X/A}` は有限の Postnikov フィルトレーションを持ち、その次数部分 $`\Omega^i_{X/(A/I)}\{-i\}[-i]` は局所自由 $`\mathcal O_X` 加群。$`g^*` と p 完備化はこれらの三角形を保ち、局所自由加群の p 完備な底変換は $`\Omega^i_{X_B/(B/IB)}\{-i\}` を与える。比較写像は Construction 4.9 の関手性で $`\eta^*` と両立するので、各次数部分で同型。

宣言：`prismaticCohomology_baseChange'`、`PrismaticCohomologyBaseChangeStatement`

:::

:::proposition "bs_4_13"
*注意 4.13*　Higgs 特殊化。対応表の状態：なし。

持ち上げ X̃ と Frobenius に依存する Higgs specialization および構造写像の分裂を未同定。

*注意 4.2.5（原典 Rem 4.13） — 主張*

（Higgs 特殊化）A は p ねじれなしとする。X が、Frobenius の両立する持ち上げを備えた $`(p,I)` 完全平坦な $`(p,I)` 進形式スキーム $`\mathfrak X/A` に持ち上がるとする。このとき $`\mathfrak X_{\mathrm{\acute et}}\simeq X_{\mathrm{\acute et}}` の affine は $`(X/A)_\Delta` の対象を自然に与える：affine $`\mathfrak U\to\mathfrak X` ごとに図式 $`(\mathfrak U\leftarrow\mathfrak U\times_AA/I\to X)` が $`(X/A)_\Delta` の対象。大域切断をとると $`X_{\mathrm{\acute et}}` 上の $`E_\infty` A 代数の $`\varphi` 同変な写像 $`\Delta_{X/A}\to\mathcal O_{\mathfrak X}` を得る。mod I をとると、構造写像 $`\mathcal O_X\to\overline\Delta_{X/A}` を分裂させる $`E_\infty` $`A/I` 代数の写像 $`\overline\Delta_{X/A}\to\mathcal O_X` が定まる。これを Higgs 特殊化と呼び、$`\mathfrak X`（その δ 構造を含む）の選び方に依存する。

（脚注 9）用語の理由：$`(X/A)_\Delta` 上の導来 p 完備な $`\mathcal O_\Delta` 複体の crystal の ∞ 圏は（層化した大域切断で）$`D_{p\text{-comp}}(X,\Delta_{X/A})` と同値であり、Higgs 特殊化に沿う底変換で、相対余接束の 0 切断での形式完備化 $`\widehat{T^*X}` 上の準連接層の ∞ 圏と同値になることが示せる。こうして crystal に X 上の位相的冪零な Higgs 場が対応する。原典はこれを証明しない。

*注意 4.2.5（原典 Rem 4.13） — 証明*

原典は確認を省いている（補った）。$`\mathfrak U=\mathrm{Spf}\,C` とすると、A が p ねじれなしで C が $`(p,I)` 完全平坦なので C も p ねじれなし（$`C[p]` は導来 I 完備で、$`C\otimes^L_AA/(p,I)` が離散であることから $`C[p]=I\,C[p]`、導来 Nakayama で零）。よって Frobenius の持ち上げは C の δ 構造を定め（Rem 2.2）、$`(C,IC)` は $`(A,I)` 上の prism で、有界性も完全平坦性から出る。よって $`(\mathfrak U\leftarrow\mathfrak U\times_AA/I\to X)` は site の対象で、$`\mathcal O_\Delta` のこの対象での値は C。大域切断からこの値への評価が $`\Delta_{X/A}(U)\to C` を与え、étale 局所的に貼り合う。mod I では $`\overline{\mathcal O}_\Delta` の値は $`C/IC=\mathcal O_X(U)` で、$`U=\mathfrak U\times_AA/I` は X の étale な affine で $`C/IC=\mathcal O_X(U)` だから、合成 $`\mathcal O_X(U)\to\overline\Delta_{X/A}(U)\to C/IC` はこの対象の構造射、つまり恒等で、分裂が得られる。

:::

:::proposition "bs_4_14"
*注意 4.14*　\\(A/I\^2\\) への持ち上げの障害。対応表の状態：なし。

τ≤1 Δ̄ の分裂 iff A/I² への持ち上げという同じ障害比較を未同定。

*注意 4.2.6（原典 Rem 4.14） — 主張*

（mod $`I^2` への持ち上げの障害）写像 $`\mathcal O_X\to\tau^{\le1}\overline\Delta_{X/A}` が $`\mathcal O_X` 加群の写像として分裂することと、X が $`A/I^2` に持ち上がることは同値である（余接複体はすべて p 完備な意味）。

*注意 4.2.6（原典 Rem 4.14） — 証明*

*原典*：非零因子による環の商の余接複体の一般的性質から、X の $`A/I^2` への持ち上げは $`L_{X/A}\to L_{X/(A/I)}` の分裂と同値。あとは命題 4.2.7（Prop 4.15）から出る。

*補った点*：$`A\to A/I\to X` の推移三角形は $`L_{(A/I)/A}=I/I^2[1]` と X の smooth 性から $`\mathcal O_X\{1\}[1]\to L_{X/A}\to\Omega^1_{X/(A/I)}` となる。命題 4.2.7 の同型 $`L_{X/A}\simeq\tau^{\le1}\overline\Delta_{X/A}\{1\}[1]` で捻りとずらしを戻すと、この三角形は $`\mathcal O_X\to\tau^{\le1}\overline\Delta_{X/A}\to\Omega^1_{X/(A/I)}\{-1\}[-1]` に移る（$`H^{-1}` の上で両者の写像が一致することは命題 4.2.7 の証明の中の比較）。三角形の分裂は第一の写像の分裂とも第二の写像の分裂とも同値なので、主張が出る。

:::

:::proposition "bs_4_15"
*命題 4.15*　余接複体と \\(\\tau\^\{\\le 1\}\\overline\{\\Delta\}\\)。対応表の状態：なし。

同じ cotangent complex LX/A と τ≤1 Δ̄\{1\}\[1\] の自然同型を未同定。HT 模型の結果だけではこの指定比較を得ない。

*命題 4.2.7（原典 Prop 4.15） — 主張*

自然な同型 $`L_{X/A}\simeq\tau^{\le1}\overline\Delta_{X/A}\{1\}[1]` がある。

*命題 4.2.7（原典 Prop 4.15） — 証明*

（原典は証明の概略）*写像の構成*：$`X=\mathrm{Spf}\,R` が affine のとき（Not 4.16 にならって環で書く）、∞ 圏 $`D(R)` の自然な写像 $`\eta_R\colon L_{R/A}\to\overline\Delta_{R/A}\{1\}[1]` を作る。$`(R/A)_\Delta` の各対象 $`(R\to B/IB\leftarrow B)` について自然な写像
$$`L_{R/A}\to L_{(B/IB)/B}\simeq I/I^2\otimes^L_{A/I}B/IB[1]\simeq B/IB\{1\}[1]`
がある（$`A\to R\to B/IB` と $`A\to B\to B/IB` の関手性、IB は局所的に非零因子で生成される）。$`(R/A)_\Delta` 上の導来大域切断をとって $`\eta_R`。両辺は $`D_{\mathrm{perf}}(X)` にあるので（右辺は Thm 4.11）、affine 開集合全体の極限で大域化して $`L_{X/A}\to\overline\Delta_{X/A}\{1\}[1]` を得る。$`L_{X/A}\in D^{\le0}` なので、これは $`\tau^{\le0}(\overline\Delta_{X/A}\{1\}[1])\simeq\tau^{\le1}\overline\Delta_{X/A}\{1\}[1]` を経由し、写像 $`\mu` を得る。

*同型であること*：両辺のコホモロジー層は抽象的に同型で、次数 −1 に $`\mathcal O_X\{1\}`、次数 0 に $`\Omega^1_{X/A}`（左辺は推移三角形、右辺は Thm 4.11）。両辺と $`\mu` の形成は p 完備な底変換と可換（右辺は Cor 4.12）なので、$`I=(p)` の場合に帰着する。Thm 4.11 により、$`i=0,1` の $`H^i(\mu)` が Thm 4.11 の写像を作った Construction 4.9 の写像と一致することを示せば足りる。この両立は $`X=\mathbb A^1` に帰着し、構成の底変換との両立で $`A=\mathbb Z_p` としてよい。この場合の確認を原典は読者に任せる（完全な証明は \[ALB19b, Proposition 3.2.1\]）。

（原典の続く段落）$`I=(p)` の場合は、de Rham 比較（Thm 15.4）を通じて \[DI87, Theorem 3.5\] と近い。$`A_{\mathrm{inf}}` コホモロジーでの類似は \[BMS18, §8.2\]、特異な場合の類似は Rem 15.6、結晶の場合への一般化と応用は \[Ill21a, Ill21b\]。

:::

:::definition "bs_4_16"
*記法 4.16*　\\(\\Delta\_\{R/A\}\\) の定義（site の RΓ）。対応表の状態：なし。

site の RΓ としての prismaticCohomology・hodgeTateCohomology は drafts。模型の同名 cohomology と正本を区別する。

*定義 4.3.1（原典 Notation 4.16：affine の場合の記号と $`\Delta_{R/A}`） — 主張*

$`(A,I)` を有界 prism、$`X` を滑らかな $`p` 進形式 $`A/I` スキームとする。$`X=\mathrm{Spf}(R)` が affine のとき $`(\mathrm{Spf}(R)/A)_\Delta` を $`(R/A)_\Delta` とも書き、その典型的な対象を図式 $`(B\to B/IB\leftarrow R)`（$`(B,IB)` は $`(A,I)` 上の prism）とみる。対象をスキームではなく環で見るときは、$`(R/A)_\Delta` の圏論的性質も代数の言葉で述べる。たとえば $`R=A/I` なら $`(A\to A/I\leftarrow A/I=R)\in(R/A)_\Delta` を終対象ではなく*始対象*と呼ぶ（原典は「$`A=R/I`」と誤植）。この affine の状況で

$$`\Delta_{R/A}:=R\Gamma(\mathrm{Spec}(R),\Delta_{\mathrm{Spec}(R)/A}),\qquad \overline\Delta_{R/A}:=\Delta_{R/A}\otimes^L_AA/I`

とおく。ここで $`\Delta_{X/A}=R\nu_*\mathcal O_\Delta`（§4.2）なので、$`\Delta_{R/A}=R\Gamma((R/A)_\Delta,\mathcal O_\Delta)\in D(A)`。

*定義 4.3.1（原典 Notation 4.16：affine の場合の記号と $`\Delta_{R/A}`） — Lean*

本体にない（drafts）。$`\Delta_{R/A}` は \`prismaticCohomology\`（drafts/A0/PrismaticSite.lean:179）：site の小さい模型の上の $`D(A)` 値前層 \`structurePresheafDerived\`（:171。$`B` を離散な $`A` 加群として $`D(A)` に入れる）に、∞ 層の \`derivedGlobalSections\`（層化してから大域切断 $`=` site 上の極限）を当てたもの。層化のデータと $`D(A)` の presentable 性は仮定として受け取る。$`\overline\Delta_{R/A}` は \`hodgeTateCohomology\`（:190）。

限り方：$`X` は affine だけで、$`R` は任意の $`A/d` 代数（滑らかさは定義に入らない）。site は濃度 $`\le\kappa` の対象 \`PrismOver\`（PrismOver:68）に切り落とした小さい圏（D16）。$`\kappa` によらないことは、Čech–Alexander 模型の存在を仮定した形で drafts の \`prismaticCohomology\_cutoff\_invariant\`（drafts/A0/CechAlexander.lean:234）。

*定義 4.3.1（原典 Notation 4.16：affine の場合の記号と $`\Delta_{R/A}`） — 原典との差（D17・D18）*

$`R\Gamma` は古典的な層係数コホモロジーではなく、Čech 層（被覆篩に沿う降下）としての層化と極限で定義する（D17）。$`\mathcal O_\Delta` は離散な層なので両者は一致する。値はまず $`D(A)` の対象で、可換代数対象としての構造（原典 Construction 7.6）は別に作って結ぶ（D18）。

宣言：`prismaticCohomology`、`hodgeTateCohomology`、`prismaticCohomologyFrobenius`、`prismaticCohomology_cutoff_invariant`

:::

:::definition "bs_4_17" (lean := "SerrePositivity.BhattScholze.Prismatic.cechAlexanderObj_weaklyInitial, SerrePositivity.BhattScholze.Prismatic.cechAlexanderObj, SerrePositivity.BhattScholze.Prismatic.cechSmall_weaklyTerminal, SerrePositivity.BhattScholze.Prismatic.cechAlexanderAffine_weaklyInitial, SerrePositivity.BhattScholze.Prismatic.cechAlexanderComplex, SerrePositivity.BhattScholze.Prismatic.cechAlexander_isCoproduct")
*構成 4.17*　弱始対象。対応表の状態：一部（stronger-hyp）。

*主張*　$`p` 完全滑らかな $`A/I` 代数 $`R` に、導来完備な多項式 $`A` 代数 $`B_0` からの全射を選ぶ。$`B_0` 上の自由 $`\delta` 代数を完備化し、全射の核から誘導されるイデアルに prismatic 包絡をとると、$`R/A` の prism の圏の任意の対象へ射をもつ対象を得る。この構成は $`B_0` に関手的で、そのテンソル積を prism の余積に送る。

HasEnvelopes と admissible cutoff を追加すれば、同じ site の C⁰ の弱始性と Cⁿ の標準余積・関手性を直接得る。envelope の存在の供給は変数の場合に限られ、任意 smooth R の入力を無条件とはしない。

*命題 4.3.2（原典 Construction 4.17：弱始対象） — 主張*

$`R` を $`p` 完全に滑らかな $`A/I` 代数とする。$`B_0\to R` を $`A` 代数の全射で、$`B_0` は多項式 $`A` 代数の導来 $`(p,I)` 完備化とする。$`B=\mathrm{Free}_{\delta,A}(B_0)^\wedge` を自由 δ-$`A` 代数の導来 $`(p,I)` 完備化とする（$`A` が有界なので、原典 Lemma 3.7 により古典的な完備化でもよい）。$`J_0=\ker(B_0\to R)` とおく。$`B_0\to B` は $`B` を多項式 $`B_0` 代数の導来 $`(p,I)` 完備化として表すので、$`R\to R':=(B/J_0B)^\wedge`（$`p` 進完備化）も同じ形であり、$`R'` は $`A/I` 上 $`p` 完全に ind-滑らか、$`\ker(B\to R')` は $`J_0` が生成する導来 $`(p,I)` 完備なイデアル。対 $`(B,\ker(B\to R'))` に Prop 3.13（命題 3.5.1、例 3.5.2 も参照）を当てると対象 $`(C\to C/IC\leftarrow R)\in(R/A)_\Delta` が得られ、可換図式

$$`\begin{array}{ccccccc} A &\to& B_0 &\to& B=\mathrm{Free}_{\delta,A}(B_0)^\wedge &\to& C\\ \downarrow && \downarrow && \downarrow && \downarrow\\ A/I &\to& R &\to& R' &\to& C/IC \end{array}`

（中央の四角は導来 $`(p,I)` 完備な $`A` 代数の押し出し）に収まる。このとき

1. $`(C\to C/IC\leftarrow R)` は $`(R/A)_\Delta` の*弱始対象*：任意の対象へ射を持つ。

2. 全射 $`(B_0\to R)` から $`(C\to C/IC\leftarrow R)` を作る構成は $`B_0` について関手的で、$`B_0` の（完備）テンソル積を $`(R/A)_\Delta` の余積に送る。

*命題 4.3.2（原典 Construction 4.17：弱始対象） — Lean*

envelope の存在は仮定 \`HasEnvelopes\`（:90）にまとめる（各次数で envelope が存在し、有界で、濃度が既定の cutoff 以下）。その下で、各項 \`cechAlexanderObj\`（CechAlexanderAssembly:61）、(1) の弱始性 \`cechAlexanderObj\_weaklyInitial\`（:72）、(2) を Čech 脈体に要る形に限った「$`n` 次の項は頂点の包含 $`[0]\to[n]` を脚として零次の項の $`n+1` 個の余積」\`cechAlexander\_isCoproduct\`（:79）。余積の一般の組み立ては \`CechAlexanderPresentation.isCoproduct\`（CechAlexanderCoproduct:49）。

\`HasEnvelopes\` を実際に満たすのは有限変数の完備多項式 $`R=(A/d)\langle X_1,\dots,X_r\rangle` の場合で、\`hasEnvelopes\_of\_finitePolynomial\`（BigCechSiteAffine:43）。一般の $`R` での envelope の存在は主張しない。$`B_0` についての一般の関手性は述べず、単体射から来る添字の写像についての関手性だけを使う（命題 4.3.3）。

*命題 4.3.2（原典 Construction 4.17：弱始対象） — 証明*

*弱始性.* 対象 $`(D\to D/ID\leftarrow R)` を一つ取る。$`B_0` は多項式 $`A` 代数の導来 $`(p,I)` 完備化で $`D` は導来 $`(p,I)` 完備なので、$`A/I` 代数の射 $`R\to D/ID` を持ち上げる $`A` 代数の射 $`B_0\to D` が選べる（各変数の像を $`D\to D/ID` で持ち上げる）。$`D` は δ-$`A` 代数なので、この選択は δ-$`A` 代数の射 $`B\to D` に一意に延びる（自由性と完備化の普遍性、命題 2.2.3（原典 Lemma 2.17））。構成から $`B_0\to D\to D/ID` は $`B_0\to R\to D/ID` に等しいので $`J_0` は $`ID` に入り、$`ID` は導来 $`(p,I)` 完備なので（$`D/ID` が $`p` 完備で有界）$`J_0` が生成する導来完備なイデアル $`\ker(B\to R')` も $`ID` に入る（補った）。envelope $`C` の普遍性から δ-$`A` 代数の分解 $`B\to C\to D` が一意にある。最後に $`R\to C/IC\to D/ID` が与えられた $`R\to D/ID` に一致することは、合成 $`B_0\to B\to C\to D` が最初に選んだ射で、全射 $`B_0\to R` と $`D\to D/ID` のもとで与えられた射と両立していたことから従う。

*余積.*（補った）二つの全射 $`B_0\to R`、$`B_0'\to R` から全射 $`B_0\widehat\otimes_AB_0'\to R` を作る。剛性（命題 3.2.1）により $`(R/A)_\Delta` の射は $`R` と両立する δ-$`A` 代数の射なので、$`C(B_0\widehat\otimes_AB_0')` から $`D` への射は、$`B_0\widehat\otimes_AB_0'\to D` で $`R\to D/ID` を持ち上げるもの、すなわち $`B_0\to D` と $`B_0'\to D` の持ち上げの組と一対一（$`B` の自由性と $`C` の普遍性を順に使う）。後者は $`C(B_0)\to D` と $`C(B_0')\to D` の組と一対一なので、$`C(B_0\widehat\otimes_AB_0')` は余積。

Lean では各変数の像を、標的の剰余への全射で持ち上げて弱始性を示す（変数の添字が $`R` の元そのものなので、変数の行き先は $`R\to D/ID` の像の持ち上げとして選べる）。

*命題 4.3.2（原典 Construction 4.17：弱始対象） — 原典との差（D21）*

envelope の存在は一般の $`p` 完全に滑らかな $`R` では示さず、仮定 \`HasEnvelopes\` に置く。それを満たすのは有限変数の完備多項式の場合で、そのとき envelope は（変数変換で）完備自由 δ 代数そのもの（D21、評価は命題 3.5.1 の囲み）。

:::

:::definition "bs_4_18"
*構成 4.18*　Čech–Alexander 複体。対応表の状態：なし。

big/small Čech 項・site 対象の同型と模型間の quasiIso は本体にあるが、原文の核心 C•≃RΓ の比較は drafts。構成に使う部品だけでは Δ を計算する主張の partial としない。

*命題 4.3.3（原典 Construction 4.18：Čech–Alexander 複体） — 主張*

$`R` を $`p` 完全に滑らかな $`A/I` 代数、$`B_0\to R` を命題 4.3.2 のとおりとし、$`B_0^\bullet` を $`A\to B_0` の導来 $`(p,I)` 完備な Čech 脈体とする。全射の余単体的対象 $`(B_0^\bullet\to R)` に命題 4.3.2 を当てると、余単体的対象 $`(C^\bullet\to C^\bullet/IC^\bullet\leftarrow R)\in(R/A)_\Delta` が得られる。これは $`(C^0\to C^0/IC^0\leftarrow R)` の Čech 脈体であり、$`C^\bullet`（resp. $`C^\bullet/IC^\bullet`）は $`\Delta_{R/A}`（resp. $`\overline\Delta_{R/A}`）を計算する。

入力の全射 $`B_0\to R` は $`R` について関手的に選べる（たとえば $`B_0` を集合 $`R` 上の多項式 $`A` 代数の $`(p,I)` 完備化とする）。この選び方で $`\Delta_{R/A}` を計算する厳密に関手的な複体 $`C^\bullet((R/A)_\Delta,\mathcal O_\Delta)` が得られる。ただしこの複体は prism $`(A,I)` の底変換とは可換でない（$`B_0` の選び方が底変換と両立しない）。

（原典脚注 10）topos $`\mathcal X`、アーベル群の層 $`\mathcal A`、Čech 脈体 $`X_0^\bullet` を持つ弱終対象 $`X_0\in\mathcal X` について、自然な射は同型 $`R\Gamma(\mathcal X,\mathcal A)\simeq R\lim R\Gamma(X_0^\bullet,\mathcal A)` を与える。したがって $`\mathcal A` が各 $`X_0^i` で高次コホモロジーを持たなければ、$`R\Gamma(\mathcal X,\mathcal A)` は余単体的対象 $`\mathcal A(X_0^\bullet)` で計算される。

*命題 4.3.3（原典 Construction 4.18：Čech–Alexander 複体） — Lean*

*選んだ模型.* \`HasEnvelopes\` の下で、site の余単体的対象 \`cechAlexander\`（CechAlexanderAssembly:66。単体射を変数の添字の写像として一意に延ばす）、大きい site の Čech データ \`cechAlexanderNerve\`（:89）。本質的小ささを仮定した小さい site への移送 \`cechNerveData\`（CechAlexanderSmall:47）と、反対圏での弱終性 \`cechSmall\_weaklyTerminal\`（:56）。$`A` 加群の交代余面複体（正規化しない）\`cechAlexanderComplex\` と各項を $`d` で割った複体 \`cechAlexanderReducedComplex\`（CechAlexanderComplex:53・60）。

*厳密に関手的な模型.* 完備多項式環 $`Q` の全元を各頂点の変数に取る模型 \`bigCechAlexander\`（BigCechAffineEnvelope:420）。添字 \`BigCechIndex\`（BigCechAlexander:40）、変数の評価 \`bigCechEval\`（:45）、各項の envelope \`affineBigCechTerm\`（BigCechAffineEnvelope:404、有界性 :411）。多項式代入を完備化して添字に作用させるので、$`A/d` 上の有限変数多項式代数の圏 Poly($`A/d`) から余単体的 $`A` 代数への関手になる。site 上の版 \`bigCechSiteAlexander\`（BigCechSiteAlexander:35）と選んだ模型の、全単体射に自然な同型 \`cechAlexanderBigSiteIso\`（CechAlexanderBigComparison:62）、複体の同型 \`cechAlexanderBigComplexIso\`（:71）。

\*\*$`\Delta` を計算すること.\*\* 本体にない（drafts）。脚注 10 の ∞ 圏版「$`\mathcal O_\Delta` 上の錐が極限錐 ⇔ Čech 脈体への制限が極限錐」\`cechAlexander\_isLimitCone\_iff\`（drafts/A0/CechAlexander.lean:212）、$`\Delta_{R/A}` と Tot の一致 \`prismaticCohomology\_eq\_cechAlexanderTot\`（:221）。交代余面複体が $`D(A)` の Tot を表すことは、ここに挙げた宣言には含まれない。

*命題 4.3.3（原典 Construction 4.18：Čech–Alexander 複体） — 証明*

*Čech 脈体であること.* $`B_0^n=B_0^{\widehat\otimes(n+1)}` で、命題 4.3.2 (2) により $`C^n` は $`C^0` の $`n+1` 個の余積、脚は頂点の包含 $`[0]\to[n]` から来る射。余単体的構造も余積の普遍性で決まるので、$`C^\bullet` は $`C^0` の（環の向きでの）Čech 脈体、site（反対圏）では弱終対象 $`C^0` の Čech 脈体。

\*\*$`\Delta` を計算すること.\*\* $`C^0` は弱始（site では弱終）なので脚注 10 から $`R\Gamma((R/A)_\Delta,\mathcal O_\Delta)\simeq R\lim_n R\Gamma(C^n,\mathcal O_\Delta)`。Cor 3.12（系 3.4.3）から $`\mathcal O_\Delta` は各対象上で高次コホモロジーを持たないので $`R\Gamma(C^n,\mathcal O_\Delta)=C^n`、よって $`\Delta_{R/A}\simeq R\lim C^\bullet`。$`\overline\Delta_{R/A}` は（補った）$`A/I` が完全な $`A` 加群（$`I` は可逆）なので $`-\otimes^L_AA/I` が極限と交換し、各 $`C^n` は $`I` ねじれを持たないので $`C^n\otimes^L_AA/I=C^n/IC^n`。（$`\overline{\mathcal O}_\Delta` に直接脚注 10 を当ててもよい。）

*脚注 10.* 弱終性から $`X_0\to *` は $`\mathcal X` で全射。全射 $`X_0\to *` に対する Čech コホモロジー的降下から主張が従う。前層 topos の場合は Stacks Tag 07JM で、その証明がここにも適用できる。

*命題 4.3.3（原典 Construction 4.18：Čech–Alexander 複体） — 原典との差（D21・D23）*

原典の Čech 脈体 $`B_0^\bullet` は完備テンソル積の反復だが、Lean では変数の添字で直接書く（$`B_0^n=A[X_{R\times[n]}]^\wedge`、余単体的構造は添字集合の写像から。D23）。対象は同じで、\`PrismOver\` に一般の余積がない（一般の Prop 3.13 が要る）ため、余積は Čech 脈体に要るものだけを示す。各項の envelope の存在は仮定で、満たすのは有限変数の完備多項式の場合（D21）。厳密に関手的な模型の定義域は任意の $`R` ではなく Poly($`A/d`)。

宣言：`SerrePositivity.BhattScholze.Prismatic.bigCechEval`、`SerrePositivity.BhattScholze.Prismatic.affineBigCechTerm`、`SerrePositivity.BhattScholze.Prismatic.cechAlexanderBigSiteIso`、`SerrePositivity.BhattScholze.Prismatic.affineToChosenCech_quasiIso`

:::

:::proposition "bs_4_19" (lean := "SerrePositivity.BhattScholze.Prismatic.cechAlexanderAffine_baseChange, SerrePositivity.BhattScholze.Prismatic.affineCechNerveData, SerrePositivity.BhattScholze.Prismatic.cechAlexanderAffine_isCoproduct, SerrePositivity.BhattScholze.Prismatic.affineEnvelopeTermCompletedBaseChangeIso")
*注意 4.19*　affine 直線の底変換と両立する Čech–Alexander 複体。対応表の状態：一部（special）。

*主張*　$`R` が $`A/I` 上の多項式環の $`p` 進完備化なら、Čech–Alexander 構成の多項式持ち上げとして $`A[X]` の導来 $`(p,I)` 完備化を用いることができる。得られる余単体的 $`\delta` $`A` 代数は基底 prism の底変換と可換である。

向き付き基底・有限変数の多項式の場合に、同じ Čech–Alexander cosimplicial 項の全単体射に自然な底変換を証明する。site RΓ や Tot の底変換との同一視は含まないが、本項の項ごとの構成の部分は一致。

*注意 4.3.4（原典 Remark 4.19：affine 直線の底変換と両立する Čech–Alexander 複体） — 主張*

$`R=A/I\langle X\rangle`（多項式環の $`p` 進完備化）のとき、命題 4.3.3 の $`B_0` として $`A[X]` の導来 $`(p,I)` 完備化と明らかな射 $`B_0\to R` を取れる。こうして得られる余単体的 δ-$`A` 代数 $`C^\bullet` は prism $`(A,I)` の底変換と可換。

*注意 4.3.4（原典 Remark 4.19：affine 直線の底変換と両立する Čech–Alexander 複体） — Lean*

*底変換との両立（項ごと）.* 有界 prism の射 $`f:(A,(d))\to(A',(d'))` について、各項の完備テンソル積 $`C^n\widehat\otimes_AA'` に δ 構造と prism を与え、$`A'` 上の模型の項と、両脚・δ 構造・イデアルの像・座標を保つ同型で結ぶ \`cechAlexanderAffine\_baseChange\`（AffineCechPrismBaseChange:49）。係数変更は全単体射に自然で、交代余面複体の余鎖写像 \`affineCechCoefficientCochainMap\`（AffineCechCoefficientComplex:46）を与える。導来の形：各項は $`(p,d)` 完全平坦 \`affineEnvelopeTerm\_completelyFlat\`（AffineEnvelopeDerivedBaseChange:49）で、完備導来底変換は実際の完備テンソル積で、さらに $`A'` 側の項そのもので計算される \`affineEnvelopeTermCompletedBaseChangeIso\`・\`affineEnvelopeTermCompletedBaseChangeToTargetIso\`（:56・99）。これらは項ごとの同型で、Tot・$`\Delta` の底変換（命題 4.3.5）ではない。

*選んだ模型との比較.* この模型から命題 4.3.3 の選んだ模型の複体への比較は擬同型 \`affineToChosenCech\_quasiIso\`（AffineCechChosenComparison:72）。この模型が $`\Delta_{R/A}` を計算することは drafts の \`cechAlexanderAffine\_computes\`（drafts/A0/CechAlexander.lean:277）。

*注意 4.3.4（原典 Remark 4.19：affine 直線の底変換と両立する Čech–Alexander 複体） — 証明*

（補った。原典は証明を書かない）$`B_0^n=A\langle X_0,\dots,X_n\rangle`、$`B^n=A\{X_0,\dots,X_n\}^\wedge`（完備自由 δ-$`A` 代数）で、$`\ker(B^n\to R')` は $`I` と $`X_i-X_0`（$`1\le i\le n`）で生成される。$`X_0,X_1-X_0,\dots,X_n-X_0` も $`B^n` の自由 δ 変数なので、envelope は $`Y_i=(X_i-X_0)/d` を添加したもの

$$`C^n=A\{X_0,X_1,\dots,X_n\}\{\tfrac{X_1-X_0}d,\dots,\tfrac{X_n-X_0}d\}^\wedge\;\cong\;A\{X_0,Y_1,\dots,Y_n\}^\wedge`

（$`X_i=X_0+dY_i` で $`X_i` が消える）であり、完備自由 δ-$`A` 代数そのもの（例 3.5.2 の変数変換した形）。完備自由 δ 代数の構成は係数の底変換と可換なので $`C^n\widehat\otimes_AA'\cong A'\{X_0,Y_1,\dots,Y_n\}^\wedge=C'^n`。余面・余退化写像は変数 $`X_i` の添字の付け替えで与えられ、係数によらない式なので、この同型は余単体的構造と両立する。$`C^n` は $`A` 上 $`(p,I)` 完全平坦なので、導来の完備底変換も同じものを与える。

*注意 4.3.4（原典 Remark 4.19：affine 直線の底変換と両立する Čech–Alexander 複体） — 原典との差*

原典は 1 変数、Lean は $`r` 変数。「底変換と可換」は Lean では項ごとの同型（全単体射に自然）として示し、Tot の段階の主張は命題 4.3.5 に置く。

:::

:::lemma_ "bs_4_20"
*補題 4.20*　底変換。対応表の状態：なし。

原文の Δ の completed base change は drafts。本体の envelope の項ごとの底変換は Tot・site RΓ との比較を含まない。

*命題 4.3.5（原典 Lemma 4.20：底変換） — 主張*

$`R` を $`p` 完全に滑らかな $`A/I` 代数とし、$`(A,I)\to(A',I')` を有界 prism の射で、$`A\to A'` が有限の $`(p,I)` 完全 Tor 振幅を持つとする。$`R':=R\widehat\otimes_AA'` と書くと、自然な射は同型 $`\Delta_{R/A}\widehat\otimes^L_AA'\simeq\Delta_{R'/A'}` を与え、$`\overline\Delta_{R/A}` についても同様。

（原典の続く注意）HT 比較（原典 Thm 4.11）を示した後では Tor 振幅の仮定は外せる（原典 Cor 4.12）。この補題は HT 比較の証明に使うので、この段階では外せない。

*命題 4.3.5（原典 Lemma 4.20：底変換） — Lean*

本体にない（drafts）。\`prismaticCohomology\_baseChange\`・\`hodgeTateCohomology\_baseChange\`（drafts/A0/BaseChange.lean:103・128）。限り方：$`R=(A/d)\langle X_1,\dots,X_r\rangle`、$`R'=(A'/d')\langle X_1,\dots,X_r\rangle` の場合だけ。結論は $`D(A')` の可逆な辺の存在で、自然な射の指定は含まない。Tor 振幅の仮定は Koszul 版 \`Derived.HasFiniteCompleteTorAmplitude\`（:60）。原典 Construction 6.1(3) の α に沿う特別な場合 \`crystallineCoverMap\_prismaticCohomology\`（drafts/A1/HodgeTateComparison.lean:247）。

*命題 4.3.5（原典 Lemma 4.20：底変換） — 証明*

見れば分かることと Prop 3.13 (2)（命題 3.5.1）の底変換の性質から、命題 4.3.3 の複体の構成は $`A\to A'` に沿う $`(p,I)` 完備な底変換と弱い意味で可換：余単体的環 $`C^\bullet((R/A)_\Delta,\mathcal O_\Delta)` の項ごとの導来 $`(p,I)` 完備底変換 $`C^\bullet\widehat\otimes_AA'` は $`\Delta_{R'/A'}` を計算する。（補った）実際、$`B_0\widehat\otimes_AA'\to R'` は再び完備多項式代数からの全射で、$`B\widehat\otimes_AA'` はその完備自由 δ-$`A'` 代数、Prop 3.13 (2) により $`C\widehat\otimes_AA'` はその envelope。$`C^n` は $`A` 上 $`(p,I)` 完全平坦なので導来底変換は離散で古典的な完備テンソルに一致する。よって $`C^\bullet\widehat\otimes_AA'` は $`R'/A'` に対する命題 4.3.3 の複体。

あとは、$`A\to A'` が有限の $`(p,I)` 完全 Tor 振幅を持つので、補題 4.3.7（原典 Lemma 4.22）により $`(p,I)` 完備底変換 $`-\widehat\otimes^L_AA'` が $`(p,I)` 完備な余単体的 $`A` 加群の totalization と交換すること（各項は離散なので $`D^{\ge0}`）。$`\overline\Delta` は $`\Delta` の場合を $`I` で割って従う（補った：$`I` は可逆なので $`A/I\otimes^L_AA'` は $`I\otimes_AA'\to A'` のコファイバー。この射は単射（$`A'` は $`I'` ねじれを持たない）で、像は剛性（命題 3.2.1）により $`IA'=I'`。よって $`A/I\otimes^L_AA'=A'/I'` で、$`\overline\Delta_{R/A}\widehat\otimes^L_AA'=\Delta_{R/A}\widehat\otimes^L_AA'\otimes^L_{A'}A'/I'`）。

*命題 4.3.5（原典 Lemma 4.20：底変換） — 原典との差*

drafts の主張は有限変数の完備多項式代数の場合だけ（使う場面、原典 Construction 6.1(3)・Prop 6.2・Thm 6.4 の帰着はどれも多項式代数）で、「自然な射が同型」ではなく可逆な辺の存在を述べる。Tor 振幅は Koszul 複体で測る（補題 4.3.7 の囲み）。

宣言：`prismaticCohomology_baseChange`、`hodgeTateCohomology_baseChange`、`crystallineCoverMap_prismaticCohomology`

:::

:::lemma_ "bs_4_21"
*補題 4.21*　étale 局所化。対応表の状態：なし。

任意の p-complete étale R→S について同じ Δ の étale localization を未同定。

*命題 4.3.6（原典 Lemma 4.21：étale 局所化） — 主張*

$`R\to S` を $`p` 完全に滑らかな $`A/I` 代数の $`p` 完全 étale 射とする。このとき自然な射 $`\overline\Delta_{R/A}\widehat\otimes^L_RS\to\overline\Delta_{S/A}` は同型。

*命題 4.3.6（原典 Lemma 4.21：étale 局所化） — 証明*

\*\*関手 $`F`.\*\* $`R\to S` に沿うスカラー制限 $`(S/A)_\Delta\to(R/A)_\Delta` は左随伴 $`F:(R/A)_\Delta\to(S/A)_\Delta` を持つ（対象を環の図式とみているので左随伴。原典脚注 11）。$`(B\to B/IB\leftarrow R)` に対し、$`p` 完全 étale な射 $`B/IB\to B/IB\widehat\otimes^L_RS` は Lemma 2.18（命題 2.2.4）により $`(p,I)` 完全 étale な δ 射 $`B\to B_S` に一意に変形し、$`F(B\to B/IB\leftarrow R):=(B_S\to B_S/IB_S\simeq B/IB\widehat\otimes^L_RS\leftarrow S)`。（補った）随伴性：$`(S/A)_\Delta` の対象 $`E` と $`B\to E`（$`R` 上）が与えられると、$`B/IB\widehat\otimes_RS\to E/IE` が決まり、$`B\to B_S` の $`(p,I)` 完全 étale 性による持ち上げの一意存在で $`B_S\to E` が一意に決まる。左随伴なので $`F` は余積を保ち、弱始対象を弱始対象に送る（$`E` のスカラー制限への射を随伴で移す）。

*本体.* 命題 4.3.3 の $`(C^\bullet\to C^\bullet/IC^\bullet\leftarrow R)` を取ると $`C^\bullet/IC^\bullet` は $`\overline\Delta_{R/A}` を計算し、これは零次の項（弱始対象）の Čech 脈体。$`(D^\bullet\to D^\bullet/ID^\bullet\leftarrow S):=F(C^\bullet\to\cdots)` は $`F` が余積と弱始対象を保つので再び弱始対象の Čech 脈体で、$`D^\bullet/ID^\bullet` は $`\overline\Delta_{S/A}` を計算する。よって自然な射 $`C^\bullet/IC^\bullet\widehat\otimes^L_RS\to D^\bullet/ID^\bullet` が同型であることを示せばよい。項ごとには $`F` の構成から同型。Tot との交換は補題 4.3.7 から（補った：$`C=R`、$`J=(p)`、$`R\to S` は $`p` 完全平坦なので $`p` 完全 Tor 振幅 0、各項 $`C^n/IC^n` は離散で $`D^{\ge0}`）。

*命題 4.3.6（原典 Lemma 4.21：étale 局所化） — 原典との差（D24）*

Lean では述べない。HT 比較は有限変数の完備多項式代数の場合に限って示し、滑らかな代数への延長は étale 局所化ではなく、多項式代数からの左 Kan 延長（原典 Construction 7.6 の形）で扱う（D24）。

:::

:::lemma_ "bs_4_22"
*補題 4.22*　完備底変換と totalization。対応表の状態：なし。

原文の一般の completed base change と Tot の交換は drafts。HasCochainCompleteTorAmplitude は本体にあるが、条件の定義だけでは交換定理の部分を直接証明しない。

*命題 4.3.7（原典 Lemma 4.22：完備底変換と totalization） — 主張*

$`C` を有限生成イデアル $`J` を持つ可換環、$`C\to C'` を有限の $`J` 完全 Tor 振幅を持つ可換環の射とする。このとき $`J` 完備な底変換関手 $`-\widehat\otimes^L_CC'` は $`D^{\ge0}` の totalization と交換する。

*命題 4.3.7（原典 Lemma 4.22：完備底変換と totalization） — Lean*

本体にない（drafts）。原典の一般形 \`Derived.completedBaseChange\_tot\_comm\`（drafts/A0/BaseChange.lean:73）：$`J=(x_1,\dots,x_r)`、$`D^{\ge0}(C)` に値をとる余単体的対象 $`\Delta\to D(C)` の極限錐を、完備底変換 \`completedBaseChange\` で写すと $`D(C')` の極限錐。Tor 振幅は \`Derived.HasFiniteCompleteTorAmplitude\`（:60）：任意の $`K\in D^{\ge m}(C)` について $`(K\otimes^L_CC')\otimes_{C'}\mathrm{Kos}(C';x)` の $`H^i` が $`i\lt m-c` で零。本体には同じ形の振幅の定義が半自由模型の上に \`HasCochainCompleteTorAmplitude\`（CochainCompleteTorAmplitude:37）としてある。

*命題 4.3.7（原典 Lemma 4.22：完備底変換と totalization） — 証明*

$`M^\bullet` を $`D^{\ge0}` の余単体的対象、$`M` をその totalization とし、自然な射 $`\mathrm{Tot}(M^\bullet)\widehat\otimes^L_CC'\simeq\mathrm{Tot}(M^\bullet\widehat\otimes^L_CC')` を示す。$`M^\bullet` の代わりに $`n` 骨格 $`M^{\le n}` を使えば主張は明らか（補った：$`\mathrm{Tot}(M^{\le n})` は有限極限で、完備底変換は完全関手）。

*帰着.* ある $`c\ge0` があって、$`K\in D^{\ge n}(C)` なら $`K\widehat\otimes^L_CC'\in D^{\ge n-c}(C')`（全 $`n\ge0`）であればよい。（補った）$`\mathrm{Tot}(M^\bullet)\to\mathrm{Tot}(M^{\le n})` のファイバーは $`D^{\ge n+1}` にあるので、底変換後はファイバーが $`D^{\ge n+1-c}`。底変換した側 $`M^\bullet\widehat\otimes^L_CC'` の各項は $`D^{\ge -c}` なので、その $`\mathrm{Tot}\to\mathrm{Tot}^{\le n}` のファイバーも $`D^{\ge n+1-c}`。よって両辺は次数 $`\lt n-c` で $`n` 骨格の場合と一致し、$`n` は任意。

*Koszul 複体による評価.* 生成元 $`x_1,\dots,x_r\in J` を選ぶ。関手 $`K\mapsto(K\otimes^L_CC')\otimes^L_{C'}\mathrm{Kos}(C';x_1,\dots,x_r)` が $`D^{\ge n}` を $`D^{\ge n-c}` に送る $`c` を見つければよい。実際そのとき同じ $`c` で任意の $`m\ge1` について $`K\mapsto(K\otimes^L_CC')\otimes^L_{C'}\mathrm{Kos}(C';x_1^m,\dots,x_r^m)` も $`D^{\ge n}` を $`D^{\ge n-c}` に送り（補った：$`\mathrm{Kos}(x^m)` は $`\mathrm{Kos}(x)` の有限回の拡大で、$`D^{\ge n-c}` は拡大で閉じる）、$`m` について逆極限を取れば完備化が得られる（$`R\lim` は $`D^{\ge k}` を保つ）。さて

$$`(K\otimes^L_CC')\otimes^L_{C'}\mathrm{Kos}(C';x_1,\dots,x_r)\simeq\bigl(K\otimes^L_C\mathrm{Kos}(C;x_1,\dots,x_r)\bigr)\otimes^L_{\mathrm{Kos}(C;x_1,\dots,x_r)}\mathrm{Kos}(C';x_1,\dots,x_r)`

で、$`K\mapsto K\otimes^L_C\mathrm{Kos}(C;x)` は $`D^{\ge n}` を $`D^{\ge n-r}` に送り（Koszul 複体は次数 $`[-r,0]` の有限自由複体）、$`N\mapsto N\otimes^L_{\mathrm{Kos}(C;x)}\mathrm{Kos}(C';x)` は Tor 振幅の仮定からある $`a` について $`D^{\ge m}` を $`D^{\ge m-a}` に送る。よって $`c=a+r` でよい。

*命題 4.3.7（原典 Lemma 4.22：完備底変換と totalization） — 原典との差*

Lean の Tor 振幅は標的の Koszul 複体 $`\mathrm{Kos}(C';x)` で測る（a0-design §2.9 の注意 D4-04）。商 $`C/J` で測る版とは、$`x` が標的で正則列でないとき最大 $`r` だけずれるが、有限であることは同時に成り立ち、主張は同じ。原典の証明が実際に使うのも Koszul 複体の形。

宣言：`completedBaseChange_tot_comm`、`SerrePositivity.HasCochainCompleteTorAmplitude`

:::

