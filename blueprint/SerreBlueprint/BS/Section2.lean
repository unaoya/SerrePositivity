-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.BhattScholze.Delta.Basic.DeltaColimit
import SerrePositivity.BhattScholze.Delta.Basic.DeltaQuotient
import SerrePositivity.BhattScholze.Delta.Basic.DeltaRing
import SerrePositivity.BhattScholze.Delta.Basic.DeltaWitt
import SerrePositivity.BhattScholze.Delta.Basic.Tensor
import SerrePositivity.BhattScholze.Delta.Distinguished.Distinguished
import SerrePositivity.BhattScholze.Delta.Distinguished.PrimeLocalIntegers
import SerrePositivity.BhattScholze.Delta.Distinguished.Universal
import SerrePositivity.BhattScholze.Delta.DividedPower.Coefficients.Factorial
import SerrePositivity.BhattScholze.Delta.DividedPower.PDivision.PDivision
import SerrePositivity.BhattScholze.Delta.Extension.DeltaAdicCompletion
import SerrePositivity.BhattScholze.Delta.Extension.DeltaLocalization
import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeDelta
import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeWitt
import SerrePositivity.BhattScholze.Delta.Perfect.DeltaPerfection
import SerrePositivity.BhattScholze.Delta.Perfect.DistinguishedRegular
import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDelta
import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDeltaTensor
import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismHomLift

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "§2 δ-rings" =>
%%%
number := false
tag := "bs-2"
%%%

BS §2 の項目と、本体の宣言との対応。本文は対応表（`research/bs-coverage`）の照合の理由で、原典の本文の写しではない。

*導入*

§2 は prism を定義するための言葉を用意する節である。E3 への道で後に効くのは、δ 構造の基本（§2.1・§2.2）、distinguished 元（§2.3）、完全 δ 環（§2.4、第 3 章の Thm 3.10 の土台）、pd 包との関係と envelope の平坦性（§2.5・§2.6、第 4・5 章の Čech 計算と結晶比較の土台）である。

*導入 — 原典との差（全体）*

原典は「すべての環は $`\mathbb Z_{(p)}` 代数」と仮定するが、Lean は任意の可換環で述べる（零環も含む）。δ 構造は型クラスではなくデータ \`DeltaStructure p A\` で、仮定は \`\[Fact p.Prime\]\` だけ。

*§2.1 定義と基本性質*

この節では δ 環の言葉を用意する。以下、$`p` は素数、環はすべて可換環とする（原典は $`\mathbb Z_{(p)}` 代数に限るが、形式化はこの仮定を置かない）。番号「命題 2.1.n」はこのノートの番号で、括弧内が原典の番号。原典の Def 2.1〜Rem 2.14 の全項目を扱う。原典 Rem 2.3・Rem 2.5・Ex 2.6 は注意 2.1.6・注意 2.1.7・例 2.1.8 として、原典の順の位置（命題 2.1.5 の後）に置く。

*§2.1 定義と基本性質 — 定義と言い換え*

環 $`A` の長さ 2 の Witt 環 $`W_2(A)` は、集合 $`A\times A` に
$$`(x_0,x_1)+(y_0,y_1)=\Big(x_0+y_0,\ x_1+y_1+\tfrac{x_0^p+y_0^p-(x_0+y_0)^p}{p}\Big),\qquad (x_0,x_1)(y_0,y_1)=(x_0y_0,\ x_0^py_1+x_1y_0^p+p\,x_1y_1)`
で環構造を入れたもの（分数は $`\mathbb Z[x_0,y_0]` の多項式なので任意の環で意味を持つ）。第 0 成分 $`\epsilon\colon W_2(A)\to A` と第 1 ghost 成分（Witt の Frobenius）$`F=g_1\colon(x_0,x_1)\mapsto x_0^p+px_1` はどちらも環準同型。

*§2.1 定義と基本性質 — Lean の中身（§2.1） — 読んで分かったこと（§2.1）*

- Rem 2.4 を定義に採ったので、Def 2.1 の恒等式（特に加法公式の $`(x^p+y^p-(x+y)^p)/p`）は Witt 環の加法から自動的に出る。加法の補正項は「Teichmüller 和の第 1 Witt 座標」として現れる（\`delta\_add\`、DeltaRing:122）。原典のように $`p` で割る式は使わない。

- 同じ理由で、テンソル積の δ 構造（命題 2.1.9）も $`W_2` への切断を環のテンソル積の普遍性で貼るだけで得られ、$`p` 正則性を仮定しない。

- $`\mathbb Z_{(p)}` 代数を仮定しないので、δ 環の圏の始対象は $`\mathbb Z` になる（$`\mathbb Z\to W_2(A)` の環準同型は一つしかない）。$`\mathbb Z_{(p)}` の始性（例 2.1.8 (2)）はそこから局所化の普遍性で出す。

- Lemma 2.11 の Frobenius の忠実平坦性は、p 完全忠実平坦と mod p 忠実平坦の形で示されている。原典の証明が使う場面のうち、Lemma 2.36 の (a)（生の pushout の $`p` ねじれなし）は §2.5 の自由座標の場合に入っている。そこで使う Frobenius の p 完全平坦性は、剰余が $`\mathbb F_p` 上の多項式環である p 正則な δ 環についての形 \`crystallineCompletelyFlat\_frobenius\`（CrystallineTensorRegularity:206）で、証明は同じく「mod p で Frobenius ＝ expand、expand は自由」。

*§2.2 δ 構造の延長*

δ 環 $`A` から作った環、すなわち局所化、古典的 $`I` 進完備化、導来 $`I` 完備で $`I` 完全エタールな代数に、δ 構造がただ一つ延びることを示す。どの場合も $`W_2` による言い換え（定義 2.1.1：δ 構造 ＝ 切断 $`w\colon A\to W_2(A)`）で見通しがよくなる。作った環 $`B` の普遍性を使って $`A\to W_2(A)\to W_2(B)` を $`B\to W_2(B)` に延ばせばよく、そのためには $`W_2(B)` が同じ普遍性の相手になること（分母の像が単元になる、完備である）を確かめればよい。完備化の場合の鍵は、$`p\in I` なら δ が $`I` 進連続になること。

Lean では \`Delta/Extension/\` の三つのファイルが受け持つ：\`DeltaLocalization\`（命題 2.2.1・注意 2.2.2）、\`DeltaAdicCompletion\`（命題 2.2.3）、\`DeltaPDCompletion\`（命題 2.2.4 の完備化の部分）。

*§2.3 distinguished 元*

この小節では、prism の定義の中心になる distinguished 元（$`\delta(d)` が単元）を導入し、その例（$`p` と、q-de Rham・$`A_{\inf}`・Breuil–Kisin の生成元）、distinguished 元を持つ普遍 δ 環、$`p` の変形としての見方（Rem 2.22）、単元倍・因子での安定性、イデアル $`(d,\varphi(d))` による判定（Lemma 2.25）を述べる。根基 $`\mathrm{rad}(A)` は Jacobson 根基。Lean の宣言は \`Delta/Distinguished/\` の 4 本（\`Distinguished\`：Ex 2.20(1)・Lemma 2.23〜2.25、\`Universal\`：Ex 2.21、その補助の \`PrimeLocalIntegers\`・\`PrimeLocalFlat\`）と、定義を置く \`Basic/DeltaRing\` にある。

*§2.4 完全 δ 環*

この節では Frobenius 持ち上げが同型な δ 環を調べる。鍵は Lemma 2.28 の「$`px=0\Rightarrow\varphi(x)=0`」（$`\delta(px)=0` を展開する）で、そこから完全 δ 環は p ねじれなしになり、Cor 2.31 で完全 $`p` 完備 δ 環と完全 $`\mathbb F_p` 代数が $`A\mapsto A/p`、$`R\mapsto W(R)` で対応する。後半は完全 δ 環の元の性質（p 冪根を持つ元は rank 1、distinguished 元の Teichmüller 係数による判定、distinguished 元の正則性と商の $`p^\infty` ねじれ）。Lean は \`Delta/Perfect/\` にある。

*§2.5 pd 包との関係*

$`p` ねじれなしの $`\mathbb Z_{(p)}` 代数 $`A` で、通常の分冪を $`\gamma_n(x)=x^n/n!\in A[1/p]` とおく。この節の主張は「δ 環で $`\varphi(x)/p` を添加すること」と「$`(x)` に沿う pd 包を取ること」が同じだ、ということに尽きる。まず $`\gamma_p` から全 $`\gamma_n` が出ること（命題 2.5.1）を示し、普遍な場合 $`\mathbb Z_{(p)}\{x\}` で二つが一致することを示す（命題 2.5.2・注意 2.5.3）。次に $`p` を法として正則な列に沿う pd 包を押し出しで計算し（命題 2.5.4）、二つを合わせて一般の δ 環で $`A\{\varphi(f)/p\}=D_{(f)}(A)` を得る（系 2.5.5）。最後の二項はその帰結についての注意。

*§2.5 pd 包との関係 — Delta/DividedPower/ の構成*

依存の向きは (1) → (2)、(3) → (4) → (2)、(5) の \`PrincipalDP\` は \`RankOneDP\` と (1) の \`PDivision\` の上にある。(3)(5) は原典では「standard calculation」「classical」の一言で済まされている部分を Mathlib の \`DividedPowerAlgebra\` の上で証明したもの。$`a_s/d` を添加する生の包そのもの（\`DeltaAdjoinDivision\`）とその底変換・Rem 2.37 の Tor の計算は \`Delta/Division/\` の \`Basic\`・\`BaseChange\`・\`FrobeniusPushout\` にある。

*§2.5 pd 包との関係 — Delta/DividedPower/ の構成 — 読んで分かったこと*

- §2.5 の主張は有限の列について原典の形で本体にある：生の包 $`A\{\varphi(f)/p\}` そのものが $`p` ねじれなしで $`D_{(f)}(A)` に等しい（系 2.5.5）。$`r=1` の旧版も別に残る。

- 命題 2.5.2 の像の形は原典より一般（任意の $`p` 局所 δ 環・任意の元族）で、警告 2.5.7 の前半はそこから二つの δ 構造を比べるだけで出る。原典の形（生の包の $`p` ねじれなし）は、自由座標で示して押し出しで一般の列へ移す。

- 生の包と分冪表示環の同型（系 2.5.5 の Lean）は正則性を使わない。正則性は分冪表示環の $`p` ねじれなしと Tor の消滅（命題 2.5.4）にだけ使う。

- (3) と (5) は BS 固有ではなく分冪代数の一般論。

*§2.6 pd 包と prismatic envelope の平坦性*

原典はこの小節を単体的可換環で述べる。まず Koszul 複体で「相対的に $`I` 完全正則な列」を定義し（Def 2.42）、標数 $`p` の分冪多項式代数の自由性から pd 包の押し出しの $`p` 完全平坦性を出し（Lemma 2.43）、それを Frobenius による変数の取り替えと Cor 2.39 で δ 版に移す（Cor 2.44：$`B\{x_i/p\}^\wedge` は $`p` 完全平坦）。Cor 2.44 は §3 の Prop 3.13（prismatic envelope の存在と平坦性）の証明で使われる：そこでは $`d` を普遍的な元に取り替え、$`\varphi(y)=pu`（$`u` は単元）となる基底の上で「$`d` で割る」を「$`p` で割る」に直して Cor 2.44 を当てる。

記号：単体的可換環 $`A` と $`f_1,\dots,f_n\in\pi_0(A)` に対し
$$`\mathrm{Kos}(A;f_1,\dots,f_n)=A\otimes^L_{\mathbb Z[f_1,\dots,f_n]}\mathbb Z[f_1,\dots,f_n]/(f_1,\dots,f_n)`
（$`\mathbb Z[f_1,\dots,f_n]` は多項式環で、$`f_i` を $`A` の $`f_i` に送る）。単体的可換環の射 $`R\to S` が平坦とは、$`\pi_0(R)\to\pi_0(S)` が平坦で、すべての $`i` で $`\pi_i(R)\otimes_{\pi_0(R)}\pi_0(S)\to\pi_i(S)` が同型であること。

*§2.6 pd 包と prismatic envelope の平坦性 — Delta/Division/（9 本）：$`d` で割る δ 包*

原典の §2 に対応する項目はなく、Not 2.8 の添加 $`A\{x_s\}/(dx_s-a_s)_\delta`（「$`a_s/d` を添加した δ 環」）を一般の $`d`・元族で作ったもの。$`d=p` で系 2.6.6 の $`C` の古典的な環の版、一般の $`d` で §3 の Prop 3.13（prismatic envelope）と §7 の Prop 7.2（始 prism）の対象。

:::definition "bs_2_1" (lean := "SerrePositivity.BhattScholze.DeltaStructure, SerrePositivity.BhattScholze.DeltaStructure.delta_mul, SerrePositivity.BhattScholze.DeltaStructure.delta_add, SerrePositivity.BhattScholze.DeltaStructure.ofFunction")
*定義 2.1*　δ 環。対応表の状態：本体にある。

*主張*　可換環 $`R` 上の $`\delta` 構造は $`\delta(0)=\delta(1)=0` を満たす集合写像で、$`\delta(xy)=x^p\delta(y)+y^p\delta(x)+p\delta(x)\delta(y)` と $`\delta(x+y)=\delta(x)+\delta(y)+(x^p+y^p-(x+y)^p)/p` に従う。加法公式の割り算は整数係数の多項式として読む。

W₂への切断としての DeltaStructure と ofFunction・delta\_add・delta\_mul により、同じ δ の零・一・加法・積の四公理と構造を往復できる。Witt 第1係数は原文の整数係数加法多項式である。

*命題 2.1.2（原典 Def 2.1 との同値） — 主張*

写像 $`\delta\colon A\to A` について、次は同値：(i) $`\delta` はある δ 構造 $`w` から定まる；(ii) $`\delta(0)=\delta(1)=0` かつ任意の $`x,y` で
$$`\delta(xy)=x^p\delta(y)+y^p\delta(x)+p\,\delta(x)\delta(y),\qquad \delta(x+y)=\delta(x)+\delta(y)+\tfrac{x^p+y^p-(x+y)^p}{p}.`
さらに δ 構造は $`\delta` で決まる。原典 Def 2.1 は (ii) を満たす組 $`(R,\delta)` を δ 環と定義する（文献では p 微分とも呼ばれる）。

*命題 2.1.2（原典 Def 2.1 との同値） — Lean*

(i)⇒(ii)：\`delta\_zero\`（DeltaRing:97）・\`delta\_one\`（:101）・\`delta\_mul\`（:110）・\`delta\_add\`（:122）。(ii)⇒(i)：\`ofFunction\`（DeltaRing:349）、往復 \`ofFunction\_deltaStructure\`（:402）、一意性 \`ext\`（:150）。$`W_2` の式は共通基盤 \`witt\_mul\_coeff\_one\`（Coefficients:80）・\`witt\_add\_coeff\_one\`（:119）、補正項の多項式 \`wittAdditionCarry\`（:154）。加法公式の補正項は Lean では「Teichmüller 元の和の第 1 Witt 座標」の形で書かれる。

*命題 2.1.2（原典 Def 2.1 との同値） — 証明*

$`w(x)=(x,\delta x)` が環準同型であることを第 1 座標で書けば、上の $`W_2` の和・積の式から (ii) の恒等式そのものになる（第 0 座標は自明、$`w(0)=0`・$`w(1)=1` が $`\delta(0)=\delta(1)=0`）。$`W_2` の和・積の第 1 座標の式自体は、変数 $`X_{(i,n)}` の整数係数多項式環（p ねじれなし）で $`g_1` の加法性・乗法性を書いて $`p` を消去し、任意の環へ評価して得る。加法の補正項は $`p` で割る式ではなく、$`p` 倍すると $`X^p+Y^p-(X+Y)^p` になる整数係数多項式として扱う。

*命題 2.1.2（原典 Def 2.1 との同値） — 原典との差（D1）*

原典は Def 2.1 の写像 $`\delta` を定義に採り、Rem 2.4 で $`W_2` への切断と言い換える。Lean は逆に $`W_2` への切断を定義に採り、Def 2.1 の恒等式を定理として導く（命題 2.1.2）。そのため、商・局所化・テンソル積などの δ 構造は「$`W_2` への環準同型が降りる・延びる」ことで作れ、恒等式を一つずつ確かめる必要がない。逆に δ の公式を使うたびに $`W_2` の座標を経由する。

*定義 2.1.4（δ 射） — 主張*

δ 環の間の環準同型 $`f\colon A\to B` が *δ 射*であるとは、任意の $`x\in A` で $`f(\delta(x))=\delta(f(x))` となること。δ 環と δ 射は圏をなす（原典 Def 2.1 の「明らかな圏」）。

*定義 2.1.4（δ 射） — Lean*

\`IsDeltaHom\`（DeltaRing:169）。恒等射 \`isDeltaHom\_id\`（:188）、合成 \`IsDeltaHom.comp\`（:192）、環同型の逆 \`IsDeltaHom.symm\`（:201）。

*命題 2.1.5（δ 射の言い換え） — 主張*

(1) 環準同型 $`f` が δ 射 ⇔ $`W_2(f)\circ w_A=w_B\circ f`。

(2) δ 射は Frobenius 持ち上げと可換：$`f\circ\varphi_A=\varphi_B\circ f`。

(3) $`B` が p ねじれなしなら、逆に $`f\circ\varphi_A=\varphi_B\circ f` を満たす環準同型は δ 射。

(4) 任意の δ 環で $`\varphi` と $`\delta` は可換で、$`\varphi\colon A\to A` は δ 射。

*命題 2.1.5（δ 射の言い換え） — 証明*

(1) 両辺の第 0 座標は常に一致し、第 1 座標の一致が δ 射の条件。(2) $`\varphi(x)=x^p+p\delta(x)` に $`f` を当てる。(3) $`p` の消去。(4) 自由 δ 環（p ねじれなし）で (3) を使って確かめ、普遍性で任意の δ 環へ送る。

:::

:::proposition "bs_2_2" (lean := "SerrePositivity.BhattScholze.DeltaStructure.frobeniusLift, SerrePositivity.BhattScholze.DeltaStructure.existsUnique_of_frobeniusLift, SerrePositivity.BhattScholze.DeltaStructure.existsUnique_of_mod_p")
*注意 2.2*　Frobenius 持ち上げ。対応表の状態：本体にある。

*主張*　$`\delta` 構造から $`\varphi(x)=x^p+p\delta(x)` で Frobenius の持ち上げが得られる。$`p` ねじれのない環では持ち上げを指定すると $`\delta` が一意に定まり、$`\mathbf Q` 代数では任意の環自己準同型が持ち上げに当たる。

同じ φ の構成と、p 正則下での Frobenius 持ち上げからの δ 構造の存在一意性。mod p の一致による記述もある。p が単元なら持ち上げ条件は自動で同じ対応を得る。

*命題 2.1.3（原典 Rem 2.2） — 主張*

(1) $`\varphi\colon A\to A` は環準同型で、$`A/p` の Frobenius を持ち上げる：$`f(p)=0` となる任意の環準同型 $`f\colon A\to B` で $`f(\varphi(x))=f(x)^p`。

(2) $`A` が p ねじれなしなら、$`\psi(x)\equiv x^p \bmod pA` を満たす環自己準同型 $`\psi` に対し、$`\varphi=\psi` となる δ 構造がただ一つ存在する。それは $`\delta(x)=\dfrac{\psi(x)-x^p}{p}` で与えられる。特に Frobenius 持ち上げが一致する δ 構造は一致する。

(3) $`p` が可逆なら Frobenius を持ち上げる条件は空なので、$`\mathbb Q` 上の δ 環とは自己準同型を一つ持つ $`\mathbb Q` 代数のことである。

δ 環 $`R` の Frobenius を $`\varphi`（紛れるときは $`\varphi_R`）と書く。

*命題 2.1.3（原典 Rem 2.2） — Lean*

(1) \`frobeniusLift\_apply\`（DeltaRing:145）、\`map\_frobeniusLift\_of\_map\_p\_eq\_zero\`（:213）。(2) \`existsUnique\_of\_frobeniusLift\`（DeltaRing:463）、mod p の形 \`existsUnique\_of\_mod\_p\`（:507）、一意性 \`eq\_of\_frobeniusLift\_eq\`（:220）。(3) は専用の宣言が本体にない（(2) から直ちに出る）。

*命題 2.1.3（原典 Rem 2.2） — 証明*

(1) $`\varphi=g_1\circ w` は環準同型の合成。$`f(\varphi(x))=f(x)^p+f(p)f(\delta x)=f(x)^p`。(2) $`\delta(x)` を $`p\,\delta(x)=\psi(x)-x^p` の解として選び（p ねじれなしなので一意）、$`\psi` の加法性・乗法性を書いて $`p` を消去すると命題 2.1.2 の恒等式が出る。原典の言い方では「Def 2.1 の恒等式はこの要請から逆算されたもの」。一意性も $`p` の消去から。(3) $`p` 可逆なら $`A` は p ねじれなしで $`A/p=0` なので、任意の自己準同型が (2) の仮定を満たす。

:::

:::proposition "bs_2_3"
*注意 2.3*　λ 環との関係。対応表の状態：なし。

λ-ring/p-typical λ-structure との比較定理を未同定。δ の零元条件だけでは Wilkerson の対応を示さない。

*注意 2.1.6（原典 Rem 2.3：δ 構造と λ 構造） — 主張*

Wilkerson の定理 \[Wil82, Prop 1.2\]：平坦な $`\mathbb Z` 代数 $`R` 上の λ 環構造を与えることは、すべての素数 $`\ell` についての互いに可換な Frobenius 持ち上げ $`\varphi_\ell` の族を与えることと同値である。Borger \[Bor11\] はこれを（任意の $`\mathbb Z` 代数を許すなど）いくつかの方向に拡張した。特に彼の仕事から、環 $`R` 上の δ 構造は *p 典型的な λ 構造*と同じものである。

この類似から次の用語を使う：δ 環 $`B` の元 $`x` が *rank 1* であるとは $`\delta(x)=0` となること。rank 1 の元は $`\varphi(x)=x^p` を満たし、$`B` が p ねじれなしなら逆も成り立つ。

*注意 2.1.6（原典 Rem 2.3：δ 構造と λ 構造） — Lean*

λ 環と Wilkerson・Borger の定理は本体にない。rank 1 の元を表す名前つきの述語もなく、$`\delta(x)=0` と直接書く。rank 1 の元が現れる例：変数を rank 1 にする多項式環の δ 構造 \`polynomialRankOneDeltaStructure\`（RelativeFreeDelta:178）（$`\delta(X_s)=0` は \`polynomialRankOneDeltaStructure\_delta\_X\`、:189、$`\varphi(X_s)=X_s^p` は \`polynomialRankOneDeltaStructure\_frobenius\_X\`、:199）、p 進分離な δ 環で全ての $`p^n` 乗根を持つ元は rank 1 \`delta\_eq\_zero\_of\_has\_pow\_roots\`（PerfectDelta:214）（原典 Lemma 2.32、§2.4）。

*注意 2.1.6（原典 Rem 2.3：δ 構造と λ 構造） — 証明*

Wilkerson・Borger の主張は文献の引用で、原典にも証明はない。筋だけ書くと、λ 環は（大きな）Witt 環関手 $`W_{\mathrm{big}}` の余モナドの余代数であり、平坦な場合には Adams 作用素 $`\psi^n` が環準同型の可換な族で $`\psi^\ell(x)\equiv x^\ell \bmod \ell` を満たし、$`\psi^n` は $`\psi^\ell` の合成で決まる、という形に書き直せる。p 典型版では、δ 環の圏から環の圏への忘却関手の右随伴が p 典型 Witt 環 $`W` であること（命題 2.1.9、Joyal）から、δ 構造は余モナド $`W` の余代数構造 $`R\to W(R)` と同じものになる。rank 1 についての主張は $`\varphi(x)=x^p+p\delta(x)` から直ちに出る：$`\delta(x)=0` なら $`\varphi(x)=x^p`、逆に $`\varphi(x)=x^p` なら $`p\delta(x)=0` で、p ねじれなしなら $`\delta(x)=0`。

:::

:::proposition "bs_2_4" (lean := "SerrePositivity.BhattScholze.WittTwo, SerrePositivity.BhattScholze.DeltaStructure")
*注意 2.4*　δ 構造 ＝ W₂ への切断。対応表の状態：本体にある。

*主張*　任意の環 $`R` の $`\delta` 構造は、長さ二の $`p`-typical Witt 環 $`W_2(R)` の第零成分への射影の環準同型としての切断と同値である。切断の二成分は $`x` と $`\delta(x)` である。

WittTwo と第0係数射の環準同型切断という DeltaStructure の定義は、同じ W₂(R) と (x,δ(x)) による記述に一致。

*定義 2.1.1（δ 構造。原典 Rem 2.4 の形） — 主張*

環 $`A` 上の *δ 構造*とは、環準同型 $`w\colon A\to W_2(A)` で $`\epsilon\circ w=\mathrm{id}_A` を満たすもの。$`w(x)=(x,\delta(x))` と書いて写像 $`\delta\colon A\to A` を定め、$`\varphi=g_1\circ w`、すなわち $`\varphi(x)=x^p+p\,\delta(x)` を *Frobenius 持ち上げ*と呼ぶ。δ 構造を持つ環を *δ 環*という。原典 Rem 2.4（Rezk に従う）は、これが Def 2.1 の δ 構造と同じものだと述べる（命題 2.1.2）。

*定義 2.1.1（δ 構造。原典 Rem 2.4 の形） — Lean*

\`DeltaStructure\`（DeltaRing:80）（\`sectionHom\` と \`coeff\_zero\` の二つの欄）、$`\delta` は \`delta\`（:88）、$`\varphi` は \`frobeniusLift\`（:141）。$`W_2` は Mathlib の \`TruncatedWittVector p 2 A\`。型クラスではなくデータなので、同じ環に複数の δ 構造を持てる。

:::

:::proposition "bs_2_5"
*注意 2.5*　導来 Frobenius 持ち上げ。対応表の状態：なし。

SCR\_Fp の導来 Frobenius 持ち上げの空間との同値を未同定。p 正則な通常環の構成だけではこの比較にならない。

*注意 2.1.7（原典 Rem 2.5：導来 Frobenius 持ち上げは δ 構造を与える） — 主張*

$`R` を $`\mathbb Z_{(p)}` 代数とする。$`R` 上の δ 構造を与えることは、写像 $`\varphi\colon R\to R` と、空間 $`\mathrm{End}_{\mathrm{SCR}_{\mathbb F_p}}(R\otimes^L_{\mathbb Z}\mathbb F_p)` の中の「$`\varphi` が定める点と Frobenius を結ぶ道」の組を与えることと同じである。ここで $`\mathrm{SCR}_{\mathbb F_p}` は単体的可換 $`\mathbb F_p` 代数の ∞ 圏。つまり δ 構造とは*導来の意味での Frobenius 持ち上げ*のことである。

*注意 2.1.7（原典 Rem 2.5：導来 Frobenius 持ち上げは δ 構造を与える） — Lean*

本体にない（単体的可換環・導来の Frobenius は扱わない）。(a) の $`W_2` の引き戻しの四角形も名前つきの宣言としてはない。p ねじれなしの場合の (a) の帰結にあたる「Frobenius 持ち上げ ⇔ δ 構造」は命題 2.1.3 (2)。

*注意 2.1.7（原典 Rem 2.5：導来 Frobenius 持ち上げは δ 構造を与える） — 証明*

(a) $`R` が p ねじれなしなら、
$$`\begin{array}{ccc} W_2(R) & \xrightarrow{\ F\ } & R\\ \big\downarrow{\scriptstyle\epsilon} & & \big\downarrow\\ R & \xrightarrow{\ \tilde\varphi\ } & R/p\end{array}`
は環の引き戻しの四角形である。右の縦は射影、下の $`\tilde\varphi` は射影 $`R\to R/p` と $`R/p` の Frobenius の合成 $`x\mapsto x^p\bmod p`、上は Witt の Frobenius $`F(x,y)=x^p+py`。実際、引き戻し $`\{(a,x)\in R\times R : a\equiv x^p \bmod p\}` への写像 $`(x,y)\mapsto(x^p+py,\,x)` は、$`y=(a-x^p)/p` が p ねじれなしにより一意に決まるので全単射。

(b) 多項式環は p ねじれなしなので (a) が使える。原典は「単体的分解に移る」とだけ書くが、要点は、多項式環から始めて四角形の各頂点の関手（$`W_2`、$`R`、$`R\otimes^L\mathbb F_p`）を単体的環へ延ばすと、任意の単体的環 $`R` について関手的な引き戻しの四角形
$$`\begin{array}{ccc} W_2(R) & \xrightarrow{\ F\ } & R\\ \big\downarrow & & \big\downarrow\\ R & \xrightarrow{\ \tilde\varphi\ } & R\otimes^L_{\mathbb Z}\mathbb F_p\end{array}`
を得る（右の縦の写像は $`\pi_0` で全射なので、引き戻しは連結のまま）。

(c) 定義 2.1.1 により δ 構造は $`\epsilon` の切断 $`w\colon R\to W_2(R)` で、引き戻しの普遍性によりそれは「環準同型 $`\varphi\colon R\to R`（$`=F\circ w`）と、二つの合成 $`R\xrightarrow{\varphi}R\to R\otimes^L\mathbb F_p` と $`\tilde\varphi` の間のホモトピー」の組と同じ。$`R\otimes^L\mathbb F_p` は $`\mathbb F_p` 代数なので、基底変換の随伴でこれは $`\mathrm{End}_{\mathrm{SCR}_{\mathbb F_p}}(R\otimes^L\mathbb F_p)` の中の $`\varphi\otimes\mathbb F_p` と Frobenius を結ぶ道に言い換わる。

:::

:::proposition "bs_2_6" (lean := "SerrePositivity.BhattScholze.DeltaStructure.subsingleton_of_isNilpotent_p, SerrePositivity.BhattScholze.existsUnique_primeLocalIntDeltaHom")
*例 2.6*　始 δ 環 \\(\\mathbb Z\_\{(p)\}\\)。対応表の状態：一部（component）。

*主張*　$`\mathbf Z_{(p)}` 上の $`\delta` 環の圏の始対象は $`\delta(x)=(x-x^p)/p` を備えた $`\mathbf Z_{(p)}` であり、非単元の $`p` 進付値は $`\delta` により一つ下がる。$`\delta^n(p^n)` は単元なので、非零 $`\delta` 環で $`p` の冪が零となることはない。

Z\_(p) の δ 構造の始性と p 冪零 δ 環の零性を直接述べる。p-adic valuation をちょうど1下げる計算と全反復値の単元性までは含まない。

*例 2.1.8（原典 Ex 2.6：始 δ 環） — 主張*

(1) p ねじれなしの環 $`\mathbb Z_{(p)}` の環自己準同型は恒等写像だけで、それは mod $`p` の Frobenius を持ち上げる。したがって $`\mathbb Z_{(p)}` にはただ一つの δ 構造
$$`\delta(x)=\frac{x-x^p}{p}`
があり、その Frobenius は恒等写像。

(2) $`\mathbb Z_{(p)}` は δ 環（$`\mathbb Z_{(p)}` 代数）の圏の始対象である。

(3) 単元でない $`x\ne 0` について $`v_p(\delta(x))=v_p(x)-1`。特に $`\delta^n(p^n)` はすべての $`n` で単元。

(4) ある $`n\ge0` で $`p^n=0` となる δ 環は零環だけ。

*例 2.1.8（原典 Ex 2.6：始 δ 環） — Lean*

(1) $`\mathbb Z_{(p)}` は \`PrimeLocalInt\`（PrimeLocalIntegers:55）（$`(p)` の補集合での $`\mathbb Z` の局所化）、δ 構造は \`primeLocalIntDelta\`（:61）。作り方は原典と違い、$`\varphi=\mathrm{id}` となる $`\mathbb Z` 上の δ 構造（非公開の補題 \`integerFrobenius\_exists\`、:32 で存在と一意性）を Lemma 2.15（§2.2）で局所化する。$`\mathbb Z_{(p)}` 上の δ 構造の一意性と $`\delta(x)=(x-x^p)/p` の式は宣言としてはない。(2) \`existsUnique\_primeLocalIntDeltaHom\`（PrimeLocalIntegers:93）。仮定は「$`p` と素な自然数が $`A` で単元」（$`A` が $`\mathbb Z_{(p)}` 代数であること）。証明は、$`\mathbb Z\to A` が δ 射であること（$`\mathbb Z\to W_2(A)` の環準同型が一つしかないので命題 2.1.5 (1) から）と、局所化の普遍性 \`existsUnique\_localization\_lift\`（DeltaLocalization:105）による。(3) 本体にない。(4) \`DeltaStructure.subsingleton\_of\_isNilpotent\_p\`（PerfectDelta:126）。任意の δ 環で示し、(3) を使わない：$`px=0` なら $`\varphi(x)=0`（\`torsion\_calculation\`、:50、原典 Lemma 2.28 の計算）を $`x=p^{n-1}` に使うと $`p^{n-1}=\varphi(p^{n-1})=0` で、$`n` を一つずつ下げて $`1=0`。

*例 2.1.8（原典 Ex 2.6：始 δ 環） — 証明*

(1) $`\mathbb Z_{(p)}` は $`\mathbb Z` の局所化なので環準同型は一意。$`\mathbb Z_{(p)}/p=\mathbb F_p` で $`x^p\equiv x`（Fermat）なので恒等写像は Frobenius 持ち上げ。命題 2.1.3 (2) から δ 構造がただ一つ定まり、$`\delta(x)=(\mathrm{id}(x)-x^p)/p`。

(2) δ 環 $`A`（$`\mathbb Z_{(p)}` 代数）への環準同型 $`\iota\colon\mathbb Z_{(p)}\to A` はただ一つ。それが δ 射であることを示せばよい。命題 2.1.5 (1) により $`W_2(\iota)\circ w=w_A\circ\iota` を示せばよいが、両辺は $`\mathbb Z_{(p)}\to W_2(A)` の環準同型で、$`W_2(A)` では $`p` と素な整数 $`m` が単元（$`(x_0,x_1)` が単元 ⇔ $`x_0` と $`x_0^p+px_1` が単元、で $`m` の像は両方 $`m`）なので、そのような環準同型は一つしかない。

(3) $`x=p^nu`（$`n\ge1`、$`u` は単元）とすると $`\delta(x)=p^{n-1}u-p^{np-1}u^p`。$`np-1\ge 2n-1>n-1` なので $`v_p(\delta(x))=n-1`。帰納的に $`v_p(\delta^k(p^n))=n-k`（$`k\le n`）で、$`k=n` で単元。

(4) $`A` で $`p^n=0` とする。始射 $`\mathbb Z_{(p)}\to A` は δ 射なので、$`\delta^n(p^n)` の像は $`\delta^n(0)=0`。一方 (3) よりそれは単元の像で単元。よって $`1=0`。

*例 2.1.8（原典 Ex 2.6：始 δ 環） — 原典との差（D2・D4）*

原典は環をすべて $`\mathbb Z_{(p)}` 代数とするので、始 δ 環は $`\mathbb Z_{(p)}` で、(4) は $`\delta^n(p^n)` の単元性から出る。Lean はこの仮定を置かない（D2）ので、$`\mathbb Z_{(p)}` の始性は「$`p` と素な整数が単元」という仮定つきの定理になる（仮定なしの δ 環の始対象は $`\mathbb Z` で、上の証明の中に現れる）。(4) は $`\delta(p)` の単元性の代わりに $`\delta(p)\equiv1\bmod p` で消去する Lemma 2.28 の計算（D4）を通す。

:::

:::proposition "bs_2_7" (lean := "SerrePositivity.BhattScholze.tensorDeltaStructure, SerrePositivity.BhattScholze.existsUnique_tensorDeltaHom, SerrePositivity.BhattScholze.deltaDirectLimitStructure, SerrePositivity.BhattScholze.deltaDirectLimitLift_isDeltaHom, SerrePositivity.BhattScholze.perfectDeltaTensorStructure, SerrePositivity.BhattScholze.deltaWittGhostRingHom")
*注意 2.7*　極限・余極限、Witt。対応表の状態：一部（component）。

*主張*　$`\delta` 環の極限・余極限は台環で計算され、忘却関手の左随伴は自由 $`\delta` 環、右随伴は $`p`-typical Witt ベクトルをとる関手である。右随伴から得る $`R\to W(R)` の最初の二成分は $`x\mapsto(x,\delta(x))` である。

通常の tensor pushout と有向余極限の δ 構造・普遍射を直接与える。任意の極限・余極限、Witt の右随伴全体は未供給。ghost 注入性を要する Witt 写像は一般の主張として数えない。

*命題 2.1.9（原典 Rem 2.7） — 主張*

δ 環の圏はすべての極限と余極限を持ち、それらは下の環で計算される（忘却関手 $`U\colon\delta\text{-Ring}\to\text{Ring}` は極限と余極限を保つ）。したがって $`U` は左随伴（自由 δ 環、命題 2.1.14）と右随伴（Joyal による p 典型 Witt 環 $`W`）を持ち、自然な δ 射 $`w_R\colon R\to W(R)` がある（その最初の二成分は $`x\mapsto(x,\delta(x))`、定義 2.1.1 の $`w`）。

*命題 2.1.9（原典 Rem 2.7） — Lean*

本体にあるのは*有向余極限と通常のテンソル積*。有向余極限 \`deltaDirectLimitStructure\`（DeltaColimit:76）（各段の切断を \`Ring.DirectLimit.lift\` で貼る）、普遍射も δ 射 \`deltaDirectLimitLift\_isDeltaHom\`（:98）。*テンソル積*（δ 環の押し出し）：δ 環 $`A` 上の δ 代数 $`B,C` について $`B\otimes_AC` の δ 構造 \`tensorDeltaStructure\`（Tensor:101）、二つの脚が δ 射 \`tensorDeltaStructure\_includeLeft\`・\`tensorDeltaStructure\_includeRight\`（:120・126）、両脚に合う δ 射の一意延長 \`existsUnique\_tensorDeltaHom\`（:156）。作り方は上の方針どおりで、$`B\to W_2(B)\to W_2(B\otimes_AC)` と $`C\to W_2(B\otimes_AC)` が $`A` 上で一致するので、環のテンソル積の普遍性で $`W_2` への切断が一つ決まる。p 正則性は要らない。完全 δ 環のテンソル積の完全性・離散性は別に \`perfectDeltaTensorStructure\`（PerfectDeltaTensor:200）。一般の積・引き戻し・余極限と、二つの随伴は本体にない。$`w_R` は ghost 写像が単射の場合だけ環準同型 \`deltaWittGhostRingHom\`（DeltaWitt:287）として作られ、さらに p ねじれなしなら長さ 2 に切ると $`w` に戻る（\`deltaWittGhostRingHom\_truncate\_two\_comp\`、:329）。

*命題 2.1.9（原典 Rem 2.7） — 証明*

極限は成分ごとの $`W_2` の切断を貼ればよい。余極限は自然な写像 $`\mathrm{colim}_iW_2(A_i)\to W_2(\mathrm{colim}_iA_i)` を使って切断を作る。随伴は随伴関手定理から。*論理の向き*：随伴があることから出るのは「存在すれば下の環で計算できる」（右随伴があれば余極限を、左随伴があれば極限を保つ）までで、存在そのものは上の直接の構成（あるいはモナドの代数の圏としての一般論）による。

:::

:::definition "bs_2_8" (lean := "SerrePositivity.BhattScholze.RelativeFreeDeltaRing, SerrePositivity.BhattScholze.existsUnique_relativeFreeDeltaHom, SerrePositivity.BhattScholze.existsUnique_relativeFreePresentationHom")
*記法 2.8*　添加と消去。対応表の状態：本体にある。

*主張*　$`\{\cdot\}` は $`\delta` 環での自由な元の添加を、$`(\cdot)_\delta` は $`\delta` 環として元を零にする商を表す。例えば $`f` を零にするには、自由な元 $`t` を一方で $`f`、他方で零へ送る二つの写像の押し出しをとる。

相対自由 δ 環と δ 安定閉包の商の普遍性が、添加と関係を課す原文の記法を同じ δ 環上で与える。

*命題 2.1.10（元の添加。原典 Not 2.8 の $`\{\ \}`） — 主張*

δ 環 $`R` と集合 $`\sigma` に対し、δ 環 $`R\{x_s\}_{s\in\sigma}`、δ 射 $`R\to R\{x_s\}`、元 $`x_s` の組で次を満たすものがある：任意の δ 環 $`A`、δ 射 $`f\colon R\to A`、元 $`a_s\in A` に対し、$`f` を延長し $`x_s\mapsto a_s` となる δ 射がただ一つある。具体的には $`R\{x_s\}=R[x_{(s,n)}]_{s\in\sigma,\,n\ge0}` で、$`\delta(x_{(s,n)})=x_{(s,n+1)}`、係数上は $`R` の δ。原典の記法では $`\mathbb Z_{(p)}\{x\}` は一変数の自由 δ 環。

*命題 2.1.10（元の添加。原典 Not 2.8 の $`\{\ \}`） — Lean*

多項式 δ 構造 \`polynomialDeltaStructure\`（RelativeFreeDelta:77）、δ 射の判定 \`isDeltaHom\_mvPolynomial\`（:131）。相対自由 δ 環 \`RelativeFreeDeltaRing\`（:229）とその δ 構造 \`relativeFreeDeltaStructure\`（:244）、普遍性 \`existsUnique\_relativeFreeDeltaHom\`（:320）。原典は自由 δ 環を作ってから pushout を取るが、Lean は基底 $`R` 上で直接作る（一般の pushout が無くても済む）。

*命題 2.1.10（元の添加。原典 Not 2.8 の $`\{\ \}`） — 証明*

一般に、多項式環 $`R[X_v]` と任意の多項式 $`v_v` に対し、係数上で $`R` の δ に一致し $`\delta(X_v)=v_v` となる δ 構造がただ一つある：係数の切断 $`R\to W_2(R)\to W_2(R[X])` と $`X_v\mapsto(X_v,v_v)` から、多項式環の普遍性で $`W_2` への環準同型が一つ決まる（p ねじれなしは不要）。また多項式環からの環準同型は、係数と変数で δ と可換なら δ 射。これを $`v_{(s,n)}=x_{(s,n+1)}` に使い、普遍性は $`x_{(s,n)}\mapsto\delta^n(a_s)` の評価写像で与える。

*命題 2.1.13（生成元と関係式。原典 Not 2.8 の $`\{\ \}` と $`(\ )_\delta` を合わせた形） — 主張*

δ 環 $`R`、集合 $`\sigma`、イデアル $`I\subset R\{x_s\}` に対し、$`R\{x_s\}/I_\delta` は次の普遍性を持つ：δ 射 $`f\colon R\to A` と元 $`a_s\in A` で、評価写像 $`x_s\mapsto a_s` が $`I` を零に送るものに対し、$`f` を延長し $`x_s\mapsto a_s` となる δ 射 $`R\{x_s\}/I_\delta\to A` がただ一つある。原典の例：$`\mathbb Z_{(p)}\{x,y\}/(f)_\delta` は pushout
$$`\begin{array}{ccc}\mathbb Z_{(p)}\{t\} & \xrightarrow{\ t\mapsto f\ } & \mathbb Z_{(p)}\{x,y\}\\ \big\downarrow{\scriptstyle t\mapsto 0} & & \big\downarrow\\ \mathbb Z_{(p)} & \longrightarrow & \mathbb Z_{(p)}\{x,y\}/(f)_\delta\end{array}`
で定まる。ほかに $`d` で割る包 $`A\{a_s/d\}=A\{x_s\}/(dx_s-a_s)_\delta`（\`Delta/Division\`）。

*命題 2.1.13（生成元と関係式。原典 Not 2.8 の $`\{\ \}` と $`(\ )_\delta` を合わせた形） — Lean*

\`existsUnique\_relativeFreePresentationHom\`（RelativeFreeDelta:356）。原典の pushout 図式の Lean での実体。

*命題 2.1.13（生成元と関係式。原典 Not 2.8 の $`\{\ \}` と $`(\ )_\delta` を合わせた形） — 証明*

命題 2.1.10 と 2.1.12 を合わせる。

:::

:::lemma_ "bs_2_9" (lean := "SerrePositivity.BhattScholze.DeltaStructure.isStable_iff_existsUnique_quotient, SerrePositivity.BhattScholze.DeltaStructure.quotient, SerrePositivity.BhattScholze.DeltaStructure.existsUnique_quotient_lift")
*補題 2.9*　商。対応表の状態：本体にある。

*主張*　$`\delta` 環 $`A` のイデアル $`I` が $`\delta` で安定であることと、商 $`A/I` に射影と両立する $`\delta` 構造があることは同値で、その構造は一意である。

同じ ideal I の δ 安定性 iff A/I に一意の compatible δ 構造、さらに商の普遍射まで。p 正則性を追加しない。

*命題 2.1.11（原典 Lemma 2.9） — 主張*

δ 環 $`A` のイデアル $`I` について、次は同値：(i) $`I` は δ 安定（$`\delta(I)\subset I`）；(ii) $`A/I` 上の δ 構造で $`A\to A/I` が δ 射になるものが存在する。このとき (ii) の δ 構造は一意で、$`I` を零に送る δ 射 $`A\to B` は $`A/I` からの δ 射に一意に分解する。また δ 射の核は δ 安定。

*命題 2.1.11（原典 Lemma 2.9） — 証明*

(i)⇒(ii)：$`A\to W_2(A)\to W_2(A/I)` は $`I` を零に送る（第 0 座標は $`x\in I`、第 1 座標は $`\delta(x)\in I`）ので、商の普遍性で切断が降りる。(ii)⇒(i)：$`x\in I` なら $`\delta(x)\bmod I=\delta(0)=0`。原典は加法公式から $`\delta(a)\equiv\delta(a+f)\bmod I`（$`f\in I`）を示す（補正項 $`(a^p+f^p-(a+f)^p)/p` は $`f` で割り切れる）が、$`W_2` への環準同型が降りることで済む。

:::

:::proposition "bs_2_10" (lean := "SerrePositivity.BhattScholze.DeltaStructure.deltaClosure, SerrePositivity.BhattScholze.DeltaStructure.existsUnique_deltaClosure_quotient_lift, SerrePositivity.BhattScholze.DeltaStructure.deltaClosure_eq_span_iterates")
*例 2.10*　δ 閉包での商。対応表の状態：本体にある。

*主張*　$`\delta` 環 $`A` のイデアル $`I` を零にする普遍的な $`\delta` $`A` 代数は、$`I` の各元のすべての反復 $`\delta^n` が生成するイデアルによる商である。

同じ I の反復 δ 像の生成 ideal として δClosure を同定し、A/δClosure(I) の普遍性を述べる。

*命題 2.1.12（元の消去。原典 Ex 2.10） — 主張*

δ 環 $`A` のイデアル $`I` に対し、$`I` を含む最小の δ 安定イデアル $`I_\delta`（δ 閉包）があり、$`I_\delta` は $`\bigcup_{n\ge0}\delta^n(I)` で（$`I=(S)` なら $`\bigcup_n\delta^n(S)` で）生成される。$`A\to A/I_\delta` は「$`IB=0` となる δ $`A` 代数 $`B`」の普遍対象である。

*命題 2.1.12（元の消去。原典 Ex 2.10） — 証明*

$`I_\delta` は $`I` を含む δ 安定イデアル全部の交わり。生成元の表示には「生成元の δ が生成イデアルに入れば、イデアルは δ 安定」を使う：和は加法公式の補正項が $`I` に入ること（Teichmüller 元を $`A/I` へ送ると 0）、積は積公式の三項がそれぞれ $`I` に入ることから、生成元についての帰納法。普遍性は、δ 射の核が $`I` を含む δ 安定イデアルなので $`I_\delta` も含むことと命題 2.1.11 から。

:::

:::lemma_ "bs_2_11" (lean := "SerrePositivity.BhattScholze.RelativeFreeDeltaRing, SerrePositivity.BhattScholze.existsUnique_relativeFreeDeltaHom")
*補題 2.11*　自由 δ 環、Frobenius の忠実平坦性。対応表の状態：一部（component）。

*主張*　一元生成の自由 $`\delta` 環 $`\mathbf Z_{(p)}\{x\}` は $`\delta^n(x)` を独立変数とする多項式環で、その Frobenius は忠実平坦である。$`p` を反転すると $`\varphi^n(x)` が多項式変数となる。

相対自由 δ 環の係数を Z\_(p) に取れば δ 反復変数による多項式環の表示と普遍性を得る。通常の Frobenius の忠実平坦性と Q 上の φ 反復変数表示は未供給。mod p/完全忠実平坦性で置き換えない。

*命題 2.1.14（原典 Lemma 2.11） — 主張*

(1) 集合 $`\sigma` 上の自由 δ 環 $`\mathbb Z_{(p)}\{x_s\}` は多項式環 $`\mathbb Z_{(p)}[x_{(s,n)}]` で、$`x_{(s,n)}=\delta^n(x_s)`。

(2) その Frobenius $`\varphi` は忠実平坦。

(3) $`\mathbb Q\{x\}=\mathbb Z_{(p)}\{x\}[1/p]` は $`x,\varphi(x),\varphi^2(x),\dots` 上の多項式環。

*命題 2.1.14（原典 Lemma 2.11） — Lean*

(1) 整数係数（$`\mathbb Z_{(p)}` ではなく $`\mathbb Z`）で原典どおりの経路：\`freeDeltaFrobenius\`（FreeDeltaRing:49）、mod p で Frobenius \`freeDeltaFrobenius\_mod\_p\`（:69）、δ 構造 \`existsUnique\_freeDeltaStructure\`（:93）、普遍性 \`existsUnique\_freeDeltaHom\`（:160）。基底 $`R` 上の版は命題 2.1.10。(2) *p 完全忠実平坦性まで*：\`freeDeltaFrobenius\_isCompletelyFaithfullyFlat\`（FreeDeltaFrobeniusFlat:339）、mod p の忠実平坦性 \`freeDeltaModPFrobenius\_moduleFaithfullyFlat\`（:231）。本当の（p 完全でない）忠実平坦性は本体にない。座標ごとの剰余版（$`L/(p,z)\to L/(p,\varphi(z))` の忠実平坦性）は 原典 Ex 3.4 の Frobenius の平坦性（第 3 章）の証明に使われている。(3) 本体にない。

*命題 2.1.14（原典 Lemma 2.11） — 証明*

(1) $`A=\mathbb Z_{(p)}[x_{(s,n)}]` に $`\varphi(x_{(s,n)})=x_{(s,n)}^p+px_{(s,n+1)}` を入れると $`A/p` の Frobenius の持ち上げで、p ねじれなしなので命題 2.1.3 (2) から δ 構造 $`\delta(x_{(s,n)})=x_{(s,n+1)}` が決まる。δ 環 $`R` と元 $`f` に対し $`\eta_f(x_{(s,n)})=\delta^n(f)` で環準同型を定めると、変数上で δ と可換で、Def 2.1 の恒等式が変数上の振る舞いから生成される部分代数上の振る舞いを決めるので δ 射。一意性も同じ理由。

(2) 原典：$`\varphi` を有限段 $`\varphi_i\colon\mathbb Z_{(p)}[x,\dots,\delta^i(x)]\to\mathbb Z_{(p)}[x,\dots,\delta^{i+1}(x)]` の有向余極限に分け、ファイバーごとの平坦性の判定で $`\varphi_i[1/p]` と $`\varphi_i/p` の忠実平坦性に帰着。$`\varphi_i[1/p]` は $`\mathbb Q[x,\varphi(x),\dots,\varphi^i(x)]\to\mathbb Q[x,\dots,\varphi^{i+1}(x)]` の生成元のずらし、$`\varphi_i/p` は $`\mathbb F_p[x,\dots,\delta^i(x)]` の Frobenius と包含の合成で、どちらも忠実平坦。Lean：p 完全忠実平坦性の判定（源と終域が p 正則で mod p が忠実平坦）を使い、mod p では $`\mathbb F_p[x]` の Frobenius が expand 写像 $`x\mapsto x^p` に一致し、各指数が $`p` 未満の単項式を基底とする自由加群であることから。

(3) $`\varphi^n(x)=x^{p^n}+\dots+p^n\delta^n(x)` は $`\delta^n(x)` について係数 $`p^n` の一次式（残りは $`x,\dots,\delta^{n-1}(x)` の多項式）なので、$`p` を逆にすると $`\delta^n(x)\mapsto\varphi^n(x)` は三角形の変数変換になる。

:::

:::corollary "bs_2_12"
*系 2.12*　Frobenius は fpqc 局所全射。対応表の状態：なし。

任意の δ 環・元について fpqc に Frobenius の原像を作る宣言を未同定。完全忠実平坦版だけでは通常の忠実平坦性を含まない。

*命題 2.1.15（原典 Cor 2.12：Frobenius は fpqc 局所的に全射） — 主張*

δ 環 $`A` と $`x\in A` に対し、忠実平坦な δ 射 $`A\to B` で、$`x` の像が $`\varphi(y)`（$`y\in B`）の形になるものがある。

*命題 2.1.15（原典 Cor 2.12：Frobenius は fpqc 局所的に全射） — 証明*

$`B` を $`\mathbb Z_{(p)}\{s\}\leftarrow\mathbb Z_{(p)}\{t\}\to A`（左は $`t\mapsto\varphi(s)`、右は $`t\mapsto x`）の δ 環の pushout とする。左の写像は $`s` と $`t` を同一視すれば自由 δ 環の Frobenius そのものなので、命題 2.1.14 (2) により忠実平坦。pushout は下の環のテンソル積 $`A\otimes_{\mathbb Z_{(p)}\{t\}}\mathbb Z_{(p)}\{s\}` で計算できる（命題 2.1.9）ので、$`A\to B` は忠実平坦射の底変換として忠実平坦。$`x` の像は $`\varphi(s)` の像に等しい。

:::

:::proposition "bs_2_13" (lean := "SerrePositivity.BhattScholze.deltaWittGhostRingHom, SerrePositivity.BhattScholze.deltaWittGhostVector_frobenius_formula, SerrePositivity.BhattScholze.deltaWittGhostRingHom_unique")
*注意 2.13*　Joyal の δₙ。対応表の状態：一部（stronger-hyp）。

*主張*　$`R\to W(R)` の Witt 座標は自然な演算 $`\delta_n` を与える。$`\delta_0=x`、$`\delta_1=\delta` で、$`\varphi^n(x)=\sum_{i=0}^n p^i\delta_i(x)^{p^{n-i}}` を満たす。

同じ A の ghostMap 注入性を追加すると δWittGhostRingHom と各 ghost 成分の φ 反復公式を得る。一般の p ねじれを持つ δ 環での自然な w\_R と δ\_n の一般多項式表示は含まない。

*定義 2.1.16（Joyal の $`\delta_n`。原典 Rem 2.13） — 主張*

δ 環 $`R` の元 $`x` に対し、$`w_R(x)=(\delta_0(x),\delta_1(x),\delta_2(x),\dots)\in W(R)`（Witt 座標）で自然な作用素 $`\delta_n\colon R\to R` を定める。$`\delta_0=\mathrm{id}`、$`\delta_1=\delta` で、普遍的な恒等式
$$`\varphi^n(x)=\delta_0(x)^{p^n}+p\,\delta_1(x)^{p^{n-1}}+\dots+p^n\delta_n(x)`
で特徴づけられる。$`\delta_n` は δ について次数 $`n` のモニックな多項式で表せる（$`\delta_n(x)=\delta^n(x)+(x,\dots,\delta^{n-1}(x)` の多項式$`)`）。

*定義 2.1.16（Joyal の $`\delta_n`。原典 Rem 2.13） — Lean*

ghost 座標が $`\varphi^n(x)` になる Witt 係数の列 \`deltaWittGhostVector\`（DeltaWitt:163）。係数は可除性 $`p^{n+1}\mid\varphi^{n+1}(a)-(\dots)` から一段ずつ選ぶので、存在は p ねじれがあっても成り立つ（一意性は言わない）。ghost 写像が単射なら環準同型 \`deltaWittGhostRingHom\`（:287）、ghost 成分による一意性 \`deltaWittGhostRingHom\_unique\`（:338）、$`F(w(a))=w(a)^p+p\,w(\delta a)` の形の式 \`deltaWittGhostVector\_frobenius\_formula\`（:441）。相対自由 δ 環の生成元での値 \`relativeFreeWittGhostCoefficient\`（RelativeFreeWitt:136）。Joyal の右随伴としての普遍性は本体にない。

*定義 2.1.16（Joyal の $`\delta_n`。原典 Rem 2.13） — 証明*

$`w_R` は δ 射なので Witt の Frobenius と可換で、Witt の第 $`n` ghost 成分は $`\varphi^n` を与える。ghost 成分を Witt 座標で書いたものが上の恒等式。普遍的な場合 $`\mathbb Z_{(p)}\{x\}` は p ねじれなしなので、この恒等式から $`\delta_n(x)` が帰納的に一意に決まり、自然性から任意の δ 環でも決まる。モニック性は帰納法で、たとえば $`n=2` では $`\varphi^2(x)=(x^p+p\delta x)^p+p\delta(x)^p+p^2\delta^2(x)` から
$$`\delta_2(x)=\delta^2(x)+\sum_{k=1}^{p}\binom pk p^{k-2}\,x^{p(p-k)}\delta(x)^k`
（$`k=1` の項は $`x^{p(p-1)}\delta(x)` で、係数はすべて整数）。

:::

:::proposition "bs_2_14" (lean := "SerrePositivity.BhattScholze.relativeFreeWittCoordinateEquiv, SerrePositivity.BhattScholze.relativeFreeFiniteWittCoordinateEquiv")
*注意 2.14*　Joyal の作用素による自由 δ 環。対応表の状態：一部（stronger-hyp）。

*主張*　一元生成の自由 $`\delta` 環 $`\mathbf Z_{(p)}\{x\}` は、Joyal の演算で得る $`\delta_n(x)` を変数とする多項式環でもある。

係数 δ 環の p 正則性を明示すると、同じ相対自由環の Witt 座標多項式同型を構成する。これを Z\_(p) に適用できるが、一般の係数環で無条件とはしない。

*命題 2.1.17（原典 Rem 2.14） — 主張*

$`\mathbb Z_{(p)}\{x\}` は $`\{\delta_n(x)\}_{n\ge0}` 上の多項式環である（命題 2.1.14 (1) の言い換え）。

*命題 2.1.17（原典 Rem 2.14） — Lean*

基底 $`A` が p ねじれなしの相対版で済：$`\delta_n(x_s)=x_{(s,n)}+(`下の $`n` 段の変数の多項式$`)` \`relativeFreeWittGhostCoefficient\_eq\_X\_add\_lower\`（RelativeFreeWitt:323）、下位の多項式は一意 \`relativeFreeWittGhostLowerPolynomial\_unique\`（:331）；$`x_{(s,n)}\mapsto\delta_n(x_s)` は $`A[x_{(s,n)}]` の代数自己同型 \`relativeFreeWittCoordinateEquiv\`（:457）（逆は強帰納）、有限段 $`A[x_{(s,0)},\dots,x_{(s,N-1)}]` の版 \`relativeFreeFiniteWittCoordinateEquiv\`（:632）。André の一段の拡大で $`d` で割る包の関係式を Witt 座標に移してモニックな方程式にする計算に使う（D12）。

*命題 2.1.17（原典 Rem 2.14） — 証明*

$`\delta_n(x)=\delta^n(x)+(\delta^{n-1}(x),\dots,x` の多項式$`)` なので、$`\delta^n(x)\mapsto\delta_n(x)` は三角形の変数変換で、逆も段数についての帰納法で作れる。

:::

:::lemma_ "bs_2_15" (lean := "SerrePositivity.BhattScholze.DeltaStructure.localization, SerrePositivity.BhattScholze.DeltaStructure.existsUnique_localization, SerrePositivity.BhattScholze.DeltaStructure.existsUnique_localization_lift")
*補題 2.15*　局所化。対応表の状態：本体にある。

*主張*　$`\delta` 環 $`A` の乗法的部分集合 $`S` が Frobenius で保たれるとき、$`S^{-1}A` には局所化射と両立する一意な $`\delta` 構造が入る。これは $`S` を可逆にする $`\delta` $`A` 代数の中で始対象である。

φ 安定な同じ multiplicative set の局所化に compatible δ 構造が一意に延長し、δ 準同型の普遍性も得る。

*命題 2.2.1（原典 Lemma 2.15：局所化） — 主張*

$`A` を δ 環、$`S\subset A` を $`\varphi(S)\subset S` を満たす乗法的部分集合とする。このとき局所化 $`S^{-1}A` には、$`A\to S^{-1}A` が δ 射になる δ 構造がただ一つある。さらに $`A\to S^{-1}A` は、$`S` の各元が可逆になる δ $`A` 代数 $`B` のなかで始対象である。

*命題 2.2.1（原典 Lemma 2.15：局所化） — Lean*

局所化は Mathlib の \`IsLocalization M B\` を満たす任意の環 $`B`、$`\varphi(S)\subset S` は仮定 \`hφ\`。δ 構造 \`localization\`（DeltaLocalization:76）、標準射が δ 射 \`isDeltaHom\_localization\`（:83）、一意性 \`localization\_unique\`（:88）、二つを合わせた \`existsUnique\_localization\`（:99）、始対象であること \`existsUnique\_localization\_lift\`（:105）。p ねじれを許す。切断は \`localizationSection\`（:54）で、分母の像が $`W_2(B)` の単元になることが \`localization\_section\_isUnit\`（:41）、そこで使う単元の判定が \`wittTwo\_isUnit\_iff\`（DeltaRing:302）。

*命題 2.2.1（原典 Lemma 2.15：局所化） — 証明*

まず $`A` が p ねじれなしの場合。$`S^{-1}A` も p ねじれなしで、$`\varphi(S)\subset S` なので $`\varphi` は $`\varphi(a/s)=\varphi(a)/\varphi(s)` によって $`S^{-1}A` の環自己準同型に延びる。これは Frobenius の持ち上げになる：$`\varphi(a)=a^p+p\delta(a)`、$`\varphi(s)=s^p+p\delta(s)` を代入すると
$$`\frac{\varphi(a)}{\varphi(s)}-\frac{a^p}{s^p}=p\cdot\frac{s^p\delta(a)-a^p\delta(s)}{s^p\varphi(s)}\in p\,S^{-1}A .`
よって命題 2.1.3 (2) から δ 構造がただ一つ決まる。

一般の場合は、自由 δ 環 $`F` からの全射 $`\alpha\colon F\to A` を選ぶ。$`F` は p ねじれなし（命題 2.1.14）。$`T:=\alpha^{-1}(S)` は乗法的で（$`\alpha` は乗法的）、$`\varphi` で安定（$`\alpha` は $`\varphi` と可換）。前段より $`T^{-1}F` に δ 構造があり、$`\alpha` が全射なので $`\alpha(T)=S`、したがって $`S^{-1}A=T^{-1}F\otimes_FA`。δ 環の余極限は下の環で計算される（命題 2.1.9）ので、この押し出しが $`S^{-1}A` の δ 構造を与える。

一意性と普遍性は、どちらも「局所化からの環準同型は $`A` への制限で決まる」から出る（原典は「明らか」とする）。一意性：$`A` と両立する二つの δ 構造の切断 $`S^{-1}A\to W_2(S^{-1}A)` は $`A` 上で一致するので等しい。普遍性：$`S` を可逆にする δ 射 $`f\colon A\to B` から局所化の普遍性で環準同型 $`g\colon S^{-1}A\to B` がただ一つ決まり、$`W_2(g)\circ w_{S^{-1}A}` と $`w_B\circ g` はともに $`S^{-1}A\to W_2(B)` の環準同型で $`A` 上で一致するので等しい。すなわち $`g` は δ 射（命題 2.1.5 (1)）。

*命題 2.2.1（原典 Lemma 2.15：局所化） — 原典との差（命題 2.2.1 の証明）*

原典は p ねじれなしの場合に Frobenius を延ばし、一般の場合は自由 δ 環からの全射で帰着する。Lean は帰着せず、切断 $`A\to W_2(A)\to W_2(S^{-1}A)` を局所化の普遍性で直接延ばす。必要なのは $`s\in S` の像 $`(s,\delta(s))` が $`W_2(S^{-1}A)` の単元であることで、これは次の判定から出る：$`x=(x_0,x_1)\in W_2(R)` が単元 ⇔ $`x_0` と $`g_1(x)=x_0^p+px_1` が単元。⇒ は $`\epsilon` と $`g_1` が環準同型だから。⇐ は、$`a=x_0`、$`b=x_0^p+px_1` とおくと $`y=(a^{-1},\,-x_1a^{-p}b^{-1})` が逆元になる（積の第 1 座標は $`x_0^py_1+x_1y_0^p+px_1y_1=y_1b+x_1a^{-p}=0`）。$`(s,\delta(s))` では $`x_0=s`、$`g_1=\varphi(s)\in S` なので両方が単元で、$`\varphi(S)\subset S` はここで使う。

:::

:::proposition "bs_2_16" (lean := "SerrePositivity.BhattScholze.DeltaStructure.frobeniusDenominators, SerrePositivity.BhattScholze.DeltaStructure.existsUnique_saturatedLocalization_lift")
*注意 2.16*　p 局所化。対応表の状態：一部（component）。

*主張*　$`\delta` 環の Jacobson 根基に $`p` が属するなら、単元の Frobenius 像も単元である。任意の乗法的部分集合 $`S` について、局所化後に $`p` を Jacobson 根基に入れる操作を施した環には一意な両立する $`\delta` 構造が入り、その条件の下で $`S` を可逆にする普遍環となる。

原文が使う T=\{S,φ(S),…\} の生成部分モノイドとその δ 局所化の普遍射を構成する部分。p-localization の同一視・p∈rad の標的での普遍性全体は未供給。

*注意 2.2.2（原典 Rem 2.16：p 局所的な世界での局所化） — 主張*

$`p` が Jacobson 根基 $`\mathrm{rad}(A)` に入る δ 環 $`A` では、$`\varphi(f)=f^p+p\delta(f)` より、$`f` が単元なら $`\varphi(f)` も単元。したがって任意の δ 環 $`A` と乗法的部分集合 $`S\subset A` について、局所化 $`S^{-1}A` の p 局所化 $`(S^{-1}A)_{(p)}` は、$`T=\{S,\varphi(S),\varphi^2(S),\dots\}`（が生成する乗法的部分集合）での局所化 $`T^{-1}A` の p 局所化に一致する。命題 2.2.1 により、$`(S^{-1}A)_{(p)}` は $`A` と両立する δ 構造をただ一つ持ち、$`p\in\mathrm{rad}(B)` で $`S` が可逆になる δ $`A` 代数 $`B` のなかの始対象として特徴付けられる。

ここで環 $`R` の p 局所化は $`1+pR` での局所化、すなわち $`p\in\mathrm{rad}` となる $`R` 代数のなかの始対象と読む（原典はこの語を定義しないが、特徴付けが $`p\in\mathrm{rad}(B)` で述べられている）。

*注意 2.2.2（原典 Rem 2.16：p 局所的な世界での局所化） — Lean*

本体にあるのは $`T` と $`T^{-1}A` の普遍性まで。$`T` は $`\{\varphi^n(s)\}` が生成する部分モノイド \`frobeniusDenominators\`（DeltaLocalization:148）で、$`S\subset T` が \`le\_frobeniusDenominators\`（:152）、$`\varphi` で安定が \`frobeniusDenominators\_stable\`（:158）、$`S` を含む最小の $`\varphi` 安定な乗法的集合であることが \`frobeniusDenominators\_le\`（:170）。$`S` を可逆にする δ 射は $`T` も可逆にする \`IsDeltaHom.isUnit\_frobeniusDenominators\`（:183）。$`T^{-1}A` は「$`S` が可逆になる δ $`A` 代数」のなかの始対象 \`existsUnique\_saturatedLocalization\_lift\`（:200）。(1) の単元の主張、p 局所化、$`(S^{-1}A)_{(p)}` と $`(T^{-1}A)_{(p)}` の比較は本体にない。

*注意 2.2.2（原典 Rem 2.16：p 局所的な世界での局所化） — 証明*

(1) $`f` が単元なら $`\varphi(f)=f^p(1+pf^{-p}\delta(f))` で、$`p\in\mathrm{rad}(A)` なので $`1+pf^{-p}\delta(f)` は単元。同じ計算は δ 構造のない環でも使える：環準同型 $`h\colon A\to C` で $`p\in\mathrm{rad}(C)`、$`h(s)` が単元なら $`h(\varphi(s))=h(s)^p+p\,h(\delta(s))` も単元で、繰り返して $`h(\varphi^n(s))` も単元。

(2) 環として $`(S^{-1}A)_{(p)}` と $`(T^{-1}A)_{(p)}` は、どちらも「$`p\in\mathrm{rad}(C)` で $`S` の像が可逆な $`A` 代数 $`C`」のなかの始対象である（後者は (1) で $`T` の像も可逆になるから）。よって一致する。

(3) $`T` は $`\varphi` で安定なので、命題 2.2.1 で $`T^{-1}A` は δ 環。次に $`\varphi(p)=p`（$`\delta(p)=1-p^{p-1}`）から $`\varphi(1+px)=1+p\varphi(x)` なので、$`R=T^{-1}A` の $`1+pR` は $`\varphi` で安定で、もう一度命題 2.2.1 を使うと $`(T^{-1}A)_{(p)}` も δ 環。一意性と始対象であることは二段の局所化の普遍性を重ねて得る（$`B` が δ 環で $`S` が可逆なら $`T` も可逆：$`\varphi_B` が環準同型だから）。

*注意 2.2.2（原典 Rem 2.16：p 局所的な世界での局所化） — 原典との差（注意 2.2.2）*

原典が述べるのは $`(S^{-1}A)_{(p)}` の δ 構造と、$`p\in\mathrm{rad}(B)` の条件つきの普遍性。本体にあるのは途中の $`T^{-1}A` の普遍性で、相手が δ 射なので $`p\in\mathrm{rad}(B)` は要らない（$`\varphi_B` が環準同型なので、$`S` の像が単元なら $`\varphi^n(S)` の像も単元）。p 局所化を経ないので、$`T^{-1}A` は一般に $`S^{-1}A` と違う環になる。例：$`A=\mathbb Z[x]`、$`\delta(x)=1`（$`\varphi(x)=x^p+p`）、$`S=\{x^n\}` では $`T` は $`x^p+p` を含み、これは $`S^{-1}A=\mathbb Z[x^{\pm1}]` で単元でない。

:::

:::lemma_ "bs_2_17" (lean := "SerrePositivity.BhattScholze.DeltaStructure.delta_mem_pow, SerrePositivity.BhattScholze.DeltaStructure.adicCompletion, SerrePositivity.BhattScholze.DeltaStructure.existsUnique_adicCompletion")
*補題 2.17*　I 進完備化。対応表の状態：本体にある。

*主張*　$`\delta` 環の $`p` を含む有限生成イデアル $`I` に関して、$`\delta` は $`I` 進位相で一様連続である。従って古典的 $`I` 進完備化には元の環と両立する一意な $`\delta` 構造が入る。

δ(I\^(n+1))⊆I\^n の評価と δ の加法式から原文の連続性を得る。有限生成 I⊇(p) の同じ古典完備化への compatible δ 構造も存在一意。

*命題 2.2.3（原典 Lemma 2.17：完備化） — 主張*

$`A` を δ 環、$`I\subset A` を $`p` を含む有限生成イデアルとする。このとき $`\delta\colon A\to A` は $`I` 進連続である。より詳しく、各 $`n` に対してある $`m` があって、すべての $`x\in A` で $`\delta(x+I^m)\subset\delta(x)+I^n`。さらに $`A` の古典的 $`I` 進完備化 $`\widehat A=\lim_nA/I^n` は、$`A` と両立する δ 構造をただ一つ持つ。

*命題 2.2.3（原典 Lemma 2.17：完備化） — Lean*

評価は原典より強い $`\delta(I^{n+1})\subset I^n` \`delta\_mem\_pow\`（DeltaAdicCompletion:200）で、$`W_2` への持ち上げの第 1 座標についての相対版 \`wittTwoLift\_delta\_mem\_pow\`（:101）の特別な場合。連続性の形 \`delta\_add\_sub\_mem\_pow\`（:207）・\`delta\_sub\_mem\_pow\`（:214）。延長の構成：$`A/I^{n+1}\to A/I^n` の集合の写像 \`adicDeltaStep\`（:239）、Cauchy 列を $`(x_n)\mapsto(\delta(x_{n+1}))` とずらす \`adicDeltaSequence\`（:277）、完備化上の写像 \`adicDeltaExtension\`（:289）とその座標の式 \`eval\_adicDeltaExtension\`（:295）、積公式・加法公式 \`adicDeltaExtension\_mul\`（:354）・\`adicDeltaExtension\_add\`（:370）。δ 構造 \`adicCompletion\`（:396）は \`ofFunction\`（命題 2.1.2）で作り、標準射が δ 射 \`isDeltaHom\_adicCompletion\`（:413）。一意性 \`adicCompletion\_unique\`（:421）は $`I` 有限生成を仮定し、$`\ker(\widehat A\to A/I^n)=(I\widehat A)^n` \`adicCompletion\_ker\_eval\_eq\_pow\_map\`（Completion/Basic:112）を使う。まとめて \`existsUnique\_adicCompletion\`（DeltaAdicCompletion:451）。完備化は Mathlib の \`AdicCompletion I R\`。

原典にない普遍性も本体にある：$`J` 進完備な δ 環 $`A'` への δ 射 $`f\colon A\to A'` で $`f(I)\subset J` のものは、$`\widehat A\to A'` の δ 射にただ一つ延びる \`existsUnique\_adicCompletion\_lift\`（:541）。部品は、$`J` 進分離な相手への $`f` の環としての延長は自動的に δ 射 \`IsDeltaHom.adicCompletion\_extension\`（:477）と、延長の一意性 \`adicCompletion\_extension\_unique\`（:520）。

*命題 2.2.3（原典 Lemma 2.17：完備化） — 証明*

(a) 加法公式 $`\delta(x+y)=\delta(x)+\delta(y)+c(x,y)`、$`c(x,y)=\frac{x^p+y^p-(x+y)^p}{p}=-\sum_{0\lt i\lt p}\frac1p\binom pi x^iy^{p-i}\in yA` から $`\delta(x+I^m)-\delta(x)\subset\delta(I^m)+I^m`。よって各 $`n` に $`m\ge n` で $`\delta(I^m)\subset I^n` となるものがあればよい。

(b) 積公式 $`\delta(ab)=a^p\delta(b)+b^p\delta(a)+p\,\delta(a)\delta(b)` と、和についての (a) から、二つのイデアル $`J_1,J_2` について $`\delta(J_1J_2)\subset J_1+J_2+p\,\delta(J_1)\delta(J_2)A`。

(c) $`J_1=J_2=I` とすると $`p\in I` より $`\delta(I^2)\subset I`。$`J_1=J_2=I^{2^n}`（$`n\ge1`）とすると、帰納法の仮定 $`\delta(I^{2^n})\subset I^{2^{n-1}}` から $`p\,\delta(a)\delta(b)\in I\cdot I^{2^{n-1}}\cdot I^{2^{n-1}}\subset I^{2^n}` なので $`\delta(I^{2^{n+1}})\subset I^{2^n}`。

(d) δ は連続なので $`\widehat A` 上の連続写像に延び、Def 2.1 の恒等式は連続性で保たれるので δ 構造になる。一意性：$`\widehat A` 上の両立する δ 構造は、同じ結果を $`(\widehat A,I\widehat A)` に使うと $`I\widehat A` 進連続であり、$`A` の像は稠密なので δ は $`A` 上の値で決まる。ここで $`I` の有限生成性により $`\widehat A` の $`I\widehat A` 進位相が極限の位相に一致する（$`\ker(\widehat A\to A/I^n)=I^n\widehat A`）。

*命題 2.2.3（原典 Lemma 2.17：完備化） — 原典との差（命題 2.2.3 の証明）*

原典の評価 $`\delta(I^{2^{n+1}})\subset I^{2^n}` に対し、Lean は $`m=n+1` で済む $`\delta(I^{n+1})\subset I^n` を使う。証明は $`n` についての帰納法で、$`I^{n+2}` を生成する積 $`ab`（$`a\in I^{n+1}`、$`b\in I`）に積公式を当てると $`a^p\delta(b)\in I^{n+1}`、$`b^p\delta(a)\in I\cdot I^n`、$`p\,\delta(a)\delta(b)\in I\cdot I^n`（帰納法の仮定 $`\delta(a)\in I^n` と $`p\in I`）、和の補正項 $`c(x,y)\in yA` も $`I^{n+2}` に入る。原典の (b) で $`J_1=I^{n+1}`、$`J_2=I` と非対称に取ったことにあたる。また完備化の δ 構造の存在には $`I` の有限生成性を使わず、一意性だけで使う。

:::

:::lemma_ "bs_2_18"
*補題 2.18*　エタール射・導来完備化への延長。対応表の状態：なし。

候補は p,d の完備化の H⁰ に δ 構造を入れる定理であり、原文の導来 I 完備 SCR とその完全 étale 代数上の構造の延長との比較を含まない。通常環の部品をそのまま special としない。

*命題 2.2.4（原典 Lemma 2.18：エタール射） — 主張*

$`A` を δ 環、$`I\subset A` を $`p` を含む有限生成イデアルとし、$`B` を導来 $`I` 完備かつ $`I` 完全エタールな $`A` 代数とする。このとき $`B` は $`A` と両立する δ 構造をただ一つ持つ。

特に、$`p` のある冪を含む任意のイデアル $`I\subset A` について、$`A` の δ 構造は $`A` の導来 $`I` 完備化にただ一つ延びる。

*命題 2.2.4（原典 Lemma 2.18：エタール射） — Lean*

エタール部分（主張の本体）は本体にない。本体にあるのは末尾の主張の特別な場合で、$`d\in A` 一元について $`I=(p,d)`、導来完備化はその $`H^0`：導来 $`(p,d)` 完備化の $`H^0` に、標準射が δ 射になる δ 構造がただ一つある \`existsUnique\_deltaPDCompletionStructure\`（DeltaPDCompletion:460）、選んだ構造 \`deltaPDCompletionStructure\`（:494）、標準射が δ 射 \`pdCompletionUnit\_isDeltaHom\`（:500）、一意性 \`deltaPDCompletionStructure\_unique\`（:506）。$`H^0` は \`PDCompletionH0\`（PDCompletion:29）（$`(p,d)` の冪の Koszul 塔のホモトピー逆極限の零次ホモロジー）で、環としての普遍性 \`pdCompletion\_existsUnique\_ringHom\`（:77）：$`p` と $`d` の像について導来完備な環への準同型は $`H^0` からただ一つ延びる。加群の導来 $`f` 完備性は \`IsModuleComplete\`（ModuleComplete/Basic:140）で、列の写像 $`(x_n)\mapsto(x_n-fx_{n+1})` の全単射性と同値 \`isModuleComplete\_iff\_recurrence\_bijective\`（Closure:183）。

原典の証明の短完全列の部分：$`A\to W_2(B)` \`wittTwoBaseMap\`（DeltaPDCompletion:66）、$`A` 線形な第 0 座標 \`wittTwoProjectionLinear\`（:73）とその全射性（:187）、核と $`B` の加法同型 \`wittTwoKernelEquiv\`（:90）、核への作用が $`\varphi` を通る \`wittTwoKernelEquiv\_smul\`（:117）。完備性：$`B` が $`f(\varphi(r))` について完備なら核は $`r` について完備 \`wittTwoKernel\_isModuleComplete\`（:159）、拡大として $`W_2(B)` が $`r` について完備 \`wittTwo\_isModuleComplete\`（:197）、$`r=p` の場合 \`wittTwo\_isModuleComplete\_p\`（:214）。「$`p\in I` なら導来 $`I` 完備化と導来 $`\varphi(I)` 完備化は同じ」にあたるのは、$`p` と $`f(d)` について完備なら $`f(\varphi(d))` について完備 \`deltaImage\_frobenius\_isModuleComplete\`（:323）（$`\varphi(d)=d^p+p\delta(d)` で、$`d^p` と $`p\delta(d)` についての完備性を足す）とその逆 \`deltaImage\_isModuleComplete\_of\_frobenius\`（:337）、合わせて \`wittTwo\_isModuleComplete\_d\`（:368）。

原典にない普遍性：$`p` と $`g(d)` について導来完備な δ 環への δ 射 $`g` は $`H^0` からの δ 射にただ一つ延びる \`existsUnique\_deltaPDCompletionHom\`（:568）、環としての延長が自動的に δ 射 \`pdCompletionRingHom\_isDeltaHom\`（:530）、延長そのもの \`deltaPDCompletionLift\`（:582）。

*命題 2.2.4（原典 Lemma 2.18：エタール射） — 証明*

定義 2.1.1 の $`W_2` による言い換えを使う。Elkik の代数化定理により、$`B` はあるエタール $`A` 代数 $`B'` の導来 $`I` 完備化と書ける。van der Kallen の定理（\[BMS18, Theorem 10.4\]）により $`W_2(A)\to W_2(B')` はエタール。

*主張*：$`A\xrightarrow{w_A}W_2(A)\to W_2(B')` で $`A` 代数と見たとき、$`W_2(B)` は $`W_2(B')` の導来 $`I` 完備化である。$`A` 加群の短完全列 $`0\to\varphi_*B'\to W_2(B')\to B'\to0` がある：第 0 座標の核は $`\{(0,x)\}` で、$`a\in A` は $`(a,\delta(a))(0,x)=(0,(a^p+p\delta(a))x)=(0,\varphi(a)x)` と $`\varphi` を通して作用する。$`p\in I` なので導来 $`I` 完備化と導来 $`\varphi(I)` 完備化は一致する（$`\varphi(p)=p` より $`p\in\varphi(I)A`、$`x\in I` なら $`x^p=\varphi(x)-p\delta(x)\in\varphi(I)A`、逆に $`\varphi(x)=x^p+p\delta(x)\in I` なので、$`I` と $`\varphi(I)A` の根基が一致する）。よって $`\varphi_*B'` の導来 $`I` 完備化は $`\varphi_*B` で、短完全列を完備化すると主張を得る。特に $`W_2(B)` は導来 $`I` 完備で、$`W_2(A)` 上 $`I` 完全エタール。

次に図式
$$`\begin{array}{ccc}A&\longrightarrow&W_2(B)\\ \downarrow&&\downarrow\\ B'&\longrightarrow&B\end{array}`
（上は $`A\xrightarrow{w_A}W_2(A)\to W_2(B)`、右は第 0 座標）を考える。$`A\to B'` はエタール、$`W_2(B)\to B` は pro 無限小拡大（核 $`\{(0,x)\}` は $`(0,x)(0,y)=(0,pxy)` より自乗が $`p` 倍に入り、$`W_2(B)` は導来 $`I` 完備）なので、図式を可換にする持ち上げ $`B'\to W_2(B)` がただ一つある。$`W_2(B)` が導来 $`I` 完備なので、これは $`w_B\colon B\to W_2(B)` にただ一つ延びる。$`\epsilon\circ w_B` と $`\mathrm{id}_B` はともに $`B'\to B` の延長なので一致し、$`w_B` が求める δ 構造を与える。一意性も、両立する切断の $`B'` への制限が上の持ち上げになることから出る。

末尾の主張：導来完備性はイデアルの根基だけで決まるので $`I` を $`I+(p)` に替えてよく、$`A` の導来 $`I` 完備化 $`\widehat A` は $`\widehat A\otimes^L_AA/I\simeq A/I` より $`A` 上 $`I` 完全エタール。原典では Construction 4.4 と Lemma 4.21 で、$`B/IB` 上の p 完全エタール射を $`B` 上の δ 射に一意に変形するのに使う。

*命題 2.2.4（原典 Lemma 2.18：エタール射） — 原典との差（命題 2.2.4）*

本体は $`B` を $`A` の導来 $`(p,d)` 完備化の $`H^0` に限り、$`I` も $`(p,d)` の形に限る。この場合は原典の $`B'=A` にあたり、エタールの持ち上げの段（Elkik・van der Kallen と図式の持ち上げ）が要らない：$`H^0` は「$`p` と $`d` について導来完備な環」のなかで $`A` の下の始対象なので、$`W_2(H^0)` が導来完備であることを示せば、$`A\to W_2(H^0)` が $`H^0\to W_2(H^0)` にただ一つ延びる。$`\epsilon\circ w=\mathrm{id}` も同じ普遍性の一意性から出る。$`W_2` の導来完備性は原典の短完全列の議論そのままで、$`\varphi(I)` と $`I` の根基の比較を「$`p` と $`d` について完備なら $`\varphi(d)` について完備」の形で示す。p 正則性・古典的完備性・ねじれの有界性は仮定しない。

宣言：`SerrePositivity.BhattScholze.existsUnique_deltaPDCompletionStructure`、`SerrePositivity.BhattScholze.deltaPDCompletionStructure`

:::

:::definition "bs_2_19" (lean := "SerrePositivity.BhattScholze.DeltaStructure.IsDistinguished, SerrePositivity.BhattScholze.DeltaStructure.IsDeltaHom.map_isDistinguished")
*定義 2.19*　distinguished。対応表の状態：本体にある。

*主張*　$`\delta` 環の元 $`d` が distinguished であるとは $`\delta(d)` が単元であることをいう。この性質は $`\delta` 環の射で保たれる。

δ(d) が単元という定義および同じ δ 準同型による保存に一致。

*定義 2.3.1（原典 Def 2.19） — 主張*

δ 環 $`A` の元 $`d` が *distinguished* であるとは、$`\delta(d)` が単元であること。δ 射は distinguished 元を distinguished 元へ送る。

*定義 2.3.1（原典 Def 2.19） — 証明*

後半：δ 射 $`f` について $`\delta(f(d))=f(\delta(d))` で、環準同型は単元を単元へ送る。

:::

:::proposition "bs_2_20" (lean := "SerrePositivity.BhattScholze.DeltaStructure.isDistinguished_p, SerrePositivity.BhattScholze.DeltaStructure.delta_p_sub_one_mem")
*例 2.20*　distinguished 元の例。対応表の状態：一部（component）。

*主張*　distinguished 元の例は、結晶の場合の $`p\in\mathbf Z_p`、q-de Rham の場合の $`[p]_q\in\mathbf Z_p[[q-1]]`（$`\varphi(q)=q^p`）、perfectoid 体の $`A_{\inf}` における Fontaine 写像の核の生成元、Breuil–Kisin の場合の $`W[[u]]\to\mathcal O_K` の核の生成元である。最後の写像は離散付値拡大 $`K/\mathbf Q_p` の一様化元へ $`u` を送り、$`W` は最大不分岐係数環である。

列挙中 (1) の d=p の distinguished 性を p∈Jacobson radical の同じ条件下で証明する。q・Ainf の ξ・Breuil–Kisin の他の例は未同定。

*例 2.3.2（原典 Ex 2.20） — 主張*

次の元は distinguished である。

(1)（結晶コホモロジー）$`A=\mathbb Z_p`、$`d=p`。実際 $`\delta(p)=1-p^{p-1}\in\mathbb Z_p^{*}`。

(2)（q-de Rham コホモロジー）$`A=\mathbb Z_p[\![q-1]\!]`、δ 構造は $`\varphi(q)=q^p` で定まるもの、$`d=[p]_q=\frac{q^p-1}{q-1}`。

(3)（$`A_{\inf}` コホモロジー）perfectoid 体 $`C/\mathbb Q_p` について $`A=A_{\inf}(\mathcal O_C)`（通常の Frobenius 持ち上げによる唯一の δ 構造）、$`d=\xi` は Fontaine の写像 $`\theta\colon A_{\inf}\to\mathcal O_C` の核の任意の生成元。

(4)（Breuil–Kisin コホモロジー）$`K/\mathbb Q_p` は離散付値体で素元 $`\pi`、$`W\subset\mathcal O_K` は最大不分岐部分環。$`A=W[\![u]\!]`（$`W` の標準 δ 構造と $`\varphi(u)=u^p`）、$`d` は $`u\mapsto\pi` で定まる $`W` 線形な全射 $`A\to\mathcal O_K` の核の任意の生成元。

*例 2.3.2（原典 Ex 2.20） — Lean*

(1) は任意の δ 環で：$`\delta(p)\equiv1\bmod p` が \`DS.delta\_p\_sub\_one\_mem\`（Distinguished:54）、$`p\in\mathrm{rad}(A)` なら $`p` は distinguished が \`DS.isDistinguished\_p\`（:72）。その基になるのは、標数 $`p` の環への任意の環準同型が $`\delta(p)` を 1 に送る \`DS.map\_delta\_p\`（:42）で、証明は $`W_2` 切断 $`w` が自然数 $`p` を $`W_2(A)` の $`p` へ送ることと、標数 $`p` では Witt ベクトル $`p` の第 1 座標が 1 であること（Mathlib の \`WittVector.coeff\_p\_one\`）。$`\mathbb Z_p` の場合は $`p\in\mathrm{rad}(\mathbb Z_p)` としてこれに入る。(2)〜(4) の環（$`\mathbb Z_p[\![q-1]\!]`、$`A_{\inf}(\mathcal O_C)`、$`W[\![u]\!]`）とその生成元は本体にない。完全 prism の生成元を Witt 表示 $`W(A/p)` に移した元が distinguished であること \`perfectPrismWittGenerator\_isDistinguished\`（PerfectPrismPerfectoid:316）はあるが、これは prism の生成元の distinguished 性を δ 同型で移したもので、(3) の特殊化の議論ではない。

*例 2.3.2（原典 Ex 2.20） — 証明*

(1) $`\mathbb Z_p` は $`p` ねじれなしで $`\varphi=\mathrm{id}` なので $`\delta(p)=(\varphi(p)-p^p)/p=1-p^{p-1}`。$`\mathbb Z_p` は局所環で $`p` は極大イデアルに入るから $`1-p^{p-1}` は単元。

(2) $`q\mapsto1` は δ 射 $`\mathbb Z_p[\![q-1]\!]\to\mathbb Z_p`（$`\varphi(q)=q^p\mapsto1=\varphi(1)`、標的は $`p` ねじれなしなので Frobenius との可換性で十分）で、$`[p]_q\mapsto p`。よって $`\delta([p]_q)\equiv\delta(p)\bmod (q-1)` で、(1) から右辺は単元。$`A` は $`(q-1)` 進完備なので $`q-1\in\mathrm{rad}(A)` で、mod $`(q-1)` で単元な元は単元。直接計算しても示せる。

(3) 剰余体 $`k` への $`\mathcal O_C^\flat\to k` が誘導する δ 射 $`A_{\inf}\to W(k)` に沿って特殊化し、(2) と同様に見る。

(4) δ 射 $`W[\![u]\!]\to W`（$`u\mapsto0`）に沿って特殊化し、(2) と同様に見る（$`d` は Eisenstein 多項式の単元倍なので像は $`p` の単元倍、$`u\in\mathrm{rad}(A)`）。

*例 2.3.2（原典 Ex 2.20） — 原典との差（Ex 2.20(1)）*

原典は $`\mathbb Z_p` で $`\delta(p)=1-p^{p-1}` を計算するが、Lean は $`\mathbb Z_{(p)}` 代数も $`p` 正則性も仮定しない任意の δ 環で、合同式 $`\delta(p)-1\in(p)` を $`W_2` 切断の性質から出し、$`p\in\mathrm{rad}(A)` のとき $`p` が distinguished であることを示す（D2 の一般性の一部）。$`p` で割る式は使わない。

:::

:::proposition "bs_2_21" (lean := "SerrePositivity.BhattScholze.UniversalDistinguishedRing, SerrePositivity.BhattScholze.universalDistinguishedGenerator_isDistinguished, SerrePositivity.BhattScholze.existsUnique_universalDistinguishedHom, SerrePositivity.BhattScholze.universalDistinguished_regular")
*例 2.21*　普遍 distinguished δ 環。対応表の状態：本体にある。

*主張*　distinguished 元 $`d` を備えた普遍 $`\delta` 環は、$`\mathbf Z_{(p)}\{d\}` で $`\delta(d)` とそのすべての Frobenius 反復を反転して得られる。普遍元 $`d` は $`p` を法として非零因子である。

同じ普遍 distinguished δ 環の局所化表示と存在一意の射、mod p 正則性を与える。標的の p-local 条件は原文の Z\_(p)-代数性。

*例 2.3.3（原典 Ex 2.21：普遍 distinguished δ 環） — 主張*

distinguished 元 $`d` を備えた δ 環の圏には始対象があり、一変数の自由 δ 環 $`\mathbb Z_{(p)}\{d\}` の局所化 $`S^{-1}\mathbb Z_{(p)}\{d\}`、$`S=\{\delta(d),\varphi(\delta(d)),\varphi^2(\delta(d)),\dots\}` で与えられる：δ 環 $`A`（$`\mathbb Z_{(p)}` 代数）と distinguished な $`b\in A` に対し、$`d\mapsto b` となる δ 射がただ一つある。特に普遍 distinguished 元 $`d` は $`\bmod p` で非零因子。この δ 環を $`\mathbb Z_{(p)}\{d,\delta(d)^{-1}\}` と書く。

*例 2.3.3（原典 Ex 2.21：普遍 distinguished δ 環） — Lean*

2026-11-10（BS-W15）。台環 \`UniversalDistinguishedRing\`（Universal:49）は整数係数の自由 δ 環 \`FreeDeltaRing PUnit\` を、$`\delta(d)` と $`p` と互いに素な自然数で生成した乗法系 \`distinguishedDenominators\`（:41）の Frobenius 安定化 \`DS.frobeniusDenominators\`（DeltaLocalization:148）で局所化したもの。δ 構造 \`universalDistinguishedDelta\`（Universal:58）、標準射が δ 射 \`universalDistinguished\_algebraMap\_isDeltaHom\`（:72）、生成元の distinguished 性 \`universalDistinguishedGenerator\_isDistinguished\`（:84）、普遍性 \`existsUnique\_universalDistinguishedHom\`（:99）、正則性 \`universalDistinguished\_regular\`（:136：$`p` が非零因子で、$`d` が $`\bmod p` で非零因子）。普遍性の証明は自由 δ 環の評価 \`freeDeltaEval\` と、Frobenius 安定化での局所化の普遍性 \`DS.existsUnique\_saturatedLocalization\_lift\`（DeltaLocalization:200）。正則性は自由 δ 環での $`p` 正則性 \`freeDeltaRing\_p\_mul\_injective\`（FreeDeltaRing:61）と座標の $`\bmod p` 正則性 \`freeDeltaCoordinate\_modP\_isSMulRegular\`（FreeDeltaFrobeniusFlat:493）を、平坦な射で移す \`isSMulRegular\_mod\_of\_flat\`（FlatRegularQuotient:15）で局所化へ。完備化して第 3 章の普遍向き付き prism（原典 Ex 3.4）の係数環になる。$`\mathbb Z_{(p)}` そのものの δ 構造と、$`p` と互いに素な整数が単元な δ 環への一意な δ 射は \`primeLocalIntDelta\`・\`existsUnique\_primeLocalIntDeltaHom\`（PrimeLocalIntegers:61・93）、$`p` 局所かつ $`p` 正則な環が $`\mathbb Z_{(p)}` 上平坦であることは \`primeLocalInt\_moduleFlat\`（PrimeLocalFlat:34）にあり、§2.5 の $`\mathbb Z_{(p)}` 係数の計算で使う。

*例 2.3.3（原典 Ex 2.21：普遍 distinguished δ 環） — 証明*

$`S` は Frobenius で閉じているので、Lemma 2.15 で δ 構造が局所化に一意に延び、標準射は δ 射。distinguished な $`b` に対し、自由 δ 環の評価 $`d\mapsto b` は δ 射なので $`\delta(d)\mapsto\delta(b)`（単元）と送り、Frobenius と可換なので $`\varphi^n(\delta(d))\mapsto\varphi^n(\delta(b))` も単元。局所化の普遍性（Rem 2.16 の形）で $`S^{-1}\mathbb Z_{(p)}\{d\}` からの δ 射に一意に延びる。後半は Lemma 2.11 から：$`\mathbb Z_{(p)}\{d\}=\mathbb Z_{(p)}[d,\delta(d),\delta^2(d),\dots]` は多項式環で $`p` ねじれなし、$`\bmod p` では $`\mathbb F_p[d,\delta(d),\dots]` で $`d` は変数なので非零因子。局所化は平坦なのでどちらの正則性も保たれる。

*例 2.3.3（原典 Ex 2.21：普遍 distinguished δ 環） — 原典との差（Ex 2.21）*

係数を $`\mathbb Z_{(p)}` ではなく $`\mathbb Z` にして、$`p` と互いに素な自然数も分母に入れる。局所化は分母について可換なので、環としては原典の $`S^{-1}\mathbb Z_{(p)}\{d\}` と同じものになる。普遍性の標的の仮定も「$`\mathbb Z_{(p)}` 代数」の代わりに「$`p` と互いに素な自然数が単元」と書く（同値な条件）。

:::

:::proposition "bs_2_22"
*注意 2.22*　distinguished 元を p へ。対応表の状態：なし。

原文の指定合成 A→A→W(A)→W(A/d) で d=pu となる定理を未同定。Construction6.1の別の覆いとは区別する。

*注意 2.3.4（原典 Rem 2.22：distinguished 元を $`p` の変形とみる） — 主張*

$`A` を導来 $`p` 完備な δ 環、$`d\in A` を distinguished 元とする。合成
$$`s\colon A\xrightarrow{\ \varphi\ }A\xrightarrow{\ w\ }W(A)\xrightarrow{\ \mathrm{can}\ }W(A/d)`
（$`w` は Rem 2.7 の δ 射）は δ 環の射で、$`s(d)=pu`（$`u\in W(A/d)^{*}`）となる。つまり任意の distinguished 元は、単元倍を除いて distinguished 元 $`p` へ写る。ただし $`A` から $`W(A/d)` への移行は大きく、この写像の代数的性質は制御しにくい。ホモロジー的によりよい改良が Construction 6.1（$`A` に追加の仮定のもと）。

*注意 2.3.4（原典 Rem 2.22：distinguished 元を $`p` の変形とみる） — Lean*

本体にない。途中の $`w\colon A\to W(A)` は \`deltaWittGhostRingHom\`（DeltaWitt:287）が ghost 写像の単射を仮定した場合だけある。原典が改良とする Construction 6.1 は drafts（drafts/A1/HodgeTateComparison.lean）。

*注意 2.3.4（原典 Rem 2.22：distinguished 元を $`p` の変形とみる） — 証明*

$`s` は δ 射の合成なので δ 射。$`w` は δ 射なので $`w\circ\varphi=F\circ w`（$`F` は Witt ベクトルの Frobenius）。$`w(d)` の Witt 座標は $`(d,\delta(d),\dots)` と始まるので、$`\bmod d` では $`\mathrm{can}(w(d))=(0,\delta(d),\dots)=V(\delta(d),\dots)`。よって $`s(d)=F(V(\delta(d),\dots))=p\cdot(\delta(d),\dots)`。$`\delta(d)` は単元で、$`W(A/d)` は核 $`\ker(W(A/d)\to A/d)` に沿って完備（$`A/d` の導来 $`p` 完備性と、$`\mathbb Z/p^n` 代数での同様の主張から）なので、第 0 座標が単元の Witt ベクトル $`(\delta(d),\dots)` は単元。

:::

:::lemma_ "bs_2_23" (lean := "SerrePositivity.BhattScholze.DeltaStructure.IsDistinguished.unit_mul, SerrePositivity.BhattScholze.DeltaStructure.isDistinguished_unit_mul_iff")
*補題 2.23*　distinguished 元の単元倍。対応表の状態：本体にある。

*主張*　$`\delta` 環 $`A` の distinguished 元 $`d` と $`p` が Jacobson 根基に入るなら、任意の単元 $`u` に対して $`ud` も distinguished である。

同じ d,p∈rad と単元 u の条件から ud の distinguished 性を述べる。逆向きも存在。

*命題 2.3.5（原典 Lemma 2.23：単元倍） — 主張*

δ 環 $`A`、distinguished な $`d\in A`、単元 $`u\in A^{*}` について、$`d,p\in\mathrm{rad}(A)` なら $`ud` は distinguished。

*命題 2.3.5（原典 Lemma 2.23：単元倍） — Lean*

\`DS.IsDistinguished.unit\_mul\`（Distinguished:113）。逆単元に当てた同値の形 \`DS.isDistinguished\_unit\_mul\_iff\`（:129）：同じ仮定で $`ud` が distinguished ⇔ $`d` が distinguished。

*命題 2.3.5（原典 Lemma 2.23：単元倍） — 証明*

積公式で
$$`\delta(ud)=u^p\delta(d)+d^p\delta(u)+p\,\delta(u)\delta(d).`
第 1 項は単元、第 2・3 項は $`d,p\in\mathrm{rad}(A)` から $`\mathrm{rad}(A)` に入る。単元と根基の元の和は単元。

:::

:::lemma_ "bs_2_24" (lean := "SerrePositivity.BhattScholze.DeltaStructure.isDistinguished_factor")
*補題 2.24*　distinguished 元の因子。対応表の状態：本体にある。

*主張*　$`\delta` 環の distinguished 元が $`d=fh` と分解し、$`f,p` が Jacobson 根基に入るなら、$`f` は distinguished で $`h` は単元である。

d=fh、f,p∈rad から f が distinguished かつ h 単元という同じ二結論。

*命題 2.3.6（原典 Lemma 2.24：因子） — 主張*

δ 環 $`A` の distinguished 元 $`d` が $`d=fh`（$`f,h\in A`）と書け、$`f,p\in\mathrm{rad}(A)` なら、$`f` は distinguished で $`h` は単元。

*命題 2.3.6（原典 Lemma 2.24：因子） — Lean*

\`DS.isDistinguished\_factor\`（Distinguished:142）。仮定は $`fh` が distinguished で、結論は二つの主張の連言。

*命題 2.3.6（原典 Lemma 2.24：因子） — 証明*

$`d=fh` に δ を当てて
$$`\delta(d)=f^p\delta(h)+h^p\delta(f)+p\,\delta(f)\delta(h).`
左辺は単元、右辺の第 1・3 項は $`\mathrm{rad}(A)` に入るので、$`h^p\delta(f)` は単元。よって $`\delta(f)` と $`h` はともに単元。

:::

:::lemma_ "bs_2_25" (lean := "SerrePositivity.BhattScholze.DeltaStructure.isDistinguished_iff_p_mem_span, SerrePositivity.BhattScholze.DeltaStructure.isDistinguished_iff_of_span_eq, SerrePositivity.BhattScholze.DeltaStructure.isDistinguished_iff_p_mem_span_pow")
*補題 2.25*　\\(p\\in(d,\\varphi(d))\\) ⇔ distinguished。対応表の状態：本体にある。

*主張*　$`\delta` 環の $`d,p` が Jacobson 根基に入るとき、$`d` が distinguished であることは $`p\in(d,\varphi(d))` と同値で、従ってイデアル $`(d)` だけで決まる。

同じ d,p∈rad 下の δ(d) 単元 iff p∈(d,φ(d)) と、同じ主 ideal の生成元間の不変性を直接述べる。

*命題 2.3.7（原典 Lemma 2.25：$`(d,\varphi(d))` による判定） — 主張*

δ 環 $`A` と $`d\in A` について $`d,p\in\mathrm{rad}(A)` とする。$`d` が distinguished ⇔ $`p\in(d,\varphi(d))`。特に「$`d` が distinguished」はイデアル $`(d)` だけで決まる。

*命題 2.3.7（原典 Lemma 2.25：$`(d,\varphi(d))` による判定） — Lean*

同値 \`DS.isDistinguished\_iff\_p\_mem\_span\`（Distinguished:217）。⇒ は根基の仮定なしの \`DS.IsDistinguished.p\_mem\_span\`（:167）、⇐ は \`DS.isDistinguished\_of\_p\_mem\_span\`（:184）。後半は \`DS.isDistinguished\_iff\_of\_span\_eq\`（:226）：$`d,e,p\in\mathrm{rad}(A)` と $`(d)=(e)` のもとで $`d` と $`e` は同時に distinguished。証明は前半を使わず、$`d=re` に命題 2.3.6 を当てる（逆向きも同様）。$`(d^p,\varphi(d))` で述べた変種（原典 Lemma 3.1 の主イデアルの場合）は \`DS.isDistinguished\_iff\_p\_mem\_span\_pow\`（OrientedPrism:59）。

*命題 2.3.7（原典 Lemma 2.25：$`(d,\varphi(d))` による判定） — 証明*

⇒：$`\varphi(d)=d^p+p\,\delta(d)` で $`\delta(d)` が単元なので $`p=\delta(d)^{-1}(\varphi(d)-d^{p-1}\cdot d)\in(d,\varphi(d))`（根基の仮定は使わない）。

⇐：$`p=ad+b\varphi(d)` とする。$`d,p\in\mathrm{rad}(A)` なので、$`\delta(d)` が $`\bmod (d,p)` で単元であること、すなわち $`A/(p,d,\delta(d))=0` を示せばよい。そのために $`A` を $`(p,d,\delta(d))` 進完備化（または適当な ind-Zariski 局所化）に取り替えて $`p,d,\delta(d)\in\mathrm{rad}(A)` としてよい。$`\varphi(d)=d^p+p\delta(d)` を代入して整理すると
$$`p\,(1-b\,\delta(d))=c\,d,\qquad c=a+b\,d^{p-1}.`
$`p` は distinguished（例 2.3.2 (1)）で $`1-b\delta(d)` は単元なので、左辺は命題 2.3.5 で distinguished。命題 2.3.6 を $`cd` に当てて $`d` は distinguished。

後半：$`(d)=(e)` なら $`e=rd`、$`d=r'e` と書け、$`\varphi(e)=\varphi(r)\varphi(d)` などから $`(d,\varphi(d))=(e,\varphi(e))`。また $`d\in\mathrm{rad}` ⇔ $`e\in\mathrm{rad}`。よって前半の判定は $`(d)` だけで決まる。

*命題 2.3.7（原典 Lemma 2.25：$`(d,\varphi(d))` による判定） — 原典との差（D3）*

⇐ を、完備化・ind-Zariski 局所化を使わずに極大イデアルでの計算で示す。$`\delta(d)` が単元でないとして、$`\delta(d)` を含む極大イデアル $`\mathfrak m` をとる。$`\mathfrak m\supseteq\mathrm{rad}(A)\ni p,d` なので $`A/\mathfrak m` は標数 $`p` の体。$`e=1-b\delta(d)` とおいて $`pe=cd` に δ を当て、$`\bmod\mathfrak m` で見ると、左辺 $`\delta(pe)=p^p\delta(e)+e^p\delta(p)+p\,\delta(p)\delta(e)` は $`e\equiv1` と $`\delta(p)\mapsto1`（\`DS.map\_delta\_p\`）から 1 に、右辺 $`\delta(cd)=c^p\delta(d)+d^p\delta(c)+p\,\delta(c)\delta(d)` は 0 になり矛盾。原典の証明（命題 2.3.5・2.3.6 を完備化後の環で使う）を剰余体で一度に行ったもので、$`\delta(d)\in\mathrm{rad}` にする取り替えが要らない。後半も、原典の「判定が $`(d)` だけで決まる」経由ではなく命題 2.3.6 から直接示し、非零因子を仮定しない。

:::

:::definition "bs_2_26" (lean := "SerrePositivity.BhattScholze.DeltaStructure.IsPerfect")
*定義 2.26*　完全 δ 環。対応表の状態：本体にある。

*主張*　Frobenius 持ち上げ $`\varphi` が同型である $`\delta` 環を完全 $`\delta` 環と呼ぶ。

φ の bijectivity として IsPerfect を定義。環準同型ではこれが同型と同値。

*定義 2.4.1（原典 Def 2.26） — 主張*

δ 環 $`A` が*完全*であるとは、$`\varphi\colon A\to A` が同型であること。

*定義 2.4.1（原典 Def 2.26） — Lean*

\`DS.IsPerfect\`（DeltaRing:166）。$`\varphi` が全単射という述語。環同型として束ねたものが \`DS.frobeniusEquiv\`（PerfectDelta:293）。

:::

:::proposition "bs_2_27" (lean := "SerrePositivity.BhattScholze.DeltaPerfection, SerrePositivity.BhattScholze.existsUnique_deltaPerfectionHom, SerrePositivity.BhattScholze.deltaPerfection_isPerfect")
*注意 2.27*　完全化。対応表の状態：一部（component）。

*主張*　完全 $`\delta` 環から全 $`\delta` 環への包含の左随伴は Frobenius に沿う余極限、右随伴は Frobenius に沿う逆極限で与えられる。

左側の perfection colim\_φ の構成・perfect 性・普遍性を同じ δ 環について証明する。逆極限の右随伴は含まない。

*注意 2.4.2（原典 Rem 2.27：完全化） — 主張*

完全 δ 環の圏から δ 環の圏への包含は左随伴と右随伴を持ち、それぞれ
$$`A\mapsto A_{\mathrm{perf}}=\mathrm{colim}_\varphi A=\mathrm{colim}\big(A\xrightarrow{\varphi}A\xrightarrow{\varphi}A\to\cdots\big),\qquad A\mapsto A^{\mathrm{perf}}=\lim_\varphi A=\lim\big(\cdots\to A\xrightarrow{\varphi}A\xrightarrow{\varphi}A\big)`
で与えられる。

*注意 2.4.2（原典 Rem 2.27：完全化） — Lean*

*左随伴の側だけ*。台 \`DeltaPerfection\`（DeltaPerfection:42）は $`\varphi` の反復に沿う \`Ring.DirectLimit\`、標準段射 \`deltaPerfectionOf\`（:47）、δ 構造 \`deltaPerfectionStructure\`（:80）は有向余極限の δ 構造（命題 2.1.9 の \`deltaDirectLimitStructure\`）で、遷移が δ 射であることは \`frobeniusLift\_iterate\_delta\`（FreeDeltaRing:280）。段射は δ 射 \`deltaPerfectionOf\_isDeltaHom\`（DeltaPerfection:86）、段送り \`deltaPerfectionShift\`（:99）が Frobenius の逆で、完全性 \`deltaPerfection\_isPerfect\`（:131）。普遍性 \`existsUnique\_deltaPerfectionHom\`（DeltaPerfection:192）（第 $`n` 段の射は \`deltaPerfectionStage\`、:153、$`\varphi_P^{-1}` の $`n` 回の合成）、外延性 \`deltaPerfectionHom\_ext\`（:228）。同じファイルに、完全 δ 環が閉じている操作として、有向余極限 \`Andre.Transfinite.deltaDirectLimit\_isPerfect\`（DeltaPerfection:271）、古典的 $`p` 進完備化 \`DS.IsPerfect.adicCompletion\_span\_p\`（:310）、導来 $`(p,d)` 完備化の $`H^0` \`deltaPDCompletionStructure\_isPerfect\`（:375）がある（原典にない追加。第 3 章の Lemma 3.9 で使う）。右随伴 $`\lim_\varphi` は本体にない。

*注意 2.4.2（原典 Rem 2.27：完全化） — 証明*

$`\varphi` は δ 射（命題 2.1.5 (4)）なので、二つの図式は δ 環の図式であり、余極限・極限は下の環で計算される（命題 2.1.9）。*左側*：$`\mathrm{colim}_\varphi A` の Frobenius は各段で $`\varphi` を当てる写像で、段を一つずらす写像（第 $`n` 段の $`a` を第 $`n+1` 段の $`a` へ）がその両側逆になるので完全。完全 δ 環 $`P` への δ 射 $`f\colon A\to P` に対し、第 $`n` 段の写像を $`\varphi_P^{-n}\circ f` とすれば遷移と両立し（$`\varphi_P^{-(n+1)}\circ f\circ\varphi_A=\varphi_P^{-n}\circ f`）、延長が一つ得られる。一意性は、延長 $`g` が δ 射なら $`\varphi_P\circ g=g\circ\varphi` なので第 $`n` 段での値が $`\varphi_P^{-n}\circ f` に決まることから。*右側*：$`\lim_\varphi A=\{(a_0,a_1,\dots)\mid\varphi(a_{n+1})=a_n\}` で、Frobenius は成分ごとの $`\varphi`、逆は列を一つずらす写像。完全 δ 環 $`P` からの δ 射 $`g\colon P\to A` は $`x\mapsto(g(\varphi_P^{-n}x))_n` に一意に持ち上がる。

*注意 2.4.2（原典 Rem 2.27：完全化）*

原典はここで「Frobenius が p ねじれを殺すのがこの理論のよいところ」と述べて次の補題に進む。

:::

:::lemma_ "bs_2_28" (lean := "SerrePositivity.BhattScholze.DeltaStructure.torsion_calculation, SerrePositivity.BhattScholze.DeltaStructure.p_mul_injective_of_frobeniusLift_injective, SerrePositivity.BhattScholze.DeltaStructure.p_mul_injective_of_isReduced")
*補題 2.28*　p ねじれ。対応表の状態：本体にある。

*主張*　$`\delta` 環で Frobenius が単射であるか、台環が被約であれば、その環には $`p` ねじれがない。

同じ任意の δ 環について φ 注入または reduced の二つの場合の p 正則性を証明する。

*命題 2.4.3（原典 Lemma 2.28：δ 環の p ねじれ） — 主張*

δ 環 $`A` は、次のどちらかが成り立てば p ねじれなしである。

(1) Frobenius $`\varphi` が単射（たとえば $`A` が完全）。

(2) $`A` が被約。

*命題 2.4.3（原典 Lemma 2.28：δ 環の p ねじれ） — Lean*

$`px=0\Rightarrow\varphi(x)=0\wedge p^p\delta(x)=0` が \`DS.torsion\_calculation\`（PerfectDelta:50）。(1) \`DS.p\_mul\_injective\_of\_frobeniusLift\_injective\`（:86）、完全な場合 \`DS.IsPerfect.p\_mul\_injective\`（:96）。(2) \`DS.p\_mul\_injective\_of\_isReduced\`（PerfectDelta:102）。p ねじれなしは「$`p` 倍が単射」の形。同じ計算を指数について繰り返すと「$`p` が冪零な δ 環は零環」（原典 Ex 2.6 の末尾）\`DS.subsingleton\_of\_isNilpotent\_p\`（:126）。

*命題 2.4.3（原典 Lemma 2.28：δ 環の p ねじれ） — 証明*

(1) より強く、$`px=0` なら $`\varphi(x)=0` を示す。$`px=0` に δ を当てると、積公式から
$$`0=\delta(px)=p^p\delta(x)+x^p\delta(p)+p\,\delta(x)\delta(p)=p^p\delta(x)+\varphi(x)\delta(p).`
ここで
$$`p^p\delta(x)=p^{p-1}\big(\varphi(x)-x^p\big)=\varphi(p^{p-1}x)-p^{p-1}x^p`
は $`px=0` と $`p\ge2` から 0。よって $`\varphi(x)\delta(p)=0` で、$`\delta(p)=1-p^{p-1}` は $`\mathbb Z_{(p)}` 代数では単元なので $`\varphi(x)=0`。(2) $`px=0` とすると上で $`\varphi(x)=0`、$`p^p\delta(x)=0`。後者から $`(p\,\delta(x))^p=\delta(x)^{p-1}\cdot p^p\delta(x)=0` なので被約性から $`p\,\delta(x)=0`。すると $`x^p=\varphi(x)-p\,\delta(x)=0` で、再び被約性から $`x=0`。

*命題 2.4.3（原典 Lemma 2.28：δ 環の p ねじれ） — 原典との差（D4・D2）*

Lean は $`\mathbb Z_{(p)}` 代数を仮定しないので（D2）、$`\delta(p)` の単元性が使えない。代わりに $`\delta(p)-1\in(p)` \`DS.delta\_p\_sub\_one\_mem\`（Distinguished:54）と $`p\varphi(x)=\varphi(px)=0` を使う：$`\delta(p)-1=pr` と書けば
$$`\varphi(x)=\delta(p)\varphi(x)-r\cdot p\varphi(x)=0`
（D4）。$`p\in\mathrm{rad}(A)` も要らない。

:::

:::proposition "bs_2_29"
*注意 2.29*　Lemma 2.28 の仮定についての注意。対応表の状態：なし。

Frobenius 注入性と reduced 性が互いに導かないという原文の二反例を未同定。

*注意 2.4.4（原典 Rem 2.29：Lemma 2.28 の二つの仮定は比べられない） — 主張*

標数 $`p` の環では「被約 ⇔ Frobenius が単射」だが、δ 環では命題 2.4.3 の (1) と (2) はどちらも他方を導かない。

(a) $`A=\mathbb Z_p[x]/(x^p-1)` は被約で、$`\varphi(x)=x^p=1` となる δ 構造を持つ。このとき $`\varphi(x-1)=0` なので $`\varphi` は単射でない。

(b) $`B=\mathbb Z_p[x]/(x^2)` は被約でなく、$`\varphi(x)=px` となる δ 構造を持つ。$`a,b\in\mathbb Z_p` について $`\varphi(a+bx)=a+pbx` なので $`\varphi` は単射。

*注意 2.4.4（原典 Rem 2.29：Lemma 2.28 の二つの仮定は比べられない） — Lean*

二つの例そのものは本体にない。証明で使う「p ねじれなしの環では、Frobenius 持ち上げ $`\psi` ごとに $`\varphi=\psi` となる δ 構造がただ一つある」は本体にある：存在と一意性 \`existsUnique\_of\_frobeniusLift\`（DeltaRing:463）、一意性 \`eq\_of\_frobeniusLift\_eq\`（:220）（命題 2.1.3 (2)）。

*注意 2.4.4（原典 Rem 2.29：Lemma 2.28 の二つの仮定は比べられない） — 証明*

どちらも $`\mathbb Z_p` 上自由な加群なので p ねじれなしで、命題 2.1.3 (2) により、$`\psi(y)\equiv y^p\bmod p` を満たす環自己準同型 $`\psi` ごとに $`\varphi=\psi` となる δ 構造がただ一つある（$`\mathbb Z_p` 上ではどの環自己準同型も恒等写像）。(a) $`x\mapsto1` は $`1^p=1` なので環準同型で、$`A` では $`x^p=1` だから $`\varphi(x)\equiv x^p`。$`A\subset\mathbb Q_p[x]/(x^p-1)\cong\mathbb Q_p\times\mathbb Q_p(\zeta_p)` なので被約。(b) $`x\mapsto px` は $`(px)^2=0` なので環準同型で、$`x^p=0` かつ $`px\equiv0\bmod p`。$`x` は冪零で 0 でない。

原典の「ただ一つ」の読み方（補った）。(b) は原典どおり「$`\varphi(x)=px` となる δ 構造がただ一つ」で、上の一意性そのもの。Frobenius 持ち上げ自体は一つではなく、任意の $`c\in\mathbb Z_p` について $`x\mapsto pcx` も持ち上げ（$`c\ne0` なら単射）。(a) は「$`A` の δ 構造がただ一つ」と読めるが、それが正しいのは $`p` が奇素数のとき：$`\varphi(x)` は 1 の $`p` 乗根で $`\equiv1\bmod p` となるものに限られ、$`\mathbb Z_p[\zeta_p]` で $`\zeta_p^i-1` の付値は $`1/(p-1)\lt1` なので $`\varphi(x)=1` だけ。$`p=2` では $`\varphi(x)=-1` も持ち上げで、δ 構造は二つある（どちらも $`\varphi` は単射でないので、例としての主張は変わらない）。

:::

:::proposition "bs_2_30" (lean := "SerrePositivity.BhattScholze.DeltaStructure.torsion_calculation")
*注意 2.30*　導来 Frobenius 持ち上げによる説明。対応表の状態：一部（component）。

*主張*　$`A\otimes_{\mathbf Z}^{\mathbf L}\mathbf F_p` に誘導される Frobenius は、その単体的可換 $`\mathbf F_p` 代数自身の Frobenius で、正次数のホモトピー群の上で零になる。一次ホモトピー群を $`A[p]` と同一視すると、元の Frobenius が $`A[p]` を消すことが分かる。

導来 Frobenius による説明全体ではないが、明記された最終式 φ(A\[p\])=0 は torsion\_calculation の第一結論から同じ A で直接得られる。

*注意 2.4.5（原典 Rem 2.30：導来 Frobenius 持ち上げとしての説明） — 主張*

命題 2.4.3 (1) の「$`\varphi(A[p])=0`」は、$`\varphi` が導来の Frobenius 持ち上げ（原典 Rem 2.5）であることから概念的に分かる。δ 環 $`A` に対し、単体的可換 $`\mathbb F_p` 代数 $`B=A\otimes^L_{\mathbb Z}\mathbb F_p` をとると、$`\varphi` の底変換 $`\varphi_B\colon B\to B` は $`B` の Frobenius に一致する。単体的可換 $`\mathbb F_p` 代数の Frobenius は $`i\gt0` の $`\pi_i` で常に 0 である（\[BS17, Prop 11.6\]）から $`\pi_1(\varphi_B)=0`。一方 $`\mathbb F_p` の $`\mathbb Z` 上の標準分解 $`\mathbb Z\xrightarrow{p}\mathbb Z` で $`\pi_1(B)\cong A[p]` と $`\varphi` と両立する形で同一視できるので、$`\varphi(A[p])=0`。

:::

:::corollary "bs_2_31" (lean := "SerrePositivity.BhattScholze.DeltaStructure.IsPerfect.perfectRing_mod_p, SerrePositivity.BhattScholze.existsUnique_wittDeltaStructure, SerrePositivity.BhattScholze.perfectDeltaWittRecoveryEquiv, SerrePositivity.BhattScholze.wittDeltaStructure_ringHom_isDeltaHom_of_complete, SerrePositivity.BhattScholze.perfectSource_ringHom_isDeltaHom")
*系 2.31*　完全 δ 環 ↔ 完全 F\_p 代数。対応表の状態：一部（component）。

*主張*　完全 $`p` 完備 $`\delta` 環、$`p` 進完備で $`p` ねじれがなく剰余環が完全な環、完全 $`\mathbf F_p` 代数の三つの圏は同値である。最初の同値は忘却、残りは $`p` での剰余と Witt ベクトルで与えられる。

完全 p 完備 δ 環を W(A/p) から回収する同型、剰余環の perfect 性、環準同型の δ 適合性を対象ごとに与える。三つの圏の関手と自然同型からなる圏同値全体は未供給。

*系 2.4.6（原典 Cor 2.31：完全 δ 環） — 主張*

次の三つの圏は同値である。

(1) 完全 $`p` 完備 δ 環の圏 $`C_1`。

(2) $`p` 進完備で p ねじれなし、かつ $`A/p` が完全な環 $`A` の圏 $`C_2`。

(3) 完全 $`\mathbb F_p` 代数の圏 $`C_3`。

(1) と (2) の間は忘却関手で、特に完全 $`p` 完備 δ 環の間の*任意の環準同型は自動的に δ 射*。(2) と (3) の間は $`A\mapsto A/p` と $`R\mapsto W(R)` で、特に標数 $`p` の完全環 $`R` について $`W(R)` 上の δ 構造はただ一つ。

*系 2.4.6（原典 Cor 2.31：完全 δ 環） — Lean*

圏同値としてではなく、対象ごと・射ごとの部品で。

$`C_1\to C_2`：p ねじれなしは命題 2.4.3、$`A/p` の完全性 \`DS.IsPerfect.perfectRing\_mod\_p\`（PerfectDelta:243）（完備性は不要）。

$`C_3\to C_1`：Witt Frobenius を持ち上げとする δ 構造の存在と一意性 \`existsUnique\_wittDeltaStructure\`（PerfectDelta:349）、標準構造 \`wittDeltaStructure\`（:367）、完全性 \`wittDeltaStructure\_isPerfect\`（:376）、$`p` 進完備性 \`wittDeltaStructure\_isAdicComplete\`（:382）、一意性 \`wittDeltaStructure\_unique\`（:386）、関手性 $`W(f)` が δ 射 \`wittDeltaStructure\_map\_isDeltaHom\`（:392）。

$`C_1\cong W(C_3)`：復元同型 $`W(A/p)\cong A` \`perfectDeltaWittRecoveryEquiv\`（PerfectDelta:419）（零環も含む）、その mod $`p` が第 0 Witt 座標 \`perfectDeltaWittRecoveryEquiv\_mod\_p\`（:425）、順・逆が δ 射 \`perfectDeltaWittRecoveryEquiv\_isDeltaHom\`（:457）・\`perfectDeltaWittRecoveryEquiv\_symm\_isDeltaHom\`（:467）（$`A/p` が標数 $`p`、すなわち $`A\ne0` のとき）。復元そのものは共通基盤の strict p 環の復元 \`strictPRecoveryEquiv\`（Lift:250）。

*射*：$`W(k)` から p ねじれなし $`p` 進完備 δ 環への任意の環準同型は δ 射 \`wittDeltaStructure\_ringHom\_isDeltaHom\_of\_complete\`（PerfectDelta:434）。証明は $`f\circ\varphi_W` と $`\varphi_A\circ f` が mod $`p` で一致することと、mod $`p` で一致する $`W(k)\to A` は等しいこと \`wittLift\_unique\`（Lift:74）（Teichmüller 元で比べて $`p` 進分離性で極限へ）から $`\varphi` と可換になり、終域が p ねじれなしなので命題 2.1.5 (3)。より一般に「完全 δ 環から $`p` 進分離な δ 環への任意の環準同型は δ 射」が \`Andre.perfectSource\_ringHom\_isDeltaHom\`（PerfectPrismHomLift:343）（終域の p ねじれなしも不要。原典 Lemma 4.8 のために第 4 章側にある）。

*系 2.4.6（原典 Cor 2.31：完全 δ 環） — 証明*

命題 2.4.3 により δ 構造を忘れる関手 $`F_{12}\colon C_1\to C_2` が定まる（$`A/p` の完全性は、$`\varphi` が $`A/p` の Frobenius を誘導し、$`\varphi` が全単射で $`\varphi(pA)=p\varphi(A)=pA` なので $`\varphi^{-1}(pA)=pA` となることから）。$`F_{12}` は定義から忠実。$`F_{23}\colon C_2\to C_3` は $`A\mapsto A/p`、$`F_{31}\colon C_3\to C_1` は $`R\mapsto W(R)`（Witt 環の Frobenius を $`\varphi` とする δ 構造。$`W(R)` は p ねじれなしで Frobenius は mod $`p` で $`p` 乗なので命題 2.1.3 (2) から）。$`F_{32}:=F_{12}\circ F_{31}` が $`F_{23}` の逆であることはよく知られている（変形理論など。$`p` 進完備で p ねじれなしの $`A` で $`A/p=R` 完全なら $`W(R)\cong A`）。同値 $`F_{32}` が忠実な $`F_{12}` を経由するので、$`F_{12}` も同値になる。これが「環準同型は自動的に δ 射」の意味。

*系 2.4.6（原典 Cor 2.31：完全 δ 環） — 原典との差*

原典は三つの圏の同値として述べ、$`W(R)\cong A` を「よく知られている（変形理論）」で済ませる。Lean は圏や関手を立てず、対象の対応（$`A/p` の完全性、$`W(k)` の δ 構造、復元同型 $`A\cong W(A/p)`）と射の性質（環準同型が δ 射、$`W(f)` が δ 射）を個別の定理として持つ。復元は変形理論ではなく、Teichmüller 元による $`W(k)\to A` の構成（Fontaine の θ）と $`p` 進完備性で単射・全射を示す共通基盤による。

:::

:::lemma_ "bs_2_32" (lean := "SerrePositivity.BhattScholze.DeltaStructure.pow_p_dvd_delta_pow, SerrePositivity.BhattScholze.DeltaStructure.delta_eq_zero_of_has_pow_roots")
*補題 2.32*　完全な元は rank 1。対応表の状態：本体にある。

*主張*　任意の $`\delta` 環で $`\delta(x^{p^n})\in p^nA` が成り立つ。従って $`p` 進分離な $`\delta` 環であらゆる $`p^n` 乗根をもつ元 $`y` は、$`\delta(y)=0` を満たす。

同じ x の δ(x\^(p\^n)) の p\^n 可除性と、p 分離・全 p 冪根存在下の δ(y)=0 に一致。

*命題 2.4.7（原典 Lemma 2.32：完全な元は rank 1） — 主張*

δ 環 $`A` と $`x\in A` について、任意の $`n` で $`\delta(x^{p^n})\in p^nA`。特に $`A` が $`p` 進分離で、$`y\in A` がすべての $`n\ge0` について $`p^n` 乗根を持つなら $`\delta(y)=0`、すなわち $`y` は rank 1。

後半は何らかの $`p` 局所性がないと成り立たない：環 $`\mathbb Q[x^{1/p^\infty}]` の任意の自己準同型が δ 構造を定めるが、$`x` を rank 1 にするものはごく少ない。たとえば Frobenius を恒等写像にとると $`\delta(x)=(x-x^p)/p\ne0`。

*命題 2.4.7（原典 Lemma 2.32：完全な元は rank 1） — Lean*

前半 \`DS.pow\_p\_dvd\_delta\_pow\`（PerfectDelta:208）、後半 \`DS.delta\_eq\_zero\_of\_has\_pow\_roots\`（:214）（根の両立性は仮定しない）。前半はより強い $`p^n\delta(x)\mid\delta(x^{p^n})` \`DS.pow\_mul\_delta\_dvd\_delta\_pow\`（:197）から出し、それは一段の $`p\,\delta(x)\mid\delta(x^p)` \`DS.p\_mul\_delta\_dvd\_delta\_pow\`（PerfectDelta:159）の反復（$`x` を $`x^{p^n}` に替えて当てる）。後半は完全 $`W(k)` の Teichmüller 元が rank 1 であること \`wittDeltaStructure\_delta\_teichmuller\`（:494）に使われる。

*命題 2.4.7（原典 Lemma 2.32：完全な元は rank 1） — 証明*

後半は前半から：$`y=x_n^{p^n}` なら $`\delta(y)\in\bigcap_np^nA=0`。前半は Lemma 2.11 の普遍的な場合（自由 δ 環 $`\mathbb Z_{(p)}\{x\}`）に帰着して $`A` は p ねじれなしとしてよい。すると $`\delta(x^{p^n})\in p^nA` は $`p\,\delta(x^{p^n})\in p^{n+1}A`、すなわち $`\varphi(x^{p^n})\equiv x^{p^{n+1}}\bmod p^{n+1}` と同値。$`n=0` は定義そのもの。一般に $`a\equiv b\bmod p^k`（$`k\ge0`）なら二項定理で $`a^p\equiv b^p\bmod p^{k+1}` なので、$`\varphi(x)\equiv x^p\bmod p` にこれを $`n` 回使えば $`\varphi(x^{p^n})=\varphi(x)^{p^n}\equiv x^{p^{n+1}}\bmod p^{n+1}`。

*命題 2.4.7（原典 Lemma 2.32：完全な元は rank 1） — 原典との差*

Lean は自由 δ 環への帰着をせず、p ねじれのある $`A` で直接示す。商 $`\bar A=A/(p\,\delta(x))` では積公式の第 3 項 $`p\,\delta(a)\delta(x)` が消えるので、$`\delta(x^{m+1})=x^{pm}\delta(x)+x^p\delta(x^m)`（$`\bar A` で）となり、帰納法で $`\delta(x^{m+1})\equiv(m+1)\,x^{pm}\delta(x)`（微分の公式と同じ形）。$`m+1=p` とおけば $`\delta(x^p)\equiv p\,x^{p(p-1)}\delta(x)\equiv0`。

:::

:::lemma_ "bs_2_33" (lean := "SerrePositivity.BhattScholze.wittDeltaStructure_isDistinguished_iff, SerrePositivity.BhattScholze.wittDeltaStructure_isDistinguished_iff_teichmuller_coefficient")
*補題 2.33*　Teichmüller 係数による判定。対応表の状態：一部（special）。

*主張*　完全 $`p` 完備 $`\delta` 環で元 $`d` が distinguished であることは、その Teichmüller 展開の $`p` の係数が単元であることに等しい。

A=W(k) の標準 δ 構造に限定して同じ Teichmüller 第1係数の単元性 iff distinguished を証明する。一般の完全 A への輸送はここでは数えない。

*命題 2.4.8（原典 Lemma 2.33：完全 δ 環の distinguished 元） — 主張*

$`A` を完全 $`p` 完備 δ 環、$`d\in A` とする。$`d` が distinguished であることと、$`d` の Teichmüller 展開（系 2.4.6 による $`A=W(R)`）の $`p` の係数が単元であることは同値。

*命題 2.4.8（原典 Lemma 2.33：完全 δ 環の distinguished 元） — Lean*

$`A=W(k)`（$`k` は標数 $`p` の完全環）と標準 δ 構造の場合。Teichmüller 係数の形 \`wittDeltaStructure\_isDistinguished\_iff\_teichmuller\_coefficient\`（PerfectDelta:557）、Witt 座標の形 \`wittDeltaStructure\_isDistinguished\_iff\`（:543）。鍵は「$`\delta(d)` の第 0 Witt 座標 ＝ $`d` の第 1 Witt 座標」\`wittDeltaStructure\_delta\_coeff\_zero\`（:505）：$`d=[d_0]+py` と書き、$`[d_0]` は rank 1（命題 2.4.7）、加法公式の補正項は mod $`p` で消え、$`\delta(py)\equiv y^p\delta(p)\equiv y^p`、一方 $`d_1=\bar y^p`。単元判定は「第 0 座標が単元な Witt ベクトルは単元」\`PerfectoidFrobeniusCriterion.witt\_isUnit\_of\_constantCoeff\`（Fontaine:134）。

*命題 2.4.8（原典 Lemma 2.33：完全 δ 環の distinguished 元） — 証明*

$`R` を完全 $`\mathbb F_p` 代数、$`A=W(R)` とし、$`d=\sum_{i\ge0}[a_i]p^i` と展開する。$`\varphi([a])=[a]^p` なので
$$`\delta(d)=\frac1p\Big(\sum_{i\ge0}[a_i]^pp^i-\Big(\sum_{i\ge0}[a_i]p^i\Big)^p\Big).`
右辺の括弧の中を mod $`p^2` で見ると、$`\big(\sum[a_i]p^i\big)^p\equiv[a_0]^p`（二項定理で $`p\cdot[a_0]^{p-1}\cdot p[a_1]` 以下は $`p^2` で割れる）なので、括弧の中は $`\equiv p[a_1]^p\bmod p^2`。よって $`\delta(d)\equiv a_1^p\bmod pA`。$`A` は $`p` 完備なので $`\delta(d)` が単元 ⇔ $`\delta(d)\bmod p` が単元 ⇔ $`a_1` が単元。

*命題 2.4.8（原典 Lemma 2.33：完全 δ 環の distinguished 元） — 原典との差*

原典は任意の完全 $`p` 完備 δ 環で述べ、系 2.4.6 で $`W(R)` に移す。Lean は $`W(k)` の標準 δ 構造の場合だけで、一般の $`A` へ移す形（復元同型 \`perfectDeltaWittRecoveryEquiv\` を通す）は立てていない。Mathlib の Witt 座標 $`d=(d_0,d_1,\dots)` は $`d=\sum_iV^i[d_i]=\sum_i[d_i^{1/p^i}]p^i` なので、原典の Teichmüller 係数は $`a_1=d_1^{1/p}`（Lean では $`\mathrm{frobeniusEquiv}^{-1}(d_1)`）。原典の $`\delta(d)\equiv a_1^p` は Lean の $`\delta(d)_0=d_1` と同じことで、単元性は $`p` 乗で変わらない。

:::

:::lemma_ "bs_2_34" (lean := "SerrePositivity.BhattScholze.DeltaStructure.IsDistinguished.mul_injective, SerrePositivity.BhattScholze.DeltaStructure.IsPerfect.distinguished_mul_injective, SerrePositivity.BhattScholze.DeltaStructure.IsDistinguished.quotient_p_pow_torsion_killed_by_p")
*補題 2.34*　d は非零因子、R\[p\]=R\[p\^∞\]。対応表の状態：本体にある。

*主張*　$`p` ねじれがなく $`p` 進分離で、$`A/p` が被約な $`\delta` 環 $`A` をとる。distinguished 元 $`d` は非零因子であり、$`A/d` の $`p` 冪ねじれはすべて $`p` で消える。

同じ p 正則・p 分離・A/p reduced の条件から d の正則性と A/d の全 p 冪ねじれを p が消す二結論。

*命題 2.4.9（原典 Lemma 2.34） — 主張*

$`A` を p ねじれなしで $`p` 進分離、$`A/p` が被約な δ 環とする（たとえば完全 $`p` 完備な δ 環）。$`d\in A` が distinguished なら

(1) $`d` は $`A` の非零因子。

(2) $`R=A/d` の $`p^\infty` ねじれは有界で、実際 $`R[p]=R[p^\infty]`。

*命題 2.4.9（原典 Lemma 2.34） — Lean*

仮定は原典どおり（$`A/p` 被約、$`p` 進分離、$`p` 倍が単射）。(1) \`DS.IsDistinguished.mul\_injective\`（DistinguishedRegular:64）。核心は「$`fd=0\Rightarrow p\mid f`」\`DS.p\_dvd\_of\_mul\_distinguished\_eq\_zero\`（:41）で、それを繰り返して $`p^n\mid f`（$`f=pr` なら p ねじれなしで $`rd=0`）、分離性で $`f=0`。完全な場合 \`DS.IsPerfect.distinguished\_mul\_injective\`（:96）（$`A/p` の被約性は完全性から）。(2) \`DS.IsDistinguished.quotient\_p\_pow\_torsion\_killed\_by\_p\`（DistinguishedRegular:196）（$`R` で $`p^Nx=0` なら $`px=0`。(2) には $`p` 進分離性を使わない）、核心 \`DS.p\_dvd\_of\_p\_sq\_mul\_eq\_mul\_distinguished\`（:131）、$`d\mid p^2f\Rightarrow d\mid pf` \`DS.IsDistinguished.dvd\_p\_mul\_of\_dvd\_p\_sq\_mul\`（:157）、指数の帰納 \`DS.IsDistinguished.dvd\_p\_mul\_of\_dvd\_p\_pow\_mul\`（:174）、完全な場合 \`DS.IsPerfect.distinguished\_quotient\_p\_pow\_torsion\_killed\_by\_p\`（:216）。原典にない追加として、冪 $`d^n` の商 $`A/d^n` の $`p^\infty` ねじれは $`p^n` で消える \`DS.IsDistinguished.quotient\_power\_p\_pow\_torsion\_killed\_by\_p\_pow\`（:283）（$`d` の正則性を仮定）・完全な場合（:301）、完全 $`p` 完備なら $`A/d`・$`A/d^k` は古典的に $`p` 進完備 \`DS.IsPerfect.distinguished\_quotient\_isAdicComplete\`（:332）・\`DS.IsPerfect.distinguished\_power\_quotient\_isAdicComplete\`（:341）（第 3 章の Thm 3.10 の証明で使う）。

*命題 2.4.9（原典 Lemma 2.34） — 証明*

(1) $`fd=0` で $`f\ne0` とする。$`A` は p ねじれなしで $`p` 進分離なので、$`f` を $`p` の冪で割って $`p\nmid f` としてよい。$`fd=0` に δ を当てると $`f^p\delta(d)+\delta(f)\varphi(d)=0`（$`d^p\delta(f)+p\,\delta(f)\delta(d)=\delta(f)\varphi(d)`）。$`\varphi(f)` を掛けて $`\varphi(f)\varphi(d)=\varphi(fd)=0` を使うと $`f^p\varphi(f)\delta(d)=0`、$`\delta(d)` は単元なので $`f^p\varphi(f)=0`。mod $`p` では $`\varphi(f)\equiv f^p` なので $`f^{2p}\equiv0`、$`A/p` は被約（Frobenius が単射）なので $`f\equiv0\bmod p`。これは $`p\nmid f` に反する。

(2) $`R[p]=R[p^2]` を示せば十分（帰納法で $`R[p^n]=R[p]`）。$`A` に持ち上げると、$`p^2f=gd` なら $`p\mid g` を示せばよい（そうなら $`g=pg'` で、p ねじれなしから $`pf=g'd\in dA`）。$`gd\in p^2A` に δ を当てると $`\delta(p^2A)\subset pA` なので $`\delta(d)g^p+\delta(g)\varphi(d)\in pA`。$`\varphi(g)` を掛けて $`\varphi(dg)\in\varphi(p^2A)\subset pA` を使うと $`\delta(d)g^p\varphi(g)\in pA`、$`\delta(d)` は単元なので $`g^p\varphi(g)\in pA`、よって $`g^{2p}\in pA`。$`A/p` の Frobenius は単射なので $`g\in pA`。

:::

:::lemma_ "bs_2_35" (lean := "SerrePositivity.BhattScholze.DeltaStructure.factorial_dvd_pow_of_prime_dvd_pow, SerrePositivity.BhattScholze.DeltaStructure.exists_factorial_quotient_mem")
*補題 2.35*　γ\_p から全 γ\_n。対応表の状態：本体にある。

*主張*　$`p` ねじれのない $`\delta` 環 $`A` で $`z\in A` の分割冪 $`\gamma_p(z)` が $`A` に属するなら、すべての $`n\ge0` で $`\gamma_n(z)\in A` となる。

Z\_(p)-代数の同じ z で p\|z\^p から n!\|z\^n を示す。p 正則なら分数体内の γ\_n(z) の所属という原文に戻る。さらに pd ideal 内の値も与える。

*命題 2.5.1（原典 Lemma 2.35） — 主張*

$`A` を $`p` ねじれなしの δ 環とし、$`z\in A` が $`\gamma_p(z)\in A` を満たすとする。このとき任意の $`n\ge0` で $`\gamma_n(z)\in A`。

*命題 2.5.1（原典 Lemma 2.35） — Lean*

\`DS.factorial\_dvd\_pow\_of\_prime\_dvd\_pow\`（Factorial:316）：非 $`p` 倍の自然数が単元の δ 環で、$`p\mid x^p` なら任意の $`n` で $`n!\mid x^n`。手順 (i) は \`DS.prime\_dvd\_divided\_pow\`（:209）で、$`x^p=pz` なら $`p\mid z^p`（$`p` 正則性も $`p` 局所性も使わない）。商も同じイデアルに取れる形 \`DS.exists\_factorial\_quotient\_mem\`（:391）。これを使って、$`p` 局所・$`p` 正則な δ 環のイデアル $`\{x\mid p\mid x^p\}`（\`DS.primeDividedPowerIdeal\`、:349）の上の分冪構造 \`DS.primeDividedPowers\`（:474）とその一意性 \`DS.primeDividedPowers\_unique\`（:509）も作る。

*命題 2.5.1（原典 Lemma 2.35） — 証明*

\*\*(i) $`\gamma_p(z)` もまた条件を満たす。\*\* $`\mathrm{val}_p((p^2)!)=p+1` なので、示すべきは $`z^{p^2}/p^{p+1}\in A`（同じことだが $`\gamma_p(\gamma_p(z))\in A`。$`\gamma_p(\gamma_p(z))` と $`\gamma_{p^2}(z)` は $`\mathbb Z_{(p)}` の単元倍の違い）。$`z^p/p\in A` なので $`\delta(z^p/p)\in A` で、$`\varphi` の定義から
$$`\delta\Big(\frac{z^p}{p}\Big)=\frac1p\Big(\frac{\varphi(z)^p}{p}-\frac{z^{p^2}}{p^p}\Big)=\frac{(z^p+p\delta(z))^p}{p^2}-\frac{z^{p^2}}{p^{p+1}}.`
$`\frac{z^p+p\delta(z)}{p}=\frac{z^p}{p}+\delta(z)\in A` なので $`\frac{(z^p+p\delta(z))^p}{p^2}=p^{p-2}\big(\frac{z^p+p\delta(z)}{p}\big)^p\in A`（$`p\ge2`）。よって $`z^{p^2}/p^{p+1}\in A`。

\*\*(ii) $`n` についての帰納法.\*\* 「$`\gamma_p(y)\in A`」を満たす $`y` を許容的と呼び、すべての許容的な $`y` と $`m<n` で $`\gamma_m(y)\in A` と仮定する。$`p\nmid n` なら $`\gamma_n(z)=\gamma_{n-1}(z)\cdot z/n` で $`n` は $`\mathbb Z_{(p)}` の単元なので済む。$`n=kp`（$`k<n`）なら、恒等式 $`\gamma_{kp}=u\cdot\gamma_k\circ\gamma_p`（$`u\in\mathbb Z_{(p)}^\times`）を使う。これは $`\mathrm{val}_p((kp)!)=k+\mathrm{val}_p(k!)=\mathrm{val}_p\big((p!)^k\,k!\big)` から出る。(i) により $`\gamma_p(z)` は許容的なので、帰納法の仮定から $`\gamma_k(\gamma_p(z))\in A`、よって $`\gamma_n(z)\in A`。

*命題 2.5.1（原典 Lemma 2.35） — 原典との差*

Lean は結論を「$`n!\mid x^n`」（割り切れる）で述べるので、$`p` ねじれなしを仮定しない（$`p` ねじれがあると商 $`x^n/n!` は一意でないが、存在は言える）。代わりに原典が暗に使う $`p` 局所性（$`p\nmid n` の $`n` が単元）を明示の仮定にする。帰納法は $`n=p\lfloor n/p\rfloor+(n\bmod p)` と $`\mathrm{val}_p(n!)=\mathrm{val}_p(\lfloor n/p\rfloor!)+\lfloor n/p\rfloor` による強帰納で、原典の $`\gamma_{kp}=u\,\gamma_k\circ\gamma_p` と同じ計算。分冪構造としての形は原典にない。

:::

:::lemma_ "bs_2_36"
*補題 2.36*　A\{φ(x)/p\} ＝ pd 包。対応表の状態：なし。

候補は同じ通常の δ 除算環と DPFamilyPresentation・階乗部分環の同型。原文の universal PD-envelope D\_(x) への分冪構造・普遍 PD 射としての指定同定は未同定で、別の表示環との環同型だけを C≅D の component としない。

*命題 2.5.2（原典 Lemma 2.36） — 主張*

δ 環の押し出しの四角
$$`\begin{array}{ccc}\mathbb Z_{(p)}\{y\}&\xrightarrow{\ y\mapsto pz\ }&\mathbb Z_{(p)}\{z\}\\ {\scriptstyle y\mapsto\varphi(x)}\downarrow&&\downarrow\\ \mathbb Z_{(p)}\{x\}&\longrightarrow&\mathbb Z_{(p)}\{x,z\}/(\varphi(x)-pz)_\delta=:C\end{array}`
で定まる環 $`C=\mathbb Z_{(p)}\{x,\varphi(x)/p\}` は、pd 包 $`D:=D_{(x)}(\mathbb Z_{(p)}\{x\})` と一致する。

*命題 2.5.2（原典 Lemma 2.36） — Lean*

二つの形で持つ。

*像の形*（任意の $`p` 局所 δ 環 $`A` と任意の元族 $`y=(y_s)`）。生の包 $`A\{\varphi(y)/p\}` から $`A[1/p]` への δ 射 \`deltaPDivisionToAway\`（PDivision:181）の像が、$`A` と全 $`\gamma_n(y_s)` で生成される部分環 \`pDivisionFactorialSubring\`（:476）に一致する \`pDivisionFactorialSubring\_eq\_raw\_range\`（:749）。$`C[1/p]=A[1/p]` は \`deltaPDivisionLocalizationEquiv\`（:291）。(c) は \`pDivisionFactorialSubring\_le\_raw\_range\`（:510）。(d) の δ 安定性は \`pDivisionFactorialSubring\_delta\_mem\`（:738）で、生成元の δ の展開 \`pDivisionFactorialValue\_delta\_expansion\`（:605）と、「生成元の δ が生成部分環に入れば部分環全体が δ で閉じる」\`delta\_mem\_subringClosure\`（:703）から出す。展開の係数の $`p` 整性は \`dividedPowerFrobeniusCoefficient\_valuation\_nonneg\`（Factorial:69）・\`dividedPowerPowerCoefficient\_valuation\_nonneg\`（:95）で、それぞれ $`\varphi(\gamma_n)/p` の係数 $`\frac{(pi)!}{i!}\cdot\frac{p^{n-i}}{(n-i)!}\cdot\frac1p` と $`\gamma_n^p/p` の係数 $`\frac{(pn)!}{(n!)^p\,p}`。最小性 \`deltaPDivisionToAway\_range\_le\_of\_delta\_stable\`（PDivision:425）。$`\varphi(y)/p\leftrightarrow y^p/p` の書き換えは生の包どうしの δ 同型 \`deltaPDivisionFrobeniusShiftEquiv\`（PDivisionCompletion:133）。

*原典の形*（生の包そのもの）。(a) の $`p` ねじれなし：係数 $`R` 上の自由 δ 環 $`A=R\{x_s\}` が $`p` 正則で $`A/p` が $`\mathbb F_p` 上の多項式環なら、任意個の座標について $`A\{\varphi(x)/p\}` は $`p` 正則 \`freeCoordinateFrobeniusDivision\_primeRegular\`（FrobeniusDivisionPD:119）。$`p` 正則な生の包と部分環の環同型 \`frobeniusDivisionFactorialEquiv\`（:167）（単射性は \`deltaPDivisionToAway\_injective\_of\_p\_mul\_injective\`、Andre/Envelope/PDivision:516）。有限個の座標で、係数が $`p` 局所・$`p` 正則・$`R/p\cong\mathbb F_p` のとき、分冪表示（命題 2.5.4 の $`D'`）との係数上の同型 \`freeCoordinateFrobeniusDivisionPDEquiv\`（FrobeniusDivisionRegularSequence:119）。

*命題 2.5.2（原典 Lemma 2.36） — 証明*

\*\*(a) $`C` の記述.\*\* 左の縦の射は（$`y` と $`x` を同一視すれば）$`\mathbb Z_{(p)}\{x\}` の $`\varphi` そのもので、Lemma 2.11（命題 2.1.14）により忠実平坦。押し出しで右の縦の射も忠実平坦なので、$`\mathbb Z_{(p)}\{z\}` とともに $`C` も $`p` ねじれなし。上の横の射は $`p` を逆にすると同型なので下の横の射も同型で、$`C\subset C[1/p]=\mathbb Z_{(p)}\{x\}[1/p]`。よって $`C` は $`\mathbb Z_{(p)}\{x\}[1/p]` の中で $`\mathbb Z_{(p)}\{x\}` と $`\varphi(x)/p` を含む最小の δ 部分環。$`\varphi(x)/p=x^p/p+\delta(x)` なので、$`x^p/p` を含む最小の δ 部分環と言っても同じ。

\*\*(b) $`D` の記述.\*\* $`x` は自由変数なので $`D` は $`p` ねじれなし（標準的事実）で、$`\mathbb Z_{(p)}\{x\}[1/p]` の中で $`\mathbb Z_{(p)}\{x\}` と全 $`\gamma_n(x)`（$`n\ge1`）で生成される部分環。

\*\*(c) $`D\subset C`\*\* は命題 2.5.1（$`C` は $`p` ねじれなしの δ 環で $`\gamma_p(x)\in C`）。

\*\*(d) $`C\subset D`.\*\* $`x^p/p\in D` なので、$`D` が δ 部分環であること、すなわち $`\varphi` が $`D` を保ち、$`D` 上で Frobenius 持ち上げになることを示せばよい（$`D` は $`p` ねじれなしなので命題 2.1.3 (2) で δ 構造が決まる）。
$$`\varphi\Big(\frac{x^n}{n!}\Big)=\frac{(x^p+p\delta(x))^n}{n!}=\sum_{i=0}^n\frac{\binom ni(pi)!\,p^{n-i}}{n!}\cdot\frac{x^{pi}}{(pi)!}\cdot\delta(x)^{n-i},\qquad \frac{\binom ni(pi)!\,p^{n-i}}{n!}=\frac{(pi)!}{i!}\cdot\frac{p^{n-i}}{(n-i)!}.`
右の二つの因子はどちらも $`\mathbb Z_{(p)}` に入り、第一因子は $`i>0` で、第二因子（$`p` の分冪 $`\gamma_{n-i}(p)`）は $`i<n` で $`p` で割れる。よって $`\varphi` は $`D` を保ち、$`n>0` で $`\varphi(\gamma_n(x))\equiv0\bmod pD`。また $`\gamma_n(x)^p=p!\cdot\gamma_p(\gamma_n(x))\equiv0\bmod pD`（$`n>0`）。したがって $`D` の上の $`\varphi` は生成元 $`\mathbb Z_{(p)}\{x\}` と $`\gamma_n(x)` の上で $`\bmod p` の Frobenius に一致し、$`\bmod p` の Frobenius は環準同型なので $`D` 全体で一致する。

*命題 2.5.2（原典 Lemma 2.36） — 原典との差*

原典は普遍な場合 $`\mathbb Z_{(p)}\{x\}` だけを述べる。Lean の像の形は一般の $`p` 局所 δ 環と任意の元族で述べ、$`A` の $`p` ねじれなしを仮定しない（像は $`A[1/p]` の中で取る）。δ 安定性は原典の「$`\varphi` が Frobenius 持ち上げ」の議論ではなく、生成元の δ を直接展開して示す（二つの係数の $`p` 整性は原典の計算と同じ）。

(a) の $`p` ねじれなしは、原典は Lemma 2.11 の Frobenius の忠実平坦性から出すが、Lean は二段で出す：座標そのものを $`p` で割る包 $`A\{x/p\}` は再び自由 δ 環で $`p` 正則（\`freeCoordinatePDivisionEquiv\`、FrobeniusDivisionPD:59）、$`A\{\varphi(x)/p\}` はそれを $`\varphi` に沿って押し出した通常の環の押し出しで（\`deltaAdjoinDivisionBaseChange\_isPushout\`、BaseChange:95）、$`\varphi` は $`p` 完全平坦（\`crystallineCompletelyFlat\_frobenius\`、CrystallineTensorRegularity:206）なので $`p` 正則性が移る（\`crystallinePrimeRegular\_of\_isPushout\`、:256）。pd 包 $`D` は、部分環としては階乗部分環、環の表示としては命題 2.5.4 の分冪表示で表す。

宣言：`SerrePositivity.BhattScholze.frobeniusDivisionFactorialEquiv`、`SerrePositivity.BhattScholze.freeCoordinateFrobeniusDivision_primeRegular`、`SerrePositivity.BhattScholze.freeCoordinateFrobeniusDivisionPDEquiv`

:::

:::proposition "bs_2_37"
*注意 2.37*　導来 pushout の離散性。対応表の状態：なし。

通常環の TorAlg 消滅と通常の pushout の普遍性はあるが、原文の SCR の homotopy pushout との比較宣言は未同定。両者の識別を部品だけから既証明としない。

*注意 2.5.3（原典 Rem 2.37） — 主張*

命題 2.5.2 の証明は、$`\mathbb Z_{(p)}\{x\}` に $`\varphi(x)/p` を自由に添加した単体的可換環が離散であること、つまり命題 2.5.2 の四角が単体的可換環の ∞ 圏でも押し出しであることも示している。したがってそれは上の環 $`\mathbb Z_{(p)}\{x,\varphi(x)/p\}\simeq D_{(x)}(\mathbb Z_{(p)}\{x\})` に一致する。

*注意 2.5.3（原典 Rem 2.37） — Lean*

$`P=\mathbb Z_{(p)}\{x_s\}`（任意個の座標、\`PrimeLocalFreeDeltaRing\`、FrobeniusPushout:138）の二脚 $`\varphi` と $`y_s\mapsto pz_s` について、通常の環の高次 Tor が消える \`frobeniusDivisionPushout\_torAlg\_subsingleton\`（:314）。零次：生の δ 商 \`FrobeniusDivisionPushoutRaw\`（:374）は二脚の通常の環の押し出しの普遍性を持つ \`existsUnique\_frobeniusDivisionPushoutLift\`（:398）（試験環に δ 構造を要求しない）。

*注意 2.5.3（原典 Rem 2.37） — 証明*

導来押し出しの高次ホモトピーは $`\mathrm{Tor}^{\mathbb Z_{(p)}\{y\}}_{i}(\mathbb Z_{(p)}\{x\},\mathbb Z_{(p)}\{z\})`（$`i>0`）で、左の脚 $`\varphi` が平坦なので消える。零次は通常の押し出しで、それが $`C`（δ 環の押し出しは通常の環の押し出しで計算される）。

*注意 2.5.3（原典 Rem 2.37） — 原典との差*

単体的可換環の押し出しではなく、高次 Tor の消滅と零次の押し出しの同定の二つで述べる。Tor の消滅の証明は原典の忠実平坦性ではなく、$`P` の $`p` 正則性、$`\varphi` 脚の $`p` 完全平坦性、$`p` を逆にするともう一方の脚が平坦になることの三つを合わせる。

宣言：`SerrePositivity.BhattScholze.frobeniusDivisionPushout_torAlg_subsingleton`、`SerrePositivity.BhattScholze.existsUnique_frobeniusDivisionPushoutLift`

:::

:::lemma_ "bs_2_38"
*補題 2.38*　正則列の pd 包。対応表の状態：なし。

通常の DPFamilyPresentation の p 正則性・底変換と Tor 消滅は本体にあるが、原文の SCR の derived pushout D⁰ および universal PD-envelope との指定同定は未同定。同じ対象への比較を欠く証明部品を partial としない。

*命題 2.5.4（原典 Lemma 2.38。正則列の pd 包） — 主張*

$`B` を $`p` ねじれなしの環とし、$`f_1,\dots,f_r\in B` が $`B/p` 上 Koszul 正則な列を与えるとする。単体的可換環の ∞ 圏での押し出し
$$`\begin{array}{ccc}\mathbb Z_{(p)}[x_1,\dots,x_r]&\xrightarrow{\ x_i\mapsto f_i\ }&B\\ \downarrow&&\downarrow\\ D_{(x_1,\dots,x_r)}(\mathbb Z_{(p)}[x_1,\dots,x_r])&\longrightarrow&D'\end{array}`
で $`D'` を定める。このとき $`D'` は離散・$`p` ねじれなしで、pd 包 $`D_{(f_1,\dots,f_r)}(B)` と同一視される。特に後者も $`p` ねじれなしで、その作り方は、$`f_1,\dots,f_r` が $`B'/p` 上 Koszul 正則になる $`p` ねじれなしの環への射 $`B\to B'` に沿う底変換と可換。

*命題 2.5.4（原典 Lemma 2.38。正則列の pd 包） — Lean*

$`D'` を、自由分冪代数 $`\Gamma_B(\oplus_sBe_s)` を $`\gamma_1(e_s)-f_s` で割った環 \`DPFamilyPresentation\`（RegularSequencePD:49）として定義する（任意の係数環・任意の添字集合）。正則性なしで成り立つもの：任意の分冪標的への評価の普遍性 \`existsUnique\_dpFamilyEval\`（:143）、任意の係数拡大との可換性 \`dpFamilyBaseChangeEquiv\`（:211）、原典の押し出し $`B\otimes_{\mathbb Z_{(p)}[x]}\Gamma_{\mathbb Z_{(p)}}(\mathbb Z_{(p)}^r)` との同一視 \`dpFamilyUniversalTensorEquiv\`（RegularSequencePDUniversalTor:93）。

$`B` が $`p` 正則で $`f` が $`B/p` 上 Koszul 正則なとき：*離散性*は原典の押し出しの高次 Tor の消滅 \`dpFamilyUniversalTor\_subsingleton\`（:114）、$`B[x]` 上に係数拡大した形 \`dpFamilyPresentation\_tor\_subsingleton\`（RegularSequencePDTor:136、$`p` 局所性も仮定）。\*\*$`p` ねじれなし\*\* \`dpFamilyPresentation\_primeRegular\`（RegularSequencePDPrimeRegular:104）。\*\*$`D_{(f)}(B)` との同一視\*\*（$`p` 局所のとき）：$`B[1/p]` の階乗部分環との $`B` 代数同型 \`dpFamilyFactorialEquiv\`（RegularSequencePDFactorial:203）、階乗部分環の分冪構造 \`dpFamilyFactorialDividedPowers\`（:115）と、$`p` ねじれを許す任意の分冪標的への普遍性 \`existsUnique\_dpFamilyFactorialDPMorphism\`（:224）。

鍵の計算：標数 $`p` で自由分冪代数は切断多項式環 $`\mathbb F_p[x]/(x^p)` 上自由 \`freeDPTruncated\_moduleFree\`（FreeDPModPBlocks:155）、そこから標数 $`p` で関係列 $`(\gamma_1(e_s)-f_s)` が Koszul 正則 \`dpFamilyRelations\_isKoszulResolution\_of\_prime\_zero\`（RegularSequencePDKoszul:121）。原典の「$`f` が Koszul 正則なら $`f^{n}` も」は \`IsKoszulResolution.pow\`（Powers:188）。標数 $`p` の表示環は $`B/(f^p)` 上忠実平坦 \`dpTruncatedCoefficientMap\_faithfullyFlat\`（RegularSequencePDTruncatedFlat:140）。$`r=1` の旧版 \`PrincipalDPPresentation\`（PrincipalDP:49）も残る。

*命題 2.5.4（原典 Lemma 2.38。正則列の pd 包） — 証明*

\*\*離散性と $`p` ねじれなし.\*\* 左の縦の射は $`p` を逆にすると同型なので右も同型で、$`D'[1/p]=B[1/p]`。よって $`D'\otimes^L_{\mathbb Z}\mathbb F_p` が離散であることを示せばよい（そうなら $`D'` の高次ホモトピーは $`p` 倍で単射かつ $`p` を逆にすると零、$`\pi_0` も $`p` ねじれなし）。標準計算：$`\mathbb F_p[x]\to D_{(x)}(\mathbb F_p[x])` は、目標を $`\mathbb F_p[x]/(x_1^p,\dots,x_r^p)=\mathrm{Kos}(\mathbb F_p[x];x_1^p,\dots,x_r^p)` 上の自由加群にする。四角に $`-\otimes^L_{\mathbb Z}\mathbb F_p` を当てると、$`D'\otimes^L\mathbb F_p` は $`\mathrm{Kos}(B/p;f_1^p,\dots,f_r^p)` 上の自由加群。仮定から $`\mathrm{Kos}(B/p;f)` は次数 0 に集中し、$`\sum n_i` についての帰納法で任意の正の $`(n_i)` について $`\mathrm{Kos}(B/p;f_1^{n_1},\dots,f_r^{n_r})` も次数 0 に集中する。特に $`n_i=p` で、その上の自由加群 $`D'\otimes^L\mathbb F_p` も次数 0 に集中。

*同一視.* $`p` ねじれなしの $`B` 代数 $`D'` で $`f_i` の像は分冪を持つ（左下の $`\gamma_n(x_i)` の像）ので、普遍性で $`B` 代数の射 $`a\colon D_{(f)}(B)\to D'`。逆に押し出しの記述と pd 包の関手性で $`b\colon D'\to D_{(f)}(B)`。$`a\circ b` は $`B` 代数の射なので $`D'[1/p]=B[1/p]` の上で恒等、$`D'` は $`p` ねじれなしなので恒等。$`b\circ a` は各 $`\gamma_n(f_i)` を $`\gamma_n(x_i)` の像、すなわち $`\gamma_n(f_i)` に送るので、生成元の上で恒等。

*底変換.* $`D'` の作り方は任意の底変換と可換なので、上の同一視から従う。

*命題 2.5.4（原典 Lemma 2.38。正則列の pd 包） — 原典との差*

$`D_{(x)}(\mathbb Z_{(p)}[x])` を自由分冪代数 $`\Gamma_{\mathbb Z_{(p)}}(\mathbb Z_{(p)}^r)`（$`x_i\mapsto\gamma_1(e_i)`）で置き、$`D'` を通常の環の押し出し（＝分冪表示環）として定義する。離散性は高次 Tor の消滅として述べる。

証明の経路も違う。原典は $`D'\otimes^L\mathbb F_p` の自由性から離散性と $`p` ねじれなしを同時に出すが、Lean はまず「関係列 $`(\gamma_1(e_s)-f_s)` に $`p` を加えた列」が $`\Gamma_B` 上 Koszul 正則であることを示し（$`\bmod p` の Koszul 計算と $`\Gamma_B` の $`p` 正則性、\`dpFamilyRelations\_snoc\_isKoszulResolution\`、RegularSequencePDPrimeRegular:73）、そこから $`p` ねじれなしを出す。Tor の消滅は、それと「$`p` を逆にすると $`\gamma_1(e_s)` は自由な多項式変数なので関係列は Koszul 正則」を合わせて関係列そのものの Koszul 正則性を得て（\`isKoszulResolution\_of\_snoc\_and\_away\`、PrincipalReduction:143）から出す。$`\bmod p` の Koszul 計算では、原典の「$`\mathrm{Kos}(B/p;f^p)` 上自由」を、切断多項式環上の自由性と Tor の対称性で $`\mathrm{Kos}(B/p;f^p)` に帰着する形で使う。同一視は原典の「$`a\circ b=\mathrm{id}`・$`b\circ a=\mathrm{id}`」の代わりに、階乗部分環への評価が全射で、表示環の $`p` 正則性から単射、とする。原典の正則性は Koszul 正則性（有限列）で、Lean も同じ。

宣言：`SerrePositivity.BhattScholze.dpFamilyPresentation_primeRegular`、`SerrePositivity.BhattScholze.dpFamilyPresentation_tor_subsingleton`、`SerrePositivity.BhattScholze.dpFamilyFactorialEquiv`、`SerrePositivity.BhattScholze.dpFamilyBaseChangeEquiv`

:::

:::corollary "bs_2_39"
*系 2.39*　A\{φ(f)/p\} ＝ D\_I(A)。対応表の状態：なし。

通常の δ 除算環と分冪表示環の同型・p 正則性は本体。原文の SCR の derived δ pushout C とその離散性・universal PD-envelope への比較は未同定で、表示環の部品だけでは直接の部分と判定できない。

*系 2.5.5（原典 Cor 2.39） — 主張*

$`A` を $`p` ねじれなしの δ 環とし、$`f_1,\dots,f_r\in A` が $`A/p` で正則列を定めるとする。単体的可換 δ 環の ∞ 圏での導来押し出し
$$`\begin{array}{ccc}\mathbb Z_{(p)}\{x_1,\dots,x_r\}&\xrightarrow{\ x_i\mapsto py_i\ }&\mathbb Z_{(p)}\{y_1,\dots,y_r\}\\ {\scriptstyle x_i\mapsto\varphi(f_i)}\downarrow&&\downarrow\\ A&\longrightarrow&A\{\varphi(f_1)/p,\dots,\varphi(f_r)/p\}\end{array}`
で $`A\{\varphi(f)/p\}` を定める。このとき $`A\{\varphi(f)/p\}` は離散・$`p` ねじれなしで、$`I=(f_1,\dots,f_r)` の pd 包 $`D_I(A)` と同一視される。特に $`D_I(A)` は δ 環で、δ 環として $`A` 上有限表示。

*系 2.5.5（原典 Cor 2.39） — Lean*

$`A` を $`p` 局所な δ 環、$`f_1,\dots,f_r` を有限族とする。正則性なしで、生の包 $`A\{\varphi(f)/p\}` は分冪表示環 \`DPFamilyPresentation f\` と $`A` 代数同型 \`frobeniusDivisionDPFamilyEquiv\`（FrobeniusDivisionRegularSequence:176）。さらに $`A` が $`p` 正則で $`f` が $`A/p` 上 Koszul 正則なら：$`A\{\varphi(f)/p\}` は $`p` 正則 \`frobeniusDivision\_primeRegular\`（:264）、pd 包 $`D_{(f)}(A)`（階乗部分環）と $`A` 代数同型 \`frobeniusDivisionDPEnvelopeEquiv\`（:280）。分冪表示環への δ 構造の移送 \`dpFamilyDelta\`（:302）、$`p` 完備化への延長 \`frobeniusDivisionPDCompletionEquiv\`（:325）。$`r=1` の旧版 \`deltaPDivisionRaw\_p\_mul\_injective\`（Andre/Envelope/PDivision:390）・\`deltaPDivisionRawPrincipalEquiv\`（:716）も残る。根の関係・モニック族の特殊形は別系統（\`deltaRootFamilyRaw\_isCompletelyFaithfullyFlat\`、RootFamilySource:842；\`monicFamilyRaw\_isCompletelyFaithfullyFlat\`、RootedExtension:1084）。

*系 2.5.5（原典 Cor 2.39） — 証明*

四角を二つの押し出しの合成に分ける：
$$`\begin{array}{ccc}\mathbb Z_{(p)}\{x\}&\xrightarrow{x_i\mapsto py_i}&\mathbb Z_{(p)}\{y\}\\ {\scriptstyle\varphi}\downarrow&&\downarrow\\ \mathbb Z_{(p)}\{x\}&\longrightarrow&\mathbb Z_{(p)}\{x,\varphi(x)/p\}\\ {\scriptstyle x_i\mapsto f_i}\downarrow&&\downarrow\\ A&\longrightarrow&A\{\varphi(f)/p\}\end{array}`
（右列の二つ目と三つ目の頂点は押し出しで定まる）。命題 2.5.2 と注意 2.5.3（原典の本文は「Remark 2.36」と書くが Rem 2.37 のこと）の $`r` 変数版により、中段の横の射は $`\mathbb Z_{(p)}\{x\}\to D_{(x)}(\mathbb Z_{(p)}\{x\})`（$`x_i` の分冪を形式的に添加する射）と同一視される。pd 包の作り方は平坦な底変換 $`\mathbb Z_{(p)}[x]\to\mathbb Z_{(p)}\{x\}` と可換なので、これは $`\mathbb Z_{(p)}[x]\to D_{(x)}(\mathbb Z_{(p)}[x])` の底変換で、下段は命題 2.5.4 の押し出しになる。命題 2.5.4 から右下の頂点は離散・$`p` ねじれなしで $`D_I(A)` と同一視される。

*系 2.5.5（原典 Cor 2.39） — 原典との差*

原典どおり、自由座標（命題 2.5.2）を押し出しで一般の列へ特殊化し、下段を命題 2.5.4 で処理する。ただし導来押し出しではなく通常の環の押し出しで比べ（生の包と分冪表示環の同型は正則性を使わない）、離散性は命題 2.5.4 の Tor の消滅に任せる。原典の「$`A/p` で正則列」を、Lean は「$`A/p` 上 Koszul 正則な有限列」で述べ、$`A` の $`p` 局所性を明示の仮定にする（原典は $`\mathbb Z_{(p)}` 代数を仮定）。「δ 環として有限表示」は、生の包が有限個の添加と δ 関係で定義されていることそのもので、別の主張としては立てない。

宣言：`SerrePositivity.BhattScholze.frobeniusDivisionDPEnvelopeEquiv`、`SerrePositivity.BhattScholze.frobeniusDivision_primeRegular`、`SerrePositivity.BhattScholze.frobeniusDivisionPDCompletionEquiv`、`SerrePositivity.BhattScholze.frobeniusDivisionDPFamilyEquiv`

:::

:::proposition "bs_2_40"
*注意 2.40*　\\(D\_I(A)\\) は φ の引き戻し。対応表の状態：なし。

指定 PD-envelope の φ-pullback と選んだ生成列に依存しない普遍性の同定を未同定。除算環の部品だけから φ 降下を主張しない。

*注意 2.5.6（原典 Rem 2.40） — 主張*

系 2.5.5 は、pd 包 $`D_I(A)` が $`A\{f_1/p,\dots,f_r/p\}` の $`\varphi` による引き戻し（$`\varphi\colon A\to A` に沿う底変換）であることを示している。後者は列の選び方によらずイデアル $`I=(f_1,\dots,f_r)` だけで決まる：「$`p\mid I` となる $`p` ねじれなしの δ-$`A` 代数 $`B` のうち普遍なもの」として特徴づけられる。特に、この形で現れる pd 包は標準的な $`\varphi` 降下を持つ。

*注意 2.5.6（原典 Rem 2.40） — Lean*

主張そのもの（$`D_I(A)` が $`\varphi` 引き戻しであること、列によらないこと、$`\varphi` 降下）は本体にない。部品として、$`a_s/d` を添加する生の包の δ 射に沿う底変換が通常の環の押し出しであること \`deltaAdjoinDivisionBaseChange\_isPushout\`（BaseChange:95）（命題 2.5.2 の Lean の証明では $`\varphi` に沿って使う）、$`f/p` を添加して $`p` 冪ねじれを δ 閉包で除いた商 \`DeltaDivisionTorsionQuotient\`（Division/Basic:221）が $`p` 正則 \`deltaDivisionTorsionQuotient\_p\_mul\_injective\`（:338）で、「$`p` が非零因子で $`p\mid f_s` となる δ 代数」への普遍性を持つ \`existsUnique\_deltaDivisionTorsionHom\`（:240）がある（生成元の族で述べ、イデアルによらないことは述べない）。

*注意 2.5.6（原典 Rem 2.40） — 証明*

引き戻しの部分は形式的：「$`f_i/p` を添加する」押し出しを δ 射 $`\varphi\colon A\to A` に沿って底変換すると「$`\varphi(f_i)/p` を添加する」押し出しになる（$`\varphi(p)=p`）。特徴づけ：$`p` ねじれなしの $`B` では $`p\mid f_i` なら $`f_i/p` は一意なので、$`A\{f/p\}` からの δ 射は「$`B` で $`p\mid f_i`」という条件だけで一意に決まり、$`p\mid f_i\ (\forall i)\Leftrightarrow p\mid I` は生成元の取り方によらない。ただしこれが $`A\{f/p\}` そのものの特徴づけになるには $`A\{f/p\}` が $`p` ねじれなしであることが要り、原典はその理由を書かない。

:::

:::proposition "bs_2_41" (lean := "SerrePositivity.BhattScholze.deltaPDivisionToAway_range_eq_of_deltaStructure")
*Warning 2.41*　部分環は δ 構造によらない。対応表の状態：一部（component）。

*主張*　$`p` を反転した環内の $`A\{\varphi(f_1)/p,\ldots,\varphi(f_r)/p\}` の $`\delta` 構造によらない性質には Frobenius が必要である。$`\mathbf Z_{(p)}[x]` で Frobenius を $`x\mapsto x^p` と $`x\mapsto x^p+p` に選ぶと、$`x^p/p` を添加した二つの $`\delta` 部分環は異なる。

原文前半の φ-twisted 除算部分環の δ 構造からの独立性を同じ A\[1/p\] の range 等式で証明する。後半の untwisted R₁,R₂ の非包含の反例は含まない。

*警告 2.5.7（原典 Warning 2.41） — 主張*

系 2.5.5 から、部分環 $`A\{\varphi(f_1)/p,\dots,\varphi(f_r)/p\}\subset A[1/p]`（これは $`A\{f_1^p/p,\dots,f_r^p/p\}` にも等しい）は $`A` の δ 構造によらない。ここで $`\varphi` による捻りは本質的で、捻りなしでは成り立たない。例：$`A=\mathbb Z_{(p)}[x]`、$`f=x` とする。Frobenius 持ち上げ $`x\mapsto x^p` で定まる δ 構造 $`\delta_1` では、$`R_1:=A\{x/p\}\subset A[1/p]` は
$$`\delta_1\Big(\frac xp\Big)=\frac{x^p}{p^{p+1}}\,(p^{p-1}-1)`
を含む。$`x\mapsto x^p+p` で定まる $`\delta_2` では、$`R_2:=A\{x/p\}\subset A[1/p]` は $`\delta_2(x/p)=\frac{x^p}{p^{p+1}}(p^{p-1}-1)+\frac1p` を含む。両方を含む部分環は $`1/p` を含むが、$`R_1` も $`R_2` も $`1/p` を含まない。特に $`R_1\not\subset R_2` かつ $`R_2\not\subset R_1`。

*警告 2.5.7（原典 Warning 2.41） — Lean*

前半（像が δ 構造によらない）は、任意の $`p` 局所 δ 環と元族で \`deltaPDivisionToAway\_range\_eq\_of\_deltaStructure\`（PDivision:758）（命題 2.5.2 の像の形を二つの δ 構造に使う）。$`A\{\varphi(f)/p\}\cong A\{f^p/p\}` は \`deltaPDivisionFrobeniusShiftEquiv\`（PDivisionCompletion:133）。捻りなしでは成り立たないことと例 $`R_1,R_2` は本体にない。

*警告 2.5.7（原典 Warning 2.41） — 証明*

前半：系 2.5.5 で $`A\{\varphi(f)/p\}` は $`A[1/p]` の部分環 $`D_I(A)` に等しく、$`D_I(A)` は δ 構造を使わずに定まる。$`\varphi(f_i)/p=f_i^p/p+\delta(f_i)` なので $`A\{f^p/p\}` とも等しい。

例の計算：$`\varphi_1(x/p)=x^p/p` なので $`\delta_1(x/p)=\frac1p\big(\frac{x^p}p-\frac{x^p}{p^p}\big)=\frac{x^p(p^{p-1}-1)}{p^{p+1}}`。$`\varphi_2(x/p)=\frac{x^p+p}{p}` なので $`\delta_2(x/p)=\delta_1(x/p)+\frac1p`。差が $`1/p`。

$`1/p\notin R_i` は原典では「系 2.5.5 から容易」とだけ書かれる。補うと：$`\varphi_i\colon A\to A` は δ 射なので、$`A\{x/p\}\to A\{\varphi_i(x)/p\}` を誘導し、$`A[1/p]` の中では（単射な）$`\varphi_i` そのもの。系 2.5.5 から $`A\{\varphi_i(x)/p\}=D_{(x)}(A)` で、これは $`\gamma_n(x)` の $`\mathbb Z_{(p)}` 係数の多項式からなり $`1/p` を含まない。$`\varphi_i(1/p)=1/p` なので $`1/p\notin R_i`。

:::

:::definition "bs_2_42"
*定義 2.42*　相対的 \\(I\\) 完全正則性。対応表の状態：なし。

通常環の Koszul ホモロジーで定めた IsCompletelyRegularRel はあるが、原文の SCR 上の flat map との比較がない。相対導来完全正則性の同じ定義と未照合。

*定義 2.6.1（原典 Def 2.42） — 主張*

単体的可換環 $`A` と有限生成イデアル $`I=(f_1,\dots,f_n)\subset\pi_0(A)`、導来 $`I` 完備な単体的可換 $`A` 代数 $`B` を固定する。列 $`x_1,\dots,x_r\in\pi_0(B)` が \*\*$`A` 上相対的に $`I` 完全正則\*\*（$`I`-completely regular relative to $`A`）であるとは、
$$`\mathrm{Kos}(A;f_1,\dots,f_n)\longrightarrow\mathrm{Kos}(B;f_1,\dots,f_n,x_1,\dots,x_r)`
が単体的可換環の平坦な射であること。

$`A,B` が離散なとき、平坦性をほどくと次の三条件になる：(i) $`B` が導来 $`I` 完備（定義の前提）、(ii) $`H_0(\mathrm{Kos}(B;f,x))=B/(f,x)` が $`A/I` 上平坦、(iii) すべての $`q` で標準射 $`B/(f,x)\otimes_{A/I}H_q(\mathrm{Kos}(A;f))\to H_q(\mathrm{Kos}(B;f,x))` が同型。たとえば $`B=A[x_1,\dots,x_r]^\wedge_I`（変数）なら $`\mathrm{Kos}(B;f,x)\simeq\mathrm{Kos}(A;f)` なので変数の列は相対的に $`I` 完全正則。prism $`(A,(d))` では $`I=(p,d)` とする。

*定義 2.6.1（原典 Def 2.42） — Lean*

古典的な環の場合（$`A,B` が離散）を (i)〜(iii) の形で定義：\`IsCompletelyRegularRel\`（Prismatic/RelativeCompleteRegularity:149）。$`A` の有限列 $`a` と $`B` の有限列 $`x` について、三つの連言がそれぞれ (i)（各 $`a_i` について導来完備）、(ii)、(iii)（全次数 $`q\in\mathbb Z` で全単射）。比較射 \`relativeKoszulComparison\`（:120）は、係数拡大と列の付加が誘導する Koszul 複体の射を剰余環上の線形射に降ろし、スカラー拡大の随伴でテンソル積からの射にしたもの。$`H_q(\mathrm{Kos}(A;a))` は $`a` で消えるので $`A/(a)` 加群になる（\`koszulResidueModule\`、:95）。prism の $`(p,d)` への特殊化は \`IsPrismCompletelyRegularRel\`（:156）。単体的可換環の版は本体にない。

*定義 2.6.1（原典 Def 2.42） — 原典との差（D20）*

原典の「$`\mathrm{Kos}(A;a)\to\mathrm{Kos}(B;a,x)` が平坦」（単体的可換環の射の平坦性）を、連結な環の射の平坦性の判定（$`\pi_0` の平坦性と、全次数の $`\pi_i` の底変換同型）でホモロジーに書いたもの（D20）。高次ホモロジーの消滅で定義すると、基底の $`H_1` が零でない結晶 prism $`(\mathbb Z_p,(p))` で原典と食い違う。

宣言：`SerrePositivity.BhattScholze.Prismatic.IsCompletelyRegularRel`、`SerrePositivity.BhattScholze.Prismatic.relativeKoszulComparison`

:::

:::lemma_ "bs_2_43"
*補題 2.43*　pd 包の押し出しの \\(p\\) 完全平坦性。対応表の状態：なし。

設計と rank-one mod p 計算の部品のみ。原文の相対完全正則列に沿う derived PD pushout の完全平坦性は未同定。

*補題 2.6.4（原典 Lemma 2.43） — 主張*

$`A` を単体的可換環、$`B` を $`p` 完備な単体的可換 $`A` 代数、$`x_1,\dots,x_r\in\pi_0(B)` を、$`x_1^p,\dots,x_r^p` が $`A` 上相対的に $`p` 完全正則であるような列とする。$`D` を導来 $`p` 完備な単体的可換環の ∞ 圏での押し出し
$$`\begin{array}{ccc} \mathbb Z_p[y_1,\dots,y_r]^\wedge_p & \longrightarrow & B \\ \downarrow{\scriptstyle\mathrm{can}} & & \downarrow \\ D_{(y_1,\dots,y_r)}(\mathbb Z_p[y_1,\dots,y_r])^\wedge_p & \longrightarrow & D \end{array}`
で定める。上の横の射は $`\pi_0` で $`y_i\mapsto x_i` となる単体的可換環の射（ホモトピーを除いて一意）、左の縦の射は pd 包（分冪多項式代数の $`p` 完備化）への標準射。このとき $`A\to D` は $`p` 完全平坦。

*補題 2.6.4（原典 Lemma 2.43） — Lean*

主張は本体にない（$`p` 完全平坦性への帰着と単体的可換環の押し出しは扱っていない）。標数 $`p` の段の部品はある。鍵の自由性：一変数で $`\Gamma_A\langle x\rangle` が $`A[x]/(x^p)` 上自由 \`rankOneDPTruncated\_moduleFree\`（Delta/DividedPower/RankOneDP:684）、多変数で自由分冪代数が切断多項式環上自由 \`freeDPTruncated\_moduleFree\`（Delta/DividedPower/FreeDPModPBlocks:155）。一変数の導来版：$`p=0` の $`A` 上で、$`A[x]` 加群の有界上の複体 $`X` について「$`X\otimes^L_{A[x]}\Gamma_A\langle x\rangle` の各ホモロジーが $`A` 平坦 ⇔ $`x^p` の錐（$`\mathrm{Kos}(X;x^p)`）の各ホモロジーが $`A` 平坦」\`rankOneDPDerivedKoszulHomology\_flat\_iff\`（RankOneDP:1729）。離散な一元の場合：標数 $`p` の $`B` で $`B/(y^p)` が $`A` 平坦なら分冪表示環 $`\Gamma_B\langle T\rangle/(T-y)` も $`A` 平坦 \`principalDPPresentation\_flat\_of\_quotient\_flat\`（Delta/DividedPower/PrincipalDP:1006）。離散な多変数では、表示環が $`B/(f^p)` 上忠実平坦 \`dpTruncatedCoefficientMap\_faithfullyFlat\`（Delta/DividedPower/RegularSequencePDTruncatedFlat:140）で、そこから $`A` 平坦性を出す宣言はない。

*補題 2.6.4（原典 Lemma 2.43） — 証明*

$`p` 完全平坦性は $`\pi_0(A/p)\to\pi_0(A/p)\otimes^L_AD` の平坦性で判定できる。$`D` の作り方は底変換と可換で、仮定も底変換で保たれる（注意 2.6.3 (1)）ので、$`A\to\pi_0(A/p)` に沿って底変換し、$`A` が離散な $`\mathbb F_p` 代数の場合に帰着する。このとき $`\mathrm{Kos}(A;p)=A\otimes^L_{\mathbb Z}\mathbb F_p` で $`\mathrm{Kos}(B;p,x^p)=\mathrm{Kos}(B;x^p)\otimes^L_A\mathrm{Kos}(A;p)` なので、仮定は「$`\mathrm{Kos}(B;x_1^p,\dots,x_r^p)` が $`A` 上平坦」と読める。

あとは「$`D` は $`\mathrm{Kos}(B;x^p)` 上の自由加群」を言えばよい。左の縦の射を $`\bmod p` すると $`\mathbb F_p[y]\to D_{(y)}(\mathbb F_p[y])` で、これは古典的に $`\mathbb F_p[y]/(y_1^p,\dots,y_r^p)` 上の自由加群（一変数では $`\Gamma_{\mathbb F_p}\langle y\rangle` が $`\gamma_{pk}(y)`（$`k\ge0`）を基底とする $`\mathbb F_p[y]/(y^p)` 上の自由加群で、多変数はそのテンソル積）。$`B` は $`\mathbb F_p` 代数なので $`D=B\otimes^L_{\mathbb F_p[y]}D_{(y)}(\mathbb F_p[y])`（$`p` 完備化は効かない）で、$`B\otimes^L_{\mathbb F_p[y]}\mathbb F_p[y]/(y^p)=\mathrm{Kos}(B;x^p)` から $`D` は $`\mathrm{Kos}(B;x^p)` の直和。$`\mathrm{Kos}(B;x^p)` は $`A` 平坦だから $`D` も $`A` 平坦。これは Lemma 2.38（§2.5）の証明の鍵の計算の相対版。

:::

:::corollary "bs_2_44"
*系 2.44*　envelope の p 完全平坦性。対応表の状態：なし。

設計と自由変数での完全忠実平坦性のみ。原文の一般の相対完全正則列の derived δ pushout との比較は未同定。

*系 2.6.6（原典 Cor 2.44） — 主張*

$`A` を $`p` 完備な単体的可換 δ 環、$`B` を $`p` 完備な単体的可換 δ-$`A` 代数、$`x_1,\dots,x_r\in\pi_0(B)` を $`A` 上相対的に $`p` 完全正則な列とする。$`B` に $`x_i/p` を自由に添加した $`p` 完備な単体的可換 δ-$`A` 代数 $`C:=B\{x_i/p\}^\wedge`、すなわち単体的可換 δ 環の ∞ 圏での押し出し
$$`\begin{array}{ccc} \mathbb Z_p\{x_1,\dots,x_r\}^\wedge_p & \xrightarrow{x_i\mapsto x_i} & B \\ \downarrow{\scriptstyle x_i\mapsto pz_i} & & \downarrow \\ \mathbb Z_p\{z_1,\dots,z_r\}^\wedge & \longrightarrow & C \end{array}`
を考える。このとき $`C` は $`A` 上 $`p` 完全平坦。

*系 2.6.6（原典 Cor 2.44） — Lean*

主張は本体にない（単体的可換 δ 環の押し出しも本体にない）。部品：(1) の Frobenius の $`p` 完全忠実平坦性は $`\mathbb Z` 上の自由 δ 環で \`freeDeltaFrobenius\_isCompletelyFaithfullyFlat\`（Delta/Free/FreeDeltaFrobeniusFlat:339）。(4) の Cor 2.39 は有限の列について \`frobeniusDivisionDPEnvelopeEquiv\`（Delta/DividedPower/FrobeniusDivisionRegularSequence:280）、その $`p` 完備化 \`frobeniusDivisionPDCompletionEquiv\`（:325）。古典的な環の押し出しとしての生の包 $`B\{x/d\}=B\{z\}/(dz-x)_\delta` は \`DeltaAdjoinDivision\`（Delta/Division/Basic:50、$`d=p` が $`C` の古典版）。Prop 3.13 での使われ方については、本体は変数の場合の envelope（第 3 章の命題 3.5.1）を Cor 2.44 を経由せずに出す：完備自由 δ 環の $`(p,d)` 完全平坦性 \`completedFreeDelta\_completelyFlat\`（Prismatic/CompletedFreeDeltaFlat:83）と変数の置換による存在 \`exists\_prismaticEnvelope\_of\_variables\`（:125）（D21）。

*系 2.6.6（原典 Cor 2.44） — 証明*

可換図式
$$`\begin{array}{ccccccc} A & \to & A\{x_1,\dots,x_r\}^\wedge & \to & B & \to & B\{\tfrac{x_1}{p},\dots,\tfrac{x_r}{p}\}^\wedge=:C \\ \| & & \downarrow{\scriptstyle\psi} & & \downarrow{\scriptstyle\psi_B} & & \downarrow{\scriptstyle\psi_C} \\ A & \to & A\{y_1,\dots,y_r\}^\wedge & \to & B' & \to & B'\{\tfrac{\varphi(y_1)}{p},\dots,\tfrac{\varphi(y_r)}{p}\}^\wedge=:C' \end{array}`
をとる。$`\psi` は $`x_i\mapsto\varphi(y_i)` で決まる δ-$`A` 代数の射、$`B'`・$`C'` は中央と右の四角が $`p` 完備な単体的可換環の導来押し出しになるように定める（右の四角の下段が $`B'\{\varphi(y)/p\}^\wedge` になるのは、自由添加の押し出しを $`\psi_B` に沿って押し出すと $`x_i` の像 $`\varphi(y_i)` を $`p` で割ることになるから）。

1. $`\psi` は自由 δ 環の Frobenius（変数の名前を取り替えたもの）の底変換なので、Lemma 2.11（命題 2.1.14）により $`p` 完全忠実平坦。押し出しで $`\psi_B`・$`\psi_C` も $`p` 完全忠実平坦。よって $`C'` が $`A` 上 $`p` 完全平坦なら $`C` もそう（$`\psi_C` の忠実平坦性で降下）。

2. $`\psi_B` が $`p` 完全平坦なので、$`x` の像 $`\varphi(y_1),\dots,\varphi(y_r)\in\pi_0(B')` は $`A` 上相対的に $`p` 完全正則（$`\mathrm{Kos}(B';p,\varphi(y))=\mathrm{Kos}(B;p,x)\otimes^L_{\mathrm{Kos}(B;p)}\mathrm{Kos}(B';p)` で、平坦な射の合成）。

3. $`\varphi(y_i)=y_i^p+p\,\delta(y_i)` なので、注意 2.6.3 (2) で $`p` の倍数だけずらして、$`y_1^p,\dots,y_r^p` も $`A` 上相対的に $`p` 完全正則。

4. Cor 2.39（§2.5）を $`\mathbb Z_p\{y\}`（$`y` は $`\bmod p` で正則列）に使うと $`\mathbb Z_p\{y\}\{\varphi(y)/p\}^\wedge` は $`y` の pd 包 $`D_{(y)}(\mathbb Z_p\{y\})^\wedge` で、Lemma 2.38 によりこれは $`\mathbb Z_p\{y\}\otimes_{\mathbb Z_p[y]}D_{(y)}(\mathbb Z_p[y])` の $`p` 完備化。したがって $`C'=B'\widehat\otimes^L_{\mathbb Z_p[y]}D_{(y)}(\mathbb Z_p[y])^\wedge` は、補題 2.6.4 の $`D`（$`B'` と列 $`y` について）にほかならない。3 と補題 2.6.4 から $`C'` は $`A` 上 $`p` 完全平坦。

:::

