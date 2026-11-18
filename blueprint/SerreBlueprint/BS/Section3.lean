import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.BhattScholze.Delta.Distinguished.Distinguished
import SerrePositivity.BhattScholze.Prism.Basic.Bounded
import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
import SerrePositivity.BhattScholze.Prism.Basic.Rigidity
import SerrePositivity.BhattScholze.Prism.Basic.UniversalOriented
import SerrePositivity.BhattScholze.Prism.Basic.UniversalOrientedFrobenius
import SerrePositivity.BhattScholze.Prism.Bounded.CompleteFlatCochain
import SerrePositivity.BhattScholze.Prism.Bounded.CompleteFlatDiscrete
import SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensorCover
import SerrePositivity.BhattScholze.Prism.Bounded.CompletelyFlatPrism
import SerrePositivity.BhattScholze.Prism.Bounded.Completeness
import SerrePositivity.BhattScholze.Prism.Perfection.ClassicalPrismPerfection
import SerrePositivity.BhattScholze.Prism.Perfection.PCompletedPerfection
import SerrePositivity.BhattScholze.Prism.Perfection.PrismPerfection
import SerrePositivity.BhattScholze.Prism.Perfectoid.AinfClassical
import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismHomLift
import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid
import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectoidWittEquiv
import SerrePositivity.BhattScholze.Prismatic.Envelopes.CompletedFreeDeltaFlat
import SerrePositivity.BhattScholze.Prismatic.Envelopes.Envelope
import SerrePositivity.BhattScholze.Prismatic.Envelopes.VariableEnvelope
import SerrePositivity.BhattScholze.Prismatic.Envelopes.VariableEnvelopeBaseChange
import SerrePositivity.BhattScholze.Prismatic.Site.FlatCechDescent
import SerrePositivity.BhattScholze.Prismatic.Site.FlatCechSheaf
import SerrePositivity.BhattScholze.Prismatic.Site.FlatSiteResidue
import SerrePositivity.BhattScholze.Prismatic.Site.FlatSiteSheaf
import SerrePositivity.BhattScholze.Prismatic.Site.FlatTopologyPushout

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "§3 " =>
%%%
number := false
tag := "bs-3"
%%%

BS §3 の項目と、本体の宣言との対応。本文は対応表（`research/bs-coverage`）の照合の理由で、原典の本文の写しではない。

*導入*

§3 の流れ：Lemma 3.1（イデアルが distinguished 元で生成される条件）→ Def 3.2（prism）→ Ex 3.4（普遍向き付き prism）→ *Lemma 3.5（剛性）* → Lemma 3.6〜3.8（φ(I)A は単項、有界 prism・完全 prism の性質）→ *Lemma 3.9（prism の完全化）* → *Thm 3.10（完全 prism ＝ perfectoid 環）* → Cor 3.12（prism の site）→ *Prop 3.13（prismatic envelope）*。Lean の prism は向き付き（単項）で、その範囲で Lemma 3.1・3.5（前半）・3.7 (1)〜(3)・3.8・3.9、Ex 3.3・3.4 は本体にある。Thm 3.10 は三つの事実と $`W(R^\flat)` との比較、Cor 3.12 は固定した基底の上の site、Prop 3.13 は変数の場合。

この章では prism を定義し、基本性質（剛性、有界・完全 prism の性質）、prism の完全化、perfectoid 環と完全 prism の対応（Thm 3.10）、prismatic envelope（Prop 3.13）を扱う。番号「命題 3.k.n」はこのノートの番号（k は小節）で、括弧内が原典の番号。

*3.1 定義*

prism の定義の前に、δ 環のイデアルが（局所的に）distinguished 元で生成される条件（Lemma 3.1）を置き、それを使って prism とその圏（Def 3.2）を定める。例は結晶 prism（Ex 3.3）と普遍向き付き prism（Ex 3.4）。根基 $`\mathrm{rad}(A)` は Jacobson 根基。Lean の prism は向き付き（イデアルが単項で、生成元をデータに持つ）で、宣言は \`Prism/Basic/\` の \`OrientedPrism\`（Lemma 3.1 の単項の場合・Def 3.2・Ex 3.3・Lemma 3.8）、\`UniversalOriented\` と \`UniversalOrientedFrobenius\`（Ex 3.4）にある。

*3.2 剛性と有界・完全 prism の性質*

prism の射ではイデアルが標的のイデアル全体に移ること（剛性、Lemma 3.5）、$`\varphi(I)A` がいつも単項であること（Lemma 3.6）、有界 prism の完備性と完全平坦な対象の離散性（Lemma 3.7）、完全 prism が有界であること（Lemma 3.8）を示す。原典は局所単項な $`I` を Lemma 3.1 で局所的に単項にして Lemma 2.24 を当てるが、Lean は向き付きなので直接 Lemma 2.24 を当てる。そのとき要る $`e,p\in\mathrm{rad}(B)` は導来完備性から出る（\`DerivedCompletion.mem\_jacobson\_bot\_of\_isModuleComplete\`、HomologicalAlgebra/DerivedCompletion/ModuleComplete/Closure:464）。Lean の宣言は \`Prism/Basic/Rigidity\`（Lemma 3.5）と \`Prism/Bounded/\`（Lemma 3.7・3.8）にある。

*3.3 prism の完全化（原典 Lemma 3.9）*

任意の prism から、その上の普遍な完全 prism を作る。Frobenius の余極限 $`A_{\mathrm{perf}}` を取るだけでは完備性が崩れるので、$`(p,I)` 完備化し直す。その際、導来完備化と古典的完備化が一致することが要点になる。

*3.4 perfectoid 環 ＝ 完全 prism（原典 Thm 3.10〜Cor 3.12）*

完全 prism は perfectoid 環と同じものである。続けて原典は、その応用として正則局所環の perfectoid 被覆を説明し（Rem 3.11）、有界 prism 全体が忠実平坦な位相で site をなすことを示す（Cor 3.12）。この節では原典の順に三つを並べる。perfectoid 環は \[BMS18, §3\] の意味：$`p` 進完備で、$`\pi^p` が $`p` を割り切る（$`p=u\pi^p`、$`u` 単元）元 $`\pi` があり、$`R/p` の Frobenius が全射で、$`\theta\colon A_{\inf}(R)=W(R^\flat)\to R` の核が単項であるもの。Lean では \`IsIntegralPerfectoid\`（Defs:39）がこの条件に零環を加えた形で定める（零環では $`p` が単元）。

*3.5 prismatic envelope（原典 Prop 3.13）*

δ 対 $`(B,J)` から、$`J` を $`I` に送る普遍な prism を作る。正則性の仮定のもとで、これが平坦で底変換と可換になる。第 4 章の Čech–Alexander 複体の各項はこの形で作られる。

:::lemma_ "bs_3_1" (lean := "SerrePositivity.BhattScholze.DeltaStructure.isDistinguished_iff_p_mem_span_pow, SerrePositivity.BhattScholze.DeltaStructure.IsDistinguished.p_mem_span_pow, SerrePositivity.BhattScholze.OrientedPrism.isDistinguished_generator, SerrePositivity.BhattScholze.DeltaStructure.isDistinguished_iff_p_mem_span")
*補題 3.1*　δ-pair の条件。対応表の状態：一部（special）。

I=(d) の場合に (1) と (2) を distinguished 性と比較して同値とする。局所主 ideal の ind-Zariski 被覆 (3) は扱わない。

*命題 3.1.1（原典 Lemma 3.1：イデアルが distinguished 元で生成される条件） — 主張*

δ 環 $`A` と局所単項なイデアル $`I\subset A` の組 $`(A,I)` で、$`p` と $`I` が $`\mathrm{rad}(A)` に入るものを考える。次は同値。

(1) $`p\in I^p+\varphi(I)A`。

(2) $`p\in I+\varphi(I)A`。

(3) δ 環の忠実平坦な射 $`A\to A'` で ind-（Zariski 局所化）であるものがあって、$`IA'` は distinguished 元 $`d` で生成され、$`d,p\in\mathrm{rad}(A')`。

ここで $`A` 代数 $`B` が *ind-（Zariski 局所化）*であるとは、$`f_1,\dots,f_{n_j}\in A` について $`B_j=\prod_{i=1}^{n_j}A_{f_i}` の形の $`A` 代数の射のフィルター付き余極限として表せること（原典の脚注 8）。このような $`B` が $`A` 上忠実平坦であることは、ある（同値だが任意の）表示で各組 $`(f_1,\dots,f_{n_j})` が単位イデアルを生成することと同値。

*命題 3.1.1（原典 Lemma 3.1：イデアルが distinguished 元で生成される条件） — Lean*

単項 $`I=(d)` の場合だけ。(3)⇒(1) の計算 \`DeltaStructure.IsDistinguished.p\_mem\_span\_pow\`（OrientedPrism:44）（$`d` が distinguished なら $`p\in(d^p,\varphi(d))`。根基の仮定も要らない）、$`d,p\in\mathrm{rad}(A)` のもとでの (1)⇔(3) \`DeltaStructure.isDistinguished\_iff\_p\_mem\_span\_pow\`（:59）。(2)⇔(3) は第 2 章の命題 2.3.7 \`DeltaStructure.isDistinguished\_iff\_p\_mem\_span\`（Distinguished:217）。どちらも (3) は「$`d` が distinguished」の形（$`A'=A`）。局所単項なイデアルと ind-Zariski 局所化を使う一般形は本体にない。

*命題 3.1.1（原典 Lemma 3.1：イデアルが distinguished 元で生成される条件） — 証明*

(1)⇒(2) は $`I^p\subset I` から明らか。

(2)⇒(3)：$`g_1,\dots,g_n\in A` を、単位イデアルを生成し各 $`IA[1/g_i]` が単項になるように選ぶ。$`\widetilde{A[1/g_i]}` を $`A[1/g_i]` の $`V(p,I)` に沿った Zariski 局所化（$`1+(p,I)A[1/g_i]` での局所化）とし、$`A'=\prod_i\widetilde{A[1/g_i]}` とおく。作り方から $`p` と $`IA'` は $`\mathrm{rad}(A')` に入る。第 2 章の注意 2.2.2（原典 Rem 2.16）により $`A'` には δ-$`A` 代数の構造がただ一つある。忠実平坦性は、原典が「明らか」とするところを補うと次のとおり（補った）：各因子は局所化なので平坦。$`A` の極大イデアル $`\mathfrak m` は $`p,I\subset\mathrm{rad}(A)` より $`(p,I)` を含み、ある $`g_i\notin\mathfrak m` について $`\mathfrak mA[1/g_i]` は $`(p,I)` を含む素イデアルで $`1+(p,I)A[1/g_i]` と交わらないので、局所化の後にも残る。よって $`\mathrm{Spec}(A')\to\mathrm{Spec}(A)` の像はすべての閉点を含み、平坦なので忠実平坦。各 $`\widetilde{A[1/g_i]}` は $`A[1/g_if]`（$`f\in1+(p,I)`）のフィルター付き余極限なので ind-Zariski 局所化。作り方から $`IA'=(d)` となる $`d\in A'` があり、$`p\in(d,\varphi(d))A'` と $`d,p\in\mathrm{rad}(A')` から、第 2 章の命題 2.3.7（原典 Lemma 2.25）で $`d` は distinguished。

(3)⇒(1)：示すことは $`A/(I^p+\varphi(I)A)` で $`p=0` であること。$`A\to A'` は忠実平坦なので $`A/J\to A'/JA'`（$`J=I^p+\varphi(I)A`）は単射で、$`A'` へ底変換して確かめてよい。$`JA'=(d^p,\varphi(d))` なので $`A'/(d^p,\varphi(d))` で $`p=0` を示せばよいが、$`\varphi(d)=d^p+p\,\delta(d)` と $`\delta(d)` の単元性から $`p=\delta(d)^{-1}(\varphi(d)-d^p)\in(d^p,\varphi(d))`。

単項 $`I=(d)` の場合、(3) は「$`d` が distinguished」と同値である（補った）：⇐ は $`A'=A` をとればよい。⇒ は、$`IA'=(d')`、$`d'` が distinguished なら $`dA'=d'A'\subset\mathrm{rad}(A')` なので命題 2.3.7 の後半（distinguished 性は生成するイデアルで決まる）から $`\delta(d)` は $`A'` で単元、忠実平坦な射に沿って単元は降りるので $`A` でも単元。

*命題 3.1.1（原典 Lemma 3.1：イデアルが distinguished 元で生成される条件） — 原典との差（D5）*

Lean は単項な $`I=(d)` に限る。このとき (3) の ind-Zariski 局所化は要らず、命題は「$`d,p\in\mathrm{rad}(A)` のもとで $`d` が distinguished ⇔ $`p\in(d^p,\varphi(d))` ⇔ $`p\in(d,\varphi(d))`」になる。prism は向き付きなので、本体ではこれで足りる。

:::

:::definition "bs_3_2" (lean := "SerrePositivity.BhattScholze.OrientedPrism, SerrePositivity.BhattScholze.OrientedPrism.Hom, SerrePositivity.BhattScholze.Prismatic.IsBoundedPrism")
*定義 3.2*　prism の圏。対応表の状態：一部（special）。

生成元とその正則性を選んだ向き付き prism とその射・有界性の定義。一般の Cartier 因子、全 δ-pair の圏および flat map の全記述は含まない。

*定義 3.1.2（原典 Def 3.2：prism の圏） — 主張*

δ 環 $`A` とイデアル $`I\subset A` の組 $`(A,I)` を *δ 対*と呼ぶ。δ 対全体は圏（δ 対の圏）をなす（射 $`(A,I)\to(B,J)` は $`f(I)\subset J` となる δ 射 $`f\colon A\to B`）。

(1) $`(A,I)` が *prism* であるとは、$`I\subset A` が $`\mathrm{Spec}(A)` の Cartier 因子を定め、$`A` が導来 $`(p,I)` 完備で、$`p\in I+\varphi(I)A` であること。prism の圏は δ 対の圏の対応する充満部分圏。

(2) prism $`(A,I)` は次のように呼ばれる。

・*完全*：$`A` が完全 δ 環、すなわち $`\varphi\colon A\to A` が同型。

・*有界*：$`A/I` の $`p^\infty` ねじれが有界。

・*向き付け可能*：イデアル $`I` が単項。$`I` の生成元の選び方を*向き*と呼ぶ。

・*結晶*：$`I=(p)`。このような prism は有界かつ向き付け可能。

(3) prism の射 $`(A,I)\to(B,J)` が*（忠実）平坦*であるとは、$`A\to B` が $`(p,I)` 完全（忠実）平坦であること。

*定義 3.1.2（原典 Def 3.2：prism の圏） — Lean*

(1) は向き付きの形。構造 \`OrientedPrism\`（OrientedPrism:120）の欄は δ 構造 \`deltaStructure\`、生成元 \`generator\`、生成元の正則性 \`generator\_regular\`（Cartier 因子にあたる）、導来 $`p` 完備性 \`complete\_p\` と導来生成元完備性 \`complete\_generator\`（二つを合わせて導来 $`(p,d)` 完備）、$`p\in(d,\varphi(d))` \`p\_mem\`。イデアル \`OrientedPrism.ideal\`（:132）は $`(d)`、原典の形 $`p\in I+\varphi(I)A` は \`OrientedPrism.p\_mem\_sup\_map\`（:139）。distinguished な正則元からの構成 \`OrientedPrism.ofDistinguished\`（:146）。導来完備性は共通基盤の \`DerivedCompletion.IsModuleComplete\`（HomologicalAlgebra/DerivedCompletion/ModuleComplete/Basic:140）で、生成元が非零因子なので古典的 $`d` 進完備性と同値（\`OrientedPrism.isAdicComplete\_generator\`、OrientedPrism:153）。導来完備な環ではパラメータが Jacobson 根基に入る \`OrientedPrism.p\_mem\_jacobson\`・\`OrientedPrism.generator\_mem\_jacobson\`（:165・169）。

射は δ 対の射の形 \`OrientedPrism.Hom\`（:210）：δ 射 \`map\_delta\` と $`(d)\subset f^{-1}(J)` \`ideal\_le\`。生成元そのものの保存は要求しない。恒等射・合成 \`Hom.id\`・\`Hom.comp\`（:226・230）と結合律 \`Hom.comp\_assoc\`（:245）。\`Category\` のインスタンスは置いていない。

(2) 完全は述語 \`DeltaStructure.IsPerfect\`（DeltaRing:166）を δ 構造に課す仮定として使う。有界は述語 \`Prismatic.IsBoundedPrism\`（Prismatic/PrismOver:41）（$`A/d` の $`p` 冪ねじれが一様な冪 $`p^N` で消える）。向きは構造のデータ（生成元）。結晶は例 3.1.3。

(3) 完全（忠実）平坦性は \`IsCompletelyFlat\`・\`IsCompletelyFaithfullyFlat\`（CommutativeAlgebra/CompletelyFlat/Basic:42・48）を $`I=(p,d)` で使う。prism の射についての述語は、site の射について \`Prismatic.PrismOver.IsFaithfullyFlat\`（Prismatic/FlatCover:40）がある。

*定義 3.1.2（原典 Def 3.2：prism の圏） — 証明*

確かめることは (2) の最後の一文だけ（補った）。$`I=(p)` は単項なので向き付け可能。$`A/I=A/p` は $`p` で消えるので $`p^\infty` ねじれは $`p^1` で消え、有界。

Lean の形との関係（補った）：(i) Cartier 因子 $`I` が単項 $`(d)` なら $`d` は非零因子である：局所的に $`I=(g)`、$`g` 非零因子と書くと $`d=ug`、$`g=vd` で $`(1-uv)g=0` から $`uv=1`、よって $`d` は局所的に非零因子の単元倍。(ii) 有限生成イデアル $`(f_1,\dots,f_r)` についての導来完備性は、各 $`f_i` についての導来完備性と同値。よって導来 $`(p,d)` 完備性は欄 \`complete\_p\`・\`complete\_generator\` の組と同じ。

*定義 3.1.2（原典 Def 3.2：prism の圏） — 原典との差（D5・D19）*

Lean の対象は向き付き prism（単項イデアルと生成元を持つ）だけで、局所単項な一般の Cartier 因子 $`I` は扱わない（D5）。射は向きを保つことを要求しないので、\`OrientedPrism\` と \`OrientedPrism.Hom\` の圏は向き付け可能な prism の充満部分圏と同値になる（同じイデアルの別の生成元を選んだ対象どうしは恒等写像で同型）。固定した向き付きの基底の上では、剛性（命題 3.2.1）により相手も自動的に向き付き（D19）。

:::

:::proposition "bs_3_3" (lean := "SerrePositivity.BhattScholze.OrientedPrism.crystalline, SerrePositivity.BhattScholze.OrientedPrism.exists_crystalline_iff")
*例 3.3*　結晶 prism。対応表の状態：本体にある。

I=(p) なら p 自体を向きに選べる。同じ δ 環の結晶 prism の存在 iff p 正則かつ古典 p 完備を述べる。

*例 3.1.3（原典 Ex 3.3：結晶 prism） — 主張*

$`p` ねじれなしで $`p` 完備な任意の δ 環 $`A` について、$`(A,(p))` は結晶 prism である。逆に、結晶 prism はすべてこの形。

*例 3.1.3（原典 Ex 3.3：結晶 prism） — Lean*

構成 \`OrientedPrism.crystalline\`（OrientedPrism:308）（$`p` 正則で古典的 $`p` 進完備な δ 環に、生成元 $`p` の向き付き prism）。両向きの判定 \`OrientedPrism.exists\_crystalline\_iff\`（:329）：δ 構造 $`D` を固定して「δ 構造が $`D` で生成元が $`p` の向き付き prism がある ⇔ $`p` 正則かつ古典的 $`p` 進完備」。逆向きは生成元が $`p` そのものである場合の形。

*例 3.1.3（原典 Ex 3.3：結晶 prism） — 証明*

原典は証明を書かない（補った）。

順：$`p` は非零因子なので $`(p)` は Cartier 因子。$`A` は古典的 $`p` 進完備なので導来 $`p` 完備で、$`(p,I)=(p)`。$`p\in I` なので $`p\in I+\varphi(I)A` は明らか。（$`p` 完備なので $`p\in\mathrm{rad}(A)` で、第 2 章の例 2.3.2 (1) により $`p` は distinguished でもある。）

逆：$`(A,(p))` が prism なら、Cartier 因子 $`(p)` の生成元 $`p` は非零因子（定義 3.1.2 の証明の (i)）で、$`A` は $`p` ねじれなし。導来 $`p` 完備で $`p` ねじれなしの加群は古典的に $`p` 進完備。

:::

:::proposition "bs_3_4" (lean := "SerrePositivity.BhattScholze.universalOrientedPrism, SerrePositivity.BhattScholze.universalOrientedPrism_bounded, SerrePositivity.BhattScholze.existsUnique_universalOrientedPrismHom, SerrePositivity.BhattScholze.universalOrientedPrism_frobenius_isCompletelyFlat, SerrePositivity.BhattScholze.universalOrientedPrism_regular")
*例 3.4*　普遍向き付き prism。対応表の状態：本体にある。

同じ普遍向き付き prism の構成・有界性・向きを保つ射の存在一意性に加え、universalOrientedPrism\_regular が p,d 正則列を、frobenius\_isCompletelyFlat が mod p の d 完全平坦性を与える。

*例 3.1.4（原典 Ex 3.4：普遍向き付き prism） — 主張*

$`A_0=\mathbb Z_{(p)}\{d,\delta(d)^{-1}\}` を一変数 $`d` の自由 δ 環の（第 2 章の例 2.3.3、原典 Ex 2.21 で示した）局所化とし、$`A` を $`A_0` の $`(p,d)` 完備化、$`I=(d)\subset A` とする。このとき $`(A,I)` は有界 prism で、$`d\in I` は distinguished な生成元（したがって向きを定める）。実はこの組は普遍向き付き prism である（が、普遍向き付け可能 prism ではない）。後のために：この prism では列 $`p,d` は正則で、Frobenius $`\varphi\colon A/p\to A/p` は $`d` 完全平坦。

*例 3.1.4（原典 Ex 3.4：普遍向き付き prism） — Lean*

台環 \`UniversalOrientedPrismRing\`（UniversalOriented:38）は \`UniversalDistinguishedRing\`（$`A_0`）の導来 $`(p,d)` 完備化の $`H^0`。prism \`universalOrientedPrism\`（:48）、$`A/d` が $`p` 正則 \`universalOrientedPrism\_mod\_generator\_p\_regular\`（:65）、有界性 \`universalOrientedPrism\_bounded\`（:84）（$`N=0`）、$`p,d` の正則性 \`universalOrientedPrism\_regular\`（:97）、生成元を生成元へ送る射の一意存在 \`existsUnique\_universalOrientedPrismHom\`（:133）。Frobenius は $`A/p` を Frobenius に沿って $`A/p` 加群とみたものが $`(\bar d)` 完全平坦 \`universalOrientedPrism\_frobenius\_isCompletelyFlat\`（UniversalOrientedFrobenius:309）。「普遍向き付け可能 prism ではない」は本体にない。

*例 3.1.4（原典 Ex 3.4：普遍向き付き prism） — 証明*

原典は証明を書かない（補った）。

*prism であること・正則性・有界性.* $`\mathbb Z_{(p)}\{d\}` は多項式環 $`\mathbb Z_{(p)}[d,\delta(d),\delta^2(d),\dots]` なので $`p` は非零因子、$`\mathbb Z_{(p)}\{d\}/d\cong\mathbb Z_{(p)}[\delta(d),\delta^2(d),\dots]` も $`p` ねじれなしで、局所化 $`A_0` でも $`p` は $`A_0` と $`A_0/d` 上正則。例 2.3.3 から $`d` は $`A_0/p` で非零因子。こうして $`A_0` で $`p,d` と $`d,p` がどちらも正則列になり、二元の完備化でこの正則性は保たれる。特に $`d` は $`A` の非零因子（Cartier 因子）、$`A/d` は $`p` ねじれなし（有界）。$`d` は δ 射 $`A_0\to A` の像として distinguished で（δ 構造は第 2 章の命題 2.2.4 で完備化に延びる）、$`p\in(d,\varphi(d))`（命題 2.3.7）。$`A` は作り方から導来 $`(p,d)` 完備。

*普遍性.* 向き付き prism $`(B,(e))` について、$`e` は distinguished（命題 3.1.1）。$`p\in\mathrm{rad}(B)` なので $`p` と互いに素な整数は $`B` の単元で、$`B` は $`\mathbb Z_{(p)}` 代数。例 2.3.3 の普遍性から $`d\mapsto e` の δ 射 $`A_0\to B` がただ一つあり、$`B` が導来 $`(p,e)` 完備なので完備化 $`A` からの δ 射にただ一つ延びる（δ 構造の延長と完備化の普遍性、命題 2.2.4）。

*普遍向き付け可能 prism ではないこと.* 向き付け可能な prism $`(B,J)` への射 $`(A,(d))\to(B,J)` は、剛性（命題 3.2.1）で $`f(d)` が $`J` を生成し、上の普遍性で $`f(d)` から決まるので、$`J` の生成元全体（$`e\,B^\times`）と一対一に対応する。$`B^\times\ne\{1\}` なら射は一つに決まらない。

\*\*Frobenius の $`d` 完全平坦性.\*\* 自由 δ 環 $`L=\mathbb Z_{(p)}\{d\}` で $`L/(p,d)\to L/(p,\varphi(d))`（Frobenius が誘導する射）が忠実平坦であること（第 2 章の命題 2.1.14 の座標ごとの版）を局所化と完備化に移すと、$`A/(p,d)\to A/(p,\varphi(d))` が平坦。$`A/p` で $`\bar d` は非零因子なので、主元についての完全平坦性の判定（$`\bar d` 正則な加群は $`M/\bar dM` が平坦なら $`\bar d` 完全平坦）から結論が出る。

*例 3.1.4（原典 Ex 3.4：普遍向き付き prism） — 原典との差（D74）*

Frobenius の平坦性は原典どおり $`d` 完全平坦の形で本体に置く（D74）。普遍性は向きを保つ射（$`d\mapsto e`）についての形で、原典の「普遍向き付き prism」の意味と同じ。

:::

:::lemma_ "bs_3_5" (lean := "SerrePositivity.BhattScholze.OrientedPrism.Hom.map_ideal_eq, SerrePositivity.BhattScholze.OrientedPrism.Hom.idealBaseChangeEquiv, SerrePositivity.BhattScholze.OrientedPrism.Hom.idealTensorEquiv, SerrePositivity.BhattScholze.OrientedPrism.Hom.existsUnique_generator_unit, SerrePositivity.BhattScholze.OrientedPrism.Hom.map_generator_mul_injective")
*補題 3.5*　剛性。対応表の状態：一部（special）。

向き付き prism の同じ射の I⊗B≃J と IB=J および像の生成元の正則性。一般の非主 ideal と後半の必要十分条件の十分方向は含まない。

*命題 3.2.1（原典 Lemma 3.5：剛性） — 主張*

$`(A,I)\to(B,J)` が prism の射なら、自然な写像は同型 $`I\otimes_AB\cong J` を与える。特に $`IB=J`。

逆に、$`A\to B` が δ 環の射で $`B` が導来 $`(p,I)` 完備なら、$`(B,IB)` が prism であることと $`B[I]=0` は同値。

*命題 3.2.1（原典 Lemma 3.5：剛性） — Lean*

前半は向き付き prism の射 \`f : OrientedPrism.Hom P Q\`（$`P=(A,(d))`、$`Q=(B,(e))`）について。生成元の像は標的の生成元の一意な単元倍 \`OrientedPrism.Hom.existsUnique\_generator\_unit\`（Rigidity:40）、$`IB=J` \`OrientedPrism.Hom.map\_ideal\_eq\`（OrientedPrism:255）とその δ 射の形 \`OrientedPrism.map\_ideal\_eq\_of\_isDeltaHom\`（:183）、$`I\otimes_AB\cong J` は両立する代数構造について \`OrientedPrism.Hom.idealTensorEquiv\`（Rigidity:156）、射自身の代数構造で \`OrientedPrism.Hom.idealBaseChangeEquiv\`（:183）。局所的な計算：δ 射が distinguished 元 $`d` を $`(e)` に送り $`e,p\in\mathrm{rad}(B)` なら $`f(d)=e\cdot r` の $`r` は単元 \`DeltaStructure.IsDeltaHom.exists\_isUnit\_of\_distinguished\_of\_mem\_span\`（OrientedPrism:77）、イデアルの形 \`DeltaStructure.IsDeltaHom.map\_span\_eq\_of\_distinguished\_of\_mem\_span\`（:92）。

後半（逆）の主張は本体にない。その「⇒」にあたる、prism の射では生成元の像が非零因子（$`B[I]=0`）であること \`OrientedPrism.Hom.map\_generator\_mul\_injective\`（Rigidity:53）と、標的が生成元の像について導来完備 \`OrientedPrism.Hom.isModuleComplete\_map\_generator\`（:68）はある。完全平坦な場合の「⇐」は命題 3.2.3 (3)。

*命題 3.2.1（原典 Lemma 3.5：剛性） — 証明*

*前半.* 命題 3.1.1 で忠実平坦な $`A\to A'`、$`B\to B'` を選び、$`IA'=(d)`、$`JB'=(e)`、$`d,p\in\mathrm{rad}(A')`、$`p,e\in\mathrm{rad}(B')` とする。$`I,J` は Cartier 因子なので $`d,e` は非零因子。必要なら $`B'` を $`A'\otimes_AB'` の局所化に替えて、$`A\to B` が $`A'\to B'` に延びるとしてよい。$`I\otimes_AB\to J` が同型であることは忠実平坦降下により δ 対の射 $`(A',(d))\to(B',(e))` で確かめればよい。$`f(d)\in(e)` なので $`f(d)=e\,g`（$`g\in B'`）と書け、$`f(d)` は distinguished、$`p,e\in\mathrm{rad}(B')` なので第 2 章の命題 2.3.6（原典 Lemma 2.24）で $`g` は単元、よって $`(f(d))=(e)`。生成元どうしが単元倍なので $`I\otimes B'\cong B'\xrightarrow{\cdot f(d)}(e)` は同型。

*後半.* 自然な写像 $`I\otimes_AB\to IB` が同型であることと $`B[I]=0` は同値（局所的に $`I=(d)` とすると、この写像は $`B\xrightarrow{\cdot d}dB` で、単射 ⇔ $`d` が $`B` の非零因子）。前半から、$`(B,IB)` が prism なら $`I\otimes_AB\cong IB` で $`B[I]=0`。逆に $`I\otimes_AB\cong IB` なら $`IB` は可逆 $`B` 加群で $`\mathrm{Spec}(B)` の Cartier 因子を定める。$`p\in IB+\varphi(I)B` は $`A` での包含の像、$`B` の導来 $`(p,I)` 完備性は仮定なので、$`(B,IB)` は prism。

*命題 3.2.1（原典 Lemma 3.5：剛性） — 原典との差（D5・D6）*

Lean は向き付きなので、Lemma 3.1 による局所化と忠実平坦降下を使わず、$`f(d)=e\cdot r` に直接 Lemma 2.24 を当てる（D5）。標的に $`p` 正則性などの仮定はない（D6）。後半の逆は本体にない。単項の場合の逆「$`B` が導来 $`(p,f(d))` 完備で $`f(d)` が非零因子なら $`(B,(f(d)))` は向き付き prism」は、$`f(d)` が distinguished（\`DeltaStructure.IsDeltaHom.map\_isDistinguished\`、DeltaRing:180）なので \`OrientedPrism.ofDistinguished\` で作れるが、名前の付いた定理にはなっていない。

:::

:::lemma_ "bs_3_6"
*補題 3.6*　φ(I)A は主で生成元は distinguished。対応表の状態：なし。

一般 prism の φ(I)A の主性と二つの可逆加群の自明化を未同定。向きを仮定して初めから主 ideal とするだけでは一般の結論を示さない。

*命題 3.2.2（原典 Lemma 3.6：$`\varphi(I)A` は単項） — 主張*

$`(A,I)` を prism とする。イデアル $`\varphi(I)A\subset A` は単項で、その生成元はどれも distinguished 元である。さらに可逆 $`A` 加群 $`\varphi^*(I)=I\otimes_{A,\varphi}A` と $`I^p` は自明、すなわち $`A` に同型。

*命題 3.2.2（原典 Lemma 3.6：$`\varphi(I)A` は単項） — Lean*

本体にない。向き付きの場合は $`\varphi(I)A=(\varphi(d))` で、部品として Frobenius が δ 射であること \`DeltaStructure.isDeltaHom\_frobeniusLift\_general\`（FreeDeltaRing:276）と、δ 射が distinguished 元を保つこと \`DeltaStructure.IsDeltaHom.map\_isDistinguished\`（DeltaRing:180）、生成元の取り替え \`DeltaStructure.isDistinguished\_iff\_of\_span\_eq\`（Distinguished:226）がある。

*命題 3.2.2（原典 Lemma 3.6：$`\varphi(I)A` は単項） — 証明*

*第一の主張.* 一つの生成元が distinguished なら、第 2 章の命題 2.3.6（原典 Lemma 2.24）からすべての生成元が distinguished（$`b'=ub` で $`u` 単元、命題 2.3.5）。よって $`\varphi(I)A` が distinguished 元で生成されることを示せばよい。命題 3.1.1 により $`p=a+b`、$`a\in I^p`、$`b\in\varphi(I)A` と書ける。$`b` が $`\varphi(I)A` を生成する、すなわち $`1\mapsto b` で定まる $`A\to\varphi(I)A` が全射であることを示す。命題 3.1.1 (3) の忠実平坦な $`A\to B` をとると、$`B\to\varphi(I)B`（$`1\mapsto b`）の全射性と $`b` の distinguished 性を $`B` で示せばよい（全射性は忠実平坦な底変換で降り、$`\delta(b)` の単元性も降りる。補った）。$`IB=(d)`、$`d` は distinguished。$`a\in I^p`、$`b\in\varphi(I)` から $`a=xd^p`、$`b=y\varphi(d)`（$`x,y\in B`）と書ける。示すことは $`y` が単元であること。$`d,p\in\mathrm{rad}(B)` なので、$`y` が $`(d,p)` を法として単元であること、すなわち $`B/(d,p,y)=0` を示せばよい。そうでなければ $`\mathrm{Spec}(B/(d,p,y))\subset\mathrm{Spec}(B)` に沿って局所化して（$`B` を $`1+(d,p,y)` での局所化に替えて）$`d,p,y\in\mathrm{rad}(B)` としてよい。$`p=a+b=xd^p+y\varphi(d)=xd^p+yd^p+yp\,\delta(d)` から
$$`p\,(1-y\delta(d))=d^p(x+y)=d\cdot\bigl(d^{p-1}(x+y)\bigr).`
$`y\in\mathrm{rad}(B)` なので $`1-y\delta(d)` は単元で、左辺は distinguished（$`p` は distinguished で、命題 2.3.5）。命題 2.3.6 から $`d^{p-1}(x+y)` は単元、したがって $`d` も単元（$`p\ge2`）で、$`d\in\mathrm{rad}(B)` に反する。

*第二の主張.* $`A/p` 上では $`\varphi` は Frobenius で、標数 $`p` では直線束の Frobenius 引き戻しはその $`p` 乗なので、$`\varphi^*(I)` と $`I^p` は $`A/p` 上で同型になる。$`p\in\mathrm{rad}(A)` なので $`\varphi^*(I)\cong I^p`（補った：$`\varphi^*(I)` は射影的なので $`\bmod p` の同型は $`\varphi^*(I)\to I^p` に持ち上がり、中山の補題で全射、可逆加群の間の全射は同型）。よって $`\varphi^*(I)\cong A` を示せばよい。自然な全射 $`\varphi^*(I)\to\varphi(I)A\subset A` があり、$`\varphi(I)A` は単項である。$`\varphi(I)A` の生成元に移る $`f\in\varphi^*(I)` をとり、$`A\to\varphi^*(I)`、$`1\mapsto f` が同型であることを示す。可逆加群の間の射なので、$`\mathrm{Spec}(A)` のすべての閉点のファイバーで全射ならよい。閉点はすべて $`\mathrm{Spec}(A/p)` にある（$`p\in\mathrm{rad}(A)`）。$`B` を $`A_{\mathrm{perf}}` の $`p` 進完備化とすると、$`A/p\to B/p=(A/p)_{\mathrm{perf}}` は全単射な $`\mathrm{Spec}` を誘導するので（補った）、$`B\to\varphi^*(I)\otimes_AB`、$`1\mapsto f` の全射性を示せばよい。ここで自然な写像 $`\varphi^*(I)\otimes_AB\to\varphi(I)B` は同型（$`\varphi(I)B` は distinguished 元で生成され、完全 δ 環の distinguished 元は非零因子（第 2 章の命題 2.4.9、原典 Lemma 2.34）なので $`\varphi(I)B` は可逆、可逆加群の間の全射は同型）。$`f` は $`\varphi(I)A` の生成元に移るので $`B\to\varphi(I)B`、$`1\mapsto f` は全射。

*命題 3.2.2（原典 Lemma 3.6：$`\varphi(I)A` は単項） — 原典との差（D5）*

向き付き prism $`(A,(d))` では主張はすぐ出る：$`\varphi(I)A=(\varphi(d))` は単項、$`\delta(\varphi(d))=\varphi(\delta(d))` は単元なので $`\varphi(d)` は distinguished（他の生成元も、$`\varphi(d)\in(d,p)\subset\mathrm{rad}(A)` から命題 2.3.7 の後半で distinguished）、$`I\cong A` から $`\varphi^*(I)\cong A`、$`I^p=(d^p)\cong A`（$`d` は非零因子）。Lean ではこれを定理として置いていない。

:::

:::lemma_ "bs_3_7" (lean := "SerrePositivity.BhattScholze.boundedPrism_pair_isAdicComplete, SerrePositivity.BhattScholze.Prismatic.derivedCompletelyFlat_isDiscrete_of_boundedPrism, SerrePositivity.BhattScholze.Prismatic.completelyFlatCochain_isDiscrete_of_boundedPrism, SerrePositivity.BhattScholze.Prismatic.prismCompletedTensor_completelyFaithfullyFlat, SerrePositivity.BhattScholze.Prismatic.exists_boundedPrism_of_completelyFlat_deltaAlgebra")
*補題 3.7*　有界 prism の性質。対応表の状態：一部（special）。

向き付き有界 P の古典完備性、bounded-above の導来完全平坦複体・指定 K-flat 複体の離散性、完全平坦 δ 代数からの prism 構成を得る。任意 D(A)・非主 ideal と局所向きの構成(4)は含まない。

*命題 3.2.3（原典 Lemma 3.7：有界 prism の性質） — 主張*

$`(A,I)` を有界 prism とする。

(1) 環 $`A` は古典的に $`(p,I)` 完備。

(2) $`(p,I)` 完全平坦な $`A` 複体 $`M\in D(A)` を固定する。このとき $`M` は離散で古典的に $`(p,I)` 完備。任意の $`n\ge0` について $`M[I^n]=0` で、$`M/I^nM` の $`p^\infty` ねじれは有界。

(3) prism の（忠実）平坦な射 $`(A,I)\to(B,J)` の圏は、$`B` を $`(B,IB)` に送る関手により、$`(p,I)` 完全（忠実）平坦な δ-$`A` 代数 $`B` の圏と同一視される。

(4)（有界 prism は局所的に向き付け可能）δ 環の $`(p,I)` 完全忠実平坦な射 $`A\to B` で、$`IB=(d)`、$`d\in B` は distinguished で非零因子、となるものがある。実際 $`A\to B` として、$`A` の ind-Zariski 局所化の導来 $`(p,I)` 完備化をとれる。特に $`(A,I)\to(B,(d))` は有界 prism の忠実平坦な射。

*命題 3.2.3（原典 Lemma 3.7：有界 prism の性質） — Lean*

基底は向き付き prism $`P=(A,(d))` で、有界性 \`Prismatic.IsBoundedPrism P\`（$`A/d` の $`p` 冪ねじれが $`p^N` で消える）を仮定する（\`Prism/Bounded/Completeness\` の宣言では同じ条件を仮定 \`hB\` として書く）。

(1)：$`(p,d)` 進完備 \`Andre.boundedPrism\_pair\_isAdicComplete\`（Completeness:188）、$`p` 進完備 \`Andre.boundedPrism\_isAdicComplete\_prime\`（:276）。部品：$`A/d^m` が古典的 $`p` 進完備 \`Andre.boundedPrism\_generator\_power\_quotient\_prime\_complete\`（:157）、その入力の $`A/d^m` の $`p` 冪ねじれが $`p^{Nm}` で消える評価 \`Andre.regular\_power\_quotient\_torsion\_bound\`（:93）、二つのイデアルの和についての完備性 \`isAdicComplete\_sup\_of\_complete\_quotients\`（CommutativeAlgebra/Adic/Complete:260）。

(2)：上に有界な導来対象 $`X\in D^-(A)` について \`Prismatic.derivedCompletelyFlat\_isDiscrete\_of\_boundedPrism\`（CompleteFlatDiscrete:39）。完全平坦性は \`Prismatic.IsDerivedCompletelyFlat\`（CompleteFlatReduction:91）（$`X\otimes^L_AA/(p,d)` が次数 0 に集中し、その $`H^0` が $`A/(p,d)` 上平坦）。次数に上界のない項別平坦な K-flat 複体について \`Prismatic.completelyFlatCochain\_isDiscrete\_of\_boundedPrism\`（CompleteFlatCochain:180）。結論はどちらも「次数 0 に集中、$`H^0` は古典的に $`(p,d)` 進完備、各 $`d^n` が $`H^0` 上正則、$`H^0/d^n` の $`p` 冪ねじれは有界」。通常の導来圏 \`DerivedCategory (ModuleCat A)\` で述べ、$`X` の導来 $`p` 完備性・導来 $`d` 完備性を仮定する。中間の $`d^n` 剰余の評価 \`Prismatic.derivedGeneratorPowerReduction\_pure\_bounded\`（CompleteFlatReduction:157）。

(3)：対象の対応の向き「完全平坦で導来 $`(p,f(d))` 完備な δ-$`A` 代数 $`B` に、$`f(d)` を向きとする有界 prism の構造と $`P` からの prism の射が入る」\`Prismatic.exists\_boundedPrism\_of\_completelyFlat\_deltaAlgebra\`（CompletelyFlatPrism:70）。圏の同一視としては述べない。Cor 3.12 の押し出しで使う、完備テンソル積が左因子の上で完全（忠実）平坦 \`Prismatic.prismCompletedTensor\_completelyFlat\`・\`Prismatic.prismCompletedTensor\_completelyFaithfullyFlat\`（CompletedTensorCover:78・128）もこの (2)(3) の上にある。

(4)：本体にない。

*命題 3.2.3（原典 Lemma 3.7：有界 prism の性質） — 証明*

*(1)* 示すことは $`A\simeq\lim_kA/(I^k,p^k)`。可逆 $`A` 加群 $`J_1,\dots,J_m` と写像 $`a_i\colon J_i\to A` について、$`\bigoplus_iJ_i\xrightarrow{\sum a_i}A` の Koszul 複体を $`\mathrm{Kos}(A;J_1,\dots,J_m)` と書く（$`J_i=A` ならふつうの $`\mathrm{Kos}(A;a_1(1),\dots,a_m(1))`）。すると
$$`A\simeq R\lim_nR\lim_m\mathrm{Kos}(A;I^n,p^m)\simeq R\lim_nR\lim_m\mathrm{Kos}(A/I^n;p^m)\simeq R\lim_nR\lim_mA/(I^n,p^m)\simeq\lim_kA/(I^k,p^k).`
一つ目は $`A` の導来 $`(p,I)` 完備性、二つ目は $`I^n` が局所的に非零因子で生成されること、三つ目は $`A/I^n` の $`p^\infty` ねじれが有界であること（$`0\to I^{n}/I^{n+1}\to A/I^{n+1}\to A/I^n\to0` と、局所的に $`A/I` に同型な $`I^n/I^{n+1}\cong I^n\otimes_AA/I` による帰納法：$`A/I` の $`p^\infty` ねじれが $`p^N` で消えるなら $`A/I^n` の $`p^\infty` ねじれは $`p^{Nn}` で消える。補った）、四つ目は共終性による。三つ目の段の中身は、有界ねじれの系 $`\{A/I^n[p^m]\}_m` が（$`p` 倍の推移写像について）pro-零になるので $`R\lim_m\mathrm{Kos}(A/I^n;p^m)` の $`H^{-1}` が消えること。

*(2)* 任意の $`n\ge0` について $`M\otimes^L_AA/I^n` は $`A/I^n` 上 $`p` 完全平坦な複体。$`A/I` の $`p^\infty` ねじれが有界なので $`A/I^n` も同様（(1) の証明）。\[BMS19, Lemma 4.7\] により $`M\otimes^L_AA/I^n\simeq M/I^nM` は $`p^\infty` ねじれが有界な離散 $`A/I^n` 加群で、特に $`M[I^n]=0`。$`M` の離散性は、$`M` の導来 $`I` 完備性（$`M\simeq R\lim_nM\otimes^L_AA/I^n`、Mittag-Leffler 系の極限）と $`M\otimes^L_AA/I^n` の離散性から。古典的な $`(p,I)` 完備性は (1) と同様。原典は $`M` の導来 $`(p,I)` 完備性を主張には書かないが、証明で使う（補った注意）。

*(3)* $`(A,I)\to(B,J)` が prism の（忠実）平坦な射なら、仮定から $`B` は $`(p,I)` 完全（忠実）平坦な $`A` 代数で、命題 3.2.1 から $`J=IB`。逆に $`B` が $`(p,I)` 完全（忠実）平坦な δ-$`A` 代数（導来 $`(p,I)` 完備なもの）なら、命題 3.2.1 の後半により $`B[I]=0` を確かめればよく、これは (2) から出る（$`M=B`、$`n=1`）。射については、prism の射 $`(B,IB)\to(B',IB')` は δ-$`A` 代数の射と同じ（$`IB` の像は自動的に $`IB'` に入る）。

*(4)* $`B` を命題 3.1.1 (3) の環 $`A'` の導来 $`(p,I)` 完備化とすると、$`IB=(d)`、$`d` は distinguished（δ 構造は第 2 章の命題 2.2.4 で完備化に延びる）。$`A'` は $`A` 上忠実平坦なので $`B` は $`(p,I)` 完全忠実平坦。(2) から $`B` は離散、$`B/IB` の $`p^\infty` ねじれは有界、$`B[I]=0` なので、命題 3.2.1 の後半で $`(B,IB)` は prism。

*命題 3.2.3（原典 Lemma 3.7：有界 prism の性質） — 原典との差（D5・D19）*

基底は向き付き（D5）。(1) の Lean の経路は Koszul 複体を使わず、古典的な極限で同じことを行う：$`d` 進完備性（生成元が非零因子なので導来完備性と同値）と、各 $`A/d^m` の古典的 $`p` 進完備性（導来 $`p` 完備で $`p` 冪ねじれが $`p^{Nm}` で消えるから）を合わせて $`(p,d)` 進完備性を出す。(2) は原典の \[BMS19, Lemma 4.7\] の代わりに、$`d^n` による導来剰余を、$`(p,d)` の冪で消える係数加群の有限なフィルトレーションに分けて $`A/(p,d)` 上の平坦性に帰着し、離散性と $`H^0` の $`p` 冪ねじれの有界性を出す。(3) は対象の対応の一方向だけを定理にする。(4) は向き付きの基底では要らない（D19）。

:::

:::lemma_ "bs_3_8" (lean := "SerrePositivity.BhattScholze.OrientedPrism.quotient_p_pow_torsion_killed_by_p, SerrePositivity.BhattScholze.perfectPrism_pair_isAdicComplete, SerrePositivity.BhattScholze.OrientedPrism.isDistinguished_generator")
*補題 3.8*　完全 prism の性質。対応表の状態：一部（special）。

完全な向き付き prism の商の全 p 冪ねじれを p が消すことと古典 (p,d) 完備性を証明する。一般の完全 prism の ideal が主であるという結論は向きとして仮定している。

*命題 3.2.5（原典 Lemma 3.8：完全 prism の性質） — 主張*

$`(A,I)` を完全 prism とする。

(1) イデアル $`I` は単項で、その生成元はどれも distinguished 元。

(2) prism $`(A,I)` は有界。特に環 $`A` は古典的に $`(p,I)` 完備。

*命題 3.2.5（原典 Lemma 3.8：完全 prism の性質） — Lean*

(1)：単項性は向き付き prism の定義に入っている。選んだ生成元が distinguished であることは完全性なしにすべての向き付き prism で \`OrientedPrism.isDistinguished\_generator\`（OrientedPrism:176）。他の生成元への取り替えは \`DeltaStructure.isDistinguished\_iff\_of\_span\_eq\`（Distinguished:226）。

(2)：$`A/d` の $`p` 冪ねじれが $`p` で消える \`OrientedPrism.quotient\_p\_pow\_torsion\_killed\_by\_p\`（OrientedPrism:363）（\`IsBoundedPrism\` の $`N=1`。\`IsBoundedPrism\` の形の名前の付いた定理はない）、その入力の第 2 章の命題 2.4.9 \`DeltaStructure.IsPerfect.distinguished\_quotient\_p\_pow\_torsion\_killed\_by\_p\`（DistinguishedRegular:216）。古典的 $`p` 進完備 \`OrientedPrism.isAdicComplete\_p\_of\_perfect\`（OrientedPrism:357）、$`(p,d)` 進完備 \`Andre.perfectPrism\_pair\_isAdicComplete\`（Completeness:335）とその部品 \`Andre.perfectPrism\_generator\_power\_quotient\_prime\_complete\`（:320）。

*命題 3.2.5（原典 Lemma 3.8：完全 prism の性質） — 証明*

(1) $`\varphi\colon A\to A` は同型なので、命題 3.2.2 から出る：$`\varphi(I)A=\varphi(I)` は distinguished 元 $`b` で生成される単項イデアルで、$`I=\varphi^{-1}(\varphi(I))` は $`\varphi^{-1}(b)` で生成される。$`\varphi^{-1}` は δ 射なので $`\varphi^{-1}(b)` は distinguished。他の生成元も命題 3.2.2 と同じく命題 2.3.6 で distinguished。

(2) 生成元 $`d\in I` を選ぶ。命題 3.2.3 (1) により、$`A/d` の $`p^\infty` ねじれが有界であることを確かめれば足りる。第 2 章の命題 2.4.3（原典 Lemma 2.28）により $`A` は $`p` ねじれなし。$`A/p` は完全なので（被約で）、第 2 章の命題 2.4.9（原典 Lemma 2.34）から $`A/d[p^\infty]=A/d[p]`、特に有界。（Lemma 2.34 の仮定の $`p` 進分離性は、$`p` ねじれなしで導来 $`p` 完備なら古典的に $`p` 進完備であることから出る。）

*命題 3.2.5（原典 Lemma 3.8：完全 prism の性質） — 原典との差（D5）*

向き付きなので (1) の単項性は定義に含まれ、生成元の distinguished 性は Lemma 3.6 を経ずに Lemma 2.25 から（完全でない prism でも）出る。(2) の Lean の主張は有界性の具体的な評価 $`N=1` の形。

:::

:::lemma_ "bs_3_9" (lean := "SerrePositivity.BhattScholze.classicalPrismPerfection, SerrePositivity.BhattScholze.existsUnique_classicalPrismPerfectionHom, SerrePositivity.BhattScholze.existsUnique_perfectDeltaPDPrismHom, SerrePositivity.BhattScholze.existsUnique_deltaPerfectionPDCompletionHom, SerrePositivity.BhattScholze.existsUnique_pCompletedPrismHom")
*補題 3.9*　prism の完全化。対応表の状態：一部（special）。

向き付き入力の同じ prism perfection と、完全 prism への射の普遍性を与える。未完備 Aperf の諸正則性と derived/classical 完備化の比較全体は含まない。

*命題 3.3.1（原典 Lemma 3.9：prism の完全化） — 主張*

$`(A,I)` を prism とし、$`A_{\mathrm{perf}}=\mathrm{colim}_\varphi A` を $`A` の完全化とする。このとき $`IA_{\mathrm{perf}}=(d)` は distinguished 元 $`d` で生成され、$`d` と $`p` は $`A_{\mathrm{perf}}` の非零因子で、$`A_{\mathrm{perf}}/d\,[p^\infty]=A_{\mathrm{perf}}/d\,[p]`。特に、$`A_{\mathrm{perf}}` の導来 $`(p,I)` 完備化 $`A_\infty` は古典的 $`(p,I)` 進完備化と一致し、$`(A,I)_{\mathrm{perf}}:=(A_\infty,IA_\infty)` は $`(A,I)` の下の普遍な完全 prism である。

*命題 3.3.1（原典 Lemma 3.9：prism の完全化） — Lean*

*原典の形（向き付きの場合）*：完全化 \`classicalPrismPerfection\`（ClassicalPrismPerfection:34）は δ 完全化の導来 $`(p,d)` 完備化の $`H^0` に入れた向き付き prism。完全性 \`classicalPrismPerfection\_isPerfect\`（:41）、有界性 \`classicalPrismPerfection\_isBounded\`（:46、剰余の $`p^\infty` ねじれは $`p` で消える）、標準射 \`classicalPrismPerfectionMap\`（:54）とその生成元の像 \`classicalPrismPerfectionMap\_generator\`（:68）。普遍性 \`existsUnique\_classicalPrismPerfectionHom\`（:75）：向き付き prism $`Q` から完全な向き付き prism $`Y` への射は、標準射を通って一意に延びる。源の完全性は仮定しない。

*部品*は二系統ある。

(i) 完全化 → 導来 $`(p,d)` 完備化：完全 δ 環と distinguished 元から作る完全 prism \`perfectDeltaPDPrism\`（PrismPerfection:45）とその普遍性 \`existsUnique\_perfectDeltaPDPrismHom\`（:113）、任意の δ 環から完全化を挟んだ普遍性 \`existsUnique\_deltaPerfectionPDCompletionHom\`（:247）。完全 δ 環の導来 $`(p,d)` 完備化の $`H^0` が完全であること \`deltaPDCompletionStructure\_isPerfect\`（DeltaPerfection:375）。

(ii) 完全化 → 古典的 $`p` 進完備化（原典の証明の第一段）：完全 $`p` 進完備 δ 環への普遍性 \`existsUnique\_pCompletedDeltaPerfectionHom\`（PCompletedPerfection:80）。この段での付随の主張：$`p` 倍が単射 \`pCompletedDeltaPerfection\_p\_mul\_injective\`（:124）、$`d` の像が distinguished \`pCompletedDeltaPerfectionMap\_isDistinguished\`（:130）で非零因子 \`pCompletedDeltaPerfectionMap\_mul\_injective\`（:136）、剰余の $`p^\infty` ねじれが $`p` で消える \`pCompletedDeltaPerfection\_quotient\_p\_pow\_torsion\_killed\_by\_p\`（:145）。prism への普遍性 \`existsUnique\_pCompletedPrismHom\`（:515）は、完全化の上での生成元の像の $`d` 進完備性を仮定する。

未完備の $`A_{\mathrm{perf}}` そのものについての主張（$`d`・$`p` の正則性、ねじれ）と、導来完備化と古典的完備化の一致の主張は、この形では本体にない。一般の完全 δ 環の事実としては、$`p` 正則 \`DeltaStructure.IsPerfect.p\_mul\_injective\`（PerfectDelta:96）、distinguished 商の $`p^\infty` ねじれ \`DeltaStructure.IsPerfect.distinguished\_quotient\_p\_pow\_torsion\_killed\_by\_p\`（DistinguishedRegular:216）、$`p` 進分離なら distinguished 元が非零因子 \`DeltaStructure.IsPerfect.distinguished\_mul\_injective\`（:96）がある。

*命題 3.3.1（原典 Lemma 3.9：prism の完全化） — 証明*

*生成元.* $`A\to A_{\mathrm{perf}}` は $`\varphi\colon A\to A` を経由する（第 $`0` 段の $`x` と第 $`1` 段の $`\varphi(x)` が同じ元）ので、$`IA_{\mathrm{perf}}=\varphi(I)A\cdot A_{\mathrm{perf}}`。原典 Lemma 3.6 により $`\varphi(I)A` は distinguished 元で生成される単項イデアルで、δ 射は distinguished 元を distinguished 元に送るので $`IA_{\mathrm{perf}}=(d)`、$`d` は distinguished。

*正則性とねじれ.* $`A_{\mathrm{perf}}` は完全なので p ねじれなし（命題 2.4.3、原典 Lemma 2.28）で、$`A_{\mathrm{perf}}/p` は完全、特に被約。命題 2.4.9（原典 Lemma 2.34）から $`d` は非零因子で $`A_{\mathrm{perf}}/d\,[p^\infty]=A_{\mathrm{perf}}/d\,[p]`。（補った）Lemma 2.34 は $`p` 進分離性を仮定するが、その (2)（ねじれの主張）の証明は分離性を使わない。(1)（$`d` の正則性）は分離性を使うので、未完備の $`A_{\mathrm{perf}}` にそのまま当てるには $`p` 進分離性が要る。次の段で $`p` 進完備化した後なら仮定は満たされ、原典もそこで改めて Lemma 2.34 を引く。

*完備化.* まず $`p` 進完備化する。$`A_{\mathrm{perf}}` は p ねじれなしなので導来 $`p` 完備化と古典的 $`p` 進完備化は一致し（Koszul 複体 $`\mathrm{Kos}(-;p^n)` が $`H^0` に集中するので $`\mathrm{R}\lim` が通常の $`\lim` になる）、完備化も完全 δ 環で（完全性は余極限・完備化で保たれる）、Lemma 2.34 により $`d` は依然非零因子。完備化を改めて $`A_{\mathrm{perf}}` と書くと、これは $`p` 進完備なので各商 $`A_{\mathrm{perf}}/d^n` は導来 $`p` 完備（導来完備な加群の余核）で、$`p^\infty` ねじれは有界（$`d^n` の商についても Lemma 2.34 (2) と同じ論法。命題 2.4.9 の Lean の囲みにある冪 $`d^n` の版）なので古典的に $`p` 進完備。よって次に $`d` 進完備化しても導来と古典的が一致し（$`d` 正則なので $`\mathrm{Kos}(-;d^n)=A/d^n`）、結果は古典的に $`(p,d)` 進完備。

*普遍性.* 完全 prism $`(B,J)` と prism の射 $`(A,I)\to(B,J)` について、$`B` は完全なので $`A\to B` は $`A_{\mathrm{perf}}\to B` に一意に延び（完全化の普遍性、原典 Rem 2.27 の左随伴）、$`B` は $`(p,I)` 完備（完全 prism は有界、原典 Lemma 3.8）なので $`A_\infty\to B` に一意に延びる。$`IA_\infty` が $`J` に入ることは $`IB\subset J` から。

*命題 3.3.1（原典 Lemma 3.9：prism の完全化） — 原典との差（D5・D7）*

Lean の prism は向き付き（単項イデアルと生成元を持つ）なので、生成元の段（原典 Lemma 3.6 の適用）は不要で、$`d` の像をそのまま生成元にする（D5）。完全化の構成は「完全 δ 環と distinguished 元から完全 prism を作る」部品に分け、その上に原典の形の普遍性の定理を置く（D7）。完備化は導来 $`(p,d)` 完備化の $`H^0` で一段で取り、原典のように $`p` 進・$`d` 進の二段に分けない。そのため導来と古典的の一致は主張として現れない。

:::

:::theorem "bs_3_10" (lean := "SerrePositivity.BhattScholze.OrientedPrism.quotient_isIntegralPerfectoid, SerrePositivity.BhattScholze.exists_perfectoidTrialPrism, SerrePositivity.BhattScholze.existsUnique_perfectPrismHomLift, SerrePositivity.BhattScholze.wittDistinguishedQuotient_isIntegralPerfectoid, SerrePositivity.BhattScholze.Semiperfectoid.exists_fontaineCompatibleWittEquiv, SerrePositivity.BhattScholze.Semiperfectoid.exists_ainfClassicalPrism")
*定理 3.10*　perfectoid 環 ＝ 完全 prism。対応表の状態：一部（component）。

完全向き付き prism の商の perfectoid 性、perfectoid 環の prism 表示および射の持ち上げ・Witt 回収を個々に与える。絶対圏の関手と自然同型からなる原文の圏同値そのものは未供給。

*定理 3.4.1（原典 Thm 3.10：perfectoid 環 ＝ 完全 prism） — 主張*

次の二つの圏は同値である。

- perfectoid 環 $`R`（\[BMS18, §3\] の意味）の圏。

- 完全 prism $`(A,I)` の圏。

関手はそれぞれ $`R\mapsto(A_{\inf}(R),\ker(\theta))` と $`(A,I)\mapsto A/I`。

*定理 3.4.1（原典 Thm 3.10：perfectoid 環 ＝ 完全 prism） — Lean*

圏同値としてではなく、対象と射についての次の事実で述べる（D8）。

(a) *完全 prism の商は perfectoid*（関手 $`G` の対象の部分）：\`OrientedPrism.quotient\_isIntegralPerfectoid\`（PerfectPrismPerfectoid:340）。Witt 表示 $`W(A/p)\cong A` \`perfectPrismWittRecoveryEquiv\`（:240）（原典 Cor 2.31）を経て、完備な distinguished Witt 商が perfectoid であること \`wittCompleteDistinguishedQuotient\_isIntegralPerfectoid\`（WittQuotientPerfectoid:562）に帰着する。$`d` 進完備性を仮定しない版 \`wittDistinguishedQuotient\_isIntegralPerfectoid\`（PerfectPrismPerfectoid:422）。Witt 商の計算（mod $`p`、Frobenius の核、tilt、Fontaine の比較）は \`WittQuotientTilt\`・\`WittQuotientPerfectoid\` の 2 本。

(b) *perfectoid 環は完全 prism の商*（関手 $`F` の対象の部分）：Fontaine 核の distinguished 生成元 \`exists\_distinguished\_fontaine\_kernel\_generator\`（PerfectPrismPerfectoid:121）と、$`W(R^\flat)` の導来 $`(p,d)` 完備化の $`H^0` による表示 \`exists\_perfectoidTrialPrism\`（:383）（$`p` が $`R` の単元でない場合）。$`W(R^\flat)` そのものとの比較：剰余が $`R` の完全 prism $`(A,(d))` は、固定した $`W(R^\flat)` と δ 構造・$`\theta` を保って同型 \`exists\_fontaineCompatibleWittEquiv\`（PerfectoidWittEquiv:72）。したがって $`W(R^\flat)` 自身に、$`\theta` を剰余写像とする有界な完全 prism の構造が入る \`exists\_fontainePrism\_of\_perfectPresentation\`（FontainePrism:29）。零環の場合も合わせて、perfectoid $`R` に対し係数環 \`ainfClassicalCoefficients\`（AinfClassical:45）（$`p` が単元なら $`R`、そうでなければ $`W(R^\flat)`）の上に、$`\theta` を保つ剰余同型を持つ有界な完全 prism がある \`exists\_ainfClassicalPrism\`（:105）。これが $`R\mapsto(A_{\inf}(R),\ker\theta)` の対象ごとの形にあたる。

(c) *射の持ち上げ*（充満忠実性）：完全 prism の商の間の環準同型は prism の射に一意に持ち上がる \`existsUnique\_perfectPrismHomLift\`（PerfectPrismHomLift:522）（両方の商で $`p` が単元でない場合）。標的が一般の有界な向き付き prism の版 \`existsUnique\_perfectPrismHomLift\_to\_bounded\`（:749）は原典 Lemma 4.8 にあたる（第 4 章）。

圏同値の形は本体にない。drafts の \`perfectSiteEquivPerfectoidUnder\`（drafts/A5/PerfectSite:267、sorry あり）は、固定した基底の上の完全 site と、その下の perfectoid 環の圏の同値（原典 Lemma 4.8 の系の形）。

*定理 3.4.1（原典 Thm 3.10：perfectoid 環 ＝ 完全 prism） — 証明*

\*\*$`F`.\*\* perfectoid 環 $`R` について、$`A_{\inf}(R)=W(R^\flat)` は完全 δ 環（完全 $`\mathbb F_p` 代数の Witt 環）で、$`\ker\theta` は非零因子である distinguished 元で生成される（\[BMS18, Rem 3.11\]）。$`A_{\inf}(R)` は構成から古典的に $`(p,\ker\theta)` 完備なので導来 $`(p,\ker\theta)` 完備でもあり、$`(A_{\inf}(R),\ker\theta)` は完全 prism。

\*\*$`G`.\*\* 完全 prism $`(A,I)` について、原典 Lemma 3.8 から $`I=(d)`（$`d` は distinguished な非零因子）で、$`A` は古典的に $`(p,d)` 完備。$`R=A/d` が perfectoid であることを示す。$`A` が完全なので $`R/p` の Frobenius は全射。系 2.4.6（原典 Cor 2.31）で $`A\cong W(S)`（$`S` は完全 $`\mathbb F_p` 代数）とし、命題 2.4.8（原典 Lemma 2.33）で $`d=[a_0]+pu`（$`u` 単元）と書ける。$`\pi\in R` を $`[a_0^{1/p}]` の像とすると $`\pi^p` は $`[a_0]\equiv -pu` の像なので $`\pi^p\mid p`。最後に、$`R` は導来 $`p` 完備な加群の写像 $`A\xrightarrow{d}A` の余核なので導来 $`p` 完備で、命題 2.4.9（原典 Lemma 2.34）で $`p^\infty` ねじれが有界なので古典的に $`p` 進完備。$`\ker\theta` の単項性は次の段の同型 $`A_{\inf}(R)\cong A` から出る。

\*\*$`GF\simeq\mathrm{id}`\*\* は構成から（$`A_{\inf}(R)/\ker\theta=R`）。\*\*$`FG\simeq\mathrm{id}`\*\*：完全 prism $`(A,I)` について $`(A,I)\cong(A_{\inf}(A/I),\ker\theta)` を示す。$`A_{\inf}(A/I)\xrightarrow{\theta}A/I` は $`A/I` の普遍な pro 無限小 thickening なので、$`A\to A/I` と両立する $`A_{\inf}(A/I)\to A` がただ一つあり、特に $`\ker(\theta)A\subset IA`。系 2.4.6 によりこれは自動的に δ 射。$`\ker\theta` と $`I` はどちらも distinguished 元で生成されるので、命題 2.3.6（原典 Lemma 2.24）から $`\ker\theta=dA_{\inf}(A/I)` なら $`I=dA`。$`d` は両方の環で非零因子（Lemma 2.34）で、両方とも $`d` 進完備。最後に $`A_{\inf}(A/I)/d\to A/d` は両辺とも $`A/I` と同一視されて同型なので、$`d` 進完備で $`d` 正則な環の間の写像として $`A_{\inf}(A/I)\to A` は同型。

*定理 3.4.1（原典 Thm 3.10：perfectoid 環 ＝ 完全 prism） — 原典との差（D8・D9）*

原典は関手の圏同値として述べるが、Lean は (a)〜(c) の対象と射の事実で述べる（D8）。(b) の表示は原典の $`A_{\inf}(R)` そのものではなく $`W(R^\flat)` の導来 $`(p,d)` 完備化の $`H^0` を一段挟み、$`W(R^\flat)` との比較は別の定理（\`exists\_fontaineCompatibleWittEquiv\`）で戻す。Fontaine の比較には一般版と、仮定を足した版の二系統がある（D9）。

:::

:::proposition "bs_3_11"
*注意 3.11*　正則局所環の perfectoid 被覆。対応表の状態：なし。

完備正則局所環の Cohen 表示から Frobenius lift と忠実平坦 perfectoid 被覆を作る宣言を未同定。

*注意 3.4.2（原典 Rem 3.11：正則局所環の perfectoid 被覆） — 主張*

$`R` を次元 $`d`、剰余体 $`k` の標数が $`p>0` の完備ネーター正則局所環とし、混標数（$`R` は p ねじれなし）とする。prism の形式論で、忠実平坦な写像 $`R\to R_\infty`（$`R_\infty` は perfectoid）が作れる（\[And18b, Ex 3.4.6 (3)\]・\[Bha18a, Prop 5.2\] の構成の説明）。

手順：$`k` の Cohen 環 $`W` と Frobenius 持ち上げ $`\varphi_W` を選び、Cohen の構造定理で $`R=A/(f)`、$`A:=W[[x_1,\dots,x_d]]`、$`f\in\mathfrak m-\mathfrak m^2`（$`\mathfrak m=(p,x_1,\dots,x_d)`）と書く。$`\mathfrak m/\mathfrak m^2` で $`f=a_0p+\sum_{i=1}^d a_ix_i`（$`a_i\in k`）とする。

- $`a_0\ne0` のとき：$`\varphi_W` を延ばし $`\varphi_A(x_i)=x_i^p` とする Frobenius 持ち上げで $`A` を δ 環にすると、$`f` は distinguished。

- $`a_0=0` のとき：変数を取り替えて $`f=x_1-p` とでき、同じ δ 構造で $`f` は distinguished。

こうして $`(A,(f))` は prism。$`A/p=k[[x_1,\dots,x_d]]` は正則なので $`\varphi_A` は $`p` 完全忠実平坦。$`(A,(f))` の完全化を $`(A_\infty,(f))`（命題 3.3.1。原典は「Proposition 3.9」と書く）、対応する perfectoid 環を $`R_\infty=A_\infty/(f)`（定理 3.4.1）とすると、$`(A,(f))\to(A_\infty,(f))` は完全な標的への忠実平坦な prism の射なので、$`R\to R_\infty` は $`p` 完全忠実平坦で $`R_\infty` は perfectoid。$`R` はネーターなので $`R\to R_\infty` は実際に忠実平坦である（\[Bha18a, Prop 5.1\]）。

*注意 3.4.2（原典 Rem 3.11：正則局所環の perfectoid 被覆） — 証明*

\*\*$`a_0\ne0` の場合.\*\* $`x_i\mapsto0` で与える評価 $`A\to W` は δ 射（$`\varphi_A(x_i)=x_i^p` は $`0` に行き、$`W` 上では $`\varphi_W`）で、核 $`(x_1,\dots,x_d)` は位相的冪零（$`A` は局所環で核は $`\mathfrak m` に入る）。$`f` の像 $`f(0)\in W` は $`p` 進付値 $`1`、すなわち $`f(0)=pv`（$`v\in W^\times`）。$`\delta(pv)=v^p\delta(p)+p^p\delta(v)+p\,\delta(p)\delta(v)\equiv v^p\bmod p` は単元なので $`f(0)` は distinguished。（補った）δ 射は δ と可換なので $`\delta(f)` の像は単元 $`\delta(f(0))`。核は $`\mathfrak m` に入るので、像が単元である $`A` の元は $`\mathfrak m` に入らず、局所環 $`A` で単元。よって $`f` は distinguished（原典は「核が位相的冪零な δ 射の像が distinguished なら distinguished」と一言で済ませる）。

\*\*$`a_0=0` の場合.\*\*（補った）$`f` の $`\mathfrak m/\mathfrak m^2` での像は $`x_i` の $`k` 線形結合で $`0` でないので、番号を付け替えて $`a_1\ne0` としてよい。$`x_1':=f+p` と置くと、$`p,x_1',x_2,\dots,x_d` の像は $`\mathfrak m/\mathfrak m^2` の基底をなすので、$`x_1\mapsto x_1'`、$`x_i\mapsto x_i`（$`i\ge2`）で定まる連続な $`W` 代数の自己準同型 $`A\to A` は同型（完備局所環の間で、余接空間に同型を引き起こす全射）。新しい座標で $`f=x_1'-p`。前の段と同じ δ 構造（新しい座標について $`\varphi_A(x_i)=x_i^p`）で、評価 $`A\to W` は $`f` を $`-p` に送り、$`-p` は distinguished なので $`f` は distinguished。

*平坦性.* $`A` は p ねじれなしなので、$`\varphi_A` の $`p` 完全（忠実）平坦性は mod $`p` の Frobenius $`k[[x]]\to k[[x]]` の（忠実）平坦性に帰着し、これは正則環の Frobenius の平坦性（Kunz の定理の易しい側）。完全化 $`A_{\mathrm{perf}}=\mathrm{colim}_\varphi A` は $`p` 完全忠実平坦な写像の余極限なので $`A` 上 $`p` 完全忠実平坦で、$`(p,f)` 完備化しても同様（原典 Lemma 3.7 (3) の意味で忠実平坦な prism の射）。$`\bmod f` で底変換して $`R\to R_\infty` が $`p` 完全忠実平坦。$`R_\infty` の perfectoid 性は定理 3.4.1。最後の忠実平坦性は、$`R` がネーターであることを使って \[Bha18a, Prop 5.1\] から出る。

:::

:::corollary "bs_3_12" (lean := "SerrePositivity.BhattScholze.Prismatic.PrismOver.flatTopology, SerrePositivity.BhattScholze.Prismatic.PrismOver.exists_isPushout_isFaithfullyFlat, SerrePositivity.BhattScholze.Prismatic.PrismOver.isSheaf_of_flatRingCechExact, SerrePositivity.BhattScholze.Prismatic.PrismOver.isPushout_flatResidueRing, SerrePositivity.BhattScholze.Prismatic.PrismOver.structureRing_isSheaf, SerrePositivity.BhattScholze.Prismatic.PrismOver.quotientStructureRing_isSheaf")
*系 3.12*　全 prism の site。対応表の状態：一部（special）。

固定向き付き有界基底と濃度 cutoff の site に限り、flat topology と同じ構造環・商環の層条件を証明する。全 bounded prism の site と RΓ の高次消滅との接続は未供給。

*系 3.4.3（原典 Cor 3.12：prism の site） — 主張*

有界 prism $`(A,I)` 全体の圏の反対圏に、被覆を忠実平坦な prism の射で定める位相を入れると site になる。$`(A,I)` を $`A`（resp. $`A/I`）に送る関手はこの位相の層で、任意の $`(A,I)` 上で高次コホモロジーが消える。

*系 3.4.3（原典 Cor 3.12：prism の site） — Lean*

対象は有界 prism 全体ではなく、固定した向き付き有界 prism $`(A,(d))` と $`A/d` 代数 $`R` について、$`(A,(d))` 上の有界な向き付き prism $`(B,dB)` と $`R\to B/dB` の組で、台の濃度が $`\le\kappa` のもの \`PrismOver\`（PrismOver:68）（原典 Def 4.1 の affine の場合。許容濃度 \`IsAdmissibleCutoff\`（:60）。D5・D16・D19）。

*位相*：忠実平坦な射（$`(p,d)` 完全忠実平坦）\`PrismOver.IsFaithfullyFlat\`（FlatCover:40）一本の被覆 \`flatCoverage\`（FlatSiteSheaf:36）が生成する Grothendieck 位相 \`flatTopology\`（:50）（D22）。site の公理の中身：同型は被覆 \`isFaithfullyFlat\_of\_isIso\`（FlatCover:45）、合成 \`IsFaithfullyFlat.comp\`（:61）、忠実平坦な射の任意の射に沿う押し出しが存在して忠実平坦 \`exists\_isPushout\_isFaithfullyFlat\`（FlatTopologyPushout:43）。押し出しの台環は完備テンソル積 \`exists\_completedTensor\_pushoutEquiv\`（FlatSiteResidue:54）で、$`p` と $`d` の冪を含むイデアルで剰余すると環の押し出し \`isPushout\_flatResidueRing\`（:209）。完全平坦な δ 代数が有界 prism を与えること（原典 Lemma 3.7 (3) の向き）は \`exists\_boundedPrism\_of\_completelyFlat\_deltaAlgebra\`（CompletelyFlatPrism:70）。

*層条件*：構造環 \`structureRing\`・剰余 \`quotientStructureRing\`（FlatSiteSheaf:54・61）について、忠実平坦な被覆の増大完備 Čech 余脈体が全次数で完全 \`structureRing\_flatCechExact\`・\`quotientStructureRing\_flatCechExact\`（FlatCechDescent:100・136）、環値の前層としての層条件 \`structureRing\_isSheaf\`・\`quotientStructureRing\_isSheaf\`（:179・184）。完全性から層条件を出す一般の補題 \`isSheaf\_of\_flatRingCechExact\`（FlatCechSheaf:49）、有限段の剰余から完全性を戻す補題 \`flatRingCechExact\_of\_residues\`（FlatCechLimit:163）。高次コホモロジーの消滅は Čech 余脈体の完全性の形で述べ、$`D(A)` 値の層や $`R\Gamma` の形では本体にない。drafts の \`structurePresheafDerived\_isSheaf\`・\`reducedStructurePresheafDerived\_isSheaf\`・\`prismaticCohomology\_isLimit\`（drafts/A0/FlatDescent:197・214・222、sorry あり）がその形。

*系 3.4.3（原典 Cor 3.12：prism の site） — 証明*

*site の公理.* 示すのは (a) 同型は被覆、(b) 被覆の合成は被覆、(c) 被覆の任意の射に沿う押し出しは被覆。(a)(b) は自明。(c) は原典 Lemma 3.5（剛性）の記述を使うと、有界 prism の射の図式 $`(C,IC)\xleftarrow{c}(A,IA)\xrightarrow{b}(B,IB)`（$`b` は忠実平坦）について、$`b` の $`c` に沿う押し出しが存在して忠実平坦であることに帰着する。$`D` を $`B\otimes^L_AC` の導来 $`(p,I)` 完備化とすると、標準的な性質から $`D` は $`C` 上 $`(p,I)` 完全忠実平坦で、原典 Lemma 3.7 から $`(C,IC)\to(D,ID)` は有界 prism の忠実平坦な射。これが押し出しになることは確かめられる。

*層条件.* $`(A,I)\to(B,IB)` を忠実平坦な prism の射とし、その有界 prism の圏での Čech 脈体 $`(B^\bullet,IB^\bullet)` を $`(A,I)` 上の余単体的有界 prism とみる。前段から $`B^\bullet` は $`A\to B` の導来 Čech 脈体（$`D(A)` の余単体的対象）の導来 $`(p,I)` 完備化である。したがって各 $`n` で $`\mathrm{Kos}(A;p^n,I^n)\to\mathrm{Kos}(B^\bullet;p^n,I^n)` は、単体的可換環の写像の忠実平坦降下により $`D(A)` の極限図式。$`n` について逆極限を取ると $`A\to B^\bullet` も $`D(A)` の極限図式で、これが層条件と高次 Čech コホモロジーの消滅を与える。$`(A,I)\mapsto A/I` の場合は、$`D(A)` での同値 $`A\simeq\lim B^\bullet` を完全複体 $`A/I` とテンソルする。

*系 3.4.3（原典 Cor 3.12：prism の site） — 原典との差（D5・D16・D19・D22）*

site の対象を、固定した向き付き基底 $`(A,(d))` の上の向き付き prism に限り（D5・D19。基底が向き付きなら剛性で自動的に向き付き）、濃度 $`\le\kappa` で切り落とす（D16）。位相は「site であることを示してから被覆を定める」のではなく、忠実平坦な単一射の被覆が生成する位相として定義し、押し出しの存在を定理にする（D22）。層条件の証明は原典と同じ筋で、$`D(A)` の極限図式の代わりに、各 $`(p^n,d^n)` 剰余（$`A/I` では $`(d,p^n)` 剰余）での通常の忠実平坦降下と、全射の逆塔の逆極限で Čech 余脈体の完全性を戻す。

:::

:::proposition "bs_3_13" (lean := "SerrePositivity.BhattScholze.Prismatic.exists_prismaticEnvelope_of_variables, SerrePositivity.BhattScholze.Prismatic.IsPrismaticEnvelope, SerrePositivity.BhattScholze.Prismatic.IsPrismaticEnvelope.unique, SerrePositivity.BhattScholze.Prismatic.prismaticEnvelope_completedBaseChange_of_variables")
*命題 3.13*　正則イデアルの prismatic envelope。対応表の状態：一部（special）。

向き付き基底、B が完備自由 δ 環、J が d と変数で生成される場合の envelope の存在・普遍性・完全平坦性と底変換。一般の相対完全正則列と flat localization (3) は含まない。

*命題 3.5.1（原典 Prop 3.13：正則イデアルの prismatic envelope） — 主張*

$`(A,I)` を有界 prism、$`B` を $`(p,I)` 完全平坦な δ-$`A` 代数とし、$`J\subset B` を $`IB` を含むイデアルとする（δ 対の写像 $`(A,I)\to(B,J)` が定まる）。$`\mathrm{Spf}(B)` 上 Zariski 局所的に、$`A` 上相対的に $`(p,I)` 完全正則な列（定義 2.6.1、原典 Def 2.42）$`x_1,\dots,x_r\in B` によって $`J=(I,x_1,\dots,x_r)` と書けると仮定する。

このとき、$`(A,I)` 上の prism $`(C,IC)` への δ 対の普遍な写像 $`(B,J)\to(C,IC)` が存在する。紛れがなければ $`C:=B\{\tfrac JI\}^\wedge` と書く。この普遍対象は次を満たす。

1. $`(B\{\tfrac JI\}^\wedge,IB\{\tfrac JI\}^\wedge)` は $`(A,I)` 上 $`(p,I)` 完全平坦。

2. 構成 $`(B,J)\mapsto(B\{\tfrac JI\}^\wedge,IB\{\tfrac JI\}^\wedge)` は、有界 prism の任意の射 $`(A,I)\to(A',IA')` に沿う底変換と可換。

3. 構成は $`B` の平坦局所化と両立する：$`B\to B'` が δ-$`A` 代数の $`(p,I)` 完全平坦な写像なら $`B\{\tfrac JI\}^\wedge\widehat\otimes^L_BB'\cong B'\{\tfrac{J'}I\}^\wedge`（$`J'=JB'`）。

写像 $`(B,J)\to(B\{\tfrac JI\}^\wedge,IB\{\tfrac JI\}^\wedge)` を、有界 prism $`(A,I)` 上の δ 対 $`(B,J)` の *prismatic envelope* と呼ぶ。

*命題 3.5.1（原典 Prop 3.13：正則イデアルの prismatic envelope） — Lean*

*普遍性（定義）は一般の形*：envelope であることの述語 \`IsPrismaticEnvelope\`（Envelope:39）。基底は向き付き prism $`(A,(d))`、δ-$`A` 代数 $`B`（δ 構造と δ 射 $`\iota\colon A\to B`）、$`d` の像を含むイデアル $`J`、向き付き prism $`(C,dC)` と δ 射 $`\eta\colon B\to C` について、$`J\mapsto dC` で、$`(A,(d))` 上の任意の向き付き prism（有界性を要求しない）への同じ条件の δ 射が $`\eta` を一意に経由すること。同型を除いて一意 \`IsPrismaticEnvelope.unique\`（:60）、$`J` を完備閉包に置き換えてもよい \`IsPrismaticEnvelope.of\_closure\`（:125）。

一般の完全正則な $`J` での存在と (3) は本体にない。仮定の形（古典環の相対完全正則性、定義 2.6.1）は \`IsPrismCompletelyRegularRel\`（RelativeCompleteRegularity:156）として定義だけある。原典の証明の部品のうち、$`\varphi(y)=pu` の単元係数は \`exists\_classicalPDivision\_unit\_factor\`（PDivisionCompletion:623）、$`d` で割る δ 包の生の構成は \`Delta/Division/\`。

*命題 3.5.1（原典 Prop 3.13：正則イデアルの prismatic envelope） — 証明*

*向き付き・大域的な場合への帰着.* まず $`(A,I)` が向き付き（$`I` が単項）の場合に示せば十分：向き付きの場合の (2) と、導来 $`(p,I)` 完備で $`(p,I)` 完全平坦な $`A` 加群の $`(p,I)` 完全忠実平坦降下（原典 Lemma 3.7 の後の注意）から一般の場合が出る（Lemma 3.7 (4) で局所的に向き付ける）。以下 $`I=(d)`。次に、$`J=(I,x_1,\dots,x_r)` が大域的に成り立つ場合に示せば十分：同様の議論を (2) の代わりに (3) で行う。ただし $`B\{\tfrac JI\}^\wedge` は一般に $`B` 上 $`(p,I)` 完全平坦ではないので、平坦な対象に制限した層ではなく $`D_{(p,I)\text{-comp}}(-)` 全体の層の性質を使う。

*構成と普遍性.* $`C:=B\{\tfrac{x_1}d,\dots,\tfrac{x_r}d\}^\wedge` を、導来 $`(p,I)` 完備な単体的 δ-$`A` 代数の圏で $`x_i/d` を自由に添加したもの（系 2.6.6 のような押し出し）とする。$`C` が $`A` 上 $`(p,I)` 完全平坦であることを示せば命題が従う。実際、そのとき原典 Lemma 3.7 から $`C` は離散で $`d` ねじれなしなので $`(C,(d))` は $`(A,(d))` 上の有界 prism で、構成から $`(B,J)\to(C,(d))` がある。普遍性は明らか：$`d` ねじれなしで $`(p,d)` 完備な δ 環 $`D` への $`C` からの写像を与えることは、$`x_i`、したがって $`J` を $`dD` に送る $`B\to D` を与えることと同じ。(2) は $`C` が $`\{x_i/d\}` 上の自由な導来 $`(p,I)` 完備 δ-$`B` 代数であることから、(3) は普遍性（または $`C` の定義と、$`B\to B'` の完全平坦性により $`x_1,\dots,x_r\in B'` も相対完全正則であること）から明らか。

*平坦性.* 導来 $`(p,d)` 完備な単体的可換 δ 環の可換図式

$$`\begin{array}{ccccccc} \mathbb Z_p\{z\}^\wedge &\xrightarrow{z\mapsto d}& A &\to& B &\to& B\{\tfrac{x_1}d,\dots,\tfrac{x_r}d\}^\wedge=:C\\ \downarrow{\scriptstyle\psi\colon z\mapsto\varphi(y)} && \downarrow && \downarrow && \downarrow\\ \mathbb Z_p\{y\}^\wedge &\to& A' &\to& B' &\to& B'\{\tfrac{x_1}{\varphi(y)},\dots,\tfrac{x_r}{\varphi(y)}\}^\wedge=:C'\\ && \downarrow && \downarrow && \downarrow\\ && D:=A'\{\tfrac{\varphi(y)}p\}^\wedge &\to& B'' &\to& B''\{\tfrac{x_1}p,\dots,\tfrac{x_r}p\}^\wedge=:C'' \end{array}`

を考える。第一行が入力で、左上の $`\psi` は自由 $`(p,z)` 完備 δ 環 $`\mathbb Z_p\{z\}^\wedge` の Frobenius と抽象的に同一視され、四角はすべて左上の頂点の上の $`(p,z)` 完備な単体的可換環の導来押し出し。右下の頂点の記述は、$`\pi_0(D)` で $`\varphi(y)=p\cdot u`（$`u` 単元。命題 2.3.6、原典 Lemma 2.24）であることから。$`\psi` は $`(p,z)` 完全忠実平坦なので第一行と第二行を結ぶ縦の写像もすべてそうで、$`A'\to C'` が $`(p,z)` 完全平坦であることを示せばよい。$`D\to C''` は系 2.6.6（原典 Cor 2.44）で $`(p,z)` 完全平坦（仮定は底変換で保たれる）。よって $`A'` 上の $`(p,z)` 完全平坦性（同値に $`(p,y)` 完全平坦性）が $`A'\to D` に沿う底変換で検出できることを示せば足りる。系 2.5.5（原典 Cor 2.39）から $`D` は $`A'` に $`y` の divided power を自由に添加した環と同一視される。$`A'` 代数の $`(p,y)` 完全平坦性は $`A'\to\mathrm{Kos}(A';p,y)` への底変換後の平坦性で定義されるので、$`A'` 代数の写像 $`D\to\mathrm{Kos}(A';p,y)` があればよく、これは普遍な場合 $`A'=\mathbb Z_p\{y\}` に帰着して容易に分かる。

*命題 3.5.1（原典 Prop 3.13：正則イデアルの prismatic envelope） — 原典との差（D5・D21）*

基底は向き付き prism に限る（D5）。普遍性（定義）は原典の一般の形で入れ、存在は完備自由 δ 代数と変数で生成されるイデアルの場合（例 3.5.2 の状況を変数変換した形）だけ（D21）。その場合の envelope は完備自由 δ 代数そのもの（変数の置換）なので、存在と平坦性の証明は原典の図式（系 2.5.5・系 2.6.6 を使う Frobenius の底変換）を経由しない。

:::

:::proposition "bs_3_14" (lean := "SerrePositivity.BhattScholze.Prismatic.exists_prismaticEnvelope_of_variables, SerrePositivity.BhattScholze.Prismatic.isPrismaticEnvelope_variableSubstitution, SerrePositivity.BhattScholze.Prismatic.IsPrismaticEnvelope.of_closure")
*例 3.14*　Prop 3.13 の典型的な適用。対応表の状態：一部（special）。

自由変数と variable substitution の場合の同じ envelope の普遍性と存在。任意の完全滑らかな B₀→R の場合は扱わない。

*例 3.5.2（原典 Ex 3.14：命題 3.5.1 の典型的な適用） — 主張*

$`R` を $`p` 完全に滑らかな $`A/I` 代数、$`B_0\to R` を導来 $`(p,I)` 完備な $`A` 代数の全射で $`B_0` は $`A` 上 $`(p,I)` 完全に滑らか、$`B_0\to B` を $`(p,I)` 完全平坦な写像で $`B` は δ-$`A` 代数とする。$`J\subset B` を $`\ker(B_0\to R)` の像で生成される導来 $`(p,I)` 完備なイデアル、同値に $`B\to R\widehat\otimes^L_{B_0}B` の核とする。このとき対 $`(B,J)` は命題 3.5.1 の仮定を満たす。したがって (1)(2)(3) を満たす prismatic envelope $`(B,J)\to(B\{\tfrac JI\}^\wedge,IB\{\tfrac JI\}^\wedge)` が作れる。

*例 3.5.2（原典 Ex 3.14：命題 3.5.1 の典型的な適用） — Lean*

変数の場合が本体にある：$`B` が完備自由 δ-$`A` 代数 $`A\{X_S\}^\wedge` で、$`J` が $`d` と変数の部分集合 $`\{X_z\}_{z\in Z}` で生成される場合の存在と平坦性 \`exists\_prismaticEnvelope\_of\_variables\`（CompletedFreeDeltaFlat:125）、その envelope が変数の置換であること \`isPrismaticEnvelope\_variableSubstitution\`（VariableEnvelope:143）。原典の「導来 $`(p,I)` 完備なイデアル」としての $`J` は、生成されたイデアルを完備閉包に置き換える \`IsPrismaticEnvelope.of\_closure\`（Envelope:125）で扱う。一般の $`p` 完全に滑らかな $`B_0\to R` と平坦な $`B_0\to B` からの存在は本体にない。

*例 3.5.2（原典 Ex 3.14：命題 3.5.1 の典型的な適用） — 証明*

（補った）原典は「仮定を満たす」とだけ述べる。示すことは、$`\mathrm{Spf}(B)` 上 Zariski 局所的に $`J=(I,x_1,\dots,x_r)` と、$`A` 上相対的に $`(p,I)` 完全正則な列で書けること。

$`B_0` と $`R` はどちらも（$`A` 上、$`A/I` 上）$`p` 完全に滑らかなので、$`B_0/I\to R` は $`p` 完全に滑らかな $`A/I` 代数の間の全射で、その核は Zariski 局所的に正則列 $`\bar x_1,\dots,\bar x_r` で生成される（滑らかな代数の間の全射は正則な閉埋め込み。ヤコビアン判定法で局所的に座標の一部を切り出す形になる）。$`x_i\in B_0` を持ち上げとすると、$`\ker(B_0\to R)` は局所的に $`(I,x_1,\dots,x_r)` の完備閉包で、局所的に $`\mathrm{Kos}(B_0;p,I,x_1,\dots,x_r)\simeq\mathrm{Kos}(R;p)` で、これは $`\mathrm{Kos}(A;p,I)\simeq\mathrm{Kos}(A/I;p)` 上平坦（$`R` は $`A/I` 上 $`p` 完全平坦）なので、$`x_1,\dots,x_r` は $`A` 上相対的に $`(p,I)` 完全正則。相対完全正則性は $`(p,I)` 完全平坦な底変換 $`B_0\to B` で保たれる（Koszul 複体の比較が底変換で保たれる）ので、$`B` での像についても同じ。$`J` は導来 $`(p,I)` 完備なイデアルとして生成されるが、envelope の普遍性は $`J` を生成元のイデアルに置き換えても変わらない（標的は $`(p,I)` 完備）。

*例 3.5.2（原典 Ex 3.14：命題 3.5.1 の典型的な適用） — 原典との差（D21）*

本体の存在定理は、$`B` が完備自由 δ 代数で $`J` が変数で生成される場合に限る（D21）。Čech–Alexander 複体の各項（原典 Constr 4.17）では $`R` が多項式代数で $`B` が完備自由 δ 代数なので、変数を取り替えればこの形になる。

:::

