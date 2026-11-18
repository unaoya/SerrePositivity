import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.BhattScholze.Andre.AndreFlatness
import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Initiality
import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.VarpiComparison
import SerrePositivity.BhattScholze.Andre.Transfinite.Tower
import SerrePositivity.BhattScholze.Semiperfectoid.Discrete.PrismRetract
import SerrePositivity.BhattScholze.Semiperfectoid.Perfection.Perfectoidization
import SerrePositivity.BhattScholze.Semiperfectoid.Quasiregular.RootRelationPerfection
import SerrePositivity.BhattScholze.Semiperfectoid.Surjectivity.RootEnvelope.PerfectPrism
import SerrePositivity.BhattScholze.Semiperfectoid.Surjectivity.Surjectivity
import SerrePositivity.CategoryTheory.InitialOfRetraction
import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosed.Basic

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "§7 Semiperfectoid rings and perfection in mixed characteristic" =>
%%%
number := false
tag := "bs-7"
%%%

BS §7 の項目と、本体の宣言との対応。本文は対応表（`research/bs-coverage`）の照合の理由で、原典の本文の写しではない。

*導入*

§7 は三つの小節からなる。§7.1 は semiperfectoid 環 $`S`（perfectoid 環の商）について、全ての prism の中での始対象（Prop 7.2）と普遍 perfectoid 環 $`S_{\mathrm{perfd}}`（Cor 7.3）を作り、主定理「$`S\to S_{\mathrm{perfd}}` は全射」（Thm 7.4）を述べる。§7.2 は導来 prismatic コホモロジー（Construction 7.6）と、それが離散な場合の性質（Lemma 7.7、Ex 7.9、Prop 7.10）。§7.3 は prismatic site の被覆の持ち上げ（Prop 7.11）から André の補題（Thm 7.14）を出し、Thm 7.4 を証明する。本体は §7.1 と §7.3 の環の結果（Cor 7.3、Thm 7.4、Thm 7.14）を §7.2 を使わずに証明している。§7.2 のうち通常の環と prism だけで述べられる部分（離散な δ 構造、冪等分裂による始対象、lci 商の有界な prismatic envelope、qrsp の模型の始的な prism と完全化）は本体にあり、導来 prismatic コホモロジー $`\Delta_{R/A}` そのものとそれとの同一視は drafts にある。形式化の設計の決定は a2-design.md・a3-design.md にあり、原典との差として各項目の下に引く。

*7.1 semiperfectoid 環の perfectoid 化*

この小節（原典 §7.1「Universal prisms for semiperfectoid rings」）では、semiperfectoid 環 $`S` の絶対 prismatic site の始対象 $`\Delta^{\mathrm{init}}_S` を手で作り（Prop 7.2）、それを完全化して普遍な perfectoid 環 $`S_{\mathrm{perfd}}` を得る（Cor 7.3）。$`S\to S_{\mathrm{perfd}}` が全射であること（Thm 7.4）はこの節の主定理で、証明は 7.3 節で行う。証明の道具は三つ：完全 prism からの射の一意な持ち上げ（原典 Lemma 4.8、命題 4.1.8）、剛性（原典 Lemma 3.5、命題 3.2.1）、prism の完全化（原典 Lemma 3.9、命題 3.3.1）と perfectoid 環 ＝ 完全 prism（原典 Thm 3.10、定理 3.4.1）。番号「7.1.n」はこのノートの番号で、括弧内が原典の番号。原典 Not 7.1〜Rem 7.5 のうち Thm 7.4 を除く全項目を扱う（Thm 7.4 は 7.3 節）。

*7.2 導来 prismatic コホモロジー*

Quillen の非可換左導来関手（左 Kan 延長）の形式で、prismatic コホモロジーを全ての p 完備な（単体的）環に延ばす。HT 比較から $`\overline{\Delta}_{R/A}` は $`\wedge^iL_{R/(A/I)}` を次数商とする filtration を持つので、余接複体がよい環（lci 商、quasiregular semiperfectoid 環）では $`\Delta_{R/A}` が次数 0 に集中し、prismatic site の始対象と結びつく（Lemma 7.7・Ex 7.9・Prop 7.10）。

Lean の状況は二層に分かれる。$`\Delta_{R/A}` そのもの（∞ 圏の左 Kan 延長）は drafts にある。本体にあるのは $`\Delta_{R/A}` を使わずに述べられる古典的な部分で、通常の環・向き付き prism・prismatic site \`PrismOver P R κ\`（有界 prism の圏、濃度の上限 κ つき）で述べる：離散な場合の δ 構造と prism、冪等完備な圏の始対象、lci 商の prismatic envelope とその始性、qrsp の模型 $`T`・$`S'` の始的な prism とその完全化。

*7.3 André の補題と Thm 7.4*

この小節では、§7.2 の導来 prismatic コホモロジーを使って quasisyntomic 被覆を prismatic site へ持ち上げ（Prop 7.11）、その応用として André の平坦性補題（Thm 7.14）を新しく証明し、最後に §7.1 で述べた Thm 7.4（$`S\to S_{\mathrm{perfd}}` の全射性）を証明する。Ex 7.12・7.13 は Prop 7.11 を使って prismatic site の終対象の被覆を作る例、Rem 7.15 は André の補題の精密形（mod p で ind-syntomic に取れる）の概略である。

本体の André の補題は、外側の構成（一段の拡大を超限的に積む）は原典と同じだが、一段の拡大を Prop 7.11 ではなく、モニック多項式の根の prismatic envelope の直接計算（Rem 7.15 と同じ種類の pd 計算）で作る（D12）。Thm 7.4 は原典どおり André の補題から導く（D11）。

:::definition "bs_7_1"
*記法 7.1*　semiperfectoid。対応表の状態：なし。

qrsp の有界ねじれ・cotangent flatness を束ねた定義は drafts。本体の semiperfectoid quotient の展開仮定だけでは本項の qrsp 定義全体にならない。

*定義 7.1.1（原典 Not 7.1） — 主張*

環 $`S` が *semiperfectoid* であるとは、$`S` が導来 $`p` 完備で、ある perfectoid 環 $`R` の商 $`R\twoheadrightarrow S` として書けること。semiperfectoid 環 $`S` が *quasiregular*（以下 qrsp）であるとは、$`S` の $`p^\infty` ねじれが有界で、余接複体 $`L_{S/\mathbb Z_p}[-1]` が $`S` 上 $`p` 完全平坦であること（\[BMS19, §4.4\]）。このとき $`S` は古典的に $`p` 進完備である。

*定義 7.1.1（原典 Not 7.1） — Lean*

semiperfectoid は本体に名前つきの定義がなく、使う所（Cor 7.3・Thm 7.4 など）で「整 perfectoid 環 $`R`（\`IsIntegralPerfectoid\`）からの全射 $`q\colon R\to S`、$`S` は導来 $`p` 完備」と仮定を展開して書く（系 7.1.3 の Lean の囲み）。

qrsp は本体にない。drafts に原典どおりの定義 \`IsQuasiregularSemiperfectoid\`（drafts/A3/LciAndQuasiregular:277）がある。欄は導来 $`p` 完備性 \`pComplete\`、perfectoid 環からの全射 \`semiperfectoid\`、有界 $`p^\infty` ねじれ \`boundedTorsion\`（述語 \`BoundedPTorsion\`、同:60）、余接複体の条件 \`cotangent\_flat\`（述語 \`CotangentPCompletelyFlat\`、同:269。$`\widehat L_{S/\mathbb Z_p}[-1]` の導来 mod $`p` が次数 0 の平坦な $`S/p` 加群）。drafts の補助 \`padicBaseAlgebra\` には sorry が残る。

*定義 7.1.1（原典 Not 7.1） — 証明*

確かめることは最後の一文（補った）。導来 $`p` 完備な加群 $`M` について、$`M[p^\infty]=M[p^N]` と有界なら、導来 $`p` 完備化は古典的 $`p` 進完備化と一致する：$`\mathrm{R}\lim_n(M\otimes^L\mathbb Z/p^n)` の $`H^{-1}` 側の項 $`\lim_n M[p^n]` は、推移写像が $`p` 倍で $`N` 回合成すると $`M[p^N]` 上で零になるので Mittag-Leffler 零で、$`\lim` も $`\lim^1` も消える。よって $`M\simeq \lim_n M/p^n`。

注意（補った）：「$`p` 進完備で $`S/p` が semiperfect」だけでは semiperfectoid にならない。たとえば $`\mathbb Z_p` は $`p` 進完備で $`\mathbb Z_p/p=\mathbb F_p` は完全だが、perfectoid 環 $`R` から $`\mathbb Z_p` への環準同型はない（$`R\ne0` は $`p=u\varpi^p`、$`u` 単元となる $`\varpi` を持ち、像では $`v_p` が $`1=p\,v_p(\varpi)` となって矛盾）。逆に perfectoid 環 $`R` 上の代数 $`S` なら、$`p` 完備で $`S/p` が semiperfect のとき $`\theta\colon W(S^\flat)\to S` は全射で、その核は $`R` の $`\ker\theta_R` の生成元 $`\xi`（distinguished）の像を含むので、$`S` は perfectoid 環 $`W(S^\flat)/\xi` の商になる。

宣言：`IsQuasiregularSemiperfectoid`、`BoundedPTorsion`、`CotangentPCompletelyFlat`

:::

:::proposition "bs_7_2"
*命題 7.2*　普遍 prism の存在。対応表の状態：なし。

全 prism の圏の同じ Δinit\_S の始性は未同定。δ 除算とねじれ除去の完備化前の普遍性は構成の部品。

*命題 7.1.2（原典 Prop 7.2） — 主張*

$`S` を semiperfectoid 環とする。prism $`(A,I)` と写像 $`S\to A/I` の組の圏は始対象 $`(\Delta^{\mathrm{init}}_S,I)` を持ち、$`I=(d)` は単項である。

*命題 7.1.2（原典 Prop 7.2） — Lean*

本体にない（$`\Delta^{\mathrm{init}}_S` の超限構成も、一般の $`S` の始対象としての主張もない）。証明の最初の二段の代数的な部分（完備化の前の普遍性）だけが本体にある：

- δ 除算 $`B=A\{x_f\}/(dx_f-f)_\delta` の普遍性：\`existsUnique\_deltaAdjoinDivisionHom\`（Delta/Division/Basic:96）。指定した解 $`b_f` で $`f(d)b_f=f(a_f)` となる δ 射は一意に延長する。$`d` の像が非零因子なら解は一意なので解を指定しない版 \`existsUnique\_deltaAdjoinDivisionHom\_of\_regular\`（:201）。台は \`DeltaAdjoinDivision\`（:50）。

- $`d` 冪ねじれの δ 閉包による商 $`B/B[d^\infty]_\delta` の普遍性：\`existsUnique\_torsionReductionHom\`（:160）。$`B[d^\infty]` は $`B\to B[1/d]` の核として書く。

始的な prism そのものは、Prop 7.10 の模型 $`S'` の場合に、有界 prism の中での始対象として本体が直接作っている（\`exists\_rootRelationCompletedInitial\`、RootRelationCompletedInitial:33。7.2 節）。

*命題 7.1.2（原典 Prop 7.2） — 証明*

全射 $`R\to S`（$`R` perfectoid）を取る。Lemma 4.8 により、prism $`(A,I)` と $`R\to A/I` の組の圏の始対象は $`(A_{\inf}(R),\ker\theta)` で、$`\ker\theta=(d)` は単項。$`J\subset A_{\inf}(R)` を合成 $`A_{\inf}(R)\xrightarrow{\theta}R\to S` の核とする。

prism $`(C,K)` と $`S\to C/K` が与えられると、$`A_{\inf}(R)/d=R\to S\to C/K` を可換にする射 $`(A_{\inf}(R),(d))\to(C,K)` が一意に決まり、剛性（Lemma 3.5）で $`K=dC`。$`d` は $`C` の非零因子なので、各 $`f\in J` について $`f/d\in C` が一意に決まる。そこで
$$`B=A_{\inf}(R)\{x_f\mid f\in J\}/(dx_f-f\mid f\in J)_\delta`
とおくと、δ 環の射 $`B\to C` が一意に存在する（$`x_f\mapsto f/d`）。$`C` は $`d` ねじれなしなので、これは $`B/B[d^\infty]_\delta\to C` に一意に降りる（$`B[d^\infty]_\delta` は $`B[d^\infty]` を含む最小の δ 安定イデアル。$`B[d^\infty]` は $`C` で $`d` ねじれになるので零へ行き、核は δ 安定なので δ 閉包も零へ行く）。$`C` は導来 $`(p,d)` 完備な古典的な環なので、さらに $`B/B[d^\infty]_\delta` の導来 $`(p,d)` 完備化の $`H^0` へ一意に延びる。

この $`H^0` は新たに $`d` ねじれを持ちうるので、二つの操作（$`d` ねじれの δ 閉包での商、導来 $`(p,d)` 完備化の $`H^0`）を超限的に繰り返す。各段で $`C` への射は一意に延び、極限順序数では余極限を取る。段階 $`\omega_1` で止める（補った）：余極限 $`B_{\omega_1}=\mathrm{colim}_{\alpha<\omega_1}B_\alpha` の元 $`x` で $`d^nx=0` となるものは、ある段 $`B_\alpha` に代表を持ち、ある段 $`B_\beta` ですでに $`d^nx=0` なので $`B_{\beta+1}` で消える。よって $`d` は非零因子。導来 $`(p,d)` 完備性は $`\mathrm{RHom}(\mathbb Z[1/p],-)`・$`\mathrm{RHom}(\mathbb Z[1/d],-)` の消滅で判定され、$`\mathbb Z[1/p]` などは可算表示なので、この判定は $`\omega_1` フィルター余極限と可換（原典の「完備化は $`\omega_1` フィルター余極限と可換」）。完備化の段 $`B_{\alpha+1}` は共終なので $`B_{\omega_1}` は導来 $`(p,d)` 完備。こうして $`d` が非零因子の導来 $`(p,d)` 完備な δ-$`A_{\inf}(R)` 代数 $`\Delta^{\mathrm{init}}_S` を得て、一意な射 $`(\Delta^{\mathrm{init}}_S,(d))\to(C,K)` がある。

δ 射は distinguished 元を distinguished 元に送るので $`d` の像は distinguished で、$`(\Delta^{\mathrm{init}}_S,(d))` は prism。最後に $`R\cong A_{\inf}(R)/d\to\Delta^{\mathrm{init}}_S/d` は、$`J` の元がすべて $`\Delta^{\mathrm{init}}_S` で $`d` で割り切れる（$`f=dx_f`）ので商 $`S` を経由する。これが求める始対象。

原典は証明の後に注意する：$`\Delta^{\mathrm{init}}_S` は一般に性質がよくなく、たとえば有界とは限らない。完全化するとこの問題は消える（系 7.1.3）。

*命題 7.1.2（原典 Prop 7.2） — 原典との差（D10）*

Lean は全 prism の中の始対象 $`\Delta^{\mathrm{init}}_S` を作らず、Cor 7.3 に要る「完全 prism の中での始対象」を直接作る。評価は系 7.1.3 の囲み。

:::

:::corollary "bs_7_3" (lean := "SerrePositivity.BhattScholze.Semiperfectoid.exists_rootRelationPrismaticPerfection, SerrePositivity.BhattScholze.Semiperfectoid.exists_perfectoidization_of_perfectoid_surjective_quotient, SerrePositivity.BhattScholze.Semiperfectoid.exists_perfectoidization_of_semiperfectoid_quotient")
*系 7.3*　S\_perfd の存在（B3）。対応表の状態：一部（component）。

*主張*　semiperfectoid 環 $`S` からの射をもつ普遍 perfectoid 環は、始 prism $`\Delta_S^{\mathrm{init}}` の Frobenius 完全化を $`I` で割り、$`p` 進完備化して得られる。

任意の semiperfectoid quotient の同じ単位の普遍 perfectoid 化の存在を証明する。全 prism の Δinit\_S の p 完全化との一般の同一視は未供給。rootRelation の比較は特別な入力のみ。

*系 7.1.3（原典 Cor 7.3） — 主張*

$`S` を semiperfectoid 環とする。写像 $`S\to S_{\mathrm{perfd}}` を持つ普遍な perfectoid 環 $`S_{\mathrm{perfd}}` が存在する（$`S` から perfectoid 環への任意の写像は $`S_{\mathrm{perfd}}` を一意に経由する）。実際、$`S_{\mathrm{perfd}}` は $`(\Delta^{\mathrm{init}}_S)_{\mathrm{perf}}/I` の $`p` 進完備化である。

*系 7.1.3（原典 Cor 7.3） — Lean*

*普遍性の述語.* \`IsPerfectoidization\`（CommutativeAlgebra/Perfectoid/Defs:50）：$`f\colon S\to C` について、$`C` が整 perfectoid で、同じ宇宙の任意の整 perfectoid 環 $`T` への写像が一意に $`f` を経由する。

*第一文（存在と普遍性）.* 原典の仮定（導来 $`p` 完備）つきの入口 \`exists\_perfectoidization\_of\_semiperfectoid\_quotient\`（Perfectoidization:417）。$`S` の導来 $`p` 完備性を仮定しない、より一般の入口 \`exists\_perfectoidization\_of\_perfectoid\_surjective\_quotient\`（:385）。選んだ普遍環 \`QuotientPerfectoidization\`（:441）と単位 \`toQuotientPerfectoidization\`（:450）、普遍性 \`isPerfectoidization\_toQuotientPerfectoidization\`（:455）。

2. その導来 $`(p,d)` 完備化の $`H^0` 上の完全 prism \`perfectDeltaDivisionPrism\`（Perfectoidization:53。一般の形は \`perfectDeltaPDPrism\`、PrismPerfection:45）。$`d` が非零因子であることは完全 δ 環の distinguished 元についての Lemma 2.34(1)（\`IsPerfect.distinguished\_mul\_injective\`、DistinguishedRegular:96）。完全 prism への写像の一意な延長 \`existsUnique\_perfectDeltaDivisionPrismHom\`（Perfectoidization:102）。

3. 商への写像 \`perfectPrismQuotientPerfectoidizationMap\`（:212）が perfectoid 化であること \`perfectPrismQuotientPerfectoidizationMap\_isPerfectoidization\`（:234）。完全試験 prism への始性を Thm 3.10 で perfectoid 環の普遍性に読み替える。

\*\*第二文（式 $`S_{\mathrm{perfd}}=(\Delta^{\mathrm{init}}_S)_{\mathrm{perf}}/I`）.\*\* 始的な prism が与えられた場合の比較としてだけある。

1. prism の完全化：任意の prism $`Q` の δ 完全化の導来 $`(p,d)` 完備化 \`classicalPrismPerfection\`（ClassicalPrismPerfection:34）と、完全な標的への一意な延長 \`existsUnique\_classicalPrismPerfectionHom\`（:75）。$`Q` の完全性は仮定しない。

2. 始性の移行：剰余単位 $`v\colon T\to Q/I` が全ての有界 prism の中で始的（\`IsInitialPrismUnit\`、InitialPrismPerfection:28）なら、完全化の剰余単位は完全 prism の中で始的（\`classicalPrismPerfection\_initial\`、:46）。完全 prism の中での始性は環としての perfectoid 化を与える（\`isPerfectoidization\_of\_perfectInitial\`、:67。perfectoid な標的を有界な完全 prism の商で表す \`exists\_boundedPerfectPrismPresentation\`、PerfectoidPrismPresentation:47 と Lemma 4.8）。二つを合わせたものが \`classicalPrismPerfectionUnit\_isPerfectoidization\`（InitialPrismPerfection:94）。

3. 具体的な候補との比較：同じ perfectoid 化を与える二つの完全 prism の間には単位を保つ唯一の δ-prism 同型がある（\`existsUnique\_perfectPrismComparison\`、Cor73PrismComparison:30）。これを \`perfectDeltaDivisionPrism\` に当てたものが \`classicalPrismPerfection\_cor73\`（:75、主張の形は \`IsClassicalCor73Comparison\`、:63）、零環の商の枝は \`classicalPrismPerfection\_cor73\_of\_subsingleton\`（:93）。

*系 7.1.3（原典 Cor 7.3） — 証明*

原典の筋：perfectoid 環 $`S_{\mathrm{perfd}}` と写像 $`S\to S_{\mathrm{perfd}}` の組の圏は、完全 prism $`(A,I)` と写像 $`S\to A/I` の組の圏と同値（Thm 3.10：perfectoid 環 $`T` ↔ 完全 prism $`(A_{\inf}(T),\ker\theta)`、$`A/I` は perfectoid）。原典の文では「$`R\to A/I`」と書かれているが、$`S` を経由する写像と読む（補った）。後者の圏の始対象は、命題 7.1.2 の $`\Delta^{\mathrm{init}}_S` の完全化 $`(\Delta^{\mathrm{init}}_S,I)_{\mathrm{perf}}`：完全 prism への射は完全化を一意に経由する（Lemma 3.9）。Lemma 3.9 によりこの完全化は $`(\Delta^{\mathrm{init}}_S)_{\mathrm{perf}}` の古典的 $`(p,I)` 進完備化で、その $`I` での商は $`(\Delta^{\mathrm{init}}_S)_{\mathrm{perf}}/I` の $`p` 進完備化（補った：$`(\Delta^{\mathrm{init}}_S)_{\mathrm{perf}}/d` の $`p^\infty` ねじれは $`p` で消えるので、導来と古典的な $`p` 完備化が一致する）。

Lean の筋（補った）：$`\Delta^{\mathrm{init}}_S` を経由せず、完全 prism $`(C,(e))` と $`S\to C/e` について命題 7.1.2 の証明を繰り返す。$`A` から $`C` への δ 射は一意（Lemma 4.8）で $`J` を $`(e)` に送るので、δ 除算 $`B` から一意に延び、$`C` は $`p` 進完備で完全なので $`B` の $`p` 進完備な δ 完全化から一意に延びる。完全化した後では $`d` は Lemma 2.34(1) により非零因子なので、$`d` ねじれの除去は不要で、導来 $`(p,d)` 完備化を一回行えば完全 prism になり、超限帰納が要らない。こうして得た完全 prism が「完全 prism の中の始対象」で、その商が Thm 3.10 により $`S_{\mathrm{perfd}}`。

*系 7.1.3（原典 Cor 7.3） — 原典との差（D10）*

原典は全 prism の中の始対象 $`\Delta^{\mathrm{init}}_S`（命題 7.1.2、超限帰納）を作ってから完全化する。Lean はそれを経由せず、完全 prism の中の始対象を δ 除算・$`p` 進完備な δ 完全化・導来 $`(p,d)` 完備化の三段で直接作る。主張の第一文（存在と普遍性）は原典と同じ一般性で、導来 $`p` 完備性を仮定しない入口もある。第二文の式は、始的な prism が与えられた場合の比較としてだけ入っている。

:::

:::theorem "bs_7_4" (lean := "SerrePositivity.BhattScholze.Semiperfectoid.surjective_of_isPerfectoidization_of_semiperfectoid_quotient, SerrePositivity.BhattScholze.Semiperfectoid.surjective_of_isPerfectoidization_of_andre, SerrePositivity.BhattScholze.Semiperfectoid.exists_surjective_perfectoidization_of_semiperfectoid_quotient, SerrePositivity.BhattScholze.Semiperfectoid.surjective_of_isPerfectoidization_of_semiperfectoid_quotient_of_rootEnvelope")
*定理 7.4*　S → S\_perfd は全射（B4）。対応表の状態：本体にある。

*主張*　semiperfectoid 環 $`S` からその普遍 perfectoid 化 $`S_{\mathrm{perfd}}` への射は全射である。

同じ semiperfectoid quotient と任意の普遍 perfectoid 化の単位 f の全射性に一致。André の経路と root-envelope の別経路があり、E3 存在入力を要しない。

*定理 7.3.6（原典 Thm 7.4） — 主張*

semiperfectoid 環 $`S`（導来 p 完備で、ある perfectoid 環 $`R` の商として書ける環）について、射 $`S\to S_{\mathrm{perfd}}` は全射である。ここで $`S_{\mathrm{perfd}}` は $`S` からの射を持つ普遍的な perfectoid 環（Cor 7.3）。

*定理 7.3.6（原典 Thm 7.4） — Lean*

\`surjective\_of\_isPerfectoidization\_of\_semiperfectoid\_quotient\`（Surjectivity.lean:509）：perfectoid 環 $`R` の全射商 $`S` が導来 p 完備なら、$`S` の任意の perfectoid 化（普遍性で特徴づけた $`S\to C`）は全射。全射な perfectoid 化の存在（Cor 7.3 と合わせた形）は \`exists\_surjective\_perfectoidization\_of\_semiperfectoid\_quotient\`（:517）。証明は原典どおり André の補題経由で \`surjective\_of\_isPerfectoidization\_of\_andre\`（:460）。その中身：

1. 定理 7.3.4 で絶対整閉な perfectoid 環 $`T` へ p 完全忠実平坦に拡大し、\`surjective\_of\_isPerfectoidization\_of\_aicPerfectoidBaseChange\`（:432）で全射性を降下する。核の全元の両立する p 冪根は \`IsAbsolutelyIntegrallyClosed.exists\_compatible\_pow\_roots\`（Basic.lean:48）から。

2. 根を持つ拡大からの降下 \`surjective\_of\_isPerfectoidization\_of\_rootedPerfectoidBaseChange\`（Surjectivity.lean:401）：$`C\otimes_RT` の perfectoid 化（Witt 余積による構成 \`exists\_perfectoidizationTensorBaseChange\`、TensorPerfectoidization.lean:465）の上で全射性を示し、mod p のテンソル射の全射性に移して、p 完全忠実平坦な降下 \`surjective\_of\_isPerfectoidization\_of\_residue\_baseChange\`（Surjectivity.lean:141）を当てる。

3. 核の全元が根を持つ場合：\`surjective\_of\_isPerfectoidization\_of\_rootedKernel\`（:295）、\`surjective\_of\_isPerfectoidization\_of\_rootedIdeal\`（:263）。根の族の最初の元が生成するイデアルによる商の perfectoid 化は、全ての根で割った商の p 進完備化で、全射（\`surjective\_of\_isPerfectoidization\_of\_compatibleRootFamily\`、CompatibleRootPerfectoid.lean:493）。

André の補題を使わない別証明 \`surjective\_of\_isPerfectoidization\_of\_semiperfectoid\_quotient\_of\_rootEnvelope\`（PerfectPrism.lean:993、完全 prism 上の根の割り算包から降下する）も本体にある。主定理の経路では使わない。

*定理 7.3.6（原典 Thm 7.4） — 証明*

$`S=R/J`（$`R` perfectoid）と書く。

1. *単項への帰着.* 有向余極限により $`J` は有限生成としてよく、さらに帰納法で $`J=(f)` は単項としてよい（補った：$`R/(f_1)` の perfectoid 化が $`R` の商の perfectoid 環になれば、それを新しい $`R` として次の生成元へ進む）。

2. *André の補題で根を持たせる.* Thm 7.14 により、$`f` は $`R` の中に両立する p 冪根 $`f^{1/p^n}` を持つと仮定してよい。原典はこの帰着を一文で済ませる。補うと（補った）：絶対整閉な p 完全忠実平坦拡大 $`R\to R'` を取ると、$`S'=S\,\widehat{\otimes}_RR'=R'/f` の perfectoid 化は $`S_{\mathrm{perfd}}\,\widehat{\otimes}_RR'`（perfectoid 環の完備テンソル積は perfectoid で、普遍性が底変換と両立する）。$`S\to S_{\mathrm{perfd}}` の全射性は mod p で調べればよく（両辺が導来 p 完備なので導来 Nakayama）、mod p では $`R'/p` が $`R/p` 上忠実平坦なので $`S'\to S'_{\mathrm{perfd}}` の全射性から降りる。

3. *被約性.* perfectoid 環 $`T` は被約なので、任意の射 $`S=R/f\to T` で $`f^{1/p^n}` の像は $`p^n` 乗が 0 になり 0。従って $`S\to T` は $`R/(f^{1/p^\infty})` の p 完備化を通り、これ自身 perfectoid である。よって $`S_{\mathrm{perfd}}` は $`R/(f^{1/p^\infty})` の p 完備化で、特に $`R\to S\to S_{\mathrm{perfd}}` は全射。

*定理 7.3.6（原典 Thm 7.4） — 原典との差（D11）*

原典どおり André の補題（Thm 7.14）を経由する。ただし原典の「有向余極限で有限生成に、帰納法で単項に帰着」は使わない：$`R` を絶対整閉な $`T` へ拡大すると、底変換した核 $`JT` の全元が同時に両立する p 冪根を持つので、任意の元の族を一度に扱える。原典が一文で済ませる「根を持つと仮定してよい」の降下（perfectoid 化と底変換の両立、mod p での忠実平坦降下）は本体で明示的な定理になっている。

:::

:::proposition "bs_7_5"
*注意 7.5*　Zariski 閉集合。対応表の状態：なし。

Spa の Zariski closed と strongly Zariski closed の同定を未同定。環の全射性だけでは同じ adic 空間の比較を示さない。

*注意 7.1.4（原典 Rem 7.5：Zariski 閉集合は強 Zariski 閉） — 主張*

\[Sch15, §II.2\] は affinoid perfectoid 空間 $`X=\mathrm{Spa}(R,R^+)`（$`R` は perfectoid Tate 環で位相的冪零な単元 $`\varpi` を持ち、$`R^+\subset R^\circ` は開で整閉な部分環）の「Zariski 閉」と「強 Zariski 閉」な部分集合を定義した。強 Zariski 閉集合は perfectoid Tate 環への商 $`R\to R'` と一対一に対応し、Zariski 閉集合はあるイデアル $`I\subset R` の零点集合となる閉集合である。\[Sch15, Rem II.2.4\] では Zariski 閉集合が強 Zariski 閉とは限らないと主張したが、Thm 7.4 によりこれは誤りで、二つの概念は一致する。

*注意 7.1.4（原典 Rem 7.5：Zariski 閉集合は強 Zariski 閉） — 証明*

イデアル $`I\subset R` を取り、$`S` を $`R^+/(I\cap R^+)` の $`\varpi` 進完備化とする。$`S` は semiperfectoid（補った：$`R^+` は整 perfectoid で、$`\varpi` 進完備な $`R^+` からその商の完備化への写像は全射。$`p` は位相的冪零なので $`\varpi` 進完備なら $`p` 進完備）。Thm 7.4 により $`S\to S_{\mathrm{perfd}}` は全射なので、$`R'=S_{\mathrm{perfd}}[1/\varpi]` は $`R` の商である perfectoid Tate 環で、$`R` から perfectoid 環への写像で $`I` 上消えるものは一意に $`R'` を経由する（補った：そのような写像 $`R\to T` は $`R^+` を $`T` の整な perfectoid 部分環に送り、$`I\cap R^+` を消し、完備化 $`S` を経由し、Cor 7.3 の普遍性で $`S_{\mathrm{perfd}}` を経由する。$`\varpi` を逆にして $`R'` を経由する）。よって $`I` の零点集合はちょうど強 Zariski 閉集合 $`\mathrm{Spa}(R',R'^+)` で、$`R'^+\subset R'` は $`R^+` の像を含む最小の開で整閉な部分環。

:::

:::definition "bs_7_6"
*構成 7.6*　導来 prismatic コホモロジー。対応表の状態：なし。

同じ prismatic cohomology の left Kan extension・HT filtration・tensor/底変換/層条件の組み立ては drafts。本体の一般 Kan extension 基盤だけは本項の構成と未接続。

*定義 7.2.1（原典 Construction 7.6） — 主張*

有界 prism $`(A,I)` を固定する。p 完全 smooth な $`A/I` 代数 $`R` に対する関手 $`R\mapsto\Delta_{R/A}` を、$`\varphi_A` 半線形な自己準同型 $`\varphi` を持つ「$`D(A)` の $`(p,I)` 完備な対象の ∞ 圏」の可換代数に値を取るものと見て、全ての導来 p 完備な単体的可換 $`A/I` 代数へ左 Kan 延長したものを $`R\mapsto\Delta_{R/A}` と書き、*導来 prismatic コホモロジー*と呼ぶ。$`\Delta_{R/A}` は $`D(A)` の導来 $`(p,I)` 完備な可換代数で、自己準同型 $`\varphi:\Delta_{R/A}\to\varphi_{A,*}\Delta_{R/A}` を持つ。

HT 比較により、$`\overline{\Delta}_{R/A}:=\Delta_{R/A}\otimes^L_AA/I` は exhaustive な増大 $`\mathbb N` 添字の filtration を持ち、$`\mathrm{gr}_i` は $`\wedge^iL_{R/(A/I)}\{-i\}[-i]` の導来 p 完備化（$`\overline{\Delta}_{R/A}` の *HT 比較*）。帰結：

1. （smooth 代数での値）$`R` が p 完全 smooth なら $`\Delta_{R/A}` は元のものと一致する。

2. （étale 層）$`R\mapsto\Delta_{R/A}` は導来 p 完備な $`A/I` 代数の圏上の p 完全 étale 位相の層。特に p 進形式スキーム $`X` に対し $`\Delta_{X/A}` が $`D(X_{\mathrm{\acute et}},A)` の導来 $`(p,I)` 完備な対象の可換代数（Frobenius つき）として定まる。

3. （quasisyntomic 層）$`(A,I)` が完全なら、$`R\mapsto\Delta_{R/A}` は quasisyntomic な $`A/I` 代数の圏上の quasisyntomic 位相の層。

4. （底変換）有界 prism の射 $`(A,I)\to(B,J)` と、$`R\otimes^L_AB` の導来 p 完備化 $`R_B` に対し $`\Delta_{R_B/B}\simeq\Delta_{R/A}\widehat{\otimes}^L_AB`（右辺は導来 $`(p,J)` 完備化）。

5. （余極限）関手 $`\Delta_{-/A}`（p 完備な単体的可換 $`A/I` 代数 → $`D(A)` の $`(p,I)` 完備な $`E_\infty` 代数）は対称モノイダルで、実は全ての余極限と可換。

*定義 7.2.1（原典 Construction 7.6） — Lean*

本体にない。drafts：定義は \`derivedPrismaticCohomology\`（drafts/A2/DerivedPrismaticCohomology:226）、Frobenius \`derivedPrismaticFrobenius\`（:265）、離散な $`k` 代数での値 \`derivedPrismaticCohomologyDiscrete\`（:271）。HT filtration は \`hodgeTateFiltration\`（drafts/A2/HodgeTateFiltration:114）、次数商 \`hodgeTateFiltration\_gr\`（:240）、exhaustive 性 \`hodgeTateFiltration\_exhaustive\`（:250）。(1) は多項式代数での値 \`derivedPrismaticCohomology\_poly\`（DerivedPrismaticCohomology:240）。(4) は \`derivedPrismaticCohomology\_baseChange\`（drafts/A2/BaseChangeAndTensor:94）。(5) は sifted 余極限 \`derivedPrismaticCohomology\_siftedColimit\`（:122）、テンソル積 \`derivedPrismaticCohomology\_tensor\`（:147）、空の余積 \`derivedPrismaticCohomology\_initial\`（:165）。(2)(3) は drafts にもない。

*定義 7.2.1（原典 Construction 7.6） — 証明*

原典は帰結を「HT 比較から直ちに」とする。筋を補った（補った）。HT 比較の filtration は、smooth（Lean では多項式）代数の HT 比較（Thm 4.11。$`\overline{\Delta}` の共役 filtration で $`\mathrm{gr}_i=\Omega^i\{-i\}[-i]`）を左 Kan 延長したもの。安定 ∞ 圏で sifted 余極限は余ファイバー列を保つので filtration ごと延長でき、$`\Omega^i` の左 Kan 延長は $`\wedge^iL`（Illusie の導来外冪）である。

(1) 充満忠実な包含に沿う左 Kan 延長は元の関手を制限で復元する。(2)(3) $`\Delta` は導来 $`I` 完備なので、$`\overline{\Delta}` で確かめれば足りる（導来 Nakayama）。filtration は exhaustive なので次数商で確かめれば足り、$`\wedge^iL` の p 完全 étale 降下（(2)）、quasisyntomic 降下（(3)、BMS19 の $`\wedge^iL` の降下）に帰着する。(4) 多項式代数では smooth 代数の底変換（Cor 4.12）。両辺とも $`R` について sifted 余極限を保つ（完備底変換は左随伴の合成）ので一般に延びる。(5) sifted 余極限は構成から保たれる。有限余積（テンソル積）は多項式代数の Künneth に帰着し、それは HT 比較の次数商で $`\Omega^\bullet_{P\otimes P'}=\Omega^\bullet_P\otimes\Omega^\bullet_{P'}` から出る。

*定義 7.2.1（原典 Construction 7.6） — 原典との差（D31〜D35）*

(D31) 単体的可換 $`A/I` 代数の ∞ 圏を $`P_\Sigma(\mathrm{Poly}_{A/I})`（animated 環）として扱う。同じ ∞ 圏である。(D32) 原典の始域は導来 p 完備な単体的代数で、生成系は p 完備化した多項式代数。drafts の始域は $`P_\Sigma(\mathrm{Poly})` 全体、生成系は完備化しない多項式代数で、$`\Delta` の導来 p 完備化に対する不変性を定理にする（\`derivedPrismaticCohomology\_completion\_animated\`、BaseChangeAndTensor:176）。値は $`(p,I)` 完備なので同じものになる。(D33) $`\wedge^iL` の p 完備化を $`\widehat\Omega^i` の p 完備な $`D(k)` での Kan 延長として定義する（Mathlib に余接複体がない）。(D34) (1) は p 完全 smooth ではなく多項式代数で述べる。(2)(3) は述べない。(D35) 値は $`(p,I)` 完備な $`E_\infty` 代数（$`\mathrm{CAlg}_A` の対象）で、$`D(A)` 値の版は忘却で得る。

宣言：`derivedPrismaticCohomology`、`hodgeTateFiltration`、`derivedPrismaticCohomology_baseChange`、`derivedPrismaticCohomology_tensor`

:::

:::lemma_ "bs_7_7"
*補題 7.7*　離散な場合の導来 prismatic コホモロジー。対応表の状態：なし。

離散環への δ 延長・prism 構成と retract の一般論は本体だが、指定された Δ\_R/A の Frobenius と同定する比較が drafts。原文の同じ離散 Δ の部分を直接示す宣言ではない。

*命題 7.2.2（原典 Lemma 7.7） — 主張*

$`(A,I)` を有界 prism、$`R` を導来 p 完備な単体的 $`A/I` 代数で $`\overline{\Delta}_{R/A}` が次数 0 に集中するものとする。

1. $`\Delta_{R/A}` 上の $`\varphi_A` 線形な Frobenius $`\varphi_R` は、環 $`\Delta_{R/A}` 上の δ-$`A` 構造に自然に持ち上がる。

2. $`(\Delta_{R/A},I\Delta_{R/A})` は $`(A,I)` 上の prism で、写像 $`R\to\overline{\Delta}_{R/A}=\Delta_{R/A}/I\Delta_{R/A}` を持つ。

3. $`(A,I)` 上の prism $`(B,J)` と写像 $`R\to B/J` の組の圏は始対象を持ち、$`(\Delta_{R/A},I\Delta_{R/A})` は弱始対象。特に始対象は $`(\Delta_{R/A},I\Delta_{R/A})` のある冪等自己準同型の像。

原典は (3) について「$`(\Delta_{R/A},I\Delta_{R/A})` 自身が始対象である」と予想する。

*命題 7.2.2（原典 Lemma 7.7） — Lean*

本体は $`\Delta_{R/A}` を経ない環の段階だけ。(1)：p 正則な $`A` 代数 $`C` と、mod p で p 乗になり基底の Frobenius と両立する $`\varphi:C\to C` に対し、$`\varphi` を Frobenius とし基底射を δ 射にする δ 構造が一意に存在する（\`DeltaStructure.existsUnique\_over\_of\_frobeniusLift\`、DiscreteDelta:35）。既知の δ 環と Frobenius・基底射を保って同型な環へ δ 構造を一意に引き戻す版（envelope と同型な場合）が \`existsUnique\_over\_of\_equiv\`（:50）。

(2)：δ 環 $`C` と δ 射 $`\eta:A\to C` で、$`\eta(d)` が正則かつ $`C` が $`p`・$`\eta(d)` について導来完備なら向き付き prism（\`OrientedPrism.ofDiscreteDelta\`、DiscretePrism:36）、基底からの prism の射 \`toDiscreteDelta\`（:62）。$`C/\eta(d)` の p 冪ねじれが有界なら有界 prism（\`ofDiscreteDelta\_bounded\`、:48）。

$`\Delta_{R/A}` を使う型は drafts（drafts/A3/DiscreteCase）：離散性の仮定 \`IsDiscretePrismatic\`（:89）、(1) の p ねじれなしの場合 \`deltaStructure\_of\_discrete\_pTorsionFree\`（:141）と envelope と同型な場合 \`deltaStructure\_of\_envelopeIso\`（:155）、(2) \`discretePrism\`（:180）・\`discretePrismOver\`（:220）、(3) 評価脚 \`prismMapOfDiscrete\`（:265）とその自然性（:269）、p ねじれなしの標的への弱始性 \`discrete\_weaklyInitial\`（:280）、p ねじれなしの対象の充満部分圏での始対象 \`exists\_initial\_of\_discrete\`（:299）。drafts の (2) は有界性を別の仮定で受ける。

*命題 7.2.2（原典 Lemma 7.7） — 証明*

(1) Čech–Alexander 複体と標準単体分解から、導来 p 完備な $`A/I` 代数 $`R` に対し、prismatic コホモロジーを計算する単体的余単体的な導来 $`(p,I)` 完備 δ-$`A` 代数 $`F_A(R)` が関手的に得られる：$`\operatorname{colim}_{\Delta^{op}}\lim_\Delta F_A(R)\simeq\Delta_{R/A}`。$`F_A(R)` の δ 構造は $`A\to W_2(A)` の上にある $`F_A(R)\to W_2(F_A(R))` で、制限 $`W_2(F_A(R))\to F_A(R)` を分裂させる。colim lim を取ると $`E_\infty` 環の射 $`\Delta_{R/A}\to\operatorname{colim}\lim W_2(F_A(R))` が制限の切断として得られる。関手的な引き戻し四角形 $`W_2(B)=B\times_{\varphi,B\otimes^L_{\mathbb Z}\mathbb F_p}B`（$`F` と $`\varphi` の二辺）は単体的可換環（したがって $`E_\infty` 環）の四角形で、colim lim と交換するので、$`\Delta_{R/A}` の離散性から $`\operatorname{colim}\lim W_2(F_A(R))\simeq W_2(\Delta_{R/A})`。これが $`\varphi_R` を持ち上げる δ-$`A` 構造を与える。

(2) $`\Delta_{R/A}` の導来 $`(p,I)` 完備性と、$`\overline{\Delta}_{R/A}=\Delta_{R/A}\otimes^L_AA/I` が離散であること（$`I` 捩れがない）から。

(3) まず $`(R/A)_\Delta` の任意の対象 $`(B,J)` への関手的な射 $`(\Delta_{R/A},I\Delta_{R/A})\to(B,J)` を作る。p 完全 ind-smooth な $`A/I` 代数による分解 $`R_\bullet\to R` を取ると、Čech–Alexander 複体の理論（$`\Delta_{R_i/A}=\lim_{C\in(R_i/A)_\Delta}C`）から $`\Delta_{R/A}=\operatorname{colim}_{\Delta^{op}}\lim_{C\in(R_\bullet/A)_\Delta}C`。$`(B,J)` は全ての $`(R_i/A)_\Delta` の両立する対象を与えるので、極限をそこに制限して $`\Delta_{R/A}\to\operatorname{colim}_{\Delta^{op}}B=B`。(1) の議論でこれは δ 環の射。この関手的な弱始性に Lemma 7.8（命題 7.2.3）を当てる。

Lean の本体の (1) は、p 正則な環では δ 構造が Frobenius 持ち上げで決まること（命題 2.1.3 (2)）による。(3) の評価射が δ 射であることも、標的が p 正則なら Frobenius との可換性から出る（命題 2.1.5 (3)）。

*命題 7.2.2（原典 Lemma 7.7） — 原典との差（D36）*

原典の (1) は $`W_2` の引き戻し四角形と $`F_A(R)` から一般に δ 構造を作り、(3) の δ 射も任意の prism へ作る。Lean は (1) を p ねじれなしの場合と envelope と同型な場合だけ述べ、(3) の δ 射を p 正則（p ねじれなし）な標的に限る。全有界 prism の中での始性は、Ex 7.9・Prop 7.10 で envelope の普遍性から別に得る（例 7.2.4・命題 7.2.5）。

宣言：`SerrePositivity.BhattScholze.DeltaStructure.existsUnique_over_of_frobeniusLift`、`SerrePositivity.BhattScholze.DeltaStructure.existsUnique_over_of_equiv`、`SerrePositivity.BhattScholze.OrientedPrism.ofDiscreteDelta`、`SerrePositivity.BhattScholze.OrientedPrism.ofDiscreteDelta_bounded`、`SerrePositivity.BhattScholze.OrientedPrism.homOfFrobenius`、`SerrePositivity.BhattScholze.Prismatic.PrismOver.exists_initial_of_primeRegular_evaluation`、`SerrePositivity.BhattScholze.Prismatic.PrismOver.homOfFrobenius`

:::

:::lemma_ "bs_7_8" (lean := "CategoryTheory.initial_of_retraction_idempotent, CategoryTheory.initial_of_natural_legs, SerrePositivity.BhattScholze.Prismatic.PrismOver.exists_split_idempotent, SerrePositivity.BhattScholze.Prismatic.PrismOver.isIdempotentComplete")
*補題 7.8*　離散な場合の始対象。対応表の状態：本体にある。

*主張*　冪等完備圏 $`\mathcal C` の恒等関手が、対象 $`X` の下の圏からの忘却を通って $`F\colon\mathcal C\to\mathcal C_{X/}` により因数分解するとする。$`F(X)` が与える $`X` の自己射は冪等で、その像に当たるレトラクトが $`\mathcal C` の始対象になる。

原文どおりの冪等完備圏 C と忘却を分裂する F:C→Under X から、F(X) の冪等と対応する retract の始性を構成する。

*命題 7.2.3（原典 Lemma 7.8） — 主張*

$`\mathcal C` を冪等完備な圏、$`X\in\mathcal C` とし、$`\mathcal C_{X\backslash}` を $`X\to Y` を持つ対象 $`Y` の圏とする。$`\mathcal C` の恒等関手が射影 $`\mathcal C_{X\backslash}\to\mathcal C` を経由して関手 $`F:\mathcal C\to\mathcal C_{X\backslash}` に分解するとする。このとき $`F(X)` は $`X` の冪等自己準同型で、対応する $`X` のレトラクトは $`\mathcal C` の始対象。

*命題 7.2.3（原典 Lemma 7.8） — Lean*

原典の形が \`CategoryTheory.initial\_of\_retraction\_idempotent\`（InitialOfRetraction:53）。自然な脚の族 $`a_Y:X\to Y`（$`a_Y\circ f=a_Z`）で述べた形が \`initial\_of\_natural\_legs\`（:37）で、分裂の二つの射と $`r\circ s=a_X` も結論に含む。prismatic site への入力は冪等完備性：冪等な site の射 $`e` の不動点の部分環 $`\{x\mid e(x)=x\}` に prism の構造・完備性・有界性・剰余脚を降ろす（\`PrismOver.exists\_split\_idempotent\`、PrismRetract:42）、\`PrismOver.isIdempotentComplete\`（:127）。

*命題 7.2.3（原典 Lemma 7.8） — 証明*

$`F(X)=(X\xrightarrow{e}X)` とおく。$`\mathcal C` の射 $`e:X\to X` に $`F` を当てると $`\mathcal C_{X\backslash}` の射 $`(X\xrightarrow eX)\to(X\xrightarrow eX)` なので $`e\circ e=e`。分裂 $`X\xrightarrow{r}X'\xrightarrow{s}X`（$`r\circ s=\mathrm{id}`、$`s\circ r=e`）を取ると、$`F(X')=(X\to X')` は $`r` で、エピ射。$`F` は忠実なので $`\mathrm{Hom}_{\mathcal C}(X',Y)\hookrightarrow\mathrm{Hom}_{\mathcal C_{X\backslash}}(X\to X',X\to Y)` で、右辺は $`X\to X'` がエピなので高々一点。一方 $`X'\to X\to Y` で射は少なくとも一つある。

Lean の \`initial\_of\_natural\_legs\` の証明：冪等射 $`a_X` を $`a_X=s\circ r`、$`r\circ s=\mathrm{id}_{X'}` と分裂させる。自然性を $`r` に当てると $`a_{X'}=r\circ a_X=r\circ s\circ r=r`。$`Z` への射として $`a_Z\circ s` を取り、任意の $`f:X'\to Z` は自然性 $`f\circ a_{X'}=a_Z` から $`f\circ r=a_Z`、したがって $`f=f\circ r\circ s=a_Z\circ s`。

:::

:::proposition "bs_7_9"
*例 7.9*　lci 商の prismatic コホモロジー。対応表の状態：なし。

lci envelope の存在・始性と稠密分冪生成元の部品は本体。原文の指定 Δ\_R/A と包 B の比較がないため、Δ の離散性・始性として数えない。

*例 7.2.4（原典 Ex 7.9） — 主張*

有界 prism $`(A,I)` を固定し、$`R:=A/J`、$`J=(I,f_1,\dots,f_r)`、$`f_1,\dots,f_r` は $`A/I` 上 Koszul 正則な列とし、$`R` の p 冪ねじれは有界とする。このとき $`\Delta_{R/A}` は次数 0 に集中し $`I` 捩れがない（HT 比較による）ので $`(\Delta_{R/A},I\Delta_{R/A})` は $`(R/A)_\Delta` の対象で、これは始対象である。$`I=(d)` のときは $`\Delta_{R/A}\simeq A\{\tfrac{f_1}{d},\dots,\tfrac{f_r}{d}\}^\wedge`（prismatic envelope $`A\{\tfrac JI\}^\wedge`）。

*例 7.2.4（原典 Ex 7.9） — Lean*

- *有界な envelope の存在*：\`Prismatic.exists\_bounded\_lciRelationEnvelope\`（LciEnvelopeExistence:142）。仮定は $`\bar f_i\in A/d` の Koszul 複体の負次数ホモロジーの消滅（Koszul 正則）と、$`R=A/(d,f)` の p 冪ねじれの有界性。結論はイデアル $`(d)+(f)` の prismatic envelope（\`IsFiniteLciRelationEnvelope\`、:40。Prop 3.13 の envelope \`IsPrismaticEnvelope\`、Envelope:39 の特別な場合）で、有界な prism。envelope の普遍性は任意の有界 prism 上の対象について成り立つ。剰余 $`R\to B/dB` が p 完全忠実平坦であることまで含めた版が \`exists\_bounded\_lciRelationEnvelope\_faithful\`（LciEnvelopeFaithful:209）。

- *p 反転の議論の古典的な入力*：除算座標から余法加群 $`J/(J^2+I)` への一次の比較の全射性（\`lciRelationConormalLinearMap\_surjective\`、LciEnvelopeConormal:113。関係 $`f_i-dz_i` の Koszul 複体での余法類の同定 \`lciRelationConormalClass\_eq\`、:76）、分冪で生成される稠密な部分代数が像に入り連続な分裂があれば全射という判定（\`surjective\_of\_dense\_dividedPower\_generators\_retraction\`、LciEnvelopeInvertPGenerators:44。有限段の持ち上げによる版 \`surjective\_of\_dense\_filtration\_retraction\`、LciEnvelopeInvertP:98）。

$`\Delta_{R/A}` との同一視は drafts（drafts/A3/LciAndQuasiregular）：変数の envelope $`E` の $`U\to A` に沿う完備導来底変換 \`lciDerivedEnvelope\`（:118）、それと $`\Delta_{R/A}` の比較 \`lciDerivedEnvelope\_eq\_prismatic\`（:124）、離散性 \`lci\_isDiscretePrismatic\`（:130）、p 反転後の全射性 \`lci\_envelope\_surjective\_invert\_p\_universal\`（:220）、結論 \`prismaticCohomology\_lci\_eq\_envelope\`（:237。任意の有界な $`P_0` と d を保つ分類射を明示引数に取る）。普遍向き付き prism への特殊化が \`prismaticCohomology\_lci\_universal\`（drafts/A1/DeRhamComparisonPoly:505）。

*例 7.2.4（原典 Ex 7.9） — 証明*

始対象であることは $`\mathrm{Spf}(A)` 上局所的に確かめられるので $`I=(d)` とする。$`f_i/d` を自由に添加した導来 $`(p,I)` 完備な単体的可換 δ-$`A` 代数 $`B=A\{\tfrac{f_1}d,\dots,\tfrac{f_r}d\}^\wedge` を考える。$`\overline{\Delta}_{R/A}` で $`f_i=0` なので自然な射 $`B\to\Delta_{R/A}` がある。これが同型なら、$`B` は離散で $`(B,IB)` は $`(R/A)_\Delta` の対象になり、$`B` の普遍性から $`(B,IB)` は始対象、したがって $`(\Delta_{R/A},I\Delta_{R/A})` も始対象。

同型であること：両辺とも任意の底変換と可換（Construction 7.6 (4)）なので、普遍の場合 $`A=\mathbb Z_p\{d,f_1,\dots,f_r\}[\delta(d)^{-1}]^\wedge` で示せばよく、そこでは $`A/I` も $`R` も p ねじれなし。$`(A_0,I_0)=(\mathbb Z_p\{d\}[\delta(d)^{-1}]^\wedge,(d))` とおくと $`f_1,\dots,f_r` は $`A/I` で $`A_0/I_0` 上 p 完全正則なので、Prop 3.13 の envelope の構成から $`B` は envelope $`A\{\tfrac JI\}^\wedge` と一致し、次数 0 に集中して $`(B,IB)` は $`(R/A)_\Delta` の始対象。Lemma 7.7 から $`B\to\Delta_{R/A}` はレトラクションを持ち、$`B/IB\to\overline{\Delta}_{R/A}` もレトラクションを持つ。$`R` が p ねじれなしなので $`\overline{\Delta}_{R/A}` も p ねじれなしで、余核も p ねじれなし。よって $`B/IB[1/p]\to\overline{\Delta}_{R/A}[1/p]` の全射性を示せばよい。HT 比較から $`\overline{\Delta}_{R/A}[1/p]` は Banach $`R[1/p]` 代数として $`\mathrm{gr}_1=L^\wedge_{R/(A/I)}\{-1\}[-1]=J/(J^2+I)\{-1\}` で生成されるので、$`B=A\{\tfrac JI\}\to\Delta_{R/A}` が $`\tfrac JI` を $`\mathrm{gr}_1` へ全射に写すことを見ればよい。原典はこれを「$`R` の $`A/I` 上の自由分解による標準的な計算」とし、結晶コホモロジーでの変種 \[Bha12, Claim 3.30\] を引く。

その計算の要点（補った）：関係 $`f_i-dz_i` の Koszul 複体では、標準生成元 $`\tilde t_i` の微分が $`f_i-dz_i` で、その d 剰余の余法類は $`\bar f_i\bmod J^2`。したがって除算座標 $`z_i=f_i/d` は $`\mathrm{gr}_1` の基底 $`\bar f_i\{-1\}` に写り、一次の比較は全射。$`\mathrm{gr}_i` は $`J/J^2` の分冪 $`\Gamma^i` なので、p を反転すると像は $`\mathrm{gr}_1` の元の分冪で生成される稠密な部分代数を含む。レトラクションがあるので像は閉じており、全射が出る。

Lean の本体の envelope の存在（D76）：普遍向き付き prism 上の完備自由 δ 環とその変数の envelope を分類射で特殊化し、完備通常テンソル積で生成元が正則で剰余の p ねじれが有界であること（\`exists\_lciRelation\_regular\_completedTensor\`、LciEnvelopeDiscrete:65）を、有界な関係商への完備平坦底変換の純性（\`completedBaseChange\_bounded\_torsion\_pure\`、CompletedFlatBoundedTorsion:22）で示す。site の始性は envelope の普遍性で、イデアルを送る条件を剰余脚の条件に言い換えて得る。

*例 7.2.4（原典 Ex 7.9） — 原典との差（D40・D76）*

(D40) 原典の $`B\to\Delta_{R/A}` は単体的可換 δ 代数の射（導来 δ 構造）。drafts は先に $`\Delta_{R/A}` の離散性を HT 比較で示し、δ 環にしてから envelope の普遍性で $`B\to\Delta_{R/A}` を作る。同じ写像で、導来 δ 環を避ける。(D76) envelope の存在には原典どおり $`R` の p 冪ねじれの有界性を仮定する。原典は envelope $`B` の離散性を $`\Delta_{R/A}` との同一視から得るが、本体は $`\Delta_{R/A}` を経ずに、普遍の場合からの完備平坦底変換で古典的な envelope の存在と有界性を直接示す。

宣言：`SerrePositivity.BhattScholze.Semiperfectoid.exists_bounded_lciRelationEnvelope`、`SerrePositivity.BhattScholze.Semiperfectoid.IsFiniteLciRelationEnvelope`、`SerrePositivity.BhattScholze.Prismatic.IsPrismaticEnvelope.exists_initial_of_base_quotient`、`SerrePositivity.BhattScholze.Semiperfectoid.exists_lciRelation_regular_completedTensor`、`SerrePositivity.BhattScholze.Semiperfectoid.lciRelationConormalLinearMap_surjective`、`SerrePositivity.BhattScholze.Semiperfectoid.surjective_of_dense_dividedPower_generators_retraction`、`SerrePositivity.BhattScholze.Semiperfectoid.exists_bounded_lciRelationEnvelope_faithful`

:::

:::proposition "bs_7_10"
*命題 7.10*　qrsp の計算。対応表の状態：なし。

rootRelation の有界 Ainf-envelope と完全化の比較・始性は本体にあるが、同じ derived Δ\_S/A の離散性・初期 prism・全入力での忠実平坦性との同定は drafts。

*命題 7.2.5（原典 Prop 7.10） — 主張*

$`S` を quasiregular semiperfectoid 環、$`R` を $`R\to S` を持つ任意の perfectoid 環、$`(A,I)=(A_{\inf}(R),\ker\theta)` とする。このとき $`\overline{\Delta}_{S/A}` は離散で、$`\Delta_{S/A}` は $`S\to\Delta^{\mathrm{init}}_S/I` を持つ始 prism $`\Delta^{\mathrm{init}}_S` である。特に $`\Delta_{S/A}=\Delta^{\mathrm{init}}_S` は $`R` によらない。さらに $`S\to\overline{\Delta}_{S/A}` は p 完全忠実平坦。以後、quasiregular semiperfectoid な $`S` に対し $`\Delta_S=\Delta^{\mathrm{init}}_S=\Delta_{S/A}` と書く。

*命題 7.2.5（原典 Prop 7.10） — Lean*

- \*\*固定した $`A_{\inf}`\*\*：perfectoid 環 $`R` に対し、Witt 環 $`W(R^\flat)` 上の有界な完全 prism と、θ と両立する剰余の同型 $`A_{\inf}/I\cong R`（\`exists\_ainfClassicalPrism\`、AinfClassical:105）。p が単元の枝（$`R=0`）も含む。

- \*\*任意添字の $`S'`\*\*（\`exists\_rootRelationCompletedInitial\`、RootRelationCompletedInitial:33）。本体の $`S'` は $`R\langle X_j^{1/p^\infty}\mid j\in J\rangle/(X_j\mid j\in J)` の p 完備化、すなわち原典の $`S'` で全ての $`f_j` を 0 とした環（初期の根 $`X_j` だけを殺し、p 冪根は殺さない）。固定した $`A_{\inf}` 上の有界な envelope、$`S'` からの剰余単位、全ての有界 prism への一意な射を返す。有限部分族の envelope の図式（\`exists\_finiteEnvelopeDiagram\`、FiniteEnvelopeDiagram:235）、生の余極限の剰余の p 冪ねじれの一様な上界（\`finiteEnvelopeRawColimit\_residue\_uniform\_torsion\_bound\`、FiniteEnvelopeRawColimit:82）、その $`(p,d)` 完備化が全関係の有界な envelope であること（\`exists\_boundedFiniteEnvelopeCompletion\`、FiniteEnvelopeCompletion:97）から組み立てる。通常の商から $`S'` への標準射の全射性は \`rootRelationCompletedQuotientMap\_surjective\`（RootRelationCompletedSurjective:92）。

- \*\*$`S'` の完全化と Cor 7.3\*\*（\`exists\_rootRelationPrismaticPerfection\`、RootRelationPerfection:52）。上の始的な prism の完全化の商が $`S'` の perfectoid 化で、Cor 7.3 の具体的な候補と $`S'` の単位を保つ唯一の δ-prism 同型を持つ。根付き基底が零環の枝も同じ結論を出す。部品は、全有界 prism への始性から完全 prism への始性を得る \`classicalPrismPerfection\_initial\`（InitialPrismPerfection:46）、完全な始的 prism の剰余が perfectoid 化であること \`isPerfectoidization\_of\_perfectInitial\`（:67）・\`classicalPrismPerfectionUnit\_isPerfectoidization\`（:94）、同じ perfectoid 化を与える完全 prism の唯一の同型 \`existsUnique\_perfectPrismComparison\`（Cor73PrismComparison:30）、Cor 7.3 の候補との比較 \`classicalPrismPerfection\_cor73\`（:75）とその零環の枝 \`classicalPrismPerfection\_cor73\_of\_subsingleton\`（:93）。

本体にないもの：一般の qrsp 環 $`S` とその $`S'` への帰着、本体の $`S'` について $`S'\to\overline{\Delta}_{S'}` の p 完全忠実平坦性（有限の $`T` では入っている）、始的な prism を $`\Delta_{S/A}` と同一視すること。これらは drafts（drafts/A3/LciAndQuasiregular）：qrsp の定義 \`IsQuasiregularSemiperfectoid\`（:277。完備・perfectoid 環からの全射・有界 p 冪ねじれ・余接複体の平坦性の四条件）、離散性 \`qrsp\_isDiscretePrismatic\`（:334）、平坦性 \`qrsp\_completelyFaithfullyFlat\`（:347）、$`T` の場合 \`regularSemiperfectoid\_prismatic\`（:396。$`\Delta_{T/A}\simeq\Delta_{T/A'}` は \`perfectBaseComparison\_isIso\`、drafts/A2/BaseChangeAndTensor:108）、一般の始性 \`qrsp\_initial\`（:418）、$`S'` の始性 \`rootQuotient\_initial\`（:458）、完全化の比較 \`rootQuotient\_prismatic\_perfection\_eq\`（:465）。

*命題 7.2.5（原典 Prop 7.10） — 証明*

$`S` が quasiregular なら $`L_{S/R}[-1]` は p 完全平坦で、全ての $`\wedge^iL_{S/R}[-i]` の導来 p 完備化は p 完全平坦な $`S` 加群、特に離散。HT 比較から $`\overline{\Delta}_{S/A}` は離散で $`S` 上 p 完全忠実平坦（$`\mathrm{gr}_0=S` で、各次数商が平坦）。残るのは $`\Delta_{S/A}` が始対象であること、すなわち Lemma 7.7 (3) の冪等自己準同型が恒等であること。

$`R` を $`R\langle Y_i^{1/p^\infty}\mid i\in I\rangle` に替えても余接複体は変わらず、したがって $`\Delta_{S/R}` も変わらないので、$`R\to S` は全射としてよい。核の生成系 $`\{f_j\}_{j\in J}` を取ると
$$`S'=R\langle X_j^{1/p^\infty}\mid j\in J\rangle/(X_j-f_j\mid j\in J)^\wedge\to S,\qquad X_j\mapsto0`
は全射で、余接複体にも全射を誘導する。HT 比較から $`\Delta_{S'/R}\to\Delta_{S/R}` は全射なので、$`\Delta_{S'/A}` の冪等自己準同型が恒等であることを示せば足りる。$`J` を有限部分集合で切ると、$`S'` は正則 semiperfectoid 環
$$`T=R\langle X_1^{1/p^\infty},\dots,X_r^{1/p^\infty}\rangle/(X_1-f_1,\dots,X_r-f_r)`
の filtered 余極限なので、各 $`T` で示せばよい。$`A'=A_{\inf}(R\langle X_1^{1/p^\infty},\dots,X_r^{1/p^\infty}\rangle)` とすると、冪等自己準同型と両立して $`\Delta_{T/A}\simeq\Delta_{T/A'}`。$`A'/I` で $`X_i-f_i` は Koszul 正則なので、Ex 7.9 から $`\Delta_{T/A'}` の冪等自己準同型は恒等。

Lean の本体の $`T` では、$`A'` 上の lci の envelope（例 7.2.4）が始的な prism を直接与え、$`A'` が完全なので任意の有界 prism への $`A'` からの射は Lemma 4.8 で一意に持ち上がる。したがって始性は $`A` と $`A'` のどちらの上で測っても同じ（原典の $`\Delta_{T/A}\simeq\Delta_{T/A'}` に当たる）。$`S'` では、有限部分族の envelope の余極限の剰余の p 冪ねじれが全段で共通の指数 1 で消えることを使い、生の余極限を $`(p,d)` 完備化しても有界な envelope のままであることを示す。完全化については、始的な prism の完全化は完全な試験 prism の中で始的（Lemma 3.9 の形）、その剰余は perfectoid 化（Thm 3.10）なので、Cor 7.3 の候補と単位を保って一意に同型。

*命題 7.2.5（原典 Prop 7.10） — 原典との差（D10・D37・D39）*

(D39) quasiregular semiperfectoid の定義は、BMS19 の quasisyntomic の理論を経ずに、余接複体（左 Kan 延長、基底 $`\mathbb Z_p`）で直接述べる。条件は原典のまま（有界 p 冪ねじれを含む）で、理論の範囲を絞るだけ。(D37・D10) 全 prism の中の始 prism $`\Delta^{\mathrm{init}}_S` の一般構成（Prop 7.2 の超限構成）は持たない。本体は qrsp の模型 $`T`（有限）と $`S'`（$`f_j=0` の場合）について全有界 prism の中の始的な prism を envelope として直接作り、その完全化が Cor 7.3 の対象（完全な試験 prism の中の始対象）と単位を保って一意に同型であることを示す。

宣言：`SerrePositivity.BhattScholze.Semiperfectoid.exists_rootRelationAinfEnvelope`、`SerrePositivity.BhattScholze.Semiperfectoid.exists_rootRelationCompletedInitial`、`SerrePositivity.BhattScholze.Semiperfectoid.exists_rootRelationPrismaticPerfection`、`SerrePositivity.BhattScholze.Semiperfectoid.exists_ainfClassicalPrism`、`SerrePositivity.BhattScholze.Semiperfectoid.existsUnique_perfectEnvelopeHom`、`SerrePositivity.BhattScholze.Semiperfectoid.existsUnique_perfectPrismComparison`、`SerrePositivity.BhattScholze.Semiperfectoid.classicalPrismPerfection_cor73`、`SerrePositivity.BhattScholze.Semiperfectoid.classicalPrismPerfection_initial`、`SerrePositivity.BhattScholze.Semiperfectoid.rootRelationCompletedQuotientMap_surjective`

:::

:::proposition "bs_7_11"
*命題 7.11*　quasisyntomic 被覆の prismatic site への持ち上げ。対応表の状態：なし。

任意の quasisyntomic R に対する prismatic site の指定被覆とその perfection の flatness を未同定。

*命題 7.3.1（原典 Prop 7.11） — 主張*

$`(A,I)` を有界 prism、$`R` を quasisyntomic な $`A/I` 代数とする。このとき $`(R/A)_{\Delta}` の対象 $`(B\to B/IB\leftarrow R)` で、$`R\to B/IB` が p 完全忠実平坦となるものが存在する。従って：

1. $`(A,I)\to(B,IB)` は prism の平坦射である（$`A/I\to R` が p 完全忠実平坦なら忠実平坦）。

2. $`A` が完全なら、$`(A,I)\to(B,IB)_{\mathrm{perf}}` も平坦である（$`A/I\to R` が p 完全忠実平坦なら忠実平坦）。

*命題 7.3.1（原典 Prop 7.11） — Lean*

本体にない。drafts にもない。本体の André の補題（定理 7.3.4）は Prop 7.11 を使わない。

*命題 7.3.1（原典 Prop 7.11） — 証明*

*(i) 相対 semiperfect な被覆に取り替える.* 全射 $`A/I\langle x_j\mid j\in J\rangle\to R` を選び、$`x_j` の p 冪根を形式的に添加した p 完備な $`R` 代数
$$`S:=A/I\langle x_j^{1/p^\infty}\mid j\in J\rangle\ \widehat{\otimes}^{L}_{A/I\langle x_j\mid j\in J\rangle}\ R`
を取る。$`A/I\langle x_j\rangle\to A/I\langle x_j^{1/p^\infty}\rangle` は p 完全自由で、mod p の余接複体は $`\Omega^1_{\mathbb F_p[x_j]}` を次数 $`-1` に置いたもの（$`\mathbb F_p[x_j^{1/p^\infty}]` は完全なので $`L_{\mathbb F_p[x_j^{1/p^\infty}]/\mathbb F_p}=0`）だから quasisyntomic な被覆である（補った）。その底変換として $`R\to S` も quasisyntomic な被覆で、$`S` も $`A/I` 上 quasisyntomic。さらに $`S/p` は $`A/(I,p)` 上相対 semiperfect（相対 Frobenius が全単射な平坦代数の商）なので $`\Omega^1_{S/(A/I)}/p=0` となり、$`L^\wedge_{S/(A/I)}[-1]` は p 完全平坦な $`S` 加群である。

\*\*(ii) $`B=\Delta_{S/A}`.\*\* Prop 7.10 の前半の議論がそのまま使える：導来 Hodge–Tate 比較（Construction 7.6）により $`\overline{\Delta}_{S/A}` は増大で網羅的な filtration を持ち、その次数つき片は $`\wedge^i L_{S/(A/I)}[-i]` の p 完全化、すなわち $`L_{S/(A/I)}[-1]` の $`i` 次分冪で、p 完全平坦な $`S` 加群（次数 0 に集中）。従って $`\Delta_{S/A}` は離散で $`(p,I)` 完全平坦、$`\mathrm{gr}_0=S` から $`S\to\overline{\Delta}_{S/A}=B/IB` は p 完全忠実平坦。δ 構造は Lemma 7.7 で入り、$`(B,IB)` は prism になる。

*(iii) 帰結.* (1)：合成 $`A/I\to R\to S\to B/IB` の各射が p 完全平坦（$`A/I\to R` が p 完全忠実平坦ならすべて忠実平坦）なので、$`A\to B` は $`(p,I)` 完全（忠実）平坦。(2)：$`A` が完全なら $`\varphi_A` は同型なので、$`A\to\varphi^n_*B` は $`A\to B` を $`\varphi_A^n` で底変換したものと同一視でき平坦。$`(B,IB)_{\mathrm{perf}}` はその有向余極限の $`(p,I)` 完備化なので、平坦性（忠実平坦性）が保たれる（補った）。

:::

:::proposition "bs_7_12"
*例 7.12*　quasisyntomic 被覆の例。対応表の状態：なし。

相対 perfectoid を使う同じ site の終対象の被覆性を未同定。André の別の PD 経路は本項の証明ではない。

*例 7.3.2（原典 Ex 7.12） — 主張*

$`(A,I)` を有界 prism、$`R` を p 完全に滑らかな $`A/I` 代数、$`R\to R_\infty` を quasisyntomic な被覆で $`R_\infty` が $`A/I` 上形式的に p 完全エタール（$`L_{R_\infty/(A/I)}` が導来 p 完備化で消える）なものとする。このとき $`B:=\Delta_{R_\infty/A}` は $`(p,I)` 完全平坦で相対完全な δ-$`A` 代数で、自然な射が $`R_\infty\simeq\overline{\Delta}_{R_\infty/A}=B/IB` を与える。特に $`(B,IB)` は $`(R/A)_{\Delta}` の対象を与え、この対象は終対象を被覆する。

このような被覆の例（原典の脚注 12）：$`(A,I)` が完全な結晶的 prism なら $`R_\infty=R` の完全化。一般に、エタール座標 $`x_1,\dots,x_n\in R` を選べば $`R_\infty=R[y_1^{1/p^\infty},\dots,y_n^{1/p^\infty}]^\wedge_p/(y_1-x_1,\dots,y_n-x_n)`（$`x_i` の p 冪根を自由に添加した導来 p 完備な $`R` 代数）。

*例 7.3.2（原典 Ex 7.12） — 証明*

$`B` の性質は導来 Hodge–Tate 比較から：$`L_{R_\infty/(A/I)}` の完備化が 0 なので $`\overline{\Delta}_{R_\infty/A}\simeq R_\infty`。被覆であることを示すには、試験対象 $`(C\to C/IC\leftarrow R)\in(R/A)_{\Delta}` に対し、$`(p,I)` 完全忠実平坦な被覆 $`(C,IC)\to(D,ID)` と $`(R/A)_{\Delta}` の射 $`(B,IB)\to(D,ID)` を見つければよい。

1. $`R\to R_\infty` の底変換 $`C/IC\to C/IC\,\widehat{\otimes}^L_R\,R_\infty` は quasisyntomic な被覆なので、Prop 7.11 から忠実平坦な prism の射 $`(C,IC)\to(D,ID)` と分解 $`C/IC\to C/IC\,\widehat{\otimes}^L_R\,R_\infty\to D/ID` が得られる。

2. 特に $`A/I\to D/ID` は p 完全エタールな $`A/I` 代数 $`R_\infty` を通る。変形理論により、$`B/IB\simeq R_\infty\to D/ID` を持ち上げる δ-$`A` 代数の射 $`B\to D` がただ一つある。

3. 合成 $`R\to R_\infty\to D/ID`（$`R\to C/IC\to D/ID` に等しい）で $`(R\to D/ID\leftarrow D)\in(R/A)_{\Delta}` となり、$`C/IC\to D/ID` が $`R` 代数の射であることは図式の追跡で確かめられる。

:::

:::proposition "bs_7_13"
*例 7.13*　正則環の絶対 prismatic site の終対象の被覆。対応表の状態：なし。

絶対 site の終対象を prism perfection が覆うという同じ主張を未同定。

*例 7.3.3（原典 Ex 7.13） — 主張*

$`(A,I)` を有界 prism で $`\varphi\colon A\to A` が $`(p,I)` 完全平坦なものとし、$`(B,IB)` をその完全化（Lemma 3.9）とする。このとき $`B/IB` は perfectoid 環で、$`(B,IB)` は絶対 prismatic site $`(A/I)_{\Delta}`（Remark 4.7）の対象を与え、この対象は終対象を被覆する。このような $`(A,I)` の自然な例は、$`A/I` が正則環である任意の prism である。

*例 7.3.3（原典 Ex 7.13） — 証明*

原典は「Ex 7.12 と同様の議論」とだけ書く。筋を補うと次のとおり（補った）。試験対象 $`(C,J)` と $`A/I\to C/J` に対し、$`A/I\to B/IB` の底変換 $`C/J\to C/J\,\widehat{\otimes}^L_{A/I}\,B/IB` を考える。$`\varphi_A` は $`(p,I)` 完全平坦で、mod p では Frobenius なので Spec 上全単射だから完全忠実平坦。従って $`A\to B=\bigl(\operatorname{colim}_\varphi A\bigr)^\wedge` は $`(p,I)` 完全忠実平坦で、$`A/I\to B/IB` は p 完全忠実平坦。これが quasisyntomic でもあることを確かめれば（原典は触れない）、底変換は quasisyntomic な被覆になる。そこで Prop 7.11 を基底 $`(C,J)` で使うと忠実平坦な被覆 $`(C,J)\to(D,JD)` と $`B/IB\to D/JD` が得られる。$`(B,IB)` は完全なので、Ex 7.12 の変形理論の代わりに Lemma 4.8 の型の剛性（完全 prism からの射は商の上の射で一意に決まる）で $`B/IB\to D/JD` が prism の射 $`(B,IB)\to(D,JD)` に持ち上がる。最後の主張（$`A/I` 正則なら $`\varphi_A` が完全平坦）の理由は原典に書かれていない。

:::

:::theorem "bs_7_14" (lean := "SerrePositivity.BhattScholze.Inputs.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed, SerrePositivity.BhattScholze.Andre.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed, SerrePositivity.IsAbsolutelyIntegrallyClosed.exists_compatible_pow_roots")
*定理 7.14*　André の補題。対応表の状態：一部（component）。

*主張*　任意の perfectoid 環 $`R` には $`p` 完全忠実平坦な perfectoid 拡大 $`S` があり、$`S` 上の任意のモニック多項式が $`S` に根をもつ。特に任意の元に整合する $`p` 冪根の系を選べる。

第一文の p 完全忠実平坦な絶対整閉 perfectoid 拡大と両立する p 冪根は証明済み。末尾の mod p ind-syntomic に選べるという精密化は含まない。

*定理 7.3.4（原典 Thm 7.14） — 主張*

（André の平坦性補題）$`R` を perfectoid 環とする。このとき perfectoid 環の p 完全忠実平坦な射 $`R\to S` で、$`S` が絶対整閉（任意のモニック多項式が解を持つ）となるものが存在する。特に $`S` の任意の元は両立する p 冪根の系を持つ。

実は $`R\to S` は mod p で ind-syntomic に取ることもできる（注意 7.3.5）。

*定理 7.3.4（原典 Thm 7.14） — Lean*

第一文：\`Andre.exists\_completelyFaithfullyFlat\_absolutelyIntegrallyClosed\`（Tower.lean:1509）。仮定は $`R` の（整）perfectoid 性だけで、$`S` は $`R` と同じ宇宙に取る。主経路で使う入口 \`Inputs.exists\_completelyFaithfullyFlat\_absolutelyIntegrallyClosed\`（AndreFlatness.lean:58）はこれをそのまま返す（名前空間は Inputs だが証明済み）。絶対整閉の定義 \`IsAbsolutelyIntegrallyClosed\`（Basic.lean:41）は「正次数のモニック多項式が根を持つ」で、原典の「任意のモニック多項式」は正次数の意味に読む。第二文：\`IsAbsolutelyIntegrallyClosed.exists\_compatible\_pow\_roots\`（:48、p に限らず任意の $`n>0` 乗根の両立系）。

1. *完全 prism の商の上の一段.* \`exists\_monicRootPerfectoidExtension\_of\_perfectPrism\`（PerfectPrismMonic.lean:1156。有限族の版 \`exists\_finiteMonicRootedPerfectoidExtension\_of\_perfectPrism\`、同:1112）。候補は、モニック多項式を $`A` へ持ち上げ、階数 1 の変数 $`Y` の多項式 δ 環で関係式 $`f(Y)` を $`d` で δ 除算し、完全化して $`d` で割った環 \`PolynomialPerfectoidCandidate\`（MonicCandidate.lean:238）。その p 完全忠実平坦性 \`perfectPrismMonicPerfectoidBaseMap\_isCompletelyFaithfullyFlat\`（PerfectPrismMonic.lean:1051）は Koszul 分解と pd 包の計算（\`Andre/Envelope/\`）で示す。

3. *族の飽和.* 固定した正次数モニック族の全部に根を持つ一つの拡大：\`Transfinite.exists\_monicFamilyRootedPerfectoidExtension\`（Tower.lean:1463）。添字族より大きい後続基数に沿って一元ずつ根を添加する反復 \`exists\_allBasePolynomialRoots\`（:1351）に、一元の段 \`exists\_familyRoot\_successor\`（:1427）を入れる。任意の族を一度に扱う一段の別の形 \`exists\_monicRootedPerfectoidExtension\`（RootedExtension.lean:1584）もある。

4. *ω₁ までの反復.* \`Transfinite.exists\_completelyFaithfullyFlat\_absolutelyIntegrallyClosed\`（Tower.lean:1083）は一段の拡大 \`step\` を仮定に取る形で、3 がその \`step\` を与える。反復は「固定した $`R` の上の perfectoid で p 完全忠実平坦な代数」の圏 \`AndreTowerAlgebra\`（:503）で行い、極限段は環の有向余極限の p 進完備化 \`colimitObject\`（:727）。終段 ω₁ では未完備の余極限を使う：可算個の段は上界を持つ（\`omegaOneIndex\_countable\_upperBound\`、Limit.lean:875）ので余極限は自動的に p 進完備で perfectoid（\`isIntegralPerfectoid\_ringDirectLimit\_of\_countable\_upperBound\_without\_flatness\`、Tower.lean:395）、完全忠実平坦性は \`isCompletelyFaithfullyFlat\_algebraRingDirectLimit\`（:180）、絶対整閉性は「各段のモニック多項式が後の段で根を持つ」から \`isAbsolutelyIntegrallyClosed\_directLimit\_of\_eventual\_roots\`（Limit.lean:798）。

*定理 7.3.4（原典 Thm 7.14） — 証明*

*一段.* 完全 prism $`(A,I)` で $`R=A/I` と書く。$`R` 上の全てのモニック多項式の根を形式的に添加した p 完備な $`R` 代数を $`\tilde R` とする。$`\tilde R` は $`R` の quasisyntomic な被覆で、$`R` の各モニック多項式は $`\tilde R` に解を持つ（各 $`R[Y]/(f(Y))` はモニックなので有限自由で syntomic、$`\tilde R` はそのテンソル積の有向余極限の完備化：補った）。Prop 7.11 (2) から、$`(A,I)` 上の完全 prism $`(B,IB)` と $`A/I` 代数の射 $`\tilde R\to B/IB=:R_1` で、合成 $`R\to\tilde R\to R_1` が p 完全忠実平坦なものが得られる。$`R_1` は perfectoid（Thm 3.10）で、$`R` 上の任意のモニック多項式は $`R_1` に解を持つ。

*超限反復.* $`R\mapsto R_1` を超限的に繰り返すと、quasisyntomic な被覆 $`R\to R'` で $`R'` が perfectoid かつ絶対整閉なものが得られる。原典はここを一文で済ませる。細部を補うと（補った）：極限段では有向余極限の p 進完備化を取る（perfectoid 環の有向余極限の完備化は perfectoid で、p 完全忠実平坦性も保たれる）。ω₁ 段では、p 進 Cauchy 列のデータは可算個の段に収まり、それらは ω₁ より前で上界を持つので、余極限は完備化せずに p 進完備になる。モニック多項式の係数は有限個なのである段 $`i` に入り、次の段 $`i+1` で根を持つので、ω₁ 段は絶対整閉。

*第二文.* $`X^p-a` はモニックなので根を持ち、これを繰り返すと両立する p 冪根の系が得られる。

*定理 7.3.4（原典 Thm 7.14） — 原典との差（D12）*

外側の構造（一段の拡大を超限的に積み、極限段で完備化する）は原典と同じ。一段の拡大の作り方が違う：原典は $`\tilde R` に Prop 7.11 (2)（導来 prismatic コホモロジーと Hodge–Tate 比較）を当て、本体はモニック多項式の根の prismatic envelope（階数 1 の変数で $`f(Y)/d` を δ 除算して完全化したもの）を直接作り、その p 完全忠実平坦性を Koszul 分解と pd 包の計算で示す。これは Rem 7.15 の計算と同じ種類のもの。また原典の $`\tilde R` は全てのモニック多項式の根を一度に添加するが、本体の主経路は一元ずつ根を添加して後続基数に沿って飽和させる。原典の「mod p で ind-syntomic」の強化は含めない。

:::

:::proposition "bs_7_15" (lean := "SerrePositivity.BhattScholze.Andre.VarpiComparison.perfectPrismPDTensorVarpi_isDPMorphism, SerrePositivity.BhattScholze.Andre.existsUnique_perfectPrismVarpiPDMorphism_of_unconditional, SerrePositivity.BhattScholze.Andre.VarpiComparison.hodgeTate_completelyFaithfullyFlat_iff")
*注意 7.15*　André の補題の精密形。対応表の状態：一部（component）。

*主張*　André の補題の拡大 $`R\to S` は、$`p` を法として ind-syntomic な被覆になるように選べる。根の添加の段で生じる prismatic 包絡への写像が、標数 $`p` の分割冪多項式表示と冪零イデアルに沿う平坦な持ち上げによってこの条件を満たす。

同じモニック根の商 S の envelope T の ϖ 剰余に関する PD 表示・PD 射の普遍性と被覆性の成分を直接扱う。最終的な mod p ind-syntomic 性とその二つの一般的補題全体は未供給。

*注意 7.3.5（原典 Rem 7.15） — 主張*

（André の補題の精密形）Thm 7.14 で構成した $`R\to S` は mod p で ind-syntomic な被覆にとれる。構成をほどくと、次を示せば足りる：モニックな $`f(Y)\in R[Y]` について、prism $`(A,I)` 上で $`S:=R\langle Y^{1/p^\infty}\rangle/(f(Y))` とおくと、$`S\to T:=\Delta_S` は mod p で ind-syntomic な被覆である。これは次の二つの事実から従う。

1. $`A` が $`\mathbb F_p` 代数で $`f\in A` が非零因子なら、自然な射 $`A/f^p\to D_{(f)}(A)` は $`g_i\mapsto\gamma_{p^i}(f)` により $`A/f^p\to A/f^p[g_1,g_2,\dots]/(g_1^p,g_2^p,\dots)` と同一視される。特にこの射は ind-syntomic。

2. $`A\to B=A/I` が冪零な核 $`I` を持つ $`\mathbb F_p` 代数の全射で、$`D` が平坦な $`A` 代数で $`D/ID\simeq B[g_1,g_2,\dots]/(g_1^p,g_2^p,\dots)` なら、$`D` は $`A` 上 ind-syntomic。

$`R\to S` が mod p で ind-syntomic にとれることは \[GR, Theorem 16.9.17\] からも従う。

*注意 7.3.5（原典 Rem 7.15） — Lean*

- 被覆の部分（p 完全忠実平坦性と $`\varpi` での忠実平坦性の同値）：\`hodgeTate\_completelyFaithfullyFlat\_iff\`（VarpiComparison.lean:671、$`R` の p 正則性を仮定）。

*注意 7.3.5（原典 Rem 7.15） — 証明*

「被覆」の部分は Prop 7.10 から従う。ind-syntomic 性は、底変換により $`R` が p ねじれなしの場合に帰着し、$`(\varpi^p)=(p)` となる $`\varpi\in R` を選ぶ。$`T` が prismatic envelope であることと Cor 2.39 から、$`\varphi_A^*(T/\varpi)` は $`R/\varpi[Y^{1/p^\infty}]` における $`f(Y)` の pd 包である。あとは (1)・(2) を組み合わせる。

(1) は標数 p の分冪代数についてよく知られた事実で、普遍の場合 $`A=\mathbb F_p[f]` に帰着して示せる。(2)：$`g_i` の持ち上げ $`\bar h_i\in D` を選ぶと全射 $`A[h_1,h_2,\dots]\to D`（$`h_i\mapsto\bar h_i`）が得られる。$`\bar h_i^p\in ID` なので $`\epsilon_i\in IA[h_1,h_2,\dots]` で $`h_i^p-\epsilon_i` が $`D` で 0 になるものが取れる。$`D_n=A[h_1,h_2,\dots]/(h_1^p-\epsilon_1,\dots,h_n^p-\epsilon_n)` とおくと射 $`\operatorname{colim}_nD_n\to D` が得られ、これは平坦な $`A` 代数の全射で冪零イデアル $`I` を法として同型なので同型。各 $`D_n` は $`A` 上 ind-syntomic。

*注意 7.3.5（原典 Rem 7.15） — 原典との差（D12）*

本体は Rem 7.15 の結論（mod p で ind-syntomic）を証明せず、その途中の計算（$`\varphi_A^*(T/\varpi)` の pd 包としての記述と、被覆であること）を Thm 7.14 の一段の拡大の p 完全忠実平坦性に使う（評価は定理 7.3.4 の「原典との差（D12）」）。

:::

