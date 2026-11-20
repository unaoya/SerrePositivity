-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.BhattScholze.Almost.AlmostConnectivity
import SerrePositivity.BhattScholze.Almost.AlmostTensor
import SerrePositivity.BhattScholze.Almost.AlmostTensorForward
import SerrePositivity.BhattScholze.Almost.Lemma103
import SerrePositivity.BhattScholze.Almost.PerfectoidAlmost
import SerrePositivity.BhattScholze.Inputs.PerfectoidizationInterface
import SerrePositivity.BhattScholze.Perfectoidization.CompletedTensor
import SerrePositivity.BhattScholze.Perfectoidization.Interface.Derived
import SerrePositivity.BhattScholze.Perfectoidization.Interface.IntegralExistence
import SerrePositivity.CommutativeAlgebra.Almost.Basic
import SerrePositivity.CommutativeAlgebra.EtaleStratification.Stratification

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "§10 The almost purity theorem" =>
%%%
number := false
tag := "bs-10"
%%%

BS §10 の項目と、本体の宣言との対応。本文は対応表（`research/bs-coverage`）の照合の理由で、原典の本文の写しではない。

*導入*

§10 は二つに分かれる。§10.1 は perfectoid 環 $`R` と導来 p 完備なイデアル $`J` について、$`J_{\mathrm{perfd}}=\ker(R\to(R/J)_{\mathrm{perfd}})` に関する almost 数学を作る（Thm 7.4 で $`R\to(R/J)_{\mathrm{perfd}}` が全射なので意味を持つ）。§10.2 は almost purity（Thm 10.9）と、その帰結の整代数の perfectoid 化の離散性（Thm 10.11 ＝ Thm 1.17(1)）。本体には、§10.1 の Def 10.1・Prop 10.4・Lemma 10.5 が任意のイデアルについてあり、Prop 10.2・Lemma 10.3・Rem 10.7 は単項 $`J=(g)` の場合と一般の perfectoid 商の場合がある。§10.2 は Lemma 10.12 が原典どおり本体にあり、Thm 10.9・10.11 は証明の部品（主イデアルへの帰着、分裂比較環、整閉包の完備化、filtered 余極限への帰着と有限表示近似）が本体にある。Thm 10.9・10.11 の組み立ては §8 の導来 perfectoid 化を使うので drafts にあり、Thm 10.11 は界面 \`PerfectoidizationInterfaceE3\` の欄 \`integral\` として受け取っている。形式化の設計の決定は a8-design.md にあり、原典との差として各項目の下に引く。

*10.1 任意のイデアルに関する almost 数学*

この小節を通して、$`R` は perfectoid 環、$`J\subset R` は導来 p 完備なイデアルとし、
$$`J_{\mathrm{perfd}}=\ker\big(R\to(R/J)_{\mathrm{perfd}}\big)`
と置く。Thm 7.4 により $`R\to(R/J)_{\mathrm{perfd}}` は全射なので $`(R/J)_{\mathrm{perfd}}=R/J_{\mathrm{perfd}}` であり、この小節では p 完備な R 加群・複体の $`J_{\mathrm{perfd}}` に関する almost 数学を調べる。$`J` が有限生成であることは §10.2 で使う（Thm 10.9 の仮定）。perfectoid 環は被約なので $`J_{\mathrm{perfd}}` は $`J` の根基だけで決まり、$`\sqrt J\subset J_{\mathrm{perfd}}`。番号「命題 10.1.n」はこのノートの番号で、括弧内が原典の番号（原典の Lemma は「命題」と呼ぶ）。原典 Def 10.1〜Prop 10.8 の全項目を扱う。

*基底変換についての注意.* $`f\colon R\to R'` を perfectoid 環の写像とすると、$`(JR')_{\mathrm{perfd}}` は完備テンソル $`J_{\mathrm{perfd}}\widehat\otimes_RR'\to R'` の像であり、$`J` が有限生成でもイデアルの式としては $`J_{\mathrm{perfd}}R'` の *p 進閉包*が現れる（Fayolle, Prop 2.9）。$`J_{\mathrm{perfd}}R'` そのものとの一致は一般には成り立たない：p ねじれなしの perfectoid 付値環 $`V` 上で $`R=V\langle x_1^{1/p^\infty},x_2^{1/p^\infty},\dots\rangle`、$`J=\ker(R\to V)`、$`R'=R\langle t^{1/p^\infty}\rangle` が反例になる。

*10.2 almost purity と整代数の離散性*

§10.2 の目標は、perfectoid 環 $`R` 上で、任意の閉集合 $`V(J)` に沿った分岐を扱う almost purity 定理（André の perfectoid Abhyankar の補題を含む）である。証明は三段で進む。まず Thm 10.9 を $`J`-almost の意味でだけ示し、それを使って整代数の perfectoid 化の離散性（Thm 10.11）を示し、最後に二つを合わせて Thm 10.9 を完全な形で得る。鍵になる入力は二つで、$`S\mapsto S_{\mathrm{perfd}}` の arc 降下の性質（特に Cor 8.12 の excision）と André の補題（Thm 7.14）である。Thm 10.11 の帰納法には、有限表示有限射の構成可能な層別（Lemma 10.12）を使う。

記号：$`R` は perfectoid 環、$`J\subset R` は有限生成イデアル、$`J_{\mathrm{perfd}}=\ker(R\to(R/J)_{\mathrm{perfd}})`、$`J_{\mathrm{perfd},n}` はその $`R/p^n` での像（§10.1、Rem 10.7）。

:::definition "bs_10_1" (lean := "SerrePositivity.BhattScholze.Almost.perfectoidKernel, SerrePositivity.Almost.IsAlmostZero")
*定義 10.1*　J-almost zero。対応表の状態：一部（component）。

*主張*　perfectoid 環 $`R` の $`p` 完備イデアル $`J` に対し、導来 $`p` 完備な $`R` 加群 $`M` は $`J_{\mathrm{perfd}}M=0` のとき $`J`-almost 零である。$`J=(p)` なら古典的な almost 零性に一致する。

同じ J\_perfd を商の普遍 perfectoid 化への核で定め、IsAlmostZero の零化条件を適用する。末尾 J=(p) の核が√pRという同一視まではこの行の型から直接得ていない。

*定義 10.1.1（原典 Def 10.1） — 主張*

導来 p 完備な R 加群 $`M` が *J-almost zero* であるとは、$`J_{\mathrm{perfd}}M=0` となること。

$`J=(p)` のときは $`J_{\mathrm{perfd}}=\sqrt{pR}` であり、この概念は perfectoid 環上の加群に対する通常の「almost zero」と一致する。

*定義 10.1.1（原典 Def 10.1） — Lean*

零化の述語は任意の環・イデアル・加群について \`IsAlmostZero\`（CommutativeAlgebra/Almost/Basic:38、$`I\le\operatorname{Ann}(M)`。完備性は述語に含めない）。任意の $`J` の $`J_{\mathrm{perfd}}` は \`perfectoidKernel\`（Almost/AlmostConnectivity:38）で、古典的な商 $`R/J` の perfectoid 化への写像 \`quotientPerfdMap\`（:34）の核。その全射性（Thm 7.4）\`quotientPerfdMap\_surjective\`（:100）、$`R/J_{\mathrm{perfd}}` が perfectoid であること \`perfectoidKernel\_quotient\_isIntegralPerfectoid\`（:108）、$`J\subset J_{\mathrm{perfd}}` \`le\_perfectoidKernel\`（:41）、普遍性 \`perfectoidKernel\_le\`（:47、$`J` を殺す perfectoid 環への写像は $`J_{\mathrm{perfd}}` も殺す）、単調性 \`perfectoidKernel\_mono\`（:61）、根基で決まること \`perfectoidIdeal\_radical\`（:67）。複体版の J-almost 零性 \`IsJAlmostZero\`（:86）は命題 10.1.4 で使う。

単項 $`J=(g)` の場合は別の定義 \`perfectoidIdeal\`（PerfectoidIdeal/Basic:37）もあり、定義を展開すると \`perfectoidKernel\` の $`J=(g)` の場合と同じ式になる。$`\sqrt{(g)}\subset(g)_{\mathrm{perfd}}` は \`radical\_span\_le\_perfectoidIdeal\`（PerfectoidIdeal/Powers:147）、$`(g^n)_{\mathrm{perfd}}=(g)_{\mathrm{perfd}}` は \`perfectoidIdeal\_pow\_eq\`（:154）。$`J=(p)` での等式 $`J_{\mathrm{perfd}}=\sqrt{pR}` は本体にない（包含 $`\supset` だけが上の補題）。

*定義 10.1.1（原典 Def 10.1） — 証明*

$`J=(p)` の場合の等式（補った）。$`R` は perfectoid なので $`R/p` は semiperfect（Frobenius が全射）。すると $`R/\sqrt{pR}` は被約かつ semiperfect、すなわち完全な $`\mathbb F_p` 代数であり、特に perfectoid。一方 $`\mathbb F_p` 代数 $`S` の perfectoid 化は完全化 $`S_{\mathrm{perf}}=\operatorname{colim}_\varphi S` で、semiperfect な $`S` では $`S_{\mathrm{perf}}=S/\sqrt0`。$`S=R/p` に当てると $`(R/p)_{\mathrm{perfd}}=R/\sqrt{pR}` なので $`J_{\mathrm{perfd}}=\sqrt{pR}`。通常の almost 数学は $`\sqrt{pR}`（$`p` が p 冪根を持つときは $`(p^{1/p^\infty})`）を基本のイデアルに取るので、両者は一致する。

:::

:::proposition "bs_10_2" (lean := "SerrePositivity.BhattScholze.Almost.perfectoidIdeal_isAlmostZero_extension, SerrePositivity.BhattScholze.integralPerfectoid_completeIdealExtensionClosed")
*命題 10.2*　almost zero の拡大閉性。対応表の状態：一部（component）。

*主張*　$`J`-almost 零な導来 $`p` 完備 $`R` 加群は核・余核・拡大で閉じ、テンソルイデアルをなす。その圏は $`(R/J)_{\mathrm{perfd}}` 上の導来 $`p` 完備加群の圏に同値である。

同じ perfectoid 商の核に関する導来 p 完備短完全列の拡大閉性は直接得る。任意 J は perfectoidKernel\_quotient\_isIntegralPerfectoid と一般商の extension-closed 定理を適用。圏同値と tensor ideal 全体は含まない。

*命題 10.1.2（原典 Prop 10.2） — 主張*

J-almost zero な導来 p 完備 R 加群のなす部分圏は、導来 p 完備 R 加群の圏の中で核・余核・拡大で閉じ、⊗ イデアルをなす。さらにこの部分圏は、導来 p 完備な $`(R/J)_{\mathrm{perfd}}` 加群の圏と同値である。

*命題 10.1.2（原典 Prop 10.2） — Lean*

*核・余核*：部分加群・商加群での閉性 \`IsAlmostZero.submodule\`（CommutativeAlgebra/Almost/Basic:87）・\`IsAlmostZero.quotient\`（:91）。任意の加群について成り立つ。

*拡大*：単項 $`J=(g)` の場合が \`perfectoidIdeal\_isAlmostZero\_extension\`（Almost/PerfectoidAlmost:470、導来 p 完備加群の短完全列で両端が $`(g)_{\mathrm{perfd}}` で消えれば中央も消える）。もう一つの形として、$`R` と $`R/I` がともに perfectoid な任意のイデアル $`I` について、導来 p 完備加群の短完全列での閉性 \`integralPerfectoid\_completeIdealExtensionClosed\`（Perfectoidization/CompletedTensor:294、述語は \`CompleteIdealExtensionClosed\`、DerivedCompletion/IdealExtension:44）。\`perfectoidKernel\_quotient\_isIntegralPerfectoid\`（Almost/AlmostConnectivity:108）と合わせると任意の $`J` の $`J_{\mathrm{perfd}}` に当てはまる（この特殊化を述べる名前つきの宣言はない）。単項の場合のこの形は \`perfectoidIdeal\_completeIdealExtensionClosed\`（PerfectoidIdeal/CompletedQuotient:63）。

*商環の加群との対応（加群の水準）*：$`K` で消える加群に $`R/K` 加群の構造を入れる \`quotientModule\`（CommutativeAlgebra/Almost/Quotient:115）、線形写像を $`R/K` 線形写像にする \`quotientLinearMap\`（:152）。⊗ イデアルであること、圏同値、RHom の保存は本体にない（下の D14）。

*命題 10.1.2（原典 Prop 10.2） — 証明*

原典の証明。忘却関手 $`\iota\colon\{\text{導来 p 完備な }(R/J)_{\mathrm{perfd}}\text{ 加群}\}\to\{\text{導来 p 完備な R 加群}\}` が完全忠実で $`\mathrm{Ext}^1` を保つことを示せばよく、実際 RHom を保つことを示す。$`M,N` を導来 p 完備な $`(R/J)_{\mathrm{perfd}}` 加群とすると、随伴により
$$`\mathrm{RHom}_R(M,N)=\mathrm{RHom}_{(R/J)_{\mathrm{perfd}}}\big(M\widehat\otimes^L_R(R/J)_{\mathrm{perfd}},\,N\big).`
よって $`M\to M\widehat\otimes^L_R(R/J)_{\mathrm{perfd}}` が同型であることを見ればよい。$`M` は $`(R/J)_{\mathrm{perfd}}` 加群なので $`M=(R/J)_{\mathrm{perfd}}` の場合に帰着し、それは命題 10.1.3 の一部（$`(R/J)_{\mathrm{perfd}}` の自己積が同型）。

結論の取り出し方（補った）。$`Q=(R/J)_{\mathrm{perfd}}=R/J_{\mathrm{perfd}}` なので、R 加群が J-almost zero であることは $`Q` 加群の構造を（一意に）持つことと同じで、$`\iota` の本質的な像がちょうど J-almost zero な加群になる。核・余核は $`Q` 加群の部分加群・商加群なので閉じる（これは $`J_{\mathrm{perfd}}` が零化することから直ちにも分かる）。拡大：両端が $`Q` 加群の拡大は $`\mathrm{Ext}^1_R(M_3,M_1)` の元で、$`\iota` が $`\mathrm{Ext}^1` を保つので $`\mathrm{Ext}^1_Q(M_3,M_1)` から来る、すなわち中央も $`Q` 加群。⊗ イデアル：$`M` が $`Q` 加群なら、任意の導来 p 完備 R 加群 $`N` との完備テンソル（$`M\otimes^L_RN` の導来 p 完備化の $`H^0`）も $`M` を通じて $`Q` 加群になる。

Lean の拡大閉性の二つの証明（補った）。(a) \`perfectoidIdeal\_isAlmostZero\_extension\` は命題 10.1.4 の加群版を使う：両端 $`M_1,M_3` について $`K\widehat\otimes^L_RM_i=0`（$`K=J_{\mathrm{perfd}}`、命題 10.1.3 の混合積の消滅を $`Q` 加群に移す）、三角形 $`K\widehat\otimes M_1\to K\widehat\otimes M_2\to K\widehat\otimes M_3` で中央も零、すると係数の三角形 $`K\to R\to Q` から $`M_2\simeq Q\widehat\otimes^L_RM_2` となり、その $`H^0` の $`Q` 作用から $`KM_2=0`。(b) \`integralPerfectoid\_completeIdealExtensionClosed\` は conormal を使う：命題 10.1.3 の $`Q\widehat\otimes^L_RQ\simeq Q` から、ファイバーの完備化が零なので $`p` がファイバーに同型で作用し、$`\mathrm{Tor}_1^R(Q,Q)=K/K^2` 上で $`p` 倍が全射になる（\`quotientTorOne\_smul\_surjective\_of\_completed\_mul\_isIso\`、DerivedCompletion/IdealExtension:184）。短完全列 $`0\to M_1\to M_2\to M_3\to0` で両端が $`K` で消えるとき、$`a\in K` の作用は $`M_3\to M_1` を引き起こし、$`a\mapsto` この写像は $`K^2` を殺すので R 線形写像 $`K/K^2\to\mathrm{Hom}_R(M_3,M_1)` になる。右辺は導来 p 完備で、p 可除な加群から導来 p 完備な加群への線形写像は零（p 可除な元の列は $`\mathbb Z[1/p]` からの写像を与えるが、導来 p 完備な加群への $`\mathbb Z[1/p]` からの写像は零）なので、$`K` は $`M_2` を殺す（\`completeIdealExtensionClosed\_of\_conormal\_surjective\`、同 :133）。

*命題 10.1.2（原典 Prop 10.2） — 原典との差（D14）*

原典は忘却関手の完全忠実性（RHom の保存）から圏同値と閉性をまとめて出す。Lean は使う拡大閉性だけを、完備テンソルの判定（または conormal の p 可除性）で示し、圏同値・⊗ イデアルは結論にしない。核・余核の閉性は零化の定義から直ちに出る。

:::

:::lemma_ "bs_10_3" (lean := "SerrePositivity.BhattScholze.Almost.perfectoidIdeal_lemma103, SerrePositivity.BhattScholze.Almost.integralPerfectoid_completedQuotientTensorIdeal_isZero, SerrePositivity.BhattScholze.Almost.perfectoidIdeal_completedQuotientMul_isIso, SerrePositivity.BhattScholze.Almost.integralPerfectoid_completedIdealTensorQuotient_isZero, SerrePositivity.BhattScholze.Almost.integralPerfectoid_completedIdealMul_isIso, SerrePositivity.BhattScholze.Almost.integralPerfectoid_completedDerivedIdealMul_isIso, SerrePositivity.BhattScholze.Almost.perfectoidKernel_quotient_isIntegralPerfectoid, SerrePositivity.BhattScholze.integralPerfectoid_completedQuotientMul_isIso")
*補題 10.3*　J\_perfd に沿った完備テンソル。対応表の状態：本体にある。

*主張*　$`K=J_{\mathrm{perfd}}`、$`Q=(R/J)_{\mathrm{perfd}}` とおくと、導来完備テンソルでの積 $`K\widehat\otimes_R^{\mathbf L}K\to K` と $`Q\widehat\otimes_R^{\mathbf L}Q\to Q` は擬同型であり、$`K\widehat\otimes_R^{\mathbf L}Q=0` である。

K=perfectoidKernel(J) の商の perfectoid 性と環の第一同型定理に一般商の三定理を適用し、同じ標準積 K⊗̂ᴸK→K・Q⊗̂ᴸQ→Q の同型と K⊗̂ᴸQ=0 を得る。任意 J に対し組み合わせ可能で、単項に限定しない。

*命題 10.1.3（原典 Lemma 10.3） — 主張*

積写像
$$`J_{\mathrm{perfd}}\widehat\otimes^L_RJ_{\mathrm{perfd}}\to J_{\mathrm{perfd}},\qquad (R/J)_{\mathrm{perfd}}\widehat\otimes^L_R(R/J)_{\mathrm{perfd}}\to(R/J)_{\mathrm{perfd}}`
は擬同型であり、
$$`J_{\mathrm{perfd}}\widehat\otimes^L_R(R/J)_{\mathrm{perfd}}=0.`
証明の中で、より一般に次を示す：perfectoid 環の写像 $`S\leftarrow R\to T` について、$`S\widehat\otimes^L_RT` は次数 0 に集中し、perfectoid 環である。

*命題 10.1.3（原典 Lemma 10.3） — Lean*

*三つの主張*（$`R` と $`R/I` がともに perfectoid な任意のイデアル $`I` について）：商の自己積の同型 \`integralPerfectoid\_completedQuotientMul\_isIso\`（Perfectoidization/CompletedTensor:286）、混合積の消滅 \`integralPerfectoid\_completedQuotientTensorIdeal\_isZero\`・\`integralPerfectoid\_completedIdealTensorQuotient\_isZero\`（Almost/Lemma103:87・123）、イデアルの自己積の同型 \`integralPerfectoid\_completedIdealMul\_isIso\`（:190）とその標的を $`I[0]` にした形 \`integralPerfectoid\_completedDerivedIdealMul\_isIso\`（:256）。$`I` の導来 p 完備性 \`integralPerfectoid\_quotientIdeal\_isModuleComplete\`（:217）。任意の $`J` の $`J_{\mathrm{perfd}}` へは \`perfectoidKernel\_quotient\_isIntegralPerfectoid\`（Almost/AlmostConnectivity:108）で当てはまる（特殊化を述べる名前つきの宣言はない）。

*命題 10.1.3（原典 Lemma 10.3） — 証明*

$`Q=(R/J)_{\mathrm{perfd}}`、$`K=J_{\mathrm{perfd}}` と書く。*帰着.* 最初の二つの写像が同型であることは $`K\widehat\otimes^L_RQ=0` と同値である（補った：係数の三角形 $`K\to R\to Q` に $`Q` を完備テンソルすると $`K\widehat\otimes Q\to Q\to Q\widehat\otimes Q` で、合成 $`Q\to Q\widehat\otimes Q\to Q` は恒等なので、積 $`Q\widehat\otimes Q\to Q` が同型 ⇔ $`Q\to Q\widehat\otimes Q` が同型 ⇔ $`K\widehat\otimes Q=0`。$`K` を完備テンソルすると $`K\widehat\otimes K\to K\to K\widehat\otimes Q` で、同様に $`K\widehat\otimes K\to K` が同型 ⇔ $`K\widehat\otimes Q=0`）。よって $`Q\widehat\otimes^L_RQ\to Q` が擬同型であることを示せばよい。$`H^0` では明らか（$`Q` は $`R` の商なので $`Q\otimes_RQ=Q`）なので、$`Q\widehat\otimes^L_RQ` が次数 0 に集中することを示せばよく、より一般に上の $`S\widehat\otimes^L_RT` の主張を示す。

*一般の主張.* $`(B,IB)\leftarrow(A,I)\to(C,IC)` を $`S\leftarrow R\to T` に対応する完全 prism の図式とする。$`D:=B\widehat\otimes^L_AC` は次数 0 に集中し完全 δ 環である。これは（導来）mod p で確かめればよく、mod p では完全環の Tor 独立性（\[BS17, Lemma 3.16\]）から従う：$`\bar A=A/p` 上の完全環 $`\bar B,\bar C` について $`\mathrm{Tor}^{\bar A}_i(\bar B,\bar C)=0`（$`i>0`）、かつ完全環のテンソル積は完全。とくに $`(D,ID)` は完全 prism で、$`ID` は Cartier 因子を定める。よって $`D/ID=S\widehat\otimes^L_RT`（補った：$`D\otimes^L_AA/I=B/IB\,\widehat\otimes^L_{A/I}\,C/IC` で、$`A/I=R` 等）は次数 0 に集中し perfectoid。

Lean の証明の順（補った）。まず一般の主張から $`Q\widehat\otimes Q` が離散と分かり、全射 $`R\to Q` の積写像が同型になる（\`completedSurjectiveAlgebraMul\_isIso\`、DerivedCompletion/CompletedAlgebraH0:1149）。次に上の三角形で混合積の消滅、さらにイデアルの自己積の同型を出す。原典の順を逆にたどったもの。完全環の Tor 独立性は \[BS17\] の単体的な証明ではなく、自由な完全多項式代数による平坦な全射表示と Tor の底変換で示す（D13）。

*命題 10.1.3（原典 Lemma 10.3） — 原典との差（D13）*

原典は mod p の Tor 独立性を \[BS17, Lemma 3.16\] に任せる。そこでは Tor を単体的可換環 $`B_\bullet(\bar A,\bar A,\bar B)\otimes_{\bar A}\bar C` のホモトピー群として表し、Frobenius が同型でありかつ正次数で零を引き起こすことを使う（p 乗写像は加法的でないので、基点付き単体集合のホモトピー群を経由する）。Lean は単体的な議論を使わず、完全環 $`\bar B` を自由な完全多項式代数の平坦な全射の像として表して Tor を底変換で計算する代数的な証明をとる。

:::

:::proposition "bs_10_4" (lean := "SerrePositivity.BhattScholze.Almost.isAlmostZero_iff_completedTensor_isZero, SerrePositivity.BhattScholze.Almost.isAlmostZero_of_completedTensor_isZero")
*命題 10.4*　非有界複体の almost zero。対応表の状態：一部（component）。

*主張*　導来 $`p` 完備な $`R` 複体 $`M` の全コホモロジーが $`J`-almost 零であることと、$`J_{\mathrm{perfd}}` との導来完備テンソルが零になることは同値である。こうした複体は厚いテンソルイデアルをなし、$`(R/J)_{\mathrm{perfd}}` の導来 $`p` 完備複体の圏と同値である。

同じ任意の p 完備 J と同じ p 完備複体 M について、全 cohomology の K 零化 iff K との completed tensor が零という最初の同値を証明する。後半の導来圏同値・thick tensor ideal 全体は含まない。

*命題 10.1.4（原典 Prop 10.4） — 主張*

R 加群の導来 p 完備な複体 $`M` について、$`M` が J-almost zero である（すなわち全ての $`i` で $`H^i(M)` が J-almost zero）ことと
$$`J_{\mathrm{perfd}}\widehat\otimes^L_RM=0`
は同値。このような複体のなす圏は、$`(R/J)_{\mathrm{perfd}}` 加群の導来 p 完備な複体の圏 $`D_{p\text{-comp}}((R/J)_{\mathrm{perfd}})` と同値であり、導来 p 完備な R 加群の複体全体の圏の中で thick な ⊗ イデアルをなす。

*命題 10.1.4（原典 Prop 10.4） — Lean*

*同値*（任意の $`J`、原典の仮定どおり $`J` は導来 p 完備）：\`isAlmostZero\_iff\_completedTensor\_isZero\`（Almost/AlmostTensorForward:394）。複体は導来 ∞ 圏の頂点 \`DVertex\`（Almost/CompletedModuleTensor:36）で、完備テンソルは \`completedModuleTensor\`（:39）、$`J_{\mathrm{perfd}}\widehat\otimes^L_R-` は \`kernelTensor\`（Almost/AlmostTensor:55）、$`(R/J)_{\mathrm{perfd}}\widehat\otimes^L_R-` は \`quotientTensor\`（:85）、J-almost 零性は \`IsJAlmostZero\`（Almost/AlmostConnectivity:86）、導来 p 完備性は \`isPCompleteVertex\`（:138）。

命題 10.1.3 で使う完備テンソルの模型（有界上側の導来圏）と、ここでの頂点の完備テンソルを、同じ自由分解で比べる同型 \`completedTensorAlgebraVertexIso\`（Almost/CompletedModuleTensor:71）。

*命題 10.1.4（原典 Prop 10.4） — 証明*

原典の証明。命題 10.1.2 の証明で $`\iota\colon D_{p\text{-comp}}((R/J)_{\mathrm{perfd}})\to D_{p\text{-comp}}(R)` が完全忠実であることは示した。像の対象が J-almost zero なのは明らか。逆に J-almost zero な複体は、切り捨ての極限かつ余極限として書け、$`\iota` は全ての極限・余極限と可換なので像に入る。像の対象 $`M` については
$$`J_{\mathrm{perfd}}\widehat\otimes^L_RM=J_{\mathrm{perfd}}\widehat\otimes^L_R(R/J)_{\mathrm{perfd}}\otimes^L_{(R/J)_{\mathrm{perfd}}}M=0`
（命題 10.1.3）。逆に $`J_{\mathrm{perfd}}\widehat\otimes^L_RM=0` なら、係数の三角形から $`M\to M\widehat\otimes^L_R(R/J)_{\mathrm{perfd}}` は擬同型で、右辺のコホモロジーは $`(R/J)_{\mathrm{perfd}}` 加群なので $`M` は J-almost zero。後半の thick ⊗ イデアルであることは圏同値と、$`\iota` が三角形・直和因子・テンソルと両立することから（補った）。

Lean の証明（補った）。逆向きは原典どおり：係数の短完全列 $`J_{\mathrm{perfd}}\to R\to(R/J)_{\mathrm{perfd}}` を半自由代表で完備導来圏の三角形に移し、第一項が零なら第二の射が同型で、$`(R/J)_{\mathrm{perfd}}` の作用を各コホモロジーに渡す。順向きは圏同値を使わずに直接示す：各コホモロジー加群 $`H^i(M)` には $`(R/J)_{\mathrm{perfd}}` 加群の構造が入るので、命題 10.1.3 の混合積の消滅から $`J_{\mathrm{perfd}}\widehat\otimes H^i(M)=0`。良い切り捨ての列の各段の差は一つのコホモロジー加群のずらしなので、有限区間の切り捨てでテンソルが消える。非有界な $`M` は切り捨ての逐次余極限で、完備化の前に $`p^n` の Koszul 簡約をとって余極限と交換し、消滅を移す。

*命題 10.1.4（原典 Prop 10.4） — 原典との差（D14・D66）*

原典は圏同値（$`\iota` の完全忠実性と像の記述）から同値を導く。Lean は必要な同値「J-almost zero ⇔ $`J_{\mathrm{perfd}}\widehat\otimes^L_RM=0`」だけを、命題 10.1.3 の一般形と係数の三角形、切り捨ての積み上げで示し、圏同値・thick ⊗ イデアルは結論にしない（D66。方針は D14 と同じで、評価は命題 10.1.2 の下）。

:::

:::lemma_ "bs_10_5" (lean := "SerrePositivity.BhattScholze.Almost.connective_iff_almost, SerrePositivity.BhattScholze.Almost.isAlmostConnective_iff_completedTensor_connective")
*補題 10.5*　連結性の判定。対応表の状態：本体にある。

*主張*　$`p` 完備 $`R` 複体 $`M` が連結であることと、$`M` を $`R/J_{\mathrm{perfd}}` へ導来完備底変換すると連結で、かつ $`M` の正コホモロジーがすべて $`J`-almost 零であることは同値である。

§10.1の立ち仮定 J が導来 p 完備という条件を保ち、同じ M の connective iff 商との完備テンソルが connective かつ J-almost connective に一致。

*命題 10.1.5（原典 Lemma 10.5） — 主張*

p 完備な複体 $`M\in D(R)` が連結であることは、$`M\widehat\otimes^L_RR/J_{\mathrm{perfd}}` が連結で、かつ $`M` が *J-almost 連結*（すなわち $`i>0` で $`H^i(M)` が J-almost zero）であることと同値。

*命題 10.1.5（原典 Lemma 10.5） — 証明*

「のみ」の向きは、$`(-)\widehat\otimes^L_RR/J_{\mathrm{perfd}}` が連結性を保つことから明らか（$`M` が連結なら $`i>0` で $`H^i(M)=0` なので J-almost 連結）。逆向き：導来 p 完備な $`M` について三角形
$$`J_{\mathrm{perfd}}\widehat\otimes^L_RM\to M\to(R/J_{\mathrm{perfd}})\widehat\otimes^L_RM`
があるので、$`M` が J-almost 連結なら $`J_{\mathrm{perfd}}\widehat\otimes^L_RM` が連結であることを示せばよい（逆も成り立ち、明らか）。三角形
$$`J_{\mathrm{perfd}}\widehat\otimes^L_R\tau^{\le0}M\to J_{\mathrm{perfd}}\widehat\otimes^L_RM\to J_{\mathrm{perfd}}\widehat\otimes^L_R\tau^{>0}M`
で、$`\tau^{>0}M` は J-almost zero なので最後の項は命題 10.1.4 により零、最初の項は連結。Thm 10.11 の帰納法でこの判定を使う。

:::

:::definition "bs_10_6"
*定義 10.6*　J-almost G-Galois 拡大。対応表の状態：なし。

J-almost G-Galois の群作用・指定二射による定義を本体で未同定。

*定義 10.1.6（原典 Def 10.6） — 主張*

有限群 $`G` の作用を持つ p 完備な R 代数 $`S` が *J-almost G-Galois 拡大*であるとは、写像
$$`R\to R\Gamma(G,S),\qquad S\widehat\otimes^L_RS\to\prod_GS`
が J-almost 同型、すなわち錐が J-almost zero であること。

*定義 10.1.6（原典 Def 10.6） — Lean*

本体にない。Thm 10.9 の Lean の証明はこの概念を使わない（D63）。

:::

:::proposition "bs_10_7" (lean := "SerrePositivity.BhattScholze.Almost.perfectoidIdealMod_idempotent, SerrePositivity.BhattScholze.integralPerfectoid_ideal_mod_power_idempotent")
*注意 10.7*　mod pⁿ の冪等性。対応表の状態：一部（component）。

*主張*　定義直後の $`J`-almost Galois 条件は、$`p^n` を法とした不変環への比較と $`G` で添字づけた積へのテンソル比較を $`J`-almost 同型にする。$`R/p^n` 内の $`J_{\mathrm{perfd}}` の像は冪等で、$`J` が単項ならその像のテンソル平方は $`R/p^n` 上平坦である。

原文明記の J\_perfd の mod p\^n 像の冪等性は、任意 J の perfectoid 商の核への一般定理の適用で得る。Galois 条件の mod p\^n 版と単項核の tensor flatness は含まない。

*注意 10.1.7（原典 Rem 10.7） — 主張*

(1) 定義 10.1.6 の条件から mod $`p^n` の同様の主張が従い、$`H^0` をとると
$$`R/p^n\to(S/p^n)^G,\qquad S/p^n\otimes_{R/p^n}S/p^n\to\prod_GS/p^n`
は J-almost 同型である。

(2) 各 $`n` について $`(R/p^n,J_{\mathrm{perfd},n})` は almost の設定（\[GR03, §2.1.1\] の basic setup）を定める。ここで $`J_{\mathrm{perfd},n}` は $`J_{\mathrm{perfd}}` の $`R/p^n` での像で、$`R/p^n` の冪等イデアルである。

(3) $`J=(g)` が一つの元で生成されるなら、$`J_{\mathrm{perfd},n}\otimes_{R/p^n}J_{\mathrm{perfd},n}` は平坦な $`R/p^n` 加群である（\[GR03, §2.5.15\] の仮定）。実際 $`g` が p 冪根を持つとき、これは $`\operatorname{colim}_{g^{1/p^i-1/p^{i-1}}}R/p^n` で与えられる。

*注意 10.1.7（原典 Rem 10.7） — Lean*

(2) 冪等性：単項 $`J=(g)` の場合 \`perfectoidIdealMod\_idempotent\`（Almost/PerfectoidAlmost:343、像のイデアル \`perfectoidIdealMod\` は :45）。$`R` と $`R/I` がともに perfectoid な任意の $`I` について \`integralPerfectoid\_ideal\_mod\_power\_idempotent\`（Perfectoidization/CompletedTensor:301）で、\`perfectoidKernel\_quotient\_isIntegralPerfectoid\`（Almost/AlmostConnectivity:108）と合わせると任意の $`J` に当てはまる（特殊化を述べる名前つきの宣言はない）。途中の段：conormal の完備化の消滅 \`perfectoidIdeal\_conormal\_completion\_isZero\`（Almost/PerfectoidAlmost:194）、$`K=K^2+p^nK` \`perfectoidIdeal\_eq\_square\_sup\_pow\_mul\`（:312）、一般の判定 \`ideal\_mod\_power\_idempotent\_of\_conormal\_surjective\`（DerivedCompletion/IdealExtension:62）・\`ideal\_mod\_power\_idempotent\_of\_completed\_quotient\_mul\_isIso\`（:217）。almost の設定：冪等イデアルで消える加群の Serre 類 \`zeroObjects\`（CommutativeAlgebra/Almost/Category:41）と almost 加群の圏 \`ModuleCategory\`（:67）、単項の $`(R/p^N,(g)_{\mathrm{perfd},N})` への適用 \`perfectoidAlmostModCategory\`（Almost/PerfectoidAlmost:512）。

(3) 平坦性と余極限の記述は本体にない。関連して、$`g` が両立する p 冪根の族 $`\rho`（$`\rho_0=g`）を持つとき、$`(g)_{\mathrm{perfd}}` の $`R/p^k` での像が根の生成するイデアルの像と一致すること \`perfectoidIdeal\_mod\_p\_pow\_eq\_compatibleRootIdeal\`（PerfectoidIdeal/Cover:105）。

*注意 10.1.7（原典 Rem 10.7） — 証明*

(1)（補った）。錐が J-almost zero な写像に $`\otimes^L\mathbb Z/p^n` をとっても錐は J-almost zero（命題 10.1.4 の ⊗ イデアル性）。$`R\Gamma(G,-)` は左 t 完全なので、$`X\in D^{\le0}` について $`H^0R\Gamma(G,X)=H^0(G,H^0X)`。よって $`H^0` は $`R/p^n\to(S/p^n)^G` と $`S/p^n\otimes_{R/p^n}S/p^n\to\prod_GS/p^n`。錐 $`C` の長完全列 $`H^{-1}C\to H^0A\to H^0B\to H^0C` で両端が J-almost zero なので、$`H^0` の写像は J-almost 同型。

(2) 原典は冪等性を述べるだけ。（補った）$`K=J_{\mathrm{perfd}}`、$`Q=R/K` とする。命題 10.1.3 の $`Q\widehat\otimes^L_RQ\simeq Q` から、積写像のファイバー $`F`（次数 $`\le-1`、$`H^{-1}F=\mathrm{Tor}_1^R(Q,Q)=K/K^2`）の導来 p 完備化は零、すなわち $`p` が $`F` に同型で作用する。$`F\xrightarrow{p}F\to F/p` の長完全列で $`H^{-1}(F/p)=0` なので $`K/K^2` 上で $`p` 倍は全射：$`K=K^2+pK`。繰り返して $`K=K^2+p^nK`、これを $`R/p^n` に写すと $`J_{\mathrm{perfd},n}^2=J_{\mathrm{perfd},n}`。冪等イデアル $`\mathfrak m` について、$`\mathfrak m` で消える加群は拡大で閉じる（$`\mathfrak m^2=\mathfrak m` なので、両端が消えれば中央は $`\mathfrak m^2=\mathfrak m` で消える）ので Serre 類をなし、これが almost の設定を与える。

(3) 原典の脚注 17。$`J_{\mathrm{perfd}}/p^n` について、第 $`i` 成分の $`a` を $`g^{1/p^i}a` に送る写像
$$`\operatorname{colim}_{g^{1/p^i-1/p^{i+1}}}R/p^n\to J_{\mathrm{perfd}}/p^n`
が同型であることを示す（左辺は自由加群の有向余極限なので平坦）。全射は明らか。単射：$`a\in R` が第 $`i` 成分で 0 に写るとすると、ある $`k`（$`i` より大きくとれる）と $`b\in R` で $`g^{1/p^i}a=p^ng^{1/p^k}b`。よって $`g^{1/p^k}(g^{1/p^i-1/p^k}a-p^nb)=0`。$`R` は被約なので $`g^{1/p^{k+1}}(g^{1/p^i-1/p^k}a-p^nb)=0`（$`y=g^{1/p^{k+1}}x` について $`y^p=g^{1/p^k}x^p=0`、補った）、すなわち $`g^{1/p^i-1/p^k+1/p^{k+1}}a=p^ng^{1/p^{k+1}}b\in p^nR`。したがって $`a` の余極限での像は 0。（原典の本文と脚注の最初の式は添字を $`g^{1/p^i-1/p^{i-1}}` と書くが、脚注の最後の行と同じく、$`i` 番目から $`i+1` 番目への推移を $`g^{1/p^i-1/p^{i+1}}` 倍と読んだ。これで第 $`i` 成分の写像 $`a\mapsto g^{1/p^i}a` と両立する。）

:::

:::proposition "bs_10_8"
*命題 10.8*　André の命題（And18b 1.9.1）。対応表の状態：なし。

J-almost G-Galois から almost finite projective・unramified への同じ主張を未同定。

*命題 10.1.8（原典 Prop 10.8） — 主張*

（\[And18b, Proposition 1.9.1\]）$`S` を $`G` 作用を持つ p 完備な R 代数で、J-almost G-Galois 被覆であるものとする。このとき $`R/p^n\to S/p^n` は $`(R/p^n,J_{\mathrm{perfd},n})` に関して almost 有限射影的かつ almost 不分岐である。より一般に、部分群 $`H\subset G` について $`S'=S^H\to S` が J-almost H-Galois 被覆なら、$`R/p^n\to S'/p^n` は almost 有限射影的かつ almost 不分岐である。

*命題 10.1.8（原典 Prop 10.8） — Lean*

本体にない。Thm 10.9 の Lean の証明はこの命題を使わない（D63）。下の証明で触れる「J-almost zero ⇔ 全ての $`g\in J` で (g)-almost zero」の有限生成な $`J` の生成元ごとの形は \`isAlmostZero\_iff\_forall\_gen\`（Almost/AlmostGenerators:155、複体について）。

*命題 10.1.8（原典 Prop 10.8） — 証明*

原典は \[And18b, Proposition 1.9.1\] を引用する。\[And18b, §1.1\] には $`\mathfrak m\otimes_{\mathfrak A}\mathfrak m` の平坦性という常設の仮定があり、そのままでは命題 10.1.8 の状況に当てはまらない。これを回避するには、\[And18b, Proposition 1.9.1\] の証明にこの仮定が不要であることを直接確かめるか、または注意 10.1.7 (3)（単項 $`J` なら平坦性の仮定が満たされる）と、$`D_{p\text{-comp}}(R)` の対象が J-almost zero であることは全ての $`g\in J` について (g)-almost zero であることと同値であることを使って、平坦な場合に帰着する。

:::

:::theorem "bs_10_9"
*定理 10.9*　almost purity。対応表の状態：なし。

主 ideal への帰着・分裂比較環・局所化同型の証明部品は本体。指定 S\_perfd の離散性と almost finite projective/unramified の主張は未組立で、補助を partial にしない。

*定理 10.2.1（原典 Thm 10.9） — 主張*

$`R` を perfectoid 環、$`J\subset R` を有限生成イデアル、$`J_{\mathrm{perfd}}=\ker(R\to(R/J)_{\mathrm{perfd}})` とする。$`S` を有限表示な有限 $`R` 代数で、$`\mathrm{Spec}(S)\to\mathrm{Spec}(R)` が $`V(J)` の外で有限エタールなものとする。このとき

- $`S_{\mathrm{perfd}}` は離散で perfectoid 環であり、$`S\to S_{\mathrm{perfd}}` は $`V(J)` の外で同型である。

- 各 $`n>0` について、$`R/p^n\to S_{\mathrm{perfd}}/p^n` は almost setting $`(R/p^n,J_{\mathrm{perfd},n})` に関して almost 有限射影かつ almost 不分岐である。

さらに、有限群 $`G` が $`S` に作用し、$`\mathrm{Spec}(S)\to\mathrm{Spec}(R)` が $`V(J)` の外で $`G`-Galois 被覆なら、$`R\to S_{\mathrm{perfd}}` は Def 10.6 の意味の $`J`-almost $`G`-Galois 被覆である。

*定理 10.2.1（原典 Thm 10.9） — Lean*

定理そのものは本体にない。下の証明の (0)(1) の環論的な部品が本体にある。

- 絶対整閉な基底上の分裂：$`R` が絶対整閉で $`S[1/g]` が $`R[1/g]` 上有限エタールなら、$`D(g)` の有限な開被覆で各片の上で $`S` が自明な被覆 $`R^{r}` に分裂する（\`IsAbsolutelyIntegrallyClosed.finiteEtaleAway\_exists\_finite\_cover\`（Etale:327））。

- 自明な被覆との比較環：分裂 $`S[1/g]\simeq R[1/g]^r`（\`AwaySplitting\`（FiniteEtaleComparison:36））のとき、$`S` と $`R^r` の像が $`R[1/g]^r` の中で生成する部分環 \`trivialCoverComparison\`（:58）。これは $`R` 上有限（\`trivialCoverComparison\_finite\`、:111）、$`S` と $`R^r` の両方から整（\`trivialCoverComparison\_integral\`、:130）、$`g` を反転すると両方からの射が同型（\`trivialCoverComparison\_localization\_iso\`、:156）、$`R` が perfectoid なら導来 $`p` 完備（\`trivialCoverComparison\_isModuleComplete\`、:253。有限個の分母を払い、完備加群からの全射と完備加群への単射で挟む）。

導来 perfectoid 化を使う組み立ては drafts にある：結論の $`J`-almost 連結性 \`perfectoidization\_almostConnective\_of\_finiteEtaleAway\`（drafts/A8/AlmostPurityConnectivity:214）、絶対整閉な基底への帰着 \`almostConnective\_of\_aic\_baseChange\`（:94）、生成元の細分 \`exists\_principal\_splitting\_cover\`（:107）。

*定理 10.2.1（原典 Thm 10.9） — 証明*

\*\*$`J`-almost 版.\*\* まず次の (∗) を示す：$`S_{\mathrm{perfd}}` は $`J`-almost 連結（$`i>0` で $`J_{\mathrm{perfd}}H^i(S_{\mathrm{perfd}})=0`）、$`S\to S_{\mathrm{perfd}}` は $`V(J)` の外で同型、各 $`n>0` で $`R/p^n\to H^0(S_{\mathrm{perfd}})/p^n` は $`(R/p^n,J_{\mathrm{perfd},n})` に関して almost 有限射影かつ almost 不分岐、$`G` 作用があれば $`R\to H^0(S_{\mathrm{perfd}})` は $`J`-almost $`G`-Galois 被覆。

(0) 置き換えの原理。$`S'` が $`S` 上整な $`S` 代数で、$`\mathrm{Spec}(S')\to\mathrm{Spec}(S)` が $`V(J)` の外で同型なら、Cor 8.12 により $`S_{\mathrm{perfd}}\to S'_{\mathrm{perfd}}` は $`J`-almost 同型。（補った）Cor 8.12 の引き戻しの四角形から、$`S_{\mathrm{perfd}}\to S'_{\mathrm{perfd}}` のファイバーは $`(S/JS)_{\mathrm{perfd}}\to(S'/JS')_{\mathrm{perfd}}` のファイバーに等しく、後者は $`(R/J)_{\mathrm{perfd}}` 加群の複体なので Prop 10.4 により $`J`-almost 零。特に $`S_{\mathrm{perfd}}` は、$`\mathrm{Spec}(R)\setminus V(J)` 上の与えられた有限エタール被覆を誘導する $`S` の選び方に、$`J`-almost 同型を除いて依らない。

(1) Galois の場合。$`S` に $`G` が作用し $`V(J)` の外で $`G`-Galois とする。Thm 7.14 により $`R` を絶対整閉としてよい（補った：$`R\to R'` が $`p` 完全忠実平坦なら、$`J`-almost 零性は $`R'` への完備底変換で判定でき、Prop 8.13 で $`(S\widehat\otimes_RR')_{\mathrm{perfd}}=S_{\mathrm{perfd}}\widehat\otimes_RR'`）。絶対整閉な環では、任意の Zariski 局所化上の有限エタール被覆は Zariski 局所的に分裂するので、$`J` の生成元 $`f_1,\dots,f_r` を取り直して、各 $`i` で $`V(f_i)` の外で $`\mathrm{Spec}(S)\to\mathrm{Spec}(R)` が分裂するようにできる。$`J`-almost 同型 ⇔ 全ての $`i` で $`(f_i)`-almost 同型なので、$`J=(f)` が主イデアルで $`\mathrm{Spec}(S)\to\mathrm{Spec}(R)` が $`\mathrm{Spec}(R)[1/f]` 上で分裂する場合に帰着する。ここで生成元は取り直しているので、元が $`J=(p)` のような主イデアルでも一般の元が要る（原典の脚注 18）。すると (0) により $`S` を自明な $`G`-torsor $`\prod_GR` に置き換えてよく、そこでは主張は明らか（$`\prod_GR` はすでに perfectoid）。

(2) 次数一定の場合。$`V(J)` の外で $`\mathrm{Spec}(S)\to\mathrm{Spec}(R)` の次数が $`r` で一定なら、$`X\setminus V(J)` 上の $`\Sigma_r`-Galois 拡大で、$`\mathrm{Spec}(S)\setminus V(J)` がその $`\Sigma_{r-1}` による商になるものがある（\[And18b, Lemma 1.9.2\]）。Prop 10.8 により Galois の場合に帰着する。

(3) 一般の場合。次数が一定になる開かつ閉な分解 $`\mathrm{Spec}(R)\setminus V(J)=\bigsqcup_{i=1}^nU_i` を取り、$`R_i` を $`R` の $`H^0(U_i,\mathcal O)` での像とする。$`R\to\prod_i(R_i)_{\mathrm{perfd}}` は Cor 8.12 の仮定を満たす：$`J` を殺さない $`R\to V` は $`\mathrm{Spec}(V)\to\mathrm{Spec}(R)\setminus V(J)` を与え、ちょうど一つの $`U_i` を経由して $`R_i\to V` を誘導し、これは $`(R_i)_{\mathrm{perfd}}` へ一意に延びる。よって $`R` を $`(R_i)_{\mathrm{perfd}}` に替えて次数一定の場合に帰着する。

*完全な形.* $`S` は $`R` 上有限なので整で、Thm 10.11（定理 10.2.3）により $`S_{\mathrm{perfd}}` は離散で perfectoid。すると $`H^0(S_{\mathrm{perfd}})=S_{\mathrm{perfd}}` で、(∗) がそのまま定理の主張になる（補った）。

*定理 10.2.1（原典 Thm 10.9） — 原典との差（D63）*

Lean は結論を $`J`-almost 連結性だけに限り、原典の (0)(1) の議論で示す。Galois 作用は使わない：絶対整閉な基底では任意の有限エタール被覆が Zariski 局所的に分裂するので、(1) の議論が Galois でない $`S` にもそのまま通り、比較環 \`trivialCoverComparison\` に Cor 8.12 を $`S` と $`R^r` の両方から当てれば $`S_{\mathrm{perfd}}` と $`(R^r)_{\mathrm{perfd}}=R^r` が $`(f)`-almost 同型になる。(2)(3) は使わない。

宣言：`SerrePositivity.BhattScholze.Almost.isAlmostZero_iff_forall_gen`、`SerrePositivity.BhattScholze.Almost.trivialCoverComparison_localization_iso`

:::

:::proposition "bs_10_10"
*注意 10.10*　注意。対応表の状態：なし。

証明手法の説明であり、独立した対応数学的宣言は未同定。

*注意 10.2.2（原典 Rem 10.10） — 主張*

Thm 10.9 の証明は、特に almost purity 定理の新しい証明を与える。この議論は adic 空間（特に perfectoid 空間）を一切使わない。

*注意 10.2.2（原典 Rem 10.10） — Lean*

本体にない（数学的な注意で、形式化する主張はない）。

*注意 10.2.2（原典 Rem 10.10） — 証明*

証明の入力は、$`S\mapsto S_{\mathrm{perfd}}` の arc 降下（Cor 8.12、その元の Prop 8.10 は完全スキームの v 降下と arc 降下の判定から）と André の補題（Thm 7.14、絶対整閉な perfectoid 環への忠実平坦な拡大）だけで、どちらも環とその perfectoid 化の言葉で述べられ、adic 空間を経由しない。

:::

:::theorem "bs_10_11" (lean := "SerrePositivity.BhattScholze.PerfectoidizationInterface.PerfectoidizationInterfaceE3, SerrePositivity.BhattScholze.Inputs.exists_perfectoidizationInterfaceE3, SerrePositivity.BhattScholze.Inputs.exists_perfectoidization_of_integral")
*定理 10.11*　整代数の perfectoid 化は離散で perfectoid。対応表の状態：未証明の入力に依存。

*主張*　完全 prism $`(A,I)` に対応する perfectoid 環 $`R` からの射 $`R\to S` が整射の $`p` 完備化なら、$`\Delta_{S/A,\mathrm{perf}}` は離散な完全 $`p` 完備 $`\delta` $`A` 代数である。従って $`S_{\mathrm{perfd}}` は離散で perfectoid 環になる。

E3 存在 sorry の integral 欄と universal 欄から、通常の整 R-代数の perfd の離散性・perfectoid 性・普遍環の存在を受け取る。Δ\_S/A,perf 自体の δ 構造・perfect 性との具体的比較は drafts。近似・余極限の部品だけを本項の証明としない。

*定理 10.2.3（原典 Thm 10.11） — 主張*

$`R` を perfect prism $`(A,I)` に対応する perfectoid 環とし、$`R\to S` を整写像の $`p` 完備化とする。このとき $`\Delta_{S/A,\mathrm{perf}}` は離散で、完全な $`p` 完備 δ-$`A` 代数である。したがって $`S_{\mathrm{perfd}}` は離散で perfectoid 環である。

*定理 10.2.3（原典 Thm 10.11） — Lean*

E3 の界面の欄 \`integral\`（Interface:688）として受け取る。欄の形は、任意の整 $`R` 代数 $`S`（非完備も含む）について「$`S_{\mathrm{perfd}}` は離散 ∧ $`H^0` は perfectoid」で、$`\Delta_{S/A,\mathrm{perf}}` についての部分は欄にない。欄から証明済みの環の帰結：整代数の perfectoid 化の存在 \`exists\_perfectoidization\_of\_integral\`（IntegralExistence:422、界面を引数に取る版。界面の存在から出す版は :467）、有限代数版 \`exists\_perfectoidization\_of\_finite\`（:491）。

証明の部品（本体）：

- filtered 余極限への帰着：整 $`R` 代数 $`S` は、$`S` へ向かう有限表示有限 $`R` 代数の小さい filtered 図式の余極限（\`integral\_isFilteredColimit\_finitePresentation\`（IntegralApproximation:275）。有限個の変数と関係に、各変数のモニック関係を足した段を取る）。perfectoid 環の filtered 図式の余極限は、$`p` 冪ねじれが $`p` で消え、導来 $`p` 完備化が離散な perfectoid 環（\`isIntegralPerfectoid\_completedFilteredColimit\`（PerfectoidFilteredColimit:98））。

- 整閉包とその完備化：$`B=S_{\mathrm{red}}[1/g]`（\`reducedAway\`（IntegralClosureCompletion:61））の中の $`R` の整閉包 $`T`（\`integralClosureInLocalization\`、:72）について、$`S\to T` は整（\`integralClosureInLocalization\_integral\`、:101）、$`S\to T` と $`S\to\widehat T`（\`integralClosureCompletion\`、:168）は Cor 8.12 の条件 \`ArcOutside\`（Interface:645）を満たす（\`integralClosureInLocalization\_arcOutside\`・\`arcOutside\_completionRing\`、IntegralClosureCompletion:138・178）。$`R` が perfectoid で $`B` が $`R[1/g]` 上有限エタールなら、$`T` の $`p` 冪ねじれは有界で、$`\widehat T` は導来 $`p` 完備（\`integralClosureCompletion\_isModuleComplete\`、:232）。

- 局所化を固定した有限表示近似：$`T[1/g]\simeq B` で $`B` が $`R[1/g]` 上有限表示なら、$`T` は、$`g` を反転すると $`B` と全単射になる有限表示有限 $`R` 代数の filtered 余極限（\`exists\_finitePresentation\_approximation\_fixedLocalization\`（IntegralClosureApproximation:41）、図式の形は \`integral\_isFilteredColimit\_finitePresentation\_fixedLocalization\`（IntegralApproximation:436））。

- 層別と普遍同相：Lemma 10.12（命題 10.2.4）、および「完全環から被約環への普遍同相は同型」\`isUniversalHomeomorphism\_bijective\_of\_perfect\_reduced\`（UniversalHomeomorphism/Basic:528）。

組み立ては drafts/A8/IntegralDiscreteness にある：有限表示有限 $`S` の連結性 \`perfectoidization\_connective\_of\_finitePresentation\`（drafts/A8/IntegralDiscreteness:305）、帰納段の $`g_1`-almost 連結性 \`perfectoidization\_almostConnective\_of\_stratification\`（:297）、欄の形 \`e3Integral\`（:330）。

*定理 10.2.3（原典 Thm 10.11） — 証明*

*帰着.* filtered 余極限に移って、$`R\to S` は有限表示な有限射としてよい。（補った）整 $`S` は有限表示有限 $`R` 代数 $`S_\lambda` の filtered 余極限で、$`\Delta_{-/A,\mathrm{perf}}` と $`(-)_{\mathrm{perfd}}` は完備化を込めて filtered 余極限と可換、離散な perfectoid 環の filtered 余極限の完備化は離散な perfectoid 環。原典の脚注 19：このような $`S` は $`R` 加群として有限表示（$`R` 代数としての各生成元がモニック多項式を満たすので、代数としての有限表示から加群としての有限表示が直ちに出る）で、特にすでに $`p` 完備。Cor 8.14 により、$`S_{\mathrm{perfd}}` が連結であることを示せばよい（そのとき導来 Nakayama で $`\Delta_{S/A,\mathrm{perf}}` も離散で完全 δ 環になる）。

$`R` は $`p` 完備なので $`p` 以外の素数は可逆、すなわち $`\mathbb Z_{(p)}` 代数で（補った）、Lemma 10.12 の $`g_1,\dots,g_n` が取れる。$`S_{\mathrm{perfd}}` の連結性を $`n` に関する帰納法で示す。

\*\*$`n=1`.\*\* $`g_1` は単元で、$`R_1=R_{\mathrm{red}}=R`（perfectoid 環は被約）、$`S_1=S_{\mathrm{red}}`。Lemma 10.12 の条件から $`R\to S_{\mathrm{red}}` は有限エタールになる（補った：$`p` が単元なら $`R` は $`p` 完備なので零環。$`p=0` なら $`R` は完全 $`\mathbb F_p` 代数で、有限エタールな $`T_1` も完全、$`T_1\to S_{\mathrm{red}}` は完全環から被約環への普遍同相なので同型）。よって $`S_{\mathrm{red}}` は perfectoid。$`S\to S_{\mathrm{red}}` は arc 層化で同型なので、Cor 8.11 により $`S_{\mathrm{perfd}}\cong S_{\mathrm{red},\mathrm{perfd}}\cong S_{\mathrm{red}}` は離散。

\*\*$`n>1`.\*\* $`(R/g_1R)_{\mathrm{perfd}}\to S\otimes_R(R/g_1R)_{\mathrm{perfd}}` には長さ $`n-1` の層別（$`g_2,\dots,g_n` の像）があるので、帰納法の仮定と Prop 8.13 により $`(S/g_1S)_{\mathrm{perfd}}` は連結。Lemma 10.5（$`J=(g_1)`、$`S_{\mathrm{perfd}}\widehat\otimes^L_R(R/g_1)_{\mathrm{perfd}}=(S/g_1S)_{\mathrm{perfd}}`）により、$`S_{\mathrm{perfd}}` が $`g_1`-almost 連結であることを示せばよい。Lemma 10.12 の条件から

1. $`R[1/g_1]` で $`p=0` か $`p\in R[1/g_1]^\ast`。

2. $`R[1/g_1]\to S_{\mathrm{red}}[1/g_1]` は $`R[1/g_1]\to T_1\to S_{\mathrm{red}}[1/g_1]` と分解し、前半は有限エタール、後半は普遍同相。$`p\in R[1/g_1]^\ast` なら後半は同型。

$`T_1\to S_{\mathrm{red}}[1/g_1]` は常に同型である：(2) の最後の文により $`p=0` の場合だけ考えればよく、そのとき $`R[1/g_1]` は完全 $`\mathbb F_p` 代数、$`T_1` も完全で、完全環から被約環への普遍同相は同型。まとめると $`R[1/g_1]\to S[1/g_1]\to S_{\mathrm{red}}[1/g_1]` は有限エタール被覆。

$`S'` を $`S_{\mathrm{red}}[1/g_1]` の中の $`R` の整閉包とする。$`S` が $`R` 上有限なので $`S\to S'` は整 $`R` 代数の射で、$`(g_1)` の外で arc 層の同型（補った：$`g_1` を殺さない階数 1 の付値環 $`V` への $`S\to V` は $`S_{\mathrm{red}}[1/g_1]\to\mathrm{Frac}(V)` に一意に延び、$`S'` の像は $`V` 上整なので $`V` に入る）。Cor 8.12 により $`S_{\mathrm{perfd}}\to S'_{\mathrm{perfd}}` は $`g_1`-almost 同型なので、$`S'_{\mathrm{perfd}}` の $`g_1`-almost 連結性を示せばよい。$`S'` を、$`g_1` を反転すると与えられた有限エタール被覆 $`R[1/g_1]\to S_{\mathrm{red}}[1/g_1]` を誘導する有限表示有限 $`R` 代数 $`A_\lambda` で近似すると、各 $`(A_\lambda)_{\mathrm{perfd}}` は Thm 10.9 の $`J`-almost 版（$`J=(g_1)`）で $`g_1`-almost 連結。almost 連結性は完備な filtered 余極限で保たれるので（補った）、$`S'_{\mathrm{perfd}}` も $`g_1`-almost 連結。

*定理 10.2.3（原典 Thm 10.11） — 原典との差（D70・D64・D67）*

原典は整閉包 $`S'` に Cor 8.12 を直接当てるが、Cor 8.12 は導来 $`p` 完備な環を要求し、$`S'`（Lean の $`T`）は導来 $`p` 完備とは限らない（perfectoid な値域をもつ収束列の環での反例を drafts に記録：\`integralClosure\_not\_complete\_counterexample\`（drafts/A8/IntegralDiscreteness:224））。Lean は Cor 8.12 を $`S\to\widehat T` に当てる。$`n=1` の $`S_{\mathrm{perfd}}\cong S_{\mathrm{red},\mathrm{perfd}}` は Cor 8.11 の arc 層化ではなく、perfectoid 環が被約であることと Prop 8.5 の極限の形から出す（D64、内容は同じ）。E3 の欄は任意の整 $`S` について、$`S^\wedge` を経由して述べる（D67・D41）。

:::

:::lemma_ "bs_10_12" (lean := "SerrePositivity.CommutativeAlgebra.exists_finiteEtaleStratification, SerrePositivity.CommutativeAlgebra.exists_noetherian_finiteEtaleStratification")
*補題 10.12*　有限表示有限射の層別。対応表の状態：本体にある。

*主張*　有限かつ有限表示の可換 $`\mathbf Z_{(p)}` 代数射 $`R\to S` に対し、$`1` を生成する列 $`g_i\in R` を選び、先行元で割って被約化してから $`g_i` を反転した層 $`R_i,S_i` をとる。各 $`R_i\to S_i` は有限エタール射 $`R_i\to T_i` と普遍的同相射を誘導する $`T_i\to S_i` に分かれ、後者は $`p` を反転すると同型である。各 $`R_i` では $`p=0` または $`p` が単元である。

同じ有限表示有限 Z\_(p)-代数射に、有限個の g\_i・unit ideal・各 reduced stratum の finite étale/universal homeomorphism 分解・p 反転後同型・p=0又は単元という三結論を与える。root import 閉包内かどうかとは別の宣言の数学的対応。

*命題 10.2.4（原典 Lemma 10.12） — 主張*

$`R\to S` を可換 $`\mathbb Z_{(p)}` 代数の有限表示な有限射とする。このとき元の列 $`g_1,\dots,g_n\in R` で、$`R_i=R/(g_1,\dots,g_{i-1})_{\mathrm{red}}[1/g_i]`、$`S_i=S/(g_1,\dots,g_{i-1})_{\mathrm{red}}[1/g_i]`（$`i=1,\dots,n`）とおくと次を満たすものが存在する。

1. $`(g_1,\dots,g_n)` は $`R` の単位イデアル。同値に $`\bigcup_i\mathrm{Spec}(R_i)=\mathrm{Spec}(R)`。

2. $`R_i\to S_i` は $`R_i\to T_i\to S_i` と分解し、$`R_i\to T_i` は有限エタール、$`T_i\to S_i` は普遍同相。さらに $`T_i[1/p]\to S_i[1/p]` は同型。

3. 各 $`R_i` で $`p=0` か $`p\in R_i^\ast`。

大まかに言えば、qcqs スキームの有限表示有限射は、普遍同相を除いて、目標の構成可能な層別の上で有限エタールになる。

*命題 10.2.4（原典 Lemma 10.12） — Lean*

\`exists\_finiteEtaleStratification\`（Stratification:374）。原典どおりで、$`\mathbb Z_{(p)}` 代数であることを「$`p` 以外の素数 $`q` は $`R` で可逆」として仮定する（D65、差なし）。層は \`StratumRing\`（Factorization:33）、層の間の射は \`stratumMap\`（:66）、$`g_1,\dots,g_{i-1}` の生成するイデアルは \`earlierIdeal\`（NoetherianInduction:29）。(2) の分解は述語 \`HasEtaleFactorization\`（Factorization:112。「有限エタール射と普遍同相の合成で、$`p` を反転すると後者は全単射」）。noetherian な場合 \`exists\_noetherian\_finiteEtaleStratification\`（Stratification:331）。層の底変換 \`hasEtaleFactorization\_stratum\_baseChange\`（StratumBaseChange:178）。

普遍同相 \`IsUniversalHomeomorphism\`（UniversalHomeomorphism/Basic:45）は、整・Spec で全射・radicial（Spec で単射で、剰余体の拡大が純非分離）で定義する。標数 $`p` では「核の各元が冪零で、$`B` の各元のある $`p` 冪が像に入る」と同値（\`isUniversalHomeomorphism\_iff\_charP\`、:502）。ここで「核が冪零」は各元が冪零（核が冪零根基に含まれる）の意味で、イデアルとしての冪零性ではない。

*命題 10.2.4（原典 Lemma 10.12） — 証明*

(1)(2) を満たす $`g_1,\dots,g_n` を見つければよい：そのあと必要なら層をさらに細分して (3) も満たせる。具体的には $`(g_1,\dots,g_n)` を $`(pg_1,g_1,pg_2,g_2,\dots,pg_n,g_n)` に替える（補った：$`pg_i` の層では $`p` が可逆、その次の $`g_i` の層では $`pg_i` を割ってあるので $`p=0`）。

(1)(2) について。noetherian 近似により、$`R` は有限表示 $`\mathbb Z_{(p)}` 代数としてよい。$`\mathfrak p_1,\dots,\mathfrak p_r` を $`R` の極小素イデアル、$`K=\prod_iK_i` を対応する剰余体の積（$`R_{\mathrm{red}}` の全商環）とする。$`R\to S` は有限なので、$`K\to(S\otimes_RK)_{\mathrm{red}}` は $`K_i\to L_i`、$`L_i=(S\otimes_RK_i)_{\mathrm{red}}` の積で、各 $`L_i` は有限被約 $`K_i` 代数、すなわち $`K_i` の有限次拡大体の有限積。よって $`K_i\to L_i` は $`K_i\to M_i\to L_i` と分解し、前半は有限エタール、後半は普遍同相で、$`K_i` で $`p` が可逆なら同型（補った：$`M_i` は各成分の分離閉包。$`\mathbb Z_{(p)}` 代数なので $`K_i` の標数は $`0` か $`p` で、標数 $`0` なら $`M_i=L_i`）。近似の議論で、$`K` で可逆な $`g_1\in R` を取って $`R_{\mathrm{red}}[1/g_1]\to S_{\mathrm{red}}[1/g_1]` が (2) の形になるようにできる。これが開いた層で、残りは $`R/(g_1)\to S/(g_1)` への noetherian 帰納法から出る。

（補った）$`\mathbb Z_{(p)}` の仮定は外せない：$`q\ne p` のとき $`K=\mathbb F_q(t)\to K(t^{1/q})` は有限表示有限な純非分離拡大で、非空の層では $`p` が可逆なので (2) は $`T_i\to S_i` が同型、つまり有限エタールを要求し、矛盾する。

:::

:::proposition "bs_10_13"
*注意 10.13*　可換環論への応用。対応表の状態：なし。

同じ完備正則局所環の R⁺ と Tor の c-almost 消滅を結ぶ HM17 応用の宣言を未同定。

*注意 10.2.5（原典 Rem 10.13） — 主張*

Thm 10.9 を使うと、可換環論の既知の結果のいくつかを比較的すばやく示し直せる。例えば \[HM17\] の主定理はほぼ直ちに従う。\[HM17, Theorem 1.3\]：混標数の完備正則局所環 $`R` と、固定した絶対整閉包 $`R\to R^+` に含まれる有限拡大 $`R\to S` を取り、$`n>0` を固定する。ある $`c\in R` があって、全ての $`i>0` で自然変換

$$`\mathrm{Tor}_i^{R/p^n}(S/p^n,-)\to\mathrm{Tor}_i^{R/p^n}(R^+/p^n,-)`

が $`c`-almost 零、すなわち像が $`R^+` の中の全ての $`p` 冪根 $`c^{1/p^n}` で消える。実際、$`R[1/c]\to S[1/c]` が有限エタールとなる任意の $`c\in pR` でよい。

*注意 10.2.5（原典 Rem 10.13） — Lean*

本体にない（応用の注意で、形式化していない）。

*注意 10.2.5（原典 Rem 10.13） — 証明*

$`R^+` の $`p` 進完備化に含まれる忠実平坦な拡大 $`R\to R_\infty` で $`R_\infty` が perfectoid なものを取る（Rem 3.11）。$`T=S\otimes_RR_\infty` とおくと、有限射 $`R_\infty\to T` は $`c` を反転すると有限エタール。Thm 10.9 により $`R_\infty\to T_{\mathrm{perfd}}` は $`c`-almost 有限エタール。$`R\to R_\infty` が忠実平坦なので、$`i>0` で関手 $`\mathrm{Tor}_i^{R/p^n}(T_{\mathrm{perfd}}/p^n,-)` は $`c`-almost 零（$`(cT_{\mathrm{perfd}})_{\mathrm{perfd}}` で消える）。ここで $`c\in pR` であることと、$`T_{\mathrm{perfd}}` の $`p` ねじれが $`p`-almost 零（したがって $`c`-almost 零）であることを暗に使う。一方 $`S/p^n\to R^+/p^n` は $`S/p^n\to T/p^n\to T_{\mathrm{perfd}}/p^n\to R^+/p^n` と分解する（最後の射は、$`R^+` の $`p` 進完備化が perfectoid なので perfectoid 化の普遍性から）。よって

$$`\mathrm{Tor}_i^{R/p^n}(S/p^n,-)\to\mathrm{Tor}_i^{R/p^n}(T_{\mathrm{perfd}}/p^n,-)\to\mathrm{Tor}_i^{R/p^n}(R^+/p^n,-)`

と分解し、中央が $`i>0` で $`c`-almost 零なので主張が従う。

:::

