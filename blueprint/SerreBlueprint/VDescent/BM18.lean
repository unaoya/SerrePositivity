import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.AlgebraicGeometry.AffineVCover
import SerrePositivity.AlgebraicGeometry.ArcRouteB.AicValuationArc
import SerrePositivity.AlgebraicGeometry.ArcRouteB.ArcCoverCech
import SerrePositivity.AlgebraicGeometry.ArcRouteB.CoverLaws
import SerrePositivity.AlgebraicGeometry.ArcRouteB.Definitions
import SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalSpectrum
import SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalTensorComparison
import SerrePositivity.AlgebraicGeometry.ArcRouteB.OverlapShortExact
import SerrePositivity.AlgebraicGeometry.ArcRouteB.UniversalCech
import SerrePositivity.AlgebraicGeometry.ArcRouteB.UniversalUltraproduct
import SerrePositivity.AlgebraicGeometry.SchemeVCover
import SerrePositivity.BhattScholze.Perfectoidization.Arc.Valuations.ArcValuationMilnor
import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosed.Basic
import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosed.Etale
import SerrePositivity.CommutativeAlgebra.Ultraproduct.Basic
import SerrePositivity.CommutativeAlgebra.Ultraproduct.Localization
import SerrePositivity.CommutativeAlgebra.ValuationExtension.Aic
import SerrePositivity.CommutativeAlgebra.ValuationInterval.Basic
import SerrePositivity.CommutativeAlgebra.ValuationInterval.Zorn

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "BM18（Bhatt–Mathew, The arc-topology, arXiv 1807.04725v4）" =>
%%%
number := false
tag := "vdescent-bm18"
%%%

BM18 の項目のうち、この経路で本体か Mathlib に対応があるもの。

# §1 Introduction

%%%
number := false
tag := "vdescent-bm18-1"
%%%

:::definition "bm18_1_1" (lean := "SerrePositivity.AlgebraicGeometry.IsSchemeVCover, SerrePositivity.AlgebraicGeometry.IsAffineVCoverFamily")
*BM18 定義 1.1*　v 位相と v 被覆。対応表の状態：一部（component）。

*主張*　qcqs スキームの射 $`Y\to X` が v 被覆であるとは、任意の付値環 $`V` からの点 $`\operatorname{Spec}V\to X` が、付値環の忠実平坦拡大 $`V\to W` の後に $`Y` に持ち上がることをいう。全スキーム上の v 位相では、標的の各アフィン開上で被覆族の有限個のアフィン開を選び、その非交和からの射がこの条件を満たすことを求める。

原典 PDF p.2, y=447.9。忠実平坦な付値環拡大によるスキームの射の v 被覆判定と、アフィン有限族の定義を持つ。全スキーム上の Grothendieck 位相の被覆族までの定義は見出していない。

外の文献：RydhII、VHomology

:::

:::definition "bm18_eq_1" (lean := "SerrePositivity.AlgebraicGeometry.IsSchemeVCover")
*BM18 式 (1)*　v 被覆の付値持ち上げ。対応表の状態：一部（special）。

*主張*　付値環の拡大 $`V\to W` で $`\operatorname{Spec}V\to X` を引き戻すと、$`\operatorname{Spec}W\to Y` が存在し、$`Y\to X` と合成した射が引き戻しで得た点に一致する。これが v 被覆の持ち上げ条件を表す可換四角形である。

原典 PDF p.2, y=513.6。一射の v 被覆に対する付値環拡大と持ち上げの可換性を合成等式で表している。

:::

:::definition "bm18_1_2" (lean := "SerrePositivity.AlgebraicGeometry.ArcRouteB.IsArcHom, SerrePositivity.AlgebraicGeometry.ArcRouteB.IsArcCoverFamilyCharP, SerrePositivity.AlgebraicGeometry.ArcRouteB.isArcHom_pi_iff")
*BM18 定義 1.2*　arc 位相と arc 被覆。対応表の状態：一部（special）。

*主張*　qcqs スキームの射が arc 被覆であるとは、階数 1 以下の付値環から標的への点が、階数 1 以下の付値環への忠実平坦拡大の後に源へ持ち上がることをいう。全スキーム上の arc 位相では、標的の各アフィン開上で被覆族の有限個のアフィン開を選び、その非交和からの射がこの条件を満たすことを求める。

原典 PDF p.3, y=125.2。アフィンの射と有限アフィン族を rank ≤ 1 の付値環で判定する。一般の qcqs スキームの射および全スキーム上の arc 位相は型に含まれない。

外の文献：Pic、Rydh、RydhII

:::

# §2 The arc-topology

%%%
number := false
tag := "vdescent-bm18-2"
%%%

:::lemma_ "bm18_2_3" (lean := "SerrePositivity.AlgebraicGeometry.ArcRouteB.isArcHom_of_refinement") (uses := "bm18_1_2")
*BM18 補題 2.3*　合成の arc 被覆性からの反映。対応表の状態：一部（special）。

*主張*　qcqs スキームの射 $`Z\xrightarrow{g}Y\xrightarrow{f}X` の合成が arc 被覆なら、$`f` も arc 被覆である。

原典 PDF p.9, y=551.8。合成が arc 被覆なら後段も arc 被覆になる。環の射で記述したアフィンの場合。

:::

:::proposition "bm18_2_8" (lean := "SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationRing_milnorSquare")
*BM18 命題 2.8*　付値環の excision datum。対応表の状態：一部（component）。

*主張*　付値環 $`V` の素イデアル $`\mathfrak p\subseteq\mathfrak q` に対し、$`(V_{\mathfrak q},\mathfrak pV_{\mathfrak q})\to(V_{\mathfrak p},\mathfrak pV_{\mathfrak p})` は切除データをなす。特に $`(V,\mathfrak p)\to(V_{\mathfrak p},\mathfrak pV_{\mathfrak p})` に適用できる。

原典 PDF p.10, y=516.4。q が極大の場合の V、V\_p、V/p、κ(p) の加法群の短完全列から、局所化が素イデアル p を像のイデアルに同型に移すことが従う。一般の q での述語として excision datum を返す型は見出していない。

:::

:::definition "bm18_2_12"
*BM18 定義 2.12*　submersion の定義。対応表の状態：Mathlib にある。

*主張*　qcqs スキームの射が submersive であるとは、台の位相空間上で全射であり、標的が商位相を持つことをいう。任意の qcqs スキームによる底変換後もそうであるとき、普遍的に submersive という。

原典 PDF p.11, y=431.9。スキームの台位相写像に IsQuotientMap を課し、普遍版はすべての引き戻しで同じ性質を課す。原典の qcqs の範囲に制限して一致する。

宣言：`Topology.IsQuotientMap`、`AlgebraicGeometry.topologically`、`CategoryTheory.MorphismProperty.universally`

:::

:::lemma_ "bm18_2_21" (lean := "SerrePositivity.valuationSubringComapHom_faithfullyFlat") (uses := "rydh_2_6")
*BM18 補題 2.21*　部分体に引き戻した付値環。対応表の状態：本体にある。

*主張*　付値環 $`W` の分数体の部分体を $`K_0` とすると、$`W_0=W\cap K_0` は付値環で $`W_0\to W` は忠実平坦である。$`K_0` が代数閉体なら、$`W_0` は絶対整閉である。

原典 PDF p.14, y=288.5。分数体への部分体の包含を体の単射として扱い、付値部分環の逆像から元の付値環への射の忠実平坦性を与える。逆像は ValuationSubring として型付けされる。

:::

# §3 Studying v-sheaves via valuation rings

%%%
number := false
tag := "vdescent-bm18-3"
%%%

:::definition "bm18_3_2" (lean := "SerrePositivity.AlgebraicGeometry.ArcRouteB.PerfectRingCechUniversalExact, SerrePositivity.AlgebraicGeometry.ArcRouteB.perfectRingCechUniversalExact_baseChange")
*BM18 定義 3.2*　普遍 F 降下。対応表の状態：一部（special）。

*主張*　小さい極限をもつ $`\infty` 圏に値をとる qcqs $`R` スキーム上の前層 $`F` に対し、$`Y\to X` が $`F` 降下を満たすとは、$`F(X)` から Čech 図式に $`F` を適用して得る全化への比較射が同値であることをいう。任意の qcqs $`R` スキームからの底変換後にも成り立てば普遍的 $`F` 降下という。

原典 PDF p.16, y=428.4。完全なアフィン係数へのすべての底変換後の構造層の増大 Čech 完全性として記述する。任意の F の値の ∞ 圏的比較写像を定義するものではない。

:::

:::lemma_ "bm18_3_4" (lean := "SerrePositivity.AlgebraicGeometry.ArcRouteB.perfectRingCechUniversalExact_baseChange")
*BM18 補題 3.4*　普遍降下の切断・合成・反映・底変換。対応表の状態：一部（special）。

*主張*　小さい極限をもつ $`\infty` 圏に値をとる qcqs $`R` スキーム上の前層 $`F` に対し、切断をもつ射は普遍的 $`F` 降下を満たし、そのような射は合成と底変換で閉じる。合成 $`f\circ g` が普遍的 $`F` 降下を満たすなら、$`f` も満たす。

原典 PDF p.16, y=602.4。結論 (4) の完全アフィン係数・構造層の場合。任意の F の普遍降下の合成・反映・切断の全項目を述べる型はない。

外の文献：EHIK

:::

:::definition "bm18_3_13"
*BM18 構成 3.13*　Stone–Čech コンパクト化。対応表の状態：一部（component）。

*主張*　離散集合 $`T` の Stone–Čech コンパクト化 $`\beta T` は $`T` 上の超フィルター全体からなる副有限空間で、主超フィルターは $`T` の稠密開埋め込みを与える。$`\beta T` の開閉集合は $`T` の部分集合と対応し、その開閉集合上の層の超フィルター $`\mathcal U` における茎は $`\mathcal U` に属する部分集合に沿ったフィルター余極限で計算できる。

原典 PDF p.19, y=325.1。離散空間の Stone–Čech コンパクト化を与える。原典の超フィルターでの表示は、この二つの宣言の型に現れない。

宣言：`StoneCech`、`stoneCechUnit`

外の文献：GJ60

:::

:::definition "bm18_3_15" (lean := "SerrePositivity.RingUltraproduct, SerrePositivity.isLocalization_ringUltraproduct")
*BM18 定義 3.15*　環の超積。対応表の状態：本体にある。

*主張*　$`R` 代数の族 $`(A_t)_{t\in T}` と $`T` 上の超フィルター $`\mathcal U` に対し、超積は $`\mathcal U` に属する部分集合 $`T'` 上の積 $`\prod_{t\in T'}A_t` を制限射で結んだフィルター余極限と定める。

原典 PDF p.20, y=96.3。超フィルター上ほとんど至る所で零となる元による商。指示冪等元による局所化としても得られ、超フィルター集合上の部分積の filtered 余極限と同じ環の超積を表す。

:::

:::lemma_ "bm18_3_25" (lean := "SerrePositivity.AlgebraicGeometry.ArcRouteB.perfectRingCechUniversalExact_of_ultraproducts, SerrePositivity.isLocalization_ringUltraproduct") (uses := "bm18_3_15, bm18_3_2")
*BM18 補題 3.25*　超積による普遍降下の検出。対応表の状態：一部（special）。

*主張*　余切断対象でコンパクト生成される $`\infty` 圏 $`\mathcal C` に値をとり、有限積を保つ finitary 関手 $`F\colon\operatorname{Ring}_R\to\mathcal C` をとる。任意の $`R` 代数族 $`(A_t)_{t\in T}` について、積 $`\prod_{t\in T}A_t` から各超フィルターに対応する超積への射の族は、普遍的 $`F` 降下を検出する。

原典 PDF p.22, y=96.3。超積全部のテストから積上の完全構造層の普遍 Čech 完全性を得る。任意の finitary F の普遍降下の検出を述べる型はない。

:::

:::definition "bm18_3_26" (lean := "SerrePositivity.IsAbsolutelyIntegrallyClosed, SerrePositivity.valuationSubring_aic")
*BM18 定義 3.26*　絶対整閉環。対応表の状態：本体にある。

*主張*　環が絶対整閉であるとは、その環上のモニック多項式がすべて環内に根を持つことをいう。整域の場合は正規で分数体が代数閉であることと同値で、絶対整閉整域は局所化と素イデアルによる剰余で保たれる。

原典 PDF p.22, y=314.1。正次数のモニック多項式が根を持つ条件を定める。代数閉体内の付値部分環の絶対整閉性も与える。

:::

:::lemma_ "bm18_3_27" (lean := "SerrePositivity.valuationRing_ultraproduct, SerrePositivity.aic_ultraproduct") (uses := "bm18_3_15, bm18_3_26")
*BM18 補題 3.27*　絶対整閉付値環の超積。対応表の状態：本体にある。

*主張*　絶対整閉付値環の超積は絶対整閉付値環である。

原典 PDF p.22, y=396.5。付値環の超積の付値環性と、絶対整閉整域の超積の絶対整閉性を合わせて結論が従う。

外の文献：BS17、CKmodel、GabberKelly、GooLi

:::

:::lemma_ "bm18_3_28" (lean := "SerrePositivity.exists_valuationSubring_algebraicClosure, SerrePositivity.valuationSubring_aic") (uses := "rydh_2_6")
*BM18 補題 3.28*　絶対整閉付値環への忠実平坦拡大。対応表の状態：本体にある。

*主張*　任意の付値環は絶対整閉付値環への忠実平坦な拡大をもつ。

原典 PDF p.22, y=568.6。分数体の代数閉包内への付値環の忠実平坦な拡大が存在する。代数閉体内の付値部分環なので絶対整閉性も得る。

:::

:::lemma_ "bm18_3_29" (lean := "SerrePositivity.valuationSubringComapHom_faithfullyFlat") (uses := "rydh_2_6")
*BM18 補題 3.29*　濃度を制限した絶対整閉付値部分環。対応表の状態：一部（component）。

*主張*　可換環 $`A` と絶対整閉付値環 $`W` への射 $`A\to W` に対し、$`A\to W'\to W` と分解できる。ここで $`W'` は濃度 $`\max(|A|,\aleph_0)` 以下の絶対整閉付値環で、$`W'\to W` は忠実平坦である。

原典 PDF p.23, y=96.3。原典の W と部分体の共通部分から W への忠実平坦性はある。濃度を制御した部分体の選択と A-代数としての因子分解の存在はこの型に含まれない。

:::

# §4 The main result for arc-descent

%%%
number := false
tag := "vdescent-bm18-4"
%%%

:::lemma_ "bm18_4_4" (lean := "SerrePositivity.AlgebraicGeometry.ArcRouteB.overlapTensorModuleComplex_shortExact") (uses := "bm18_4_6")
*BM18 補題 4.4*　aic-v-excision の代数への持ち上げ。対応表の状態：一部（special）。

*主張*　$`V` を絶対整閉付値環、$`A` を $`V` 代数とし、余切断対象でコンパクト生成される $`\infty` 圏に値をとる finitary v 層 $`F` が aic-v 切除を満たすとする。任意の素イデアル $`\mathfrak p\subset V` について、$`F(A)\to F(A\otimes_V V_{\mathfrak p})\times_{F(A\otimes_V\kappa(\mathfrak p))}F(A/\mathfrak p A)` は同値である。

原典 PDF p.26, y=403.4。完全標数 p の付値環と完全な係数 A では同一点の重なりの短完全列が、四つの環の加法群の引き戻しを与える。一般の V-代数や任意の finitary v-sheaf F は扱わない。

:::

:::definition "bm18_4_6" (lean := "SerrePositivity.ValuationIntervalRing, SerrePositivity.AlgebraicGeometry.ArcRouteB.intervalRingSpectrumOrderIso")
*BM18 定義 4.6*　付値環スペクトルの区間。対応表の状態：本体にある。

*主張*　絶対整閉付値環 $`V` の素イデアル $`\mathfrak p\subseteq\mathfrak q` に対し、区間 $`I=[\mathfrak p,\mathfrak q]` に絶対整閉付値環 $`V_I=(V/\mathfrak p)_{\mathfrak q}` を対応させる。区間の包含に対して反変で、区間の鎖には上限と下限があり、共通部分に対応する環は鎖の環のフィルター余極限である。

原典 PDF p.27, y=338.9。区間 \[p,q\] に (V/p)\_q を割り当て、その素スペクトルが同じ順序区間になる。

:::

:::lemma_ "bm18_4_7" (lean := "SerrePositivity.valuationIntervalProperty_of_localExtensions")
*BM18 補題 4.7*　局所延長と貼り合わせによる区間判定。対応表の状態：本体にある。

*主張*　付値環のスペクトルの区間の族が、一点または隣接する二点だけの区間をすべて含み、部分区間と重なる区間の和で閉じているとする。また極大点でない各点から右に、零素イデアルでない各点から左に、族に属する非自明な区間が延びるなら、この族はすべての区間を含む。

原典 PDF p.27, y=464.6。上下の局所延長、点、部分区間、重なりの貼り合わせから全区間を得る。原典の隣接点の条件は上下の延長条件から部分区間に制限して従う。

:::

:::proposition "bm18_4_8" (lean := "SerrePositivity.AlgebraicGeometry.ArcRouteB.aicValuationArc_universalExact, SerrePositivity.AlgebraicGeometry.ArcRouteB.cechExact_of_arcHom_perfect, SerrePositivity.AlgebraicGeometry.ArcRouteB.cech_exact_of_arcCover_perfect") (uses := "bm18_eq_6, bm18_1_2, bm18_2_21, bm18_2_3, bm18_3_15, bm18_3_2, bm18_3_25, bm18_3_26, bm18_3_27, bm18_3_28, bm18_3_29, bm18_4_4, bm18_4_6, bm18_4_7, bs17_3_1, bs17_4_1")
*BM18 命題 4.8*　【この部の目標】aic-v-excision から arc 降下。対応表の状態：一部（special）。

*主張*　$`\mathcal C` を余切断対象でコンパクト生成される $`\infty` 圏とする。qcqs $`R` スキーム上の $`\mathcal C` 値の finitary v 層が aic-v 切除を満たせば、それは arc 層である。

原典 PDF p.28, y=220.5。G-A6-1 の経路 B。絶対整閉付値環上で完全環への arc 被覆を任意の完全アフィン係数へ底変換した構造層の Čech 完全性を示し、最後に完全標数 p のアフィン射・有限族へ戻す。一般の qcqs 基底、cotruncated 対象でコンパクト生成された ∞ 圏値の任意の finitary v-sheaf、任意の aic-v-excisive F の arc-sheaf 性を与える型はない。

:::

:::definition "bm18_eq_6" (lean := "SerrePositivity.AlgebraicGeometry.ArcRouteB.overlapTensorModuleComplex_shortExact, SerrePositivity.AlgebraicGeometry.ArcRouteB.intervalTensorLocalizationEquiv, SerrePositivity.AlgebraicGeometry.ArcRouteB.intervalTensorQuotientEquiv, SerrePositivity.AlgebraicGeometry.ArcRouteB.intervalTensorIntersectionEquiv") (uses := "bm18_4_6")
*BM18 式 (6)*　重なる区間の比較正方形。対応表の状態：一部（special）。

*主張*　命題 4.8 の証明で、絶対整閉付値環 $`V` の全スペクトルを覆う重なり合う区間 $`I,J` をとると、任意の $`V` 代数 $`B` に対して $`F(B)\to F(B\otimes_V V_I)\times_{F(B\otimes_V V_{I\cap J})}F(B\otimes_V V_J)` が同値になるという引き戻し四角形である。

原典 PDF p.29, y=134.3。同じ端点の局所化・商・交差の係数を比較し、完全な係数で短完全列を得る。この列の核が図式の引き戻しを表す。一般の F に適用した図式ではない。

:::

# §5 Examples of arc-sheaves

%%%
number := false
tag := "vdescent-bm18-5"
%%%

:::lemma_ "bm18_5_3" (lean := "SerrePositivity.IsAbsolutelyIntegrallyClosed.henselianLocalRing, SerrePositivity.IsAbsolutelyIntegrallyClosed.residue_isAlgClosed") (uses := "bm18_3_26")
*BM18 補題 5.3*　絶対整閉付値環の狭義 Hensel 性。対応表の状態：本体にある。

*主張*　絶対整閉付値環は狭義ヘンゼル局所環である。

原典 PDF p.38, y=144.2。付値環の局所性を使い、絶対整閉局所環の Hensel 性と剰余体の代数閉性を合わせて狭義 Hensel 性を得る。

:::

:::theorem "bm18_5_17" (lean := "SerrePositivity.AlgebraicGeometry.ArcRouteB.cechExact_of_arcHom_perfect") (uses := "bm18_1_2, bm18_2_21, bm18_3_15, bm18_3_2, bm18_3_25, bm18_3_26, bm18_3_27, bm18_3_28, bm18_3_29, bs17_4_1")
*BM18 定理 5.17*　Universally effective epimorphisms of perfect schemes。対応表の状態：一部（special）。

*主張*　素数 $`p` と $`\mathbf F_p` 上の qcqs 代数空間 $`Y` に対し、qcqs $`\mathbf F_p` スキーム $`X` を $`X_{\mathrm{perf}}` から $`Y` への射の集合に送る前層は arc 層である。また qcqs 完全 $`\mathbf F_p` スキームの間の射が arc 被覆であることと、その圏で普遍的な有効エピ射であることは同値である。

原典 PDF p.45, y=190.6。完全アフィンの arc 被覆について、Čech 複体の次数零の完全性から環の等化子が得られ、アフィンな試験対象への射についての降下を与える。任意の qcqs 代数空間への射、ならびに普遍有効エピから arc 被覆への逆向きは含まない。

外の文献：B、RNoeth

:::

