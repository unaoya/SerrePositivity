import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.AlgebraicGeometry.AffineBaseProperInductiveLevel
import SerrePositivity.AlgebraicGeometry.ArcRouteB.FrobeniusPerfect
import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitInvariance
import SerrePositivity.AlgebraicGeometry.NoetherianProperInductiveLevel
import SerrePositivity.AlgebraicGeometry.PerfectAffineVCoverCech
import SerrePositivity.AlgebraicGeometry.PerfectCechUniversalAffineRefinement
import SerrePositivity.AlgebraicGeometry.PerfectFrobeniusCechComparison
import SerrePositivity.AlgebraicGeometry.PrimeFieldVCoverFilteredModel
import SerrePositivity.AlgebraicGeometry.ProperInductiveLevel
import SerrePositivity.AlgebraicGeometry.ProperInductiveLevelBaseChange
import SerrePositivity.AlgebraicGeometry.SchemeVCover
import SerrePositivity.AlgebraicGeometry.SchemeVCoverFlatSurjective
import SerrePositivity.AlgebraicGeometry.SchemeVCoverOpenCover
import SerrePositivity.AlgebraicGeometry.SchemeVCoverProper
import SerrePositivity.BhattScholze.Perfectoidization.Arc.Valuations.ArcValuationMilnor
import SerrePositivity.CommutativeAlgebra.PerfectTorIndependence.Basic
import SerrePositivity.CommutativeAlgebra.UniversalHomeomorphism.Basic

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "BS17（Bhatt–Scholze, Projectivity of the Witt vector affine Grassmannian, arXiv 1507.06490v3）" =>
%%%
number := false
tag := "vdescent-bs17"
%%%

目標は二つ。BS17 Theorem 4.1 (i)（完全スキームの上の v 降下、BS Proposition 8.10 が引用する）と、BM18 Proposition 4.8（aic-v 切除を満たす finitary v 層は arc 層）。本体は BS17 4.1 (i) のうち n = 1・E = O・アフィン・有限族の場合を作り、BM18 4.8 は構造層の場合を、その BS17 4.1 を入力にして作った（どちらも対応表では「一部」）。この部には、三つの文献の項目のうち、本体か Mathlib に対応があるものだけを載せる。辺は本体の経路（宣言どうしの参照、`research/bs17-coverage/route-edges.csv`）で、原典の引用の辺ではない。二つの目標から辺をたどって届かない項目は、本体に対応はあるが経路には使っていないもの。全項目の表は `research/bs17-coverage`・`bm18-coverage`・`rydh-coverage`。

# §2 h-Sheaves

%%%
number := false
tag := "vdescent-bs17-2"
%%%

:::definition "bs17_2_1" (lean := "SerrePositivity.AlgebraicGeometry.IsSchemeVCover")
*BS17 定義 2.1*　v 被覆と細分。対応表の状態：一部（component）。

*主張*　qcqs スキームの射が v 被覆（普遍的 subtrusive）であるとは、標的への任意の付値環のスペクトルからの射が、付値環の拡大を施せば源へ持ち上がることをいう。細分とは、元の射を経由する別の v 被覆のことである。

原典 PDF p.4, y=521.1。忠実平坦な付値環拡大による持ち上げの定義を持つ。項目中の細分の定義と、普遍 subtrusive・submersive との比較はこの宣言の結論に含まれない。

外の文献：Rydh 2.8、Rydh 2.9

:::

:::proposition "bs17_2_3" (lean := "SerrePositivity.AlgebraicGeometry.isSchemeVCover_of_flat_surjective, SerrePositivity.AlgebraicGeometry.isSchemeVCover_of_proper_surjective, SerrePositivity.AlgebraicGeometry.isSchemeVCover_sigmaDesc_openCover") (uses := "bm18_eq_1, bm18_1_1, bs17_2_1, rydh_2_6")
*BS17 例 2.3*　v 被覆の例。対応表の状態：一部（component）。

*主張*　qcqs スキームの間では、忠実平坦射・固有全射・Voevodsky の h 被覆はいずれも v 被覆である。全射だけでは十分でなく、原点を爆発したアフィン平面の例外曲線から一点を除いたものを平面へ写す射が反例となる。

原典 PDF p.5, y=136.6。平坦全射・固有全射・開被覆の各場合を与える。他の例や反例をまとめて示す型はない。

:::

:::definition "bs17_2_5" (lean := "SerrePositivity.AlgebraicGeometry.ProperInductiveLevel, SerrePositivity.AlgebraicGeometry.ProperInductiveLevel.baseChange")
*BS17 定義 2.5*　固有全射の帰納的レベル。対応表の状態：本体にある。

*主張*　qcqs スキーム間の有限表示な固有全射について、固有 fppf 射の後に有限表示な冪零閉埋め込みを置いた形へ細分できるとき、その帰納レベルを 0 とする。レベルが $`n>0` 以下という条件では、両者の間に、有限表示の閉部分スキームの外で同型となる有限表示な固有全射を挟み、その閉部分上への制限にレベル $`n-1` 以下を求める。この条件は底変換で保たれる。

原典 PDF p.5, y=423.6。レベル零の proper fppf 細分と有限表示 nilimmersion、後続段の中心・中心外同型・再帰・proper fppf 細分を表し、底変換で保存する。nilimmersion は有限表示な全射閉埋め込みで表す。

:::

:::lemma_ "bs17_2_6" (lean := "SerrePositivity.AlgebraicGeometry.exists_properInductiveLevel_affineBase, SerrePositivity.AlgebraicGeometry.exists_properInductiveLevel_noetherian") (uses := "bs17_2_5, rydh_3_3, rydh_3_5, rydh_3_6")
*BS17 補題 2.6*　有限の帰納的レベルの存在。対応表の状態：一部（special）。

*主張*　qcqs スキーム間の有限表示な固有全射には有限の帰納レベルがある。

原典 PDF p.5, y=565.8。有限表示固有全射が有限の帰納的レベルを持つ。基底がアフィン、または Noether の場合を与え、一般の qcqs 基底を一括する型はない。

外の文献：RG71、Rydh、Stacks 0815、TT

:::

:::lemma_ "bs17_2_10" (lean := "SerrePositivity.AlgebraicGeometry.perfectCechUniversalDescent_of_affine_refinement") (uses := "rydh_B_3")
*BS17 補題 2.10*　合成と普遍降下。対応表の状態：一部（special）。

*主張*　$`S` 上の有限表示スキーム間の合成 $`X\xrightarrow{f}Y\xrightarrow{g}Z` が普遍的 $`F` 降下を満たせば、$`g` も普遍的 $`F` 降下を満たす。$`f` が普遍的 $`F` 降下を満たし $`g` が $`F` 降下を満たせば合成は $`F` 降下を満たし、特に両者が普遍的 $`F` 降下を満たせば合成もそうである。

原典 PDF p.7, y=615.0。合成での普遍降下から後段へ移す (a) の構造層 Čech 版。元の射に分離・準コンパクト・局所有限表示、合成にアフィン性と局所有限表示を課す。一般の F と (b) の一般形を含まない。

外の文献：LiuZhengSixOp

:::

:::lemma_ "bs17_2_12" (lean := "SerrePositivity.AlgebraicGeometry.exists_primeField_vCover_filtered_model") (uses := "bm18_eq_1, bm18_1_1, bs17_2_1, bs17_2_3, rydh_2_1, rydh_2_5, rydh_3_3, rydh_3_6")
*BS17 補題 2.12*　アフィン v 被覆の有限表示模型。対応表の状態：一部（special）。

*主張*　qcqs 基底 $`S` 上のアフィンスキーム間の v 被覆は、源と標的が $`S` 上有限表示でアフィンな h 被覆の余フィルター極限として表せる。

原典 PDF p.9, y=74.4。環の射圏で与えた filtered 余極限の各段が有限表示な affine v-cover。双対の逆極限表示に相当し、基底は素体で、任意の qcqs の S は扱わない。

:::

# §3 Perfect schemes

%%%
number := false
tag := "vdescent-bs17-3"
%%%

:::definition "bs17_3_1" (lean := "SerrePositivity.AlgebraicGeometry.ArcRouteB.frobeniusDirectLimit_perfectRing, SerrePositivity.AlgebraicGeometry.ArcRouteB.frobeniusDirectLimitDesc")
*BS17 定義 3.1*　完全スキームと完全化。対応表の状態：一部（special）。

*主張*　$`\mathbf F_p` 上のスキームが完全であるとは、その Frobenius が同型であることをいう。任意の $`\mathbf F_p` スキームの完全化は、Frobenius を推移射とする逆極限で定める。

原典 PDF p.10, y=307.2。標数 p の環の Frobenius 余極限の完全性と降下写像を与える。Spec の双対でアフィン完全化に相当する。一般のスキームの逆極限は含まない。

:::

:::lemma_ "bs17_3_8" (lean := "SerrePositivity.CommutativeAlgebra.isUniversalHomeomorphism_bijective_of_perfect_reduced, SerrePositivity.AlgebraicGeometry.frobeniusDirectLimitUniversalHomeomorphismEquiv") (uses := "rydh_B_3")
*BS17 補題 3.8*　普遍同相と完全化。対応表の状態：一部（special）。

*主張*　完全スキーム間の普遍的同相射は同型である。一般に $`\mathbf F_p` 上のスキームの射は、完全化した射が同型であるとき、かつそのときに限り普遍的同相射となる。

原典 PDF p.11, y=629.1。アフィンの普遍同相な環の射について、完全環での全単射と Frobenius 余極限上の同型を与える。一般のスキームへの貼り合わせと完全化後の同型からの逆向きは、この二つの型に含まれない。

外の文献：Stacks 04DC、Yanagihara

:::

:::lemma_ "bs17_3_16" (lean := "SerrePositivity.tor_vanishing_of_perfect")
*BS17 補題 3.16*　完全環上の正次数 Tor の消滅。対応表の状態：本体にある。

*主張*　完全環の図式 $`C\leftarrow A\to B` に対し、$`i>0` なら $`\operatorname{Tor}_i^A(B,C)=0` である。

原典 PDF p.14, y=74.4。同じ素標数 p の完全環 A と完全 A-代数 B、C に対して、すべての正次数の Tor を零対象とする。

:::

# §4 h-Descent for vector bundles on perfect schemes

%%%
number := false
tag := "vdescent-bs17-4"
%%%

:::theorem "bs17_4_1" (lean := "SerrePositivity.AlgebraicGeometry.cech_exact_of_vCover_perfect, SerrePositivity.AlgebraicGeometry.perfectAffineVCover_cechExact") (uses := "bm18_eq_1, bm18_1_1, bs17_2_1, bs17_2_10, bs17_2_3, rydh_2_1, rydh_2_5, rydh_3_10, rydh_3_3, rydh_3_5, rydh_3_6, rydh_B_3")
*BS17 定理 4.1*　【この部の目標】Witt ベクトル束の v コホモロジーと v-stack。対応表の状態：一部（special）。

*主張*　完全アフィンスキーム $`X=\operatorname{Spec} A` 上で、有限射影 $`W_n(A)` 加群（または $`W(A)` 加群）$`M` に対応するベクトル束 $`E` の導来 v 大域切断は $`M` である。各 $`n` で $`X\mapsto\operatorname{Vect}(W_n(X))` は完全スキーム上の v スタックをなし、$`X\mapsto\operatorname{Vect}(W(X))` も v スタックをなす。

原典 PDF p.15, y=314.7。4.1(i) の n=1、E=O、完全なアフィン環の有限 v 被覆族に対する増大 Čech 完全性。W\_n（n\>1）・W・任意の有限射影係数、サイト上の RΓ\_v との比較および (ii) の v-stack は型に含まれない。

外の文献：Stacks 01XD

:::

# §6 Construction of line bundles: geometric approach

%%%
number := false
tag := "vdescent-bs17-6"
%%%

:::lemma_ "bs17_6_3" (lean := "SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationRing_milnorSquare_perfect") (uses := "bm18_2_8")
*BS17 補題 6.3*　perfect · valuation · with · ordered · abelian。対応表の状態：一部（component）。

*主張*　完全付値環 $`V` の値群から順序アーベル群への写像をとり、像の値が 1 の元を反転した環を $`V'`、像の値が 1 未満の元で割った付値環を $`V_0` とおく。$`V_0'=\operatorname{Frac}(V_0)` に対し $`0\to V\to V'\oplus V_0\to V_0'\to0` は完全で、任意の完全 $`V` スキーム $`X` と $`K\in D_{\mathrm{qc}}(X)` について、$`X`、$`V',V_0` への底変換、$`V_0'` への底変換の順にとった $`R\Gamma(K)` は完全三角形をなす。

原典 PDF p.22, y=74.4。局所化・素イデアル商・剰余体による加法群の短完全列を与える。一般の完全 V スキームと任意の準連接複体に対する導来大域切断の三角は含まない。

:::

