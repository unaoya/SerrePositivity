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

目標は BS17 Theorem 4.1 (i)（完全スキームの上の v 降下）で、BS が引用する。本体はこのうち n = 1・E = O・アフィン・有限族の場合を、BM18 Proposition 4.8 の構造層の場合を通る経路で作った（どちらも対応表では「一部」）。この部には、三つの文献の項目のうち、本体か Mathlib に対応があるものだけを載せる。全項目の表は `research/bs17-coverage`・`bm18-coverage`・`rydh-coverage`。

# §2 h-Sheaves

%%%
number := false
tag := "vdescent-bs17-2"
%%%

:::definition "bs17_2_1" (lean := "SerrePositivity.AlgebraicGeometry.IsSchemeVCover") (uses := "rydh_2_2")
*BS17 定義 2.1*　v 被覆と細分。対応表の状態：一部（component）。

原典 PDF p.4, y=521.1。忠実平坦な付値環拡大による持ち上げの定義を持つ。項目中の細分の定義と、普遍 subtrusive・submersive との比較はこの宣言の結論に含まれない。

外の文献：Rydh 2.8、Rydh 2.9

:::

:::proposition "bs17_2_3" (lean := "SerrePositivity.AlgebraicGeometry.isSchemeVCover_of_flat_surjective, SerrePositivity.AlgebraicGeometry.isSchemeVCover_of_proper_surjective, SerrePositivity.AlgebraicGeometry.isSchemeVCover_sigmaDesc_openCover") (uses := "rydh_2_5")
*BS17 例 2.3*　v 被覆の例。対応表の状態：一部（component）。

原典 PDF p.5, y=136.6。平坦全射・固有全射・開被覆の各場合を与える。他の例や反例をまとめて示す型はない。

:::

:::definition "bs17_2_5" (lean := "SerrePositivity.AlgebraicGeometry.ProperInductiveLevel, SerrePositivity.AlgebraicGeometry.ProperInductiveLevel.baseChange")
*BS17 定義 2.5*　固有全射の帰納的レベル。対応表の状態：本体にある。

原典 PDF p.5, y=423.6。レベル零の proper fppf 細分と有限表示 nilimmersion、後続段の中心・中心外同型・再帰・proper fppf 細分を表し、底変換で保存する。nilimmersion は有限表示な全射閉埋め込みで表す。

:::

:::lemma_ "bs17_2_6" (lean := "SerrePositivity.AlgebraicGeometry.exists_properInductiveLevel_affineBase, SerrePositivity.AlgebraicGeometry.exists_properInductiveLevel_noetherian")
*BS17 補題 2.6*　有限の帰納的レベルの存在。対応表の状態：一部（special）。

原典 PDF p.5, y=565.8。有限表示固有全射が有限の帰納的レベルを持つ。基底がアフィン、または Noether の場合を与え、一般の qcqs 基底を一括する型はない。

外の文献：RG71、Rydh、Stacks 0815、TT

:::

:::lemma_ "bs17_2_10" (lean := "SerrePositivity.AlgebraicGeometry.perfectCechUniversalDescent_of_affine_refinement")
*BS17 補題 2.10*　合成と普遍降下。対応表の状態：一部（special）。

原典 PDF p.7, y=615.0。合成での普遍降下から後段へ移す (a) の構造層 Čech 版。元の射に分離・準コンパクト・局所有限表示、合成にアフィン性と局所有限表示を課す。一般の F と (b) の一般形を含まない。

外の文献：LiuZhengSixOp

:::

:::lemma_ "bs17_2_12" (lean := "SerrePositivity.AlgebraicGeometry.exists_primeField_vCover_filtered_model")
*BS17 補題 2.12*　アフィン v 被覆の有限表示模型。対応表の状態：一部（special）。

原典 PDF p.9, y=74.4。環の射圏で与えた filtered 余極限の各段が有限表示な affine v-cover。双対の逆極限表示に相当し、基底は素体で、任意の qcqs の S は扱わない。

:::

# §3 Perfect schemes

%%%
number := false
tag := "vdescent-bs17-3"
%%%

:::definition "bs17_3_1" (lean := "SerrePositivity.AlgebraicGeometry.ArcRouteB.frobeniusDirectLimit_perfectRing, SerrePositivity.AlgebraicGeometry.ArcRouteB.frobeniusDirectLimitDesc")
*BS17 定義 3.1*　完全スキームと完全化。対応表の状態：一部（special）。

原典 PDF p.10, y=307.2。標数 p の環の Frobenius 余極限の完全性と降下写像を与える。Spec の双対でアフィン完全化に相当する。一般のスキームの逆極限は含まない。

:::

:::lemma_ "bs17_3_8" (lean := "SerrePositivity.CommutativeAlgebra.isUniversalHomeomorphism_bijective_of_perfect_reduced, SerrePositivity.AlgebraicGeometry.frobeniusDirectLimitUniversalHomeomorphismEquiv")
*BS17 補題 3.8*　普遍同相と完全化。対応表の状態：一部（special）。

原典 PDF p.11, y=629.1。アフィンの普遍同相な環の射について、完全環での全単射と Frobenius 余極限上の同型を与える。一般のスキームへの貼り合わせと完全化後の同型からの逆向きは、この二つの型に含まれない。

外の文献：Stacks 04DC、Yanagihara

:::

:::lemma_ "bs17_3_16" (lean := "SerrePositivity.tor_vanishing_of_perfect")
*BS17 補題 3.16*　完全環上の正次数 Tor の消滅。対応表の状態：本体にある。

原典 PDF p.14, y=74.4。同じ素標数 p の完全環 A と完全 A-代数 B、C に対して、すべての正次数の Tor を零対象とする。

:::

# §4 h-Descent for vector bundles on perfect schemes

%%%
number := false
tag := "vdescent-bs17-4"
%%%

:::theorem "bs17_4_1" (lean := "SerrePositivity.AlgebraicGeometry.cech_exact_of_vCover_perfect, SerrePositivity.AlgebraicGeometry.perfectAffineVCover_cechExact")
*BS17 定理 4.1*　【この部の目標】Witt ベクトル束の v コホモロジーと v-stack。対応表の状態：一部（special）。

原典 PDF p.15, y=314.7。4.1(i) の n=1、E=O、完全なアフィン環の有限 v 被覆族に対する増大 Čech 完全性。W\_n（n\>1）・W・任意の有限射影係数、サイト上の RΓ\_v との比較および (ii) の v-stack は型に含まれない。

外の文献：Stacks 01XD

:::

# §6 Construction of line bundles: geometric approach

%%%
number := false
tag := "vdescent-bs17-6"
%%%

:::lemma_ "bs17_6_3" (lean := "SerrePositivity.BhattScholze.Perfectoidization.Arc.valuationRing_milnorSquare_perfect")
*BS17 補題 6.3*　perfect · valuation · with · ordered · abelian。対応表の状態：一部（component）。

原典 PDF p.22, y=74.4。局所化・素イデアル商・剰余体による加法群の短完全列を与える。一般の完全 V スキームと任意の準連接複体に対する導来大域切断の三角は含まない。

:::

