import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Elements
import Mathlib.Topology.Homotopy.Lifting
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianEdgeTransport
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CrossingComparison
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.BoundaryPrism
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Choices
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Composition
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.EdgeTransport
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FatJoinPointCylinder
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.HomotopyTransport
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Identity
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IntervalCocartesianCriterion
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinDiagonal
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinDiagonalInnerFibration
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinQuasicategory
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.LiftSpace
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.MappingCylinderComparison
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.MappingCylinderGeneralComparison
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.ParametrizedFiberTransport
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.PrescribedCartesianTransport
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoin
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCocartesianFibration
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCrossingCocartesian
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCylinder
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCylinderEquivalence
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCylinderNaturality
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinEmpty
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinExtensionEquivalence
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinIdentity
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinPoint
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinPullbackIso
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinPullbackMap
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Witness
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibrationInternalHom
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinPoint
import SerrePositivity.KST.SConstruction.DoubleCoconeUniversality

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "5.2 Covariant Transport" =>
%%%
number := false
tag := "kerodon-5-2"
%%%

Kerodon の 5.2 節（[Tag 019A](https://kerodon.net/tag/019A)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

*route-classification.html — 4. 段 2：左 fibration — 4.2（2.2）fiber は Kan 複体、全ての辺は cocartesian*

*fiber の定義*：$`b\colon\Delta^0\to B` に沿った厳密な引き戻し $`E_b:=\Delta^0\times_BE`、つまり $`(E_b)_n=\{\sigma\in E_n\mid p(\sigma)=b_n\}`（$`b_n` は $`b` の定値 $`n` 単体）。辺は像が*ちょうど* $`s_0b` の辺。例：$`N(F)\to N(I)` の fiber は $`N(F_i)`、$`\mathcal C_{x/}\to\mathcal C` の $`y` 上の fiber は $`\mathrm{Hom}^L(x,y)`、$`B\times K\to B` の fiber は $`K`。単体 $`\sigma\colon\Delta^n\to B` に沿った $`E_\sigma:=\Delta^n\times_BE` も使い、$`n=1` が写像柱（2.6）。

*(a) 点上の左 fibration は Kan*：内ホーンで準圏、$`\Lambda^2_0` を $`(u,\mathrm{id}_a)` で埋めて左逆元、亜群なので 3.2 の系で Kan（$`\mathrm{Hom}^R` が $`\Lambda^2_2` で右逆元を作ったのと左右逆）。よって fiber $`E_b`、$`\mathrm{Fun}_B(E,E')`、$`\mathrm{Hom}^L(x,y)` は Kan。

*(b) 全ての辺が cocartesian*：$`\Lambda^n_0` の持ち上げは最初の辺が何でも定義に含まれる。逆に cocartesian fibration について、左 fibration ⟺ 全辺 cocartesian ⟺ fiber が全て Kan（任意の辺を cocartesian な持ち上げと fiber の中の辺に分解し、fiber が Kan なら後者は同値）。0.6 の「全ての辺が輸送する辺」の正確な形。1 圏では fiber が亜群の opfibration ⟺ 全ての射が opcartesian。

*(c)* 同値を反映する（3.2）。特に fiber の中の辺は全て $`E` の同値。*(d)* 写像空間では $`\mathrm{Map}_E(y,z)\simeq\mathrm{Map}_E(x,z)\times_{\mathrm{Map}_B(px,pz)}\mathrm{Map}_B(py,pz)`（補章 4）、ここから $`\mathrm{Map}_E(x,z)\to\mathrm{Map}_B(px,pz)` の $`u` 上の fiber が $`\mathrm{Map}_{E_{b'}}(u_!x,z)`。

*質問：厳密な fiber は ∞ 圏的な fiber と一致するか*。左 fibration（底が準圏）では一致する。

- 意味　／　$`E_b` と　／　理由
- $`\mathrm{sSet}` の引き戻し　／　定義　／　—
- $`\mathrm{QCat}`（1 圏）の引き戻し　／　一致　／　$`E_b` が準圏（一般の準圏の $`\mathrm{sSet}` 引き戻しは準圏とは限らないが、片方が内 fibration なら準圏）
- $`\mathrm{Cat}_\infty` の引き戻し　／　一致（$`B` 準圏）　／　左 fibration は isofibration（Kerodon Ex. 4.4.1.11）＝ Joyal のモデル構造の fibration、fibration に沿った引き戻しはホモトピー引き戻し
- 一般の写像の厳密な fiber　／　不一致　／　例：$`\{0\}\to J`（$`J` は自由な同型の圏のナーブ）の 1 上の fiber は空、∞ 圏的 fiber は一点

モデル構造なしの形：∞ 圏的 fiber は $`\Delta^0\times_BP(B)\times_BE`（$`P` は同値な辺の path 空間、3.5・3.6 の置換）で、定値 path による $`E_b\to\Delta^0\times_BP(B)\times_BE` は isofibration の性質から圏同値。底が準圏でないときは内アノダインな置換 $`B\to B'` で読み、共変モデル構造の不変性で $`E_b` は正しい（正確な主張は 2.5 で確認）。

*Lean での扱い*：fiber は \`vertexFiber\`（引き戻し）。

- 内容　／　宣言　／　ファイル
- 左ホーンが埋まれば Kan　／　\`kanComplex\_of\_leftHornFillers\`　／　Core/LeftFiberKan
- fiber は Kan　／　\`vertexFiber\_kanComplex\_of\_leftFibration\`　／　同上
- cocartesian 辺　／　\`IsCocartesianEdge\`、\`IsCartesianEdge\`　／　F1/Fibrations/CartesianEdge
- 全辺が cocartesian　／　\`isCocartesianEdge\_of\_leftFibration\`、\`leftFibration\_cocartesianFibration\`　／　F1/Fibrations/CartesianEdge、CartesianFibration
- 逆向き　／　\`leftFibration\_of\_cocartesianFibration\_of\_all\_edges\`、\`leftFibration\_iff\_cocartesianFibration\_all\_edges\`　／　F1/Fibrations/AllEdges

*route-classification.html — 4. 段 2：左 fibration — 4.3（2.3）輸送 $`u_!\colon E_b\to E_{b'}`*

*構成*：$`u\colon b\to b'` について $`h\colon\Delta^1\times E_b\to E`（$`\{0\}\times E_b` で包含、$`p h=u\circ\mathrm{pr}_1`）を持ち上げで取る。$`\{0\}\times E_b\subset\Delta^1\times E_b` は左アノダイン（$`\{0\}\subset\Delta^1` 左アノダイン × 単射、0.5 の積の補題の左版）。$`u_!:=h|_{\{1\}\times E_b}`。各点では $`u_!(e)` は $`e` から始まる $`u` の持ち上げの終点（$`L(e,u)` を全体で同時に取ったもの）。

*一意性*：$`h` の選び方は自明 Kan fibration $`\mathrm{Fun}(\Delta^1\times E_b,E)\to\mathrm{Fun}(\{0\}\times E_b,E)\times_{\mathrm{Fun}(\{0\}\times E_b,B)}\mathrm{Fun}(\Delta^1\times E_b,B)` の fiber で可縮。

*関手性*：(1) $`(\mathrm{id}_b)_!\simeq\mathrm{id}`（射影を取る）。(2) 2 単体 $`(u,v,w)` の上で $`\Delta^2\times E_b` を持ち上げて $`w_!\simeq v_!u_!`。(3) ホモトピックな辺は同じ輸送。(4) $`u` が同値なら $`u_!` はホモトピー同値。よって関手 $`hB\to h\mathrm{Kan}`（定理 I の 1 圏的な影、$`\mathrm{St}(E)` のホモトピー圏への像）。

- 左 fibration　／　$`u_!`
- 離散 opfibration　／　$`F(u)`
- $`\mathcal C_{x/}\to\mathcal C`　／　後合成 $`u\circ-`
- $`B\times K\to B`　／　恒等
- 被覆空間・Kan fibration　／　モノドロミー

*失われる情報*：$`B(\mathbb Z/2)` 上では $`hB\to h\mathrm{Kan}` はホモトピー作用（$`\tau^2\simeq\mathrm{id}`）しか持たず、そのホモトピーの選び方と整合性は失われる。整合的な作用に持ち上がらないホモトピー作用もある。定理 I はこの影を ∞ 関手に格上げする主張。

*Lean での扱い*：

- 内容　／　宣言　／　ファイル
- 左アノダイン × 単射　／　\`leftAnodyneExtensions\_unionProd\`　／　Core/PairingHorns
- fiber 全体の輸送　／　\`LeftFibrationFiberTransport\`、\`nonempty\_leftFibrationFiberTransport\`　／　Stable/LeftFibrationFiberTransport
- 径数づけた輸送の族　／　\`FiberTransportFamily\`、\`fiberTransportFamily\`、\`FiberTransportFamily.endpointIso\`　／　F1/Transport/FiberTransportFamily
- 輸送が同値であることの判定　／　\`parametrizedFiberTransport\_isQCatEquivalence\_of\_squareIso\`　／　F1/Transport/ParametrizedTransportSquare

*route-classification.html — 4. 段 2：左 fibration — 4.4（2.4）安定性*

*形式的に閉じる操作*（右持ち上げ性質のクラスなので）：引き戻し（fiber は $`(E\times_BB')_{b'}=E_{k(b')}`）、合成、積、レトラクト、塔の逆極限。

*局所性*：$`p` が左 fibration ⟺ 全ての単体 $`\sigma\colon\Delta^n\to B` について $`E_\sigma\to\Delta^n` が左 fibration（ホーンの持ち上げ問題は底の単体に沿った引き戻しの中で読める）。2.5 や段 7 で $`B=\Delta^n` に帰着する根拠。

*関手の ∞ 圏への上げ*：$`K\subseteq L` 単射なら $`\mathrm{Fun}(L,E)\to\mathrm{Fun}(K,E)\times_{\mathrm{Fun}(K,B)}\mathrm{Fun}(L,B)` は左 fibration、$`K\subseteq L` が左アノダインなら自明 Kan fibration（0.5）。$`K=\emptyset` で $`\mathrm{Fun}(L,E)\to\mathrm{Fun}(L,B)`、相対関手の空間 $`\mathrm{Fun}_B(E',E)` は Kan。*切断の空間* $`\mathrm{Fun}_B(B,E)` は $`\mathrm{St}(E)` の極限に当たり、余極限は全空間 $`E` のホモトピー型（0.4、証明は段 7 の後）。

*双対*：$`p` 左 ⟺ $`p^{\mathrm{op}}` 右（$`\Lambda^n_i\leftrightarrow\Lambda^n_{n-i}`）。左 fibration の間の写像そのものの性質は形式的には出ず、2.5 の内容。

*Lean での扱い*：\`leftFibrations\` は \`deriving IsMultiplicative, IsStableUnderBaseChange, IsStableUnderRetracts\`（Core/RightFibration）。引き戻しのインスタンス \`leftFibration\_pullback\_fst\`（Core/RelativeCoslice）。$`\mathrm{Fun}(K,-)` への上げ \`ihom\_map\_leftFibration\`、\`leftAnodyneExtensions\_pushoutObjObj\_horn\`（F1/Fibrations/LeftFibrationInternalHom）。

:::definition "kerodon_5_2_0_1"
Kerodon Construction 5.2.0.1（[Tag 027S](https://kerodon.net/tag/027S)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の離散 opfibration・左ファイブレーション・hC 値・双対と Set 値を照合。left covering に対する離散ファイバーと一意な辺の持ち上げによる輸送関数。左ファイブレーションの輸送関手に一意な持ち上げの仮定はない。

:::

:::proposition "kerodon_5_2_0_3"
Kerodon Proposition 5.2.0.3（[Tag 0352](https://kerodon.net/tag/0352)）。対応表の状態：なし。

homotopyTransportの値域はhQCat。原文は離散fiberをSetに送る一意な関手で、hQCatからそのSet値輸送へ比較する型がない。別の値域の類似構成。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.homotopyTransport`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.homotopyTransport_map_edge`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.homotopyTransport_unique`

:::

:::definition "kerodon_5_2_0_4"
Kerodon Definition 5.2.0.4（[Tag 0353](https://kerodon.net/tag/0353)）。対応表の状態：なし。

homotopyTransportはhQCat値であり、原文が名付けるleft coveringのSet値の表現ではない。同じ対象の定義として直接使えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.homotopyTransport`

:::

# 5.2.1 Exponentiation for Cartesian Fibrations

%%%
number := false
tag := "kerodon-5-2-1"
%%%

Kerodon [Tag 01VF](https://kerodon.net/tag/01VF)

:::theorem "kerodon_5_2_1_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.ihom_map_leftFibration, SerrePositivity.KST.SConstruction.ihom_pre_innerFibration") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_1_4_3, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_1_4_12, kerodon_5_1_4_13, kerodon_5_2_1_3, kerodon_5_2_1_5")
Kerodon Theorem 5.2.1.1（[Tag 01VG](https://kerodon.net/tag/01VG)）。対応表の状態：一部。

qをleft fibrationに制限するとihom\_map\_leftFibrationは同じ内部Hom後合成をleft fibration、従ってcocartesian fibrationと直接返す。原文(1′)の特殊形のみ。

:::

:::proposition "kerodon_5_2_1_3" (uses := "kerodon_1_1_0_6, kerodon_3_1_2_12, kerodon_4_1_2_17, kerodon_5_1_1_1")
Kerodon Proposition 5.2.1.3（[Tag 01VK](https://kerodon.net/tag/01VK)）。対応表の状態：なし。

引用はcocartesian辺全体から始点評価への射。原文はcartesian辺全体から終点評価の像Zへの射であり、同じ射の制限とは言えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathSource_trivialKanFibration`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPath`

:::

:::lemma_ "kerodon_5_2_1_5" (uses := "kerodon_1_1_0_6, kerodon_4_1_4_3, kerodon_4_4_4_7, kerodon_4_4_4_8, kerodon_5_1_1_1")
Kerodon Lemma 5.2.1.5（[Tag 01VM](https://kerodon.net/tag/01VM)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：関手空間の点ごとの評価・通常圏の指数化・右側・相対版を照合。点ごとの評価と Fun(B,q) の cocartesian 辺の比較。内部 Hom の内ファイブレーション性には評価した辺ごとの判定がない。

:::

# 5.2.2 Covariant Transport Functors

%%%
number := false
tag := "kerodon-5-2-2"
%%%

Kerodon [Tag 019M](https://kerodon.net/tag/019M)

*03-straightening.html — 1. cocartesian 辺と cocartesian fibration — transport*

cocartesian fibration では、底の辺 $`e\colon b\to b'` に沿って fiber の間の関手 $`e_!\colon X_b\to X_{b'}` が「ほぼ一意に」決まる。

- 内容　／　Lean　／　場所
- 一点の持ち上げ（対象の移送）　／　\`chooseCocartesianEdgeLift\`、\`cocartesianTransportObject\`　／　F1/TransportObjects
- transport の選択空間は可縮（Kerodon Prop. 5.2.2.8）　／　\`transportChoiceSpace\_isContractibleKan\`　／　F1/TransportChoices
- transport 関手を一つ選ぶ　／　\`cocartesianTransport p e : X\_b ⟶ X\_\{b'\}\`　／　F1/TransportHo
- どの選び方でもホモトピー圏上で自然同型　／　\`IsCocartesianTransport.toHoIso\`　／　同上

「選択空間が可縮」という形で一意性を述べるのが、以後の構成の基本の型である。選び方の任意性を、可縮な Kan 複体の点を選ぶことに閉じ込めておく。

:::proposition "kerodon_5_2_2_1"
Kerodon Proposition 5.2.2.1（[Tag 01SA](https://kerodon.net/tag/01SA)）。対応表の状態：なし。

IsCocartesianとFiberの定義だけでは原文が要求するf\_!関手・自然変換・一意性のいずれも直接構成しない。

宣言：`CategoryTheory.Functor.IsCocartesian`、`CategoryTheory.Functor.Fiber`

:::

:::definition "kerodon_5_2_2_2"
Kerodon Construction 5.2.2.2（[Tag 023T](https://kerodon.net/tag/023T)）。対応表の状態：なし。

IsCocartesianという射の述語は、原文が名付けるfiber間の共変輸送関手ではない。関手構成への比較がない。

宣言：`CategoryTheory.Functor.IsCocartesian`

:::

:::definition "kerodon_5_2_2_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IsEdgeTransport, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IsCocartesianTransport")
Kerodon Definition 5.2.2.4（[Tag 019N](https://kerodon.net/tag/019N)）。対応表の状態：本体にある。

仮定：内ファイブレーション p、底の辺 e:a→b、候補 F:E\_a→E\_b（Lean が弱い：述語は任意の p に定義）。結論：IsEdgeTransport は両端を指定し e 上にあり全垂直辺が cocartesian な Δ¹×E\_a の prism の存在（一致）。

:::

:::proposition "kerodon_5_2_2_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isEdgeTransport_identity") (uses := "kerodon_1_1_0_6")
Kerodon Example 5.2.2.5（[Tag 019P](https://kerodon.net/tag/019P)）。対応表の状態：一部。

底を準圏、Uをcocartesian fibrationに強めるとisEdgeTransport\_identityは同じ退化辺に沿うfiber恒等が輸送であることを直接返す。任意のinner fibrationではない。

:::

:::proposition "kerodon_5_2_2_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport_isTransport, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IsEdgeTransport.functorIso, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.transportChoiceSpace_isContractibleKan") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_2_2_13")
Kerodon Proposition 5.2.2.8（[Tag 01VS](https://kerodon.net/tag/01VS)）。対応表の状態：一部。

edgeTransport\_isTransportは原文の輸送の存在を直接返し、IsEdgeTransport.functorIsoは任意の二つの輸送の同型を返す。同型な任意候補も輸送になる逆は含まない。

:::

:::definition "kerodon_5_2_2_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport")
Kerodon Notation 5.2.2.9（[Tag 023Y](https://kerodon.net/tag/023Y)）。対応表の状態：本体にある。

仮定：CocartesianFibration p と底の辺 e:a→b（Kerodon と一致）。結論：edgeTransport p e がファイバー間の輸送の選択された代表 f\_!。原文の記法はこの代表を許す（一致）。

:::

:::definition "kerodon_5_2_2_10" (uses := "kerodon_1_1_0_6, kerodon_5_1_1_1, kerodon_5_1_4_1")
Kerodon Definition 5.2.2.10（[Tag 02R8](https://kerodon.net/tag/02R8)）。対応表の状態：なし。

cocartesianLiftSpaceは指定始点と底を固定した持ち上げの空間。原文の任意の個別prism Hに対する点ごとのcocartesianという述語との頂点対応が引用した型にはない。空間の名前だけを定義のcomponentとしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianLiftSpace`

:::

:::lemma_ "kerodon_5_2_2_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianLiftSpace_isContractibleKan, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesian_prism_extend_boundary") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_2_1_1")
Kerodon Lemma 5.2.2.13（[Tag 02RB](https://kerodon.net/tag/02RB)）。対応表の状態：一部。

cocartesianLiftSpace\_isContractibleKanは任意の始点・底のprismを固定した持ち上げ空間を可縮Kanと直接返す。特に頂点があり、原文(1)のcocartesian liftを与える。(2)の任意の同型な終点の厳密実現は含まない。

:::

:::definition "kerodon_5_2_2_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgeTransport, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgeTransport_witness") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_1_1")
Kerodon Definition 5.2.2.15（[Tag 01VN](https://kerodon.net/tag/01VN)）。対応表の状態：一部。

Uをcartesian fibrationに強めるとcartesianEdgeTransportとそのwitnessは、同じ辺に沿う反変輸送と両端・底の等式および全頂点のcartesianなprismを直接構成する。任意inner fibrationと任意候補の述語全体は含まない。

:::

:::proposition "kerodon_5_2_2_17" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.exists_cartesianPrism_prescribed_vertices, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgeTransport_witness")
Kerodon Proposition 5.2.2.17（[Tag 019X](https://kerodon.net/tag/019X)）。対応表の状態：一部。

現本体のcartesianEdgeTransport\_witnessは一般の底の各辺について同じ反変輸送の存在を直接返す。原文第一結論のみで、任意の輸送の同型類の一意性は含まない。

:::

:::definition "kerodon_5_2_2_18" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgeTransport, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgeTransport_witness")
Kerodon Notation 5.2.2.18（[Tag 019Y](https://kerodon.net/tag/019Y)）。対応表の状態：一部。

cartesianEdgeTransportとそのwitnessは原文が許す代表f\*の選択とそのprismを直接与える。全ての候補が一つの同型類になる結論は含まない。

:::

:::proposition "kerodon_5_2_2_19" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_3_1_3_2")
Kerodon Proposition 5.2.2.19（[Tag 01A1](https://kerodon.net/tag/01A1)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：底辺が可逆な場合・左右の輸送の合成・Kan・離散の場合を照合。Kan fibration の同じ底辺に沿う共変・反変輸送が hQCat で互いに逆。invertibleLeftTransport の共変側の同値だけでは両者を比較しない。

:::

:::theorem "kerodon_5_2_2_20"
Kerodon Theorem 5.2.2.20（[Tag 01A2](https://kerodon.net/tag/01A2)）。対応表の状態：なし。

引用は底の可逆辺に沿うleft fibrationの輸送の同値性。原文は任意の射のKan fibration性を全辺の輸送で判定するiffであり、可逆辺だけの証明部品ではその方向を直接与えない。

*f-06-straightening.html — 1. 何を分類するか*

- Kan fibration は、transport がすべてホモトピー同値である左 fibration（Kerodon 5.2.2.20）。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport_isQCatEquivalence_of_isInvertibleEdge`

:::

:::corollary "kerodon_5_2_2_21"
Kerodon Corollary 5.2.2.21（[Tag 0240](https://kerodon.net/tag/0240)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：底辺が可逆な場合・左右の輸送の合成・Kan・離散の場合を照合。covering と左右輸送の可逆性による判定。Quiver.IsCovering は simplicial covering の全次元の一意持ち上げと異なる。

:::

# 5.2.3 Example: The Relative Join

%%%
number := false
tag := "kerodon-5-2-3"
%%%

Kerodon [Tag 0241](https://kerodon.net/tag/0241)

:::definition "kerodon_5_2_3_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection")
Kerodon Construction 5.2.3.1（[Tag 0242](https://kerodon.net/tag/0242)）。対応表の状態：本体にある。

仮定：同じ標的 S を持つ単体集合の射 f:X→S、g:Y→S（Kerodon と一致）。結論：relativeJoin f g は X⋆Y→S⋆S と joinDiagonal S:Δ¹×S→S⋆S の引き戻し。Δ¹ への射影を持つ（一致）。

:::

:::proposition "kerodon_5_2_3_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr_emptySource_isIso, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin_joinInr_emptySource_isIso")
Kerodon Example 5.2.3.4（[Tag 0245](https://kerodon.net/tag/0245)）。対応表の状態：一部。

relativeJoinInr\_emptySource\_isIsoはCが空かつG=idのとき原文の同じ右包含が同型と直接返す。任意Gおよび左包含の結論は含まない。

:::

:::proposition "kerodon_5_2_3_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin_point_fst_isIso, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal_point_isIso")
Kerodon Example 5.2.3.5（[Tag 0246](https://kerodon.net/tag/0246)）。対応表の状態：本体にある。

仮定：単体集合 X,Y と点への射（Kerodon と一致）。結論：相対 join の通常の join への第1射影が同型（一致）。

:::

:::proposition "kerodon_5_2_3_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinSelfIso")
Kerodon Example 5.2.3.6（[Tag 0247](https://kerodon.net/tag/0247)）。対応表の状態：本体にある。

仮定：任意の単体集合 S（Kerodon と一致）。結論：relativeJoin (id S) (id S) と Δ¹×S の同型（一致）。

:::

:::proposition "kerodon_5_2_3_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPullbackMap_isPullback, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPullbackMap")
Kerodon Remark 5.2.3.9（[Tag 024A](https://kerodon.net/tag/024A)）。対応表の状態：一部。

relativeJoinPullbackMap\_isPullbackはD=E、G=idの場合の同じrelative joinの底変換四角そのもの。任意の二つの因子には一般化しない。

:::

:::proposition "kerodon_5_2_3_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin_quasicategory, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection_innerFibration")
Kerodon Proposition 5.2.3.11（[Tag 024C](https://kerodon.net/tag/024C)）。対応表の状態：本体にある。

仮定：Quasicategory X,Y,S と f:X→S、g:Y→S（Kerodon と一致）。結論：relativeJoin f g が Quasicategory。Δ¹ への射影の内ファイブレーション性もある（一致）。

:::

:::lemma_ "kerodon_5_2_3_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal_innerFibration") (uses := "kerodon_1_1_0_6")
Kerodon Lemma 5.2.3.12（[Tag 024D](https://kerodon.net/tag/024D)）。対応表の状態：一部。

E′=Δ⁰に制限するとrelative joinは通常join、比較はjoinDiagonalとなり、joinDiagonal\_innerFibrationが同じ射のinner性を直接返す。一般のUの相対版は含まない。

:::

:::lemma_ "kerodon_5_2_3_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin_fst_innerFibration") (uses := "kerodon_1_1_0_6, kerodon_4_3_3_24, kerodon_5_2_3_12")
Kerodon Lemma 5.2.3.13（[Tag 02RF](https://kerodon.net/tag/02RF)）。対応表の状態：一部。

C′=C,D′=D,E′=Δ⁰、W:E→Δ⁰に制限すると原文の射はrelative joinから通常joinへの第一射影。relativeJoin\_fst\_innerFibrationが同じ射を直接扱う。

:::

:::proposition "kerodon_5_2_3_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection_cocartesianFibration, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianFibration_interval_of_lift") (uses := "kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_2_3_18")
Kerodon Proposition 5.2.3.15（[Tag 024J](https://kerodon.net/tag/024J)）。対応表の状態：一部。

relativeJoinProjection\_cocartesianFibrationは原文第一結論の同じrelative joinからΔ¹への射影について直接の型。prismがFの輸送を表す第二結論は引用にない。

:::

:::lemma_ "kerodon_5_2_3_16" (uses := "kerodon_1_1_0_6")
Kerodon Lemma 5.2.3.16（[Tag 02RG](https://kerodon.net/tag/02RG)）。対応表の状態：なし。

引用はrelative joinのΔ¹への射影と両端での公式。原文の任意の誘導射Wに対するcocartesian辺の結論は含まず、構造の部品にとどまる。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl_projection`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr_projection`

:::

:::lemma_ "kerodon_5_2_3_17" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_2_3_13, kerodon_5_2_3_16")
Kerodon Lemma 5.2.3.17（[Tag 02RH](https://kerodon.net/tag/02RH)）。対応表の状態：なし。

relativeJoin\_crossing\_isCocartesianはΔ¹への構造射と混合辺だけ。原文の一般Wがcocartesian fibrationである結論や同じWの全辺のiffを直接与えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin_crossing_isCocartesian`

:::

:::proposition "kerodon_5_2_3_18" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin_crossing_isCocartesian, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection_cocartesianFibration") (uses := "kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_2_3_17")
Kerodon Example 5.2.3.18（[Tag 02RJ](https://kerodon.net/tag/02RJ)）。対応表の状態：一部。

relativeJoinProjection\_cocartesianFibrationは原文の最初の結論、crossing補題は混合辺が像の同型に対応する場合の十分条件を直接返す。三場合全体のiffは含まない。

:::

:::definition "kerodon_5_2_3_19"
Kerodon Variant 5.2.3.19（[Tag 024K](https://kerodon.net/tag/024K)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対 join の一方が点・左右の collage・普通の圏の Grothendieckを照合。相対 join から Δ¹ への cartesian fibration と、G を反変輸送として表す結論。左側の cocartesian collage だけでは G を与える右側の比較がない。

:::

# 5.2.4 Fibrations over the 1-Simplex

%%%
number := false
tag := "kerodon-5-2-4"
%%%

Kerodon [Tag 024M](https://kerodon.net/tag/024M)

*route-classification.html — 4. 段 2：左 fibration — 4.6（2.6）$`\Delta^1` 上の左 fibration（写像柱）*

*主張*：$`\Delta^1` 上の左 fibration は本質的に Kan 複体の間の写像 $`u_!\colon E_0\to E_1` と同じ（写像空間まで込めて $`\mathrm{LFib}(\Delta^1)\simeq\mathrm{Fun}(\Delta^1,\mathcal S)`、定理 I の $`B=\Delta^1` の場合）。

- *左 fibration → 写像*：2.3 の輸送。

- \*\*写像 → $`\Delta^1` 上の対象\*\*：写像柱 $`M(\varphi):=(\Delta^1\times K)\sqcup_{\{1\}\times K}L\to\Delta^1`。一般に左 fibration ではない（$`L` の辺と $`\Delta^1\times K` の 2 単体を組み合わせた $`\Lambda^2_1` が埋まらない）。左アノダインな置き換えか相対ナーブ（HTT §3.2.5）で左 fibration にするか、置き換えずに比較する（形式化の方針）。

- *比較*：$`h` と包含 $`E_1\subset E` から $`c\colon M(u_!)\to E`。任意の左 fibration $`X\to\Delta^1` で $`c^*\colon\mathrm{Fun}_{\Delta^1}(E,X)\to\mathrm{Fun}_{\Delta^1}(M(u_!),X)` はホモトピー同値。右辺は押し出しと $`\{0\}\times K\subset\Delta^1\times K` の左アノダイン性から $`\mathrm{Fun}(K,X_0)\times_{\mathrm{Fun}(K,X_1)}\mathrm{Fun}(L,X_1)`（ホモトピー fiber 積）＝ $`(\alpha_0,\alpha_1,\ u^X_!\alpha_0\simeq\alpha_1\varphi)`、つまり $`\mathrm{Fun}(\Delta^1,\mathcal S)` の写像空間（ホモトピー可換な正方形）。

*帰結*：$`E\simeq E'` in $`\mathrm{LFib}(\Delta^1)` ⟺ $`u_!`、$`u'_!` の間にホモトピー可換な同値の正方形。*段 6 への準備（univalence）*：fiber を $`K,L` に固定した $`\Delta^1` 上の左 fibration の空間は $`\mathrm{Fun}(K,L)` と同値、$`\mathrm{Map}_{\mathcal S}(K,L)\simeq\mathrm{Fun}(K,L)`（段 3）と合わせて「$`\mathcal S` の辺 ＝ $`\Delta^1` 上の左 fibration」。一般の $`B` は局所性で $`\Delta^n`、さらに $`\Delta^1` に帰着。

*Lean での扱い*：写像柱は押し出し \`pushout (prismEndpoint 1 K) f\` で、置き換えずに比較する。

- 内容　／　宣言　／　ファイル
- 端点の包含と比較　／　\`transportCylinderEndpointInclusion\`、\`transportCylinderEndpointInclusion\_comparison\`　／　F1/MappingSpaces/IntervalTransportBoundary
- 径数づけた写像柱　／　\`parametrizedCylinderIsPushout\`、\`parametrizedCylinderDesc\`　／　F1/Transport/ParametrizedCylinderGluing
- 比較が同値　／　\`intervalTransportCylinder\_boundaryFamily\_isQCatEquivalence\`　／　F1/MappingSpaces/IntervalTransportBoundaryFamily
- 正方形の空間　／　\`cylinderEquivalenceSquareSpace\`、\`cylinderEquivalenceSquareEndpoints\`　／　F1/MappingSpaces/CylinderEquivalenceSquares
- 区間上の本質的全射性　／　\`isEssentiallySurjective\_over\_interval\_of\_endpoint\_fibers\`　／　F1/Fibrations/FiberwiseEssentialSurjectivity

*段 2 で押さえること*：$`\mathrm{LFib}(B)=N^{hc}`（相対関手の空間を Hom とする単体的圏）で、Hom は最初から Kan。fiber は厳密な引き戻しで Kan 複体、∞ 圏的な fiber とも一致する。全ての辺が cocartesian で、輸送 $`u_!` は可縮な選択で決まり $`hB\to h\mathrm{Kan}` を与える（高次の整合性は落ちる）。左 fibration は引き戻し・合成・$`\mathrm{Fun}(K,-)` で閉じ、単体ごとに判定できる。$`B` 上の写像の同値は fiber ごとに判定でき（単体の上の切断は始点の fiber で決まる）、$`\Delta^1` 上の左 fibration は写像 $`E_0\to E_1` と同じ。

:::theorem "kerodon_5_2_4_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin_extension_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isQCatEquivalence_over_interval_of_endpoint_fibers_of_cocartesian_lifts, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_relativeJoinCylinderComparison, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinder_isPrecompositionEquivalence") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_1_5_7_5, kerodon_4_1_3_3, kerodon_4_5_5_1, kerodon_4_5_5_9, kerodon_4_5_6_2, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_1_6_1, kerodon_5_2_3_15, kerodon_5_2_4_5")
Kerodon Theorem 5.2.4.1（[Tag 024N](https://kerodon.net/tag/024N)）。対応表の状態：一部。

mappingCylinder\_isPrecompositionEquivalenceは原文の三条件を仮定して同じpushoutからMへの比較射を圏同値にするので、categorical pushoutとなる十分方向。逆とUのcocartesian性は含まない。

:::

:::corollary "kerodon_5_2_4_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinder_isPrecompositionEquivalence")
Kerodon Corollary 5.2.4.2（[Tag 024P](https://kerodon.net/tag/024P)）。対応表の状態：本体にある。

仮定：∞ 圏 M→Δ¹、端点ファイバー X,Y、輸送を表す prism H（Lean が弱い：比較補題は両端の比較が同値ならファイバーそのものでなくてもよい）。結論：pushout.desc H g は前合成同値。X,Y を実際の両ファイバー、z₀,z₁ を恒等とすると原文の比較射（一致）。

:::

:::corollary "kerodon_5_2_4_4" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_4_4_4, kerodon_4_4_5_3, kerodon_4_5_3_31, kerodon_4_5_5_4, kerodon_4_5_5_8, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_2_2_4, kerodon_5_2_2_8, kerodon_5_2_4_1")
Kerodon Corollary 5.2.4.4（[Tag 046W](https://kerodon.net/tag/046W)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：標準 collage・写像円柱・指定した端点の輸送・反対・通常圏を照合。Δ¹ 上の cocartesian fibration で指定した F が輸送を表すことと、F と id を端に持つ関手 R の条件の同値。標準 collage の端点公式は任意の U,F の判定を与えない。

:::

:::proposition "kerodon_5_2_4_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_relativeJoinCylinderComparison, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison")
Kerodon Proposition 5.2.4.5（[Tag 024R](https://kerodon.net/tag/024R)）。対応表の状態：本体にある。

仮定：任意の単体集合の射 f:X→Y（Kerodon と一致）。結論：prism の終端と f の厳密な押し出しから relativeJoin f (id Y) への比較が前合成同値（一致）。

:::

:::proposition "kerodon_5_2_4_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.fatJoinPoint_isPushout, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.fatJoinPointPrism_isPushout, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_fatJoinComparison_point")
Kerodon Example 5.2.4.6（[Tag 024S](https://kerodon.net/tag/024S)）。対応表の状態：一部。

X=Δ⁰に制限すればisPrecompositionEquivalence\_fatJoinComparison\_pointは原文の同じfat joinから通常joinへの比較の圏同値性を直接返す。任意Xの厳密pushoutの型だけは数えない。

:::

:::corollary "kerodon_5_2_4_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderMap_isPrecompositionEquivalence, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_relativeJoinCylinderComparison, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison_naturality") (uses := "kerodon_1_1_0_6, kerodon_4_5_5_9, kerodon_5_2_4_5")
Kerodon Corollary 5.2.4.7（[Tag 0357](https://kerodon.net/tag/0357)）。対応表の状態：一部。

Y′=Yで右縦射が恒等の場合、relativeJoinCylinderComparison\_naturalityは同じ二つの比較と誘導射の可換式を返す。写像円柱の誘導射と両比較の前合成同値を二対三で移せば、原文の同じrelativeJoinLeftMapの圏同値を直接得る。任意の右縦射の自然性は含まない。

:::

# 5.2.5 The Homotopy Transport Representation

%%%
number := false
tag := "kerodon-5-2-5"
%%%

Kerodon [Tag 01VT](https://kerodon.net/tag/01VT)

:::proposition "kerodon_5_2_5_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IsEdgeTransport.comp, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport_composition_iso") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_2_4, kerodon_5_1_4_1")
Kerodon Proposition 5.2.5.1（[Tag 01VU](https://kerodon.net/tag/01VU)）。対応表の状態：一部。

底を準圏に強めるとIsEdgeTransport.compは任意に与えた二つの輸送の合成を同じ長辺の輸送と直接返す。一般の単体集合の底は含まない。

:::

:::definition "kerodon_5_2_5_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.homotopyTransport, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.homotopyTransport_unique") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_2_2_5, kerodon_5_2_2_9, kerodon_5_2_5_1")
Kerodon Construction 5.2.5.2（[Tag 019U](https://kerodon.net/tag/019U)）。対応表の状態：一部。

底を準圏に強めればhomotopyTransportとそのuniqueは原文と同じfiber・辺の輸送を値とするhQCat値の関手と一意性を直接与える。

:::

:::definition "kerodon_5_2_5_7"
Kerodon Construction 5.2.5.7（[Tag 019Z](https://kerodon.net/tag/019Z)）。対応表の状態：なし。

op側のcocartesian構造と共変homotopyTransportはあるが、原文のhCの反対から元のfiberへ値を取る反変関手との比較がない。別の対象の共変関手だけでは数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cartesianFibration_op_toCocartesianHornFibration`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.homotopyTransport`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.homotopyTransport_map_isTransport`

:::

# 5.2.6 Elements of Set-Valued Functors

%%%
number := false
tag := "kerodon-5-2-6"
%%%

Kerodon [Tag 01Q7](https://kerodon.net/tag/01Q7)

:::definition "kerodon_5_2_6_1" (lean := "CategoryTheory.Functor.Elements")
Kerodon Construction 5.2.6.1（[Tag 01Q8](https://kerodon.net/tag/01Q8)）。対応表の状態：Mathlib にある。

仮定：通常の圏 C と集合値の関手 F（Kerodon と一致）。結論：Elements F は対象 (c,x)、射は F(f)(x)=y の証拠付きの f:c→d。π が底の c,f を取る（一致）。

:::

:::definition "kerodon_5_2_6_2" (lean := "CategoryTheory.Functor.Elements.costructuredArrowYonedaEquivalence")
Kerodon Variant 5.2.6.2（[Tag 01Q9](https://kerodon.net/tag/01Q9)）。対応表の状態：Mathlib にある。

仮定：通常の圏 C と前層 F:Cᵒᵖ→Type（Kerodon と一致）。結論：(Elements F)ᵒᵖ と CostructuredArrow yoneda F の同値。反対圏を取ると射の条件は F(f)(y)=x（一致）。

:::

:::proposition "kerodon_5_2_6_8"
Kerodon Proposition 5.2.6.8（[Tag 01QF](https://kerodon.net/tag/01QF)）。対応表の状態：なし。

elementsFunctorとGrothendieck.functorは関手の構成。原文のOver Cへの充満忠実性を結論しないため証明の材料にとどまる。

宣言：`CategoryTheory.Functor.elementsFunctor`、`CategoryTheory.Grothendieck.functor`

:::

# 5.2.7 Covering Space Theory

%%%
number := false
tag := "kerodon-5-2-7"
%%%

Kerodon [Tag 01QG](https://kerodon.net/tag/01QG)

:::theorem "kerodon_5_2_7_1" (lean := "IsCoveringMap.monodromyFunctor, IsCoveringMap.monodromy_bijective")
Kerodon Theorem 5.2.7.1（[Tag 027R](https://kerodon.net/tag/027R)）。対応表の状態：一部。

monodromyFunctorは原文の分類関手の対象部分、すなわち各被覆からπ≤1(S)上のSet値のモノドロミー表現を直接作る。被覆間の射を含む分類関手全体と圏同値は含まない。

:::

:::proposition "kerodon_5_2_7_2"
Kerodon Proposition 5.2.7.2（[Tag 027V](https://kerodon.net/tag/027V)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Set 値圏 of elements・covering と基本群oid・Space 値の特例を照合。left covering が hC 上の Set 値 transport の Grothendieck 構成の nerve の pullback に同型。Space 値 unstraightening の同値は離散構成との厳密な同型ではない。

:::

:::corollary "kerodon_5_2_7_3"
Kerodon Corollary 5.2.7.3（[Tag 027W](https://kerodon.net/tag/027W)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Set 値圏 of elements・covering と基本群oid・Space 値の特例を照合。LCov\_C と Fun(hC,Set) の通常圏同値。left fibration の ∞ 圏分類では値域が Space である。

:::

:::corollary "kerodon_5_2_7_4"
Kerodon Corollary 5.2.7.4（[Tag 027X](https://kerodon.net/tag/027X)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Set 値圏 of elements・covering と基本群oid・Space 値の特例を照合。left covering の pullback・一意持ち上げ等による同値条件。左ホーンに対する LeftFibration は一意性を求めない。

:::

:::corollary "kerodon_5_2_7_5"
Kerodon Corollary 5.2.7.5（[Tag 01R0](https://kerodon.net/tag/01R0)）。対応表の状態：なし。

grothendieckTypeToCatは二つの通常圏の構成の比較同値。原文のCat\_\{/C\}への充満忠実性とleft/right coveringによる本質的像の判定を直接述べない。

宣言：`CategoryTheory.Grothendieck.grothendieckTypeToCat`

:::

:::corollary "kerodon_5_2_7_6"
Kerodon Corollary 5.2.7.6（[Tag 027Z](https://kerodon.net/tag/027Z)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Set 値圏 of elements・covering と基本群oid・Space 値の特例を照合。Kan 複体上の covering と基本群oid の Set 値関手の通常圏同値。Space 値分類や projection\_isCovering の個別構成はこの同値を与えない。

:::

# 5.2.8 Parametrized Covariant Transport

%%%
number := false
tag := "kerodon-5-2-8"
%%%

Kerodon [Tag 02RL](https://kerodon.net/tag/02RL)

:::definition "kerodon_5_2_8_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.parametrizedFiberTransport, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.fiberTransportFamily") (uses := "kerodon_1_1_0_6, kerodon_5_1_1_1, kerodon_5_1_4_1")
Kerodon Definition 5.2.8.1（[Tag 02RM](https://kerodon.net/tag/02RM)）。対応表の状態：一部。

left fibrationに制限するとFiberTransportFamilyのprism・start・finish・over\_baseとparametrizedFiberTransportが原文の同じ区間写像空間をパラメータとする輸送を構成する。全辺がcocartesianなので点ごとの条件も直接満たす。

:::

:::proposition "kerodon_5_2_8_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.parametrizedFiberTransport") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_2_2_13")
Kerodon Proposition 5.2.8.4（[Tag 02RQ](https://kerodon.net/tag/02RQ)）。対応表の状態：一部。

left fibrationに制限するとparametrizedFiberTransportFamilyのprismと両端・底の等式が原文の輸送の存在を直接与える。任意の同型な候補についてのiffは含まない。

:::

:::definition "kerodon_5_2_8_6" (uses := "kerodon_1_1_0_6, kerodon_5_1_4_1, kerodon_5_2_8_4")
Kerodon Variant 5.2.8.6（[Tag 02RS](https://kerodon.net/tag/02RS)）。対応表の状態：なし。

引用はop側のfibrationと非パラメーターのホモトピー圏の共変輸送。原文の元のHom空間からfiber間の関手空間への反変の射を直接構成しない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cartesianFibration_op_toCocartesianHornFibration`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.homotopyTransport_map_edge`

:::

:::proposition "kerodon_5_2_8_7" (uses := "kerodon_1_4_0_1, kerodon_4_6_8_5, kerodon_4_6_8_9, kerodon_5_2_8_1")
Kerodon Proposition 5.2.8.7（[Tag 02GT](https://kerodon.net/tag/02GT)）。対応表の状態：なし。

cosliceTransportPointHomはホモトピー圏の点の作用、coherentCompositionReverseTransport\_parametrizedIsoは反対向きのcoherent nerveの比較。原文のConstruction 4.6.8.9の同じ合成射との比較がなく、別模型の類似だけは数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceTransportPointHom`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.coherentCompositionReverseTransport_parametrizedIso`

:::

:::proposition "kerodon_5_2_8_8" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_6_8_1, kerodon_4_6_8_9, kerodon_5_1_4_1, kerodon_5_1_4_13, kerodon_5_2_2_10, kerodon_5_2_2_13")
Kerodon Proposition 5.2.8.8（[Tag 02GU](https://kerodon.net/tag/02GU)）。対応表の状態：なし。

parametrizedFiberTransportと各辺での比較だけでは、原文の二つのパラメーターを持つ合成四角の可換性を直接返さない。合成を結ぶ型が要る。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.parametrizedFiberTransport`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.parametrizedFiberTransport_at_edgeIso`

:::

:::definition "kerodon_5_2_8_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.homotopyTransport, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.homotopyTransport_map_isTransport") (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_6_8_13, kerodon_5_1_4_1, kerodon_5_2_2_5, kerodon_5_2_5_2, kerodon_5_2_8_4, kerodon_5_2_8_8")
Kerodon Construction 5.2.8.9（[Tag 02GW](https://kerodon.net/tag/02GW)）。対応表の状態：一部。

底準圏上のhomotopyTransportは原文が最後に指定するunderlying ordinary functorの構成を直接与え、その辺での作用も一致する。hKan豊穣のHom作用・合成の整合性は含まない。

:::

:::definition "kerodon_5_2_8_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.parametrizedFiberTransport") (uses := "kerodon_1_4_0_1, kerodon_5_2_8_9")
Kerodon Variant 5.2.8.11（[Tag 02RW](https://kerodon.net/tag/02RW)）。対応表の状態：一部。

parametrizedFiberTransportは原文の豊穣関手の各Hom作用、すなわち同じ区間HomからKanなfiber間の関手空間への射を直接与える。豊穣関手の合成・単位を束ねる主張は含まない。

:::

:::definition "kerodon_5_2_8_12" (uses := "kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_5_2_8_6, kerodon_5_2_8_9")
Kerodon Variant 5.2.8.12（[Tag 02GX](https://kerodon.net/tag/02GX)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：反対圏の辺の輸送・一点と写像空間の評価・豊穣と通常の hCを照合。cartesian fibration の op から作る hQCat 豊穣反変 transport の一意性。op のファイブレーション性と通常の hTr の一意性からは豊穣な型が得られない。

:::

