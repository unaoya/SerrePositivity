import Verso
import VersoManual
import VersoBlueprint
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Logic.Equiv.Prod
import SerrePositivity.InfinityCategories.HA.Section4_1_2.BarVertexInclusion
import SerrePositivity.InfinityCategories.HA.Section5_2_2.ClassifiedConeLimit
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalOppositeFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalVertices
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.YonedaInfinityConstruction
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseSubdivision
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.LeftFibration
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.SourceInitial
import SerrePositivity.KST.Comparison.GroupCompletion

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 5.2 Bar Constructions and Koszul Duality" =>
%%%
number := false
tag := "ha-5-2"
%%%

HA 5.2 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 5.2.1 Twisted Arrow ∞-Categories

%%%
number := false
tag := "ha-5-2-1"
%%%

:::definition "ha_5_2_1_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight")
*HA 構成 5.2.1.1*　twisted arrow ∞ 圏の構成（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=804)）。対応表の状態：本体にある。

*主張*　単体集合 $`C` のねじれ矢印単体集合は、順序和 $`[n]\star[n]^{\mathrm{op}}` による引き戻しで定義され、$`n` 単体は $`C` の $`(2n+1)` 単体である。

仮定：単体集合 C（HA と一致）。結論：join の重みからの射を前合成して twisted arrow の単体集合を構成する（HA と一致する双対版）。本体の重みは \[n\]op⋆\[n\] の左版で、単体の添字を反転した反対単体集合が HA の \[n\]⋆\[n\]op の右版となる。

二つの順序を貼り合わせると $`[2n+1]` になる。頂点は一本の辺であり、高次単体には始域側の順方向の列と終域側の逆方向の列が現れる。

:::

:::proposition "ha_5_2_1_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection_leftFibration, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrow_quasicategory, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalLeftFibration_op_rightFibration")
*HA 命題 5.2.1.3*　twisted arrow 射影の right fibration 性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=805)）。対応表の状態：本体にある。

*主張*　準圏 $`C` のねじれ矢印圏から $`C\times C^{\mathrm{op}}` への標準射は右ファイブレーションであり、ねじれ矢印圏自身も準圏である。

仮定：準圏 C（HA と一致）。結論：本体の Tw(C)→Cop×C は left fibration であり Tw(C) は準圏となる。全射を単体的に反転すると HA の TwArr(C)→C×Cop の right fibration と準圏性になる（左右の規約を反転した HA の主張と一致）。

標準射はそれぞれの順序部分への制限である。辺 $`x\to y` は $`(x,y)` の上にあり、二つの変数における反変・共変な写像空間をこの右ファイブレーションで表す。

:::

:::definition "ha_5_2_1_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration")
*HA 定義 5.2.1.5*　Twisted Arrow ∞-Categories (p. 807)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=807)）。対応表の状態：本体にある。

*主張*　∞ 圏のペアリングとは、二つの ∞ 圏 $`C,D` と、その積への右ファイブレーション $`M\to C\times D` の組である。

原文が与えた準圏C,Dと同じλ:M→C×DにRightFibration λを課せば、pairingの定義全体と一致する。λ以外の同じ対象の構成や選択は追加しない。

この右ファイブレーションは $`C^{\mathrm{op}}\times D^{\mathrm{op}}` 上の空間値関手で分類される。二対象での値はその上のファイバーとなる。

:::

:::proposition "ha_5_2_1_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection_leftFibration, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalLeftFibration_op_rightFibration")
*HA 例 5.2.1.7*　twisted arrow の pairing（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=807)）。対応表の状態：本体にある。

*主張*　ねじれ矢印圏から $`C\times C^{\mathrm{op}}` への右ファイブレーションはペアリングの例である。

仮定：準圏 C（HA と一致）。結論：Tw の両端射影が left fibration であり、その反対の射影が right fibration となる（HA の典型 pairing の性質と一致する双対版）。一般の CPair の対象をまとめる型についての主張は含めない。

第一成分と第二成分を、それぞれ辺の始域と終域として取る。固定した対の上のファイバーがその対の写像空間を表す。

:::

:::definition "ha_5_2_1_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices")
*HA 定義 5.2.1.8*　Twisted Arrow ∞-Categories (p. 807)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=807)）。対応表の状態：一部（component）。

*主張*　ペアリングの対象は $`C` 側のファイバーで終対象なら左普遍、$`D` 側のファイバーで終対象なら右普遍である。

同じ射影M→CのvertexFiberとそのIsTerminalVertexは、原文のleft universal object条件そのものを直接表す。M→Dについても同様。CPair内での関手の分類・representabilityを保証する定理ではない。

各対象の上に該当する普遍対象が存在する場合、左または右表現可能という。普遍な対象に絞った充満部分圏をそれぞれ $`M_L,M_R` と書く。

:::

:::proposition "ha_5_2_1_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceIdentity_isInitialVertex, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceIdentity_projection")
*HA 命題 5.2.1.10*　pairing の universal 対象と同値射（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=807)）。対応表の状態：一部（special）。

*主張*　ねじれ矢印圏のペアリングは左右とも表現可能であり、左右いずれの意味でも、普遍対象であることは対応する辺が同値であることと同値である。

同じCの恒等射id\_xに制限すると、twistedArrowSourceIdentity\_isInitialVertexとprojectionが（原文との反対の規約で）該当fiberの普遍対象を与える。任意の射の(a)⇔(b)⇔(c)や両側の全representabilityは含まない。

各対象には恒等射を選べるため、左右それぞれ表現対象が存在する。同値な辺は固定した成分のファイバーの中で恒等射と比較できる。

:::

:::proposition "ha_5_2_1_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowHomInfinity, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap_uncurry")
*HA 命題 5.2.1.11*　twisted arrow の分類と Yoneda（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=810)）。対応表の状態：一部（stronger-hyp）。

*主張*　ねじれ矢印圏の右ファイブレーションを分類する $`C^{\mathrm{op}}\times C\to\mathcal S` を一方でカリー化した $`C\to\operatorname{Fun}(C^{\mathrm{op}},\mathcal S)` は、米田埋め込みにホモトピックである。

KB-W2型再照合：仮定：準圏 C と、本体が Tw の射影を straighten して選んだ分類図式 χ（Lean が強い：この指定 χ の場合。HA と左右双対の規約）。結論：χ の共同評価を curry した写像が構成済み Yoneda 写像であり、uncurry の等式が成立する（この選択での HA の比較の部分に一致）。任意の別の分類図式 χ に対する比較の独立性は含まれない。

$`y` に対応する前層は $`x\mapsto\operatorname{Map}_C(x,y)` である。ここでの比較は各対象の値とその自然性を一緒に含む。

:::

# 5.2.2 The Bar Construction for Associative Algebras

%%%
number := false
tag := "ha-5-2-2"
%%%

:::definition "ha_5_2_2_20" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration")
*HA 定義 5.2.2.20*　The Bar Construction for Associative Algebras (p. 829)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=829)）。対応表の状態：一部（component）。

*主張*　$`O` モノイダル ∞ 圏のペアリングは、二つの圏の $`O^\otimes` 上の積への圏論的ファイブレーションである $`O` モノイダル関手で、各色で右ファイブレーションになるものである。

原文が既に与えた同じλ⊗について、EquivalenceLiftingはcategorical fibrationという条件を直接表す。各色のfiberでのRightFibrationも同じ述語で表す。O-monoidal functor構造の構成・辺保存の比較は含まない。

全体では演算に沿う余デカルト移送を保つことを課し、各色のファイバーでは通常の ∞ 圏のペアリングを得る。

:::

:::corollary "ha_5_2_2_39" (lean := "SerrePositivity.InfinityCategories.HA.Section5_2_2.exists_classifiedLimitCone, SerrePositivity.InfinityCategories.HA.Section5_2_2.classifiedCone_isLimit")
*HA 系 5.2.2.39*　right fibration の相対余極限の判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=837)）。対応表の状態：一部（direction）。

*主張*　右ファイブレーション上で、底の余錐を相対余極限へ延ばせることは、分類する反変空間値関手がその底の余錐を極限に送ることと同値である。

KB-W2型再照合：仮定：準圏 B、空間値 F:B→S と指定した小さい left unstraightening、底の極限錐と F による像の極限性（Lean が強い：この選択した分類模型と底で極限となる場合）。結論：任意の持ち上げた始域図式に、底の同じ錐を厳密に保つ全空間の極限錐が存在する。反対を取ると HA の right fibration の (2)⇒(3) の向きに一致する。一般の f への比較と (1)・(2) の同値の逆向きは含まれない。

余錐の底を固定し、そこに与えられた持ち上げをすべて検査する。底の余錐が余極限余錐なら、全体でも余極限となり、その像も余極限となるよう延長できるという条件が同値になる。

:::

# 5.2.4 Reduced Pairings

%%%
number := false
tag := "ha-5-2-4"
%%%

:::definition "ha_5_2_4_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration")
*HA 定義 5.2.4.1*　Reduced Pairings (p. 849)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=849)）。対応表の状態：一部（component）。

*主張*　ペアリングが被約であるとは、両側に始対象があり、それぞれで片側を固定した右ファイブレーションが自明 Kan ファイブレーションとなることである。

原文の同じM→C,M→Dの単位点でのvertexFiberの射影にTrivialKanFibrationを適用すると、reduced条件(b)の二つの自明Kan条件を直接表す。weakly reduced条件の全体・CPair上の構成は含まない。

弱被約では、全体に始対象があり、その両側への像も始対象であることを要求する。被約性を検査するのは、始対象で取った左右二つの制限である。

:::

:::proposition "ha_5_2_4_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan")
*HA 注意 5.2.4.2*　reduced pairing の単位 fiber の可縮性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=849)）。対応表の状態：一部（component）。

*主張*　被約なペアリングでは、両側の始対象の対の上のファイバーは可縮 Kan 複体であり、その任意の頂点は全体の始対象になる。

KB-W2型再照合：仮定：reduced pairing の片側の単位 fiber の射影が trivial Kan fibration（HA の仮定 (b) と一致）。結論：その射影のもう一方の単位点での fiber が可縮 Kan となる（原典冒頭の二つの単位を固定した fiber の可縮性に一致する部分）。全空間 M におけるその点の始対象性と weakly reduced 性は含まれない。

従って被約なペアリングは弱被約でもある。可縮性は片側の始対象で制限した自明 Kan ファイブレーションから得る。

:::

# 5.2.6 Iterated Loop Spaces

%%%
number := false
tag := "ha-5-2-6"
%%%

*spectra-k-theory.html — 4. 連結 K 理論 II：群完備化*

$$`\mathcal A\ \rightsquigarrow\ (\mathcal A^{\simeq},\oplus)\in\mathrm{CMon}(\mathcal S)\ \rightsquigarrow\ (\mathcal A^{\simeq})^{\mathrm{gp}}\in\mathrm{CMon}^{\mathrm{gp}}(\mathcal S)\ \overset{\sim}{\rightsquigarrow}\ K(\mathcal A)\in\mathrm{Sp}_{\ge0}\qquad(\mathcal A\text{ は加法的}).`

*spectra-k-theory.html — 4. 連結 K 理論 II：群完備化 — Step 1：$`E_\infty` 空間*

$`\mathrm{CMon}(\mathcal S)`：∞ 関手 $`M\colon\mathrm{Fin}_*\to\mathcal S` で Segal 写像 $`M\langle n\rangle\to M\langle1\rangle^n` が同値なもの（補章 6-2）。有限積を持つ ∞ 圏は積で一意に対称モノイダルになり、core は右随伴で積を保つので $`\langle n\rangle\mapsto(\mathcal A^{\simeq})^n` が Segal 条件を満たす。例：$`\mathrm{Proj}_R^{\simeq}\simeq\coprod_{[P]}B\mathrm{Aut}(P)`、自由加群なら $`\coprod_nBGL_n(R)`。

*spectra-k-theory.html — 4. 連結 K 理論 II：群完備化 — Step 2：群完備化 ＝ bar 構成の実現のループ*

$$`M^{\mathrm{gp}}\simeq\Omega BM,\qquad BM:=\operatorname*{colim}_{\Delta^{\mathrm{op}}}\bigl([n]\mapsto M^n\bigr).`

$`[n]\mapsto M^n` は $`M` を $`\Delta^{\mathrm{op}}\to\mathrm{Fin}_*` に沿って引き戻したもの。胞体：点 1 つ、元ごとのループ、$`(a,b)` ごとの三角形（辺 $`a,a+b,b`）。$`\pi_1BM=\pi_0(M)^{\mathrm{gp}}`。群完備化定理 $`H_*(M^{\mathrm{gp}})\cong H_*(M)[\pi_0^{-1}]`（McDuff–Segal、Quillen）から $`M^{\mathrm{gp}}\simeq K_0(R)\times BGL(R)^+`。

*spectra-k-theory.html — 4. 連結 K 理論 II：群完備化 — Step 3：$`\mathrm{CMon}^{\mathrm{gp}}(\mathcal S)\simeq\mathrm{Sp}_{\ge0}`*

$`BM` も $`E_\infty` なので反復でき、$`(M^{\mathrm{gp}},BM,B^2M,\dots)` が $`\Omega` スペクトル（$`S_\bullet` の反復と並行）。逆は $`\Omega^\infty`。認識原理（May、Segal、Boardman–Vogt）、∞ 版は Gepner–Groth–Nikolaus が $`\mathrm{Pr}^L` の普遍性から証明。

:::proposition "ha_5_2_6_3" (lean := "Equiv.prodCongrRight, Equiv.prodCongrLeft, Equiv.mulLeft, Equiv.mulRight")
*HA 例 5.2.6.3*　Iterated Loop Spaces (p. 872)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=872)）。対応表の状態：一部（direction）。

*主張*　集合の圏のモノイドが群的であることは、$`(x,y)\mapsto(x,xy)` と $`(x,y)\mapsto(xy,y)` がともに全単射となることと同値であり、これは群であることに等しい。

原文が明示する通常のmonoid Gについて、群の場合はprodCongrRight (fun x↦Equiv.mulLeft x)とprodCongrLeft (fun y↦Equiv.mulRight y)が同じ二写像(x,y)↦(x,xy),(xy,y)の全単射を直接与える。二写像の全単射性から群の逆元を作る逆向きは含まない。

二つの全単射は、左乗法と右乗法について一方の因子を一意に解けることを表す。積を単位に指定すると、各元の逆元が得られる。

:::

:::proposition "ha_5_2_6_14" (lean := "SerrePositivity.KST.Comparison.monoidBar, SerrePositivity.KST.Comparison.monoidBarBasepoint, SerrePositivity.KST.Comparison.constantMonoidBarIso")
*HA 例 5.2.6.14*　離散群の Bar と分類空間 BG（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=874)）。対応表の状態：一部（component）。

*主張*　離散群を空間内の群的 $`E_1` モノイドとして見たとき、その一重 bar 構成は点付き分類空間 $`BG` である。

KB-W2型再照合：仮定：離散群 G を定数単体的モノイドとして与える（HA と一致する離散群）。結論：各次数の一対象圏の nerve の対角とその唯一の零単体を使うので、通常の BG とその基点を得る（原典の通常の分類空間という対象の構成に一致）。HA の E₁ 代数の普遍的 Bar との比較宣言は含まれない。

単体的 bar の各段は群の有限直積である。群の積と単位で面・退化写像を作って実現すると、通常の分類空間になる。

:::

