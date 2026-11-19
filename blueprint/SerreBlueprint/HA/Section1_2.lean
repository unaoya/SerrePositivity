import Verso
import VersoManual
import VersoBlueprint
import Mathlib.Algebra.Homology.Embedding.Basic
import Mathlib.Algebra.Homology.Embedding.TruncLE
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.AlgebraicTopology.DoldKan.Equivalence
import Mathlib.AlgebraicTopology.DoldKan.EquivalencePseudoabelian
import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
import Mathlib.AlgebraicTopology.DoldKan.Normalized
import Mathlib.AlgebraicTopology.MooreComplex
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import Mathlib.CategoryTheory.Triangulated.TStructure.Basic
import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.NormalizedChains
import SerrePositivity.InfinityCategories.HA.Section1_2_3.MappingHomotopyGroups
import SerrePositivity.InfinityCategories.HA.Section1_2_4.DGIdempotentCompleteGeneral
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Bicartesian
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberConnecting
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Triangulated
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TriangulatedInstance
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWChainMap
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AlexanderWhitney
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ChainTensorVanishing
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DoldKanIso
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NormalizedAlexanderWhitney
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.LocalStrongSaturation
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalVertices
import SerrePositivity.KST.LocalizingInvariants.StableFunctorMaps
import SerrePositivity.KST.SConstruction.CoreSimplicial
import SerrePositivity.KST.SConstruction.FirstRowFibration
import SerrePositivity.KST.SConstruction.Gapped

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 1.2 Stable ∞-Categories and Homological Algebra" =>
%%%
number := false
tag := "ha-1-2"
%%%

HA 1.2 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 1.2.1 t-Structures on Stable ∞-Categories

%%%
number := false
tag := "ha-1-2-1"
%%%

:::definition "ha_1_2_1_1" (lean := "CategoryTheory.Triangulated.TStructure")
*HA 定義 1.2.1.1*　三角圏の t 構造（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=37)）。対応表の状態：Mathlib にある。

*主張*　三角圏の $`t` 構造は、移動に閉じた上下の部分圏で直交性を持ち、各対象を上側の項と一段下げた下側の項の三角形に分解できるものである。

仮定：加法的な整数シフトを持つ三角圏（Lean が弱い：前三角圏で定義できる）。結論：両側の充満部分圏、シフトへの閉性、直交性、任意の対象の切断三角形を備える。Mathlib の添字はコホモロジー式なので le と ge を反転して一致。

具体的には $`\operatorname{Hom}(D_{\ge0},D_{\le-1})=0`、$`D_{\ge0}[1]\subseteq D_{\ge0}`、$`D_{\le0}[-1]\subseteq D_{\le0}` を要求する。任意の $`X` の切断三角形は $`X'\to X\to X''` で $`X'\in D_{\ge0}`、$`X''\in D_{\le-1}` とする。

:::

:::definition "ha_1_2_1_2" (lean := "CategoryTheory.Triangulated.TStructure.isLE_shift_iff, CategoryTheory.Triangulated.TStructure.isGE_shift_iff")
*HA 記法 1.2.1.2*　t 構造のホモロジー的添字（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=37)）。対応表の状態：Mathlib にある。

*主張*　ホモロジー次数の約束で、$`D_{\ge n}=D_{\ge0}[n]`、$`D_{\le n}=D_{\le0}[n]` と書く。

仮定：t 構造と整数シフト（HA と一致）。結論：シフトで le・ge の添字を移す同値を与える。Mathlib の次数を符号反転すれば HA のホモロジー式添字と一致。

整数 $`n` による添字の変更を、三角圏の移動そのもので表す。

:::

:::proposition "ha_1_2_1_3" (lean := "CategoryTheory.Triangulated.TStructure.isLE_iff_orthogonal, CategoryTheory.Triangulated.TStructure.isGE_iff_orthogonal")
*HA 注意 1.2.1.3*　直交性による t 構造の片側の決定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=37)）。対応表の状態：Mathlib にある。

*主張*　$`t` 構造の片方の部分圏は他方を決める。例えば $`D_{\le-1}` は $`D_{\ge0}` からの Hom がすべて零になる対象の圏である。

仮定：t 構造と隣接する整数次数（HA と一致）。結論：反対側との Hom の消滅によって各側の所属を判定し、一方が他方を決める（一致）。

直交性が一方の包含を与え、切断三角形が逆を与える。反対側も同じように直交条件から取り出せる。

:::

:::definition "ha_1_2_1_4" (lean := "CategoryTheory.Triangulated.TStructure, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isTriangulated_ho, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices") (uses := "ha_1_1_1_9, htt_1_1_2_4")
*HA 定義 1.2.1.4*　安定 ∞ 圏の t 構造（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=38)）。対応表の状態：本体にある。

*主張*　安定 ∞ 圏の $`t` 構造とは、そのホモトピー圏の $`t` 構造である。

同じhCのTStructureを取り、fullSubcomplexOnVerticesにt.le nおよびt.ge nをhCの頂点へ代入すれば、原文のt構造と二つの全部分準圏の定義全体を直接表す。専用のまとめた名称は不要。

各次数の上側と下側は、ホモトピー圏で該当する部分圏に入る対象からなる充満 ∞ 部分圏として扱う。

:::

:::definition "ha_1_2_1_11" (lean := "CategoryTheory.Triangulated.TStructure.heart, CategoryTheory.Triangulated.TStructure.hasHeartFullSubcategory, CategoryTheory.Triangulated.TStructure.truncGELEIsoLEGE, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices")
*HA 定義 1.2.1.11*　t 構造のハートとホモトピー対象（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=40)）。対応表の状態：一部（component）。

*主張*　安定 ∞ 圏の $`t` 構造の心は $`C_{\ge0}\cap C_{\le0}` であり、$`\pi_n(X)` は $`X[-n]` の両側零次切断である。

t.heartの頂点述語を同じCのfullSubcomplexOnVerticesへ入れれば、原文のC≥0∩C≤0という同じ全部分準圏の構成成分を直接与える。πnという∞関手の構成は含まない。

$`\pi_0` は $`\tau_{\le0}\tau_{\ge0}` または標準同値を通じて $`\tau_{\ge0}\tau_{\le0}` として得られる。値は心の対象になる。

:::

:::definition "ha_1_2_1_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.IsStronglySaturatedEdgeSetOfShapes")
*HA 定義 1.2.1.14*　射の準飽和類（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=41)）。対応表の状態：一部（stronger-hyp）。

*主張*　押し出しを持つ ∞ 圏の準飽和類とは、同値を含み、押し出しと二つから三つの規則で閉じた射の類である。

同じ辺集合SにIsStronglySaturatedEdgeSetOfShapesも与えると、そのfieldsは同じ準圏の可逆辺包含・2-of-3・pushout安定性という原文の準飽和条件を直接返す。小arrow余極限閉性を加えない全定義と最小閉包は含まない。

準飽和類は任意の交叉で閉じるため、射の族を含む最小の準飽和類を取れる。ここでの定義には矢印圏における小余極限全般の条件を課していない。

:::

:::definition "ha_1_2_1_15" (lean := "CategoryTheory.ObjectProperty.IsClosedUnderExtensions, CategoryTheory.Triangulated.TStructure.isLE₂, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle_mem_cofiberDistinguishedTriangles")
*HA 定義 1.2.1.15*　拡大で閉じた部分圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=42)）。対応表の状態：一部（special）。

*主張*　安定 ∞ 圏の充満部分圏が拡大で閉じているとは、ファイバー列の両端が部分圏に属すれば中央も属することである。

C0を同じhCのt構造のt.le nの頂点で張る全部分準圏に限ると、cofiberTriangle\_memとisLE₂は同じfiber/cofiber列の中項の所属を直接返す。任意のC0の定義全体と局所化の準飽和性の付記は含まない。

条件を適用する図式は $`X\to Y\to Z` で、$`X,Z` の所属から $`Y` の所属を結論する。この用語で $`t` 構造の部分圏の閉性を記述できる。

:::

# 1.2.2 Filtered Objects and Spectral Sequences

%%%
number := false
tag := "ha-1-2-2"
%%%

:::definition "ha_1_2_2_2" (lean := "SerrePositivity.KST.SConstruction.IsGapped, SerrePositivity.KST.SConstruction.sConstruction")
*HA 定義 1.2.2.2*　順序集合で添字付けた区間複体（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=47)）。対応表の状態：一部（special）。

*主張*　全順序集合 $`I` 上の複体は、区間の両端 $`(i,j)` の図式で、対角が零であり、$`i\le j\le k` で $`F(j,k)` が $`F(i,j)\to F(i,k)` の余ファイバーとなるものである。

KB-W2型再照合：仮定：点付き準圏と有限全順序 \[n\]（Lean が強い：HA の I は任意の全順序）。結論：Ar の対角を零にし、順序付き三点の所定の正方形に押し出しを要求し、その充満部分複体を作る（有限の場合は一致）。

区間の対は両端を同時に比較する半順序をなす。指定の押し出し四角形は、区間を切り分ける際の余ファイバーの整合性を表す。これらの図式の充満部分圏を $`\operatorname{Gap}(I,C)` と書く。

:::

:::proposition "ha_1_2_2_3" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting")
*HA 注意 1.2.2.3*　区間複体からホモトピー圏の鎖複体へ（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=47)）。対応表の状態：一部（component）。

*主張*　安定 ∞ 圏の $`\mathbb Z`-複体から、隣接区間を移動し、接続射を微分とするホモトピー圏の鎖複体が得られる。

KB-W2型再照合：仮定：安定準圏の一つの余ファイバー列（HA の隣接区間から作る列に適用可能）。結論：hC で余ファイバーから懸垂への境界射。すべての区間の境界をシフトでつないだ鎖複体と二乗零性は型に含まれない（Lean が弱い）。

次数 $`n` の項は $`F(n-1,n)[-n]` である。二つの隣接する接続射の合成は対角の零対象を経由するため、微分の平方が零になる。

:::

:::lemma_ "ha_1_2_2_4" (lean := "SerrePositivity.KST.SConstruction.firstRowEquivalence")
*HA 補題 1.2.2.4*　最小元を加えた区間複体とフィルター付き図式（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=48)）。対応表の状態：一部（stronger-hyp）。

*主張*　点付きで押し出しを持つ ∞ 圏では、最小元 $`-\infty` を持つ全順序上の複体を区間 $`(-\infty,i)` に制限すると、残りの順序上の図式の圏と同値になる。

KB-W2型再照合：仮定：有限全順序 \[n\] と安定準圏 C（Lean が強い：HA は任意の全順序と点付きかつ押し出しがあればよい）。結論：gapped 図式から始点を固定した第一行の関手圏への制限が準圏同値（有限安定な場合は一致）。

最小元から始まる区間の値を指定すれば、他の区間は対応する二項の余ファイバーとして復元できる。復元は自然変換のデータも含めて圏の同値を与える。

:::

:::proposition "ha_1_2_2_5" (lean := "SerrePositivity.KST.SConstruction.simplicialCoreSConstruction, SerrePositivity.KST.SConstruction.diagonalCoreSConstruction")
*HA 注意 1.2.2.5*　区間複体による Waldhausen K 理論（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=48)）。対応表の状態：一部（component）。

*主張*　点付きで押し出しを持つ ∞ 圏の Waldhausen K 理論の空間は、$`[n]\mapsto\operatorname{Gap}([n],C)^\simeq` の幾何学的実現で与えられる。

KB-W2型再照合：仮定：点付き準圏の gapped 構成（HA の構成に対応）。結論：各 \[n\] の S 構成の core と、その双単体集合の対角を与える。注記の A∞ 環の加群から得る通常の K 理論との比較はこれらの型にない（Lean が弱い）。

各段で複体の圏の最大 Kan 部分複体を取るため、これらは二重単体集合をなす。例えば対角でその実現を表せる。$`A_\infty` 環 $`A` に対し、$`\operatorname{Mod}_A` の $`A` を含む最小の安定部分圏を使うと、環の K 理論を回収する。

:::

:::definition "ha_1_2_2_9" (lean := "SerrePositivity.KST.LocalizingInvariants.stableFunctorCategory, CategoryTheory.Abelian.SpectralObject.spectralSequence")
*HA 定義 1.2.2.9*　フィルター付き対象と付随するスペクトル系列（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=52)）。対応表の状態：一部（component）。

*主張*　安定 ∞ 圏のフィルター付き対象は $`N(\mathbb Z)\to C` であり、$`t` 構造があれば、それが定める区間複体からスペクトル系列を得る。

KB-W2型再照合：仮定：安定準圏と添字の nerve、またはアーベル圏のスペクトル対象。結論：N(Z) を始域とするフィルター付き対象の関手圏を取れ、別途スペクトル対象の系列はある。フィルター付き対象からその入力を作る接続が確認できなかった（Lean が弱い）。

$`\mathbb Z` に最小元を加えてフィルトレーションを区間複体に延ばし、$`\mathbb Z` 内の区間に制限する。その複体に切断で得られるホモロジーを適用して、フィルトレーションのスペクトル系列を作る。

:::

:::definition "ha_1_2_2_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit, CategoryTheory.Limits.HasColimitsOfShape")
*HA 定義 1.2.2.12*　列の余極限と t 構造との両立性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=52)）。対応表の状態：一部（component）。

*主張*　逐次余極限とは非負整数の順序の nerve で添字付けた図式の余極限であり、$`t` 構造がこれと両立するとは $`C_{\le0}` がこれらの余極限で閉じることである。

KB-W2型再照合：仮定：準圏の N(ℕ) 図式または通常圏（HA と同じ形状を取れる）。結論：各図式の余極限の存在および 1 圏で形状の全図式に対する存在を表せる。t 構造の余連結側が列の余極限で閉じるという両立条件は型にない（Lean が弱い）。

両立性を述べる際には全体が安定で逐次余極限を持つと仮定する。閉性を検査するのは $`t` 構造の下側である。

:::

# 1.2.3 The Dold-Kan Correspondence

%%%
number := false
tag := "ha-1-2-3"
%%%

:::definition "ha_1_2_3_1" (lean := "ChainComplex")
*HA 定義 1.2.3.1*　加法圏に値を取る鎖複体（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=54)）。対応表の状態：Mathlib にある。

*主張*　加法圏の鎖複体は整数次数の対象と次数を一つ下げる射の列で、連続する微分の合成が零である。

仮定：零射を持つ圏と次数型（Lean が弱い：加法圏でなくても複体は定義できる）。結論：整数を次数型に取ると対象列と下降微分および二乗零性を持つ鎖複体（一致）。

鎖複体と鎖写像も加法圏をなす。$`\operatorname{Ch}(A)_{\ge n}` は $`n` 未満の項が零、$`\operatorname{Ch}(A)_{\le n}` は $`n` より上の項が零の複体の充満部分圏とする。

:::

:::proposition "ha_1_2_3_2" (lean := "ChainComplex")
*HA 注意 1.2.3.2*　鎖複体のホモロジー的添字（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=54)）。対応表の状態：Mathlib にある。

*主張*　鎖複体の添字はホモロジー次数で取り、微分は次数を一つ下げる。

仮定：零射を持つ圏と次数型（HA は整数）。結論：複体の形状を ComplexShape.down として定め、隣接次数の微分が一つ次数を下げる（一致）。

微分は $`A_n\to A_{n-1}` の向きになる。次数の記法を変える文献と式を比較するときは、この向きを合わせる。

:::

:::proposition "ha_1_2_3_3" (lean := "ChainComplex, ComplexShape.embeddingDownNat")
*HA 注意 1.2.3.3*　非負次数に集中する鎖複体（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=54)）。対応表の状態：Mathlib にある。

*主張*　鎖複体を $`(A_*,d)` と書き、$`A_*` を次数付き対象、$`d` を平方零の次数 $`-1` の射と見る。

仮定：零射を持つ圏（Lean が弱い：加法圏でなくても定義できる）。結論：自然数次数の ChainComplex は負次数を除いた形状を持ち、embeddingDownNat が符号を反転して対応する整数コチェイン形状を与える（一致する添字規約）。

複体を $`A_*` や $`A` と略記する場合も、微分を指定した複体を指す。

:::

:::proposition "ha_1_2_3_4" (lean := "HomologicalComplex.truncLE', HomologicalComplex.truncLE'XIsoCycles, ComplexShape.embeddingDownNat")
*HA 注意 1.2.3.4*　非負次数への切断（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=54)）。対応表の状態：一部（component）。

*主張*　アーベル圏の非負鎖複体の包含は核で作る右随伴 $`\tau_{\ge0}` を持ち、非正鎖複体の包含は余核で作る左随伴 $`\tau_{\le0}` を持つ。

KB-W2型再照合：仮定：アーベル圏の複体、下側の切断を与える形状の埋め込み（HA の非負鎖次数は非正余鎖次数）。結論：切断は境界次数で cycles を取り、内部の次数を保つ。包含の右随伴としての同定は採用した型にない（Lean が弱い）。

右随伴は正次数を残し、零次を $`\ker(d_0)` に取る。左随伴は負次数を残し、零次を $`\operatorname{coker}(d_1)` に取る。どちらの場合も切断境界で微分が整合する。

:::

:::definition "ha_1_2_3_5"
*HA 構成 1.2.3.5*　鎖複体から作る Dold–Kan 単体的対象（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=55)）。対応表の状態：Mathlib にある。

*主張*　Dold–Kan 構成は、非負鎖複体 $`A` を、次数 $`n` の項が全射 $`[n]\twoheadrightarrow[k]` にわたる $`A_k` の直和となる単体的対象へ送る。

仮定：前加法圏に有限余積がある（HA の加法圏の仮定から従う）。結論：非負鎖複体から単体的対象を作る関手で、各次数の項は全射 \[n\]→\[k\] に添字付けられた余積（一致）。

単調写像による構造射は直和の成分の行列で与える。元の全射との合成が目的の全射そのものなら恒等射を取り、その合成が全射の後に始端を除く面を通る指定の成分なら微分を使う。その他の成分は零となる。

宣言：`AlgebraicTopology.DoldKan.Γ₀`、`AlgebraicTopology.DoldKan.Γ₀.Obj.obj₂`

:::

:::theorem "ha_1_2_3_7" (lean := "CategoryTheory.Idempotents.DoldKan.equivalence, CategoryTheory.Idempotents.DoldKan.equivalence_inverse")
*HA 定理 1.2.3.7*　Dold-Kan Correspondence（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=56)）。対応表の状態：一部（component）。

*主張*　Dold–Kan 関手は任意の加法圏で非負鎖複体の圏から単体的対象の圏への充満忠実関手であり、加法圏が冪等完備なら圏の同値である。

KB-W2型再照合：仮定：冪等完備な前加法圏と有限余積（HA の同値を主張する場合に一致）。結論：Γ を逆に持つ鎖複体と単体的対象の圏同値。冪等完備性を外した場合の Γ₀ の充満忠実性は採用した型にない（Lean が弱い）。

単体的対象から鎖複体を取り出すとき、冪等射の分裂が必要な成分を与える。アーベル群では正規化複体が同値の逆を具体的に表す。

:::

:::definition "ha_1_2_3_8" (lean := "AlgebraicTopology.alternatingFaceMapComplex, AlgebraicTopology.alternatingFaceMapComplex_obj_d")
*HA 定義 1.2.3.8*　半単体的対象の交代面写像複体（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=56)）。対応表の状態：一部（stronger-hyp）。

*主張*　加法圏の半単体的対象の非正規化鎖複体は、面写像の交代和を微分とする非負複体である。

KB-W2型再照合：仮定：前加法圏の単体的対象（Lean が強い：半単体的対象の面写像に加えて退化写像がある）。結論：微分が面写像の交代和である鎖複体（一致）。

微分は $`\sum_i(-1)^i d_i` で、面写像の恒等式により平方が零になる。単体的対象にも、退化写像を忘れて同じ構成を適用する。

:::

:::definition "ha_1_2_3_9" (lean := "AlgebraicTopology.normalizedMooreComplex")
*HA 定義 1.2.3.9*　正規化鎖複体（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=56)）。対応表の状態：Mathlib にある。

*主張*　アーベル圏の単体的対象の正規化鎖複体は、次数 $`n` で $`d_1,\ldots,d_n` の核の共通部分を取り、$`d_0` を微分にする。

仮定：アーベル圏の単体的対象（HA と一致）。結論：正の番号の面写像の核の共通部分を取り、d₀ の制限を微分とする正規化鎖複体（一致）。

共通部分は面写像を並べた有限直和への射の核として作れる。面写像の恒等式によって $`d_0` はこれらの核を一つ下の次数の核へ移す。

:::

:::definition "ha_1_2_3_10" (lean := "SSet.chainComplexFunctor, SerrePositivity.SimplicialChains.AlexanderWhitney.chains")
*HA 記法 1.2.3.10*　単体集合の正規化・非正規化鎖複体（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=56)）。対応表の状態：一部（component）。

*主張*　単体集合の正規化・非正規化鎖複体は、各次数で自由アーベル群を取ってからそれぞれの鎖複体構成を適用して得る。

KB-W2型再照合：仮定：単体集合と係数（HA の ℤ を取れる。own の正規化は小さい単体集合）。結論：自由加群の交代面写像複体と、own の退化を消去した正規化複体がある。HA の Moore 正規化と退化商の比較を採用した型は明示しない（Lean が弱い）。

単体集合のホモロジーは非正規化複体のホモロジーで定義される。正規化複体の包含は擬同型なので、どちらを使っても同じホモロジーを得る。

:::

:::proposition "ha_1_2_3_11" (lean := "CategoryTheory.Abelian.DoldKan.equivalence, CategoryTheory.Abelian.DoldKan.equivalence_inverse")
*HA 注意 1.2.3.11*　Dold–Kan の正規化による鎖複体の回復（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=57)）。対応表の状態：Mathlib にある。

*主張*　Dold–Kan で非負複体を単体化してから正規化すると、標準的に元の複体に戻る。

仮定：アーベル圏の非負鎖複体（HA と一致）。結論：Γ の後に N を適用した関手と恒等との自然同型が圏同値の余単位から得られる（一致）。

正規化の核条件を課すと、次数 $`n` の直和のうち恒等全射 $`[n]\to[n]` の成分が残る。これらの同定は各次数の微分と両立する。

:::

:::lemma_ "ha_1_2_3_12" (lean := "CategoryTheory.Abelian.DoldKan.equivalence, CategoryTheory.Abelian.DoldKan.equivalence_inverse")
*HA 補題 1.2.3.12*　正規化関手と Dold–Kan 関手の随伴（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=57)）。対応表の状態：Mathlib にある。

*主張*　アーベル圏で、$`\mathrm{id}\simeq N\circ\mathrm{DK}` の標準同型は、正規化を Dold–Kan 関手の右随伴とする単位である。

仮定：アーベル圏（HA と一致）。結論：逆向きの圏同値の随伴で Γ が左随伴、N が右随伴となり、id≅NΓ を単位に取れる（一致）。

単体化した複体から単体的対象への射は、その対象の正規化への鎖写像に対応する。この対応に複体の恒等写像を入れると、前項の同型を得る。

:::

:::lemma_ "ha_1_2_3_13" (lean := "CategoryTheory.Abelian.DoldKan.equivalence")
*HA 補題 1.2.3.13*　アーベル群に対する Dold–Kan 同値（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=57)）。対応表の状態：Mathlib にある。

*主張*　アーベル群の非負鎖複体の圏から単体的アーベル群の圏への Dold–Kan 関手は同値である。

仮定：アーベル圏 A（Lean が弱い：アーベル群の圏に限らない）。結論：非負鎖複体と単体的対象が Dold–Kan により同値（一致）。

正規化で逆を与える。特に、正規化複体を再び単体化すると、元の単体的アーベル群を各次数で回収できる。

:::

:::proposition "ha_1_2_3_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanHomSpaceKan, SerrePositivity.InfinityCategories.HA.Section1_2_3.derivedInfinityPiCohomologyEquiv")
*HA 注意 1.2.3.14*　単体的アーベル群のホモトピー群と正規化ホモロジー（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=58)）。対応表の状態：一部（special）。

*主張*　単体的アーベル群の基礎単体集合は Kan 複体であり、零を基点とするホモトピー群は正規化複体のホモロジー群に一致する。

A•をdg圏のDold–Kan写像単体的加群の underlying simplicial setに限れば、doldKanHomSpaceKanは原文の同じ単体集合のKan性という成分を直接返す。任意の単体的アーベル群のπnと正規化ホモロジーの比較全体はこの型には含まない。

次数ゼロでもアーベル群構造があり、高次では通常のホモトピー群の演算と一致する。正規化の微分により、ホモトピー群をサイクルと境界で表せる。

:::

:::proposition "ha_1_2_3_15" (lean := "CategoryTheory.Idempotents.DoldKan.N, CategoryTheory.Idempotents.DoldKan.equivalence_functor")
*HA 注意 1.2.3.15*　冪等完備な加法圏での正規化関手（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=59)）。対応表の状態：Mathlib にある。

*主張*　冪等完備な加法圏での正規化は Dold–Kan の逆同値であり、各項は正の添字の面写像を並べた射の核として特徴付けられる。

仮定：冪等完備な前加法圏と有限余積（HA の冪等完備な加法圏と対応）。結論：N が Γ の逆となる正規化関手（一致）。

$`N_n(A)\to A_n` を通る射は、$`d_1,\ldots,d_n` との合成が全て零になる射とちょうど一致する。アーベル圏で構成した正規化と同じ普遍性である。

:::

:::proposition "ha_1_2_3_16" (lean := "AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex")
*HA 注意 1.2.3.16*　退化写像と非正規化複体からの正規化（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=60)）。対応表の状態：一部（stronger-hyp）。

*主張*　冪等完備な加法圏では、正規化の各項を、退化写像を並べた射の余核としても表せる。

KB-W2型再照合：仮定：Γ₀ から得た単体的対象、またはアーベル圏の単体的対象（Lean が強い：HA の任意の冪等完備加法圏の単体的対象を一つの型で扱わない）。結論：退化成分に沿う分裂と非正規化から正規化への比較。一般の冪等完備加法圏での退化商との同定は型にない（Lean が弱い）。

退化写像の像を落とす射を各次数で合わせると、非正規化複体から正規化複体への全射な鎖写像になる。この鎖写像は正規化複体の包含を分裂させる。

:::

:::proposition "ha_1_2_3_17" (lean := "AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex")
*HA 命題 1.2.3.17*　正規化複体と非正規化複体の比較（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=60)）。対応表の状態：Mathlib にある。

*主張*　アーベル圏の単体的対象について、正規化複体と非正規化複体を結ぶ標準包含と標準射影はともに擬同型である。

仮定：アーベル圏の単体的対象（HA と一致）。結論：正規化と非正規化の標準包含・射影が互いに鎖ホモトピー逆。従って両者は擬同型（Lean が強い）。

退化項からなる部分はホモロジーに寄与しない。そのため、正規化によってサイズを減らしながらホモロジーを保てる。

:::

:::definition "ha_1_2_3_19" (lean := "CategoryTheory.MonoidalPreadditive")
*HA 定義 1.2.3.19*　多重加法的関手（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=61)）。対応表の状態：一部（special）。

*主張*　加法圏の積を始域とする関手が多重加法的であるとは、各変数で個別に直和を保つことである。

KB-W2型再照合：仮定：前加法的なモノイダル圏（Lean が強い：任意の多重加法関手でなく二変数テンソルに限る）。結論：左と右の各変数で零射・和を保ち、テンソルが別々に加法的（一致する特例）。

一つの変数以外を固定すると、その変数について加法関手になる。変数ごとの条件は Hom に誘導される多重線形性を与える。

:::

:::proposition "ha_1_2_3_20" (lean := "CategoryTheory.tensorLeft_additive, CategoryTheory.tensorRight_additive")
*HA 注意 1.2.3.20*　多重加法的関手の直和分解（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=61)）。対応表の状態：一部（special）。

*主張*　多重加法関手が Hom に誘導する写像は各変数で加法的であり、Hom 群のテンソル積を経由する。

KB-W2型再照合：仮定：前加法的なモノイダル圏（Lean が強い：一般の多重加法関手ではなく二変数テンソル）。結論：固定した対象による左右のテンソル関手が加法的で、Hom 上の写像は各変数で加法的（テンソルの場合の部分と一致。Lean が弱い：任意の多重加法関手と Hom のテンソル積を経由する写像を一括して構成しない）。

各変数の射を一組ずつ選んで写した射は、どの変数でも和と両立する。この多重線形性がテンソル積からの一つのアーベル群準同型を定める。

:::

:::proposition "ha_1_2_3_21" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensor, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap")
*HA 注意 1.2.3.21*　多重加法的関手の鎖複体への拡張（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=62)）。対応表の状態：一部（special）。

*主張*　多重加法関手は非負鎖複体上の多重加法関手を誘導し、全次数 $`p` の項は $`p_1+\cdots+p_n=p` の成分の直和、微分は Koszul 符号付きの和で与えられる。

KB-W2型再照合：仮定：整数加群の非負鎖複体二つ（Lean が強い：一般の多重加法関手ではなく二変数テンソル）。結論：全次数の直和と符号付き微分によるテンソル複体、および鎖写像への作用（この特殊例の構成と一致。Lean が弱い：任意の多重加法関手への一括拡張は含まれない）。

第 $`i` 成分の微分につける符号は $`(-1)^{p_1+\cdots+p_{i-1}}` である。非負複体では和が有限であり、終域で可算余積があれば同じ式を一般の整数次数でも使える。

:::

:::definition "ha_1_2_3_22" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitney, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitneySummand")
*HA 構成 1.2.3.22*　Alexander–Whitney 写像の構成（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=62)）。対応表の状態：一部（special）。

*主張*　Alexander–Whitney 写像は、多重加法関手を単体的対象に点ごとに適用して得た鎖複体から、各入力の鎖複体に関手を適用して全複体化したものへの鎖写像である。

KB-W2型再照合：仮定：二つの整数加群値単体的対象（Lean が強い：一般の n 変数の多重加法関手でなくテンソルの場合）。結論：前面と後面を取り全次数の分割について加える Alexander–Whitney 写像（二変数の場合は一致）。

次数を $`p_1+\cdots+p_n=p` に分け、$`[p]` の連続する部分区間に制限する成分写像を加える。退化写像の余核を通すと、正規化複体についても比較写像を得る。

:::

:::proposition "ha_1_2_3_24" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitney_naturality, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedAlexanderWhitney_naturality")
*HA 注意 1.2.3.24*　Alexander–Whitney 写像の正規化への制限（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=63)）。対応表の状態：一部（special）。

*主張*　正規化と非正規化の Alexander–Whitney 写像はいずれも入力の単体的対象の族に自然である。

KB-W2型再照合：仮定：整数加群の単体的対象二つとそれぞれの射（Lean が強い：二変数テンソルに特化）。結論：正規化・非正規化の Alexander–Whitney 写像が各射について可換（二変数の場合は一致）。

各成分は単体的対象の構造射である部分区間への制限から作られる。従って入力の自然変換と可換になり、複体値関手の間の自然変換となる。

:::

:::proposition "ha_1_2_3_26" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitney, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedAlexanderWhitney")
*HA 例 1.2.3.26*　鎖複体のモノイド構造と正規化の余モノイド性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=64)）。対応表の状態：一部（component）。

*主張*　加法的・冪等完備で積が各変数に加法的なモノイダル圏では、正規化と非正規化は左 lax モノイダルになり、逆の Dold–Kan 同値は右 lax モノイダルになる。

KB-W2型再照合：仮定：整数加群のテンソル（Lean が強い：一般の冪等完備な加法的モノイダル圏ではない）。結論：正規化と非正規化それぞれのテンソル比較射。一般の両関手の oplax monoidal 構造を返す型は含まれない（Lean が弱い）。

複体のテンソルは全複体化で定まる。左 lax 構造射は $`N(A\otimes B)\to N(A)\otimes N(B)` および非正規化での同様の Alexander–Whitney 写像で、結合子との両立を持つ。

:::

# 1.2.4 The ∞-Categorical Dold-Kan Correspondence

%%%
number := false
tag := "ha-1-2-4"
%%%

:::lemma_ "ha_1_2_4_6" (lean := "SerrePositivity.InfinityCategories.HA.Section1_2_4.idempotentComplete_of_ulift_ho_complete")
*HA 補題 1.2.4.6*　安定 ∞ 圏の冪等完備性とホモトピー圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=69)）。対応表の状態：一部（stronger-hyp）。

*主張*　安定 ∞ 圏が冪等完備であることは、そのホモトピー圏が冪等完備であることと同値である。

hCだけでなく明示されたuniverse lift後のホモトピー圏の冪等完備性も入力すれば、idempotentComplete\_of\_ulift\_ho\_completeは同じCの冪等完備性を直接返す。lift前のhCの入力からの比較と逆向きはこの引用だけでは含まない。

安定性を仮定すれば、ホモトピー圏の冪等射が分裂するという条件で ∞ 圏の冪等完備性を判定できる。

:::

:::proposition "ha_1_2_4_13" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pullback_iff_pushout_square")
*HA 命題 1.2.4.13*　安定 ∞ 圏の立方体における極限と余極限（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=73)）。対応表の状態：一部（special）。

*主張*　安定 ∞ 圏の立方体は、終頂点がそれを除いた図式の余極限であるとき、かつそのときに限り、始頂点がそれを除いた図式の極限である。

KB-W2型再照合：仮定：安定準圏と 2 次元正方形（Lean が強い：任意の n 立方体ではない）。結論：正方形が引き戻しであることと押し出しであることは同値（n=2 の場合に一致）。

二次元では押し出しと引き戻しの同値である。この命題は同じ双対性を高次元の立方体にも拡張する。

:::

:::lemma_ "ha_1_2_4_16" (lean := "Convex.contractibleSpace")
*HA 補題 1.2.4.16*　指定点を含む単調列の空間の可縮性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=74)）。対応表の状態：一部（special）。

*主張*　開区間 $`(0,1)` の高々 $`n` 個の指定点をすべて含む、$`[0,1]` 内の昇順 $`n` 項列の空間は可縮である。

S=∅に限れば、Yは0≤y1≤…≤yn≤1という非空凸部分集合であり、Convex.contractibleSpaceへ同じYの凸性・非空性を入力すると原文の可縮性を直接得る。一般の指定点を含む集合との同相は含まない。

項の重複と区間の端点を許す。指定点が列のどこかに現れるという条件を課した部分空間全体について、可縮性を述べている。

:::

