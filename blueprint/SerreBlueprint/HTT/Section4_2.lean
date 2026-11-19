import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Elements
import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinBaseProjection
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.GeneralOriginalCriterion
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconePointHomInitiality
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitAttachmentDiagram
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CosliceLaxEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoin
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinGeneralComparison
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinEquivalenceFunctor
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LaxSliceUniversal
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceModelEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PreFiberKan
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RightIntervalEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinAnodyne
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.RightConeMonoAnodyne
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconeDiagonalTransformation
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconeTransformationEquivalence

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HTT 4.2 Techniques for Computing Colimits" =>
%%%
number := false
tag := "htt-4-2"
%%%

HTT 4.2 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/htt-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 4.2.1 Alternative Join and Slice Constructions

%%%
number := false
tag := "htt-4-2-1"
%%%

:::definition "htt_4_2_1_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStage, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin")
*HTT 定義 4.2.1.1*　円筒の両端を貼る太い結合（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=257)）。対応表の状態：本体にある。

*主張*　太い join $`X\diamond Y` は $`X\times Y\times\Delta^1` の始端を $`X`、終端を $`Y` への射影で貼った押し出しであり、両端を保つ通常の join への自然な比較を持つ。

仮定：任意の単体集合 X と Y（HTT と一致）。結論：直積円筒の零端を第一射影で X に、一端を第二射影で Y に貼る押し出しを二段で定める（円筒の直積因子の順序を除き一致）。

中間の柱体には $`X` と $`Y` の両座標があるが、両端ではそれぞれ一方の座標だけを残す。貼り合わせがホモトピー押し出しになるため、両因子の圏同値に対してこの模型は不変である。

:::

:::proposition "htt_4_2_1_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_fatJoinComparison")
*HTT 命題 4.2.1.2*　太い結合から通常の結合への同値（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=258)）。対応表の状態：本体にある。

*主張*　任意の単体的集合 $`X,Y` について、太い join から通常の join への自然な写像は圏同値である。

仮定：任意の二つの単体集合（HTT と一致）。結論：標準比較射が任意の準圏への前合成で準圏同値を誘導する（HTT 2.2.5.8 の圏同値の判定と一致）。

太い join の柱体模型と、頂点を前後の区間に分ける通常の join は単体として違う。比較写像は両端を固定したまま、∞ 圏としては同じ取扱いを可能にする。

:::

:::corollary "htt_4_2_1_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IsPrecompositionEquivalence.joinMap_left, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IsPrecompositionEquivalence.joinMap_right")
*HTT 系 4.2.1.3*　結合による圏同値の保存（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=258)）。対応表の状態：本体にある。

*主張*　二つの因子を圏同値な単体的集合で置き換えると、通常の join の誘導射も圏同値になる。

仮定：任意の単体集合間の二つの圏同値を準圏への前合成で判定する（HTT 2.2.5.8 と一致）。結論：左右それぞれの結合による保存を同じ結合写像の合成則に代入して、二射の結合が圏同値となる（一致）。

柱体で作る太い join では置換の保存を押し出しから調べられる。両側で通常の join へ比較すると結果を移せる。

:::

:::proposition "htt_4_2_1_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_cosliceLaxMap")
*HTT 命題 4.2.1.5*　通常と太いコスライスの圏同値（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=259)）。対応表の状態：本体にある。

*主張*　∞ 圏 $`\mathcal C` の図式 $`p` に対し、通常の join による余錐圏から太い join による余錐圏への比較は ∞ 圏の同値である。

仮定：準圏 C と任意の単体集合からの図式 p（HTT と一致）。結論：太い結合から通常の結合への標準射の前合成で得る通常コスライスから太いコスライスへの射が準圏同値（一致）。

この向きは、太い join から通常の join への写像に前合成して余錐を移すことから決まる。始対象を判定する際には、どちらの余錐圏の模型も使える。

:::

:::corollary "htt_4_2_1_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeftToIntervalMappingSpace_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence.isSimplicialHomotopyEquivalence")
*HTT 系 4.2.1.7*　太いコスライス比較の繊維同値（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=260)）。対応表の状態：一部（special）。

*主張*　余錐の通常 join 模型と太い join 模型の比較は、頂点 $`v` を固定すると Kan 複体のホモトピー同値になる。

KB-W2原文・型再照合：仮定：準圏 C の図式 p と頂点 v（Lean が強い：p が一点の包含）。結論：その一点の通常コスライスの繊維を左 pinched 模型で、太い方を両端固定の区間模型で表すと、同じ比較がホモトピー同値となる（一致する場合。一般の図式は含まない）。

余錐圏全体の同値に加え、両側を頂点への射影の同じファイバーへ制限しても比較が成り立つ。与えた頂点上の余錐空間を計算する場合に使う。

:::

:::corollary "htt_4_2_1_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeftToIntervalMappingSpace_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace_kanComplex, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence.isSimplicialHomotopyEquivalence")
*HTT 系 4.2.1.8*　左右の写像空間と区間模型の同値（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=260)）。対応表の状態：本体にある。

*主張*　∞ 圏の二頂点について、右および左の写像単体集合から端点固定の柱体模型への写像は、ともに Kan 複体のホモトピー同値である。

仮定：準圏 C の二頂点（HTT と一致）。結論：右・左の pinched 写像空間から両端固定の区間模型への二つの標準比較は準圏同値なので単体的ホモトピー同値であり、区間模型も Kan 複体である（一致）。

二つの比較を通じて、左と右の定値面の違いを吸収する。柱体模型は区間の両端を同時に固定するため、反対化との比較にも使いやすい。

:::

:::proposition "htt_4_2_1_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSliceHomEquiv")
*HTT 注意 4.2.1.9*　太いスライスの普遍性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=260)）。対応表の状態：本体にある。

*主張*　太い join による上の圏 $`X_{/p}^{\diamond}` は、$`K'\diamond K\to X` のうち右因子 $`K` 上で指定図式 $`p` に一致するものを表現する。

仮定：任意の単体集合の射 p とパラメータ K′（HTT と一致）。結論：太いスライスへの K′ からの射と、太い結合上で右因子を p に固定する射との標準全単射（一致）。

余錐と双対に、ここでは変数 $`K'` を左に置く。$`K'` を一点としたとき、得られる頂点は指定図式へ向かう錐である。

:::

# 4.2.2 Parametrized Colimits

%%%
number := false
tag := "htt-4-2-2"
%%%

:::definition "htt_4_2_2_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection")
*HTT 定義 4.2.2.1*　底を固定した相対的な太い結合（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=260)）。対応表の状態：一部（special）。

*主張*　底 $`S` 上の太い join は柱体の積を $`X\times_S Y` に置き換えて作り、底変換と可換で、相対余錐を表す対象も底変換と可換である。

KB-W2原文・型再照合：仮定：二つの単体集合が同じ底 S に写る（Lean が強い：右因子の構造射が S の恒等射）。結論：X×ₛS ≅ X によって円筒の零端は X に同一写像で貼られ、一端を X→S で貼る写像円筒となる。Lean はこの押し出しとその底への構造射を与える（一致する場合。任意の右因子は含まない）。

両因子の底での点が一致する対だけを柱体に入れる。そのため底の一頂点でのファイバーでは、対応するファイバーどうしの通常の太い join に戻る。

:::

:::lemma_ "htt_4_2_2_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration")
*HTT 補題 4.2.2.3*　デカルト辺を使うプリズムの充填（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=261)）。対応表の状態：一部（special）。

*主張*　最後の外角の柱体と区間の両端で指定した写像は、終端面の最後の辺が各パラメータ頂点で Cartesian なら、Cartesian ファイブレーションに沿って相対的に柱体全体へ延長できる。

KB-W2原文・型再照合：仮定：指定の終端辺がデカルトなプリズムの持ち上げ問題（Lean が強い：q が自明 Kan ファイブレーションの場合）。結論：積と部分複体の包含による同じ単射に持ち上げ性を適用し、元の四角形の充填を得る（一致する場合。一般のデカルトファイブレーションは含まない）。

始端・終端の面と右外角側面をすでに固定している。最後の辺の Cartesian 性をどこで使うかは終端面 $`\{1\}` で指定されており、始端面ではない。

:::

# 4.2.3 Decomposition of Diagrams

%%%
number := false
tag := "htt-4-2-3"
%%%

*f-02-model-free.html — 5. bisimplicial 集合の対角*

bisimplicial 集合 $`A : \Delta^{\mathrm{op}} \to \mathbf{sSet}` の*対角*は、$`n \mapsto A_n` の $`n` 単体である。次の定理は、ホモトピー余極限の計算（例：Ex∞ やスペクトラムの構成）で繰り返し使われる。

$$`f : A \to B,\quad \text{各 } n \text{ で } f_n : A_n \to B_n \text{ が弱同値} \ \Longrightarrow\ \mathrm{diag}(f) \text{ は弱同値}`

（\`localized\_diagonal\_map\`、HomotopicalAlgebra/Simplicial/DiagonalLocalizedEquivalence.lean:55。弱同値は §4 の (a) の意味）。
docstring にあるとおり、モデル構造は置かずに、anodyne 局所化で可逆性を読んでいる。
証明は、Reedy 型の単射への分解（境界による分解系 \`BoundaryFactorization.reedy\_wfs\`）と、§4 の Kan 複体による判定を組み合わせる。

ただし、補助のファイル（BisimplicialCofibrancy・QuillenStandardFrame・StandardCosimplicial）が、末尾に Model の節を持っていたり、HomotopyFunctionComplex という名前のディレクトリにあったりする。そのため import の閉包にはモデル圏が入っている（§7）。

:::lemma_ "htt_4_2_3_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isInitialVertex_iff_trivialKanFibration")
*HTT 補題 4.2.3.3*　始点が始対象の単体の余錐制限（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=267)）。対応表の状態：一部（special）。

*主張*　∞ 圏の単体 $`\sigma:\Delta^n\to\mathcal C` の最初の頂点が始対象なら、余錐の $`\mathcal C_{\sigma/}\to\mathcal C_{\partial\sigma/}` は自明ファイブレーションである。

KB-W2原文・型再照合：仮定：準圏 C の単体 σ の初頂点が始対象（Lean が強い：σ が零単体の場合に適用）。結論：零単体の境界は空なので、同じコスライスの頂点射影が自明 Kan ファイブレーションとなる（その場合に一致。正次元の境界制限は含まない）。

境界上で与えた余錐は $`\sigma` のすべての顔と両立する。その同じ余錐を全単体へ延長する際に、先頭の対象の始対象性が使える。

:::

:::proposition "htt_4_2_3_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachedDiagram, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachedDiagram_left, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachedDiagram_right, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachedDiagram_restriction_trivialKanFibration") (uses := "htt_1_1_2_4")
*HTT 命題 4.2.3.4*　部分余極限を付加した図式の余錐比較（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=267)）。対応表の状態：一部（special）。

*主張*　通常圏で添字づけた $`K` 上の単体的集合 $`K_I` において、$`p:K\to\mathcal C` の各制限の余極限余錐 $`q_I` があれば、$`K_F` 上に $`p` と全 $`q_I` を延ばす図式 $`q` が存在し、$`\mathcal C_{q/}\to\mathcal C_{p/}` は自明ファイブレーションである。

KB-W2原文・型再照合：仮定：K 上の図式と、各 K\_I に対する指定余極限余錐（Lean が強い：I が一対象一射）。結論：K\_F は K と K\_I の余錐を貼る押し出しとなり、Lean は双方の制限を満たす図式とその余錐制限の自明 Kan ファイブレーション性を与える（指定した拡張の場合に一致。一般の I と全拡張は含まない）。

余極限対象をそれぞれ選んだだけでは、それらが一つの大きな図式になったとはいえない。$`K_F` は $`K` と各 $`K_I` 上の指定余錐をまとめる形であり、結論はその形上の整合的な延長を与える。

:::

:::lemma_ "htt_4_2_3_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion_innerAnodyne_of_leftAnodyne") (uses := "htt_2_1_2_3")
*HTT 補題 4.2.3.5*　弱同値を含む結合の押し出し隅（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=269)）。対応表の状態：一部（stronger-hyp）。

*主張*　単体的包含 $`A'\subseteq A`、$`B'\subseteq B` で後者が弱ホモトピー同値なら、$`(A'\star B)\cup(A\star B')\hookrightarrow A\star B` は右アノダインである。

KB-W2原文・型再照合：仮定：二つの部分複体包含と右因子の弱ホモトピー同値（Lean が強い：右因子の包含が左アノダイン）。結論：同じ結合の押し出し隅は内アノダインで、右ファイブレーションも内ファイブレーションなので右アノダイン（Lean が強い：内アノダイン性まで与える）。

右因子の比較に対しては通常の弱ホモトピー型の一致を仮定する。join の両側の指定部分を合わせると、結論はより方向をもった右アノダイン性になる。

:::

:::lemma_ "htt_4_2_3_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinPoint_mono_rightAnodyne") (uses := "htt_4_2_3_5")
*HTT 補題 4.2.3.6*　弱可縮な右因子との結合の右アノダイン性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=269)）。対応表の状態：一部（special）。

*主張*　単体的包含 $`A'\subseteq A` と弱可縮な $`B` に対し、$`A'\star B\subseteq A\star B` は右アノダインである。

KB-W2原文・型再照合：仮定：単射と弱可縮な右因子 B（Lean が強い：B が一点）。結論：同じ結合写像は右アノダイン（一致する場合。一般の弱可縮な右因子は含まない）。

右側の弱可縮性が、左因子を拡張しても右ファイブレーションの持ち上げを保つ理由である。ここで左因子の最初の包含に共終性は要求しない。

:::

:::definition "htt_4_2_3_7" (lean := "CategoryTheory.Functor.Elements")
*HTT 記法 4.2.3.7*　単体の持ち上げの圏と退化部分（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=270)）。対応表の状態：一部（component）。

*主張*　$`K` の $`n`-単体 $`\sigma` に対し $`I_\sigma` はその $`K_I` への持ち上げと持ち上げを保つ添字射の圏で、退化な持ち上げだけの充満部分圏を $`I^0_\sigma` とする。

KB-W2原文・型再照合：仮定：K の n 単体 σ と K 上の図式族 F（Lean が弱い：任意の型値関手を受け取り、I 上の各 K\_I の n 単体の σ 上の繊維に適用できる）。結論：対象と射が一致する要素圏 Iσ を与える（Lean が弱い：退化単体に限る充満部分圏 I′σ は指定しない）。

射は添字だけの射ではなく、その射で指定した持ち上げが次の持ち上げに移ることを要求する。$`\sigma` が非退化なら、退化単体の像も退化なので $`I^0_\sigma` は空になる。

:::

:::corollary "htt_4_2_3_11" (lean := "SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits, SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits.hasSmallKappaFilteredColimits") (uses := "htt_1_1_2_4, htt_4_2_3_4")
*HTT 系 4.2.3.11*　濃度の異なる余極限による余完備性判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=271)）。対応表の状態：一部（stronger-hyp）。

*主張*　原典の正則基数 $`\tau\ll\kappa` の条件で、∞ 圏が $`\kappa`-小余極限を持つことは、$`\tau`-小余極限と $`\kappa`-小な $`\tau`-filtered 半順序集合で添字づけた余極限を持つことと同値である。

KB-W2原文・型再照合：仮定：κ 未満の図式に対する余極限の存在（Lean が強い：κ 未満だけでなく、指定宇宙内の全図式に要求）。結論：τ 未満の図式と小さい τ-フィルター付き半順序の神経について同じ余極限が存在する（必要方向。τ≪κ に基づく分解による十分方向は含まない）。

大きな余極限を、より小さな部分図式の余極限と、それらをまとめる filtered 余極限に分けて作る。二種類を個別に持つことから、元の図式形状についての存在を取り出す。

:::

:::corollary "htt_4_2_3_12" (lean := "SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits, SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits.isKappaAccessibleFunctor")
*HTT 系 4.2.3.12*　濃度の異なる余極限による保存性判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=271)）。対応表の状態：一部（stronger-hyp）。

*主張*　始域に $`\kappa`-小余極限があり $`\tau\ll\kappa` が原典の正則基数の条件を満たすとき、その余極限の保存は $`\tau`-小余極限と $`\kappa`-小な $`\tau`-filtered 半順序集合による余極限の保存で判定できる。

KB-W2原文・型再照合：仮定：κ 未満の図式に対する余極限を保つ関手（Lean が強い：κ 未満だけでなく、指定宇宙内の全図式に要求）。結論：τ 未満の図式と小さい τ-フィルター付き半順序の神経について同じ余極限を保つ（必要方向。τ≪κ に基づく分解による十分方向は含まない）。

大きな余極限を二段に計算して、各段で像の余錐が普遍性を保つことを調べる。ここでは余極限を持つという判定に加え、指定関手が保存するという判定である。

:::

# 4.2.4 Homotopy Colimits

%%%
number := false
tag := "htt-4-2-4"
%%%

*coherent-nerve-diagrams.html — 3. ホモトピー整合的図式 — 厳密化定理*

単体的モデル圏 $`\mathbf M` について（Vogt、HTT Prop. 4.2.4.4）
$$`\mathrm{Fun}\bigl(N(J),\,N^{hc}(\mathbf M^\circ)\bigr)\ \simeq\ N\bigl(\mathrm{Fun}(J,\mathbf M)^\circ\bigr).`
ホモトピー整合的図式は厳密な図式とちょうど同じ情報をホモトピー不変な形で持つ。ホモトピー可換図式は一般には持ち上がらない（§4 の例 3）。∞ 圏の言葉では、関手 $`N(J)\to\mathcal S` がそのまま $`\mathcal S` 値の整合的図式で、straightening によって $`N(J)` 上の左 fibration と同じものになる。

:::theorem "htt_4_2_4_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictNativeCocone_isColimit_iff_general_representableComparison") (uses := "htt_1_1_5_5")
*HTT 定理 4.2.4.1*　豊穣ホモトピー余極限と神経の余極限（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=275)）。対応表の状態：一部（special）。

*主張*　ファイブレントな単体的圏の間の豊穣図式と両立した指定余錐について、それがホモトピー余極限であることと、誘導された整合的 nerve の余錐が余極限であることは同値である。

KB-W2原文・型再照合：仮定：局所 Kan な単体圏への図式と指定余錐（Lean が強い：添字は離散豊穣化した通常の小圏）。結論：神経の余錐の余極限性と、各対象への豊穣 Hom の Bousfield–Kan ホモトピー極限への比較がホモトピー同値であることを同値にする（HTT のホモトピー余極限の定義 A.3.3.13 に一致する場合。豊穣添字一般は含まない）。

比較するのは両側の対象の存在だけではなく、与えた各脚を持つ余錐である。豊穣の写像対象を用いるホモトピー的な普遍性が、nerve 側の写像空間での普遍性と対応する。

:::

:::lemma_ "htt_4_2_4_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_coconePointHomFamily_homotopyEquivalence, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationMap_homotopyEquivalence, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeDiagonalTransformationHomotopy, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeftToIntervalMappingSpace_isQCatEquivalence")
*HTT 補題 4.2.4.3*　写像空間の合成による余極限判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=275)）。対応表の状態：本体にある。

*主張*　図式 $`p:K\to\mathcal C` の指定余錐が余極限であることは、その頂点 $`X` から任意の $`Y` への写像空間が、$`p` から定値図式 $`\Delta Y` への写像空間と余錐による合成で同値になることと同値である。

仮定：準圏の任意の余錐（HTT と一致）。結論：全 Hom による余錐空間の判定を定値図式への変換空間に移す標準同値があり、合成で作る対角の変換とその比較はホモトピック。始域の左 pinched 模型も両端固定の写像空間と同値なので、同じ合成写像のホモトピー同値による判定を得る（一致）。

$`p\to\Delta X` が余錐を表す変換である。$`X\to Y` をその変換と合成すると $`p` からの新しい余錐を得る。これが写像空間全体の同値であることが普遍性になる。

:::

