-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Comma.Over.Pullback
import SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfDerivedComparison
import SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfDerivedTransport
import SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfEndpointEquivalence
import SerrePositivity.InfinityCategories.HTT.Section1_2_9.OverIso
import SerrePositivity.InfinityCategories.HTT.Section5_2_5.Adjunction
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.Adjunction
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.HomotopyCategory
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.PointwiseUnitComparison
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QuillenCfBifibration
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveIdempotence
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveUnitInvertible
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingAdjunction
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Reflective
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveLocalization
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversalConsequences
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AdjointFunctorTheorem
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NativeAdjointFunctorCriterion
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PairDuality
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PreservingFunctorSpaces
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.AdjunctionLimits
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LeftAdjointAllColimitPreservation
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HTT 5.2 Adjoint Functors" =>
%%%
number := false
tag := "htt-5-2"
%%%

HTT 5.2 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/htt-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 5.2.2 Adjunctions

%%%
number := false
tag := "htt-5-2-2"
%%%

:::definition "htt_5_2_2_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence") (uses := "htt_1_1_2_4, htt_2_4_2_1")
*HTT 定義 5.2.2.1*　両側ファイブレーションによる随伴（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=358)）。対応表の状態：本体にある。

*主張*　∞ 圏 $`\mathcal C,\mathcal D` の間の随伴は、Cartesian かつ余 Cartesian な $`\mathcal M\to\Delta^1` と、その両端ファイバーの $`\mathcal C,\mathcal D` との同値で与える。

同じq:M→Δ¹のCartesianFibrationとCocartesianFibration、両端のvertexFiberへのQCatEquivalenceを並べると原文のadjunctionの定義全体そのもの。QCatAdjunction F Gによる別の定義との比較を仮定して置換した判定ではない。

区間に沿う前向きの余 Cartesian 移送が左随伴、後ろ向きの Cartesian 移送が右随伴になる。二つの関手を同じ全空間から読むのがこの定義の特徴である。

:::

:::proposition "htt_5_2_2_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.rightAdjointFunctorIso")
*HTT 注意 5.2.2.2*　右随伴のホモトピーまでの一意性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=358)）。対応表の状態：本体にある。

*主張*　左随伴が固定されると、右随伴は存在すればホモトピーまで一意であり、より精密にはその選択の空間が可縮である。

仮定：同じ左随伴 f に対する二つの ∞ 随伴 f⊣g,f⊣g′（HTT と一致）。結論：g,g′ が Fun(D,C) 内で同値、すなわち FunctorIso を持つ（HTT と一致）。随伴は h Fun の単位・余単位の模型であり、単なる hC,hD の随伴ではない。この項目は対応 M 自体の構成を結論に含めない。

同じ左随伴をもつ二つの右随伴は、写像空間の同じ関手を表現する。その表現の普遍性により、比較の同値だけでなく比較どうしの高次の選択も制御される。

:::

:::proposition "htt_5_2_2_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.comp")
*HTT 命題 5.2.2.6*　随伴関手の合成と右随伴（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=360)）。対応表の状態：本体にある。

*主張*　$`f\dashv g`、$`f'\dashv g'` のとき、$`f'f\dashv gg'` である。

仮定：準圏間の二つの ∞ 随伴 f⊣g,f′⊣g′（HTT と一致）。結論：f′f⊣gg′ の合成随伴（HTT と一致）。h Fun の二胞体を持つ双圏随伴の合成であり、通常のホモトピー圏だけの随伴に弱めていない。区間上対応の合成の構成を述べる §5.2.1.5 とは区別する。

終域の試験対象からまず $`g'` で中間へ戻し、次に $`g` を使う。写像空間の二つの随伴比較を合成するとこの順序になる。

:::

:::definition "htt_5_2_2_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitMappingSpaceCondition_iff_interval")
*HTT 定義 5.2.2.7*　写像空間を特徴づける単位変換（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=360)）。対応表の状態：本体にある。

*主張*　$`f:\mathcal C\to\mathcal D`、$`g:\mathcal D\to\mathcal C` に対する単位は $`u:1\to gf` で、$`g` による写像の像と $`u(C)` との前合成が $`\operatorname{Map}(fC,D)\to\operatorname{Map}(C,gD)` を同値にするものである。

仮定：準圏 C,D、二関手 f,g と idC→gf の自然変換 u（HTT と一致）。結論：標準比較 MapD(fC,D)→MapC(C,gD) が全 C,D でホモトピー同値となる単位変換の条件（HTT と一致）。pinchedHom の条件と区間写像空間条件の同値もあり、全パラメータの追加仮定はない。h Fun の射で書くため自然変換の代表の選択には依存しない。

自然変換が一つあることに加え、各成分が誘導する指定比較をすべての対象対で検査する。単位はこの向きの写像空間の比較を起こすデータである。

:::

:::proposition "htt_5_2_2_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcat_exists_adjunction_unitHom_iff_unitMappingSpaceCondition")
*HTT 命題 5.2.2.8*　単位変換による随伴の存在判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=361)）。対応表の状態：本体にある。

*主張*　関手 $`f` が $`g` の左随伴であることは、写像空間の普遍性を満たす単位変換 $`1\to gf` が存在することと同値である。

仮定：準圏 C,D と f:C→D,g:D→C（HTT と一致）。結論：∞ 随伴 f⊣g の存在と単位変換の存在が同値（HTT と一致）。任意の指定 u について随伴の単位が u であることまで同値にする型なので、u を存在量化すれば本文の条件になる。随伴は h Fun の単位・余単位の模型であり、通常の h の随伴で代用しない。

任意の単位候補が使えるわけではなく、前合成により写像空間が同値になることを要する。この条件から区間上の随伴を回復できる。

:::

:::proposition "htt_5_2_2_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.toHoAdjunction")
*HTT 命題 5.2.2.9*　随伴から豊穣ホモトピー圏への移行（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=362)）。対応表の状態：一部（component）。

*主張*　∞ 圏間の随伴関手は、ホモトピー型に豊穣化されたホモトピー圏の間にも随伴を誘導する。

KB-W2原文・型再照合：仮定：準圏 C,D と ∞ 随伴 f⊣g（HTT と一致）。結論：同じ f,g が誘導する通常のホモトピー圏上の随伴（Lean が弱い：原典が要求する H 豊穣随伴の構造から豊穣を忘れた部分）。元の対象と二関手を変えず、全ての通常の射に関する自然性も型に含む。H 豊穣の自然同値を構造として出力する宣言はここでは確認していない。

比較は写像の成分集合に落とした通常の随伴よりも情報を持つ。豊穣の段階では、元の写像空間の同値をホモトピー圏の同型として使う。

:::

# 5.2.3 Preservation of Limits and Colimits

%%%
number := false
tag := "htt-5-2-3"
%%%

:::proposition "htt_5_2_3_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.mapJoinCocone_isColimit_of_adjunction, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.mapJoinCone_isLimit_of_adjunction")
*HTT 命題 5.2.3.5*　左右随伴による全余極限と極限の保存（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=367)）。対応表の状態：本体にある。

*主張*　左随伴は始域に存在する余極限をすべて保ち、右随伴は始域に存在する極限をすべて保つ。

仮定：準圏 C,D と ∞ 随伴 f⊣g、任意形状の図式とその指定余極限錐または極限錐（HTT と一致）。結論：f が元の余極限錐を、g が元の極限錐を保存する（HTT と一致）。両方とも形状 K の準圏性や圏の完備性を要求せず、有限形状や filtered 形状にも限定しない。

余錐を試験する写像空間を随伴によって右随伴側へ移せば、もとの余極限の普遍性が使える。極限では射の向きを反転する。

:::

:::proposition "htt_5_2_3_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_rightAdjoint_iff_preservesSmallColimits")
*HTT 注意 5.2.3.6*　適切な集合論的仮定下の随伴関手定理（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=368)）。対応表の状態：一部（special）。

*主張*　適切な集合論的仮定の下では、余極限保存から右随伴の存在を導ける。

KB-W2原文・型再照合：仮定：C,D が presentable、準圏間の関手 f（Lean が強い：本文の「適切な集合論的仮定」のうち presentable の場合）。結論：f の右随伴の存在と全小余極限保存の同値（この場合に一致）。単なる余極限保存から無条件に右随伴を得る主張としては読まない。

前の定理は随伴がある場合の保存だけを述べる。逆向きの条件がそろう例は第5.5.2.9項にあり、可提示性が使われる。

:::

# 5.2.4 Examples of Adjoint Functors

%%%
number := false
tag := "htt-5-2-4"
%%%

:::proposition "htt_5_2_4_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.quillenCfCollageProjection_cartesianFibration, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.quillenCfCollageProjection_cocartesianFibration, SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfBottomFiberIso, SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfTopFiberIso")
*HTT 命題 5.2.4.6*　単体的 Quillen 随伴の cf 対応（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=371)）。対応表の状態：一部（stronger-hyp）。

*主張*　単体的モデル圏の単体的 Quillen 随伴から作る二つの圏を合わせた豊穣圏のファイブレント・コファイブレント対象に制限し、その nerve を取ると、両側の導来 ∞ 圏の随伴が得られる。

KB-W2原文・型再照合：仮定：二つの単体模型圏と単体的 Quillen 随伴（Lean が強い：固定 tensor/cotensor、固定 SM7、Hom 随伴の合成互換、および関手的な両側の分解を明示入力）。結論：原典と同じ cf 対応の射影が Cartesian かつ coCartesian で、両端ファイバーが元の cf nerve と同型（この入力の下で一致）。具体例に使う ModelCategory instance なし：SSet の Kan–Quillen 入力は sorry に依存し、本行でそれを実在する instance としては数えない。

混合する写像対象を Quillen 随伴から与え、区間の両側に各モデル圏の良い対象を置く。その構成の nerve で、単なるホモトピー圏の随伴にとどまらない比較が得られる。

:::

:::proposition "htt_5_2_4_7" (lean := "SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftDerived, SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightDerived, SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfDerivedAdjunctionWithComparisons_exists")
*HTT 注意 5.2.4.7*　非可換導来関手と通常置換との比較（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=372)）。対応表の状態：一部（stronger-hyp）。

*主張*　単体的 Quillen 随伴が導く nerve 間の随伴関手は非アーベルの左・右導来関手であり、ホモトピー圏では通常の導来関手に戻る。

KB-W2原文・型再照合：仮定：単体的 Quillen 随伴（Lean が強い：固定 SM7・合成互換と両側の関手的分解を指定し、ModelCategory instance なしの具体例を残す）。結論：同じ cf nerve 間の左右導来関手、標準単位を持つ全 ∞ 随伴、および通常の cf 置換関手の nerve との FunctorIso（置換を用いた本文の導来関手の比較に一致）。本行では SSet の未証明 Kan–Quillen 入力を instance の証拠としない。

高次の関手として導来した後、射のホモトピー類に移すと古典的な導来関手が得られる。両者の区別は写像空間を保つ段階にある。

:::

# 5.2.5 Adjoint Functors and Overcategories

%%%
number := false
tag := "htt-5-2-5"
%%%

:::proposition "htt_5_2_5_1" (lean := "CategoryTheory.Over.postAdjunctionLeft, SerrePositivity.InfinityCategories.HTT.Section5_2_5.nerveAdjunctionOfAdjunction, SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso")
*HTT 命題 5.2.5.1*　スライスへの随伴と単位に沿う引き戻し（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=372)）。対応表の状態：一部（special）。

*主張*　随伴 $`F\dashv G` と引き戻しを持つ $`\mathcal C` の対象 $`C` に対し、$`\mathcal C_{/C}\to\mathcal D_{/FC}` の右随伴は $`G` を適用してから単位 $`C\to GFC` で引き戻すものに同値である。

KB-W2原文・型再照合：仮定：引き戻しを持つ通常圏 C の随伴 F⊣G、対象 c（Lean が強い：通常圏の神経の場合）。結論：Over.post F の右随伴は Over.post G と単位 c→GFc に沿う pullback の合成（この場合に (1)(2) が一致）。通常の Over の nerve と native な頂点上 slice の同型、および通常随伴を元の nerve 間の ∞ 随伴へ移す宣言を併用する。一般の準圏の slice 随伴は含まない。

$`G` を適用すると、まず $`GFC` への射を得る。所望のスライスの底は $`C` なので、そこで単位に沿って底変換する。

:::

:::lemma_ "htt_5_2_5_2" (lean := "CategoryTheory.Over.postAdjunctionLeft, CategoryTheory.Over.mapPullbackAdj, SerrePositivity.InfinityCategories.HTT.Section5_2_5.nerveAdjunctionOfAdjunction, SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso")
*HTT 補題 5.2.5.2*　図式スライス間の随伴の存在と計算（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=372)）。対応表の状態：一部（special）。

*主張*　随伴 $`F\dashv G` と変換 $`Fp_0\to p_1` によるスライス関手は、$`\mathcal C` に引き戻しと $`K`-型極限があれば右随伴を持ち、それは $`G` の適用と随伴な変換 $`p_0\to Gp_1` に沿う引き戻しである。

KB-W2原文・型再照合：仮定：引き戻しを持つ通常圏間の随伴 F⊣G と F(c)→d（Lean が強い：C,D は神経、形状 K は一点）。結論：C/c→D/d の F による後合成と指定射による後合成の合成が右随伴を持つ（この場合に (1) と一致）。二つの明示随伴の合成で得られる。任意の K に対する主張、および (2) の単一の図式 pullback による計算との比較は含まない。

対象一つでの単位を、図式どうしの随伴な比較へ置き換える。元の図式と像の図式の形は同じ $`K` なので、その全脚と両立する引き戻しが必要になる。

:::

# 5.2.6 Uniqueness of Adjoint Functors

%%%
number := false
tag := "htt-5-2-6"
%%%

:::definition "htt_5_2_6_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_rightAdjoint_iff_preservesSmallColimits, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_leftAdjoint_iff_accessible_preservesLimits")
*HTT 定義 5.2.6.1*　左右随伴を持つ全関手準圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=378)）。対応表の状態：一部（stronger-hyp）。

*主張*　$`\operatorname{Fun}^{L}(\mathcal C,\mathcal D)` と $`\operatorname{Fun}^{R}(\mathcal C,\mathcal D)` は、それぞれ左随伴・右随伴である関手の張る充満部分圏である。

KB-W2原文・型再照合：仮定：C,D が presentable（Lean が強い：原典の任意の準圏にこの仮定を追加）。結論：左右随伴の存在で頂点を選ぶ FunL(C,D),FunR(C,D) の全部分準圏（この場合に一致）。PrL は全小余極限保存、PrR は accessible かつ全小極限保存で定義され、二つの存在判定の同値により同じ頂点条件となる。core だけには制限していない。

関手を対象として選別するが、それらの間の自然変換は関手圏から引き継ぐ。随伴の証拠の選び方を新しい射の条件にはしない。

:::

:::proposition "htt_5_2_6_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presentableAdjointFunctorEquivalence, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presentableAdjointFunctorEquivalence_adjunction, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_rightAdjoint_iff_preservesSmallColimits, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_leftAdjoint_iff_accessible_preservesLimits")
*HTT 命題 5.2.6.2*　左随伴関手圏と反対右随伴関手圏の同値（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=378)）。対応表の状態：一部（stronger-hyp）。

*主張*　左随伴関手の ∞ 圏 $`\operatorname{Fun}^{L}(\mathcal C,\mathcal D)` は、逆向きの右随伴関手の ∞ 圏の反対圏 $`\operatorname{Fun}^{R}(\mathcal D,\mathcal C)^{\mathrm{op}}` と標準的に同値である。

KB-W2原文・型再照合：仮定：C,D が presentable（Lean が強い：任意の準圏の場合は含まない）。結論：FunL(C,D) と FunR(D,C)op の全準圏の同値で、同値の順方向の各値は元の左関手の右随伴（この場合に一致）。PrL/PrR の頂点条件と随伴存在の同値も併用する。非可逆な自然変換と全高次単体を保持し、右随伴の対象ごとの選択だけでは代用しない。

左随伴間の自然変換は、単位と余単位によって逆向きの右随伴間の変換へ移る。対象の随伴の対応に加え、この変換の向きも結論に含まれる。

:::

# 5.2.7 Localization Functors

%%%
number := false
tag := "htt-5-2-7"
%%%

:::definition "htt_5_2_7_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.inclusion_fullyFaithful") (uses := "htt_1_1_2_4")
*HTT 定義 5.2.7.2*　充満忠実な右随伴を持つ局所化（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=383)）。対応表の状態：一部（special）。

*主張*　∞ 圏の関手が局所化であるというのは、その右随伴が存在して充満忠実である場合である。

KB-W2原文・型再照合：仮定：頂点条件 P による充満部分準圏への反射 r（Lean が強い：右随伴が充満包含として与えられる場合）。結論：r.reflector が、充満忠実な右随伴である包含を持つ局所化関手（この場合に HTT の定義と一致）。任意の辺反転による IsLocalization は原典のこの狭い意味と区別し、その定義を代用しない。

右随伴により終域を始域の充満部分圏として見ると、局所化はそこへの反射になる。単なる指定射の反転とこの定義がいつ一致するかは別に判定する。

:::

:::proposition "htt_5_2_7_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.localizationPrecompositionEquivalence, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversalConsequences.IsLocalization.precomposition_isFullyFaithful, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.isLocalization")
*HTT 警告 5.2.7.3*　反射的局所化と辺を反転する関手（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=383)）。対応表の状態：一部（special）。

*主張*　充満忠実な右随伴を持つ局所化は、局所化で同値になる射を逆にする関手を前合成で分類するが、指定射を反転する普遍関手が一般にこの意味の反射であるとは限らない。

KB-W2原文・型再照合：仮定：充満包含への反射 r と任意の準圏 E（Lean が強い：右随伴が充満包含の形）。結論：r.reflector に沿う前合成は全関手圏で充満忠実で、その本質像は r.reflector が反転する全辺を反転する関手（この場合に一致）。明示的な QCatEquivalence が反転関手の全部分圏へ与えられる。一般の辺集合の局所化に右随伴があるという逆の主張は型に含めない。

反射であることには、終域の対象を始域内の局所対象として戻せる条件がある。反転の普遍性だけを述べる用語と、右随伴を含む原典の用語を区別する。

:::

:::proposition "htt_5_2_7_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveSubcategory.unitOnLocalizationIso, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveSubcategory.reflectedUnitIso, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.localization") (uses := "htt_1_1_2_4")
*HTT 命題 5.2.7.4*　反射と冪等単位の三条件（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=383)）。対応表の状態：一部（direction）。

*主張*　自己関手 $`L` が充満忠実な右随伴を持つ反射の合成として書けることは、その本質像への反射であること、または $`1\to L` の二つの $`L^2` への比較が同値となることと同値である。

KB-W2原文・型再照合：仮定：充満部分圏への反射で L は reflector と包含の合成（原典の (2) を満たす場合）。結論：同じ単位 α の αL と Lα の全自然同型、すなわち (3)（Lean が弱い：(2)⇒(3) の向き）。Lα は reflectedUnitIso を包含で後合成して得る。(3) だけから反射を構成する向きや三条件の同値は主張しない。

二つの比較は $`L(\alpha_C)` と $`\alpha_{LC}` で、すでに局所化した対象にもう一度局所化しても変わらないという条件を指定する。

:::

:::proposition "htt_5_2_7_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasColimit_of_reflection, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.mapJoinCocone_isColimit_of_adjunction, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveSubcategory.counitIso") (uses := "htt_1_1_2_4, htt_1_2_13_4")
*HTT 注意 5.2.7.5*　反射的局所化における余極限の計算（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=385)）。対応表の状態：一部（special）。

*主張*　局所化の始域が $`K`-型余極限を持てば終域も持ち、終域図式を右随伴で戻して余極限を取り、その結果を局所化すれば計算できる。

KB-W2原文・型再照合：仮定：充満包含への反射 r と、その周囲の圏での K 型余極限の存在（Lean が強い：右随伴を包含として指定した形）。結論：部分圏の任意の K 型図式を包含し、周囲の余極限を反射すれば元の図式の余極限となり、その存在を得る（この場合に一致）。K の準圏性や filtered 性は要求しない。

余極限は充満部分圏内でそのまま計算できるとは限らない。大きい圏で余極限を形成した後、左随伴の保存性により局所対象へ戻す。

:::

:::definition "htt_5_2_7_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.reflectionMappingEquivalence, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.unitPinchedMapIso") (uses := "htt_1_1_2_4")
*HTT 定義 5.2.7.6*　部分圏に関する局所化射の普遍性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=385)）。対応表の状態：一部（special）。

*主張*　充満部分圏 $`\mathcal C_0` に相対的な対象 $`C` の局所化は、$`D\in\mathcal C_0` への射 $`C\to D` で、任意の $`E\in\mathcal C_0` に対する前合成が $`\operatorname{Map}(D,E)\simeq\operatorname{Map}(C,E)` となるものである。

KB-W2原文・型再照合：仮定：反射 r と対象 x、局所化射には同じ反射の単位成分を取る（Lean が強い：任意の指定射ではなく反射単位の場合）。結論：全 y∈P について MapC(rx,y)→MapC(x,y) の同値であり、この単位が P に関する局所化射（この場合に定義の条件と一致）。随伴の標準単位比較との同型もあり、無関係な写像空間の同値を選んだものではない。

すべての試験対象を部分圏の中に限定する。その範囲では元の対象からの写像が局所化を一意的に経由することを、写像空間で述べる。

:::

:::proposition "htt_5_2_7_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.reflectionMappingEquivalence, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.unit") (uses := "htt_1_1_2_4")
*HTT 命題 5.2.7.8*　点ごとの局所化射と反射の存在（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=385)）。対応表の状態：一部（direction）。

*主張*　充満包含が左随伴を持つことは、全対象がその部分圏に相対的な局所化射を持つことと同値である。

KB-W2原文・型再照合：仮定：P の包含への左随伴が存在する（原典の (2)、Lean はそのデータ r を取る）。結論：同じ単位が各 x の局所化射を与える（Lean が弱い：(2)⇒(1) の向き）。写像空間の同値でその普遍性を与える。各対象ごとの局所化射から全左随伴を構成する逆方向は含まない。

対象ごとにある普遍射は、写像空間についての普遍性を満たす。これらから左随伴としての関手性も得られる。

:::

:::proposition "htt_5_2_7_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsReflectiveSubcategory, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory")
*HTT 注意 5.2.7.9*　反射的充満部分準圏の定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=386)）。対応表の状態：本体にある。

*主張*　左随伴を持つ充満包含が定める部分圏を反射的部分圏と呼ぶ。

仮定：準圏 C と頂点条件が張る充満部分圏 C′（HTT と一致）。結論：C′ の包含への左随伴の存在を反射的と呼ぶ性質（HTT と一致）。IsReflectiveSubcategory は、その反射関手と同じ包含への QCatAdjunction を持つデータの Nonempty であり、局所化の普遍性を追加仮定にしない。

部分圏に入らない対象についても、部分圏内の対象への普遍射を用意できる。ここでの反射は包含の左随伴を指す。

:::

:::proposition "htt_5_2_7_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.localizationPrecompositionEquivalence, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.isLocalization, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversalConsequences.IsLocalization.precomposition_isFullyFaithful")
*HTT 命題 5.2.7.12*　局所化関手に沿う前合成の普遍性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=386)）。対応表の状態：一部（special）。

*主張*　局所化の本質像から任意の ∞ 圏への関手を前合成すると、元の圏上の関手のうち局所化の逆にする射をすべて同値へ送るものが張る充満部分圏と同値になる。

KB-W2原文・型再照合：仮定：局所化が充満部分圏への反射 r として与えられ、任意の標的準圏 D を取る（Lean が強い：包含を右随伴として指定した形）。結論：元の全関手準圏で前合成が充満忠実で、本質像は反射が反転する全辺を反転する関手（この場合に一致）。明示的な逆と両往復の FunctorIso があり、core や関手の同値類の集合だけの普遍性ではない。

局所化後の関手は反転対象の射を自動的に同値として読む。逆にその条件を満たすものは局所化を経由し、比較は自然変換を含む関手 ∞ 圏のレベルで成立する。

:::

