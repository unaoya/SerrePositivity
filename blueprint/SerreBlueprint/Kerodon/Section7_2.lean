import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Limits.Final
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrowCofinality
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredPosetNerve
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalAnodyneRecognition
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalCoconeRestriction
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalComposition
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalConeRestriction
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalFactorizationCriterion
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalFunctorSpace
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalLimitTransfer
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalOpposite
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalTensor
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalWeakEquivalence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.Cofinality
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.FilteredDiagonalCofinality
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.LastHornPullback
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.LeftFibrationAnodynePullback
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.LeftFibrationCofinalPullback
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.LimitExistence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.QuillenA
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.QuillenALeft
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.RoofTerminalFiberCofinality
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.TerminalFiberCofinality
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.TerminalPointAnodyne
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.TrivialFibrationCofinality
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.JoinCells

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "7.2 Cofinality" =>
%%%
number := false
tag := "kerodon-7-2"
%%%

Kerodon の 7.2 節（[Tag 02MZ](https://kerodon.net/tag/02MZ)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

*f-b-literature-yoneda.html — 3. cofinality*

$`e\colon C'\to C` が cofinal とは、どんな $`F\colon C\to\mathcal D` についても $`\operatorname{colim}_{C'}(F\circ e)\to\operatorname{colim}_C F` が同値であること（極限には逆向きの coinitial、Kerodon の left cofinal を使う）。判定法は Quillen の定理 A：すべての $`c` で $`C'\times_C C_{c/}` が弱可縮。

- *余極限を簡単にする*：終対象 $`t` があれば $`\operatorname{colim}_C F\simeq F(t)`。filtered な図式は cofinal な部分で計算できる。図式の形を取り替える。

- *他の一般論の土台*：Kan 拡張の各点公式、極限の推移性、Ind とコンパクト対象（密度、単一の filtered 図式での表示）、局所化と余極限の整合。

- *不変性*：cofinal は「制限が余極限を変えない」という極限の理論の中での同値の概念。モデル圏での「ホモトピー余極限は添字の弱同値で不変」の ∞ 版。

- 1 圏の final functor は「$`c\downarrow e` が空でなく連結」。∞ 版では連結が弱可縮に強まる。

- 単射が left anodyne ⇔ left cofinal。§6 の「始対象の包含は left anodyne」はこれから出る。

# 7.2.1 Cofinal Morphisms of Simplicial Sets

%%%
number := false
tag := "kerodon-7-2-1"
%%%

Kerodon [Tag 02N0](https://kerodon.net/tag/02N0)

*04-yoneda-adjunction-kan.html — 5. cofinality*

\`\`\`text
def IsLeftCofinal \{A B : SSet.\{u\}\} (i : A ⟶ B) : Prop :=
  ∀ (E : SSet.\{u\}) (p : E ⟶ B) \[LeftFibration p\],
    IsSimplicialHomotopyEquivalence (cofinalFunctorPre p (𝟙 B) i)
\`\`\`

- 内容　／　Lean　／　場所
- left anodyne ⇒ left cofinal（right も同様）　／　\`isRightCofinal\_of\_rightAnodyne\` など　／　F1B/Cofinal\*
- cofinal ⇔ 「anodyne の後に trivial Kan fibration」と分解できる　／　\`isLeftCofinal\_iff\_exists\_anodyne\_trivialKan\_factorization\`　／　F1B/CofinalFactorizationCriterion
- trivial Kan fibration ⇔ 左 fibration かつ left cofinal　／　\`trivialKanFibration\_iff\_leftFibration\_and\_isLeftCofinal\`　／　同上
- 反対圏による left/right の入れ替え　／　\`isLeftCofinal\_iff\_isRightCofinal\_op\`　／　F1B/CofinalOpposite
- Quillen の定理 A 型の判定：slice が弱可縮なら、単射に沿う slice の制限は trivial　／　\`sliceOverRestrict\_trivialKanFibration\_of\_weaklyContractible\_slices\`　／　F1B/InitialQuillenRecovery
- 例：始対象への制限は極限を変えない　／　\`initialCofinality\_via\_quillenA\`　／　同上

cofinal な射に沿う slice の制限が trivial Kan fibration になる（\`sliceOverRestrict\_trivialKanFibration\_of\_isLeftCofinal\`）ので、極限は cofinal な部分図式で計算できる。

:::definition "kerodon_7_2_1_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorSpace")
Kerodon Definition 7.2.1.1（[Tag 02N1](https://kerodon.net/tag/02N1)）。対応表の状態：本体にある。

*主張*　単体集合の射 $`A\to B` は、任意の左ファイブレーション $`\tilde B\to B` について、前合成 $`\operatorname{Fun}_{/B}(B,\tilde B)\to\operatorname{Fun}_{/B}(A,\tilde B)` が Kan 複体のホモトピー同値であるとき左共終である。右共終では右ファイブレーションを用いる。

仮定：任意の単体集合の射 f。A,B の Quasicategory は不要（Kerodon と一致）。結論：任意の左・右ファイブレーションの相対関手空間上で f による前合成が単体的ホモトピー同値（原文の二定義と一致）。

*04-yoneda-adjunction-kan.html — 5. cofinality*

任意の左 fibration $`E\to B` について、切断の空間の制限 $`\mathrm{Fun}_{/B}(B,E)\to\mathrm{Fun}_{/B}(A,E)` がホモトピー同値であること（Kerodon Def. 7.2.1.1）。極限を計算する向きが left、余極限の向きが right である。

:::

:::proposition "kerodon_7_2_1_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.leftAnodyneExtensions_iff_mono_and_isLeftCofinal, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_iff_leftAnodyne_of_mono, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.rightAnodyneExtensions_iff_mono_and_isRightCofinal")
Kerodon Proposition 7.2.1.3（[Tag 02N3](https://kerodon.net/tag/02N3)）。対応表の状態：本体にある。

*主張*　単体集合の射が左無害であることは、左共終かつ単射であることと同値である。右無害性は右共終かつ単射であることと同値である。

仮定：任意の単体集合の射 i（Kerodon と一致）。結論：左 anodyne と Mono i かつ IsLeftCofinal i の iff、および右側の iff（原文と一致）。

:::

:::proposition "kerodon_7_2_1_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.roofTerminalPoint_isRightCofinal, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.terminalPoint_rightAnodyne, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.nervePoint_isLeftCofinal") (uses := "kerodon_1_4_0_1, kerodon_4_7_3_22, kerodon_7_2_1_3")
Kerodon Example 7.2.1.4（[Tag 03LQ](https://kerodon.net/tag/03LQ)）。対応表の状態：一部。

*主張*　無限圏 $`C` の対象 $`x` の包含 $`\{x\}\to C` が右共終であることは $`x` が終対象であることと同値であり、左共終であることは $`x` が始対象であることと同値である。

roofTerminalPoint\_isRightCofinalは終対象Xの点包含がright cofinalというiffの向きを直接返す。任意準圏の逆とleft側のiff全体は含まない。

:::

:::proposition "kerodon_7_2_1_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal.isWeakHomotopyEquivalence, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal.isWeakHomotopyEquivalence") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_3_1_3_2, kerodon_3_1_3_4, kerodon_3_1_7_17, kerodon_3_2_8_1, kerodon_4_4_3_8")
Kerodon Proposition 7.2.1.5（[Tag 02N5](https://kerodon.net/tag/02N5)）。対応表の状態：一部。

*主張*　単体集合の左共終射と右共終射は弱ホモトピー同値である。標的が Kan 複体なら、弱ホモトピー同値は左共終かつ右共終である。

IsLeftCofinal.isWeakHomotopyEquivalenceとRight版は原文(1)の両場合を同じfについて直接返す。Kan終域と弱同値からの逆(2)は含まない。

:::

:::proposition "kerodon_7_2_1_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal.comp, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal.cancel_left, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal.cancel_left")
Kerodon Proposition 7.2.1.6（[Tag 02N6](https://kerodon.net/tag/02N6)）。対応表の状態：本体にある。

*主張*　単体集合の合成 $`gf` で $`f` が左共終なら、$`g` が左共終であることと $`gf` が左共終であることは同値である。特に左共終射は合成で閉じる。

仮定：任意の単体集合の合成可能な i,j と IsLeftCofinal i（Kerodon と一致）。結論：j の左 cofinal 性から合成、合成の左 cofinal 性から j の二方向（原文と一致）。

:::

:::corollary "kerodon_7_2_1_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal.cancel_left, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_iff_leftAnodyne_of_mono, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal.cancel_left, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_iff_rightAnodyne_of_mono")
Kerodon Corollary 7.2.1.7（[Tag 02N7](https://kerodon.net/tag/02N7)）。対応表の状態：本体にある。

*主張*　単体集合の単射 $`f,g` が合成でき、$`f` と $`gf` が左無害なら $`g` は左無害である。三つの左無害性を右無害性に置き換えても成り立つ。

左右それぞれのcofinal/anodyneのmono判定とIsLeft/RightCofinal.cancel\_leftを同じf,gに適用すれば、原文の二つのanodyne消去則を直接得る。専用のanodyne\_cancelという名前の不足はpartial理由にしない。

:::

:::corollary "kerodon_7_2_1_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.nervePoint_isLeftCofinal") (uses := "kerodon_1_4_0_1, kerodon_7_2_1_4, kerodon_7_2_1_6")
Kerodon Corollary 7.2.1.9（[Tag 043E](https://kerodon.net/tag/043E)）。対応表の状態：一部。

*主張*　無限圏の関手 $`F:C\to D` と $`C` の始対象 $`x` に対し、$`F` が左共終であることは $`F(x)` が $`D` の始対象であることと同値である。

Cを一点、Dを通常圏Iのnerve、Fを点包含に制限すれば、通常の始対象cに対するnervePoint\_isLeftCofinalは原文の「始対象の像が始対象ならFはleft cofinal」という向きを直接与える。一般のFのiffは含まない。

:::

:::proposition "kerodon_7_2_1_10" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_2_5_2, kerodon_4_4_2_11, kerodon_4_5_3_31, kerodon_5_6_7_3, kerodon_6_3_1_1, kerodon_6_3_1_9")
Kerodon Proposition 7.2.1.10（[Tag 02N9](https://kerodon.net/tag/02N9)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：局所化の述語と自明 Kan ファイブレーションから両余終性を得る補題はある。任意の指定辺を反転する局所化写像に両余終性を与える型は見つからない。

:::

:::corollary "kerodon_7_2_1_11" (uses := "kerodon_1_1_0_6, kerodon_6_3_5_1")
Kerodon Corollary 7.2.1.11（[Tag 02NA](https://kerodon.net/tag/02NA)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：辺の局所化と左ファイブレーションに沿う右余終性の引き戻しは別々に扱う。すべての基底変換で局所化になる写像に両余終性を与える型は見つからない。

:::

:::corollary "kerodon_7_2_1_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.exists_cofinal_kappaFiltered_poset")
Kerodon Corollary 7.2.1.12（[Tag 02NB](https://kerodon.net/tag/02NB)）。対応表の状態：一部。

*主張*　任意の単体集合 $`C` に、ある半順序集合の神経から左共終かつ右共終な射が存在する。$`C` が有限なら半順序集合も有限に取れる。

Cを正則κに対してκ-filteredな準圏に強めるとexists\_cofinal\_kappaFiltered\_posetは半順序のnerveから同じCへのright cofinal射の存在を直接返す。原文の存在結論のright成分のみで、同じ射のleft cofinal性・有限版は含まない。

:::

:::corollary "kerodon_7_2_1_13" (lean := "CategoryTheory.Functor.final_iff_comp_equivalence, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_of_trivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_trivialKanFibration") (uses := "kerodon_1_1_0_6, kerodon_7_2_1_10")
Kerodon Corollary 7.2.1.13（[Tag 02NC](https://kerodon.net/tag/02NC)）。対応表の状態：一部。

*主張*　単体集合の圏同値は左共終かつ右共終である。

fをtrivial Kan fibrationに強めるとisLeftCofinal\_of\_trivialKanFibrationとRight版は同じfの左右cofinal性を直接返す。一般のcategorical equivalenceは含まない。

:::

:::corollary "kerodon_7_2_1_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.trivialKanFibration_iff_leftFibration_and_isLeftCofinal, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.trivialKanFibration_iff_rightFibration_and_isRightCofinal")
Kerodon Corollary 7.2.1.14（[Tag 02ND](https://kerodon.net/tag/02ND)）。対応表の状態：本体にある。

*主張*　単体集合の射について、左共終かつ左ファイブレーションであること、右共終かつ右ファイブレーションであること、自明な Kan ファイブレーションであることは同値である。

仮定：任意の単体集合の射 f（Kerodon と一致）。結論：TrivialKanFibration f と「左ファイブレーションかつ左 cofinal」、同じく右側の二つの iff（原文の三条件と一致）。

:::

:::corollary "kerodon_7_2_1_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_iff_exists_anodyne_trivialKan_factorization, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal.exists_anodyne_trivialKan_factorization")
Kerodon Corollary 7.2.1.15（[Tag 02NE](https://kerodon.net/tag/02NE)）。対応表の状態：本体にある。

*主張*　単体集合の射は、左無害射に続く自明な Kan ファイブレーションに分解できるとき、かつそのときに限り左共終である。

仮定：任意の単体集合の射 f（Kerodon と一致）。結論：IsLeftCofinal f と、左 anodyne i と自明 Kan ファイブレーション p を使う i≫p=f の存在の iff（原文と一致）。

:::

:::corollary "kerodon_7_2_1_16" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_iff_leftAnodyne_of_mono, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_of_leftAnodyne, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions")
Kerodon Corollary 7.2.1.16（[Tag 02NF](https://kerodon.net/tag/02NF)）。対応表の状態：一部。

*主張*　単体集合の圏論的押し出し正方形で上辺が左共終なら、下辺も左共終である。

四角をstrict pushout、fをmonoにも強めると、cofinal/anodyneのmono判定、leftAnodyneExtensionsのcobase change閉性、left anodyne⇒left cofinalを同じf,f′に順に適用して原文の結論を直接得る。任意のcategorical pushoutは含まない。

:::

:::corollary "kerodon_7_2_1_17"
Kerodon Corollary 7.2.1.17（[Tag 02NH](https://kerodon.net/tag/02NH)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：個別の左アノダイン射の余終性に関する候補を確認した。矢印圏のフィルター付き図式とその余極限上の左余終性を扱う型は見つからない。

:::

:::corollary "kerodon_7_2_1_18"
Kerodon Corollary 7.2.1.18（[Tag 02NJ](https://kerodon.net/tag/02NJ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：左アノダイン性を単射と左余終性で特徴付ける型はある。フィルター付き図式の余極限で性質が閉じる型は見つからない。

:::

:::corollary "kerodon_7_2_1_19" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_whiskerRight, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_whiskerLeft, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal.op, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal.op, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_iff_isRightCofinal_op") (uses := "kerodon_1_1_0_6, kerodon_4_2_5_3, kerodon_7_2_1_15")
Kerodon Corollary 7.2.1.19（[Tag 02NK](https://kerodon.net/tag/02NK)）。対応表の状態：本体にある。

*主張*　単体集合の左共終射 $`f` に対し、任意の単体集合 $`K` との積 $`f\times\mathrm{id}_K` も左共終である。

IsLeftCofinal.opで右側へ移しisRightCofinal\_whiskerRightを適用してopで戻す。MathlibのopFunctorのmonoidal構造の積比較はIso.reflなので元と同じf×id\_Kに戻り、追加の数学的比較は不要。原文全体を直接得る。

:::

:::corollary "kerodon_7_2_1_20" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_whiskerRight, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal.comp, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal.op, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal.op, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_iff_isRightCofinal_op, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_whiskerLeft")
Kerodon Corollary 7.2.1.20（[Tag 02NL](https://kerodon.net/tag/02NL)）。対応表の状態：本体にある。

*主張*　単体集合の二つの左共終射の直積は左共終である。

opで右側へ移し、左右のwhiskerのright cofinal性とIsRightCofinal.compを合成すれば同じ積射f×f′がright cofinal。opFunctorの積比較は恒等で、CofinalOppositeで戻すと原文のleft cofinal性そのもの。

:::

:::proposition "kerodon_7_2_1_21" (lean := "CategoryTheory.Functor.final_iff_final_comp, CategoryTheory.Functor.final_iff_comp_equivalence, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_of_isIso, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal.comp") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_5_6_0_6, kerodon_7_2_1_13")
Kerodon Proposition 7.2.1.21（[Tag 02NM](https://kerodon.net/tag/02NM)）。対応表の状態：一部。

*主張*　合成可能な単体集合の射 $`f,g` で $`g` が圏同値なら、$`f` が左共終であることと $`gf` が左共終であることは同値である。

gを単体集合の厳密同型に強めれば、gと逆射はいずれもleft cofinal。IsLeftCofinal.compを各方向に適用しgf≫g⁻¹=fで戻せば同じfのiffを直接得る。一般の圏同値は含まない。

:::

:::corollary "kerodon_7_2_1_22" (lean := "CategoryTheory.Functor.initial_iff_comp_equivalence, CategoryTheory.Functor.initial_iff_equivalence_comp, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal.of_arrow_iso") (uses := "kerodon_1_1_0_6, kerodon_7_2_1_6, kerodon_7_2_1_21")
Kerodon Corollary 7.2.1.22（[Tag 02NN](https://kerodon.net/tag/02NN)）。対応表の状態：一部。

*主張*　単体集合の可換正方形の二本の縦の射が圏同値なら、上辺が左共終であることと下辺が左共終であることは同値である。

g,g′を厳密同型に強めると可換四角は同じf,f′のArrow同型。IsLeftCofinal.of\_arrow\_isoとそのsymmへの適用が原文のiffを直接返す。通常圏のInitialのiffは根拠にしない。

:::

:::corollary "kerodon_7_2_1_23"
Kerodon Corollary 7.2.1.23（[Tag 02NP](https://kerodon.net/tag/02NP)）。対応表の状態：なし。

of\_arrow\_isoは始域・終域の厳密同型による移送。原文のFunctor準圏内の二図式の同型から、そのようなArrow同型を作る型はなく、Mathlibの通常圏のFinalも同じ述語への橋がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal.of_arrow_iso`、`CategoryTheory.Functor.final_of_natIso`

:::

# 7.2.2 Cofinality and Limits

%%%
number := false
tag := "kerodon-7-2-2"
%%%

Kerodon [Tag 02NQ](https://kerodon.net/tag/02NQ)

:::proposition "kerodon_7_2_2_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.sliceOverRestrict_isQCatEquivalence_of_leftCofinal, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.sliceUnderRestrict_equivalence_of_rightCofinal") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_3_6_5, kerodon_4_4_5_3, kerodon_4_5_3_30, kerodon_4_5_5_8, kerodon_4_5_5_9, kerodon_4_5_5_10, kerodon_4_5_5_11, kerodon_4_6_2_3, kerodon_4_6_2_8, kerodon_4_6_2_9, kerodon_4_6_4_14, kerodon_4_6_4_15, kerodon_4_6_4_19, kerodon_5_1_7_1, kerodon_5_1_7_5, kerodon_5_1_7_16, kerodon_5_6_0_6, kerodon_7_2_1_1, kerodon_7_2_1_15")
Kerodon Proposition 7.2.2.1（[Tag 02NR](https://kerodon.net/tag/02NR)）。対応表の状態：一部。

*主張*　単体集合の射 $`F:A\to B` が左共終であることは、左錐の比較正方形または $`\Delta^0\diamond-` による比較正方形が圏論的押し出しであることと同値である。すべての無限圏 $`C` と $`G:B\to C` で、$`F` に沿う制限がスライスまたは対応する向き付きファイバー積の同値を誘導することとも同値である。これは各定数図式から $`G` への射空間、または $`C_{x/}\to C` 上の持ち上げの空間に対するホモトピー同値の条件とも同値である。

Bを準圏に強めるとsliceOverRestrict\_isQCatEquivalence\_of\_leftCofinalは原文(1)⇒(5)の同じ制限射の圏同値性を直接返す。右cofinalのcoslice版は左側の全七条件の代用にはしない。

:::

:::corollary "kerodon_7_2_2_2" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_7_2_2_1")
Kerodon Corollary 7.2.2.2（[Tag 02XQ](https://kerodon.net/tag/02XQ)）。対応表の状態：なし。

引用はright anodyneによる相対余極限余錐の制限。原文はleft cofinalによる相対極限錐であり、反転した制限錐との比較を型に含まない。双対の類似だけでは数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.kanIsRelativeColimitCone_iff_restrict_of_rightAnodyne`

:::

:::corollary "kerodon_7_2_2_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLimitCone_iff_restrict_of_leftCofinal, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isColimitCone_iff_restrict_rightCofinal") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_7_2_2_2")
Kerodon Corollary 7.2.2.3（[Tag 02XR](https://kerodon.net/tag/02XR)）。対応表の状態：一部。

*主張*　単体集合の左共終射 $`e:A\to B` で、無限圏への左錐 $`B^{\triangleleft}\to C` が極限図式であることは、その $`A^{\triangleleft}` への制限が極限図式であることと同値である。

Bを準圏に強めればisLimitCone\_iff\_restrict\_of\_leftCofinalは原文の同じ錐とeによる制限の極限性のiffを直接返す。

:::

:::corollary "kerodon_7_2_2_5" (uses := "kerodon_1_4_0_1, kerodon_4_7_3_22, kerodon_5_1_1_1, kerodon_7_2_2_2")
Kerodon Corollary 7.2.2.5（[Tag 02XV](https://kerodon.net/tag/02XV)）。対応表の状態：なし。

引用は終対象の点に制限した相対余極限とのiff。原文はその制限したΔ¹の辺がU-cocartesianであることとのiffであり、相対余極限とcocartesian辺を同定する比較がこの型にない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.kanIsRelativeColimitCone_iff_restrict_terminal`

:::

:::corollary "kerodon_7_2_2_6" (uses := "kerodon_1_4_0_1, kerodon_5_1_1_4, kerodon_7_2_2_5")
Kerodon Corollary 7.2.2.6（[Tag 02XW](https://kerodon.net/tag/02XW)）。対応表の状態：なし。

initialCofinalityはnerve上のslice制限の同値。原文の錐の指定辺が可逆というiffまで直接結論する型ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialCofinality`、`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialRestriction_isQCatEquivalence`

:::

:::corollary "kerodon_7_2_2_7" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_6_2_8, kerodon_7_1_1_1, kerodon_7_2_2_3")
Kerodon Corollary 7.2.2.7（[Tag 02XS](https://kerodon.net/tag/02XS)）。対応表の状態：なし。

join錐の制限の判定と通常圏の錐のwhisker判定はあるが、原文の指定αの定値関手のHom作用が同じ制限の射になる比較を引用型に持たない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLimitCone_iff_restrict_of_leftCofinal`、`CategoryTheory.Functor.Initial.isLimitWhiskerEquiv`

:::

:::corollary "kerodon_7_2_2_8" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Corollary 7.2.2.8（[Tag 02NV](https://kerodon.net/tag/02NV)）。対応表の状態：なし。

MathlibのPreservesLimit\_comp\_iffは通常圏のInitial/Finalと通常錐に関する型。原文の任意単体形状の∞圏の保存性と比較するnerveの型がない。

宣言：`CategoryTheory.Functor.Initial.preservesLimit_comp_iff`

:::

:::proposition "kerodon_7_2_2_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.hasLimit_iff_restrict_of_leftCofinal, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.hasLimit_of_leftCofinal") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_7_1_6_9, kerodon_7_2_1_15, kerodon_7_2_2_2")
Kerodon Proposition 7.2.2.9（[Tag 02XT](https://kerodon.net/tag/02XT)）。対応表の状態：一部。

*主張*　無限圏の内部ファイブレーション $`U:C\to D` と、$`f:B\to C` の像を延長する底の左錐 $`\bar g` を取る。$`f` が $`\bar g` 上で $`U`-極限図式に延長できることは、左共終射 $`e:A\to B` に沿う制限 $`fe` が $`\bar g e^{\triangleleft}` 上で $`U`-極限図式に延長できることと同値である。

Dを一点、Uを終写像、Bを準圏に限ると原文の相対持ち上げは絶対極限錐の存在となり、hasLimit\_iff\_restrict\_of\_leftCofinalが同じfとeについてこのiffを直接返す。

:::

:::corollary "kerodon_7_2_2_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.hasLimit_iff_restrict_of_leftCofinal, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.hasLimit_of_leftCofinal") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_7_2_2_3, kerodon_7_2_2_9")
Kerodon Corollary 7.2.2.10（[Tag 02NS](https://kerodon.net/tag/02NS)）。対応表の状態：一部。

*主張*　単体集合の左共終射 $`e:A\to B` に沿う制限について、無限圏の図式 $`f:B\to C` の極限の存在と $`fe` の極限の存在は同値である。

Bを準圏に強めるとhasLimit\_iff\_restrict\_of\_leftCofinalは原文と同じfの極限存在とeによる制限の極限存在のiffを直接返す。

:::

:::corollary "kerodon_7_2_2_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLimitCone_iff_restrict_of_leftCofinal") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_7_1_1_13, kerodon_7_2_2_10")
Kerodon Corollary 7.2.2.11（[Tag 02XU](https://kerodon.net/tag/02XU)）。対応表の状態：一部。

*主張*　単体集合の左共終射 $`e:A\to B` に沿う制限について、無限圏 $`C` の対象が図式 $`f:B\to C` の極限であることと $`fe` の極限であることは同値である。

Bを準圏に強めると、頂点Xを持つ極限錐cにisLimitCone\_iff\_restrict\_of\_leftCofinalを適用して、同じ頂点を保った制限錐の極限性を直接得る。Xが制限の極限なら元でも極限となる逆向きの存在は含まない。

:::

:::corollary "kerodon_7_2_2_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.hasLimit_of_leftCofinal") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Corollary 7.2.2.12（[Tag 02NU](https://kerodon.net/tag/02NU)）。対応表の状態：一部。

*主張*　単体集合の左共終射 $`A\to B` があり無限圏が $`A` 添字の極限を持てば、$`B` 添字の極限も持つ。右共終射と余極限についても同様である。

Bを準圏に強めると、全A図式の極限存在をu≫Fに適用しhasLimit\_of\_leftCofinalを使うだけで原文の極限側の全B図式の存在を直接得る。余極限側は含まない。

:::

:::corollary "kerodon_7_2_2_13"
Kerodon Corollary 7.2.2.13（[Tag 02NW](https://kerodon.net/tag/02NW)）。対応表の状態：なし。

MathlibのcreatesLimitsOfShapeOfInitialとcolimit版は通常圏の錐の創出。原文の∞圏・任意単体形状の保存されたjoin錐との比較がない。

宣言：`CategoryTheory.Functor.Initial.createsLimitsOfShapeOfInitial`、`CategoryTheory.Functor.Final.createsColimitsOfShapeOfFinal`

:::

:::corollary "kerodon_7_2_2_14" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_7_3_22, kerodon_5_1_4_1, kerodon_7_2_2_9")
Kerodon Corollary 7.2.2.14（[Tag 039B](https://kerodon.net/tag/039B)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対極限錐の述語はある。底の指定錐と上の図式を受け、形状の終対象を仮定して U-極限となる持ち上げを返す型は見つからない。

:::

# 7.2.3 Quillen's Theorem A for ∞-Categories

%%%
number := false
tag := "kerodon-7-2-3"
%%%

Kerodon [Tag 02NX](https://kerodon.net/tag/02NX)

:::theorem "kerodon_7_2_3_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_iff_weaklyContractible_slices, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_iff_weaklyContractible_coslices")
Kerodon Theorem 7.2.3.1（[Tag 02NY](https://kerodon.net/tag/02NY)）。対応表の状態：本体にある。

*主張*　無限圏 $`D` への単体集合の射 $`F:C\to D` は、各対象 $`x\in D` で $`C\times_D D_{/x}` が弱可縮であるとき、かつそのときに限り左共終である。右共終では各 $`C\times_D D_{x/}` の弱可縮性を課す。

仮定：f:A→B と Quasicategory B。A の∞圏性は不要（Kerodon と一致）。結論：全頂点 b について f と slice・coslice の忘却射の引き戻しが弱可縮となることと、左右 cofinal 性の二つの iff（原文と一致）。

:::

:::corollary "kerodon_7_2_3_4" (uses := "kerodon_1_1_0_6, kerodon_3_2_8_5, kerodon_4_9_1_26, kerodon_7_2_1_1, kerodon_7_2_3_1")
Kerodon Corollary 7.2.3.4（[Tag 03U2](https://kerodon.net/tag/03U2)）。対応表の状態：なし。

Monotone.final\_functor\_iffは通常圏のFinalと順序的cofinalityのiff。原文が判定する同じnerve写像のIsRightCofinalへの比較がなく、通常圏の類似だけは数えない。

宣言：`Monotone.final_functor_iff`

:::

:::corollary "kerodon_7_2_3_5"
Kerodon Corollary 7.2.3.5（[Tag 02XX](https://kerodon.net/tag/02XX)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：定値図式の定値錐は構成される。指定錐の全辺が可逆であることと、底の全辺が可逆で錐が極限であることの iff は見つからない。

:::

:::corollary "kerodon_7_2_3_6" (uses := "kerodon_1_4_0_1, kerodon_7_1_6_10, kerodon_7_2_2_6")
Kerodon Corollary 7.2.3.6（[Tag 02XY](https://kerodon.net/tag/02XY)）。対応表の状態：なし。

引用は一点への制限による相対余極限のiff。原文の指定辺の可逆性から、その一点の相対余極限性を直接結論する型が引用にない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.kanIsRelativeColimitCone_iff_restrict_terminal`

:::

:::corollary "kerodon_7_2_3_7" (lean := "SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.nerveMap_leftAdjoint_isLeftCofinal") (uses := "kerodon_1_4_0_1, kerodon_4_7_3_23, kerodon_6_2_6_2, kerodon_7_2_3_1")
Kerodon Corollary 7.2.3.7（[Tag 02P3](https://kerodon.net/tag/02P3)）。対応表の状態：一部。

*主張*　無限圏の左随伴は左共終であり、右随伴は右共終である。

Fを通常圏の随伴L⊣RのnerveMap Lに制限すると、OE-W1後のFrameArrowCofinalityにあるnerveMap\_leftAdjoint\_isLeftCofinalは同じFのleft cofinal性を直接返す。MathlibのFinal Rだけはright cofinal性の証拠としない。

:::

:::corollary "kerodon_7_2_3_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_constantDiagram_iff")
Kerodon Corollary 7.2.3.9（[Tag 02P4](https://kerodon.net/tag/02P4)）。対応表の状態：本体にある。

*主張*　無限圏 $`C` の対角関手 $`C\to\operatorname{Fun}(K,C)` が右共終であることは、全ての図式 $`f:K\to C` の余スライス $`C_{f/}` が弱可縮であることと同値である。

仮定：Quasicategory C と任意の K（Kerodon と一致）。結論：constantDiagram K C の右 cofinal 性と全 p:K→C の sliceUnder p の弱可縮性の iff（原文と一致）。

:::

:::proposition "kerodon_7_2_3_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.leftFibration_pullback_isRightCofinal, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_pullback_fst_of_vertexFibers") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_1_5_4_13, kerodon_5_1_4_1, kerodon_5_3_4_9, kerodon_5_3_6_3, kerodon_5_3_6_5, kerodon_7_2_1_3, kerodon_7_2_1_15, kerodon_7_2_1_22")
Kerodon Proposition 7.2.3.10（[Tag 02P6](https://kerodon.net/tag/02P6)）。対応表の状態：一部。

*主張*　単体集合の右共終射を余デカルトファイブレーションに沿って引き戻した射は右共終である。

πをleft fibrationに強めればleftFibration\_pullback\_isRightCofinalは同じpullback第一射影Fのright cofinal性を直接返す。一般cocartesian fibrationではない。

:::

:::corollary "kerodon_7_2_3_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.leftFibration_pullback_rightAnodyne, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.leftFibration_lastHorn_pullback_rightAnodyne") (uses := "kerodon_1_1_0_6, kerodon_5_1_4_1, kerodon_7_2_1_3, kerodon_7_2_3_10")
Kerodon Corollary 7.2.3.11（[Tag 02P7](https://kerodon.net/tag/02P7)）。対応表の状態：一部。

*主張*　単体集合の右無害射を余デカルトファイブレーションに沿って引き戻した射は右無害である。

πをleft fibrationに強めればleftFibration\_pullback\_rightAnodyneは原文と同じ引き戻したFのright anodyne性を直接返す。

:::

:::proposition "kerodon_7_2_3_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.roofLeftFibration_terminalFiber_isRightCofinal, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.leftFibration_terminalFiber_rightAnodyne, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_iff_rightAnodyne_of_mono")
Kerodon Example 7.2.3.12（[Tag 03J8](https://kerodon.net/tag/03J8)）。対応表の状態：一部。

*主張*　無限圏の余デカルトファイブレーション $`C\to D` で、$`D` の終対象上のファイバーの $`C` への包含は右無害であり、従って右共終である。

πをleft fibrationに強めればroofLeftFibration\_terminalFiber\_isRightCofinalは同じfiber包含のright cofinal性を返す。fiber包含はmonoなのでright cofinal/anodyneのmono判定も適用でき、原文のright anodyne性まで直接得る。一般cocartesianの場合は含まない。

:::

:::corollary "kerodon_7_2_3_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.leftFibration_pullback_isRightCofinal, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal.isWeakHomotopyEquivalence") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_1_3_3, kerodon_4_7_3_23, kerodon_5_1_4_1, kerodon_5_1_4_15, kerodon_7_2_1_5, kerodon_7_2_1_13, kerodon_7_2_1_21, kerodon_7_2_3_1, kerodon_7_2_3_10")
Kerodon Corollary 7.2.3.13（[Tag 05ZU](https://kerodon.net/tag/05ZU)）。対応表の状態：一部。

*主張*　単体集合の射 $`F:C\to D` が右共終であることは、任意の余デカルトファイブレーションに沿う引き戻しが右共終であることと同値である。任意の左ファイブレーションに沿う引き戻しが弱ホモトピー同値であることとも同値であり、全体が弱可縮な左ファイブレーションに限って引き戻した全体の弱可縮性を課してもよい。

leftFibration\_pullback\_isRightCofinalとIsRightCofinal.isWeakHomotopyEquivalenceの合成は原文(1)⇒(3)を同じFの全left-fibration引き戻しについて直接返す。一般cocartesian版(2)と全逆向きは含まない。

:::

:::corollary "kerodon_7_2_3_14" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_1_3_3, kerodon_4_5_6_1, kerodon_4_7_3_20, kerodon_4_7_3_21, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_1_4_9, kerodon_5_1_4_22, kerodon_5_3_6_6, kerodon_5_6_7_2, kerodon_7_2_1_22, kerodon_7_2_3_1, kerodon_7_2_3_10")
Kerodon Corollary 7.2.3.14（[Tag 03LR](https://kerodon.net/tag/03LR)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：各頂点での coslice の弱可縮性との iff はある。cartesian 辺を保つ全空間の写像と指定したファイバー写像の右余終性を比較する型は見つからない。

:::

