-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ConeFamily
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CosliceCoconeFamilyEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CosliceFixedDiagramIso
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CosliceLaxEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceCylinderFunctorIso
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceFullyFaithful
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoin
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinComparison
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinComparisonGluing
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinFixedDiagramComparison
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinGeneralComparison
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinStdComparison
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FullyFaithfulIntervalMapping
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingSpace
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinEquivalenceFunctor
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LaxPullback
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LaxPullbackProjections
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LaxSlice
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceIntervalComparison
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceLeft
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceModelEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceRightKan
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PointedConeHornLifting
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PointedConeLeftFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PreFiberKan
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RelativeCylinderExtension
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RelativeEquivalenceCylinder
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RelativeMappingCylinder
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RightConeBoundary
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RightIntervalEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SliceConeFamilyEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SliceFixedDiagramIso
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SliceLaxEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SliceLaxMap
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "4.6 Morphism Spaces" =>
%%%
number := false
tag := "kerodon-4-6"
%%%

Kerodon の 4.6 節（[Tag 01J3](https://kerodon.net/tag/01J3)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

*route-classification.html — 3. 段 1：写像空間・同値・関手の ∞ 圏 — 3.4（1.4）写像空間 $`\mathrm{Map}_{\mathcal C}(x,y)`*

*比較*：$`\Delta^n\times\Delta^1\to\Delta^{n+1}`、$`(i,0)\mapsto i`、$`(i,1)\mapsto n+1` で引き戻して $`\mathrm{Hom}^R\to\mathrm{Map}`（$`\mathrm{Hom}^L` も同様）。これらはホモトピー同値（HTT Cor. 4.2.1.8、Kerodon §4.6）。証明は「$`\mathcal C_{/y}` と $`\mathrm{Fun}(\Delta^1,\mathcal C)\times_{\mathcal C}\{y\}` という $`\mathcal C` 上の右 fibration の間の写像が fiber ごとに同値」で、段 2 の判定法で回収する。

*合成*：厳密な合成はない。$`\mathrm{Fun}(\Delta^2,\mathcal C)\to\mathrm{Fun}(\Lambda^2_1,\mathcal C)` の $`(x,y,z)` 上の fiber が自明 Kan fibration $`\to\mathrm{Map}(x,y)\times\mathrm{Map}(y,z)` になり、切断を選んで $`\{0,2\}` に制限すると合成。可縮な選択を除いて一意。

*使われ方*：充満忠実（1.6）、段 3 の $`\mathcal S` の写像空間の比較、段 6 の充満忠実性。

*模型の比較（質問への答え）*：模型 3 が一番すっきりするという感覚は正しく、現代的な扱いもその方向。ただし計算には $`\mathrm{Hom}^R`、$`N^{hc}` との比較には $`\mathfrak C[-]` が要り、「定義は一つ、計算用の模型は別」という使い分けになる。

- 模型　／　長所　／　短所　／　主な使われ方
- $`\mathrm{Fun}(\Delta^1,\mathcal C)` の fiber　／　左右対称、$`\mathrm{Fun}`・極限・随伴と同じ言葉、$`(\mathrm{ev}_0,\mathrm{ev}_1)` が isofibration なので fiber がホモトピー fiber、$`\mathrm{Map}_{\mathrm{Fun}(K,\mathcal C)}(F,G)` も同じ形　／　単体が角柱で大きい、Kan 性に各点判定が要る　／　定義（Kerodon §4.6.1、Riehl–Verity）
- $`\mathrm{Hom}^R`・$`\mathrm{Hom}^L`（pinched）　／　単体が小さく端が厳密に固定、Kan 性が直ちに出る、表現可能前層と直結　／　左右非対称で比較に定理が要る、$`x,y` 同時には関手的でない　／　計算（HTT §1.2.2、Kerodon §4.6.5）、dg nerve では Hom 複体の切り詰めと対応
- $`\mathfrak C\mathcal C`　／　合成が厳密　／　一般に Kan でない、比較に重い定理（HTT §2.2）　／　straightening、$`N^{hc}` との比較（段 3）
- twisted arrow の fiber　／　$`x,y` 両方について関手的　／　$`\mathrm{Tw}(\mathcal C)` が先に要る　／　米田（Yoneda への道 段 7）

現代的な扱い：Kerodon は模型 3 を定義とし pinched を同値な計算模型とする（HTT は $`\mathrm{Hom}^R` と $`\mathfrak C` が主）。Riehl–Verity は comma ∞ 圏（$`A^{\Delta^1}\to A\times A` の fiber）、Riehl–Shulman の単体的ホモトピー型理論は hom 型を端点を固定した $`\Delta^1\to A` の型とする。このルートでは定義を模型 3、計算道具を $`\mathrm{Hom}^R` とし、$`\mathfrak C` の模型は段 3 で導入する。

\*\*四つ目の模型 $`\mathfrak C\mathcal C`\*\*：$`N^{hc}` の左随伴 $`\mathfrak C`（単体的集合 → 単体的圏、$`\mathfrak C\Delta^n=(\Delta^1)^{n-1}`）の Hom。段 3 で $`\mathrm{Map}_{N^{hc}(D)}(x,y)\simeq D(x,y)`（$`D` Kan 豊穣）を示すときに、余単位 $`\mathfrak C[N^{hc}D]\to D` を通して使う。つまり $`N^{hc}` で定義された ∞ 圏（$`\mathcal S`、$`\mathrm{Cat}_\infty`）の写像空間を計算するための道具。

\*\*質問：$`\mathcal C` が準圏であることは重要か\*\*。模型によって違う。

- 模型　／　任意の単体的集合 $`S` で
- $`\mathrm{Hom}^R`、$`\mathrm{Hom}^L`、$`\mathrm{Fun}(\Delta^1,S)` の fiber　／　定義はできるが意味を持たない（Kan とは限らず、$`S` が生成する ∞ 圏の写像空間とも一致しない）。Kan 性も比較も内ホーンの充填を使う
- $`\mathfrak CS`　／　常に正しい：$`S` が生成する ∞ 圏の写像空間を与える（$`\mathfrak C` は圏同値を Dwyer–Kan 同値に送る）。ただし $`S` が準圏でないと $`\mathrm{Hom}^R` との比較は成り立たない

例：$`S=\Lambda^2_1`（$`0\to1\to2`）では $`\mathrm{Hom}^R_S(0,2)=\emptyset`（辺 $`0\to2` がない）が、生成する ∞ 圏 $`\Delta^2` では $`\mathrm{Map}(0,2)=\mathrm{pt}`、$`\mathfrak C\Lambda^2_1=\mathrm{pt}` は正しい。$`S=\partial\Delta^2` では $`\mathrm{Hom}^R_S(0,2)=\mathrm{pt}`（辺 $`\{0,2\}` だけ）だが、生成する圏では $`0\to2` が $`\{0,2\}` と合成の 2 本、$`\mathfrak C\partial\Delta^2` も 2 点で正しい。$`\mathfrak C` は「単体的集合を自由に生成された ∞ 圏として読む」関手なので、準圏性は要らない。

*Lean での扱い*：Kerodon §4.6.5 に沿って右 pinched 写像空間（＝ $`\mathrm{Hom}^R`）が主な模型。

# 4.6.1 Morphism Spaces

%%%
number := false
tag := "kerodon-4-6-1"
%%%

Kerodon [Tag 01J4](https://kerodon.net/tag/01J4)

:::definition "kerodon_4_6_1_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace")
Kerodon Construction 4.6.1.1（[Tag 01J5](https://kerodon.net/tag/01J5)）。対応表の状態：本体にある。

*主張*　単体集合 $`C` の頂点 $`x,y` の間の射の単体集合 $`\operatorname{Hom}_C(x,y)` は、$`\operatorname{Fun}(\Delta^1,C)\to C\times C` の端点 $`(x,y)` 上のファイバーである。

仮定：単体集合 X と頂点 x,y（Kerodon と一致）。結論：intervalMappingSpace x y は Fun(Δ¹,X) の境界制限を (x,y) 上で取ったファイバー（一致）。

:::

:::definition "kerodon_4_6_1_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace")
Kerodon Variant 4.6.1.3（[Tag 03X9](https://kerodon.net/tag/03X9)）。対応表の状態：本体にある。

*主張*　無限圏の対象 $`x` の自己射空間は $`\operatorname{Hom}_C(x,x)` であり、$`\operatorname{Fun}(\Delta^1/\partial\Delta^1,C)` の基点評価の $`x` 上のファイバーとしても表せる。頂点は $`x` の自己射である。

仮定：∞ 圏の頂点 x（Lean が弱い：構成は任意の SSet）。結論：両端を同じ x にした intervalMappingSpace x x が自己写像空間（一致）。

:::

:::proposition "kerodon_4_6_1_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace_kanComplex, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHom_kanComplex")
Kerodon Proposition 4.6.1.10（[Tag 01JC](https://kerodon.net/tag/01JC)）。対応表の状態：本体にある。

*主張*　無限圏の任意の二対象の間の射空間は Kan 複体である。

仮定：Quasicategory X と任意の頂点 x,y（Kerodon と一致）。結論：intervalMappingSpace x y が KanComplex。右 pinched 版にも同じ結論がある（一致）。

:::

:::proposition "kerodon_4_6_1_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanComplex_preFiber_of_vertexSurjective")
Kerodon Proposition 4.6.1.11（[Tag 01P1](https://kerodon.net/tag/01P1)）。対応表の状態：本体にある。

*主張*　無限圏 $`C` と全頂点を含む単体部分集合 $`A\subseteq B` に対し、任意の $`f:A\to C` の $`B` への延長の単体集合は Kan 複体である。

仮定：Quasicategory X、頂点全射な単射 j:A→B、Fun(A,X) の頂点 p（Kerodon と一致）。結論：制限 (pre j).app X の p 上のファイバーが KanComplex（一致）。

:::

:::proposition "kerodon_4_6_1_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IsQCatEquivalence.isFullyFaithful, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IsFullyFaithful.intervalMappingPost_isQCatEquivalence")
Kerodon Proposition 4.6.1.14（[Tag 06QP](https://kerodon.net/tag/06QP)）。対応表の状態：本体にある。

*主張*　無限圏の同値 $`F:C\to D` は、任意の $`x,y\in C` で $`\operatorname{Hom}_C(x,y)\to\operatorname{Hom}_D(Fx,Fy)` に Kan 複体のホモトピー同値を誘導する。

仮定：∞ 圏間の圏同値 F、始域の頂点 x,y（Lean が弱い：写像空間の補題は充満忠実性で足りる）。結論：intervalMappingPost F x y は圏同値。ここで両辺は Kan 複体なのでホモトピー同値（一致）。

:::

:::definition "kerodon_4_6_1_16" (uses := "kerodon_1_1_0_6")
Kerodon Construction 4.6.1.16（[Tag 01P2](https://kerodon.net/tag/01P2)）。対応表の状態：なし。

引用に現れるのは右pinchedHomMapの頂点fiberで、原文の区間模型のHom\_C(X,Y)上の指定辺のfiberとの比較がない。定義の対象と相対写像の同一視が必要。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomMap_vertexFiber_kanComplex`

:::

:::proposition "kerodon_4_6_1_21"
Kerodon Proposition 4.6.1.21（[Tag 01P7](https://kerodon.net/tag/01P7)）。対応表の状態：なし。

右pinched模型の指定fiberのKan性で、原文の区間模型のfiberのKan性ではない。両模型の弱同値だけでもKan性は移らず、特定fiberの同型などの比較が要る。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomMap_vertexFiber_kanComplex`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomMap_rightFibration`

:::

:::proposition "kerodon_4_6_1_22" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_6_1_24")
Kerodon Proposition 4.6.1.22（[Tag 01P8](https://kerodon.net/tag/01P8)）。対応表の状態：なし。

pinchedHomMapのホーン持ち上げは別模型の射の性質。原文の区間模型のHomへの誘導射と厳密に比較する宣言を欠く。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomMap_hasLiftingProperty_horn`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomMap_rightFibration`

:::

:::proposition "kerodon_4_6_1_24" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomMap_hasLiftingProperty_horn, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomMap_rightFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanComplex_preFiber_of_vertexSurjective") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_4_3_10, kerodon_4_4_5_11, kerodon_4_6_1_11")
Kerodon Proposition 4.6.1.24（[Tag 01PC](https://kerodon.net/tag/01PC)）。対応表の状態：一部。

*主張*　無限圏の内部ファイブレーション $`q:C\to D`、全頂点を含む単体部分集合 $`A\subseteq B`、図式 $`f:A\to C` を取る。$`f` の $`B` への延長の単体集合から、$`qf` の延長の単体集合への射は Kan ファイブレーションである。

kanComplex\_preFiber\_of\_vertexSurjective は底Dが終対象の場合の同じ、全頂点を含むAからの制限の指定fiberのKan性を直接返す。右pinched模型の候補は区間模型との比較がなく数えない。一般の相対底は含まない。

:::

# 4.6.2 Digression: Universal Property of the Join

%%%
number := false
tag := "kerodon-4-6-2"
%%%

Kerodon [Tag 01HM](https://kerodon.net/tag/01HM)

*02-mapping-limits.html — 5. 極限 — 補助模型：fat join、lax slice、錐の族*

関手 ∞ 圏の極限を扱うには、slice $`X_{/p}` のままでは $`\mathrm{Fun}(K,-)` との相性が悪い。そこで Kerodon §4.6.2〜4.6.6 に沿って、三つの補助模型を導入し、すべて slice と同値であることを示している。

- 模型　／　中身　／　slice との比較
- fat join $`A\diamond B`　／　$`A\times\Delta^1\times B` の 0 端を $`A` に、1 端を $`B` に潰したもの（Kerodon Notation 4.6.2.3）　／　\`fatJoinComparison : fatJoin A B ⟶ join A B\`（Kerodon Thm. 4.6.2.8）
- lax slice（太い slice）　／　fat join から作る slice　／　\`isQCatEquivalence\_sliceLaxMap\`（Kerodon Prop. 4.6.4.19）
- 錐の族 \`coneFamily\`　／　錐を関手 ∞ 圏 $`\mathrm{Fun}(\Delta^0\star K,X)` の fiber として見たもの　／　\`isQCatEquivalence\_sliceConeFamilyMap\`（Kerodon Ex. 4.6.6.8）

錐の族の模型では、錐が関手 ∞ 圏の対象になる。そのため $`\mathrm{Fun}(K,-)` との交換が内部 Hom の curry だけで済む。\`isLimitCone\_iff\_isTerminalVertex\_coneFamily\`（Core/LimitConeFamily）が、極限性をこの模型に移す入口である。

原典との違い

HTT は slice $`X_{/p}` と fat slice $`X^{/p}` の比較を Joyal のモデル構造で処理する（HTT Prop. 4.2.1.5）。ここでは Kerodon の方針に従い、標準単体の場合を明示的な変形（Core/FatJoinStd\*）で示してから、pushout・余極限での閉包性で一般化している（Core/FatJoinLeftColimits、FatJoinRightColimits など）。Core/Precomposition\* の判定条件 \`IsPrecompositionEquivalence\`（「任意の quasicategory への前合成が同値」）は、quasicategory でない補助模型の比較のために導入されている。

:::definition "kerodon_4_6_2_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap")
Kerodon Construction 4.6.2.1（[Tag 01HN](https://kerodon.net/tag/01HN)）。対応表の状態：一部。

*主張*　単体集合 $`X,Y` の縮約射 $`X\times\Delta^1\times Y\to X\star Y` は、$`\Delta^1` への単体の零区間で $`X` の成分を、一区間で $`Y` の成分を採る。この射は、零端で $`X`、一端で $`Y` の射影に一致するように一意に定まる。

joinCylinderMap は原文の順序の切断による同じcollapseの写像を直接構成する。指定両端だけからの一意性は引用型に含まない。

:::

:::proposition "kerodon_4_6_2_2"
Kerodon Proposition 4.6.2.2（[Tag 01HP](https://kerodon.net/tag/01HP)）。対応表の状態：なし。

fatJoinComparisonの前合成同値性は関連する比較射の命題。原文の指定四角がcoreのホモトピーpullbackを与えることへの判定の比較がさらに必要で、同値な言い換えという説明だけではpartialにしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_fatJoinComparison`

:::

:::definition "kerodon_4_6_2_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStage, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison")
Kerodon Notation 4.6.2.3（[Tag 01HR](https://kerodon.net/tag/01HR)）。対応表の状態：本体にある。

*主張*　単体集合の鈍結合 $`X\diamond Y` は、$`X\times\Delta^1\times Y` の零端を $`X` へ、一端を $`Y` へ対応する射影で貼り付けた押し出しである。縮約射が比較写像 $`X\diamond Y\to X\star Y` を誘導する。

仮定：任意の単体集合 X,Y（Kerodon と一致）。結論：fatJoin X Y は円柱の両端をそれぞれ X,Y へ射影する押し出し。fatJoinComparison は通常の join への比較射（一致）。

:::

:::theorem "kerodon_4_6_2_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_fatJoinComparison, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison")
Kerodon Theorem 4.6.2.8（[Tag 01HV](https://kerodon.net/tag/01HV)）。対応表の状態：本体にある。

*主張*　任意の単体集合 $`X,Y` について、比較写像 $`X\diamond Y\to X\star Y` は圏同値である。

仮定：任意の単体集合 X,Y（Kerodon と一致）。結論：fatJoinComparison X Y が前合成同値（Lean が強い：各試験対象で π₀ 全単射を含む）。

:::

:::corollary "kerodon_4_6_2_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IsPrecompositionEquivalence.joinMap_left, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IsPrecompositionEquivalence.joinMap_right")
Kerodon Corollary 4.6.2.9（[Tag 01HW](https://kerodon.net/tag/01HW)）。対応表の状態：本体にある。

*主張*　単体集合の二つの圏同値の結合も圏同値である。

仮定：f,g がそれぞれ前合成同値（Kerodon と一致）。結論：joinMap f (id \_) と joinMap (id \_) g が前合成同値。二つの合成が f⋆g（一致）。

:::

:::lemma_ "kerodon_4_6_2_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_fatJoinComparison, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_fatJoinComparison_of_pushout_left")
Kerodon Lemma 4.6.2.10（[Tag 01HX](https://kerodon.net/tag/01HX)）。対応表の状態：本体にある。

*主張*　単体集合 $`Y` について $`\Delta^1\diamond Y\to\Delta^1\star Y` が圏同値なら、任意の単体集合 $`X` で $`X\diamond Y\to X\star Y` が圏同値である。

仮定：任意の単体集合 X,Y（Lean が弱い：Δ¹⋄Y での同値を事前には仮定しない）。結論：fatJoinComparison X Y が前合成同値（一致）。

:::

:::lemma_ "kerodon_4_6_2_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_fatJoinComparison, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_fatJoinComparison_stdSimplex")
Kerodon Lemma 4.6.2.11（[Tag 01HY](https://kerodon.net/tag/01HY)）。対応表の状態：本体にある。

*主張*　比較写像 $`\Delta^1\diamond\Delta^0\to\Delta^1\star\Delta^0` は圏同値である。

仮定：X=Δ¹、Y=Δ⁰（Lean が弱い：任意の標準単体の組を扱う）。結論：fatJoinComparison Δ¹ Δ⁰ が前合成同値（一致）。

:::

:::proposition "kerodon_4_6_2_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_fatJoinComparison")
Kerodon Proposition 4.6.2.12（[Tag 01HZ](https://kerodon.net/tag/01HZ)）。対応表の状態：本体にある。

*主張*　任意の単体集合 $`X` の比較写像 $`X\diamond\Delta^0\to X\star\Delta^0` は圏同値である。

仮定：X は任意、Y=Δ⁰（Lean が弱い：Y も任意）。結論：X⋄Δ⁰→X⋆Δ⁰ が前合成同値（一致）。

:::

:::corollary "kerodon_4_6_2_14" (uses := "kerodon_1_1_0_6, kerodon_4_3_6_4, kerodon_4_5_4_14, kerodon_4_5_5_9, kerodon_4_5_5_11, kerodon_4_6_2_8")
Kerodon Corollary 4.6.2.14（[Tag 01J0](https://kerodon.net/tag/01J0)）。対応表の状態：なし。

fatJoinComparisonは原文の相対pushoutからB◇Δ⁰へのθとは異なる射。通常joinとの比較の前合成同値性だけはθの同値性の直接の一部ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_fatJoinComparison`

:::

# 4.6.3 Digression: Categorical Mapping Cylinders

%%%
number := false
tag := "kerodon-4-6-3"
%%%

Kerodon [Tag 01K2](https://kerodon.net/tag/01K2)

:::proposition "kerodon_4_6_3_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.exists_equivalenceCylinder_extension_of_functorIso, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.nonempty_functorIso_of_equivalenceCylinder_extension") (uses := "kerodon_1_4_0_1, kerodon_4_6_3_9")
Kerodon Proposition 4.6.3.1（[Tag 01K3](https://kerodon.net/tag/01K3)）。対応表の状態：一部。

*主張*　無限圏への二つの図式 $`f_0,f_1:B\to C` が自然同型であることは、折り畳み写像 $`B\coprod B\to B` のある分解で、第二の射が圏同値かつ両図式が中間対象上に同時に延長することと同値である。第一の射で二つのコピーの像が交わらない任意の分解について、同時延長を要求することとも同値である。

可逆区間JによるB×Jの円柱に限ると、二つのEquivalenceCylinderFunctorIsoの型は同じ二端点を持つ延長とFunctorIsoを双方向に直接結ぶ。任意の分解B̄での三条件全部は含まない。

:::

:::definition "kerodon_4_6_3_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceCylinder, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceCylinderProjection, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceCylinderEndpoint_projection, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceCylinderEndpoint_fixed, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceCylinderEndpoint_mono, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_relativeEquivalenceCylinderEndpoint") (uses := "kerodon_1_1_0_6")
Kerodon Definition 4.6.3.3（[Tag 01K5](https://kerodon.net/tag/01K5)）。対応表の状態：一部。

*主張*　単射 $`A\to B` に相対的な圏論的写像円筒は、圏同値 $`\overline B\to B` と二つの切断からなる。切断は $`A` 上で一致し、$`B\coprod_A B\to\overline B` を単射にする。

relativeEquivalenceCylinderの二端点はA上で一致し、同じ射影への切断であることをendpoint\_fixed/projectionが直接返す。B∐\_A Bからの合わせた射のMono性と一般の円柱を束ねる型は含まない。

:::

:::corollary "kerodon_4_6_3_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.exists_relativeCylinder_extension") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_6_3_1, kerodon_4_6_3_3")
Kerodon Corollary 4.6.3.7（[Tag 01K9](https://kerodon.net/tag/01K9)）。対応表の状態：一部。

*主張*　無限圏への二つの $`B` 上の図式が自然同型であることは、任意に選んだ $`B` の圏論的写像円筒に、二つの端で元の図式に一致する図式があることと同値である。

exists\_relativeCylinder\_extension は元の二図式を結ぶ点ごとに可逆な実際の区間ホモトピーも入力すると、指定の単射円柱への同じ延長を直接返す。FunctorIsoだけからこの入力を作る方向と逆方向は含まない。

:::

:::theorem "kerodon_4_6_3_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.exists_relativeCylinder_extension, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.exists_equivalenceCylinder_extension_of_functorIso, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.nonempty_functorIso_of_equivalenceCylinder_extension") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_1_4_6, kerodon_4_4_3_15, kerodon_4_5_4_11")
Kerodon Theorem 4.6.3.8（[Tag 01KA](https://kerodon.net/tag/01KA)）。対応表の状態：一部。

*主張*　同型ファイブレーション $`q:X\to S` に対し、同じ $`g:B\to S` を持ち上げ、$`A\subseteq B` 上で一致する $`f_0,f_1:B\to X` を取る。$`A` に相対的かつ $`S` 上で自然同型であることは、折り畳み写像 $`B\coprod_A B\to B` を圏同値で終わるように分解して、指定の $`S` への写像の持ち上げとして中間対象へ同時延長できることと同値である。第一の射が単射であるすべての分解でこの延長ができることとも同値である。

S=Δ⁰、A=∅、B̄=B×Jの可逆区間円柱に限ると、二つのEquivalenceCylinderFunctorIsoの型が同じ延長とFunctorIsoを双方向に結ぶ。一般のisofibration上の相対版は含まない。

:::

:::corollary "kerodon_4_6_3_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceCylinder, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.exists_relativeCylinder_extension") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_6_3_8")
Kerodon Corollary 4.6.3.9（[Tag 01KB](https://kerodon.net/tag/01KB)）。対応表の状態：一部。

*主張*　無限圏 $`C` への二つの $`B` 上の図式が $`A\subseteq B` 上で一致するとき、$`A` に相対的に自然同型かどうかは、折り畳み写像 $`B\coprod_A B\to B` を圏同値で終わるように分解して両図式を中間対象へ同時延長できるかで判定できる。第一の射が単射である任意の分解に同時延長できることとも同値である。

exists\_relativeCylinder\_extension はA上で固定され点ごとに可逆な区間ホモトピーを追加入力すると、原文(3)の任意の単射円柱への同じ延長を直接返す。相対関手空間での同型だけからの入力の比較と逆方向は含まない。

:::

:::corollary "kerodon_4_6_3_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.exists_relativeCylinder_extension")
Kerodon Corollary 4.6.3.10（[Tag 01KC](https://kerodon.net/tag/01KC)）。対応表の状態：一部。

*主張*　同型ファイブレーション $`q:X\to S` のもとで $`B\to S` の二つの持ち上げが $`A\subseteq B` 上で一致するとする。$`A` に相対的かつ $`S` 上で自然同型であることは、選んだ相対圏論的写像円筒の上に両端を保って $`S` 上で延長できることと同値であり、判定は円筒の選択によらない。

底Sを終対象にし、A上固定で点ごとに可逆な区間ホモトピーも与える場合、exists\_relativeCylinder\_extension は指定円柱への同じ延長を返す。一般の相対底の持ち上げとiffは含まない。

:::

:::corollary "kerodon_4_6_3_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.exists_relativeCylinder_extension")
Kerodon Corollary 4.6.3.11（[Tag 01KD](https://kerodon.net/tag/01KD)）。対応表の状態：一部。

*主張*　無限圏への二つの図式 $`B\to C` が部分集合 $`A\subseteq B` 上で一致するとき、$`A` に相対的に自然同型であることと、相対圏論的写像円筒へ両端を保って延長できることは同値である。この条件は円筒の選択によらない。

exists\_relativeCylinder\_extension はA上で固定され点ごとに可逆な区間ホモトピーを追加入力すると、指定円柱への同じ延長を直接返す。相対関手空間での同型との比較・逆向きは含まない。

:::

# 4.6.4 Oriented Fiber Products

%%%
number := false
tag := "kerodon-4-6-4"
%%%

Kerodon [Tag 01KE](https://kerodon.net/tag/01KE)

*06-catinfty-ind-presentable.html — 1. Cat∞ の写像空間と極限 — 引き戻しと lax pullback*

- 内容　／　Lean　／　場所
- Cat\<sub\>∞\</sub\> の引き戻し：cospan $`A\to C\leftarrow B` を path で置き換えて作った錐は極限　／　\`catPullbackCone\_isLimit\`　／　F2/CatPullbackCone
- lax pullback $`A\times_C\mathrm{Fun}(\Delta^1,C)\times_C B`　／　\`laxPullback p q\`　／　F2/LaxPullback
- lax pullback は Cat\<sub\>∞\</sub\> のある極限の頂点　／　\`laxPullbackCone\_isLimit\`　／　F2/LaxPullbackLimit
- 安定 ∞ 圏の間の完全関手の lax pullback は安定で、両射影は完全　／　\`laxPullback\_isStable\`、\`laxPullbackFst\_isExactFunctor\`　／　F2/LaxPullbackStable

lax pullback は Tamme の切除定理（K 理論の Land–Tamme 経路）の中心にある構成で、これが安定 ∞ 圏として完成していることが、K 側の第一の入力になっている。

:::definition "kerodon_4_6_4_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst")
Kerodon Definition 4.6.4.1（[Tag 01KF](https://kerodon.net/tag/01KF)）。対応表の状態：本体にある。

*主張*　単体集合の射 $`C\to E\leftarrow D` の向き付きファイバー積は、$`\operatorname{Fun}(\Delta^1,E)\to E\times E` の始点・終点評価に $`C\times D\to E\times E` を沿わせた引き戻しである。

仮定：同じ標的 C を持つ単体集合の射 p:A→C と q:B→C（Kerodon と一致）。結論：laxPullback p q は Fun(Δ¹,C) の両端評価に沿い A×B から引き戻した単体集合（一致）。

:::

:::proposition "kerodon_4_6_4_2" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_4_5_3")
Kerodon Proposition 4.6.4.2（[Tag 01KG](https://kerodon.net/tag/01KG)）。対応表の状態：なし。

arrowEndpointPairのisofibration性は引き戻す前の射の性質。原文のlax pullbackの特定の射影θとの基底変換の同定が必要。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair_kanEquivalenceLifting`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair_innerFibration`

:::

:::corollary "kerodon_4_6_4_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback_quasicategory")
Kerodon Corollary 4.6.4.3（[Tag 01KH](https://kerodon.net/tag/01KH)）。対応表の状態：本体にある。

*主張*　無限圏の間の関手 $`C\to E\leftarrow D` の向き付きファイバー積は無限圏である。

仮定：Quasicategory A,B,C と p:A→C、q:B→C（Kerodon と一致）。結論：laxPullback p q が Quasicategory（一致）。

:::

:::proposition "kerodon_4_6_4_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedConeProjection_leftFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedConeProjection") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_5_6_2, kerodon_4_6_2_3, kerodon_4_6_2_14")
Kerodon Proposition 4.6.4.13（[Tag 01KQ](https://kerodon.net/tag/01KQ)）。対応表の状態：一部。

*主張*　無限圏 $`C` の対象 $`x` に対し、$`\{x\}\vec\times_C C\to C` は左ファイブレーション、$`C\vec\times_C\{x\}\to C` は右ファイブレーションである。

pointedConeProjectionをK=Δ⁰に取りjoinStdSimplexIso 0 0でΔ¹に移すと、原文の始点Xを固定した向き付き積の同じ射影のleft fibration性を直接得る。終点固定のright側は含まない。

:::

:::corollary "kerodon_4_6_4_14" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_6_4_13")
Kerodon Corollary 4.6.4.14（[Tag 01KR](https://kerodon.net/tag/01KR)）。対応表の状態：なし。

通常joinによるslice/coslice射影は原文の向き付き積の射影と別模型。sliceLaxMapの圏同値性だけではその射のleft/right fibration性は移らず、厳密な比較が必要。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverProjection_rightFibration`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderProjection_leftFibration`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_sliceLaxMap`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_cosliceLaxMap`

:::

:::definition "kerodon_4_6_4_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceLaxMap, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceLaxMap")
Kerodon Construction 4.6.4.15（[Tag 02GH](https://kerodon.net/tag/02GH)）。対応表の状態：本体にある。

*主張*　単体図式 $`F:K\to C` に対し、結合の比較写像 $`C_{/F}\diamond K\to C_{/F}\star K` と縮約射を合成し、スライスの対角射 $`C_{/F}\to C\vec\times_{\operatorname{Fun}(K,C)}\{F\}` を得る。二つの因子を双対に配置して余スライスの対角射も作る。

仮定：任意の単体集合の射 F:K→X（Kerodon と一致）。結論：太い join から通常の join への前合成で slice→laxSlice と coslice→laxCoslice を構成。標的は端点の固定された向き付き引き戻しの模型（一致）。

:::

:::theorem "kerodon_4_6_4_19" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_sliceLaxMap, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_cosliceLaxMap, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxSlice")
Kerodon Theorem 4.6.4.19（[Tag 01KU](https://kerodon.net/tag/01KU)）。対応表の状態：本体にある。

*主張*　無限圏 $`C` の図式 $`F:K\to C` に対し、スライスと余スライスから $`\operatorname{Fun}(K,C)` 上の対応する向き付きファイバー積への対角射はいずれも無限圏の同値である。

仮定：Quasicategory X と任意の図式 F:K→X（Kerodon と一致）。結論：sliceLaxMap F と cosliceLaxMap F が IsQCatEquivalence（一致）。

:::

:::corollary "kerodon_4_6_4_20" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_sliceLaxMap, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_cosliceLaxMap")
Kerodon Corollary 4.6.4.20（[Tag 02VT](https://kerodon.net/tag/02VT)）。対応表の状態：本体にある。

*主張*　無限圏 $`C` の対象 $`x` について、対角射 $`C_{/x}\to C\vec\times_C\{x\}` と $`C_{x/}\to\{x\}\vec\times_C C` は同値である。

仮定：∞ 圏 X の頂点（Lean が弱い：任意の K と F:K→X を扱う）。結論：K=Δ⁰ の slice・coslice から点を固定する向き付き引き戻しへの対角射が圏同値（一致）。

:::

:::corollary "kerodon_4_6_4_21" (uses := "kerodon_1_4_0_1, kerodon_4_6_4_19")
Kerodon Corollary 4.6.4.21（[Tag 02GL](https://kerodon.net/tag/02GL)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：片側を点とする場合・同値および厳密基底変換・左右と Kan ファイバーを照合。同値 G で基底図式を押し出した slice と coslice の双方の同値。図式制限や両者の op 比較は G による変換を扱わない。

:::

:::corollary "kerodon_4_6_4_22" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_4_3_21, kerodon_4_5_3_20, kerodon_4_5_3_24, kerodon_4_5_3_27, kerodon_4_5_3_28, kerodon_4_6_4_21")
Kerodon Corollary 4.6.4.22（[Tag 069H](https://kerodon.net/tag/069H)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：片側を点とする場合・同値および厳密基底変換・左右と Kan ファイバーを照合。categorical pullback を図式に沿う slice に移す比較四角。点上の pullback や pinched Hom の四角では slice 全体に及ばない。

:::

:::corollary "kerodon_4_6_4_23"
Kerodon Corollary 4.6.4.23（[Tag 06QQ](https://kerodon.net/tag/06QQ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：片側を点とする場合・同値および厳密基底変換・左右と Kan ファイバーを照合。右ファイブレーションのファイバーと K の連結度から slice 射の連結度を見積もる型。右ファイブレーションの基底変換には n と k の次数がない。

:::

:::corollary "kerodon_4_6_4_24" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceOverPostcomp_trivialKanFibration_of_rightFibration")
Kerodon Corollary 4.6.4.24（[Tag 05YA](https://kerodon.net/tag/05YA)）。対応表の状態：一部。

*主張*　無限圏の右ファイブレーション $`U:E\to C` の各ファイバーが $`n`-切断で、$`K` が $`(n+1)`-connective なら、任意の図式 $`F:K\to E` に対して $`E_{/F}\to C_{/UF}` は自明な Kan ファイブレーションである。

sliceOverPostcomp\_trivialKanFibration\_of\_rightFibration はK=Δ⁰の同じ射U\_/Fの自明Kan性を直接返す。この図式は全次数で連結で、任意の指定のfiber切断次数に依存しない。一般Kは含まない。

:::

:::lemma_ "kerodon_4_6_4_25" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.nonempty_functorIso_iff_sliceOverFixedDiagramVertexIso, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.nonempty_functorIso_iff_sliceUnderFixedDiagramVertexIso")
Kerodon Lemma 4.6.4.25（[Tag 01KV](https://kerodon.net/tag/01KV)）。対応表の状態：本体にある。

*主張*　無限圏 $`C` の図式 $`F:K\to C` を固定する。二つの $`J\to C_{/F}` が自然同型であることと、対応する二つの $`J\star K\to C` が $`K` 上で $`F` を固定した関手圏の中で自然同型であることは同値である。

仮定：Quasicategory X、固定図式 F:K→X、slice 内の二つの J 図式（Kerodon と一致）。結論：二図式の FunctorIso の存在と、対応する J⋆K 上の図式の相対関手空間での頂点同型の存在が同値（一致）。

:::

# 4.6.5 Pinched Morphism Spaces

%%%
number := false
tag := "kerodon-4-6-5"
%%%

Kerodon [Tag 01KW](https://kerodon.net/tag/01KW)

*定義 13.2 （写像空間への作用）*

単体的集合の射 $`f\colon C\to D` と頂点 $`x,y` について、$`\mathrm{Hom}^R_C(x,y)` の $`n` 単体 $`\sigma\colon\Delta^n\star\Delta^0\to C` を $`f\circ\sigma` に送ることで、射

$$`f_*\colon\mathrm{Hom}^R_C(x,y)\to\mathrm{Hom}^R_D(f(x),f(y))`

を定める（$`\mathrm{Hom}^R` は定義 7.1）。

*02-mapping-limits.html — 1. 写像空間 — 基本的な性質*

- 内容　／　Lean　／　場所
- 頂点 = $`x` から $`y` への辺　／　\`PinchedHom.vertexEquiv\`　／　PinchedHom/Edges
- Kan 複体である（HTT Prop. 1.2.2.3）　／　\`pinchedHom\_kanComplex\`（instance）　／　Core/MappingSpaceRightKan
- $`\pi_0\,\mathrm{Hom}^R(x,y)\cong\mathrm{Hom}_{hX}(x,y)`　／　\`pinchedHomPiZeroEquiv\`　／　Core/MappingSpacePiZero
- slice の fiber と同型：$`\mathrm{Hom}^R(x,y)\cong X_{/y}\times_X\{x\}`　／　\`pinchedHomSliceFiberIso\`　／　Core/PinchedSlice
- 普遍性：$`A\to\mathrm{Hom}^R(x,y)` ⇔ $`A` を $`x` に潰した $`A\star\Delta^0\to X`　／　\`pinchedHomCurry\`／\`pinchedHomUncurry\`　／　Core/PinchedUniversal
- 関手性　／　\`pinchedHomMap f x y\`　／　Core/MappingSpaceMap
- $`p` が inner fibration ⇒ 写像空間の写像は右 fibration　／　\`pinchedHomMap\_rightFibration\`　／　Core/MappingSpaceFibration
- $`p` が trivial ⇒ 写像空間の写像も trivial　／　\`pinchedHomMap\_trivialKanFibration\`　／　Core/MappingSpaceTrivialFibration

*Kan 性の証明の方針*：$`\mathrm{Hom}^R(x,y)` の右ホーン $`\Lambda^{n+1}_i`（$`0<i`）は、最後の頂点 $`y` を加えると $`X` の内ホーン $`\Lambda^{n+2}_i` になる。したがって quasicategory 性で充填できる。右ホーンが充填できれば、ホモトピー圏が亜群になることを経由して Kan 複体であることが従う（\`kanComplex\_of\_rightHornFillers\`。第 1 章の Joyal の定理を使う）。

*f-a-basics.html — 1. 始対象と写像空間 — 写像空間の定義と比較*

- 定義　／　$`n` 単体　／　スライスとの関係
- $`\mathrm{Hom}^R(x,y)`（HTT 1.2.2、Lean の pinchedHom）　／　$`\Delta^{n+1}\to\mathcal C`、前の面 $`\Delta^{\{0..n\}}` が $`x` で定値、最後の頂点が $`y`　／　$`\mathcal C_{/y}\to\mathcal C` の $`x` 上のファイバー
- $`\mathrm{Hom}^L(x,y)`　／　最初の頂点が $`x`、後ろの面が $`y` で定値　／　$`\mathcal C_{x/}\to\mathcal C` の $`y` 上のファイバー
- $`\mathrm{Hom}(x,y)=\{x\}\times_{\mathcal C}\mathrm{Fun}(\Delta^1,\mathcal C)\times_{\mathcal C}\{y\}`　／　$`\Delta^n\times\Delta^1\to\mathcal C` で両端が定値　／　fat slice のファイバー
- $`\mathrm{Map}_{\mathfrak C[\mathcal C]}(x,y)`　／　単体的圏の Hom（ネックレスで記述）　／　一般に Kan でない。置き換えが要る

- $`\mathrm{Hom}^L,\mathrm{Hom}^R` は左・右 fibration の点上のファイバーなので Kan 複体。$`\mathrm{Hom}` はすべての射が同値な quasicategory なので Kan 複体（Joyal）。

- $`\Delta^n\times\Delta^1\to\Delta^{n+1}`、$`(i,0)\mapsto i`、$`(i,1)\mapsto n+1` との合成で $`\mathrm{Hom}^R\hookrightarrow\mathrm{Hom}`。これらはホモトピー同値（HTT 4.2.1.8）。$`|\mathrm{Hom}^R|\simeq|\mathrm{Map}_{\mathfrak C[\mathcal C]}|`（HTT §2.2.4）。どの模型でも $`\pi_0=\mathrm{Hom}_{h\mathcal C}`。

:::definition "kerodon_4_6_5_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft")
Kerodon Construction 4.6.5.1（[Tag 01KX](https://kerodon.net/tag/01KX)）。対応表の状態：本体にある。

*主張*　単体集合 $`C` の頂点 $`x,y` に対し、左の pinched 射空間を $`C_{x/}\times_C\{y\}`、右のものを $`\{x\}\times_C C_{/y}` と定める。

仮定：単体集合 X と頂点 x,y（Kerodon と一致）。結論：右 pinched は X\_\{/y\} の x 上、左 pinched は X\_\{x/\} の y 上のファイバーに当たる模型（一致）。

*定義 7.1 （写像空間 $`\mathrm{Hom}^L`、$`\mathrm{Hom}^R`）*

単体的集合 $`C` の頂点 $`x,y` について、コスライスの射影 $`C_{x/}\to C` の $`y` 上のファイバーを $`\mathrm{Hom}^L_C(x,y)`、スライスの射影 $`C_{/y}\to C` の $`x` 上のファイバーを $`\mathrm{Hom}^R_C(x,y)` とおく（スライス・コスライスとその射影は定義 4.5・定義 4.7、ファイバーは定義 6.2）。

:::

:::proposition "kerodon_4_6_5_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHom_kanComplex, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft_kanComplex")
Kerodon Proposition 4.6.5.5（[Tag 01L0](https://kerodon.net/tag/01L0)）。対応表の状態：本体にある。

*主張*　無限圏の任意の二対象について、左・右の pinched 射空間はともに Kan 複体である。

仮定：Quasicategory X と頂点 x,y（Kerodon と一致）。結論：pinchedHom x y と pinchedHomLeft x y はともに KanComplex（一致）。

*定理 7.2 （写像空間は Kan 複体）*

$`C` が quasicategory なら、頂点 $`x,y` について $`\mathrm{Hom}^L_C(x,y)` と $`\mathrm{Hom}^R_C(x,y)`（定義 7.1）は Kan 複体である。

:::

:::definition "kerodon_4_6_5_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeftToIntervalMappingSpace")
Kerodon Construction 4.6.5.7（[Tag 01L2](https://kerodon.net/tag/01L2)）。対応表の状態：本体にある。

*主張*　単体集合 $`C` の頂点 $`x,y` に対し、余スライスとスライスの対角射をそれぞれ $`y,x` 上のファイバーに制限して、左・右の pinched 射空間から $`\operatorname{Hom}_C(x,y)` への包含を得る。

仮定：単体集合 X と頂点 x,y（Kerodon と一致）。結論：左右の pinched 空間から区間模型 intervalMappingSpace x y への pinch inclusion を構成（一致）。

:::

:::proposition "kerodon_4_6_5_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeftToIntervalMappingSpace_isQCatEquivalence")
Kerodon Proposition 4.6.5.10（[Tag 01L5](https://kerodon.net/tag/01L5)）。対応表の状態：本体にある。

*主張*　無限圏の任意の二対象間で、左と右の pinched 射空間から通常の射空間への包含は、いずれも Kan 複体のホモトピー同値である。

仮定：Quasicategory X と頂点 x,y（Kerodon と一致）。結論：左右の pinch inclusion が IsQCatEquivalence。両端が Kan 複体なのでホモトピー同値（一致）。

*02-mapping-limits.html — 1. 写像空間 — 左の写像空間と両者の比較*

左 pinched 写像空間 $`\mathrm{Hom}^L(x,y)` は、反対圏の右写像空間の反対として定義している。

\`\`\`text
def pinchedHomLeft \{X : SSet.\{u\}\} (x y : X \_⦋0⦌) : SSet.\{u\} :=
  (pinchedHom (X := X.op) (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x)).op
\`\`\`

Kan 性と $`\pi_0` の計算は、反対圏を通して右の場合から導かれる（Core/MappingSpaceLeft）。右の場合から双対で導く形になっている。左右の写像空間が同値であること（\`pinchedHomLeftRightEquivalence\`）は、区間模型を経由して F1/MappingSpaceModelEquivalence で示されている。Core ではなく F1 にある点に注意する。

:::

# 4.6.6 Digression: Diagrams in Slice ∞-Categories

%%%
number := false
tag := "kerodon-4-6-6"
%%%

Kerodon [Tag 04HY](https://kerodon.net/tag/04HY)

:::definition "kerodon_4_6_6_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder")
Kerodon Notation 4.6.6.1（[Tag 04HZ](https://kerodon.net/tag/04HZ)）。対応表の状態：一部。

*主張*　単体写像 $`f_\pm:K_-\star K_+\to C` の制限を $`f_-,f_+` とすると、結合による表示で $`K_-\to C_{/f_+}` が得られる。この射の下で取った $`C_{/f_+}` の余スライスを $`C_{f_-/\,/f_+}` と書く。

片方の図式が空の場合、sliceOverまたはsliceUnderが原文の両側sliceの一側だけを固定した構成を直接与える。二つの非空図式を同時に固定するtilde fと反復構成全体は含まない。

:::

:::definition "kerodon_4_6_6_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceConeFamilyMap")
Kerodon Construction 4.6.6.4（[Tag 04J1](https://kerodon.net/tag/04J1)）。対応表の状態：一部。

*主張*　$`f_\pm:K_-\star K_+\to C` を固定し、$`\operatorname{Fun}(K,C_{f_-/\,/f_+})` の評価と両側の錐の評価を結合する。これにより $`K_-\star K\star K_+\to C` で両端の結合への制限が $`f_\pm` となる図式の単体集合への比較写像を得る。

sliceConeFamilyMapはK₋=∅、K=Δ⁰のとき、原文の同じsliceからcone familyへの評価比較を直接構成する。両側の一般図式と一般Kは含まない。

:::

:::theorem "kerodon_4_6_6_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_sliceConeFamilyMap, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_cosliceCoconeFamilyMap, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_fatJoinComparison_fixedDiagram")
Kerodon Theorem 4.6.6.5（[Tag 04J2](https://kerodon.net/tag/04J2)）。対応表の状態：一部。

*主張*　無限圏 $`C` の図式 $`f_\pm:K_-\star K_+\to C` と任意の単体集合 $`K` に対し、$`\operatorname{Fun}(K,C_{f_-/\,/f_+})` から、$`f_\pm` を延長する $`K_-\star K\star K_+\to C` の無限圏への比較写像は同値である。

sliceConeFamilyMapとcosliceCoconeFamilyMapの圏同値性は、それぞれ片側の図式が空、K=Δ⁰の場合の同じ比較射の結論。一般の両側slice・任意Kは含まない。

:::

:::lemma_ "kerodon_4_6_6_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_sliceConeFamilyMap")
Kerodon Lemma 4.6.6.7（[Tag 04J4](https://kerodon.net/tag/04J4)）。対応表の状態：一部。

*主張*　無限圏 $`C` の図式 $`f_+:K_+\to C` と任意の単体集合 $`K` に対し、$`\operatorname{Fun}(K,C_{/f_+})` から、$`K_+` 上で $`f_+` を固定した $`K\star K_+\to C` の図式の無限圏への比較写像は同値である。

isQCatEquivalence\_sliceConeFamilyMap はK=Δ⁰で同じslice→cone familyの比較が圏同値となる結論を直接返す。任意Kの関手空間版は含まない。

:::

:::proposition "kerodon_4_6_6_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_sliceConeFamilyMap, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamily, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_cosliceCoconeFamilyMap")
Kerodon Example 4.6.6.8（[Tag 04J5](https://kerodon.net/tag/04J5)）。対応表の状態：本体にある。

*主張*　無限圏 $`C` の図式 $`f_+:K_+\to C` に対し、$`C_{/f_+}` から、$`K_+` 上で $`f_+` に一致する左錐 $`K_+^{\triangleleft}\to C` の無限圏への比較写像は同値である。

仮定：Quasicategory X と任意の図式 F:K→X（Kerodon と一致）。結論：sliceConeFamilyMap F が圏同値。coneFamily F は左錐図式を K 上で F に固定した関手空間（一致）。

:::

:::corollary "kerodon_4_6_6_9"
Kerodon Corollary 4.6.6.9（[Tag 04J6](https://kerodon.net/tag/04J6)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：片側が空・点・両側の拡張・関手圏の点の版を照合。mixed slice に対する A⊂B の延長比較の持ち上げ性。片側の restriction の型には二端の固定がない。

:::

:::definition "kerodon_4_6_6_10"
Kerodon Variant 4.6.6.10（[Tag 02GN](https://kerodon.net/tag/02GN)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：片側が空・点・両側の拡張・関手圏の点の版を照合。join で作る slice/coslice から Fun(K,C) の点上の slice/coslice への両比較。join と over の定義があってもこの比較射を扱う型がない。

:::

# 4.6.7 Morphism Spaces in the Homotopy Coherent Nerve

%%%
number := false
tag := "kerodon-4-6-7"
%%%

Kerodon [Tag 01LA](https://kerodon.net/tag/01LA)

*f-c-spaces.html — 9. 形式化での証明*

主定理は \`F1/Coherent/HomEquivalence.lean\` の \`coherentHomComparison\_isQCatEquivalence\` と系 \`…\_isSimplicialHomotopyEquivalence\`：局所 Kan な単体的圏の豊穣 Hom から coherent nerve の右 pinched 写像空間への比較写像は同値。カテゴリー同値は \`Core/PrecompositionEquivalence.lean\` の \`IsPrecompositionEquivalence f\`（すべての quasicategory $`Z` で前合成 $`\mathrm{Fun}(B,Z)\to\mathrm{Fun}(A,Z)` が同値）で、Kerodon の定義と同じ形。モデル構造は使わない。

- Kerodon　／　リポジトリ（F1/Coherent/）　／　内容
- $`\Phi(\Delta^n)`（4.6.7.27）　／　ResolutionFlags（\`CoherentResolutionFlag\`）、ResolutionSimplex　／　旗：始点から始まり始点が各集合の最小元の増大列。Kerodon の順序を反転した右 pinched 版
- $`\Phi\dashv\mathrm{Sing}^Q`（4.6.7.19〜21）　／　ResolutionExtension（\`coherentResolution\`、\`coherentResolutionRightAdjoint\`）　／　米田に沿った左 Kan 拡張と制限米田関手の随伴
- $`\rho_K`（4.6.7.22）　／　\`coherentResolutionProjectionAll\`　／　旗の最大元の射影の全 $`K` への拡張
- $`\mathrm{Hom}\cong\mathrm{Sing}^Q\mathcal C(X,Y)`（4.6.7.16）　／　FlagIso（\`coherentPinchedFlagIso\`）　／　局所 Kan 性を仮定しない同型
- $`\theta`　／　\`coherentResolutionComparison\`　／　$`Z\to\mathrm{Sing}^QZ`
- 4.6.7.23（標準単体）　／　ResolutionInterval、ResolutionHomotopy、ResolutionEquivalence　／　下の (i)
- 4.6.7.23（一般）　／　ResolutionMonomorphisms、Core/CellularNaturalComparison　／　下の (ii)
- 4.6.7.23 ⇒ 4.6.7.5　／　ResolutionRetraction、ResolutionCylinder、HomEquivalence　／　下の (iii)

- *(i) 標準単体*：blunt join を使わず直接縮約する。区間の切断 \`coherentResolutionSection n\`（7.2 の $`s_n`）、切断則、恒等から「射影の後に切断」への変形 \`coherentResolutionHomotopy n\`（旗を区間の旗へ広げる）、その各頂点での可逆性から、2-out-of-6 型の \`isPrecompositionEquivalence\_of\_composites\` で射影は同値。$`s_n` は固定した $`n` でしか使わないので自然性は要らない。

- \*\*(ii) 一般の $`K`\*\*：汎用補題 \`isPrecompositionEquivalence\_natComponent\_of\_stdSimplex\`：単射・押し出し・$`\mathbb N` 型余極限・wide pushout を保つ関手の間の自然変換が $`\varnothing` とすべての $`\Delta^n` で前合成の同値なら、すべての $`X` で同値（境界の次数の帰納、セルの族の余積、骨格の押し出し、可算余極限）。Kerodon 4.6.2.10 と共用で、局所化の証明（LocalizationAllBases）と同じ型。

- \*\*(iii) $`\rho` から $`\theta`\*\*：Kerodon の写像柱の代わりに、厳密な左逆 \`coherentResolutionComparison\_exists\_retraction\`（射影の押し出しに余単位を貼り、前合成の同値で延長して単射上で厳密化）と、ホモトピーの随伴転置による後合成の本質的全射性 \`coherentResolutionComparison\_postcomp\_essentiallySurjective\` から、両合成の可逆 2-cell を作る（\`coherentResolutionComparison\_isQCatEquivalence\`）。

- 論点　／　Kerodon　／　形式化
- 写像空間の向き　／　左 pinched　／　右 pinched（旗の順序を反転）
- 標準単体　／　blunt join で帰納　／　区間の切断と変形による直接の縮約
- 一般の $`K`　／　骨格の帰納法　／　汎用のセル帰納法（他と共用）
- $`\rho\Rightarrow\theta`　／　$`\mathrm{Fun}(K,-)^{\simeq}` で試す（写像柱）　／　厳密な左逆と転置による右逆
- 適用範囲　／　$`\mathcal C(X,Y)` が ∞ 圏　／　$`\mathcal C(X,Y)` が Kan 複体

*route-classification.html — 5. 段 3：$`\mathcal S=N^{hc}(\mathrm{Kan})` と写像空間の比較定理 — 5.4（3.4）$`\mathcal S` の写像空間と合成*

3.3 を $`\mathrm{Kan}` に適用して $`\mathrm{Map}_{\mathcal S}(K,L)\simeq\mathrm{Fun}(K,L)`。

- 写像空間　／　値　／　意味
- $`\mathrm{Map}_{\mathcal S}(\Delta^0,K)`　／　$`K`　／　一点からの写像の空間（段 4 の鍵）
- $`\mathrm{Map}_{\mathcal S}(K,\Delta^0)`　／　一点　／　終対象
- $`\mathrm{Map}_{\mathcal S}(\emptyset,K)`　／　一点　／　始対象
- $`\mathrm{Map}_{\mathcal S}(K,K)` の同値の部分　／　$`\mathrm{hAut}(K)`　／　$`\mathcal S^{\simeq}\simeq\coprod_{[K]}B\,\mathrm{hAut}(K)` の正当化

*合成は写像の合成と一致*：合成は自明 Kan fibration $`\{\Delta^2\to\mathcal S\}_{K,L,M}\to\mathrm{Map}(K,L)\times\mathrm{Map}(L,M)` の切断で作るが、$`\mathcal S` では $`f_{02}:=gf` と定値ホモトピーの 2 単体で族として切断が取れる。選び方は可縮なので、∞ 圏の合成は $`\theta` を通して写像の合成と一致。前合成も $`f^*` に対応。

\*\*$`\mathrm{Map}_{\mathcal S}(\Delta^0,-)` は恒等関手\*\*：fibration で言えば $`\mathcal S_*:=\mathcal S_{\Delta^0/}\to\mathcal S` は左 fibration で、$`K` 上の fiber は $`\mathrm{Hom}^L_{\mathcal S}(\Delta^0,K)\simeq K`。これが普遍左 fibration（段 4）。同じ定理から $`\mathrm{LFib}(B)` の写像空間は $`\mathrm{Fun}_B(E,E')`、$`\mathrm{Cat}_\infty` の写像空間は $`\mathrm{Fun}(\mathcal C,\mathcal D)^{\simeq}`。

*Lean での扱い*：\`coherentHomEquivalence\`（F1/Coherent/HomEquivalence）を \`KanObject\` に適用。一点からの射の合成と点での評価 \`coherentKanPointComposition\_pre\`、\`coherentKanPointComposition\_evaluate\`（F1/Coherent/KanPointComposition）、右 Hom の合成と輸送 \`coherentKanRightCompositionSquare\`、\`coherentKanRightCompositionTransportIso\`（F1/Coherent/KanRightCompositionTransport）、表現可能関手の coslice 比較 \`fiberIso\`、\`fiberIso\_square\`（F1/Coherent/KanCosliceComparison）。

:::definition "kerodon_4_6_7_1" (uses := "kerodon_1_1_0_6")
Kerodon Notation 4.6.7.1（[Tag 01LB](https://kerodon.net/tag/01LB)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：一つの豊穣 Hom・二対象・局所 Kan の特例・次数を固定した解像を照合。二対象 x,y の simplicial category E\[K\] の一方向 Hom が K で逆向きは空。enriched pair object は積でこの自由構成ではない。

:::

:::definition "kerodon_4_6_7_3" (uses := "kerodon_1_1_0_6, kerodon_2_4_3_1, kerodon_2_4_4_15, kerodon_4_6_5_1")
Kerodon Construction 4.6.7.3（[Tag 01LD](https://kerodon.net/tag/01LD)）。対応表の状態：なし。

coherentHomComparison は右pinched写像空間への比較で、原文は左pinchedへの特定のθ。Pathの包含順の規約も異なり、指定射の比較がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison`

:::

:::theorem "kerodon_4_6_7_5" (uses := "kerodon_1_2_5_1, kerodon_4_6_7_3")
Kerodon Theorem 4.6.7.5（[Tag 01LE](https://kerodon.net/tag/01LE)）。対応表の状態：なし。

右pinchedのcoherentHomComparisonのホモトピー同値性であり、原文の左pinchedの指定θの同値性ではない。対象だけでなく比較射を同定する宣言が必要。

*f-c-spaces.html — 7. 写像空間の比較定理 — 7.1 主張と $`\mathrm{Hom}^L` の具体形*

$`\mathcal C` が局所 Kan なら $`\mathcal C(x,y)\simeq\mathrm{Hom}^L_{N^{hc}\mathcal C}(x,y)`。$`\mathrm{Hom}^L` の $`n` 単体は頂点 0 が $`x`、面 $`\{1,\dots,n+1\}` が $`y` で退化した $`(n+1)` 単体、つまり $`\mathfrak C[\Delta^{n+1}]\to\mathcal C` で頂点 $`1,\dots,n+1` を $`y` に、$`\mathrm{Hom}(j,k)`（$`j\ge1`）を $`\mathrm{id}_y` に送るもの。$`\mathrm{Hom}(j,k)` をつぶす合成の関係で立方体を割って

$$`J^n:=(\Delta^1)^n\big/(S\sim S\cup T),\qquad\mathrm{Hom}^L(x,y)_n=\mathrm{Hom}_{\mathrm{sSet}}(J^n,\mathcal C(x,y)).`

$`S` の類は $`m(S)=\min(S\setminus\{0\})` で決まり、$`J^n` の頂点は $`n+1` 個。$`S\subseteq S'` なら $`m(S)\ge m(S')` なので $`S\mapsto n+1-m(S)` は $`J^n` を経由し、余単体的な写像 $`r\colon J^\bullet\to\Delta^\bullet` を与える。

\*\*$`n=2`\*\*：正方形の頂点 $`\varnothing,\{1\},\{2\},\{1,2\}` の $`m` は $`3,1,2,1`。$`\mathrm{Hom}(1,3)=\Delta^1` との合成で辺 $`\{1\}\to\{1,2\}` が一点につぶれ、三角形 $`\varnothing\subseteq\{2\}\subseteq\{1,2\}` は $`\Delta^2` のまま、三角形 $`\varnothing\subseteq\{1\}\subseteq\{1,2\}` は一辺が退化した 2 単体になる。$`J^2=\Delta^2\cup_{\Delta^1}(\text{一辺が退化した 2 単体})\ne\Delta^2`。$`J^n` と $`\Delta^n` はどちらも弱可縮だが同型ではない。

*f-c-spaces.html — 7. 写像空間の比較定理 — 7.2 比較写像と素朴な方針の難点*

$`\theta=r^*\colon\mathcal C(x,y)=\mathrm{Hom}(\Delta^\bullet,\mathcal C(x,y))\to\mathrm{Hom}(J^\bullet,\mathcal C(x,y))=\mathrm{Hom}^L(x,y)` は選択を使わない明示的な単体的写像。定理は「Kan 複体 $`Z` について $`r^*\colon\mathrm{Hom}(\Delta^\bullet,Z)\to\mathrm{Hom}(J^\bullet,Z)` はホモトピー同値」に帰着する。各 $`r_n` は弱ホモトピー同値で切断 $`s_n\colon k\mapsto\{0\}\cup[n+1-k,n+1]` をもつが、$`s_n` は $`n` について自然でないので逆写像を単体ごとに作れない。$`r` は単射でないので $`\theta` は trivial fibration でもなく、持ち上げで直接は示せない。Reedy 型の議論や二重単体の対角補題でも書けるが、Kerodon と形式化は別の道をとる。

*f-c-spaces.html — 8. Kerodon 4.6.7 の証明（モデル圏なし）*

- 構成　／　内容
- pinched 写像空間（4.6.5.1）　／　$`\mathrm{Hom}^L_{\mathcal C}(X,Y)=\mathcal C_{X/}\times_{\mathcal C}\{Y\}`。fat 版 $`\mathrm{Hom}` への包含はホモトピー同値（4.6.5.10）
- $`\mathcal E[K]`（4.6.7.1）　／　対象 $`x,y`、$`\mathrm{Hom}(x,y)=K`。$`\mathcal E[K]\to\mathcal C` は $`K\to\mathcal C(X,Y)` と同じ
- $`\theta`（4.6.7.3）　／　$`S\mapsto\min(S\setminus\{x\})`。7.2 の $`r^*` そのもの
- $`\Phi(K)=\mathrm{Hom}_{\mathrm{Path}[\Sigma K]}(x,y)`（4.6.7.10）　／　$`\Sigma K` は非約懸垂。$`\Phi(\Delta^n)=J^n`、余単体的対象 $`Q^\bullet`
- 随伴（4.6.7.16〜21）　／　$`\{K\to\mathrm{Hom}^L\}\cong\{\Phi(K)\to\mathcal C(X,Y)\}`。$`\Phi=&#124;-&#124;^Q` は余極限と単射を保つ
- $`\rho_K\colon\Phi(K)\to K`（4.6.7.22）　／　$`\theta` を随伴で移したもの。$`K=\Delta^n` なら $`r_n`

*route-classification.html — 5. 段 3：$`\mathcal S=N^{hc}(\mathrm{Kan})` と写像空間の比較定理 — 5.3（3.3）写像空間の比較定理*

*主張*（Kerodon Theorem 4.6.7.5）：局所 Kan な $`\mathcal C` について比較写像 $`\theta\colon\mathcal C(X,Y)\to\mathrm{Hom}^L_{N^{hc}\mathcal C}(X,Y)` はホモトピー同値（$`\mathrm{Hom}^R` とは向きの反転を除いて同じ）。一般形（Theorem 4.6.7.8）：$`\mathcal C(X,Y)` が準圏なら $`\mathrm{Hom}^L` も準圏で $`\theta` は圏同値。Kan 性はこの準圏性にだけ使う。

1. \*\*$`\mathrm{Hom}^L` は $`\mathcal C(X,Y)` だけで決まる\*\*：$`n` 単体は懸垂 $`\Sigma(K)=(\{x\}\star K)\sqcup_K\{y\}`（$`K=\Delta^n`）からの写像。$`\Phi(K):=\mathfrak C\Sigma K` と置くと $`\mathrm{Hom}(K,\mathrm{Hom}^L)\cong\mathrm{Hom}(\Phi(K),\mathcal C(X,Y))`、つまり $`\mathrm{Hom}^L` は $`\Phi` の右随伴。

2. \*\*$`\Phi(\Delta^n)` は太らせた $`\Delta^n`\*\*：$`\Phi(\Delta^0)=\Delta^0`、$`\Phi(\Delta^1)=\Delta^1`（向き反転、データは $`f_{01},f_{02}` と $`f_{02}\to f_{01}` の辺）、$`\Phi(\Delta^2)` は $`t_1=1` の辺を潰した正方形。一般に単体は最大元を共有する部分集合の減少列（旗、Kerodon Ex. 4.6.7.27）で、$`\Phi(\Delta^n)\cong\Delta^0\diamond\Phi(\Delta^{n-1})`（鈍い join）。頂点を $`[n]` の元に送る $`\rho_K\colon\Phi(K)\to K` が $`\theta` に対応。

3. *鍵の補題*（Prop. 4.6.7.23）：$`\rho_K` は圏同値。有限な $`K` に帰着（フィルター余極限）、$`\Phi` が余極限と単射を保つので単体ごとの帰納法で $`\Delta^n` に帰着、$`\rho_{\Delta^n}` は $`\mathrm{id}\diamond\rho_{\Delta^{n-1}}`（帰納法）と鈍い join から join への比較（Prop. 4.6.2.12）の合成。

4. *結論*：内アノダインな $`A\to B` で $`\Phi(A)\to\Phi(B)` は単射かつ圏同値なので $`\mathrm{Hom}^L` は準圏。$`\pi_0\mathrm{Fun}(K,M)^{\simeq}\to\pi_0\mathrm{Fun}(K,\mathrm{Hom}^L)^{\simeq}=\pi_0\mathrm{Fun}(\Phi(K),M)^{\simeq}`（Cor. 4.6.7.26）は $`\rho_K` の前合成で全単射、よって $`\theta` は圏同値。$`M` が Kan ならホモトピー同値。

*直観*：$`N^{hc}\mathcal C` の写像空間の単体は $`\mathcal C(X,Y)` の単体を太らせた形 $`\Phi(\Delta^n)` で見たもので、太らせても圏同値なのでホモトピー型は変わらない。$`\mathfrak C` の一般論は要らず、懸垂の場合だけを直接計算する。

*Lean での扱い*：比較写像 \`coherentHomComparisonObj\` など（F1/Coherent/HomComparison、Kerodon Construction 4.6.7.3 を右 pinched の向きに）。比較定理 \`coherentHomComparison\_isQCatEquivalence\`、\`coherentHomComparison\_isSimplicialHomotopyEquivalence\`、\`coherentHomEquivalence\`（F1/Coherent/HomEquivalence）。旗と解像は F1/Coherent の \`Flag\*.lean\`、\`MaximumFlag.lean\`、\`LeftResolution\*.lean\`。方針は「旗の解像の右随伴との同型で比較写像を同定し同値性を移す」で上と同じ組み立て。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison_isSimplicialHomotopyEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison_isQCatEquivalence`

:::

:::theorem "kerodon_4_6_7_8" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_6_7_3, kerodon_4_6_7_22, kerodon_4_6_7_23, kerodon_4_6_7_25, kerodon_4_6_7_26")
Kerodon Theorem 4.6.7.8（[Tag 01LG](https://kerodon.net/tag/01LG)）。対応表の状態：なし。

右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath\[ΣK\]の特定のΦ・ρとの同定がない。Hom が Kan 複体の場合（Thm 4.6.7.5）だけ。Hom が ∞ 圏のときの同値は未。

*f-c-spaces.html — 8. Kerodon 4.6.7 の証明（モデル圏なし）*

*定理 4.6.7.8 ⇒ 4.6.7.5*：$`\mathrm{Hom}^L` は ∞ 圏（4.6.7.25：内部 horn を $`\Phi(i)` に沿った延長に移す）。すべての $`K` で $`\pi_0\mathrm{Fun}(K,-)^{\simeq}` の全単射を示せばよく、categorical mapping cylinder（4.6.7.26）で右辺を $`\pi_0\mathrm{Fun}(\Phi(K),\mathcal C(X,Y))^{\simeq}` と同一視すると $`\theta` は $`\rho_K` の前合成になり全単射。$`\mathcal C(X,Y)` が ∞ 圏であるだけでよく、局所 Kan なら Kan 複体の間のカテゴリー同値なのでホモトピー同値（Example 4.6.7.7 が $`\mathrm{Fun}(X,Y)\simeq\mathrm{Hom}_{\mathcal S}(X,Y)`）。素朴な方針との違いは、帰納法を余単体の次数でなく定義域 $`K` の骨格で行い、自然な $`\rho_K` をより強いカテゴリー同値として示すことで、$`s_n` が自然でない問題が起きない点。

*f-c-spaces.html — 10. 局所 Kan でない場合に止まる場所*

- 段　／　仮定　／　quasicategory $`Z=\mathcal C(X,Y)` で通るか
- $`N^{hc}(\mathcal C)` が quasicategory（Coherent）　／　局所 Kan　／　通らない（4.3）
- $`\mathrm{Hom}\cong\mathrm{Sing}^QZ`（FlagIso）　／　なし　／　通る
- $`\rho_K` が前合成の同値　／　なし　／　通る
- $`\mathrm{Sing}^QZ` が quasicategory（ResolutionRightQuasicategory）　／　$`Z` が quasicategory　／　通る
- 厳密な左逆（ResolutionRetraction）　／　\`\[KanComplex Z\]\` と書いている　／　中の \`exists\_extension\_of\_functorIso\` は quasicategory で済むので、おそらく通る
- 後合成の本質的全射性（ResolutionCylinder）　／　\`\[KanComplex Z\]\`　／　*止まる*：転置したホモトピー $`H` を \`functorIsoOfSimplicialHomotopy\`（標的が Kan）で同型に戻しており、quasicategory では $`H` の可逆性を別に示す必要がある
- 単体的ホモトピー同値への変換　／　両側が Kan　／　結論の形の問題（∞ 圏の同値で止めればよい）

一般化するなら、Kerodon 4.6.7.8 の方式（写像柱で「同型の転置は同型」を処理）、転置の可逆性を直接示す（円筒の比較 $`\Phi(K\times\Delta^1)\to\Phi K\times\Delta^1` が可逆な辺を保つことを示して差し替える）、Hom を $`\mathrm{Ex}^\infty` で Kan 化する（2 射の向きは消える）のいずれか。$`\mathcal S` と $`\mathrm{Cat}_\infty` はどちらも局所 Kan なので今の形で足り、Hom が ∞ 圏の場合が要るのは $`\mathrm{Cat}_\infty` の 2 圏構造や $`\mathrm{Corr}` の 2 射のような (∞,2) 的な場面で、そこでは写像空間の比較より先に (∞,2) の模型を選ぶ問題になる。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionComparison_isQCatEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint_quasicategory`

:::

:::proposition "kerodon_4_6_7_9"
Kerodon Remark 4.6.7.9（[Tag 01LH](https://kerodon.net/tag/01LH)）。対応表の状態：なし。

右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath\[ΣK\]の特定のΦ・ρとの同定がない。右 pinched で直接作っているので op 経由の主張はない。Kan の場合だけ。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison_enriched_naturality`

:::

:::definition "kerodon_4_6_7_10" (uses := "kerodon_1_1_0_6, kerodon_2_4_4_2")
Kerodon Construction 4.6.7.10（[Tag 01LJ](https://kerodon.net/tag/01LJ)）。対応表の状態：なし。

右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath\[ΣK\]の特定のΦ・ρとの同定がない。仮定：任意の単体集合 K（Kerodon と一致）。結論：coherentResolution は標準単体上の旗から拡張した関手（Lean が弱い：Path\[ΣK\] の指定二点間の Hom と同定する型がない）。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex`

:::

:::lemma_ "kerodon_4_6_7_15"
Kerodon Lemma 4.6.7.15（[Tag 01LP](https://kerodon.net/tag/01LP)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：一つの豊穣 Hom・二対象・局所 Kan の特例・次数を固定した解像を照合。E\[K\] からの対象固定 enriched functor と K から Hom(X,Y) への射の全単射。通常 nerve の完全忠実性はこの対応の型ではない。

:::

:::corollary "kerodon_4_6_7_16" (uses := "kerodon_1_1_0_6")
Kerodon Corollary 4.6.7.16（[Tag 01LQ](https://kerodon.net/tag/01LQ)）。対応表の状態：なし。

右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath\[ΣK\]の特定のΦ・ρとの同定がない。仮定：任意の単体集合 K、単体豊穣圏 C と対象 X,Y（Kerodon と一致）。結論：右 pinched の R(Hom\_C(X,Y)) との同型と Φ⊣R が Hom 全単射を与える（Lean が弱い：原文の左 pinched 版との同定を欠く）。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinchedFlagIso`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction`

:::

:::corollary "kerodon_4_6_7_18" (uses := "kerodon_1_1_0_6, kerodon_4_6_7_1, kerodon_4_6_7_16")
Kerodon Corollary 4.6.7.18（[Tag 01LR](https://kerodon.net/tag/01LR)）。対応表の状態：なし。

右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath\[ΣK\]の特定のΦ・ρとの同定がない。E\[B\] の構成がないので、随伴 Φ ⊣ R だけ。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction`

:::

:::corollary "kerodon_4_6_7_19"
Kerodon Corollary 4.6.7.19（[Tag 01LS](https://kerodon.net/tag/01LS)）。対応表の状態：なし。

右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath\[ΣK\]の特定のΦ・ρとの同定がない。右随伴は抽象的に定義していて、Hom\^L\_\{N(E\[B\])\}(x,y) との同一視はない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint`

:::

:::corollary "kerodon_4_6_7_21" (uses := "kerodon_4_6_7_10")
Kerodon Corollary 4.6.7.21（[Tag 01LU](https://kerodon.net/tag/01LU)）。対応表の状態：なし。

右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath\[ΣK\]の特定のΦ・ρとの同定がない。仮定：任意の単体集合の図式（Kerodon と一致）。結論：旗で定めた coherentResolution が余極限を保存（Lean が弱い：原文の Path\[ΣK\] の Φ との同定は未確認）。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution_preservesColimitsOfSize`

:::

:::definition "kerodon_4_6_7_22" (uses := "kerodon_1_1_0_6, kerodon_4_6_7_1, kerodon_4_6_7_3, kerodon_4_6_7_18")
Kerodon Construction 4.6.7.22（[Tag 01LV](https://kerodon.net/tag/01LV)）。対応表の状態：なし。

右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath\[ΣK\]の特定のΦ・ρとの同定がない。仮定：任意の単体集合 K（Kerodon と一致）。結論：coherentResolutionProjectionAll は旗の解像から K への自然変換（Lean が弱い：原文の E\[K\] の左 pinched 比較を転置した射との一致は型にない）。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll`

:::

:::proposition "kerodon_4_6_7_23" (uses := "kerodon_1_1_0_6, kerodon_1_1_4_12, kerodon_4_5_5_9, kerodon_4_6_2_3, kerodon_4_6_2_12, kerodon_4_6_7_21, kerodon_4_6_7_22, kerodon_4_6_7_29, kerodon_4_8_8_11")
Kerodon Proposition 4.6.7.23（[Tag 01LW](https://kerodon.net/tag/01LW)）。対応表の状態：なし。

右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath\[ΣK\]の特定のΦ・ρとの同定がない。仮定：任意の単体集合 K（Kerodon と一致）。結論：coherentResolutionProjectionAll.app K は前合成同値（Lean が弱い：原文の指定 ρ\_K と同じ射であることを引用先から確認できない）。

*f-c-spaces.html — 8. Kerodon 4.6.7 の証明（モデル圏なし）*

\*\*命題 4.6.7.23：$`\rho_K` はすべての $`K` でカテゴリー同値\*\*。有限に帰着（$`\Phi` は余極限を保ち、カテゴリー同値は filtered 余極限で閉じる、4.8.8.11）→ 骨格の帰納法（単射に沿った押し出しはカテゴリー的押し出し、4.5.5.9）→ $`\Delta^n`：$`\Phi(\Delta^n)\cong\Delta^0\diamond\Phi(\Delta^{n-1})`（4.6.7.29）で、$`\rho_{\Delta^n}` は $`\mathrm{id}\diamond\rho`（帰納法と 4.6.2.7）と blunt join と join の比較 $`c\colon\Delta^0\diamond\Delta^{n-1}\to\Delta^n`（4.6.2.12）の合成。blunt join $`A\diamond B` は円柱 $`A\times\Delta^1\times B` の両端を $`A`、$`B` につぶしたもの。$`\Phi(\Delta^2)\cong\Delta^0\diamond\Delta^1`（正方形の一辺をつぶしたもの）は 7.1 の $`J^2` と一致する。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll_isPrecompositionEquivalence`

:::

:::corollary "kerodon_4_6_7_24" (uses := "kerodon_1_1_0_6, kerodon_4_6_7_23")
Kerodon Corollary 4.6.7.24（[Tag 01LX](https://kerodon.net/tag/01LX)）。対応表の状態：なし。

右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath\[ΣK\]の特定のΦ・ρとの同定がない。仮定：K→K′ が前合成同値（Lean が強い：原文の π₀ 条件との橋渡しが引用にない）。結論：旗の解像による像は前合成同値（Lean が弱い：Path\[Σ−\] の関手との比較を欠く）。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution_map_isPrecompositionEquivalence`

:::

:::corollary "kerodon_4_6_7_25" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_5_6_2, kerodon_4_6_7_16, kerodon_4_6_7_24")
Kerodon Corollary 4.6.7.25（[Tag 01LY](https://kerodon.net/tag/01LY)）。対応表の状態：なし。

右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath\[ΣK\]の特定のΦ・ρとの同定がない。仮定：単体豊穣圏 C の Hom\_C(X,Y) が ∞ 圏（Kerodon と一致）。結論：右随伴 R の値が ∞ 圏であり、右 pinched と同型（Lean が弱い：原文の左 pinched の模型との比較を欠く）。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint_quasicategory`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinchedFlagIso`

:::

:::corollary "kerodon_4_6_7_26" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_6_3_3, kerodon_4_6_3_7, kerodon_4_6_7_16, kerodon_4_6_7_21, kerodon_4_6_7_24")
Kerodon Corollary 4.6.7.26（[Tag 01LZ](https://kerodon.net/tag/01LZ)）。対応表の状態：なし。

右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath\[ΣK\]の特定のΦ・ρとの同定がない。仮定：単体集合 K の解像に沿う豊穣比較。型は解像側の指定ホモトピーを仮定。結論：指定ホモトピーを随伴で移す方向がある。原文の一つの豊穣 Hom の準圏性で二つの像の同型を比較する iff は未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionTransposeHomotopy`

:::

:::proposition "kerodon_4_6_7_27" (uses := "kerodon_1_1_0_6, kerodon_2_4_4_9")
Kerodon Example 4.6.7.27（[Tag 01M0](https://kerodon.net/tag/01M0)）。対応表の状態：なし。

右pinched/旗の解像についての型で、原文の左pinchedの指定θまたはPath\[ΣK\]の特定のΦ・ρとの同定がない。仮定：m,n が非負整数（Kerodon と一致）。結論：CoherentResolutionFlag n m は最小元から始まる増大旗（Lean が弱い：ΣΔⁿ の非退化単体と両端固定の減少旗による原文の集合との全単射が型にない）。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag`

:::

:::definition "kerodon_4_6_7_28" (uses := "kerodon_1_1_0_6, kerodon_4_6_7_27")
Kerodon Construction 4.6.7.28（[Tag 01M1](https://kerodon.net/tag/01M1)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：一つの豊穣 Hom・二対象・局所 Kan の特例・次数を固定した解像を照合。部分集合鎖で定める Φ(Δⁿ)×Δ¹→Φ(Δⁿ⁺¹) の指定写像。rigidification の頂点鎖・necklace はこの二変数射を定めない。

:::

:::lemma_ "kerodon_4_6_7_29" (uses := "kerodon_1_1_0_6, kerodon_4_6_7_28")
Kerodon Lemma 4.6.7.29（[Tag 01M2](https://kerodon.net/tag/01M2)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：一つの豊穣 Hom・二対象・局所 Kan の特例・次数を固定した解像を照合。指定された Φ(Δⁿ)×Δ¹→Φ(Δⁿ⁺¹) の性質。通常の Δ¹ cylinder 比較には部分集合鎖モデル Φ の端点条件がない。

:::

# 4.6.8 Composition of Morphisms

%%%
number := false
tag := "kerodon-4-6-8"
%%%

Kerodon [Tag 01PF](https://kerodon.net/tag/01PF)

:::definition "kerodon_4_6_8_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace") (uses := "kerodon_1_1_0_6")
Kerodon Notation 4.6.8.1（[Tag 01PG](https://kerodon.net/tag/01PG)）。対応表の状態：一部。

*主張*　単体集合 $`C` の空でない有限頂点列 $`x_0,\ldots,x_n` に対し、$`\operatorname{Hom}_C(x_0,\ldots,x_n)` は $`\operatorname{Fun}(\Delta^n,C)` の頂点制限の指定列上のファイバーである。

intervalMappingSpaceは頂点列が二つ、n=1の場合の原文と同じ区間関手空間の両端固定fiberを直接構成する。任意長の列は含まない。

:::

:::proposition "kerodon_4_6_8_4" (uses := "kerodon_1_1_0_6, kerodon_4_1_4_4")
Kerodon Proposition 4.6.8.4（[Tag 01PK](https://kerodon.net/tag/01PK)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：二端・1 圏・dg の特例・片方向の比較と基底変換・ホモトピー圏に降りる形を照合。内ファイブレーションが誘導する有限頂点列 Hom の Kan ファイブレーション。二点間の pinched Hom の比較だけでは任意列を固定できない。

:::

:::corollary "kerodon_4_6_8_5" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Corollary 4.6.8.5（[Tag 01PL](https://kerodon.net/tag/01PL)）。対応表の状態：なし。

compositionCorrespondenceFirstは第二辺gを固定したfiberからの射。原文の二つのHomがともに変動する積への制限射と異なり、全空間のRLPを直接返さない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceFirst_trivialKanFibration`

:::

:::corollary "kerodon_4_6_8_8"
Kerodon Corollary 4.6.8.8（[Tag 01PP](https://kerodon.net/tag/01PP)）。対応表の状態：なし。

compositionCorrespondenceは第二辺を固定した別のfiber。原文の三頂点だけを固定したHom(X₀,X₁,X₂)全体のKan性と同一視する宣言がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondence_kanComplex`

:::

:::definition "kerodon_4_6_8_9" (uses := "kerodon_1_4_0_1, kerodon_4_6_8_5")
Kerodon Construction 4.6.8.9（[Tag 01PQ](https://kerodon.net/tag/01PQ)）。対応表の状態：なし。

compositionCorrespondenceとKanMappingCompositionは特定の辺・三角形を固定した対応。原文の二つの写像空間の積からhKanでの合成射を構成する型ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondence`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanMappingComposition`

:::

:::proposition "kerodon_4_6_8_11" (uses := "kerodon_1_1_0_6, kerodon_1_1_1_4, kerodon_1_1_2_1, kerodon_1_2_5_1, kerodon_1_4_0_1")
Kerodon Proposition 4.6.8.11（[Tag 01PS](https://kerodon.net/tag/01PS)）。対応表の状態：なし。

dg nerveの右pinchedのAW合成の単位則で、原文の区間模型のhKan合成と同定されていない。対象・合成の比較なしに類似の律だけをspecialにしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomComposition_unit_left`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomComposition_unit_right`

:::

:::proposition "kerodon_4_6_8_12" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_6_8_5")
Kerodon Proposition 4.6.8.12（[Tag 01PT](https://kerodon.net/tag/01PT)）。対応表の状態：なし。

dg nerveの右pinchedのAW合成の結合則で、原文の区間模型のhKan合成と同定されていない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomComposition_assoc`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily_assoc`

:::

:::definition "kerodon_4_6_8_13" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_2_1_7_1, kerodon_4_6_1_1, kerodon_4_6_8_9, kerodon_4_6_8_11, kerodon_4_6_8_12")
Kerodon Construction 4.6.8.13（[Tag 01PV](https://kerodon.net/tag/01PV)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：二端・1 圏・dg の特例・片方向の比較と基底変換・ホモトピー圏に降りる形を照合。hKan の直積モノイダル構造上の enrichment としての hC。通常の HomotopyCategory は Hom 集合に π₀ を取る。

:::

:::definition "kerodon_4_6_8_15" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_6_8_9")
Kerodon Notation 4.6.8.15（[Tag 01TP](https://kerodon.net/tag/01TP)）。対応表の状態：なし。

固定辺のcompositionCorrespondenceの構成だけは、原文のhKanの前後合成の射とそのホモトピー類だけへの依存を結論しない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondence`

:::

:::proposition "kerodon_4_6_8_16" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_6_5_7")
Kerodon Proposition 4.6.8.16（[Tag 02LL](https://kerodon.net/tag/02LL)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：二端・1 圏・dg の特例・片方向の比較と基底変換・ホモトピー圏に降りる形を照合。f による合成と二種 Hom の比較が作る四角のホモトピー可換性。成分上の合成や単一の比較同値にはその四角がない。

:::

:::corollary "kerodon_4_6_8_18" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_3_6_12, kerodon_4_4_3_8, kerodon_4_6_5_5, kerodon_4_6_5_10, kerodon_4_6_8_16")
Kerodon Corollary 4.6.8.18（[Tag 02R3](https://kerodon.net/tag/02R3)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：二端・1 圏・dg の特例・片方向の比較と基底変換・ホモトピー圏に降りる形を照合。coslice の Hom と合成写像の指定値でのホモトピーファイバーの比較。coslice 全体の制限は f,g を固定した空間を計算しない。

:::

:::proposition "kerodon_4_6_8_19" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_4_6_8_9")
Kerodon Proposition 4.6.8.19（[Tag 02LN](https://kerodon.net/tag/02LN)）。対応表の状態：なし。

coherentCompositionCorrespondenceは射を一つ固定した対応への写像。原文の両因子が変動する積とhKan合成の可換正方形を直接返さず、canonicalなθの規約の比較も要る。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentCompositionCorrespondence`

:::

:::corollary "kerodon_4_6_8_20" (uses := "kerodon_2_4_6_9, kerodon_4_6_8_13")
Kerodon Corollary 4.6.8.20（[Tag 02LP](https://kerodon.net/tag/02LP)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：二端・1 圏・dg の特例・片方向の比較と基底変換・ホモトピー圏に降りる形を照合。locally Kan enriched category と hc nerve の Hom 比較が合成と両立。hC の通常圏同型だけでは空間レベルの合成を扱わない。

:::

:::proposition "kerodon_4_6_8_21"
Kerodon Proposition 4.6.8.21（[Tag 03E0](https://kerodon.net/tag/03E0)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：二端・1 圏・dg の特例・片方向の比較と基底変換・ホモトピー圏に降りる形を照合。dg Hom のテンソル合成と dg nerve の写像空間合成のホモトピー可換性。Dold–Kan の比較や dg nerve の定義だけでは合成四角を与えない。

:::

