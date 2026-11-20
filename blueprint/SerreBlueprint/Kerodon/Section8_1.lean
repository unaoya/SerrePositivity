-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Yoneda
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.CosliceTwistedHomComparison
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.CosliceTwistedHomEquivalence
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseDuality
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseDualityLeftEndpoint
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseEndpoints
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseLeftFilling
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseRightFilling
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseStandardSimplex
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseSubdivision
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.FullyFaithfulJointHom
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.HomSpace
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.LeftFibration
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.LeftKanFibration
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.Objects
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.Projection
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.Source
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.SourceInitial
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowFunctorComparison

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "8.1 Twisted Arrows and Cospans" =>
%%%
number := false
tag := "kerodon-8-1"
%%%

Kerodon の 8.1 節（[Tag 03JB](https://kerodon.net/tag/03JB)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

:::definition "kerodon_8_1_0_1" (lean := "CategoryTheory.coyoneda, CategoryTheory.Functor.uncurry, CategoryTheory.Functor.Elements, CategoryTheory.Functor.Elements.Hom, CategoryTheory.Functor.Elements.instCategory")
Kerodon Construction 8.1.0.1（[Tag 00AZ](https://kerodon.net/tag/00AZ)）。対応表の状態：Mathlib にある。

*主張*　通常の圏 $`C` のねじれ矢印圏の対象は射 $`f:x\to y` であり、$`f` から $`f':x'\to y'` への射は $`f'=vfu` となる $`u:x'\to x,v:y\to y'` の組である。合成は始域側を逆順、終域側を順に合成する。

仮定：通常圏 C を与える（Kerodon と一致）。結論：coyoneda を uncurry した Hom 二変数関手の Elements で、対象は f:X→Y、射は逆向き u と順向き v で u≫f≫v=f'、合成は Cᵒᵖ×C の成分別合成になる（一致）。

:::

# 8.1.1 The Twisted Arrow Construction

%%%
number := false
tag := "kerodon-8-1-1"
%%%

Kerodon [Tag 03JF](https://kerodon.net/tag/03JF)

*注意 （大きさ）*

$`C` が小さければ $`\mathrm{Tw}(C)` は小さく、射影 $`\mathrm{Tw}(C)\to C^{\mathrm{op}}\times C` は小さいファイバーをもつ（定義 11.2）。

*f-c-spaces.html — 11. $`\mathrm{Map}` を関手にする：twisted arrow の straightening — 11.6 ファイバーの計算*

$`(x,y)` 上のファイバーの $`n` 単体は、左半分がすべて $`x`、右半分がすべて $`y` の $`\Delta^{2n+1}\to C`（TwistedArrow/HomSpace）。

- 0 単体：射 $`f\colon x\to y`。

- 1 単体：3 単体 $`x\xrightarrow{\mathrm{id}}x\to y\xrightarrow{\mathrm{id}}y`。辺 $`f_0=(\bar0,0)`、$`f_1=(\bar1,1)`、$`a=(\bar1,0)`、$`b=(\bar0,1)`。四つの三角形は一辺が恒等射で $`f_0\sim a`、$`f_0\sim b`、$`a\sim f_1`、$`b\sim f_1`、3 単体がそれらを整合させる。$`\mathrm{Hom}^L(x,y)` の 1 単体（三角形 $`(x;y,y)` 一つ）よりデータは多いが同値。

*比較写像*（\`cosliceTwistedHomMap\`）：左半分を錐点につぶす崩壊 $`(\Delta^n)^{\mathrm{op}}\star\Delta^n\to\Delta^0\star\Delta^n` の前合成で、$`n` について自然な $`\mathrm{Hom}^L(x,y)\to\mathrm{Tw}(C)_{(x,y)}`。$`n=1` では三角形 $`\tau` を退化した 3 単体に送り、$`a=f_0`、$`b=f_1`。素朴な逆「$`\bar0\star\Delta^n` に制限」は、$`d_0` が $`\bar0` と $`0` を同時に除くので面写像と可換にならない（$`N^{hc}` の $`s_n` と同じ種類の難点）。

*証明*（TwistedHomRows、TwistedHomDiagonal、Joins/CosliceTwistedHomEquivalence）：前に候補として挙げた二重単体の対角の方式。

1. 左の大きさ $`m` と右の大きさ $`n` を別々に動かした二重単体集合 $`R_{m,n}=\{(\Delta^m)^{\mathrm{op}}\star\Delta^n\to C\mid\text{左は }x\text{、右は }y\text{ で一定}\}`。

2. $`m` を固定した行は、退化単体 $`\sigma`（$`x` の $`m` 単体）の下のスライス $`C_{\sigma/}` の $`y` 上のファイバーそのもの。崩壊 $`\Delta^m\to\Delta^0` による比較 $`\mathrm{Hom}^L(x,y)\to R_{m,\bullet}` は同値（\`cosliceSimplexExpansion\_isQCatEquivalence\`）。頂点への制限 $`C_{\sigma/}\to C_{x/}` が trivial fibration で、join の持ち上げの補題で端の頂点の包含が anodyne であることに帰着する。

3. 各行で同値なら対角でも同値（\`localized\_diagonal\_map\`）。

4. $`R` の対角 $`R_{n,n}` は $`\mathrm{Tw}(C)_{(x,y)}`、定数の側の対角は $`\mathrm{Hom}^L(x,y)`。

自然性の問題は行ごとに $`m` を固定して避け、対角補題が全体をまとめる。

:::definition "kerodon_8_1_1_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow")
Kerodon Construction 8.1.1.1（[Tag 03JG](https://kerodon.net/tag/03JG)）。対応表の状態：本体にある。

*主張*　単体集合 $`C` のねじれ矢印単体集合 $`\operatorname{Tw}(C)` の $`J`-単体は、全順序集合の結合 $`J^{\mathrm{op}}\star J` の神経から $`C` への単体写像である。単体作用素はこの結合に沿う前合成で定まる。

仮定：C : SSet。∞圏性の仮定なし（Kerodon と一致）。結論：TwistedArrow C は edgewiseWeight の各重みから C への写像で作る単体集合。重みは \[n\]ᵒᵖ⋆\[n\] を表す（原文の Tw(C) と一致）。

*定義 12.2 （twisted arrow $`\mathrm{Tw}(C)`）*

単体的集合 $`C` について、単体的集合 $`\mathrm{Tw}(C)` を

$$`\mathrm{Tw}(C)([n])=\mathrm{Hom}_{\mathrm{sSet}}\bigl((\Delta^n)^{\mathrm{op}}\star\Delta^n,\ C\bigr)`

で定め、$`\theta\colon[m]\to[n]` は $`(\theta_*)^{\mathrm{op}}\star\theta_*\colon(\Delta^m)^{\mathrm{op}}\star\Delta^m\to(\Delta^n)^{\mathrm{op}}\star\Delta^n` の前合成で作用させる（反対は定義 12.1、join とその関手性は定義 4.3・定義 4.4、$`\theta_*` は定義 2.2）。

:::

:::proposition "kerodon_8_1_1_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSimplexEquiv, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight") (uses := "kerodon_1_1_0_6")
Kerodon Remark 8.1.1.2（[Tag 03JH](https://kerodon.net/tag/03JH)）。対応表の状態：一部。

*主張*　$`\operatorname{Tw}(C)` の $`n`-単体は $`C` の $`(2n+1)`-単体と一意に同一視できる。$`i` 番目の面と退化は、対応する単体の対称な位置 $`n-i,n+1+i` をそれぞれ削除または重ねて得る。

edgewiseSimplexEquivは同じTw(C)のn単体をCの(2n+1)単体へ同定する原文の成分を直接与える。全ての面・退化の二重合成式は引用に含まない。

*f-c-spaces.html — 11. $`\mathrm{Map}` を関手にする：twisted arrow の straightening — 11.4 $`n=0,1,2` の計算*

\*\*$`n=0`\*\*：$`\Delta^1`（$`\bar0\to0`）。頂点は $`C` の射 $`f\colon x\to y`（退化した $`\mathrm{id}_x` も含む）。

\*\*$`n=1`\*\*：$`\Delta^3`、$`x_1\xrightarrow{u}x_0\xrightarrow{f_0}y_0\xrightarrow{v}y_1`。

- 辺　／　意味
- $`(\bar1,\bar0)=u`　／　$`C^{\mathrm{op}}` 成分（$`C^{\mathrm{op}}` では $`x_0\to x_1`）
- $`(0,1)=v`　／　$`C` 成分
- $`(\bar0,0)=f_0`　／　$`\mathrm{Tw}` の辺の始点（$`d_1`）
- $`(\bar1,1)=f_1`　／　$`\mathrm{Tw}` の辺の終点（$`d_0`）
- $`(\bar1,0)`、$`(\bar0,1)`　／　途中の合成 $`f_0u`、$`vf_0`

四つの三角形と 3 単体が $`f_1\simeq v\circ f_0\circ u` をすべての括弧の付け方で整合的に与える。$`\mathrm{Tw}` の辺 $`f_0\to f_1` は $`f_0` を内側、$`f_1` を外側に置いた入れ子の矢。$`C` が普通の圏なら $`N(\mathrm{Tw}\,C)` は古典的な twisted arrow 圏（射 $`f_0\to f_1` は $`f_1=vf_0u` をみたす $`(u,v)`）。

\*\*$`n=2`\*\*：$`\Delta^5`、$`x_2\to x_1\to x_0\xrightarrow{f_0}y_0\to y_1\to y_2`。頂点は入れ子の三本の矢 $`f_0=(\bar0,0)`、$`f_1=(\bar1,1)`、$`f_2=(\bar2,2)`。辺は $`d_2`（$`\bar1\bar0\,01`）が $`f_0\to f_1`、$`d_0`（$`\bar2\bar1\,12`）が $`f_1\to f_2`、$`d_1`（$`\bar2\bar0\,02`）が $`f_0\to f_2`。5 単体全体が「$`f_0\to f_1\to f_2` の合成が $`f_0\to f_2`」の整合性を運ぶ。

:::

:::proposition "kerodon_8_1_1_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor") (uses := "kerodon_1_1_0_6, kerodon_8_1_1_2")
Kerodon Remark 8.1.1.4（[Tag 00B3](https://kerodon.net/tag/00B3)）。対応表の状態：一部。

*主張*　単体集合のねじれ矢印関手 $`\operatorname{Tw}` は、すべての極限と余極限を保つ。

edgewiseSubdivisionFunctorは原文の同じC↦Tw(C)の関手性を直接構成する。全極限・全余極限保存はその型に含まない。

:::

:::definition "kerodon_8_1_1_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection")
Kerodon Notation 8.1.1.6（[Tag 03JK](https://kerodon.net/tag/03JK)）。対応表の状態：本体にある。

*主張*　$`\operatorname{Tw}(C)` の単体を $`[n]^{\mathrm{op}}\star[n]` の左半分と右半分に制限すると、それぞれ $`C^{\mathrm{op}}` と $`C` への射影を得る。頂点 $`f:x\to y` はそれぞれ $`x,y` に移る。

仮定：任意の C : SSet（Kerodon と一致）。結論：edgewiseLeft と edgewiseRight は重みの左半分と右半分への制限で、それぞれ Cᵒᵖ と C に値を取る。twistedArrowProjection はその積への射（λ₋ と λ₊ に一致）。

*定義 12.3 （$`\mathrm{Tw}(C)` の射影）*

$`n` 単体 $`\sigma\colon(\Delta^n)^{\mathrm{op}}\star\Delta^n\to C` について、包含 $`\iota_{(\Delta^n)^{\mathrm{op}}}`、$`\iota_{\Delta^n}`（定義 4.4）への制限は射 $`(\Delta^n)^{\mathrm{op}}\to C` と $`\Delta^n\to C` である。前者を定義 12.1 の対応で $`\Delta^n\to C^{\mathrm{op}}` とみて、射

$$`\mathrm{Tw}(C)\to C^{\mathrm{op}}\times C`

を定める（積は定義 2.1。$`\Delta^n` からの射と $`n` 単体は米田の補題で同一視する）。

:::

:::proposition "kerodon_8_1_1_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseDualityIso, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseDuality_right, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseDuality_left") (uses := "kerodon_1_1_0_6, kerodon_8_1_1_6")
Kerodon Remark 8.1.1.7（[Tag 03JL](https://kerodon.net/tag/03JL)）。対応表の状態：本体にある。

*主張*　単体集合 $`C` のねじれ矢印単体集合は、反対単体集合 $`C^{\mathrm{op}}` のねじれ矢印単体集合と標準的に同型である。各 $`[n]^{\mathrm{op}}\star[n]` の順序反転から来るこの同型は二つの射影を交換する。

edgewiseDualityIsoに現本体のedgewiseDuality\_rightとedgewiseDuality\_leftを合わせると、原文の同じ双対同型と左右射影の交換を直接得る。左側では二重opの標準同型も式に含まれる。

:::

:::proposition "kerodon_8_1_1_10"
Kerodon Proposition 8.1.1.10（[Tag 03JN](https://kerodon.net/tag/03JN)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：任意の単体集合の Tw は edgewiseSubdivision として定義され、射影は単体写像に自然。通常圏の twisted arrow 圏の nerve との同型と、対象上恒等・底の四角形による一意性は見つからない。

:::

:::proposition "kerodon_8_1_1_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection_leftFibration")
Kerodon Proposition 8.1.1.11（[Tag 03JQ](https://kerodon.net/tag/03JQ)）。対応表の状態：本体にある。

*主張*　無限圏 $`C` について、ねじれ矢印単体集合の二つの端への射影 $`\operatorname{Tw}(C)\to C^{\mathrm{op}}\times C` は左ファイブレーションである。

仮定：C : SSet と Quasicategory C（Kerodon と一致）。結論：twistedArrowProjection\_leftFibration は (λ₋,λ₊) に当たる積への射の LeftFibration（原文と一致）。

*定理 12.4 （$`\mathrm{Tw}(C)` は左 fibration）*

$`C` が quasicategory なら、射影 $`\mathrm{Tw}(C)\to C^{\mathrm{op}}\times C`（定義 12.3）は左 fibration（定義 5.3）である。

*f-c-spaces.html — 11. $`\mathrm{Map}` を関手にする：twisted arrow の straightening — 11.5 左 fibration であること：持ち上げの計算*

左 horn $`\Lambda^n_i`（$`0\le i<n`）の持ち上げで与えられるのは、$`\Lambda^n_i` の各面 $`\tau` ごとの $`\tau^{\mathrm{op}}\star\tau\to C` と、底の $`(\Delta^n)^{\mathrm{op}}\to C`、$`\Delta^n\to C`。延長の定義域は全体の join でなく対角的な和

$$`D=\bigcup_{\tau\subseteq\Lambda^n_i}(\tau^{\mathrm{op}}\star\tau)\cup(\Delta^n)^{\mathrm{op}}\cup\Delta^n\subseteq(\Delta^n)^{\mathrm{op}}\star\Delta^n`

で、$`D\subseteq\Delta^{2n+1}` が inner anodyne であることを示す（Kerodon 8.1、HA 5.2.1.3）。

- \*\*$`n=1`、$`i=0`\*\*：$`D` は三辺 $`u`、$`f_0`、$`v`、つまり $`\Delta^3` の背骨で、背骨の包含は inner anodyne。持ち上げは $`f_0` を $`(u,v)` に沿って動かした $`v\circ f_0\circ u` で、これが transport。

- \*\*$`n=1`、$`i=1`（右 horn）\*\*：$`D` は $`u`、$`f_1`、$`v`。欠けた辺 $`x_0\to y_0` には $`u` か $`v` の逆が要り、一般には延長できない。$`\mathrm{Tw}(C)` は右 fibration ではない。

- \*\*$`n=2`、$`i=0`\*\*：$`D` は 3 単体 $`\bar1\bar0\,01` と $`\bar2\bar0\,02`、三角形 $`\bar2\bar1\bar0` と $`012` の和。ここから $`\Delta^5` まで内部 horn の貼り付けで埋める。

- \*\*一般の $`n`\*\*：形式化は組合せ論の判定法で処理する（TwistedArrow/HornLifting、SimplexPairing、PairingInner、PairingRegular）。$`D` の外の非退化単体を余次元 1 の面と対にし（pairing）、対の面が常に内部の面で（inner）、祖先関係に無限下降がない（regular）ことを確かめて、内部 horn の貼り付けの列にする。主定理 \`twistedArrowProjection\_leftFibration\`（TwistedArrow/LeftFibration）。

:::

:::corollary "kerodon_8_1_1_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrow_quasicategory")
Kerodon Corollary 8.1.1.12（[Tag 03JR](https://kerodon.net/tag/03JR)）。対応表の状態：本体にある。

*主張*　無限圏 $`C` のねじれ矢印単体集合は無限圏である。

仮定：Quasicategory C（Kerodon と一致）。結論：twistedArrow\_quasicategory は Quasicategory (TwistedArrow C)（一致）。

:::

:::corollary "kerodon_8_1_1_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection_leftFibration, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.leftFibration_fibration_of_kanComplex, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision_kanComplex")
Kerodon Corollary 8.1.1.13（[Tag 048H](https://kerodon.net/tag/048H)）。対応表の状態：本体にある。

*主張*　$`C` が Kan 複体なら、$`\operatorname{Tw}(C)\to C^{\mathrm{op}}\times C` は Kan ファイブレーションであり、$`\operatorname{Tw}(C)` も Kan 複体である。

仮定：KanComplex C。積 Cᵒᵖ×C の Kan 性と Tw(C) の Kan 性で、左ファイブレーションを Kan ファイブレーションへ移す補題の仮定を満たす（Kerodon と一致）。結論：積への射の Fibration と Tw(C) の KanComplex（両方一致）。

:::

:::corollary "kerodon_8_1_1_14" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_1_4, kerodon_5_1_4_1, kerodon_8_1_1_11")
Kerodon Corollary 8.1.1.14（[Tag 03JS](https://kerodon.net/tag/03JS)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Cᵒᵖ×C への射影および始点を固定した C への射影は左ファイブレーション。元の Tw(C) からの二つの射影の cocartesian 性と、反対側射影の像が同型である辺の iff は見つからない。

:::

:::proposition "kerodon_8_1_1_15" (uses := "kerodon_1_1_0_6, kerodon_3_1_2_11, kerodon_8_1_1_6")
Kerodon Proposition 8.1.1.15（[Tag 03JT](https://kerodon.net/tag/03JT)）。対応表の状態：なし。

twistedArrowFunctorComparisonは同じ比較射を作るが、結論のleft fibration性は含まない。充満忠実な場合の前合成同値性もleft fibration性を結論せず、この命題の一部の代用にしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowFunctorComparison`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowFunctorComparison_isPrecompositionEquivalence`

:::

:::corollary "kerodon_8_1_1_16" (uses := "kerodon_1_1_0_6")
Kerodon Corollary 8.1.1.16（[Tag 06BW](https://kerodon.net/tag/06BW)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：各準圏の Tw が準圏になり U が比較写像を誘導する。U の inner fibration または isofibration の性質が Tw(U) に移る型は見つからない。

:::

# 8.1.2 Homotopy Transport for Twisted Arrows

%%%
number := false
tag := "kerodon-8-1-2"
%%%

Kerodon [Tag 03JV](https://kerodon.net/tag/03JV)

*f-c-spaces.html — 11. $`\mathrm{Map}` を関手にする：twisted arrow の straightening — 11.8 残りの比較*

- 比較　／　議論　／　形式化
- (a) $`\mathrm{id}_x` は $`\mathrm{Tw}_x=\{x\}\times_{C^{\mathrm{op}}}\mathrm{Tw}(C)` の始対象　／　崩壊写像の全空間版 $`C_{x/}\to\mathrm{Tw}_x` は $`C` 上の左 fibration の間の写像で、11.6 でファイバーごとに同値なので全体で同値。$`\mathrm{id}_x` は $`C_{x/}` の始対象で、同値で保たれる　／　SourceInitial（\`cosliceToTwistedArrowSource\_isQCatEquivalence\`、\`twistedArrowSourceIdentity\_isInitialVertex\`）
- (b) $`\mathrm{Map}(x,y)\simeq\mathrm{Hom}^L(x,y)`　／　St の値とファイバーの同値に 11.6 を合わせる　／　—
- (c) $`\mathrm{Un}(h_y)\simeq(C_{/y})^{\mathrm{op}}`　／　$`h_y` は $`\mathrm{Map}` の $`C^{\mathrm{op}}\times\{y\}` への制限で、Un は底変換と可換なので $`\mathrm{Un}(h_y)\simeq\mathrm{Tw}^y=\mathrm{Tw}(C)\times_C\{y\}\to C^{\mathrm{op}}`。比較 $`(C_{/y})^{\mathrm{op}}\to\mathrm{Tw}^y` は右半分を錐点 $`y` につぶす崩壊写像で、ファイバーごとに同じ主比較に戻して同値。(a) と双対　／　RightRepresentableTwistedArrowEquivalence
- (d) Yoneda 埋め込みの充満忠実性　／　$`\mathrm{Map}_{\mathcal P(C)}(h_x,h_y)\overset{h_1}{\simeq}\mathrm{Fun}_{/C^{\mathrm{op}}}(\mathrm{Un}\,h_x,\mathrm{Un}\,h_y)\overset{(c)}{\simeq}\mathrm{Fun}_{/C^{\mathrm{op}}}((C_{/x})^{\mathrm{op}},(C_{/y})^{\mathrm{op}})\simeq((C_{/y})^{\mathrm{op}})_x\simeq\mathrm{Hom}(x,y)`（最後から二つ目は fibration 版 Yoneda、$`\mathrm{id}_x` での評価）。加えて、合成が Yoneda 写像の写像空間への作用と一致することの照合（帳簿付けの重い部分）　／　YonedaInfinityFullyFaithful、YonedaRepresentableMapping
- (e) 関手版 Yoneda $`\mathrm{Map}(h_y,F)\simeq F(y)`　／　$`h_1` で $`\mathrm{Fun}_{/C^{\mathrm{op}}}((C_{/y})^{\mathrm{op}},\mathrm{Un}\,F)` に移し、fibration 版 Yoneda で $`\mathrm{id}_y` で評価　／　—

*f-c-spaces.html — 11. $`\mathrm{Map}` を関手にする：twisted arrow の straightening — 11.9 他の作り方との比較*

- 方法　／　内容　／　難点
- Tw の St（採用）　／　11.1〜11.7　／　一般の底の St が要る
- $`\mathfrak C[C]` の Hom（HTT 5.1.3）　／　$`\mathfrak C[C^{\mathrm{op}}\times C]\to\mathcal Kan` を $`\mathfrak C[C]` の Hom の Kan 化で作る　／　$`\mathfrak CC\simeq\mathrm{Hom}(x,y)` の比較にモデル構造を使う
- 矢の圏の両側 straightening　／　$`\mathrm{Fun}(\Delta^1,C)\to C\times C` を両側 fibration として扱う　／　二変数の straightening を別に用意する
- 関手にしない　／　前層を $`\mathrm{RFib}(C)` とし、$`h_y` を $`C_{/y}` のまま扱う（Cisinski、∞-cosmos）　／　関手として扱う場面で St が要る

流れ「fibration 版 Yoneda → St → Map → 関手版 Yoneda」の中で、$`\mathrm{Map}` の構成は 11.6・11.8 で fibration 版 Yoneda を、11.7 で St を使う中間の位置にある。

- 比較　／　鍵
- ファイバー ≃ $`\mathrm{Hom}^L`　／　行ごとの同値（スライスの頂点への制限）と対角補題
- 左 fibration　／　pairing による inner anodyne 性
- 始対象・表現可能 fibration との同値　／　崩壊写像と左 fibration のファイバーごとの判定
- 充満忠実性・関手版 Yoneda　／　$`h_1`、fibration 版 Yoneda、作用の照合

:::proposition "kerodon_8_1_2_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceIdentity_isInitialVertex") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_3_1_2_11, kerodon_4_4_2_6, kerodon_4_7_3_11, kerodon_8_1_1_15")
Kerodon Proposition 8.1.2.1（[Tag 03JW](https://kerodon.net/tag/03JW)）。対応表の状態：一部。

*主張*　無限圏 $`C` の同型 $`f:x\to y` は、始域射影の $`x` 上のファイバー $`\{x\}\times_{C^{\mathrm{op}}}\operatorname{Tw}(C)` の始対象である。

fを恒等辺id\_Xに限るとtwistedArrowSourceIdentity\_isInitialVertexは同じ始点fiber内のfの始対象性を直接返す。任意の可逆辺は含まない。

:::

:::corollary "kerodon_8_1_2_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft_trivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight_trivialKanFibration")
Kerodon Corollary 8.1.2.3（[Tag 048J](https://kerodon.net/tag/048J)）。対応表の状態：本体にある。

*主張*　Kan 複体 $`C` について、ねじれ矢印単体集合から $`C^{\mathrm{op}}` と $`C` への二つの射影はともに自明な Kan ファイブレーションである。

仮定：単体集合 C の KanComplex（Kerodon と一致）。結論：edgewiseLeft と edgewiseRight のそれぞれが TrivialKanFibration（原文の二射と一致）。

:::

:::corollary "kerodon_8_1_2_4" (uses := "kerodon_1_1_0_6, kerodon_1_1_4_12, kerodon_1_4_0_1, kerodon_4_7_3_23, kerodon_5_1_4_1, kerodon_6_3_5_1, kerodon_6_3_5_13, kerodon_6_3_5_14, kerodon_8_1_1_14, kerodon_8_1_2_1")
Kerodon Corollary 8.1.2.4（[Tag 048K](https://kerodon.net/tag/048K)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：標準単体の右半分への制限で target 射影を定める。辺の局所化の述語はあるが、この射影のすべての基底変換に局所化を与える型は見つからない。

:::

:::corollary "kerodon_8_1_2_5"
Kerodon Corollary 8.1.2.5（[Tag 048L](https://kerodon.net/tag/048L)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：標準 target 射影はある。終点固定の twisted arrow の再構成の同値は別の写像で、任意の C に対する Tw(C)→C の弱ホモトピー同値は見つからない。

:::

:::corollary "kerodon_8_1_2_6" (uses := "kerodon_1_1_0_6, kerodon_8_1_2_4")
Kerodon Corollary 8.1.2.6（[Tag 048M](https://kerodon.net/tag/048M)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：任意の f の edgewiseSubdivisionMap と、充満忠実な f の固定二端点 Hom の同値を確認した。全空間の Tw(f) の弱ホモトピー同値を f と比較する iff は見つからない。

:::

:::definition "kerodon_8_1_2_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceToTwistedArrowSource") (uses := "kerodon_1_1_0_6")
Kerodon Construction 8.1.2.7（[Tag 03JY](https://kerodon.net/tag/03JY)）。対応表の状態：一部。

*主張*　単体図式 $`f:K\to C` に対し、$`K^{\mathrm{op}}` の単体と $`C_{f/}` の単体の結合を余スライス縮約射 $`K\star C_{f/}\to C` に送ると、ねじれ矢印の単体が得られる。これを転置した $`C_{f/}\to\operatorname{Fun}_{/C^{\mathrm{op}}}(K^{\mathrm{op}},\operatorname{Tw}(C))` を余スライスの包含と呼び、点 $`x` では始域ファイバーへの射になる。

K=Δ⁰、fを頂点Xに限るとcosliceToTwistedArrowSourceは原文の同じι\_Xの構成を直接与える。一般のKの二変数Tの構成は含まない。

:::

:::proposition "kerodon_8_1_2_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceToTwistedArrowSource_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSource")
Kerodon Proposition 8.1.2.10（[Tag 03K0](https://kerodon.net/tag/03K0)）。対応表の状態：本体にある。

*主張*　無限圏 $`C` の任意の対象 $`x` で、余スライスの包含 $`C_{x/}\to\{x\}\times_{C^{\mathrm{op}}}\operatorname{Tw}(C)` は無限圏の同値である。

仮定：Quasicategory C と頂点 x（Kerodon と一致）。結論：cosliceToTwistedArrowSource x は x の coslice から Tw(C) の source ファイバーへの射で、IsQCatEquivalence（指定の包含の同値性と一致）。

:::

:::corollary "kerodon_8_1_2_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHomSpace, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceTwistedHomMap_isQCatEquivalence, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceTwistedHomMap_mono, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isSimplicialHomotopyEquivalence_iff_isQCatEquivalence")
Kerodon Corollary 8.1.2.11（[Tag 03K1](https://kerodon.net/tag/03K1)）。対応表の状態：本体にある。

*主張*　無限圏 $`C` の任意の二対象 $`x,y` に対し、余スライスの包含は、左の pinched 射空間からねじれ矢印の $`(x,y)` 上のファイバーへの Kan 複体のホモトピー同値を誘導する。

仮定：Quasicategory C と頂点 x,y。写像空間の Kan 性の下で圏同値とホモトピー同値を比較する（Kerodon と一致）。結論：cosliceTwistedHomMap の単射性と IsQCatEquivalence から、指定の二重ファイバーへの包含がホモトピー同値（原文と一致）。

:::

:::corollary "kerodon_8_1_2_12" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_1_4_3_1")
Kerodon Corollary 8.1.2.12（[Tag 03K2](https://kerodon.net/tag/03K2)）。対応表の状態：なし。

twistedArrowHomPinchedEquivalenceとcoslice比較の同型は候補だが、原文で指定された実際の二辺f,f′の成分とhCの類を同じ射で同定する型をまだ含まない。空間の同値だけをその指定比較のiffと数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceTwistedHomMap_isQCatEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_kanPinchedHomEdge_of_homMk_eq`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHomPinchedEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHomPinchedEquivalence_coslice`

:::

:::definition "kerodon_8_1_2_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHomSpace, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHomSpace_kanComplex") (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_6_5_10, kerodon_8_1_2_11")
Kerodon Notation 8.1.2.15（[Tag 03K5](https://kerodon.net/tag/03K5)）。対応表の状態：一部。

*主張*　無限圏の対象 $`x,y` の射空間と、ねじれ矢印の $`(x,y)` 上のファイバーには、左の pinched 射空間からホモトピー同値が入る。この二本から Kan 複体のホモトピー圏で両者の同型を得る。

twistedArrowHomSpaceとそのKan性は原文の右辺の同じ二重fiberを直接構成する。左向き・右向きの指定包含を反転して作るα\_X,Yそのものはこの引用に含まない。

:::

:::corollary "kerodon_8_1_2_16" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowFunctorComparison_isPrecompositionEquivalence, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.FullyFaithfulJointHom.twistedArrowHomInfinity_fullyFaithfulIso") (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_5_1_7_16, kerodon_8_1_1_11, kerodon_8_1_2_15")
Kerodon Corollary 8.1.2.16（[Tag 03LX](https://kerodon.net/tag/03LX)）。対応表の状態：一部。

*主張*　無限圏の関手 $`F:C\to D` が充満忠実であることは、ねじれ矢印圏とその底を $`F` で移す正方形 $`\operatorname{Tw}(C)\to\operatorname{Tw}(D)` 上 $`C^{\mathrm{op}}\times C\to D^{\mathrm{op}}\times D` が圏論的引き戻しであることと同値である。

twistedArrowFunctorComparison\_isPrecompositionEquivalenceは同じ四角のstrict pullbackへの比較が同値となる向き（充満忠実⇒categorical pullback）を直接与える。逆向きは含まない。

:::

:::corollary "kerodon_8_1_2_17" (uses := "kerodon_1_4_0_1, kerodon_4_5_3_22, kerodon_8_1_2_16")
Kerodon Corollary 8.1.2.17（[Tag 03K9](https://kerodon.net/tag/03K9)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：充満忠実な f に対し Tw(C) から Tw(D) の引き戻しへの前合成同値、および固定端点での同値はある。f が同値の場合の Tw(f) 全体の同値を直接述べた型は見つからない。

:::

:::corollary "kerodon_8_1_2_18"
Kerodon Corollary 8.1.2.18（[Tag 03Y6](https://kerodon.net/tag/03Y6)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：各次元の Tw の単体を edgewiseWeight からの写像とする定義はある。非可算 κ で C の本質的 κ-small 性から Tw(C) の本質的小性を導く型は見つからない。

:::

:::corollary "kerodon_8_1_2_19" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowIdentityHomTransport_isQCatEquivalence") (uses := "kerodon_1_4_0_1, kerodon_4_6_4_20, kerodon_4_6_8_13, kerodon_5_2_8_11, kerodon_8_1_2_10, kerodon_8_1_2_12, kerodon_8_1_2_15")
Kerodon Corollary 8.1.2.19（[Tag 03K6](https://kerodon.net/tag/03K6)）。対応表の状態：一部。

*主張*　無限圏 $`C` の豊穣化ホモトピー圏の Hom 関手 $`(hC)^{\mathrm{op}}\times hC\to h\operatorname{Kan}` は、ねじれ矢印の左ファイブレーションのホモトピー移送表現と自然同型である。各成分は 8.1.2.15 の同型である。

twistedArrowIdentityHomTransport\_isQCatEquivalenceは各x,yで同じTw fiberと左pinchedHomとの比較同値を直接返す。原文の二変数のhC上での自然性と指定αの全同定は含まない。

:::

:::corollary "kerodon_8_1_2_21" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceToTwistedArrowSource_isQCatEquivalence")
Kerodon Corollary 8.1.2.21（[Tag 06TQ](https://kerodon.net/tag/06TQ)）。対応表の状態：一部。

*主張*　無限圏 $`C` の図式 $`f:K\to C` の余スライスは、$`K^{\mathrm{op}}\to\operatorname{Tw}(C)` で始域を $`f^{\mathrm{op}}` に固定し、終域を定数図式に指定するファイバー積の無限圏と、余スライス包含を通じて同値である。

K=Δ⁰では原文の対象は始点Xを固定したTw fiberとなり、cosliceToTwistedArrowSource\_isQCatEquivalenceは同じcoslice包含ι\_Xの同値を直接返す。一般Kは含まない。

:::

:::corollary "kerodon_8_1_2_22" (uses := "kerodon_1_4_0_1, kerodon_8_1_2_7, kerodon_8_1_2_10")
Kerodon Corollary 8.1.2.22（[Tag 03KA](https://kerodon.net/tag/03KA)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対始頂点の Hom 比較条件と終点固定側のファイバー同型を確認した。与えた f が U-(co)cartesian であることを誘導ファイバー写像に関する相対始性で判定する iff は見つからない。

:::

:::corollary "kerodon_8_1_2_23" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceIdentity_isInitialVertex") (uses := "kerodon_1_4_0_1, kerodon_5_1_1_4, kerodon_8_1_2_22")
Kerodon Corollary 8.1.2.23（[Tag 03KB](https://kerodon.net/tag/03KB)）。対応表の状態：一部。

*主張*　無限圏の射 $`f:x\to y` が同型であることは、ねじれ矢印圏の始域射影の $`x` 上のファイバーで始対象であることと同値である。終域射影の $`y` 上のファイバーで始対象であることとも同値である。

fを恒等辺に限ればtwistedArrowSourceIdentity\_isInitialVertexは原文の(1)⇒(2)の同じ恒等頂点の結論を直接返す。(3)と任意の辺の逆向きは含まない。

:::

# 8.1.3 The Cospan Construction

%%%
number := false
tag := "kerodon-8-1-3"
%%%

Kerodon [Tag 00AY](https://kerodon.net/tag/00AY)

:::definition "kerodon_8_1_3_1"
Kerodon Construction 8.1.3.1（[Tag 03KN](https://kerodon.net/tag/03KN)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Tw 自体は Δ\[n\]ᵒᵖ ⋆ Δ\[n\] からの射で定義される。重みをさらに Tw(Δ\[n\]) に替えて各次数を組む Cospan(C) と、面・退化での前合成を与える宣言は見つからない。

:::

:::definition "kerodon_8_1_3_5" (uses := "kerodon_1_1_0_6")
Kerodon Construction 8.1.3.5（[Tag 03KT](https://kerodon.net/tag/03KT)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Tw の写像上の作用と一般の右 Kan 延長随伴の単位はある。σ を Tw(σ) に移して Cospan(Tw(D)) の単体にする写像は確認できない。

:::

:::proposition "kerodon_8_1_3_7" (uses := "kerodon_1_1_0_6, kerodon_8_1_1_4, kerodon_8_1_3_5")
Kerodon Proposition 8.1.3.7（[Tag 03KU](https://kerodon.net/tag/03KU)）。対応表の状態：なし。

ranAdjunctionは通常圏の前合成と右Kan拡張の随伴。原文のCospan自己関手・指定単位u・Tw上の射による同じ合成写像との比較を持たない。

宣言：`CategoryTheory.Functor.ranAdjunction`

:::

:::corollary "kerodon_8_1_3_8"
Kerodon Corollary 8.1.3.8（[Tag 03KV](https://kerodon.net/tag/03KV)）。対応表の状態：なし。

一般のranAdjunctionはTwをその前合成と同定せず、右随伴の値を原文のCospanと比較もしない。同じ自己関手の随伴の結論には直接適用できない。

宣言：`CategoryTheory.Functor.ranAdjunction`

:::

:::corollary "kerodon_8_1_3_10" (uses := "kerodon_1_1_0_6, kerodon_8_1_2_6, kerodon_8_1_3_7")
Kerodon Corollary 8.1.3.10（[Tag 048Q](https://kerodon.net/tag/048Q)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Tw(C)→Cᵒᵖ×C のホーン持ち上げを調べる型と前合成の一般の随伴はある。任意の Kan ファイブレーションを Cospan に適用した射で、Tw を施したホーンの持ち上げを解く型は見つからない。

:::

:::corollary "kerodon_8_1_3_11" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_8_1_3_10")
Kerodon Corollary 8.1.3.11（[Tag 048S](https://kerodon.net/tag/048S)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Tw(K) が Kan になるインスタンスはある。K が Kan のとき、右側の Cospan(K) のホーンを埋める型は見つからない。

:::

:::definition "kerodon_8_1_3_12"
Kerodon Construction 8.1.3.12（[Tag 00B4](https://kerodon.net/tag/00B4)）。対応表の状態：なし。

通常のSpanBicatの双対は原文のTw(D)からの指定Fを入力に取らず、同じF⁺の対象・射・合成制約を構成しない。

宣言：`CategoryTheory.Span.SpanBicat`、`CategoryTheory.Span.SpanBicat.instBicategory`

:::

:::theorem "kerodon_8_1_3_14"
Kerodon Theorem 8.1.3.14（[Tag 00B5](https://kerodon.net/tag/00B5)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Mathlib の双対の通常 span 双圏には pullback 合成がある。Tw(D)→C の関手と pushout 合成の cospan への strictly unital lax 関手を対応づける全単射は見つからない。

:::

:::corollary "kerodon_8_1_3_15"
Kerodon Corollary 8.1.3.15（[Tag 00B6](https://kerodon.net/tag/00B6)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常の span 双圏と単体豊穣圏の coherent nerve を確認した。pushout を持つ C の Cospan(N(C)) と cospan 双圏の Duskin nerve を全次数で結ぶ同型は見つからない。

:::

# 8.1.4 Cospans in ∞-Categories

%%%
number := false
tag := "kerodon-8-1-4"
%%%

Kerodon [Tag 03L4](https://kerodon.net/tag/03L4)

:::proposition "kerodon_8_1_4_1"
Kerodon Proposition 8.1.4.1（[Tag 03L5](https://kerodon.net/tag/03L5)）。対応表の状態：なし。

通常圏のspan双圏の構造は原文のCospan(C)という単体集合の∞-bicategory性を結論しない。両者のcoherent nerveと薄い2面の比較がない。

宣言：`CategoryTheory.Span.SpanBicat.instBicategory`

:::

:::proposition "kerodon_8_1_4_2" (uses := "kerodon_1_4_0_1, kerodon_2_3_2_3")
Kerodon Proposition 8.1.4.2（[Tag 03L6](https://kerodon.net/tag/03L6)）。対応表の状態：なし。

IsPushoutDiagramVertexは四角のpushout性の述語。原文のCospanの2単体とTw(Δ²)図式、そのthin条件と同定する型を持たない。

宣言：`SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsPushoutDiagramVertex`

:::

:::corollary "kerodon_8_1_4_3" (uses := "kerodon_1_4_0_1, kerodon_7_6_2_39, kerodon_8_1_4_2")
Kerodon Corollary 8.1.4.3（[Tag 03L8](https://kerodon.net/tag/03L8)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常 span の単位子は退化した合成の候補になる。任意の準圏の Cospan で s₀ または s₁ の像の内側の四角形を pushout と判定する型は見つからない。

:::

:::lemma_ "kerodon_8_1_4_4" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_3_6_14, kerodon_7_2_1_3, kerodon_7_2_3_7")
Kerodon Lemma 8.1.4.4（[Tag 048T](https://kerodon.net/tag/048T)）。対応表の状態：なし。

exists\_relative\_pushoutFamilyはspanから普遍余錐を作る。原文の指定Λ²₁→Cospanから同じTw(Δ²)図式を復元する型がなく、thinな延長とは結論していない。

宣言：`SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_relative_pushoutFamily`

:::

:::lemma_ "kerodon_8_1_4_6" (uses := "kerodon_1_1_0_6, kerodon_3_1_2_11, kerodon_5_1_1_1, kerodon_8_1_3_7")
Kerodon Lemma 8.1.4.6（[Tag 048V](https://kerodon.net/tag/048V)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Tw の射影のホーン条件とその標準拡張領域の内 anodyne 性を調べた。任意の U で指定した二辺が U-cocartesian と U-cartesian のとき、Tw(Λⁿ₀) 上の相対延長を与える型は見つからない。

:::

:::lemma_ "kerodon_8_1_4_7" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Lemma 8.1.4.7（[Tag 03LC](https://kerodon.net/tag/03LC)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一つの可逆辺の cocartesian ホーン条件と Tw 射影の充填はある。Tw(Λⁿ₀) 図式の二つの指定辺の可逆性から、Tw(Δⁿ) まで図式を延長する型は見つからない。

:::

:::corollary "kerodon_8_1_4_8"
Kerodon Corollary 8.1.4.8（[Tag 03LD](https://kerodon.net/tag/03LD)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：押し出し頂点の述語と全小余極限保存の定義はある。Cospan(F) の薄い単体保存と元の F の pushout 保存を往復する型は見つからない。

:::

# 8.1.5 Thin 2-Simplices of Cospan(C)

%%%
number := false
tag := "kerodon-8-1-5"
%%%

Kerodon [Tag 03LE](https://kerodon.net/tag/03LE)

:::lemma_ "kerodon_8_1_5_1"
Kerodon Lemma 8.1.5.1（[Tag 03LF](https://kerodon.net/tag/03LF)）。対応表の状態：なし。

四角とspan余錐の比較は、原文のTw(Δ²)全図式の同じφの余極限性を結論しない。残りの頂点を含む形状比較が不足。

宣言：`SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pushoutDiagramsCoconesIso`

:::

:::lemma_ "kerodon_8_1_5_2"
Kerodon Lemma 8.1.5.2（[Tag 03LG](https://kerodon.net/tag/03LG)）。対応表の状態：なし。

pushoutDiagramsCoconesIsoは原文の全Tw(Δ²)図式の余極限性を入力としない。指定内部四角のthin条件への制限の比較がない。

宣言：`SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pushoutDiagramsCoconesIso`

:::

# 8.1.6 Restricted Cospans

%%%
number := false
tag := "kerodon-8-1-6"
%%%

Kerodon [Tag 048Z](https://kerodon.net/tag/048Z)

:::definition "kerodon_8_1_6_1" (uses := "kerodon_1_1_0_6")
Kerodon Definition 8.1.6.1（[Tag 0490](https://kerodon.net/tag/0490)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常の span の両脚には個別の射の性質を課せる。すべての 0≤i≤j≤n の二脚を検査して Cospan の n 単体を切り出す部分単体集合は見つからない。

:::

:::definition "kerodon_8_1_6_5" (uses := "kerodon_1_4_0_1")
Kerodon Definition 8.1.6.5（[Tag 0494](https://kerodon.net/tag/0494)）。対応表の状態：なし。

SpanBicatの通常圏のpullback安定性の入力は、原文の∞圏でL,Rに沿う指定pushoutの存在と両脚の所属条件への比較を欠く。

宣言：`CategoryTheory.Span.SpanBicat`

:::

:::proposition "kerodon_8_1_6_7" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_4_1_1, kerodon_8_1_4_2, kerodon_8_1_4_3, kerodon_8_1_4_4, kerodon_8_1_4_7, kerodon_8_1_6_5")
Kerodon Proposition 8.1.6.7（[Tag 0496](https://kerodon.net/tag/0496)）。対応表の状態：なし。

通常のspan双圏は原文のCospan\^\{L,R\}(C)の同じ単体集合と薄い面を比較する型を持たず、∞-bicategoryという結論に直接適用できない。

宣言：`CategoryTheory.Span.SpanBicat.instBicategory`

:::

:::corollary "kerodon_8_1_6_8" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_4_7_9, kerodon_8_1_4_2, kerodon_8_1_6_7, kerodon_8_3_3_17")
Kerodon Corollary 8.1.6.8（[Tag 0498](https://kerodon.net/tag/0498)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：押し出し頂点と脚を制限した通常 span の宣言はある。Cospan の部分単体集合と全体で同じ指定 2 単体の薄さを比較する iff は見つからない。

:::

:::corollary "kerodon_8_1_6_10" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_3_5_4, kerodon_1_4_0_1, kerodon_1_4_6_10, kerodon_4_4_3_11, kerodon_5_4_6_5, kerodon_5_4_6_6, kerodon_7_6_2_39, kerodon_8_1_3_11, kerodon_8_1_6_8")
Kerodon Corollary 8.1.6.10（[Tag 049B](https://kerodon.net/tag/049B)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Mathlib で apexIso を作る入力は同じ二端点の span 間の可逆な 2 射。準圏の cospan 自体が可逆な 1 射であることを両脚の可逆性で判定する型は見つからない。

:::

:::corollary "kerodon_8_1_6_12" (uses := "kerodon_1_4_0_1")
Kerodon Corollary 8.1.6.12（[Tag 049D](https://kerodon.net/tag/049D)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常 span の固定両端点での 2 同型の構成はある。制限付き Cospan の二対象の同型を元の準圏内の同型に反映し、逆に同型から両脚の条件を得る型は見つからない。

:::

# 8.1.7 Comparing C with Cospan(C)

%%%
number := false
tag := "kerodon-8-1-7"
%%%

Kerodon [Tag 049E](https://kerodon.net/tag/049E)

:::definition "kerodon_8_1_7_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight") (uses := "kerodon_1_1_0_6, kerodon_8_1_1_6, kerodon_8_1_3_7")
Kerodon Construction 8.1.7.1（[Tag 049F](https://kerodon.net/tag/049F)）。対応表の状態：一部。

*主張*　単体集合のねじれ矢印の終域射影は、単体写像の随伴表示によって $`C\to\operatorname{Cospan}(C)` を定める。可換図式の一方の脚に元の射、他方に恒等射を置く単射である。

edgewiseRightは原文の転置前の同じλ₊の構成を直接与える。C→Cospan(C)のρ₊、次数ごとの表示とそのmono性は含まない。

:::

:::definition "kerodon_8_1_7_2"
Kerodon Construction 8.1.7.2（[Tag 049G](https://kerodon.net/tag/049G)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：片脚の射の性質を指定する通常 span と頂点で絞る部分複体はある。各次数で全左向き辺が可逆である cospan 図式だけを取る部分単体集合は見つからない。

:::

:::definition "kerodon_8_1_7_4" (uses := "kerodon_1_1_0_6, kerodon_8_1_6_1")
Kerodon Variant 8.1.7.4（[Tag 049J](https://kerodon.net/tag/049J)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常 span の二脚にはそれぞれ制約を付けられる。単体集合の二つの片側制限 Cospan\^\{L,all\} と Cospan\^\{all,R\} の共通部分が両側制限と等しい型は見つからない。

:::

:::proposition "kerodon_8_1_7_5" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_4_5_9, kerodon_7_6_2_39, kerodon_8_1_4_2, kerodon_8_1_4_4")
Kerodon Proposition 8.1.7.5（[Tag 049K](https://kerodon.net/tag/049K)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常 span の脚を射の性質で制限した双圏はある。右脚に可逆性を課した Cospan の内ホーンを埋める型は見つからない。

:::

:::proposition "kerodon_8_1_7_6" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_6_3_1_1, kerodon_6_3_1_9, kerodon_6_3_5_5, kerodon_8_1_2_4, kerodon_8_1_7_1, kerodon_8_1_7_9, kerodon_8_1_7_13")
Kerodon Proposition 8.1.7.6（[Tag 049L](https://kerodon.net/tag/049L)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：標的射影と Tw の Kan 性はある。右脚が可逆な Cospan へ移した ρ₊ の充満忠実性と本質的全射性は確認できない。

:::

:::definition "kerodon_8_1_7_8"
Kerodon Definition 8.1.7.8（[Tag 049N](https://kerodon.net/tag/049N)）。対応表の状態：なし。

HasOfPostcompPropertyは通常圏の射の性質。原文の単体集合の各指定2単体とその三辺の集合Wへの所属のiffと比較する型がない。

宣言：`CategoryTheory.MorphismProperty.HasOfPostcompProperty`

:::

:::lemma_ "kerodon_8_1_7_9" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_8_1_2_1")
Kerodon Lemma 8.1.7.9（[Tag 049P](https://kerodon.net/tag/049P)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏の後合成での消去性と Tw の二射影はある。二射影の各ファイバーで F が指定の辺の族を保つ条件を、転置 f の制限付き Cospan 経由と結ぶ iff は見つからない。

:::

:::lemma_ "kerodon_8_1_7_12" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_8_1_7_4")
Kerodon Lemma 8.1.7.12（[Tag 049T](https://kerodon.net/tag/049T)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常圏での前合成の随伴と相対関手空間を調べた。内部 Hom の比較同型を L'・R' の射の条件と両脚制限の両側に制限する型は見つからない。

:::

:::lemma_ "kerodon_8_1_7_13" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_8_1_6_12, kerodon_8_1_7_12")
Kerodon Lemma 8.1.7.13（[Tag 049U](https://kerodon.net/tag/049U)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：元の Tw の関手性と標的射影はある。右脚可逆の Cospan への二図式が関手圏で同型であることを、それぞれの Tw(D) 上の転置の同型に移す iff は見つからない。

:::

:::definition "kerodon_8_1_7_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Variant 8.1.7.14（[Tag 049V](https://kerodon.net/tag/049V)）。対応表の状態：一部。

*主張*　ねじれ矢印の始域射影は、単体写像の随伴表示によって $`C^{\mathrm{op}}\to\operatorname{Cospan}(C)` を定める。$`C` が無限圏ならこれは、左脚を同型、右脚を任意とする余スパンの単体部分集合への同値である。

edgewiseLeftは原文の転置前の同じλ₋を直接構成する。ρ₋とCospanの指定部分複体への同値までは含まない。

:::

# 8.1.8 Morphisms in the Duskin Nerve

%%%
number := false
tag := "kerodon-8-1-8"
%%%

Kerodon [Tag 03KZ](https://kerodon.net/tag/03KZ)

:::definition "kerodon_8_1_8_2"
Kerodon Construction 8.1.8.2（[Tag 01G9](https://kerodon.net/tag/01G9)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常双圏の lax 関手のデータはある。Tw(A)→Hom\_C(X,Y) から、両端で定値となる \[1\]×A 上の lax 関手を、Tw の射から合成制約も含めて作る型は見つからない。

:::

:::theorem "kerodon_8_1_8_4"
Kerodon Theorem 8.1.8.4（[Tag 01GB](https://kerodon.net/tag/01GB)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：lax 関手と通常の随伴による Hom 全単射はある。F↦U\_F の単射性と、その像が両端定値の strictly unital lax 関手からなるという型は見つからない。

:::

:::corollary "kerodon_8_1_8_6"
Kerodon Corollary 8.1.8.6（[Tag 01GC](https://kerodon.net/tag/01GC)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単体豊穣圏の nerve と lax 関手の構造はある。双圏の Duskin nerve の Hom と Cospan(N(Hom\_C(X,Y))) の同型を全次数で与える型は見つからない。

:::

# 8.1.9 Cospan Fibrations

%%%
number := false
tag := "kerodon-8-1-9"
%%%

Kerodon [Tag 049W](https://kerodon.net/tag/049W)

:::proposition "kerodon_8_1_9_1"
Kerodon Proposition 8.1.9.1（[Tag 049X](https://kerodon.net/tag/049X)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：E 内の一辺の cocartesian ホーン条件と Tw 射影の持ち上げはある。U-cocartesian な右脚で制限した Cospan(E)→Cospan(C) が内ファイブレーションである型は見つからない。

:::

:::definition "kerodon_8_1_9_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.CocartesianEdgeLift, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianFibrations") (uses := "kerodon_1_1_0_6, kerodon_5_1_1_1")
Kerodon Definition 8.1.9.5（[Tag 04A0](https://kerodon.net/tag/04A0)）。対応表の状態：一部。

*主張*　単体集合の内部ファイブレーション $`U:E\to C` で底の辺がデカルト持ち上げを許すとは、その終点上の任意の頂点を終点とする $`U`-デカルト辺に持ち上がることである。余デカルト持ち上げでは底の始点上の任意の頂点を始点とする。

各始点xについてNonempty(CocartesianEdgeLift U e x)を量化すれば、原文のeがU-cocartesian liftsを持つという定義を直接表す。専用名の欠如は不足としないがcartesian側はこの構造に含まない。

:::

:::proposition "kerodon_8_1_9_9" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_2_4, kerodon_7_1_6_11, kerodon_7_6_2_38, kerodon_8_1_3_7, kerodon_8_1_4_2")
Kerodon Proposition 8.1.9.9（[Tag 04A4](https://kerodon.net/tag/04A4)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一つの辺の cocartesian 持ち上げのデータはある。R に属する辺だけへの持ち上げを仮定し、二つの Cospan 部分単体集合間で全内ホーンを解く型は見つからない。

:::

:::proposition "kerodon_8_1_9_10" (uses := "kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_7_1_6_12, kerodon_7_6_2_38")
Kerodon Proposition 8.1.9.10（[Tag 04A7](https://kerodon.net/tag/04A7)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：相対的な押し出し図式の構成と、基底変更での cocartesian 辺の扱いはある。L の逆像と R の cocartesian 持ち上げが全空間で pushout-compatible になる型は見つからない。

:::

# 8.1.10 Beck-Chevalley Fibrations

%%%
number := false
tag := "kerodon-8-1-10"
%%%

Kerodon [Tag 04AB](https://kerodon.net/tag/04AB)

:::definition "kerodon_8_1_10_1"
Kerodon Definition 8.1.10.1（[Tag 04AC](https://kerodon.net/tag/04AC)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：個別の (co)cartesian 辺の判定と pushout 述語はある。基底の pushout に乗る四角形について、指定の二辺を仮定し残り二辺の (co)cartesian 性を同値にする公理を含むファイブレーションの型は見つからない。

:::

:::theorem "kerodon_8_1_10_3"
Kerodon Theorem 8.1.10.3（[Tag 04AE](https://kerodon.net/tag/04AE)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Mathlib の Pith は通常双圏の 2 射を可逆なものに絞る。準圏の Cospan の Pith 間の射が cartesian で、指定した二脚の性質で cartesian 辺を判定する型は見つからない。

:::

:::corollary "kerodon_8_1_10_5"
Kerodon Corollary 8.1.10.5（[Tag 04AG](https://kerodon.net/tag/04AG)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常双圏の Pith と cocartesian 辺の個別判定はある。両脚を U-(co)cartesian に制限した Cospan の ∞-双圏性と、その Pith の右ファイブレーションは見つからない。

:::

:::definition "kerodon_8_1_10_6" (uses := "kerodon_1_4_0_1, kerodon_8_1_6_5, kerodon_8_1_9_5")
Kerodon Definition 8.1.10.6（[Tag 04AH](https://kerodon.net/tag/04AH)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：辺ごとの cocartesian 持ち上げと pushout 述語はある。L と R だけへの別々の持ち上げを要求し、その二クラスに属する辺の pushout に混合条件を課す相対述語は見つからない。

:::

:::theorem "kerodon_8_1_10_9" (uses := "kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_2_4, kerodon_5_1_2_5, kerodon_5_1_4_1, kerodon_7_6_2_39, kerodon_8_1_4_6, kerodon_8_1_6_10, kerodon_8_1_9_10, kerodon_8_1_10_6")
Kerodon Theorem 8.1.10.9（[Tag 04AL](https://kerodon.net/tag/04AL)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常双圏の Pith と一辺の持ち上げはある。持ち上げた L・R による Cospan の Pith 間で、cartesian ファイブレーションの構成と cartesian 辺の両脚判定は見つからない。

:::

:::corollary "kerodon_8_1_10_12"
Kerodon Corollary 8.1.10.12（[Tag 04AQ](https://kerodon.net/tag/04AQ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：通常双圏の Pith と span 双圏はある。両脚を (co)cartesian に制限した全空間の高次双圏性、Pith 上の右ファイブレーション、底が準圏の場合の Cospan 自体の右ファイブレーションの三結論は見つからない。

:::

