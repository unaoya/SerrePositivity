import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.FiberedCategory.Cartesian
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
import Mathlib.Combinatorics.Quiver.Covering
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanIntervalEvaluation
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.CostructuredArrowCofinality
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.F1BFibrationsRightAnodyneTensor
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.FirstVertexLeftAnodyne
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.JoinCells
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftAnodyneFactorization
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftAnodynePushoutProduct
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibrationInternalHom
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftPath
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightAnodyneFactorization
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "4.2 Left and Right Fibrations" =>
%%%
number := false
tag := "kerodon-4-2"
%%%

Kerodon の 4.2 節（[Tag 014H](https://kerodon.net/tag/014H)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

# 4.2.1 Left and Right Fibrations of Simplicial Sets

%%%
number := false
tag := "kerodon-4-2-1"
%%%

Kerodon [Tag 01GT](https://kerodon.net/tag/01GT)

*定義 6.2 （頂点上のファイバー）*

単体的集合 $`B` の頂点とは $`B([0])` の元のことであり、米田の補題により射 $`\Delta^0\to B` と同一視する。単体的集合の射 $`q\colon E\to B` と頂点 $`b\colon\Delta^0\to B` について、ファイバー積（定義 6.1）

$$`E_b=E\times_B\Delta^0`

を $`q` の $`b` 上のファイバーという。

*注意 （ファイバーの具体形）*

$`\Delta^0` は各段が一点なので、$`c_m\colon[m]\to[0]` を唯一の射として、$`E_b` は $`E` の部分単体的集合

$$`E_b([m])=\{e\in E([m])\mid q(e)=B(c_m)(b)\}`

と同一視できる。

:::definition "kerodon_4_2_1_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations")
Kerodon Definition 4.2.1.1（[Tag 00T9](https://kerodon.net/tag/00T9)）。対応表の状態：本体にある。

仮定：単体集合間の任意の射 f（Kerodon と一致）。結論：LeftFibration は 0≤i\<n、RightFibration は 0\<i≤n のホーンに対する右持ち上げ性（一致）。

*定義 5.3 （fibration）*

- 名前　／　包含
- 左 fibration　／　$`\Lambda^n_i\subseteq\Delta^n`（$`0\le i<n`）

- 名前　／　包含
- 右 fibration　／　$`\Lambda^n_i\subseteq\Delta^n`（$`0<i\le n`）

:::

# 4.2.2 Fibrations in Groupoids

%%%
number := false
tag := "kerodon-4-2-2"
%%%

Kerodon [Tag 0156](https://kerodon.net/tag/0156)

:::definition "kerodon_4_2_2_1" (lean := "CategoryTheory.Functor.IsFibered, CategoryTheory.Functor.IsStronglyCartesian")
Kerodon Definition 4.2.2.1（[Tag 0157](https://kerodon.net/tag/0157)）。対応表の状態：一部。

IsFibered の cartesian lift の存在から原文(A)の任意の底の射の持ち上げが直接得られる。全ての射についてのHomのpullback条件(B)は含まない。

:::

:::definition "kerodon_4_2_2_4"
Kerodon Variant 4.2.2.4（[Tag 015A](https://kerodon.net/tag/015A)）。対応表の状態：なし。

IsStronglyCocartesian は選んだ一つの射についての普遍性。原文の任意の底の射の持ち上げの存在も、全ての射に対するpullback条件もこの型だけでは返さない。

宣言：`CategoryTheory.Functor.IsStronglyCocartesian`

:::

:::proposition "kerodon_4_2_2_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.costructuredArrowProjection_rightFibration")
Kerodon Proposition 4.2.2.9（[Tag 015H](https://kerodon.net/tag/015H)）。対応表の状態：一部。

costructuredArrowProjection\_rightFibration は U=CostructuredArrow.proj Q V の同じ nerveMap U の right fibration 性を直接返す。このUでの右側の結論だけで、一般のiffやopfibration側は含まない。

:::

# 4.2.3 Left and Right Covering Maps

%%%
number := false
tag := "kerodon-4-2-3"
%%%

Kerodon [Tag 022K](https://kerodon.net/tag/022K)

:::definition "kerodon_4_2_3_1" (lean := "Prefunctor.IsCovering, Prefunctor.star")
Kerodon Definition 4.2.3.1（[Tag 01QH](https://kerodon.net/tag/01QH)）。対応表の状態：一部。

Prefunctor.IsCovering は star と costar の全単射で、関手の基礎quiverについて仮定すると原文の左・右の一意持ち上げを直接得る。片側だけでよい原文より強い。

:::

:::proposition "kerodon_4_2_3_7"
Kerodon Proposition 4.2.3.7（[Tag 01RS](https://kerodon.net/tag/01RS)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：離散ファイバーの場合・全ホーンの一意性・1圏の圏 of elementsを照合。一意な通常圏の辺の持ち上げと離散ファイバーの判定。Quiver の star/costar はファイバー圏の離散性を参照しない。

:::

:::definition "kerodon_4_2_3_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration")
Kerodon Definition 4.2.3.8（[Tag 022N](https://kerodon.net/tag/022N)）。対応表の状態：一部。

LeftFibration/RightFibration は原文と同じホーン族について持ち上げの存在部分を直接表す。一意性を要求するcoveringの条件は含まない。

:::

:::proposition "kerodon_4_2_3_16"
Kerodon Proposition 4.2.3.16（[Tag 022W](https://kerodon.net/tag/022W)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：離散ファイバーの場合・全ホーンの一意性・1圏の圏 of elementsを照合。nerve を底とする左・右被覆と通常圏の被覆関手の両方向の比較。Quiver の被覆には nerve の比較がない。

:::

:::corollary "kerodon_4_2_3_18"
Kerodon Corollary 4.2.3.18（[Tag 022Y](https://kerodon.net/tag/022Y)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：離散ファイバーの場合・全ホーンの一意性・1圏の圏 of elementsを照合。左被覆を各標準単体への底変換における通常圏の左被覆で判定する iff。ホーンの持ち上げの底変換は一意性を扱わない。

:::

:::proposition "kerodon_4_2_3_19"
Kerodon Proposition 4.2.3.19（[Tag 022Z](https://kerodon.net/tag/022Z)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：離散ファイバーの場合・全ホーンの一意性・1圏の圏 of elementsを照合。左または右の一意ホーン充填と頂点全単射から同型を得る iff。頂点全射な充満忠実射の結論は圏同値。

:::

:::corollary "kerodon_4_2_3_20"
Kerodon Corollary 4.2.3.20（[Tag 0230](https://kerodon.net/tag/0230)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：離散ファイバーの場合・全ホーンの一意性・1圏の圏 of elementsを照合。左／右の一意ホーン充填と Kan fibration の組で被覆を判定する iff。LeftFibration と Kan fibration の型は一意性を含まない。

:::

# 4.2.4 Left Anodyne and Right Anodyne Morphisms

%%%
number := false
tag := "kerodon-4-2-4"
%%%

Kerodon [Tag 014S](https://kerodon.net/tag/014S)

:::definition "kerodon_4_2_4_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions_horn")
Kerodon Definition 4.2.4.1（[Tag 014T](https://kerodon.net/tag/014T)）。対応表の状態：一部。

leftAnodyneExtensions は指定生成ホーンの所属と弱飽和の各閉性を直接持つ。原文の最小性との同定は含まない。

:::

:::definition "kerodon_4_2_4_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions_horn")
Kerodon Variant 4.2.4.2（[Tag 014U](https://kerodon.net/tag/014U)）。対応表の状態：一部。

rightAnodyneExtensions は指定生成ホーンの所属と弱飽和の各閉性を直接持つ。最小弱飽和閉包との逆包含は含まない。

:::

:::proposition "kerodon_4_2_4_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions, CategoryTheory.MorphismProperty.rlp_llp_rlp")
Kerodon Proposition 4.2.4.5（[Tag 014X](https://kerodon.net/tag/014X)）。対応表の状態：本体にある。

仮定：任意の単体集合の射 q、左右それぞれのホーン族に一般等式を適用（Kerodon と一致）。結論：(T.rlp.llp).rlp = T.rlp により、左右それぞれで対応するアノダイン族に対する右持ち上げ性とホーンによる定義が同値（一致）。

:::

:::proposition "kerodon_4_2_4_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.exists_leftAnodyne_leftFibration_factorization")
Kerodon Proposition 4.2.4.7（[Tag 014Z](https://kerodon.net/tag/014Z)）。対応表の状態：一部。

exists\_leftAnodyne\_leftFibration\_factorization は同じ f の指定分解の存在を直接返す。関手性とfiltered colimit保存は含まない。

:::

:::definition "kerodon_4_2_4_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.exists_rightAnodyne_rightFibration_factorization")
Kerodon Variant 4.2.4.8（[Tag 0150](https://kerodon.net/tag/0150)）。対応表の状態：一部。

exists\_rightAnodyne\_rightFibration\_factorization は同じ f の指定分解の存在を直接返す。関手性とfiltered colimit保存は含まない。

:::

:::corollary "kerodon_4_2_4_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions")
Kerodon Corollary 4.2.4.9（[Tag 0151](https://kerodon.net/tag/0151)）。対応表の状態：本体にある。

仮定：任意の単体集合の射 i（Kerodon と一致）。結論：左右のアノダイン族はいずれも対応するファイブレーション族に対する左持ち上げ性で定義（一致）。

:::

:::proposition "kerodon_4_2_4_10"
Kerodon Proposition 4.2.4.10（[Tag 05HW](https://kerodon.net/tag/05HW)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：ホーン生成・単体ごとの分解・反対と通常モデル圏を照合。第0頂点から Λⁿⱼ へ低次元の左ホーンを一枚ずつ付ける有限フィルトレーション。標準単体への包含の補題は終域が Δⁿ。

:::

:::corollary "kerodon_4_2_4_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.stdSimplex_firstVertex_leftAnodyne")
Kerodon Corollary 4.2.4.11（[Tag 05HX](https://kerodon.net/tag/05HX)）。対応表の状態：本体にある。

仮定：任意の自然数 n（Kerodon と一致）。結論：標準 n 単体の第0頂点の Yoneda で表した包含が左アノダイン（一致）。

:::

:::corollary "kerodon_4_2_4_12"
Kerodon Corollary 4.2.4.12（[Tag 0231](https://kerodon.net/tag/0231)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：ホーン生成・単体ごとの分解・反対と通常モデル圏を照合。左アノダインに対する一意な持ち上げと次数ごとの集合の引き戻しとの同値。rlp の既存等式は存在しか扱わない。

:::

# 4.2.5 Exponentiation for Left and Right Fibrations

%%%
number := false
tag := "kerodon-4-2-5"
%%%

Kerodon [Tag 0152](https://kerodon.net/tag/0152)

*定義 10.2 （恒等頂点での評価）*

単体的集合の射 $`q\colon E\to B` と頂点 $`b` について、$`B_{b/}` を射影 $`B_{b/}\to B`（定義 4.7）で $`B` 上の単体的集合とみる。射

$$`\mathrm{ev}\colon\mathrm{Fun}_{/B}(B_{b/},E)\to E_b`

を、$`n` 単体 $`f\colon B_{b/}\times\Delta^n\to E` を $`f\circ(\mathrm{id}_b\times\mathrm{id}_{\Delta^n})\colon\Delta^0\times\Delta^n\cong\Delta^n\to E` に送ることで定める（$`\mathrm{id}_b` は定義 4.6、$`E_b` は定義 6.2）。$`q\circ f` は $`B_{b/}\to B` を経由するので、像は $`b` の上にある。スライス $`B_{/b}` についても同様に $`\mathrm{ev}\colon\mathrm{Fun}_{/B}(B_{/b},E)\to E_b` を定める。

*定理 10.3 （fibration 版 Yoneda）*

$`B` を単体的集合、$`b` をその頂点、$`q\colon E\to B` を射とする。

- $`q` が左 fibration（定義 5.3）なら、$`\mathrm{ev}\colon\mathrm{Fun}_{/B}(B_{b/},E)\to E_b`（定義 10.2）は trivial Kan fibration である。

- $`q` が右 fibration なら、$`\mathrm{ev}\colon\mathrm{Fun}_{/B}(B_{/b},E)\to E_b` は trivial Kan fibration である。

*注意 （大きさ）*

$`\mathrm{Fun}_{/S}(K,X)` は $`K`、$`X`、$`S` の大きさを問わず単体的集合であり、$`K` と $`X` が小さければ小さい。定理 10.3 で $`B` は quasicategory でなくてよい。

*f-b-literature-yoneda.html — 6. Yoneda の補題 — 6.3 証明の部品*

始対象 $`x` について $`\{x\}\hookrightarrow X` は left anodyne。一般には「単射が left anodyne ⇔ left cofinal」（Kerodon 7.2）から出る（始対象への包含はスライスがすべて可縮なので left cofinal）。$`B_{b/}` なら、$`\{\mathrm{id}_b\}` から先頭が $`\mathrm{id}_b` につながる left horn の充填で単体を一つずつ付け加えて全体が得られる。

*f-b-literature-yoneda.html — 7. 部品 A・B の詳しい証明 — 7.2 部品 B：始対象の包含は left anodyne（retract による証明）*

1. *切断*：$`X_{x/}\to X` は trivial fibration なので、$`\{x\}\hookrightarrow X` と $`\mathrm{id}_x` の持ち上げ問題から切断 $`s\colon X\to X_{x/}`、$`s(x)=\mathrm{id}_x` が得られる。

2. *join へ*：$`s` は $`\tilde s\colon\Delta^0\star X\to X`（錐の頂点を $`x` に、$`X` 上は恒等）と同じ。

3. *直積へ*：fat join から join へのつぶす写像 $`c\colon\Delta^1\times X\to\Delta^0\star X`（$`\{0\}\times X` を錐の頂点に）と合成して $`h=\tilde s\circ c\colon\Delta^1\times X\to X`。$`h|_{\{1\}\times X}=\mathrm{id}`、$`h|_{\{0\}\times X}` と $`h|_{\Delta^1\times\{x\}}` は $`x` で定数（後者は $`s_0(x)` の退化単体が退化単体に行くため）。定数関手 $`x` から $`\mathrm{id}_X` への自然変換。

4. *retract*：$`j\colon(\{0\}\times X)\cup(\Delta^1\times\{x\})\hookrightarrow\Delta^1\times X` は $`\{0\}\subseteq\Delta^1`（left horn）と単射の pushout-product なので left anodyne（HTT 2.1.2.7）。$`\iota_1\colon X\to\Delta^1\times X` と $`h` が、$`i\colon\{x\}\hookrightarrow X` を $`j` の retract にする（$`h\circ\iota_1=\mathrm{id}`、$`h` は $`j` の始域を $`\{x\}` に送る）。left anodyne は retract で閉じるので $`i` は left anodyne。

逆に、包含が left anodyne なら $`x` は始対象で、両者は同値。ただし逆向きは直接の議論ではなく、left anodyne ⇒ left cofinal と Quillen の定理 A を経由する（§10.5）。トポロジーで言えば、$`h` は点への向きつきの変形レトラクト。

*f-b-literature-yoneda.html — 7. 部品 A・B の詳しい証明 — 7.3 他の証明*

- 方法　／　適用範囲　／　使うもの　／　選択　／　部品 A
- 1. 持ち上げで切断を選ぶ（7.2）　／　一般の始対象　／　trivial fibration、fat join→join、pushout-product、retract　／　あり　／　必要
- 2. 余分な退化写像　／　スライス $`B_{b/}`　／　$`s(\sigma)=s_0\sigma`（$`d_0s_0\sigma=\sigma`、最初の辺は $`s_0(b)=\mathrm{id}_b`、単体的作用素と可換）。残りは 7.2 と同じ　／　なし　／　不要（系として出る）
- 3. cofinality　／　一般の始対象　／　単射が left anodyne ⇔ left cofinal（covariant 同値の理論。HTT では covariant モデル構造）　／　—　／　必要

参考：任意の $`K` について錐の頂点の包含 $`\{\ast\}\hookrightarrow\Delta^0\star K` は left anodyne（骨格の帰納法。鍵は $`\Delta^0\star\partial\Delta^n=\Lambda^{n+1}_0`）。ただし $`B_{b/}` は一般に錐ではないので直接は使えない。fibration 版 Yoneda に要るのはスライスの場合だけなので、形式化には方法 2 が向く。

*f-b-literature-yoneda.html — 7. 部品 A・B の詳しい証明 — 7.4 持ち上げ性質による証明*

単射が left anodyne ⇔ すべての左 fibration に対して左持ち上げ性質を持つ（small object argument と retract。モデル圏は使わない）。したがって、左 fibration $`p\colon E\to S`、$`e\colon\{x\}\to E`、$`g\colon X\to S` に対して持ち上げ $`X\to E` を作ればよい。

1. *底の取り替え*：$`E'=X\times_SE\to X` は左 fibration。必要なのは切断 $`\tau\colon X\to E'` で $`\tau(x)=e'` のもの。fibration 版 Yoneda の逆写像の存在そのもの。

2. *縮約*：7.2 の $`h`（$`B_{b/}` なら $`s_0` で具体的に）。

3. *引き戻して持ち上げ*：$`h^*E'\to\Delta^1\times X` は左 fibration。$`A=(\{0\}\times X)\cup(\Delta^1\times\{x\})` 上では $`h` が $`x` で定数なので、切断を $`e'` で定数と定める。$`j` は left anodyne なので $`\Delta^1\times X` 全体に延びる。

4. *制限*：$`\{1\}\times X` に制限すると $`E'\to X` の切断で、$`(1,x)\in A` なので $`\tau(x)=e'`。

直観：時刻 0 ではすべてが $`x` に縮んでいるので $`e'` を置くだけ。left fibration の持ち上げが時間の向き $`0\to 1` に沿った輸送を保証し、時刻 1 で $`X` 全体の切断が得られる。7.2 の retract は、この構成を「$`j` の持ち上げを $`\iota_1` で前合成する」と抽象化したもの。

*部品 B と C をまとめて*：$`\mathrm{ev}_x\colon\mathrm{Fun}_{/X}(X,E')\to E'_x` の $`\partial\Delta^n\subseteq\Delta^n` に対する持ち上げは $`(\partial\Delta^n\times X)\cup(\Delta^n\times\{x\})\hookrightarrow\Delta^n\times X` に沿った延長。$`\mathrm{id}_{\Delta^n}\times h` を使い、$`\Delta^n\times A\cup\partial\Delta^n\times\Delta^1\times X\hookrightarrow\Delta^n\times\Delta^1\times X` が left anodyne であること（pushout-product をもう一度）で持ち上げれば、left anodyne という中間命題を経由せずに fibration 版 Yoneda が直接出る。

- 証明の組み立て　／　使うもの
- A → B（retract）→ C　／　Joyal の定理、切断の選択、retract での閉性、pushout-product
- B を持ち上げで示す → C　／　切断の選択、pushout-product、引き戻しでの閉性
- 持ち上げで B と C を一度に（パラメータ付き）　／　縮約 $`h`、pushout-product、引き戻しでの閉性

$`X=B_{b/}` なら $`h` が $`s_0` で書けるので、最後の方法は Joyal の定理も切断の選択も使わず、依存が最も少ない。既存コード（leftFibration\_cosliceIdentityEvaluation\_trivialKanFibration の周辺）がどの方法かは要確認。

*f-b-literature-yoneda.html — 10. fibration 版 Yoneda の証明の確認 — 10.4 $`i` が left anodyne：縮約を式で書く*

$`X=B_{b/}`。$`\Delta^1\times X` の $`n` 単体 $`(\alpha,\sigma)`（$`\alpha\colon[n]\to[1]`、$`\sigma\colon\Delta^{n+1}\to B` で頂点 0 が $`b`）について $`\alpha^{-1}(0)=\{0,\dots,k-1\}` とし、

$$`\rho_k\colon[n+1]\to[n+1],\quad\rho_k(j)=\begin{cases}0&(j\le k)\\ j&(j>k)\end{cases},\qquad h(\alpha,\sigma)=\sigma\circ\rho_k.`

錐の頂点と最初の $`k` 個の頂点をまとめて $`b` につぶす操作。$`\rho_k` は単調で 0 を 0 に送るので $`X` の単体になり、単体的作用素とも整合する（$`\alpha\circ\theta` の 0 の逆像が $`\theta` で $`\alpha^{-1}(0)` に移る）。§7.3 の方法 2（余分な退化写像 $`s_0`）を fat join→join のつぶす写像と合成して書き下したもの。

- 制限　／　値　／　理由
- $`\{1\}\times X`（$`k=0`）　／　恒等　／　$`\rho_0=\mathrm{id}`
- $`\{0\}\times X`（$`k=n+1`）　／　$`\mathrm{id}_b` で定数　／　$`\rho_{n+1}` はすべてを 0 に送る
- $`\Delta^1\times\{\mathrm{id}_b\}`　／　$`\mathrm{id}_b` で定数　／　$`\sigma` が $`b` で定数なので前合成で不変

$`j\colon(\{0\}\times X)\cup(\Delta^1\times\{\mathrm{id}_b\})\hookrightarrow\Delta^1\times X` は $`\Lambda^1_0\subseteq\Delta^1` と単射の pushout-product なので left anodyne。$`\iota_1` と $`h` で $`i` は $`j` の retract（$`h\circ\iota_1=\mathrm{id}`、$`h` は $`j` の始域を $`\{\mathrm{id}_b\}` に送る）なので left anodyne。

$$`\text{縮約 }h\text{（式）}\Rightarrow i\text{ は left anodyne}\xRightarrow{\text{pushout-product}}j_n\text{ は left anodyne}\xRightarrow{p\text{ は左 fibration}}\mathrm{ev}\text{ は trivial Kan fibration}`

使うのは相対関手空間の普遍性、pushout-product の補題、retract での閉性、$`h` の式だけ。Joyal の定理も切断の選択も使わず、部品 A（$`\mathrm{id}_b` が始対象）はむしろ系として出る。$`B` は quasicategory でなくてよく、$`p` が左 fibration であることは 10.2 の延長でだけ使う。

*f-b-literature-yoneda.html — 10. fibration 版 Yoneda の証明の確認 — 10.5 一般の始対象と left anodyne*

$`X` が quasicategory で $`x` が始対象なら $`\{x\}\hookrightarrow X` は left anodyne（§7.2：$`X_{x/}\to X` の切断を選び、縮約 $`h` を作り、retract）。

- 　／　一般の始対象　／　スライス $`B_{b/}` と $`\mathrm{id}_b`
- 縮約 $`h`　／　trivial fibration の切断を選んで作る　／　$`\rho_k` の式で書ける
- 必要な仮定　／　$`X` が quasicategory、$`x` が始対象　／　なし（$`B` は任意の単体的集合）

逆向き（包含が left anodyne なら始対象）も成り立ち同値だが、直接の議論では示せず、left anodyne ⇒ left cofinal と Quillen の定理 A（$`\{x\}\times_XX_{/y}\simeq\mathrm{Hom}^R(x,y)` が弱可縮）を経由する。fibration 版 Yoneda に要るのは「始対象 ⇒ left anodyne」の向きだけで、スライスの場合は式で済む。

:::proposition "kerodon_4_2_5_1"
Kerodon Proposition 4.2.5.1（[Tag 00TP](https://kerodon.net/tag/00TP)）。対応表の状態：本体にある。

仮定：単体集合の単射 i と左または右ファイブレーション p、内部 Hom の引き戻しの選択（Kerodon と一致）。結論：内部 Hom の制限比較射 π が p と同じ側のファイブレーション（一致）。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibration_pullbackObjObjπ`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.cofinalRightFibration_pullbackObjObjπ`

:::

:::corollary "kerodon_4_2_5_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.ihom_map_leftFibration, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.cofinalIhom_map_rightFibration")
Kerodon Corollary 4.2.5.2（[Tag 00TQ](https://kerodon.net/tag/00TQ)）。対応表の状態：本体にある。

仮定：任意の単体集合 A と左または右ファイブレーション p（Kerodon と一致）。結論：Fun(A,−) の p での作用が p と同じ側のファイブレーション（一致）。

:::

:::proposition "kerodon_4_2_5_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions_pushoutObjObj_left, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions_pushoutObjObj_right, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.cofinalRightAnodyne_pushoutObjObj_right")
Kerodon Proposition 4.2.5.3（[Tag 0153](https://kerodon.net/tag/0153)）。対応表の状態：本体にある。

仮定：2 本の単射と片方の左または右アノダイン性。アノダイン側の単射は型で別の引数にしない（Lean が弱い：アノダイン性から得る）。結論：積の押し出し比較射 ι が左または右アノダイン。右版は積の因子交換で原文の順序に戻る（一致）。

:::

:::proposition "kerodon_4_2_5_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.trivialKanFibration_relativeHom_of_leftAnodyne, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.cofinalTrivialKanFibration_relativeHom_of_rightAnodyne")
Kerodon Proposition 4.2.5.4（[Tag 0154](https://kerodon.net/tag/0154)）。対応表の状態：本体にある。

仮定：i が左または右アノダインで p が同じ側のファイブレーション、内部 Hom の引き戻しの選択（Kerodon と一致）。結論：Fun(B,X) から制限と後合成を組にした比較射 π が自明 Kan ファイブレーション（一致）。

*f-b-literature-yoneda.html — 10. fibration 版 Yoneda の証明の確認 — 10.1 設定*

- $`B`：単体的集合（quasicategory でなくてよい）。$`p\colon E\to B`：*左 fibration*（本質的な仮定）。

- $`E_b=\{b\}\times_BE`：厳密な引き戻し。$`p` は isofibration なので ∞ 圏としての引き戻しでもある。

- $`B_{b/}`：join スライス（$`n` 単体は頂点 0 が $`b` の $`\Delta^{n+1}\to B`、射影は $`d_0`）。$`B_{b/}` と $`E` はどちらも $`B` 上の単体的集合。

- $`\mathrm{Fun}_{/B}(B_{b/},E)=\mathrm{Fun}(B_{b/},E)\times_{\mathrm{Fun}(B_{b/},B)}\{\text{射影}\}`（厳密な引き戻し）。

- 評価写像：$`\mathrm{id}_b=s_0(b)` は $`b` の上にあるので $`i\colon\{\mathrm{id}_b\}\hookrightarrow B_{b/}` は $`B` 上の写像。$`\mathrm{ev}=i^*\colon\mathrm{Fun}_{/B}(B_{b/},E)\to\mathrm{Fun}_{/B}(\{\mathrm{id}_b\},E)=E_b`。

*f-b-literature-yoneda.html — 10. fibration 版 Yoneda の証明の確認 — 10.2 相対関手空間の普遍性による書き直し*

内部 Hom の普遍性 $`\{K\to\mathrm{Fun}(L,E)\}\cong\{K\times L\to E\}` から、$`\mathrm{Fun}_{/B}(L,E)` が $`\mathrm{Fun}(L,E)\to\mathrm{Fun}(L,B)` の点 $`p_L` 上のファイバーであることにより

$$`\{K\to\mathrm{Fun}_{/B}(L,E)\}\cong\{g\colon K\times L\to E\mid p\circ g=p_L\circ\mathrm{pr}_L\}`

（$`K\times L` を $`L` 経由で $`B` 上にあるとみたときの $`B` 上の写像）。$`\mathrm{ev}` の $`\partial\Delta^n\subseteq\Delta^n` に対する持ち上げ問題の各部分を読み替える（$`L=B_{b/}`、$`x=\mathrm{id}_b`）。

- 持ち上げ問題　／　読み替え後
- 上の写像 $`u\colon\partial\Delta^n\to\mathrm{Fun}_{/B}(L,E)`　／　$`B` 上の $`\tilde u\colon\partial\Delta^n\times L\to E`
- 下の写像 $`v\colon\Delta^n\to E_b`　／　$`B` 上の $`\tilde v\colon\Delta^n\times\{x\}\to E`
- 可換性　／　$`\tilde u,\tilde v` が $`\partial\Delta^n\times\{x\}` で一致
- 持ち上げ $`w`　／　$`\tilde u,\tilde v` を延長する $`B` 上の $`\tilde w\colon\Delta^n\times L\to E`

$`\tilde u,\tilde v` は合併 $`(\partial\Delta^n\times L)\cup(\Delta^n\times\{x\})`（共通部分 $`\partial\Delta^n\times\{x\}`、押し出しと同じ）からの写像に貼り合わさり、底の写像は $`\Delta^n\times L\to L\to B`。したがって元の問題は、$`j_n\colon(\partial\Delta^n\times L)\cup(\Delta^n\times\{x\})\hookrightarrow\Delta^n\times L` の $`p` に対する持ち上げ問題と同じ。一般に「$`i\colon K\hookrightarrow L` に沿った制限が trivial Kan fibration」⇔「すべての $`n` で $`\partial\Delta^n\subseteq\Delta^n` と $`i` の pushout-product が $`p` に対して左持ち上げ性質を持つ」。$`n=0` では $`j_0=i` で、$`E_b` の点を通る切断の存在（逆写像）にあたる。

*f-b-literature-yoneda.html — 10. fibration 版 Yoneda の証明の確認 — 10.3 pushout-product で $`i` に帰着*

$`j_n` は単射 $`\partial\Delta^n\subseteq\Delta^n` と $`i` の pushout-product。単射と left anodyne の pushout-product は left anodyne（HTT 2.1.2.7。生成元どうしの場合に角柱 $`\Delta^m\times\Delta^n` を単体に分解する組合せ論で示される）。よって $`i` が left anodyne なら $`j_n` も left anodyne で、$`p` は左 fibration なので持ち上がる。

:::

# 4.2.6 The Homotopy Extension Lifting Property

%%%
number := false
tag := "kerodon-4-2-6"
%%%

Kerodon [Tag 00T8](https://kerodon.net/tag/00T8)

:::proposition "kerodon_4_2_6_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.trivialKanFibration_relativeHom_of_leftAnodyne, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeEdgeSource_trivialKanFibration") (uses := "kerodon_1_1_0_6, kerodon_1_5_4_9, kerodon_3_1_2_10, kerodon_4_2_5_4")
Kerodon Proposition 4.2.6.1（[Tag 00TE](https://kerodon.net/tag/00TE)）。対応表の状態：一部。

relativeEdgeSource\_trivialKanFibration は left fibration⇒ev₀の自明Kan性という原文の向きを直接返す。右側のiffと逆向きは含まない。

:::

:::corollary "kerodon_4_2_6_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIntervalEvaluation_trivialKanFibration") (uses := "kerodon_1_1_0_6, kerodon_4_2_6_1")
Kerodon Corollary 4.2.6.2（[Tag 0155](https://kerodon.net/tag/0155)）。対応表の状態：一部。

kanIntervalEvaluation\_trivialKanFibration は底が一点で X が Kan のときの ev₁ の自明Kan性を直接返す。相対の二端点の同時判定・逆向きは含まない。

:::

