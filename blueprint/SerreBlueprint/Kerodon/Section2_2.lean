import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.Lax
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor
import Mathlib.CategoryTheory.Bicategory.Functor.StrictlyUnitary
import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid
import Mathlib.CategoryTheory.Bicategory.Opposites
import Mathlib.CategoryTheory.Bicategory.Span.Basic
import Mathlib.CategoryTheory.Bicategory.Strict.Basic

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "2.2 The Theory of Bicategories" =>
%%%
number := false
tag := "kerodon-2-2"
%%%

Kerodon の 2.2 節（[Tag 007K](https://kerodon.net/tag/007K)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

:::definition "kerodon_2_2_0_1" (lean := "CategoryTheory.Bicategory.Strict")
Kerodon Definition 2.2.0.1（[Tag 007L](https://kerodon.net/tag/007L)）。対応表の状態：Mathlib にある。

*主張*　厳密 2 圏は、対象、対象対ごとの Hom 圏、合成関手、および各対象の恒等 1 射を備える。合成は Hom 圏の関手として厳密に結合的かつ単位的である。

仮定：対象型と Hom 圏・横合成を備えた双圏 B（Kerodon と一致。Lean では双圏の構造を先に与える）。結論：1 射の結合と単位を等式で課し、結合子・単位子をそれらの等式から得る厳密双圏の述語（一致）。

:::

# 2.2.1 Bicategories

%%%
number := false
tag := "kerodon-2-2-1"
%%%

Kerodon [Tag 007P](https://kerodon.net/tag/007P)

:::definition "kerodon_2_2_1_1" (lean := "CategoryTheory.Bicategory")
Kerodon Definition 2.2.1.1（[Tag 007Q](https://kerodon.net/tag/007Q)）。対応表の状態：Mathlib にある。

*主張*　双圏には対象、対象対ごとの Hom 圏、合成関手、恒等 1 射、その自己合成を恒等 1 射と同一視する可逆 2 射がある。合成の結合子は自然同型で五角形を満たし、恒等 1 射との左右の合成は Hom 圏の充満忠実関手である。

仮定：対象型 B（Kerodon と一致）。結論：Hom 圏、横合成と恒等 1 射、可逆な結合子と左右単位子、五角形と三角形の整合条件を持つ構造（一致）。

:::

:::definition "kerodon_2_2_1_7"
Kerodon Notation 2.2.1.7（[Tag 007Y](https://kerodon.net/tag/007Y)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。原文は対象・1射・2射を表す文字の慣例。Bicategory は双圏の型で、文字の使い分けに対応する宣言はない。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::definition "kerodon_2_2_1_10"
Kerodon Construction 2.2.1.10（[Tag 00EW](https://kerodon.net/tag/00EW)）。対応表の状態：なし。

B6：Bicategory の unitor の場は原文の υ に依存する一意構成・可換図式を述べない。選択された別提示の場の型だけを構成の一部とは数えない。

宣言：`CategoryTheory.Bicategory.leftUnitor`、`CategoryTheory.Bicategory.rightUnitor`

:::

:::proposition "kerodon_2_2_1_13"
Kerodon Proposition 2.2.1.13（[Tag 00EZ](https://kerodon.net/tag/00EZ)）。対応表の状態：Mathlib にある。

*主張*　双圏の連続する $`f\colon X\to Y`、$`g\colon Y\to Z` について、$`g\circ(\mathrm{id}_Y\circ f)` から $`g\circ f` への 2 射は、直接左単位制約を適用しても、結合子の後に右単位制約を適用しても同じである。

仮定：双圏 B と合成可能な 1 射 f : a ⟶ b、g : b ⟶ c（Kerodon と一致）。結論：間に 𝟙\_b を挟む結合子と左右の単位子でできる三角形の可換性（一致）。

宣言：`CategoryTheory.Bicategory.triangle`

:::

:::corollary "kerodon_2_2_1_14" (lean := "CategoryTheory.Bicategory.unitors_equal") (uses := "kerodon_2_2_1_13")
Kerodon Corollary 2.2.1.14（[Tag 0082](https://kerodon.net/tag/0082)）。対応表の状態：一部。

*主張*　双圏の恒等 1 射に対する左右単位制約は、ともにその恒等 1 射の自己合成からの単位制約 $`\upsilon_X` に一致する。

B6：unitors\_equal は恒等1射上の λ.hom=ρ.hom を直接述べる。原文の三者一致のうちこの二者の一致のみで、別に与える υ との一致は含まない。

:::

:::proposition "kerodon_2_2_1_15" (lean := "CategoryTheory.Bicategory.leftUnitor_comp, CategoryTheory.Bicategory.rightUnitor_comp")
Kerodon Proposition 2.2.1.15（[Tag 0080](https://kerodon.net/tag/0080)）。対応表の状態：Mathlib にある。

*主張*　双圏の三重合成のうち一番外または一番内の射が恒等射なら、その結合子は、恒等射を単位制約で除き、反対側の括り方に単位制約の逆で入れ直す合成で与えられる。

仮定：双圏 B と合成可能な 1 射 f : a ⟶ b、g : b ⟶ c（Kerodon と一致）。結論：端に恒等 1 射がある結合子を単位子とその逆、whiskering で表す左右二式（一致。Lean は逆単位子を移項する前の等式）。

:::

# 2.2.2 Examples of Bicategories

%%%
number := false
tag := "kerodon-2-2-2"
%%%

Kerodon [Tag 0083](https://kerodon.net/tag/0083)

:::definition "kerodon_2_2_2_2" (lean := "CategoryTheory.Span, CategoryTheory.Span.SpanBicat")
Kerodon Variant 2.2.2.2（[Tag 03J5](https://kerodon.net/tag/03J5)）。対応表の状態：Mathlib にある。

*主張*　圏の span は $`X\leftarrow M\to Y` という図式である。ファイバー積があれば $`\operatorname{Cospan}(\mathcal C^{\mathrm{op}})` の共役として、同じ対象と span を 1 射とする双圏 $`\operatorname{Span}(\mathcal C)` を得る。

仮定：引き戻しを持つ圏 C（Kerodon と一致。Lean の両脚の射の性質はともに任意の射を許す場合に取る）。結論：対象は C の対象、1 射は X ← M → Y、2 射は両脚と可換な頂点間の射、合成は引き戻しによる双圏（一致）。

:::

# 2.2.3 Opposite and Conjugate Bicategories

%%%
number := false
tag := "kerodon-2-2-3"
%%%

Kerodon [Tag 008A](https://kerodon.net/tag/008A)

:::definition "kerodon_2_2_3_1" (lean := "Bicategory.Opposite.bicategory")
Kerodon Construction 2.2.3.1（[Tag 008B](https://kerodon.net/tag/008B)）。対応表の状態：Mathlib にある。

*主張*　双圏の反対は対象を保ち、$`\operatorname{Hom}_{\mathcal C^{\mathrm{op}}}(X^{\mathrm{op}},Y^{\mathrm{op}})=\operatorname{Hom}_{\mathcal C}(Y,X)` とする。1 射の向きと合成の順は反転し、2 射の向きは保たれ、逆順で用いる結合子は元の結合子の逆になる。

仮定：双圏 B（Kerodon と一致）。結論：Bᵒᵖ の双圏構造を与え、Hom\_Bᵒᵖ(Xᵒᵖ,Yᵒᵖ) では X,Y を交換するが、その Hom 圏の 2 射の向きは保つ（一致）。

:::

:::definition "kerodon_2_2_3_4"
Kerodon Construction 2.2.3.4（[Tag 008D](https://kerodon.net/tag/008D)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。1射を保って2射だけを反転する構成は Opposites の TODO。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

# 2.2.4 Functors of Bicategories

%%%
number := false
tag := "kerodon-2-2-4"
%%%

Kerodon [Tag 008G](https://kerodon.net/tag/008G)

:::definition "kerodon_2_2_4_1" (lean := "CategoryTheory.StrictPseudofunctor")
Kerodon Definition 2.2.4.1（[Tag 008H](https://kerodon.net/tag/008H)）。対応表の状態：Mathlib にある。

*主張*　双圏の厳密関手は、対象写像と各 Hom 圏間の関手で、恒等 1 射と合成関手を厳密に保ち、単位制約と結合子も対応する制約へ送るものである。

仮定：双圏 B, C（Kerodon と一致）。結論：対象・Hom 圏の関手を持ち、恒等 1 射と横合成の比較が保存等式から来る厳密関手の型（一致）。

:::

:::definition "kerodon_2_2_4_5" (lean := "CategoryTheory.LaxFunctor")
Kerodon Definition 2.2.4.5（[Tag 008K](https://kerodon.net/tag/008K)）。対応表の状態：Mathlib にある。

*主張*　双圏間の lax 関手は対象写像と Hom 圏上の関手に、恒等制約 $`\mathrm{id}_{FX}\Rightarrow F(\mathrm{id}_X)` と自然な合成制約 $`F(g)\circ F(f)\Rightarrow F(g\circ f)` を加えたものである。これらは左右の単位と結合子の図式に両立し、すべての制約が可逆な場合を双圏間の関手と呼ぶ。

仮定：双圏 B, C（Kerodon と一致）。結論：対象と Hom 圏の作用、𝟙 → F(𝟙) と F(g)∘F(f) → F(g∘f) の比較 2 射、自然性・結合・単位条件を持つ lax 関手の型（一致）。

:::

:::definition "kerodon_2_2_4_15"
Kerodon Notation 2.2.4.15（[Tag 008Q](https://kerodon.net/tag/008Q)）。対応表の状態：Mathlib にある。

*主張*　lax 2 関手 $`F` に付随する恒等制約と合成制約を、必要に応じて $`\epsilon_X^F`、$`\mu_{g,f}^F` と関手を明示して記す。

仮定：双圏間の lax 関手 F、対象 a または合成可能な 1 射 f, g（Kerodon と一致）。結論：mapId a が 𝟙\_(F a) ⇒ F(𝟙\_a)、mapComp f g が F(g)∘F(f) ⇒ F(g∘f) を与える（一致）。

宣言：`CategoryTheory.LaxFunctor.mapId`、`CategoryTheory.LaxFunctor.mapComp`

:::

:::definition "kerodon_2_2_4_17" (lean := "CategoryTheory.StrictlyUnitaryLaxFunctor")
Kerodon Definition 2.2.4.17（[Tag 008R](https://kerodon.net/tag/008R)）。対応表の状態：一部。

*主張*　lax 関手の恒等制約が各対象で可逆なら単位的である。恒等 1 射を等号で保ち、恒等制約が恒等 2 射であれば厳密に単位的である。

B6：StrictlyUnitaryLaxFunctor.map\_id と mapId\_eq\_eqToHom は原文の strictly unital の定義を直接与える。unital だけを要求する前半の一般の述語は含まない。

:::

# 2.2.5 The Category of Bicategories

%%%
number := false
tag := "kerodon-2-2-5"
%%%

Kerodon [Tag 008V](https://kerodon.net/tag/008V)

:::definition "kerodon_2_2_5_1" (lean := "CategoryTheory.LaxFunctor.comp")
Kerodon Construction 2.2.5.1（[Tag 008W](https://kerodon.net/tag/008W)）。対応表の状態：Mathlib にある。

*主張*　lax 関手 $`F,G` の合成は対象と Hom 圏で通常どおり合成する。恒等制約と合成制約は、まず $`G` の制約を使い、次に $`F` の制約へ $`G` を適用して得る。

仮定：双圏 B, C, D と lax 関手 F : B ⥤ C、G : C ⥤ D（Kerodon と一致）。結論：対象と Hom 圏では通常の関手合成を取り、比較射は G の比較射に F の比較射の G 像を続ける lax 関手（一致）。

:::

:::definition "kerodon_2_2_5_5" (lean := "CategoryTheory.LaxFunctor.id, CategoryTheory.LaxFunctor.comp, CategoryTheory.Pseudofunctor.id, CategoryTheory.Pseudofunctor.comp, CategoryTheory.StrictPseudofunctor.id, CategoryTheory.StrictPseudofunctor.comp") (uses := "kerodon_2_2_4_5, kerodon_2_2_5_1")
Kerodon Definition 2.2.5.5（[Tag 0090](https://kerodon.net/tag/0090)）。対応表の状態：一部。

*主張*　小双圏と lax 関手は通常の圏 $`\mathrm{2Cat}_{\mathrm{Lax}}` をなす。関手、厳密双圏間の厳密関手、厳密に単位的な lax 関手に制限して、それぞれ $`\mathrm{2Cat}`、$`\mathrm{2Cat}_{\mathrm{Str}}`、$`\mathrm{2Cat}_{\mathrm{ULax}}` を得る。

B6：id と comp は原文で指定された各種関手の恒等射・合成という構成成分を直接与える。双圏を対象として束ねた普通圏とその厳密な圏則は未確認。

:::

# 2.2.6 Isomorphisms of Bicategories

%%%
number := false
tag := "kerodon-2-2-6"
%%%

Kerodon [Tag 0097](https://kerodon.net/tag/0097)

:::definition "kerodon_2_2_6_1"
Kerodon Definition 2.2.6.1（[Tag 0098](https://kerodon.net/tag/0098)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。双圏間の擬関手が等式で両側逆を持つという2Catでの同型の定義は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::proposition "kerodon_2_2_6_6"
Kerodon Proposition 2.2.6.6（[Tag 009D](https://kerodon.net/tag/009D)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。lax 関手の厳密な逆から比較2射の可逆性を導く命題は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::definition "kerodon_2_2_6_7"
Kerodon Notation 2.2.6.7（[Tag 009E](https://kerodon.net/tag/009E)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。合成する各1射対にその合成の自己同型を与える twisting cochain の型は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::definition "kerodon_2_2_6_8"
Kerodon Construction 2.2.6.8（[Tag 009F](https://kerodon.net/tag/009F)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。twisting cochain による横合成と構造2射の取り替えは未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

# 2.2.7 Strictly Unital Bicategories

%%%
number := false
tag := "kerodon-2-2-7"
%%%

Kerodon [Tag 00FC](https://kerodon.net/tag/00FC)

:::definition "kerodon_2_2_7_1" (lean := "CategoryTheory.Bicategory.Strict")
Kerodon Definition 2.2.7.1（[Tag 00FD](https://kerodon.net/tag/00FD)）。対応表の状態：一部。

*主張*　双圏が厳密に単位的であるとは、すべての 1 射の左・右単位制約が恒等 2 射であることをいう。

B6：Strict の id\_comp/comp\_id と left/rightUnitor\_eqToIso から原文の厳密単位性が直接得られる。associator も等式由来とする追加仮定がある。

:::

:::proposition "kerodon_2_2_7_2"
Kerodon Proposition 2.2.7.2（[Tag 00FE](https://kerodon.net/tag/00FE)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。厳密単位性と、恒等1射の等式・υ・恒等を二つ含む結合子の三条件の同値は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::proposition "kerodon_2_2_7_7"
Kerodon Proposition 2.2.7.7（[Tag 00FG](https://kerodon.net/tag/00FG)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。任意の双圏から厳密単位的な双圏への、単位も厳密な同型の構成は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

# 2.2.8 The Homotopy Category of a Bicategory

%%%
number := false
tag := "kerodon-2-2-8"
%%%

Kerodon [Tag 02GD](https://kerodon.net/tag/02GD)

:::definition "kerodon_2_2_8_1"
Kerodon Definition 2.2.8.1（[Tag 02AR](https://kerodon.net/tag/02AR)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。局所離散な双圏への関手はあるが、それを表現する粗ホモトピー圏の普遍性は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::definition "kerodon_2_2_8_2"
Kerodon Construction 2.2.8.2（[Tag 02AS](https://kerodon.net/tag/02AS)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。各 Hom 圏の全2射に沿う連結成分で1射を割った普通圏は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::proposition "kerodon_2_2_8_3"
Kerodon Proposition 2.2.8.3（[Tag 02AT](https://kerodon.net/tag/02AT)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。粗ホモトピー圏の指定の射影に沿う関手の一意因子化は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::corollary "kerodon_2_2_8_4"
Kerodon Corollary 2.2.8.4（[Tag 02AU](https://kerodon.net/tag/02AU)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。局所離散化に対する粗ホモトピー圏の左随伴は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::definition "kerodon_2_2_8_5" (lean := "CategoryTheory.Bicategory.IsLocallyGroupoid")
Kerodon Definition 2.2.8.5（[Tag 009Q](https://kerodon.net/tag/009Q)）。対応表の状態：Mathlib にある。

*主張*　この文献での 2 圏は、すべての 2 射が可逆な双圏である。

仮定：双圏 B（Kerodon と一致）。結論：各 Hom 圏が亜群である、すなわち任意の 2 射が可逆であるという述語（一致）。

:::

:::definition "kerodon_2_2_8_9" (lean := "CategoryTheory.Bicategory.Pith")
Kerodon Construction 2.2.8.9（[Tag 00AL](https://kerodon.net/tag/00AL)）。対応表の状態：Mathlib にある。

*主張*　双圏の pith は各 Hom 圏をその core に替え、対象・1 射を保ち、合成と結合・単位制約を制限した 2 圏である。

仮定：任意の双圏 B（Kerodon と一致。Pith の対象型は B の型に対するラッパーで、双圏構造は B の双圏構造から入る）。結論：対象と 1 射を保ち、Hom 圏の射を可逆 2 射に制限する Pith（一致）。

:::

:::definition "kerodon_2_2_8_12"
Kerodon Construction 2.2.8.12（[Tag 02AW](https://kerodon.net/tag/02AW)）。対応表の状態：なし。

B6：Pith と inclusion は可逆2射に制限する双圏であり、原文の1射の同型類を Hom とする普通圏 hPith ではない。商と合成の降下が別に要る。

宣言：`CategoryTheory.Bicategory.Pith`、`CategoryTheory.Bicategory.Pith.inclusion`

:::

:::definition "kerodon_2_2_8_17" (lean := "CategoryTheory.Bicategory.Equivalence")
Kerodon Definition 2.2.8.17（[Tag 02B1](https://kerodon.net/tag/02B1)）。対応表の状態：一部。

*主張*　双圏の 1 射が同型であるとは、pith のホモトピー圏で可逆であることをいう。同値な判定は、左右の合成がそれぞれ恒等 1 射と可逆 2 射で結ばれる逆向きの射を持つことである。

B6：Equivalence の hom に対して inv・unit・counit が原文の両側ホモトピー逆を直接与える。指定1射をこのデータの hom とし、triangle も持つ場合に限る。hPith の IsIso との iff は含めない。

:::

:::definition "kerodon_2_2_8_24" (lean := "CategoryTheory.Bicategory.IsLocallyGroupoid")
Kerodon Definition 2.2.8.24（[Tag 02B8](https://kerodon.net/tag/02B8)）。対応表の状態：一部。

*主張*　双圏が 2 亜群であるとは、すべての 1 射がホモトピー逆を持ち、すべての 2 射が同型であることをいう。

B6：IsLocallyGroupoid の ∀b c, IsGroupoid(b⟶c) は原文の全2射が可逆という結論成分。全1射が同値である条件は含まない。

:::

:::definition "kerodon_2_2_8_27"
Kerodon Construction 2.2.8.27（[Tag 02BB](https://kerodon.net/tag/02BB)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。Pith は可逆2射のみの制限。1射も同値に制限する core 双圏は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

