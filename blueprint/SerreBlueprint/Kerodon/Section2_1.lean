-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "2.1 Monoidal Categories" =>
%%%
number := false
tag := "kerodon-2-1"
%%%

Kerodon の 2.1 節（[Tag 00BL](https://kerodon.net/tag/00BL)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

# 2.1.1 Nonunital Monoidal Categories

%%%
number := false
tag := "kerodon-2-1-1"
%%%

Kerodon [Tag 00BT](https://kerodon.net/tag/00BT)

:::definition "kerodon_2_1_1_1"
Kerodon Definition 2.1.1.1（[Tag 00BU](https://kerodon.net/tag/00BU)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。単位を持たない厳密なテンソルの定義は未発見。厳密双圏の型は別。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::definition "kerodon_2_1_1_5" (lean := "CategoryTheory.MonoidalCategory")
Kerodon Definition 2.1.1.5（[Tag 00BY](https://kerodon.net/tag/00BY)）。対応表の状態：一部。

*主張*　非単位的モノイダル構造は、圏の二変数関手 $`\otimes` と自然な結合子 $`X\otimes(Y\otimes Z)\simeq(X\otimes Y)\otimes Z` からなる。四対象に対して結合子が五角形恒等式を満たすことを課す。

B6：MonoidalCategory のテンソル関手・associator（原文の向きには逆同型）・自然性・pentagon を忘却すると原文の非単位モノイダル構造を直接得る。単位対象と単位則も持つ圏に仮定を強めた場合。

:::

# 2.1.2 Monoidal Categories

%%%
number := false
tag := "kerodon-2-1-2"
%%%

Kerodon [Tag 00C2](https://kerodon.net/tag/00C2)

:::definition "kerodon_2_1_2_1"
Kerodon Definition 2.1.2.1（[Tag 00C3](https://kerodon.net/tag/00C3)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。Mathlib の MonoidalCategory は結合子・単位子が同型で、対象と射の厳密な等式を要求しない。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::proposition "kerodon_2_1_2_3"
Kerodon Proposition 2.1.2.3（[Tag 00C5](https://kerodon.net/tag/00C5)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。単位を仮定した冪等元の等式はあるが、半群で冪等かつ左乗法が単射という特徴づけは未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::corollary "kerodon_2_1_2_4"
Kerodon Corollary 2.1.2.4（[Tag 00C6](https://kerodon.net/tag/00C6)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。半群で左右の消去性と冪等性から両側単位を特徴づける宣言は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::definition "kerodon_2_1_2_5"
Kerodon Definition 2.1.2.5（[Tag 00C7](https://kerodon.net/tag/00C7)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。単位なし圏の候補 (1, υ) を両側テンソルの充満忠実性で定義する型は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::proposition "kerodon_2_1_2_9"
Kerodon Proposition 2.1.2.9（[Tag 00CB](https://kerodon.net/tag/00CB)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。二つの (1, υ) の間の乗法を保存する一意な同型は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::definition "kerodon_2_1_2_10" (lean := "CategoryTheory.MonoidalCategory")
Kerodon Definition 2.1.2.10（[Tag 00CC](https://kerodon.net/tag/00CC)）。対応表の状態：一部。

*主張*　モノイダル構造は非単位的モノイダル構造と単位の組 $`(\mathbf1,\upsilon)` を指定したものである。$`\upsilon\colon\mathbf1\otimes\mathbf1\simeq\mathbf1` は単位制約である。

B6：MonoidalCategory の tensorObj・tensorHom と associator の逆同型・pentagon が非単位部分を直接与える。原文の単位 (1,υ) と完全忠実性による提示との比較は含めない。

:::

:::definition "kerodon_2_1_2_13" (lean := "CategoryTheory.MonoidalCategoryStruct.tensorUnit")
Kerodon Notation 2.1.2.13（[Tag 00CF](https://kerodon.net/tag/00CF)）。対応表の状態：Mathlib にある。

*主張*　モノイダル圏の単位対象を $`\mathbf1` と書き、複数の圏を区別するときは $`\mathbf1_{\mathcal C}` とする。

仮定：単位を持つモノイダル圏 C（Lean が弱い：射影には MonoidalCategoryStruct で足り、整合公理を要求しない）。結論：tensorUnit は C の対象を返し、原文の 𝟙\_C と同じ単位対象を指定する（一致）。

:::

:::definition "kerodon_2_1_2_17"
Kerodon Construction 2.1.2.17（[Tag 00CH](https://kerodon.net/tag/00CH)）。対応表の状態：なし。

B6：leftUnitor/rightUnitor は選ばれた構造の場。原文は与えられた υ から特定の可換図式を満たす同型を一意に構成する主張で、その υ と場を結ぶ宣言がなく、型の一致だけでは直接の部分結論にならない。

宣言：`CategoryTheory.MonoidalCategoryStruct.leftUnitor`、`CategoryTheory.MonoidalCategoryStruct.rightUnitor`

:::

:::proposition "kerodon_2_1_2_19" (lean := "CategoryTheory.MonoidalCategory.triangle")
Kerodon Proposition 2.1.2.19（[Tag 00CK](https://kerodon.net/tag/00CK)）。対応表の状態：Mathlib にある。

*主張*　モノイダル圏の任意の $`X,Y` について、$`X\otimes(\mathbf1\otimes Y)\to X\otimes Y` は、左単位制約を直接使っても、結合子の後に右単位制約を使っても同じになる。

仮定：モノイダル圏 C と対象 X, Y（Kerodon と一致）。結論：(X ⊗ 𝟙) ⊗ Y から X ⊗ Y への二経路について、結合子を原文と逆向きに書いた三角恒等式を与える（一致）。

:::

:::corollary "kerodon_2_1_2_21" (lean := "CategoryTheory.MonoidalCategory.unitors_equal")
Kerodon Corollary 2.1.2.21（[Tag 00CM](https://kerodon.net/tag/00CM)）。対応表の状態：一部。

*主張*　単位対象での左・右単位制約 $`\lambda_{\mathbf1}` と $`\rho_{\mathbf1}` は、いずれも $`\upsilon\colon\mathbf1\otimes\mathbf1\simeq\mathbf1` に等しい。

B6：unitors\_equal は単位対象上で λ.hom=ρ.hom を直接述べる。原文の三者一致のうち λ=ρ の成分。別に指定した υ との一致は含めない。

:::

# 2.1.4 Nonunital Monoidal Functors

%%%
number := false
tag := "kerodon-2-1-4"
%%%

Kerodon [Tag 00CV](https://kerodon.net/tag/00CV)

:::definition "kerodon_2_1_4_1"
Kerodon Definition 2.1.4.1（[Tag 00CW](https://kerodon.net/tag/00CW)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。単位なしのテンソルを対象と射で厳密に保存する関手の定義は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::definition "kerodon_2_1_4_3" (lean := "CategoryTheory.Functor.LaxMonoidal")
Kerodon Definition 2.1.4.3（[Tag 00CY](https://kerodon.net/tag/00CY)）。対応表の状態：一部。

*主張*　非単位的モノイダル圏の間の関手 $`F` の非単位的 lax モノイダル構造は、$`F(X)\otimes F(Y)\to F(X\otimes Y)` という自然なテンソル制約であって、三対象について両圏の結合子と両立するものである。

B6：LaxMonoidal の μ・naturality・associativity は原文の非単位 lax 構造を直接与える。単位つき圏と ε・単位則まで持つ関手に仮定を強めた場合。

:::

:::definition "kerodon_2_1_4_4" (lean := "CategoryTheory.Functor.Monoidal")
Kerodon Definition 2.1.4.4（[Tag 00CZ](https://kerodon.net/tag/00CZ)）。対応表の状態：一部。

*主張*　非単位的モノイダル関手とは、非単位的 lax モノイダル関手のうち、どのテンソル制約も同型であるものである。

B6：Monoidal の μ/δ と μ\_δ・δ\_μ は原文の tensorator の可逆性を直接与える。圏も関手も単位つきという追加仮定がある。

:::

:::definition "kerodon_2_1_4_10" (lean := "CategoryTheory.NatTrans.IsMonoidal")
Kerodon Definition 2.1.4.10（[Tag 00D5](https://kerodon.net/tag/00D5)）。対応表の状態：一部。

*主張*　二つの非単位的 lax モノイダル関手の間の非単位的モノイダル自然変換は、各対のテンソル制約と可換な自然変換である。これらを射とする関手圏で、制約が同型である関手は充満部分圏をなす。

B6：IsMonoidal.tensor は原文のテンソル可換正方形そのもの。単位つき lax 関手と単位整合まで仮定した場合に限り、非単位変換の条件を得る。

:::

:::definition "kerodon_2_1_4_16" (lean := "CategoryTheory.Functor.OplaxMonoidal")
Kerodon Variant 2.1.4.16（[Tag 00MM](https://kerodon.net/tag/00MM)）。対応表の状態：一部。

*主張*　非単位的 colax モノイダル構造は反対関手の非単位的 lax モノイダル構造である。すなわち $`F(X\otimes Y)\to F(X)\otimes F(Y)` という逆向きの自然変換が両圏の結合子と両立する。

B6：OplaxMonoidal の δ と自然性・結合則から非単位 colax 構造を直接忘却できる。単位対象・余単位・単位則を持つ場合だけ。

:::

:::definition "kerodon_2_1_4_17" (lean := "CategoryTheory.Functor.LaxMonoidal.comp")
Kerodon Construction 2.1.4.17（[Tag 00DB](https://kerodon.net/tag/00DB)）。対応表の状態：一部。

*主張*　非単位的 lax モノイダル関手 $`F,G` の合成のテンソル制約は、まず $`G` の制約で $`GF(X)\otimes GF(Y)\to G(F(X)\otimes F(Y))` とし、次に $`F` の制約に $`G` を適用して得る。これは両関手圏の合成則をなす。

B6：LaxMonoidal.comp の μ X Y=μ G \_ \_≫G.map(μ F X Y) は原文の合成式。単位つき lax 関手に限る追加仮定がある。

:::

:::definition "kerodon_2_1_4_19" (lean := "CategoryTheory.Comma")
Kerodon Notation 2.1.4.19（[Tag 00MN](https://kerodon.net/tag/00MN)）。対応表の状態：Mathlib にある。

*主張*　$`F\colon\mathcal C\to\mathcal E`、$`G\colon\mathcal D\to\mathcal E` の有向ファイバー積は、$`(C,D,F(C)\to G(D))` を対象とし、表示した辺の四角形を可換にする $`(C\to C',D\to D')` を射とする。これは $`\mathcal E` の矢印圏の両端点で引き戻して得られる。

仮定：三つの圏 A, B, T と関手 F : A ⥤ T、G : B ⥤ T（Kerodon と一致）。結論：Comma F G は (a,b,F(a) → G(b)) を対象とし、脚の射が作る正方形を可換とする射を持つ（一致）。

:::

:::proposition "kerodon_2_1_4_21"
Kerodon Proposition 2.1.4.21（[Tag 00MP](https://kerodon.net/tag/00MP)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。Comma の構成はあるが、射影を厳密モノイダルにする構造との全単射は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

# 2.1.5 Lax Monoidal Functors

%%%
number := false
tag := "kerodon-2-1-5"
%%%

Kerodon [Tag 00DD](https://kerodon.net/tag/00DD)

:::definition "kerodon_2_1_5_1" (lean := "CategoryTheory.MonObj")
Kerodon Definition 2.1.5.1（[Tag 00DE](https://kerodon.net/tag/00DE)）。対応表の状態：一部。

*主張*　モノイダル圏の非単位的代数 $`A` の単位とは、$`\epsilon\colon\mathbf1\to A` で、左または右の因子へ挿入してから積をとると、単位制約を介して $`A` の恒等射になるものをいう。一方だけなら左単位または右単位である。

B6：MonObj の one\_mul・mul\_one は選ばれた m=mul、ε=one について左・右単位の式を与える（unitor の逆を前合成）。任意の非単位代数の任意の候補 ε の述語ではない。

:::

:::definition "kerodon_2_1_5_2" (lean := "CategoryTheory.Functor.LaxMonoidal.left_unitality, CategoryTheory.Functor.LaxMonoidal.right_unitality")
Kerodon Definition 2.1.5.2（[Tag 00DG](https://kerodon.net/tag/00DG)）。対応表の状態：一部。

*主張*　非単位的 lax モノイダル関手 $`F` の左・右単位とは、$`\epsilon\colon\mathbf1_{\mathcal D}\to F(\mathbf1_{\mathcal C})` を該当側へ挿入し、テンソル制約と $`F` による単位制約を合成すると、標的圏の単位制約になるものをいう。両側を満たせば $`F` の単位である。

B6：LaxMonoidal の left/right\_unitality は ε=ε F として原文の左右の単位式を直接与える。独立に指定する任意の ε を特徴づける定義ではない。

:::

:::proposition "kerodon_2_1_5_4"
Kerodon Proposition 2.1.5.4（[Tag 00DJ](https://kerodon.net/tag/00DJ)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。別々の左単位射・右単位射の一致を示す宣言は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::corollary "kerodon_2_1_5_5"
Kerodon Corollary 2.1.5.5（[Tag 00DK](https://kerodon.net/tag/00DK)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。独立な左右の単位の存在と両側単位の一意存在の同値は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::proposition "kerodon_2_1_5_6"
Kerodon Proposition 2.1.5.6（[Tag 00MS](https://kerodon.net/tag/00MS)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。左右の単位条件をコンマ圏上の単位子で特徴づける宣言は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::corollary "kerodon_2_1_5_7"
Kerodon Corollary 2.1.5.7（[Tag 00MT](https://kerodon.net/tag/00MT)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。単位射の条件とコンマ圏の (1, υ) の条件の同値は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::definition "kerodon_2_1_5_8" (lean := "CategoryTheory.Functor.LaxMonoidal")
Kerodon Definition 2.1.5.8（[Tag 00DL](https://kerodon.net/tag/00DL)）。対応表の状態：Mathlib にある。

*主張*　lax モノイダル関手は、非単位的 lax モノイダル構造をもち、その構造に両側単位となる $`\mathbf1_{\mathcal D}\to F(\mathbf1_{\mathcal C})` が存在する関手である。

仮定：モノイダル圏 C, D と関手 F : C ⥤ D（Kerodon と一致）。結論：F(X) ⊗ F(Y) → F(X ⊗ Y) と 𝟙\_D → F(𝟙\_C) が自然性・結合・左右の単位条件を満たす lax 構造を与える（一致。Lean では単位射も場に持つ）。

:::

:::corollary "kerodon_2_1_5_10"
Kerodon Corollary 2.1.5.10（[Tag 00MU](https://kerodon.net/tag/00MU)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。lax 構造とコンマ圏のモノイダル構造の全単射は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::definition "kerodon_2_1_5_11" (lean := "CategoryTheory.Functor.OplaxMonoidal")
Kerodon Variant 2.1.5.11（[Tag 00MV](https://kerodon.net/tag/00MV)）。対応表の状態：Mathlib にある。

*主張*　colax モノイダル構造は反対関手の lax モノイダル構造である。非単位的 colax 構造に加えて、左右の単位の双対の式を満たす余単位 $`F(\mathbf1_{\mathcal C})\to\mathbf1_{\mathcal D}` を持つ。

仮定：モノイダル圏 C, D と関手 F : C ⥤ D（Kerodon と一致）。結論：F(X ⊗ Y) → F(X) ⊗ F(Y) と F(𝟙\_C) → 𝟙\_D が結合・左右の余単位条件を満たす oplax 構造を与える（一致）。

:::

:::proposition "kerodon_2_1_5_13"
Kerodon Proposition 2.1.5.13（[Tag 00DN](https://kerodon.net/tag/00DN)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。左単位の性質を単位対象での乗法整合と比較射のモノ性で特徴づける宣言は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::definition "kerodon_2_1_5_18" (lean := "CategoryTheory.NatTrans.IsMonoidal")
Kerodon Definition 2.1.5.18（[Tag 00DT](https://kerodon.net/tag/00DT)）。対応表の状態：Mathlib にある。

*主張*　lax モノイダル関手間のモノイダル自然変換は、テンソル制約の四角形を可換にし、単位の像を相手の単位に一致させる自然変換である。これらを射とする圏を $`\operatorname{Fun}^{\mathrm{lax}}(\mathcal C,\mathcal D)` と記す。

仮定：同じ二つのモノイダル圏の間の lax モノイダル関手 F₁, F₂ と自然変換 γ : F₁ ⟶ F₂（Kerodon と一致）。結論：γ がテンソル比較の正方形と単位比較の三角形を可換にするという述語（一致）。

:::

:::proposition "kerodon_2_1_5_23"
Kerodon Proposition 2.1.5.23（[Tag 02AQ](https://kerodon.net/tag/02AQ)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。代数の単位射の可逆性・対象のテンソル可逆性・左テンソルの充満忠実性の三条件の同値は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

# 2.1.6 Monoidal Functors

%%%
number := false
tag := "kerodon-2-1-6"
%%%

Kerodon [Tag 00DX](https://kerodon.net/tag/00DX)

:::definition "kerodon_2_1_6_1" (lean := "CategoryTheory.Functor.Monoidal")
Kerodon Definition 2.1.6.1（[Tag 00DY](https://kerodon.net/tag/00DY)）。対応表の状態：Mathlib にある。

*主張*　モノイダル関手とは、テンソル制約がすべて同型で、かつ単位 $`\mathbf1_{\mathcal D}\to F(\mathbf1_{\mathcal C})` も同型にとれる lax モノイダル関手である。

仮定：モノイダル圏 C, D と関手 F : C ⥤ D（Kerodon と一致）。結論：テンソル比較と単位比較が同型である構造を、互いに逆の lax・oplax 比較として持つ（一致）。

:::

:::definition "kerodon_2_1_6_9" (lean := "CategoryTheory.NatTrans.IsMonoidal")
Kerodon Notation 2.1.6.9（[Tag 00E6](https://kerodon.net/tag/00E6)）。対応表の状態：一部。

*主張*　モノイダル関手と単位・テンソルに両立する自然変換の圏を $`\operatorname{Fun}^{\otimes}(\mathcal C,\mathcal D)` と記す。これは lax モノイダル関手圏の充満部分圏であり、単位を忘れた関手圏の部分圏としては充満とは限らない。

B6：IsMonoidal の unit/tensor の二場は、強モノイダル関手間でも原文の射の二条件を直接与える。強関手を対象とする指定の充満部分圏の構成までは含まない。

:::

# 2.1.7 Enriched Category Theory

%%%
number := false
tag := "kerodon-2-1-7"
%%%

Kerodon [Tag 00ED](https://kerodon.net/tag/00ED)

:::definition "kerodon_2_1_7_1" (lean := "CategoryTheory.EnrichedCategory") (uses := "kerodon_2_1_2_17")
Kerodon Definition 2.1.7.1（[Tag 00EE](https://kerodon.net/tag/00EE)）。対応表の状態：一部。

*主張*　モノイダル圏 $`\mathcal A` に豊穣化した圏は、対象の集まりと、対象対ごとの $`\mathcal A` の Hom 対象をもつ。連続する Hom 対象のテンソルからの合成と、単位対象から自己 Hom への恒等射を指定し、結合子と単位制約に沿った結合・単位の恒等式を課す。

B6：EnrichedCategory.Hom と id は原文のデータ (2),(4) を直接持つ。comp のテンソル順は原文と逆なので、一般の V での合成則・結合則の一致は数えない。

:::

:::definition "kerodon_2_1_7_10" (lean := "CategoryTheory.EnrichedFunctor")
Kerodon Definition 2.1.7.10（[Tag 00JE](https://kerodon.net/tag/00JE)）。対応表の状態：一部。

*主張*　同じモノイダル圏 $`\mathcal A` に豊穣化された圏の間の豊穣関手は、対象の割り当てと Hom 対象間の $`\mathcal A` の射からなる。それらは豊穣合成と恒等射を保たなければならない。

B6：EnrichedFunctor の obj・map・map\_id は原文の対象写像・Hom 写像・恒等射保存を直接与える。非対称な V では合成のテンソル順が逆のため map\_comp の原文との比較は未確認。

:::

:::definition "kerodon_2_1_7_11"
Kerodon Notation 2.1.7.11（[Tag 00JF](https://kerodon.net/tag/00JF)）。対応表の状態：なし。

B6：EnrichedCat は逆順の合成規約の豊穣圏の束であり、用意されるのは双圏。原文の豊穣関手を射とする普通圏とその圏則は引用の型から直接得られない。

宣言：`CategoryTheory.EnrichedCat`

:::

