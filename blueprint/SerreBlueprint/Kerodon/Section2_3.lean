-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "2.3 The Duskin Nerve of a Bicategory" =>
%%%
number := false
tag := "kerodon-2-3"
%%%

Kerodon の 2.3 節（[Tag 009P](https://kerodon.net/tag/009P)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

# 2.3.1 The Duskin Nerve

%%%
number := false
tag := "kerodon-2-3-1"
%%%

Kerodon [Tag 009T](https://kerodon.net/tag/009T)

:::definition "kerodon_2_3_1_1" (uses := "kerodon_1_1_0_6, kerodon_2_2_4_17")
Kerodon Construction 2.3.1.1（[Tag 009U](https://kerodon.net/tag/009U)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。厳密単位的 lax 関手の型はあるが、双圏に対する Duskin nerve の単体集合は TODO。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::proposition "kerodon_2_3_1_9" (uses := "kerodon_2_2_1_14, kerodon_2_2_1_15")
Kerodon Proposition 2.3.1.9（[Tag 00A2](https://kerodon.net/tag/00A2)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。対象・辺・2射と四頂点での整合から Duskin 単体を一意に組み立てる宣言は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::corollary "kerodon_2_3_1_10"
Kerodon Corollary 2.3.1.10（[Tag 00A3](https://kerodon.net/tag/00A3)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。Duskin nerve の境界制限が次元4以上で全単射、次元3で単射という宣言は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

# 2.3.2 From Bicategories to ∞-Categories

%%%
number := false
tag := "kerodon-2-3-2"
%%%

Kerodon [Tag 00AB](https://kerodon.net/tag/00AB)

:::theorem "kerodon_2_3_2_1"
Kerodon Theorem 2.3.2.1（[Tag 00AC](https://kerodon.net/tag/00AC)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。局所亜群性の型はあるが、Duskin nerve の準圏性との同値は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::definition "kerodon_2_3_2_3" (uses := "kerodon_1_1_0_6")
Kerodon Definition 2.3.2.3（[Tag 00AD](https://kerodon.net/tag/00AD)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。指定の連続3頂点上で固定した2単体に対する内角充填の述語は未発見。Quiver.IsThin は Hom の高々一意性。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::theorem "kerodon_2_3_2_5"
Kerodon Theorem 2.3.2.5（[Tag 00AF](https://kerodon.net/tag/00AF)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。Duskin nerve の2単体の薄さと対応2射の可逆性の同値は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::corollary "kerodon_2_3_2_7"
Kerodon Corollary 2.3.2.7（[Tag 00AH](https://kerodon.net/tag/00AH)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。Duskin nerve の退化2単体の薄さを示す宣言は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::corollary "kerodon_2_3_2_8"
Kerodon Corollary 2.3.2.8（[Tag 00AJ](https://kerodon.net/tag/00AJ)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。双圏の擬関手による Duskin nerve の薄い2単体の保存は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

# 2.3.3 Thin 2-Simplices of a Duskin Nerve

%%%
number := false
tag := "kerodon-2-3-3"
%%%

Kerodon [Tag 00AQ](https://kerodon.net/tag/00AQ)

:::proposition "kerodon_2_3_3_1"
Kerodon Proposition 2.3.3.1（[Tag 00AR](https://kerodon.net/tag/00AR)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。指定2面の可逆2射から Duskin の内角の一意充填を得る宣言は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::proposition "kerodon_2_3_3_2"
Kerodon Proposition 2.3.3.2（[Tag 00AS](https://kerodon.net/tag/00AS)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。次元3・4の指定内角の充填から比較2射の可逆性を導く宣言は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

# 2.3.4 Recovering a Bicategory from its Duskin Nerve

%%%
number := false
tag := "kerodon-2-3-4"
%%%

Kerodon [Tag 00AT](https://kerodon.net/tag/00AT)

:::theorem "kerodon_2_3_4_1"
Kerodon Theorem 2.3.4.1（[Tag 00AU](https://kerodon.net/tag/00AU)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。Duskin nerve の単体写像と厳密単位的 lax 関手の全単射は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::corollary "kerodon_2_3_4_5"
Kerodon Corollary 2.3.4.5（[Tag 00AX](https://kerodon.net/tag/00AX)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。薄い2単体を保つ nerve 写像と擬関手の全単射は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::corollary "kerodon_2_3_4_6"
Kerodon Corollary 2.3.4.6（[Tag 02BG](https://kerodon.net/tag/02BG)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。Duskin nerve のホモトピー圏と粗ホモトピー圏との比較は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

# 2.3.5 The Duskin Nerve of a Strict Bicategory

%%%
number := false
tag := "kerodon-2-3-5"
%%%

Kerodon [Tag 00B9](https://kerodon.net/tag/00B9)

:::definition "kerodon_2_3_5_1"
Kerodon Construction 2.3.5.1（[Tag 00BA](https://kerodon.net/tag/00BA)）。対応表の状態：なし。

B6：Path は任意 LinearOrder の端点付き部分集合で有限性を要求せず、射も包含で原文の逆包含と反対。compFunctor の和集合は類似模型の部品であり原文の有限鎖双圏を直接構成しない。

宣言：`CategoryTheory.SimplicialThickening.Path`、`CategoryTheory.SimplicialThickening.compFunctor`

:::

:::definition "kerodon_2_3_5_4"
Kerodon Construction 2.3.5.4（[Tag 00BC](https://kerodon.net/tag/00BC)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。各比較可能対を端点だけの鎖に送り、逆包含を合成制約に使う指定の lax 関手は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::theorem "kerodon_2_3_5_6" (uses := "kerodon_2_2_4_5, kerodon_2_3_5_4")
Kerodon Theorem 2.3.5.6（[Tag 00BE](https://kerodon.net/tag/00BE)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。T\_Q に沿う制限による厳密関手と厳密単位的 lax 関手の全単射は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

:::corollary "kerodon_2_3_5_7"
Kerodon Corollary 2.3.5.7（[Tag 00BF](https://kerodon.net/tag/00BF)）。対応表の状態：なし。

B6：現本体・固定Mathlibを再検索。局所的 nerve を取った双圏の coherent nerve と Duskin nerve の同型は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。

:::

