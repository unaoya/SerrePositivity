-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Basic
import Mathlib.AlgebraicTopology.SimplexCategory.Defs
import Mathlib.AlgebraicTopology.SimplexCategory.SemiSimplexCategory
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Shapes
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "10.1 Simplicial Objects of ∞-Categories" =>
%%%
number := false
tag := "kerodon-10-1"
%%%

Kerodon の 10.1 節（[Tag 04QJ](https://kerodon.net/tag/04QJ)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

:::definition "kerodon_10_1_0_1" (lean := "CategoryTheory.nerve")
Kerodon Definition 10.1.0.1（[Tag 04QK](https://kerodon.net/tag/04QK)）。対応表の状態：本体にある。

*主張*　無限圏 $`C` の単体対象は $`N(\boldsymbol\Delta^{\mathrm{op}})\to C` の関手である。余単体対象は $`N(\boldsymbol\Delta)\to C` の関手である。

CategoryTheory.nerveをΔop,Δへ適用した二つの単体集合からCへの射の型は、原文の単体・余単体対象の定義全体に一致する。既存の通常圏SimplicialObjectのみに依存せず、任意準圏Cを標的とする。専用名は不要。

:::

:::definition "kerodon_10_1_0_2" (lean := "CategoryTheory.nerve, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv")
Kerodon Notation 10.1.0.2（[Tag 04QL](https://kerodon.net/tag/04QL)）。対応表の状態：本体にある。

*主張*　無限圏の単体対象を $`X_\bullet`、その $`[n]` での値を $`X_n` と書く。余単体対象とその $`[n]` での値は $`X^\bullet,X^n` と書く。

同じnerve Δop,Δからの単体写像Fの0次成分をmk₀(\[n\])へ適用すれば、原文のXn,X\^nという次数評価を直接与える。通常圏の図式への限定は不要。

:::

:::definition "kerodon_10_1_0_4" (lean := "CategoryTheory.nerve, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv, CategoryTheory.nerve.edgeMk, SSet.Edge.map")
Kerodon Notation 10.1.0.4（[Tag 04QN](https://kerodon.net/tag/04QN)）。対応表の状態：本体にある。

*主張*　単体対象の退化作用素 $`s_i^n:X_n\to X_{n+1}` は $`i,i+1` を同一視する全射 $`[n+1]\to[n]` による。$`n>0` の面作用素 $`d_i^n:X_n\to X_{n-1}` は $`i` を飛ばす包含 $`[n-1]\to[n]` による。

同じFで、δi,σiの反対射をCategoryTheory.nerve.edgeMkに入れ、得られる辺をSSet.Edge.mapで写せば、原文の同じ面・退化作用素を直接得る。通常圏Cへの限定は不要。

:::

# 10.1.1 Geometric Realization

%%%
number := false
tag := "kerodon-10-1-1"
%%%

Kerodon [Tag 04QQ](https://kerodon.net/tag/04QQ)

:::proposition "kerodon_10_1_1_1"
Kerodon Proposition 10.1.1.1（[Tag 04QR](https://kerodon.net/tag/04QR)）。対応表の状態：なし。

B6再照合：toTop の Kan 拡張は標準単体の位相的実現から通常の圏で作る。離散集合 Sₙ の図式が位相空間の coherent nerve 内で持つ余極限の主張は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::definition "kerodon_10_1_1_2"
Kerodon Variant 10.1.1.2（[Tag 04QS](https://kerodon.net/tag/04QS)）。対応表の状態：なし。

B6再照合：Sing\|S\| の構成候補と 𝒮 の余極限一般を確認した。元の S の次数ごとの離散空間による余錐との比較が見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::definition "kerodon_10_1_1_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitVertexIso")
Kerodon Definition 10.1.1.3（[Tag 04QT](https://kerodon.net/tag/04QT)）。対応表の状態：本体にある。

*主張*　無限圏の単体対象の幾何学的実現は、その $`N(\boldsymbol\Delta^{\mathrm{op}})` 上の図式としての余極限である。

nerve Δopからの同じFについて∃c:JoinCocone F, c.vertex=X ∧ IsColimitCone cという型は、Xが実現であるという原文の定義全体に一致する。全図式の存在述語だけに限定せず、既存の指定余錐と頂点の型を用いる。

:::

:::definition "kerodon_10_1_1_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitVertexIso")
Kerodon Notation 10.1.1.5（[Tag 04QV](https://kerodon.net/tag/04QV)）。対応表の状態：一部。

*主張*　単体対象 $`X_\bullet` が幾何学的実現を持つとき、同型まで定まる実現を $`|X_\bullet|` と書く。集合の圏の神経を値域とするときのこの記法と、単体集合の位相的実現の記法は 10.1.1.4 で区別される。

colimitVertexIsoを同じnerve Δop図式の二つの余極限余錐へ適用すると、実現頂点の同型による一意性を直接得る。\|X•\|という専用記法・選択の構成は含まない。

:::

:::definition "kerodon_10_1_1_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitVertexIso")
Kerodon Variant 10.1.1.9（[Tag 04QZ](https://kerodon.net/tag/04QZ)）。対応表の状態：本体にある。

*主張*　無限圏の余単体対象の全化は、その $`N(\boldsymbol\Delta)` 上の図式としての極限である。存在すれば同型まで定まり、$`\operatorname{Tot}(X^\bullet)` と書く。

nerve Δからの同じFに∃c:JoinCone F, c.vertex=X ∧ IsLimitCone cを課せば原文の全化の定義そのもの。limitVertexIsoは二つのそのような頂点の同型も直接返す。Kan列の重み付きendという別模型を根拠から外した。

:::

:::definition "kerodon_10_1_1_10" (lean := "AugmentedSimplexCategory")
Kerodon Definition 10.1.1.10（[Tag 04R0](https://kerodon.net/tag/04R0)）。対応表の状態：Mathlib にある。

*主張*　増大単体圏 $`\boldsymbol\Delta_+` は、空の $`[-1]` を含むすべての標準有限全順序集合 $`[n]` と単調写像の圏である。

仮定：外部の値圏や有限極限の仮定なし。対象は有限全順序集合（Kerodon と一致）。結論：AugmentedSimplexCategory は WithInitial SimplexCategory。付加した始対象は原文の空順序集合 \[−1\]、既存の対象間は非減少写像で、空集合からは一意な射（同型な模型として一致）。

:::

:::definition "kerodon_10_1_1_12" (lean := "CategoryTheory.nerve, AugmentedSimplexCategory")
Kerodon Definition 10.1.1.12（[Tag 04R2](https://kerodon.net/tag/04R2)）。対応表の状態：本体にある。

*主張*　無限圏の増大単体対象は増大単体圏の反対圏の神経からの関手である。増大余単体対象は増大単体圏の神経からの関手である。

nerve AugmentedSimplexCategoryopおよびnerve AugmentedSimplexCategoryから任意の準圏Cへの射の型は、原文の増強単体・余単体対象の定義全体に一致する。通常圏のAugmentedとの比較を前提にしない。

:::

:::definition "kerodon_10_1_1_13" (lean := "CategoryTheory.nerve, AugmentedSimplexCategory, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv")
Kerodon Notation 10.1.1.13（[Tag 04R3](https://kerodon.net/tag/04R3)）。対応表の状態：本体にある。

*主張*　増大単体対象と増大余単体対象の $`[n]` における値を、それぞれ $`X_n`、$`X^n` と書く。この記法は空の順序集合に対応する $`n=-1` も含む。

同じ増強添字のnerveからのFの0次成分を指定次数の対象へ適用すれば、原文の増強単体・余単体対象の次数評価を直接与える。専用のXnという名前を不足としない。

:::

:::definition "kerodon_10_1_1_16"
Kerodon Definition 10.1.1.16（[Tag 04R6](https://kerodon.net/tag/04R6)）。対応表の状態：なし。

B6再照合：小さい Δᵒᵖ 図式の余極限存在は増強を引数に取らない。原文の次数 −1 の対象が実現を与えるという述語は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

# 10.1.2 Semisimplicial Objects

%%%
number := false
tag := "kerodon-10-1-2"
%%%

Kerodon [Tag 04R8](https://kerodon.net/tag/04R8)

:::definition "kerodon_10_1_2_1" (lean := "CategoryTheory.nerve, SemiSimplexCategory")
Kerodon Definition 10.1.2.1（[Tag 04R9](https://kerodon.net/tag/04R9)）。対応表の状態：本体にある。

*主張*　無限圏の半単体対象は $`N(\boldsymbol\Delta_{\mathrm{inj}}^{\mathrm{op}})` からの関手、余半単体対象は $`N(\boldsymbol\Delta_{\mathrm{inj}})` からの関手である。$`\boldsymbol\Delta_{\mathrm{inj}}` では単体圏の単射を用いる。

SemiSimplexCategoryは有限非空順序集合と狭義単調写像の圏。nerveをその反対圏および元の圏へ適用しCへの射を取れば、原文の半単体・余半単体対象の二つの定義全体になる。専用abbrevは不要。

:::

:::definition "kerodon_10_1_2_2" (lean := "SemiSimplexCategory, CategoryTheory.nerve")
Kerodon Notation 10.1.2.2（[Tag 04RA](https://kerodon.net/tag/04RA)）。対応表の状態：本体にある。

*主張*　無限圏の半単体対象 $`X_\bullet` の $`[n]` での値は $`X_n`、余半単体対象 $`X^\bullet` の $`[n]` での値は $`X^n` と書く。

同じnerve SemiSimplexCategoryopとnerve SemiSimplexCategoryからのFの0次成分を対象\[n\]へ適用すれば、原文の二つの次数評価を直接表す。専用の記法名は不要。

:::

:::proposition "kerodon_10_1_2_6"
Kerodon Proposition 10.1.2.6（[Tag 04RE](https://kerodon.net/tag/04RE)）。対応表の状態：なし。

B6再照合：半単体圏から単体圏への関手はある。通常圏での Initial インスタンスや nerve の左 cofinal 性を示す型は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::corollary "kerodon_10_1_2_7"
Kerodon Corollary 10.1.2.7（[Tag 04RF](https://kerodon.net/tag/04RF)）。対応表の状態：なし。

B6再照合：一般の制限による余極限移送はある。半単体圏の包含に必要な cofinal 性が見つからず、元の余錐と制限余錐の iff を採用できない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::definition "kerodon_10_1_2_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitVertexIso, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitVertexIso, SemiSimplexCategory, CategoryTheory.nerve")
Kerodon Definition 10.1.2.9（[Tag 04RH](https://kerodon.net/tag/04RH)）。対応表の状態：本体にある。

*主張*　無限圏の半単体対象の幾何学的実現は $`N(\boldsymbol\Delta_{\mathrm{inj}}^{\mathrm{op}})` 上の余極限である。余半単体対象の全化は $`N(\boldsymbol\Delta_{\mathrm{inj}})` 上の極限である。

同じ半単体図式Fへ頂点XのJoinCoconeとIsColimitConeの存在を課し、余半単体図式Gへ頂点XのJoinConeとIsLimitConeの存在を課せば原文の二つの定義全体になる。

:::

:::proposition "kerodon_10_1_2_11"
Kerodon Proposition 10.1.2.11（[Tag 04RK](https://kerodon.net/tag/04RK)）。対応表の状態：なし。

B6再照合：通常の単体的対象の次数評価には退化も含まれる。半単体的対象から定値対象への射を 0 次で単射に表し像を二つの面写像で与える型は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::corollary "kerodon_10_1_2_12"
Kerodon Corollary 10.1.2.12（[Tag 04RM](https://kerodon.net/tag/04RM)）。対応表の状態：なし。

B6再照合：通常の単体的対象の面写像はある。半単体的図式の nerve 内での余極限を二本の 1 次面写像の余等化子と同定する型は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::definition "kerodon_10_1_2_13"
Kerodon Notation 10.1.2.13（[Tag 04RN](https://kerodon.net/tag/04RN)）。対応表の状態：なし。

B6再照合：AugmentedSimplexCategory は単体圏全体に始対象を加える。単射だけの半単体圏に始対象を足した部分圏の名前付き構成は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::proposition "kerodon_10_1_2_14"
Kerodon Proposition 10.1.2.14（[Tag 04RP](https://kerodon.net/tag/04RP)）。対応表の状態：なし。

B6再照合：一般の押し出し正方形の判定はあるが、単体圏と半単体圏への始対象付加でできる四つの nerve に関する判定は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::definition "kerodon_10_1_2_15"
Kerodon Definition 10.1.2.15（[Tag 04RQ](https://kerodon.net/tag/04RQ)）。対応表の状態：なし。

B6再照合：通常圏で増強された単体的対象と Δ₊ᵒᵖ 上の図式を比較する同値はある。単射部分に制限した増強半単体的対象の定義は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::definition "kerodon_10_1_2_16"
Kerodon Notation 10.1.2.16（[Tag 04RR](https://kerodon.net/tag/04RR)）。対応表の状態：なし。

B6再照合：Δ₊ の次数 −1 の対象はある。Δinj,₊ 上の図式の次数評価記法は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::definition "kerodon_10_1_2_22"
Kerodon Variant 10.1.2.22（[Tag 04RX](https://kerodon.net/tag/04RX)）。対応表の状態：なし。

normalizedMooreComplexは非増強複体の構成。原文の次数−1を含む同じ増強複体と退化部分複体の商を構成せず、その商を非負次数へ制限した比較も引用の型にはない。

宣言：`AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex`、`AlgebraicTopology.normalizedMooreComplex`

:::

:::definition "kerodon_10_1_2_23"
Kerodon Definition 10.1.2.23（[Tag 04RY](https://kerodon.net/tag/04RY)）。対応表の状態：なし。

B6再照合：小さい Δᵒᵖ 図式の実現存在はある。増強半単体的図式の次数 −1 が Δinjᵒᵖ に制限した余極限であるという定義は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::proposition "kerodon_10_1_2_25"
Kerodon Proposition 10.1.2.25（[Tag 04S0](https://kerodon.net/tag/04S0)）。対応表の状態：なし。

B6再照合：通常の増強単体的対象を Δ₊ の図式と比較する同値はある。半単体版を指定の ε と二つの面に関する等式で特徴付ける型は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::corollary "kerodon_10_1_2_27"
Kerodon Corollary 10.1.2.27（[Tag 04S2](https://kerodon.net/tag/04S2)）。対応表の状態：なし。

B6再照合：既成の単体的対象の面恒等式はある。次数 −1 を含む面作用素の族から増強半単体的対象を復元する向きは見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::definition "kerodon_10_1_2_28" (lean := "AugmentedSimplexCategory, CategoryTheory.SimplicialObject.δ_comp_δ, CategoryTheory.SimplicialObject.σ_comp_σ, CategoryTheory.SimplicialObject.δ_comp_σ_of_le, CategoryTheory.SimplicialObject.δ_comp_σ_of_gt")
Kerodon Variant 10.1.2.28（[Tag 04S3](https://kerodon.net/tag/04S3)）。対応表の状態：一部。

*主張*　通常の圏で $`n\geq-1` の対象列 $`X_n` に面と退化の候補を与える。それらが増大単体対象を定めることは、面同士、退化同士、面と退化の標準単体恒等式を、増大写像 $`X_0\to X_{-1}` を含めて満たすことと同値であり、その増大単体対象は一意である。

増強単体的対象をdropした同じ非負次数の図式にδ\_comp\_δ等を適用すると、原文の必要条件(1)(2)(3)の増強次数を使わない恒等式を直接得る。次数−1を含む全恒等式と作用素からの復元・一意性は含まない。

:::

:::proposition "kerodon_10_1_2_29"
Kerodon Proposition 10.1.2.29（[Tag 04S4](https://kerodon.net/tag/04S4)）。対応表の状態：なし。

B6再照合：半単体圏から単体圏への包含は定義される。有限余積だけから、指定の半単体的対象を自由に退化させる左 Kan 拡張の存在は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

# 10.1.3 Skeletal Simplicial Objects

%%%
number := false
tag := "kerodon-10-1-3"
%%%

Kerodon [Tag 05G3](https://kerodon.net/tag/05G3)

:::definition "kerodon_10_1_3_1" (lean := "CategoryTheory.nerve, SSet.const, SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso")
Kerodon Definition 10.1.3.1（[Tag 05G4](https://kerodon.net/tag/05G4)）。対応表の状態：本体にある。

*主張*　無限圏の対象 $`c` に対し、全次数で $`c` に一定な関手を定数単体対象とする。ある定数単体対象と単体対象の関手圏で同型なものを本質的に定数と呼ぶ。

SSet.constで同じnerve Δopから定値頂点Cへの図式を作り、F=SSet.const Cの存在量化とNonempty(FunctorIso F (SSet.const C))の存在量化をそれぞれ取れば、constantとessentially constantの定義全体を直接表す。

:::

:::proposition "kerodon_10_1_3_2"
Kerodon Proposition 10.1.3.2（[Tag 05G5](https://kerodon.net/tag/05G5)）。対応表の状態：なし。

B6再照合：弱可縮な添字上の定値図式の極限性は別の主張。全ての射を同型に送ることから単体的対象の定値性を回収する iff は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::definition "kerodon_10_1_3_3" (lean := "SimplexCategory.Truncated")
Kerodon Notation 10.1.3.3（[Tag 05G6](https://kerodon.net/tag/05G6)）。対応表の状態：一部。

*主張*　整数 $`n` に対し、単体圏のうち $`0\leq m\leq n` を満たす $`[m]` で張る充満部分圏を $`\boldsymbol\Delta^{\leq n}` と書く。

n≥0に限るとSimplexCategory.Truncated nは原文の同じ次数≤nの充満部分圏そのもの。負のnにおける空圏の場合はこの引用に含まない。

:::

:::definition "kerodon_10_1_3_4" (lean := "SimplexCategory.Truncated.inclusion, CategoryTheory.nerveMap, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone")
Kerodon Definition 10.1.3.4（[Tag 05G7](https://kerodon.net/tag/05G7)）。対応表の状態：一部。

*主張*　無限圏の単体対象は、$`N(\boldsymbol\Delta^{\leq n})^{\mathrm{op}}` から左 Kan 拡張されているとき $`n`-骨格的である。

n≥0に限りnerveMap ((Truncated.inclusion n).op)をδとして、各頂点のleftKanCanonicalCocone δ FにIsColimitConeを課すと、原文の同じn-skeletalという定義を直接表す。通常圏skの随伴を∞圏の結果と見なさず、負次数は含まない。

:::

:::definition "kerodon_10_1_3_10"
Kerodon Construction 10.1.3.10（[Tag 05GD](https://kerodon.net/tag/05GD)）。対応表の状態：なし。

B6再照合：骨格関手は切断に沿う左 Kan 拡張。部分集合 J で指定する退化商 \[k\]↠\[m\] を一つの立方体に集める構成は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::definition "kerodon_10_1_3_12"
Kerodon Notation 10.1.3.12（[Tag 05GF](https://kerodon.net/tag/05GF)）。対応表の状態：なし。

B6再照合：次数 m≤n の対象の部分圏はある。固定した \[k\] を始域とする写像を対象とする、切断された coslice の記法は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::lemma_ "kerodon_10_1_3_13"
Kerodon Lemma 10.1.3.13（[Tag 05GG](https://kerodon.net/tag/05GG)）。対応表の状態：なし。

B6再照合：skAdj は切断と延長の随伴。大きさ ≤n の部分集合の poset から切断 coslice の反対圏への指定関手の右 cofinal 性は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::proposition "kerodon_10_1_3_14"
Kerodon Proposition 10.1.3.14（[Tag 05GH](https://kerodon.net/tag/05GH)）。対応表の状態：なし。

B6再照合：skAdj は通常圏での切断に沿う随伴。原文の各 k の退化立方体の余極限性を用いる iff は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::corollary "kerodon_10_1_3_16"
Kerodon Corollary 10.1.3.16（[Tag 05GK](https://kerodon.net/tag/05GK)）。対応表の状態：なし。

B6再照合：Mathlib の sk n は一つの切断の延長。隣り合う n と n−1 の骨格性を第 n 退化立方体の余極限で比較する型は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::corollary "kerodon_10_1_3_17"
Kerodon Corollary 10.1.3.17（[Tag 05GL](https://kerodon.net/tag/05GL)）。対応表の状態：なし。

B6再照合：左 Kan 拡張を作る通常圏の随伴はある。押し出し保存だけを仮定して n-skeletal 性を写す型は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::definition "kerodon_10_1_3_18" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge, SSet.Edge.map")
Kerodon Definition 10.1.3.18（[Tag 05GM](https://kerodon.net/tag/05GM)）。対応表の状態：一部。

*主張*　無限圏の単体対象の射 $`Y_\bullet\to X_\bullet` が $`Y_\bullet` を $`X_\bullet` の $`n` 次骨格として示すとは、$`Y_\bullet` が $`n`-骨格的で、$`0\leq m\leq n` で $`Y_m\to X_m` が同型であることをいう。

同じuの各0≤m≤nでの辺がIsInvertibleEdgeであるという既存の判定を課せば原文の二番目の条件を直接表す。通常圏のskAdjだけでYの∞圏のn-skeletal性を得たとはしない。

:::

:::proposition "kerodon_10_1_3_23"
Kerodon Proposition 10.1.3.23（[Tag 05GS](https://kerodon.net/tag/05GS)）。対応表の状態：なし。

通常圏で左Kan拡張の存在を入力してskを構成する型は、原文の準圏のpushoutだけから同じ指定図式のn-skeletonが存在するという結論を直接返さない。

宣言：`CategoryTheory.SimplicialObject.sk`、`CategoryTheory.SimplicialObject.skAdj`

:::

# 10.1.4 Coskeletal Simplicial Objects

%%%
number := false
tag := "kerodon-10-1-4"
%%%

Kerodon [Tag 05GU](https://kerodon.net/tag/05GU)

:::definition "kerodon_10_1_4_1"
Kerodon Definition 10.1.4.1（[Tag 04SW](https://kerodon.net/tag/04SW)）。対応表の状態：なし。

B6再照合：有限積を仮定して通常圏の Čech nerve を構成する宣言はある。指定された∞単体的対象の各次数が 0 次対象の積であることを定義する型は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::definition "kerodon_10_1_4_3"
Kerodon Definition 10.1.4.3（[Tag 04SY](https://kerodon.net/tag/04SY)）。対応表の状態：なし。

B6型照合：Mathlib に有限積をもつ 1 圏の対象の Čech nerve（cechNerveTerminalFrom）のみ。 通常圏の候補から、原文で指定された準圏の同じ対象・射・述語へ比較する型を確認していないためnone。

宣言：`CategoryTheory.cechNerveTerminalFrom`

:::

:::definition "kerodon_10_1_4_4"
Kerodon Notation 10.1.4.4（[Tag 04SZ](https://kerodon.net/tag/04SZ)）。対応表の状態：なし。

B6型照合：記法。Mathlib には 1 圏の版のみ（∞ 圏版なし）。 通常圏の候補から、原文で指定された準圏の同じ対象・射・述語へ比較する型を確認していないためnone。

宣言：`CategoryTheory.cechNerveTerminalFrom`

:::

:::proposition "kerodon_10_1_4_5"
Kerodon Proposition 10.1.4.5（[Tag 04T0](https://kerodon.net/tag/04T0)）。対応表の状態：なし。

B6再照合：通常圏全体の有限積を仮定した構成はある。指定された一対象の非空有限べきの存在との iff は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::corollary "kerodon_10_1_4_6"
Kerodon Corollary 10.1.4.6（[Tag 04T1](https://kerodon.net/tag/04T1)）。対応表の状態：なし。

B6型照合：Mathlib は HasFiniteProducts な 1 圏で構成。 通常圏の候補から、原文で指定された準圏の同じ対象・射・述語へ比較する型を確認していないためnone。

宣言：`CategoryTheory.cechNerveTerminalFrom`

:::

:::corollary "kerodon_10_1_4_8"
Kerodon Corollary 10.1.4.8（[Tag 04T3](https://kerodon.net/tag/04T3)）。対応表の状態：なし。

cechNerveAdjunctionの左側は通常圏Augmented.toArrowであり、原文の非増強図式の0次評価と同じ関手ではない。その随伴を原文のspecialと数えない。

宣言：`CategoryTheory.SimplicialObject.cechNerveAdjunction`

:::

:::definition "kerodon_10_1_4_9" (lean := "SimplexCategory.Truncated.inclusion, CategoryTheory.nerveMap, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone")
Kerodon Definition 10.1.4.9（[Tag 05GV](https://kerodon.net/tag/05GV)）。対応表の状態：一部。

*主張*　無限圏の単体対象は、$`N(\boldsymbol\Delta^{\leq n})^{\mathrm{op}}` から右 Kan 拡張されているとき $`n`-余骨格的である。

n≥0に限りδを同じ切断包含の反対のnerveMapとして、各rightKanCanonicalCone δ FへIsLimitConeを課せば、原文の同じn-coskeletal条件を直接表す。通常圏coskとの輸送は使わず、負次数は含まない。

:::

:::definition "kerodon_10_1_4_14"
Kerodon Variant 10.1.4.14（[Tag 05H0](https://kerodon.net/tag/05H0)）。対応表の状態：なし。

B6再照合：右 Kan 延長の述語の添字は通常の Δᵒᵖ。狭義単調写像だけを持つ Δinj の切断に沿う余骨格性は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::proposition "kerodon_10_1_4_15"
Kerodon Proposition 10.1.4.15（[Tag 05H1](https://kerodon.net/tag/05H1)）。対応表の状態：なし。

通常圏のcosk単位の同型性による判定は、原文の半単体への制限に沿う同じn-coskeletal性のiffとは異なる条件。

宣言：`CategoryTheory.SimplicialObject.isCoskeletal_iff_isIso`

:::

:::corollary "kerodon_10_1_4_16"
Kerodon Corollary 10.1.4.16（[Tag 05H2](https://kerodon.net/tag/05H2)）。対応表の状態：なし。

B6再照合：通常圏の単体的対象の IsCoskeletal と右 Kan 拡張はある。有限極限保存で単体・半単体の双方の余骨格性が移る結果は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::definition "kerodon_10_1_4_17" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge, SSet.Edge.map")
Kerodon Definition 10.1.4.17（[Tag 05H3](https://kerodon.net/tag/05H3)）。対応表の状態：一部。

*主張*　無限圏の単体対象の射 $`X_\bullet\to Y_\bullet` が $`Y_\bullet` を $`X_\bullet` の $`n` 次余骨格として示すとは、$`Y_\bullet` が $`n`-余骨格的で、$`0\leq m\leq n` で $`X_m\to Y_m` が同型であることをいう。

同じuの各0≤m≤nでの辺にIsInvertibleEdgeを課す型は原文の二番目の条件を直接表す。原文のYのn-coskeletal性を通常圏coskだけから得たとはしない。

:::

:::proposition "kerodon_10_1_4_21"
Kerodon Proposition 10.1.4.21（[Tag 05H7](https://kerodon.net/tag/05H7)）。対応表の状態：なし。

B6型照合：Mathlib は 1 圏で右 Kan 拡張の存在を仮定して cosk を定義。∞ 圏の存在定理なし。 通常圏の候補から、原文で指定された準圏の同じ対象・射・述語へ比較する型を確認していないためnone。

宣言：`CategoryTheory.SimplicialObject.cosk`、`CategoryTheory.SimplicialObject.coskAdj`

:::

# 10.1.5 The Nerve of a Morphism

%%%
number := false
tag := "kerodon-10-1-5"
%%%

Kerodon [Tag 04SV](https://kerodon.net/tag/04SV)

:::definition "kerodon_10_1_5_1"
Kerodon Definition 10.1.5.1（[Tag 04T4](https://kerodon.net/tag/04T4)）。対応表の状態：なし。

B6再照合：指定の射から通常圏の増強対象を構成する宣言はある。与えられた対象が増強先の∞スライスで Čech nerve となる述語は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::definition "kerodon_10_1_5_4"
Kerodon Definition 10.1.5.4（[Tag 04T7](https://kerodon.net/tag/04T7)）。対応表の状態：なし。

B6型照合：Mathlib に 1 圏の射の Čech nerve（wide pullback で構成）のみ。 通常圏の候補から、原文で指定された準圏の同じ対象・射・述語へ比較する型を確認していないためnone。

宣言：`CategoryTheory.Arrow.augmentedCechNerve`、`CategoryTheory.Arrow.cechNerve`

:::

:::definition "kerodon_10_1_5_5"
Kerodon Notation 10.1.5.5（[Tag 04T8](https://kerodon.net/tag/04T8)）。対応表の状態：なし。

B6型照合：記法。Mathlib には 1 圏の版のみ（∞ 圏版なし）。 通常圏の候補から、原文で指定された準圏の同じ対象・射・述語へ比較する型を確認していないためnone。

宣言：`CategoryTheory.Arrow.augmentedCechNerve`

:::

:::proposition "kerodon_10_1_5_6"
Kerodon Proposition 10.1.5.6（[Tag 04T9](https://kerodon.net/tag/04T9)）。対応表の状態：なし。

B6型照合：Mathlib は wide pullback の存在を仮定した 1 圏版。 通常圏の候補から、原文で指定された準圏の同じ対象・射・述語へ比較する型を確認していないためnone。

宣言：`CategoryTheory.Arrow.augmentedCechNerve`

:::

:::corollary "kerodon_10_1_5_8"
Kerodon Corollary 10.1.5.8（[Tag 04TB](https://kerodon.net/tag/04TB)）。対応表の状態：なし。

B6型照合：Mathlib に 1 圏の随伴 Augmented.toArrow ⊣ augmentedCechNerve。 通常圏の候補から、原文で指定された準圏の同じ対象・射・述語へ比較する型を確認していないためnone。

宣言：`CategoryTheory.SimplicialObject.cechNerveAdjunction`

:::

:::definition "kerodon_10_1_5_9" (lean := "AugmentedSimplexCategory, CategoryTheory.ObjectProperty.FullSubcategory")
Kerodon Notation 10.1.5.9（[Tag 05H8](https://kerodon.net/tag/05H8)）。対応表の状態：一部。

*主張*　整数 $`n` に対し、増大単体圏で $`-1\leq m\leq n` を満たす $`[m]` が張る充満部分圏を $`\boldsymbol\Delta_+^{\leq n}` と書く。

n≥0に限りAugmentedSimplexCategory上のObjectProperty.FullSubcategoryを、次数の対象が−1または0..nである述語で取れば原文の同じ切断部分圏を直接構成する。負次数の範囲全体は含まない。

:::

:::definition "kerodon_10_1_5_10"
Kerodon Definition 10.1.5.10（[Tag 05H9](https://kerodon.net/tag/05H9)）。対応表の状態：なし。

B6再照合：切断する添字は増強されていない Δᵒᵖ。次数 −1 を含む右 Kan 延長としての余骨格性は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::definition "kerodon_10_1_5_14"
Kerodon Variant 10.1.5.14（[Tag 05HD](https://kerodon.net/tag/05HD)）。対応表の状態：なし。

B6再照合：通常圏の IsCoskeletal の切断には退化があり増強次数がない。Δinj,₊ の狭義単調写像を使う版は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::definition "kerodon_10_1_5_18"
Kerodon Construction 10.1.5.18（[Tag 05HH](https://kerodon.net/tag/05HH)）。対応表の状態：なし。

B6再照合：切断に沿う右 Kan 延長はある。部分集合に対応する面を取り、空部分集合も含む反対立方体を作る型は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::proposition "kerodon_10_1_5_20"
Kerodon Proposition 10.1.5.20（[Tag 05HK](https://kerodon.net/tag/05HK)）。対応表の状態：なし。

B6再照合：右 Kan 拡張による通常の余骨格性はある。増強半単体的対象で全ての指定面立方体が極限であることとの iff は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::corollary "kerodon_10_1_5_21"
Kerodon Corollary 10.1.5.21（[Tag 05HL](https://kerodon.net/tag/05HL)）。対応表の状態：なし。

B6再照合：通常の余骨格随伴は一つの切断を用いる。増強図式の n と n−1 の比較に一つの面立方体の極限を使う型は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::corollary "kerodon_10_1_5_22"
Kerodon Corollary 10.1.5.22（[Tag 05HM](https://kerodon.net/tag/05HM)）。対応表の状態：なし。

B6再照合：通常の余骨格性は右 Kan 延長として定義される。引き戻しの保存だけで増強された余骨格性が保たれる型は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

# 10.1.6 Split Simplicial Objects

%%%
number := false
tag := "kerodon-10-1-6"
%%%

Kerodon [Tag 04S6](https://kerodon.net/tag/04S6)

:::definition "kerodon_10_1_6_1"
Kerodon Notation 10.1.6.1（[Tag 04S7](https://kerodon.net/tag/04S7)）。対応表の状態：なし。

B6再照合：追加退化は射と恒等式のデータ。最小元を保つ順序写像だけを持つ Δ\_min の構成は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::definition "kerodon_10_1_6_3"
Kerodon Definition 10.1.6.3（[Tag 04S9](https://kerodon.net/tag/04S9)）。対応表の状態：なし。

B6型照合：Mathlib の 1 圏の ExtraDegeneracy が split 増強単体的対象に相当（Δ\_min\^op への延長としての定義ではない）。Mathlib の Splitting は Dold–Kan 型の分解で別概念。 通常圏の候補から、原文で指定された準圏の同じ対象・射・述語へ比較する型を確認していないためnone。

宣言：`CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy`

:::

:::definition "kerodon_10_1_6_7"
Kerodon Variant 10.1.6.7（[Tag 04SF](https://kerodon.net/tag/04SF)）。対応表の状態：なし。

ExtraDegeneracyは追加退化の元のデータであり、原文の同じ増強正規化複体への降下とそのcontracting homotopyを返す型ではない。

宣言：`CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy`

:::

:::proposition "kerodon_10_1_6_9"
Kerodon Proposition 10.1.6.9（[Tag 04SH](https://kerodon.net/tag/04SH)）。対応表の状態：なし。

鎖複体のhomotopyEquivは原文の同じ増強図式の準圏内の余極限性とは異なる結論。比較なしにpartialと数えない。

宣言：`CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv`

:::

:::definition "kerodon_10_1_6_11"
Kerodon Variant 10.1.6.11（[Tag 04SK](https://kerodon.net/tag/04SK)）。対応表の状態：なし。

B6型照合：1 圏の ExtraDegeneracy のみ。 通常圏の候補から、原文で指定された準圏の同じ対象・射・述語へ比較する型を確認していないためnone。

宣言：`CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy`

:::

:::corollary "kerodon_10_1_6_13"
Kerodon Corollary 10.1.6.13（[Tag 04SM](https://kerodon.net/tag/04SM)）。対応表の状態：なし。

B6再照合：加法圏の鎖複体のホモトピー同値はある。任意の∞圏での実現の存在と、全関手による保存を述べる型は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::proposition "kerodon_10_1_6_14"
Kerodon Proposition 10.1.6.14（[Tag 05HN](https://kerodon.net/tag/05HN)）。対応表の状態：なし。

B6型照合：Mathlib に 1 圏で両向き（split epi ⇒ Čech nerve に extra degeneracy、extra degeneracy ⇒ split epi）。∞ 圏版なし。 通常圏の候補から、原文で指定された準圏の同じ対象・射・述語へ比較する型を確認していないためnone。

宣言：`CategoryTheory.Arrow.AugmentedCechNerve.extraDegeneracy`、`CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy.splitEpi`

:::

:::corollary "kerodon_10_1_6_15"
Kerodon Corollary 10.1.6.15（[Tag 04TL](https://kerodon.net/tag/04TL)）。対応表の状態：なし。

B6再照合：通常圏の分裂エピから Čech nerve の追加退化を作る。右ホモトピー逆を仮定した∞圏の余極限性は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::definition "kerodon_10_1_6_16"
Kerodon Notation 10.1.6.16（[Tag 05HP](https://kerodon.net/tag/05HP)）。対応表の状態：なし。

B6再照合：通常の単体圏の次数切断は最小元を保たない射も持つ。Δ\_min に限定する原文の部分圏は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::lemma_ "kerodon_10_1_6_19"
Kerodon Lemma 10.1.6.19（[Tag 04TE](https://kerodon.net/tag/04TE)）。対応表の状態：なし。

B6再照合：追加退化のデータはあるが、Δ\_minᵒᵖ への指定延長の右 Kan 性を増強対象の余骨格性と比較する型は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::definition "kerodon_10_1_6_20"
Kerodon Variant 10.1.6.20（[Tag 04TF](https://kerodon.net/tag/04TF)）。対応表の状態：なし。

B6再照合：通常の Δ の切断に沿う右随伴はある。切断された Δ\_min 上の関手と増強側の延長条件の同値は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::proposition "kerodon_10_1_6_21"
Kerodon Proposition 10.1.6.21（[Tag 04TG](https://kerodon.net/tag/04TG)）。対応表の状態：なし。

B6再照合：個別の追加退化を保持する構造はある。余骨格的な増強図式の充満部分圏と切断 Δ\_min 上の関手圏との比較は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

:::definition "kerodon_10_1_6_22"
Kerodon Construction 10.1.6.22（[Tag 04SN](https://kerodon.net/tag/04SN)）。対応表の状態：なし。

B6再照合：追加退化のデータはある。単体的対象を添字の連結で前合成して作る増強 Dec₊ の構成は見つからない。 同じ対象・射の結論への比較がなく、証明の材料または別模型の結果だけとは数えない。

:::

