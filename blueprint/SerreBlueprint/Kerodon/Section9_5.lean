-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Limits.Indization.Category
import Mathlib.Order.CompleteLattice.Defs
import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.AdjointRepresentability
import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Reflective
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveLocalization
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.Accessibility
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.Accessible
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.PresentationAssembly
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.FiniteColimitClosureUnconditional
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndComparisonFullyFaithful
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndLeftKanPreservation
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AccessibleCorepresentability
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AdjointFunctorTheorem
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.BousfieldReflection
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.BousfieldSaturation
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.BousfieldUniversalProperty
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorPresentable
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndCardinalChange
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LocalObjects
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NativeAdjointFunctorCriterion
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrInfinity
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.Presentable
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableEquivalence
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentablePresheafReflection
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentablePullback
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableSmallLimits
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafPresentable
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallGeneratorPresentation
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ReflectionSmallLimits
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.LocallySmall

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "9.5 Presentable ∞-Categories" =>
%%%
number := false
tag := "kerodon-9-5"
%%%

Kerodon の 9.5 節（[Tag 06NC](https://kerodon.net/tag/06NC)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

:::proposition "kerodon_9_5_0_1" (lean := "isLUB_sSup")
Kerodon Proposition 9.5.0.1（[Tag 06PT](https://kerodon.net/tag/06PT)）。対応表の状態：Mathlib にある。

*主張*　完備束の任意の部分集合は最小上界を持つ。

仮定：CompleteSemilatticeSup と任意の部分集合 s。原文は完備束なので下限も持つ（Lean が弱い）。結論：isLUB\_sSup s は sSup s が s の最小上界であること（原文と一致）。

:::

# 9.5.1 Presentable ∞-Categories

%%%
number := false
tag := "kerodon-9-5-1"
%%%

Kerodon [Tag 06NE](https://kerodon.net/tag/06NE)

*06-catinfty-ind-presentable.html — 6. accessible と presentable*

\`\`\`text
def IsKappaAccessible (κ : Cardinal.\{u\}) (C : SSet.\{u + 1\}) \[Quasicategory C\] : Prop
  -- κ 正則、小さい κ-filtered 余極限を持ち、小さい κ-compact 生成圏を持つ
def IsAccessible (C : SSet.\{u + 1\}) \[Quasicategory C\] : Prop
\`\`\`

完成：$`\mathrm{Ind}_\kappa(A)` の accessibility、κ-compact 対象が生成対象の retract であること、小さい Ind との同値による特徴づけ（\`isKappaAccessible\_iff\_indEquivalence\`）、濃度の変更、accessible 関手（HTT §5.4.2、F2/Presentable）。

作業中（P-1 b〜g）：presentable の定義と前層・Ind の presentable 性、極限・余極限の存在、随伴関手定理、Pr\<sup\>L\</sup\>/Pr\<sup\>R\</sup\>、Bousfield 局所化の存在、P\<sub\>Σ\</sub\> の普遍性。局所対象・強飽和性と P\<sub\>Σ\</sub\> の準備は HomotopyLimits/ にある（第 5 章）。

*f-d-adjoint-presentable.html — 4. 表現可能性定理*

注意：以前「再帰的局所化」と書いたのは誤記で、正しくは反射的局所化（reflective localization）。

*f-d-adjoint-presentable.html — 4. 表現可能性定理 — 4.1 用語*

- 用語　／　定義
- $`C_0`　／　$`C` の小さい充満部分圏で $`C` を余極限で生成するもの。標準的には十分大きい正則基数 $`\kappa` で $`C_0=C^\kappa`（$`\mathrm{Map}(c,-)` が $`\kappa`-filtered 余極限を保つ対象の全体、本質的に小さい）
- 反射的局所化　／　充満部分圏の包含 $`i\colon C\hookrightarrow E` が左随伴 $`L`（反射、局所化関手）をもつこと。$`L\circ i\simeq\mathrm{id}`。アクセシブルとは $`i` が $`\kappa`-filtered 余極限を保つこと。例：層化 $`\mathrm{Sh}\subseteq\mathrm{PSh}`
- 局所対象　／　射の集合 $`S` について、すべての $`s\colon A\to B` で $`\mathrm{Map}(B,Z)\to\mathrm{Map}(A,Z)` が同値な $`Z`。反射的部分圏 $`C\subseteq E` はちょうど $`L`-同値に関する局所対象の全体。層の条件は「被覆篩 $`\to` 表現可能前層」に関する局所性
- 稠密性　／　$`F\in\mathcal P(C_0)` は表現可能前層の余極限 $`F\simeq\operatorname{colim}_{(c,x\in F(c))}h_c`（∞ 版では $`\mathrm{Un}(F)\to C_0` と Yoneda 埋め込みの合成の余極限）。証明は $`\mathrm{Map}(\operatorname{colim}h_c,G)\simeq\lim G(c)\simeq\mathrm{Map}(F,G)`（形式化：PresheafDensity 以下）
- Lurie–Simpson の特徴づけ（HTT 5.5.1.1）　／　(1) $`C` は presentable。(2) ある小さい $`C_0` で $`C` は $`\mathcal P(C_0)` のアクセシブルな反射的局所化。(3) ある小さい $`C_0` と射の小さい集合 $`S` で $`C\simeq S^{-1}\mathcal P(C_0)`。この三つは同値

*f-d-adjoint-presentable.html — 4. 表現可能性定理 — 4.2 二つの向きの役割*

- *(1)⇒(2)*（表現可能性定理の手順 1）：比較的初等的。$`C_0=C^\kappa`、$`\nu\colon C\to\mathcal P(C_0)`、$`X\mapsto\mathrm{Map}_C(-,X)|_{C_0}`。$`C\simeq\mathrm{Ind}_\kappa(C^\kappa)` から $`\nu` は充満忠実。左随伴 $`L` は包含 $`C_0\hookrightarrow C` の Yoneda 埋め込みに沿った左 Kan 拡張（$`C` が余完備なので存在）。$`\nu` が $`\kappa`-filtered 余極限を保つのでアクセシブル。

- *(3)⇒(1)* で使う「局所化の存在」（HTT 5.5.4.15）：任意の小さい $`S` で $`S`-局所対象が反射的部分圏をなし presentable になる。反射 $`L` を作るのに small object argument の ∞ 版が要る重い部分で、新しい presentable 圏を作るときに使う。

表現可能性定理には (1)⇒(2) しか要らない。presentability の理論全体では Lurie–Simpson と局所化の存在が重いが、表現可能性定理に限れば重いのは $`\mathrm{Ind}_\kappa` による記述と稠密性。

:::theorem "kerodon_9_5_1_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsPresentable.hasSmallLimits")
Kerodon Theorem 9.5.1.1（[Tag 06PU](https://kerodon.net/tag/06PU)）。対応表の状態：一部。

*主張*　アクセス可能な無限圏が完備であることは、余完備であることと同値である。

accessibleかつcocompleteはIsPresentableの定義そのもので、hasSmallLimitsは同じCの完備性を直接返す。complete⇒cocompleteは含まない。

:::

:::definition "kerodon_9_5_1_2" (lean := "SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable")
Kerodon Definition 9.5.1.2（[Tag 06ND](https://kerodon.net/tag/06ND)）。対応表の状態：本体にある。

*主張*　無限圏は、アクセス可能で余完備であるとき呈示可能である。この場合は完備性も従う。

仮定：Quasicategory C（Kerodon と一致）。結論：IsPresentable C は IsAccessible と HasSmallColimits の連言（原文の accessible かつ余完備と一致）。

:::

:::theorem "kerodon_9_5_1_8" (lean := "SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.presentableContinuous_isRepresentable")
Kerodon Theorem 9.5.1.8（[Tag 06PY](https://kerodon.net/tag/06PY)）。対応表の状態：一部。

*主張*　アクセス可能で余完備な無限圏 $`C` に対し、空間値関手 $`C^{\mathrm{op}}\to S` は、小さい極限を保つとき、かつそのときに限り表現可能である。

IsPresentableの同じCと同じFにpresentableContinuous\_isRepresentableを適用して小極限保存⇒表現可能を直接得る。逆向きはこの引用に含まない。

*f-d-adjoint-presentable.html — 4. 表現可能性定理 — 4.3 証明*

$`C` を presentable、$`H\colon C^{\mathrm{op}}\to\mathcal S` を余極限を極限に送る関手、$`C\overset{\nu}{\hookrightarrow}\mathcal P(C_0)` を 4.2 の反射的局所化、反射を $`L` とする。

1. *候補*：$`\tilde H:=H|_{C_0^{\mathrm{op}}}\in\mathcal P(C_0)`。

2. *鍵の計算*：任意の $`F\in\mathcal P(C_0)` で自然に $`\mathrm{Map}_{\mathcal P(C_0)}(F,\tilde H)\simeq H(LF)`。稠密性 $`F\simeq\operatorname{colim}h_c` から左辺は $`\lim\tilde H(c)=\lim H(c)`。$`L` は余極限を保ち $`L(h_c)\simeq c` なので $`LF\simeq\operatorname{colim}c`（$`C` での余極限）。$`H` は余極限を極限に送るので $`H(LF)\simeq\lim H(c)`。

3. \*\*$`\tilde H` は局所対象\*\*：$`f\colon F\to F'` が $`L`-同値なら $`LF\simeq LF'` なので、2 により $`\mathrm{Map}(F',\tilde H)\to\mathrm{Map}(F,\tilde H)` は同値。よって $`\tilde H\simeq\nu Y`（$`Y=L\tilde H`）。

4. *表現*：$`X\in C` について 2 を $`F=\nu X` に適用し $`L\nu X\simeq X` を使うと $`H(X)\simeq\mathrm{Map}_{\mathcal P(C_0)}(\nu X,\nu Y)\simeq\mathrm{Map}_C(X,Y)`（$`\nu` が充満忠実）。

*自然性*：$`H` と $`\mathrm{Map}_C(-,Y)` はどちらも $`C_0^{\mathrm{op}}` への制限の右 Kan 拡張（余極限を極限に送り、$`C_0` が稠密だから）で、$`C_0` 上で一致するので Kan 拡張の一意性から関手として同値。3 は形式化の「表現可能前層の辺の作用による局所性判定」（\`presheaf\_representableInversionDetectsLocality\`）にあたる。

- 概念　／　一言で　／　証明での役割
- $`C_0=C^\kappa`　／　余極限で $`C` を生成する小さい部分圏　／　前層を小さい圏の上で扱う
- 反射的局所化　／　左随伴をもつ充満部分圏　／　$`C\subseteq\mathcal P(C_0)` と $`L`
- 局所対象　／　$`L`-同値に関して $`\mathrm{Map}(-,Z)` が同値な対象　／　候補 $`\tilde H` が $`C` に入る判定
- 稠密性　／　前層は表現可能前層の余極限　／　鍵の計算（2）
- Lurie–Simpson　／　presentable ⇔ 前層の圏のアクセシブルな反射的局所化　／　(1)⇒(2) が手順。(3)⇒(1) は別の道具
- 局所化の存在　／　$`S^{-1}\mathcal P(C_0)` が反射的で presentable　／　表現可能性定理には不要

*presentable-route.html — 2. 随伴関手定理*

- *表現可能性定理*（HTT Prop. 5.5.2.2）：$`\mathcal C` が presentable なら、$`H\colon\mathcal C^{\mathrm{op}}\to\mathcal S` が表現可能 ⇔ $`H` が小さい余極限を極限に送る。

*presentable-route.html — 5. 表現可能性定理の証明*

二段階で示す。段階 I は $`\mathcal C=\mathcal P(A)` の場合、段階 II は一般の場合を局所化で帰着させる。

*presentable-route.html — 5. 表現可能性定理の証明 — 準備*

- *(a)* presentable なら、小さい $`A`（$`\kappa`-コンパクト対象）と反射的局所化 $`L\colon\mathcal P(A)\rightleftarrows\mathcal C\colon i`（$`L\dashv i`、$`i` 充満忠実）がある。1 圏では Gabriel–Ulmer、∞ 圏では Lurie–Simpson（HTT Thm 5.5.1.1）。

- *(b)* §4 の普遍性。

*presentable-route.html — 5. 表現可能性定理の証明 — 段階 I：$`\mathcal C=\mathcal P(A)`*

$`h:=H\circ y\in\mathcal P(A)` と置く。1 圏では
$$`H(F)\cong H\bigl(\operatorname{colim}y(a)\bigr)\cong\lim H(y(a))=\lim h(a)\cong\lim\mathrm{Hom}(y(a),h)\cong\mathrm{Hom}(F,h).`
整理すると、$`H` と $`\mathrm{Hom}(-,h)` はどちらも余極限を極限に送り、$`A` への制限がどちらも $`h`（後者は米田）なので、(b) の一意性で同型。\*\*表現する対象は、$`H` を生成元に制限したものそのもの\*\*である。

*presentable-route.html — 5. 表現可能性定理の証明 — 段階 II：一般の $`\mathcal C`*

1. $`H':=H\circ L^{\mathrm{op}}` は余極限を極限に送る（$`L` は左随伴）。段階 I より $`H'\cong\mathrm{Hom}(-,h)`、$`h(a)=H(L\,y(a))`。

2. $`h` は局所的：単位 $`\eta_F` について $`\mathrm{Hom}(\eta_F,h)=H(L\eta_F)` は同型。よって $`h\cong iLh`。

3. $`c\in\mathcal C` について $`\mathrm{Hom}_{\mathcal C}(c,Lh)\cong\mathrm{Hom}(ic,h)\cong H(Lic)\cong H(c)`。

仮定の使われ方：「余極限を極限に送る」は生成元への帰着と $`L` との合成で、presentable（$`A` が小さい）は $`h` が小さい前層として存在するために使う。

*presentable-route.html — 5. 表現可能性定理の証明 — ∞ 圏で何が変わるか*

- 論点　／　1 圏　／　∞ 圏
- (a) 局所化として表す　／　Gabriel–Ulmer　／　Lurie–Simpson。主張は同じで証明は重い（HTT 第 5 章）
- 要素の圏　／　$`\mathrm{el}(F)`　／　$`\mathrm{Un}(F)`
- 段階 I の同型　／　各点の全単射 + 自然性　／　(b) を関手 ∞ 圏の同値として使い、制限側の同値を整合的に持ち上げる。関手版の米田が要る
- 段階 II の局所性　／　全単射　／　写像空間の同値。ほぼそのまま

表現可能性定理は「straightening → 米田 → $`\mathcal P(A)` の普遍性」の積み重ねの上に立つ。補章 2 §5 の「関手版の米田を何で示すか」がここに効く。

:::

:::theorem "kerodon_9_5_1_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.accessible_preservesLimits_isCorepresentable")
Kerodon Theorem 9.5.1.9（[Tag 06PZ](https://kerodon.net/tag/06PZ)）。対応表の状態：一部。

*主張*　アクセス可能で完備な無限圏 $`C` に対し、空間値関手 $`C\to S` が余表現可能であることは、アクセス可能で小さい極限を保つことと同値である。

accessible\_preservesLimits\_isCorepresentableは同じC,Fについてaccessibleかつ全小極限保存⇒corepresentableを直接返す。逆向きは含まない。

:::

:::proposition "kerodon_9_5_1_11"
Kerodon Proposition 9.5.1.11（[Tag 06Q1](https://kerodon.net/tag/06Q1)）。対応表の状態：なし。

固定宇宙の全小極限保存による表現定理は、原文の指定数値λ,μでの保存・小性と指定compact対象による表現の同じ条件に比較されていない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheaf_isRepresentable_of_sendsSmallColimitsToLimits`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presentableContinuous_isRepresentable_of_inversionLocality`

:::

:::corollary "kerodon_9_5_1_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsPresentable.hasSmallLimits")
Kerodon Corollary 9.5.1.12（[Tag 06UE](https://kerodon.net/tag/06UE)）。対応表の状態：一部。

*主張*　正則基数 $`\kappa\leq\lambda` で $`\lambda` が非可算とする。無限圏 $`C` が $`(\kappa,\lambda)`-コンパクト生成かつ $`\lambda`-余完備であり、その $`(\kappa,\lambda)`-コンパクト対象の充満部分圏が本質的に $`\lambda`-小さいとする。$`S_{<\lambda}` に $`K` 添字の極限があれば $`C` にもある。

Cをpresentableにも強め、Kを宇宙小形状に限るとhasSmallLimitsの同じKへの適用が原文の同じCのK極限の存在を直接返す。二濃度の入力だけの場合は含まない。

:::

:::proposition "kerodon_9_5_1_13"
Kerodon Proposition 9.5.1.13（[Tag 06Q2](https://kerodon.net/tag/06Q2)）。対応表の状態：なし。

固定宇宙の全小極限保存による表現定理は、原文の指定数値λ,μでの保存・小性と指定compact対象による表現の同じ条件に比較されていない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.accessible_preservesLimits_isCorepresentable`

:::

# 9.5.2 The Adjoint Functor Theorem

%%%
number := false
tag := "kerodon-9-5-2"
%%%

Kerodon [Tag 06Q4](https://kerodon.net/tag/06Q4)

*f-d-adjoint-presentable.html — 1. 随伴関手定理の主張と骨格*

$`C,D` を presentable ∞ 圏とする（HTT 5.5.2.9）。

1. $`F\colon C\to D` が右随伴をもつ ⇔ $`F` は小さい余極限を保つ。

2. $`G\colon D\to C` が左随伴をもつ ⇔ $`G` はアクセシブルで、小さい極限を保つ。

どちらも「随伴 = 各点の表現可能性」（随伴の (E)）に帰着する。

- *1 の向き*：各 $`Y` で $`\mathrm{Map}_D(F(-),Y)\colon C^{\mathrm{op}}\to\mathcal S` は、$`F` が余極限を保つので余極限を極限に送る（極限の (3)、写像空間の極限公式）。表現可能性定理（HTT 5.5.2.2）で表現され、表現対象を $`GY` とする。各点の表現を (C) の構成（cograph が cocartesian fibration になること）で関手 $`G` にまとめる。

- *2 の向き*：各 $`X` で $`\mathrm{Map}_C(X,G(-))\colon D\to\mathcal S` は極限を保ちアクセシブル。アクセシブルで極限を保つ関手は余表現可能（解集合条件の ∞ 版）。(E) から (C) で左随伴を組み立てる。

*f-d-adjoint-presentable.html — 2. 必要な部品*

- 部品　／　内容　／　どこで使うか
- $`\mathrm{Map}` の関手性　／　Hom 関手（Tw の St、補章 3 §11）、表現可能前層 $`h_y`、Yoneda 埋め込みの充満忠実性　／　表現可能性を言うため
- 随伴の (E)⇒(C)　／　各点の普遍射から関手を作る（cograph の cocartesian 持ち上げ）　／　各点の表現から随伴へ
- $`\mathcal S` の極限・余極限　／　小さい極限・余極限をもつ。$`\mathrm{Map}(\operatorname{colim}X_i,Y)\simeq\lim\mathrm{Map}(X_i,Y)`　／　「余極限を極限に送る」を扱う
- 前層の圏 $`\mathcal P(C_0)`　／　各点で計算される極限・余極限、Yoneda 埋め込みが極限を保つこと、稠密性、自由余完備化（左 Kan 拡張）　／　表現可能性定理の本体
- Kan 拡張　／　各点の左 Kan 拡張の存在　／　自由余完備化と Ind
- 大きさ　／　宇宙、正則基数 $`\kappa`、本質的に小さい、局所小　／　全体の大きさの制御
- filtered 余極限　／　$`\kappa`-filtered、$`\mathcal S` で filtered 余極限と有限極限が可換　／　コンパクト性
- アクセシブル圏　／　$`\kappa`-コンパクト対象、$`\mathrm{Ind}_\kappa`、アクセシブル関手　／　presentability の定義、2 の向き
- presentable 圏　／　定義（アクセシブルかつ余完備）と Lurie–Simpson の特徴づけ（HTT 5.5.1.1）　／　表現可能性定理を前層の場合に帰着する（(1)⇒(2) の向きだけ）
- 局所化の存在　／　射の集合での局所化 $`S^{-1}\mathcal P(C_0)` が反射的で presentable（small object argument の ∞ 版、HTT 5.5.4.15）　／　表現可能性定理には不要。新しい presentable 圏（層、安定化、Bousfield 局所化）を作るとき

\`\`\`text
Map の関手性（St・Tw）──┐
随伴 (E)⇒(C) ──────────┤
𝒮 と 𝒫(C₀) の極限・余極限、稠密性、自由余完備化 ──► 表現可能性定理 ──► 随伴関手定理 1
filtered・κ-コンパクト・Ind・アクセシブル ──► presentable（Lurie–Simpson (1)⇒(2)）──┘
                                    └──► 余表現可能性 ──► 随伴関手定理 2
\`\`\`

*f-d-adjoint-presentable.html — 3. 左随伴の側だけアクセシブル性が要る理由*

presentable 圏は「余極限の側では小さいデータで生成されるが、極限の側ではそうでない」非対称な概念で、アクセシブル性は極限の側で足りない小さい解集合を補う条件。

*f-d-adjoint-presentable.html — 3. 左随伴の側だけアクセシブル性が要る理由 — 3.1 1 の向きで条件が要らない理由*

$`C` は小さい $`C_0=C^\kappa` から余極限で生成され（$`C\simeq\mathrm{Ind}_\kappa(C^\kappa)`）、余極限を極限に送る前層は $`C_0` への制限で決まる。小さい圏上の前層なので大きさの問題は起きず、$`\mathcal P(C_0)` で表現して局所化で降ろすだけ。左随伴はすべての余極限を保つので自動的にアクセシブルで、presentable 圏の間の右随伴も自動的にアクセシブル（HTT 5.4.7.7）。

*f-d-adjoint-presentable.html — 3. 左随伴の側だけアクセシブル性が要る理由 — 3.2 2 の向きでアクセシブル性が効く場所*

$`G` の左随伴には各 $`X` でコンマ圏 $`X\downarrow G`（対象 $`(Y,X\to GY)`）の始対象が要る。$`X\downarrow G` 全体の極限は大きすぎて存在せず、小さい弱始的な部分集合（解集合）が必要。$`D` が presentable でも $`D^{\mathrm{op}}` は presentable でないので、極限の側に小さい生成系はない。

1. $`\kappa` を十分大きくとり、$`X` が $`\kappa`-コンパクト、$`G` が $`\kappa`-filtered 余極限を保つようにする。

2. 任意の $`Y` は $`\kappa`-コンパクト対象の $`\kappa`-filtered 余極限 $`Y\simeq\operatorname{colim}Y_i`。

3. $`G` は $`\kappa`-filtered 余極限を保つので $`GY\simeq\operatorname{colim}GY_i`。

4. $`X` は $`\kappa`-コンパクトなので $`X\to GY` はある $`X\to GY_i` を経由する。

5. $`\kappa`-コンパクトな $`Y'` をもつ $`(Y',X\to GY')` が弱始的で、$`D^\kappa` は本質的に小さいので小さい解集合。

6. その上で極限をとれば、$`D` の極限と $`G` の極限保存から始対象が得られる。

アクセシブル性は 3 の一点にだけ効く。1 圏では Freyd の一般随伴関手定理の解集合条件そのもの。極限を保つだけで解集合がない古典的な例は完備束の圏から集合の圏への忘却関手（3 元生成の自由完備束が存在しない、Gaifman–Hales）だが、完備束の圏は presentable ではないので「極限保存だけでは解集合が出ない」ことの説明にとどまる。presentable 圏の間で極限を保つがアクセシブルでない関手が存在するかは集合論的な仮定（Vopěnka 原理など）が絡む問題だったと記憶しているが、確かめていない。

- 　／　左随伴になる条件　／　右随伴になる条件
- presentable 圏の間　／　余極限を保つ　／　極限を保ち、かつアクセシブル
- 理由　／　余極限の側は $`C^\kappa` で生成されるので小ささが自動　／　極限の側には生成系がなく、解集合をアクセシブル性で作る
- 圏の圏　／　$`\mathrm{Pr}^L`：余極限を保つ関手　／　$`\mathrm{Pr}^R`：アクセシブルで極限を保つ関手

$`\mathrm{Pr}^R` の射の定義にアクセシブル性が入っているのもこの非対称のためで、$`\mathrm{Pr}^L\simeq(\mathrm{Pr}^R)^{\mathrm{op}}` は二つの条件が随伴でちょうど入れ替わることを言う。

:::theorem "kerodon_9_5_2_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_rightAdjoint_iff_preservesSmallColimits, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_leftAdjoint_iff_accessible_preservesLimits")
Kerodon Theorem 9.5.2.1（[Tag 06Q5](https://kerodon.net/tag/06Q5)）。対応表の状態：本体にある。

*主張*　呈示可能な無限圏同士の関手は、小さい余極限を保つとき、かつそのときに限り右随伴を持つ。左随伴を持つための必要十分条件は、アクセス可能で小さい極限を保つことである。

仮定：C,D が quasicategory で IsPresentable、指定した F または G（Kerodon と一致）。結論：右随伴の存在と小余極限保存の iff、左随伴の存在と accessible 性かつ小極限保存の iff（原文の二主張と一致）。

*presentable-route.html — 2. 随伴関手定理*

*定理*（HTT Cor. 5.5.2.9）．$`\mathcal C,\mathcal D` を presentable な ∞ 圏、$`F\colon\mathcal C\to\mathcal D` を関手とする。

1. $`F` が右随伴を持つ ⇔ $`F` が小さい余極限を保つ。

2. $`F` が左随伴を持つ ⇔ $`F` が小さい極限を保ち、accessible（ある $`\kappa` について $`\kappa`-filtered 余極限を保つ）。

「⇒」は随伴の一般論。中身は「⇐」で、1 は次の二つの組み合わせである。

- *各点の判定*：$`F` が右随伴を持つ ⇔ 各 $`d` について $`c\mapsto\mathrm{Map}(Fc,d)` が表現可能。

:::

:::proposition "kerodon_9_5_2_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_rightAdjoint_iff_preservesSmallColimits, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_rightAdjoint_iff_preservesSmallColimits_of_representability_native")
Kerodon Proposition 9.5.2.2（[Tag 06QB](https://kerodon.net/tag/06QB)）。対応表の状態：一部。

*主張*　呈示可能な無限圏から局所小さい無限圏への関手が右随伴を持つことは、小さい余極限を保つことと同値である。

Dをaccessibleにも強め、presentableなCからの全連続前層の表現定理をhRepへ入れると、native判定は同じFの右随伴存在と全小余極限保存のiffを直接返す。Dをpresentableとする必要はなく、局所小だけの場合は含まない。

:::

:::proposition "kerodon_9_5_2_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_leftAdjoint_iff_accessible_preservesLimits, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightAdjoint_isAccessible")
Kerodon Proposition 9.5.2.3（[Tag 06QC](https://kerodon.net/tag/06QC)）。対応表の状態：一部。

*主張*　呈示可能な無限圏 $`D` からアクセス可能な無限圏 $`C` への関手 $`G` は、アクセス可能で小さい極限を保つとき、かつそのときに限り左随伴を持つ。

Dをpresentableとする原文の仮定の下でrightAdjoint\_isAccessibleとadjunction\_preservesSmallLimitsは同じGの左随伴存在⇒accessibleかつ小極限保存を直接与える。引用のiffが要求するCのpresentabilityは逆向きに限る追加入力。

:::

:::definition "kerodon_9_5_2_5"
Kerodon Variant 9.5.2.5（[Tag 06QE](https://kerodon.net/tag/06QE)）。対応表の状態：なし。

全小余極限/極限保存による随伴判定は、原文の指定λ-small保存と指定写像空間のλ-small性という同じ二条件のiffではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_rightAdjoint_iff_preservesSmallColimits`

:::

:::definition "kerodon_9_5_2_6"
Kerodon Variant 9.5.2.6（[Tag 06QF](https://kerodon.net/tag/06QF)）。対応表の状態：なし。

全小余極限/極限保存による随伴判定は、原文の指定λ-small保存と指定写像空間のλ-small性という同じ二条件のiffではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_leftAdjoint_iff_accessible_preservesLimits`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_leftAdjoint_of_accessible_limitPreserving_HomModels`

:::

# 9.5.3 The ∞-Category of Presentable ∞-Categories

%%%
number := false
tag := "kerodon-9-5-3"
%%%

Kerodon [Tag 06UF](https://kerodon.net/tag/06UF)

:::definition "kerodon_9_5_3_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrL")
Kerodon Construction 9.5.3.1（[Tag 06PF](https://kerodon.net/tag/06PF)）。対応表の状態：本体にある。

*主張*　アクセス可能な無限圏と関手の無限圏の部分圏 $`\mathcal{QC}^{\mathrm{LPr}}` では、対象を呈示可能な無限圏とし、射を小さい余極限を保つアクセス可能な関手とする。

仮定：外部の圏の仮定なし。PrL の対象は小余極限を持つ accessible quasicategory（Kerodon と一致）。結論：coherent nerve PrL の写像空間は小余極限保存関手の充満関手空間の core（原文の指定の射と一致）。

:::

:::definition "kerodon_9_5_3_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrR")
Kerodon Variant 9.5.3.2（[Tag 06UG](https://kerodon.net/tag/06UG)）。対応表の状態：本体にある。

*主張*　アクセス可能な無限圏と関手の無限圏の部分圏 $`\mathcal{QC}^{\mathrm{RPr}}` では、対象を呈示可能な無限圏とし、射を小さい極限を保つアクセス可能な関手とする。

仮定：外部の圏の仮定なし。対象は presentable な quasicategory（Kerodon と一致）。結論：coherent nerve PrR の写像空間は accessible かつ小極限を保存する関手空間の core（原文の指定の射と一致）。

:::

:::definition "kerodon_9_5_3_5"
Kerodon Definition 9.5.3.5（[Tag 06PK](https://kerodon.net/tag/06PK)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単独の presentable 圏と、大域的な余カルテシアン射の輸送および小余極限保存はある。任意の局所余カルテシアン射の全ファイバー・全輸送に原文の条件を束ねる述語は未確認。

:::

:::proposition "kerodon_9_5_3_7"
Kerodon Proposition 9.5.3.7（[Tag 06UJ](https://kerodon.net/tag/06UJ)）。対応表の状態：なし。

固定された二つのpresentable圏の随伴存在判定は、原文のUのlocally cartesian/cocartesian性とその輸送関手への同一視を型に含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_leftAdjoint_iff_accessible_preservesLimits`

:::

:::corollary "kerodon_9_5_3_8"
Kerodon Corollary 9.5.3.8（[Tag 06Q8](https://kerodon.net/tag/06Q8)）。対応表の状態：なし。

PrL/PrRの構成と固定二対象の随伴同値は、原文の指定Uの輸送表現の因数分解とファイブレーション性の四条件を結ぶ型ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presentableAdjointFunctorEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrL`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrR`

:::

:::corollary "kerodon_9_5_3_9"
Kerodon Corollary 9.5.3.9（[Tag 06Q9](https://kerodon.net/tag/06Q9)）。対応表の状態：なし。

固定二対象のpresentableAdjointFunctorEquivalenceは、原文の準圏そのものを動かす全PrLop→PrRの指定Ψとは別の射。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presentableAdjointFunctorEquivalence`

:::

# 9.5.4 Closure Properties of Presentable ∞-Categories

%%%
number := false
tag := "kerodon-9-5-4"
%%%

Kerodon [Tag 06P5](https://kerodon.net/tag/06P5)

:::proposition "kerodon_9_5_4_1"
Kerodon Proposition 9.5.4.1（[Tag 06P6](https://kerodon.net/tag/06P6)）。対応表の状態：なし。

generatedSourceCategoryのpresentabilityは、指定slice/coslice準圏全体との同一視を引用に持たない。通常Overのaccessible性も別の模型。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSource_isPresentable`、`CategoryTheory.Over.instIsAccessibleCategory`、`CategoryTheory.Under.instIsAccessibleCategory`

:::

:::corollary "kerodon_9_5_4_2"
Kerodon Corollary 9.5.4.2（[Tag 06UK](https://kerodon.net/tag/06UK)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Mathlib には通常圏の普遍余極限と指数可能性の述語があり、厳密な単体集合の slice には右随伴がある。presentable な準圏で局所カルテシアン閉性と全・小普遍余極限を同値にする型は未確認。

:::

:::proposition "kerodon_9_5_4_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functor_isPresentable")
Kerodon Proposition 9.5.4.3（[Tag 06P7](https://kerodon.net/tag/06P7)）。対応表の状態：一部。

*主張*　呈示可能な無限圏 $`C` と小さい単体集合 $`K` に対し、$`\operatorname{Fun}(K,C)` も呈示可能である。

Kを小準圏に限るとfunctor\_isPresentableが同じFun(K,C)のpresentabilityを直接返す。任意の単体集合Kは含まない。

:::

:::proposition "kerodon_9_5_4_4" (uses := "kerodon_1_4_0_1, kerodon_7_1_9_5, kerodon_9_4_9_4")
Kerodon Proposition 9.5.4.4（[Tag 06P8](https://kerodon.net/tag/06P8)）。対応表の状態：なし。

Arrow(C)のpresentabilityは原文の指定F−,F+のoriented fiber productとの比較を持たない。恒等の特殊化でも指定模型との比較が未確認。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.arrow_isPresentable`、`CategoryTheory.Comma.isAccessibleCategory`、`SerrePositivity.Smith.arrow_locallyPresentable`

:::

:::corollary "kerodon_9_5_4_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullback_isPresentable_of_accessiblePullback, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.pullback_isAccessible, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.isPresentable_of_isAccessible") (uses := "kerodon_1_4_0_1")
Kerodon Corollary 9.5.4.6（[Tag 06PA](https://kerodon.net/tag/06PA)）。対応表の状態：一部。

*主張*　呈示可能な無限圏の間の二関手 $`F_\pm:C_\pm\to C` がともに小さい余極限を保つか、ともにアクセス可能で小さい極限を保つなら、その圏論的引き戻しは呈示可能である。

両脚cocontinuous、一方equivalence lifting、strict pullback模型に限りpullback\_isAccessibleを入力してisPresentable\_of\_isAccessibleを適用すると同じ全空間のpresentabilityを直接得る。continuous側と任意の指定模型は含まない。

:::

:::proposition "kerodon_9_5_4_7"
Kerodon Proposition 9.5.4.7（[Tag 06PC](https://kerodon.net/tag/06PC)）。対応表の状態：なし。

積・pullback・関手準圏のpresentabilityを、原文の指定QC内の一般図式の極限と同一視する型を引用に持たない。各構成を組む議論だけをpartialとしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet_isPresentable`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullback_isPresentable_of_accessiblePullback`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.pullback_isAccessible`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functor_isPresentable`

:::

:::definition "kerodon_9_5_4_10"
Kerodon Variant 9.5.4.10（[Tag 06UL](https://kerodon.net/tag/06UL)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：二脚の補題は余極限を保つ脚を要求し、strict な単体集合の小極限の補題は filtered 余極限との交換までを与える。小さい任意形状の accessible な極限保存関手の図式の極限が presentable となる型は見つからない。

:::

:::proposition "kerodon_9_5_4_12"
Kerodon Proposition 9.5.4.12（[Tag 06PH](https://kerodon.net/tag/06PH)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：PrL・PrR の模型と個別の積・引戻しの presentability を確認した。これらは PrL・PrR 内の任意の小極限も、QC\_\{≤Ω\} への包含での保存も与えない。

:::

:::corollary "kerodon_9_5_4_13"
Kerodon Corollary 9.5.4.13（[Tag 06UN](https://kerodon.net/tag/06UN)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：PrL・PrR の準圏模型と単独の presentable 圏の小極限存在はある。PrL と PrR 自体への小余極限の存在を与える型は見つからない。

:::

:::proposition "kerodon_9_5_4_17"
Kerodon Proposition 9.5.4.17（[Tag 06PN](https://kerodon.net/tag/06PN)）。対応表の状態：なし。

全関手準圏のpresentabilityと評価保存は、原文のUのsection準圏と同じものへの比較がない。積束に限るだけで同じ指定対象と数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functor_isPresentable`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PointwiseCompactHom.evaluateFunctorAt_preservesSmallColimits`

:::

:::lemma_ "kerodon_9_5_4_19"
Kerodon Lemma 9.5.4.19（[Tag 06PQ](https://kerodon.net/tag/06PQ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：余 cartesian 切断の部分空間と coslice の κ-filtered 余極限はある。各頂点が presentable で辺ごとに accessible な局所 (co)cartesian ファイブレーションの切断圏を presentable とする型は見つからない。

:::

# 9.5.5 Cocontinuous Functors

%%%
number := false
tag := "kerodon-9-5-5"
%%%

Kerodon [Tag 06US](https://kerodon.net/tag/06US)

:::definition "kerodon_9_5_5_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible, SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable")
Kerodon Definition 9.5.5.1（[Tag 06NF](https://kerodon.net/tag/06NF)）。対応表の状態：本体にある。

*主張*　小さい正則基数 $`\kappa` に対して、無限圏が $`\kappa`-呈示可能であるとは、呈示可能であり、かつ $`\kappa`-アクセス可能であることをいう。

同じCのIsPresentable CとIsKappaAccessible κ Cの論理積が原文のκ-presentableの定義全体を直接表す。専用名がないことは不足としない。

:::

:::proposition "kerodon_9_5_5_3"
Kerodon Proposition 9.5.5.3（[Tag 06NM](https://kerodon.net/tag/06NM)）。対応表の状態：なし。

isPresentable\_iff\_cocompleteIndEquivalenceはある基数の存在であり、原文の指定κに固定した小さいκ余完備な生成圏の表示を返さない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isPresentable_iff_cocompleteIndEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indInfinity_isPresentable_iff_hasSmallColimits`

:::

:::proposition "kerodon_9_5_5_5"
Kerodon Proposition 9.5.5.5（[Tag 06NP](https://kerodon.net/tag/06NP)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一濃度の Ind の制限同値と前層余完備化への左 Kan 延長を確認した。κ-余完備化を相対 Ind\_\{κ\}\^\{λ\} に入れた合成が λ-余完備化になる主張は未確認。

:::

:::corollary "kerodon_9_5_5_6"
Kerodon Corollary 9.5.5.6（[Tag 06NQ](https://kerodon.net/tag/06NQ)）。対応表の状態：なし。

Indのκ-filtered余極限存在だけでは指定λ-small全余極限存在は出ない。通常圏Indの全余極限存在はnerve比較なし。

宣言：`CategoryTheory.instHasColimitsIndOfHasFiniteColimits`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ind_hasSmallKappaFilteredColimits`

:::

:::corollary "kerodon_9_5_5_7"
Kerodon Corollary 9.5.5.7（[Tag 06NR](https://kerodon.net/tag/06NR)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：コンパクト対象の有限余極限閉性と小準圏形状での結果はある。二濃度の生成のもとで C の λ-余完備性、κ-余完備性、compact 部分の κ-余完備性を相互に導く型は未確認。

:::

:::corollary "kerodon_9_5_5_8" (lean := "CategoryTheory.instHasColimitsIndOfHasFiniteColimits, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.hasFiniteColimits_kappaCompactObjects")
Kerodon Corollary 9.5.5.8（[Tag 06NS](https://kerodon.net/tag/06NS)）。対応表の状態：一部。

*主張*　小さい正則基数 $`\kappa` に関して $`\kappa`-コンパクト生成される無限圏 $`C` では、$`C` が余完備であること、$`\kappa`-余完備であること、$`\kappa`-コンパクト対象の充満部分圏が $`\kappa`-余完備であることは同値である。

κ=ℵ0としCが有限余極限を持つ場合、hasFiniteColimits\_kappaCompactObjectsは同じcompact対象部分圏の有限余極限存在、すなわち(2)⇒(3)を直接返す。全iffと任意κは含まない。

:::

:::proposition "kerodon_9_5_5_9"
Kerodon Proposition 9.5.5.9（[Tag 06NU](https://kerodon.net/tag/06NU)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Ind-Yoneda に沿う左 Kan 延長が小 κ-filtered 余極限を保つ型はある。原文が比較する元の f と拡張 F の κ・λ 右完全性は異なる形状の条件であり、その三条件の同値は未確認。

:::

:::corollary "kerodon_9_5_5_10"
Kerodon Corollary 9.5.5.10（[Tag 06NV](https://kerodon.net/tag/06NV)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：小余極限保存から κ-filtered 保存への含意と、Ind 延長の同種の保存を確認した。元の f の κ-小余極限保存から F の λ-小な全余極限保存を導く、二濃度の iff は未確認。

:::

:::corollary "kerodon_9_5_5_11"
Kerodon Corollary 9.5.5.11（[Tag 06NW](https://kerodon.net/tag/06NW)）。対応表の状態：なし。

Indのκ-filtered余極限保存関手の制限同値は、原文の全λ-small余極限保存関手への同じ制限ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indKappaContinuousRestrictionEquivalence`

:::

:::corollary "kerodon_9_5_5_12"
Kerodon Corollary 9.5.5.12（[Tag 06Z9](https://kerodon.net/tag/06Z9)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：空間の 0 切断、有限模型による全空間の生成、全関手圏の presentability を確認した。S\^\{≤n\}\_fin 上の有限余極限保存関手の Δ⁰ 評価の充満忠実性と n-余切断対象による本質像は未確認。

:::

:::corollary "kerodon_9_5_5_13"
Kerodon Corollary 9.5.5.13（[Tag 06NX](https://kerodon.net/tag/06NX)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：小余極限保存が κ-filtered 保存を含む向きはある。二濃度で、finitary 性と compact 部分の κ-余連続性から任意の λ-小余極限保存を復元する向きは未確認。

:::

:::corollary "kerodon_9_5_5_14"
Kerodon Corollary 9.5.5.14（[Tag 06NY](https://kerodon.net/tag/06NY)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一濃度の Ind の制限同値と compact 生成モデルはある。原文の C の λ-余連続関手を C\_\{\<κ\} 上の κ-余連続関手へ送る、全ての小形状に関する制限同値は未確認。

:::

:::corollary "kerodon_9_5_5_15" (lean := "SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits.isKappaAccessibleFunctor, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indLeftKanExtension_preservesSmallKappaFilteredColimits")
Kerodon Corollary 9.5.5.15（[Tag 06NZ](https://kerodon.net/tag/06NZ)）。対応表の状態：一部。

*主張*　小さい正則基数 $`\kappa`、余完備で $`\kappa`-コンパクト生成な無限圏 $`C`、小さい $`\kappa`-フィルター付き余極限を持つ $`D` を取る。$`F:C\to D` が余連続であることは、$`\kappa`-finitary であり、$`\kappa`-コンパクト対象への制限が $`\kappa`-余連続であることと同値である。

Cを標準Indκ(A)に限り同じFが左Kan拡張である場合、indLeftKanExtension\_preservesSmallKappaFilteredColimitsは原文右辺の同じFのκ-finitary成分を直接返す。compact部分への保存条件と全iffは含まない。

:::

:::corollary "kerodon_9_5_5_16"
Kerodon Corollary 9.5.5.16（[Tag 06ZA](https://kerodon.net/tag/06ZA)）。対応表の状態：なし。

PrLFunctorSpaceの準圏性と全Fun(K,D)のpresentabilityは、cocontinuous全部分圏自身のpresentabilityを返さない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functor_isPresentable`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.prLFunctorSpace_quasicategory`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functor_isPresentable`

:::

:::proposition "kerodon_9_5_5_17" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsPresentable.isLocallySmall, SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable.hasSmallColimits, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaCompactGenerating.exists_smallFamilyPresentation")
Kerodon Proposition 9.5.5.17（[Tag 06P0](https://kerodon.net/tag/06P0)）。対応表の状態：一部。

*主張*　無限圏 $`C` が呈示可能であることは、局所小さく余完備で、小さい対象族が小さい余極限で $`C` を生成し、各対象がそれぞれある小さい正則基数 $`\kappa` について $`\kappa`-コンパクトであることと同値である。

IsPresentableの同じCの局所小性と全小余極限存在は原文の右辺(a)(b)を直接返す。小生成族の全余極限生成と全対象のcompact基数はこの引用だけでは含まない。

:::

:::lemma_ "kerodon_9_5_5_18" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indComparison_isFullyFaithful_of_compact")
Kerodon Lemma 9.5.5.18（[Tag 06P1](https://kerodon.net/tag/06P1)）。対応表の状態：一部。

*主張*　正則基数 $`\kappa\trianglelefteq\lambda` と $`\kappa`-余完備な無限圏 $`C` を取る。$`h:C\to\widehat C` が充満忠実で $`\kappa`-小余極限を保ち、像の全対象が $`(\kappa,\lambda)`-コンパクトで、$`\widehat C` が $`\lambda`-小余極限を持つとする。$`\operatorname{Ind}_\kappa^\lambda`-延長は充満忠実で、その本質像は $`h` の本質像を含み $`\lambda`-小余極限で閉じる最小の充満部分圏である。

数値λ制限のない標準Indκの小始域の場合、indComparison\_isFullyFaithful\_of\_compactは同じhのκ-finitary拡張Hの充満忠実性を直接返す。全λ-small余極限閉包としての像の判定は含まない。

:::

:::lemma_ "kerodon_9_5_5_19"
Kerodon Lemma 9.5.5.19（[Tag 06P2](https://kerodon.net/tag/06P2)）。対応表の状態：なし。

κ-filtered生成によるInd比較は指定λ-small全余極限生成と数値λの同じ完備化に比較されていない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indComparison_isQCatEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_isKappaCompactGenerating`

:::

:::proposition "kerodon_9_5_5_21" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsPresentable.isLocallySmall, SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable.hasSmallColimits, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaCompactGenerating")
Kerodon Proposition 9.5.5.21（[Tag 06P4](https://kerodon.net/tag/06P4)）。対応表の状態：一部。

*主張*　小さい正則基数 $`\kappa` に対し、無限圏が $`\kappa`-呈示可能であることは、局所小さく余完備であり、小さい族の $`\kappa`-コンパクト対象で小さい余極限のもと生成されることと同値である。

κ-presentableのpresentable成分から同じCの局所小性と余完備性(a)(b)が直接得られる。小κ-compact族による全小余極限生成を含む全iffは含まない。

:::

:::corollary "kerodon_9_5_5_22" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaAccessible.of_cardinalChangeBound, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsPresentable.exists_accessibilityCardinalAbove")
Kerodon Corollary 9.5.5.22（[Tag 06UT](https://kerodon.net/tag/06UT)）。対応表の状態：一部。

*主張*　小さい正則基数 $`\kappa\leq\lambda` に対し、$`\kappa`-呈示可能な無限圏は $`\lambda`-呈示可能である。

κ≤λをIsCardinalChangeBound κ λへ強めると同じCのκ-accessibilityをλ-accessibilityへ移せる。元のpresentabilityと論理積にして同じCのλ-presentabilityを得る。任意の基数比較は含まない。

:::

# 9.5.6 Bousfield Localization

%%%
number := false
tag := "kerodon-9-5-6"
%%%

Kerodon [Tag 06UU](https://kerodon.net/tag/06UU)

:::definition "kerodon_9_5_6_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory, SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable")
Kerodon Definition 9.5.6.1（[Tag 06UV](https://kerodon.net/tag/06UV)）。対応表の状態：一部。

*主張*　呈示可能な無限圏 $`C` からの関手 $`F:C\to D` が Bousfield 局所化関手であるとは、$`D` が呈示可能で、$`F` が充満忠実な右随伴を持つことである。

FをrepleteなReflectiveSubcategoryのreflectorに限り、始域・その部分圏のIsPresentableを課すと、その構造の随伴と充満包含は原文の同じFのBousfield条件を直接表す。任意のFによる定義全体は含まない。

:::

:::proposition "kerodon_9_5_6_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldLocalizationFunctor_preservesSmallColimits, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldLocalizationFunctor_isLocalization_invertedEdges, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.isLocalization")
Kerodon Proposition 9.5.6.2（[Tag 06UW](https://kerodon.net/tag/06UW)）。対応表の状態：一部。

*主張*　呈示可能な無限圏の間の関手が Bousfield 局所化であることは、小さい余極限を保ち、ある射の族に関する局所化関手であることと同値である。

同じ反射のreflectorには随伴による余極限保存とisLocalizationがあり、原文のBousfield⇒(1)(2)を直接返す。逆向きは含まない。

:::

:::definition "kerodon_9_5_6_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsReflectiveSubcategory, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isPresentable_of_reflection")
Kerodon Definition 9.5.6.9（[Tag 06V3](https://kerodon.net/tag/06V3)）。対応表の状態：一部。

*主張*　呈示可能な無限圏の充満部分圏が Bousfield 局所化であるとは、反射的であり、アクセス可能に埋め込まれていることをいう。

IsReflectiveSubcategoryは同じ部分圏に要求する定義のreflective成分を直接与える。accessibly embedded成分と併せた全定義はこの引用だけでは含まない。

:::

:::proposition "kerodon_9_5_6_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.reflective_mem_limitCone, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_leftAdjoint_iff_accessible_preservesLimits")
Kerodon Proposition 9.5.6.15（[Tag 06V9](https://kerodon.net/tag/06V9)）。対応表の状態：一部。

*主張*　呈示可能な無限圏の充満部分圏が Bousfield 局所化であることは、アクセス可能に埋め込まれ、もとの圏で小さい極限を取って閉じていることと同値である。

部分圏をrepleteにも強めればreflective\_mem\_limitConeは同じ部分圏の小極限閉性という右辺一成分を直接返す。accessibilityと逆向きは含まない。

:::

:::corollary "kerodon_9_5_6_19"
Kerodon Corollary 9.5.6.19（[Tag 06VD](https://kerodon.net/tag/06VD)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：辺の集合に関する局所対象の presentability と accessible な引戻しの結果はある。連続 accessible な G の逆像が反射部分圏になるための左随伴まで組み立てる型は未確認。

:::

:::corollary "kerodon_9_5_6_20"
Kerodon Corollary 9.5.6.20（[Tag 06VE](https://kerodon.net/tag/06VE)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：局所対象の presentability と随伴間の変換の同値はある。任意の二つの連続 accessible な関手間の α が可逆な頂点の全部分圏が Bousfield 局所化となる結果は未確認。

:::

:::corollary "kerodon_9_5_6_21"
Kerodon Corollary 9.5.6.21（[Tag 06VF](https://kerodon.net/tag/06VF)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：一組の辺に対する局所対象と生成辺の増加に対する反単調性はある。任意の小族の反射部分圏の共通部分を、共通の生成辺集合で表して局所化する型は未確認。

:::

# 9.5.7 Existence of Bousfield Localizations

%%%
number := false
tag := "kerodon-9-5-7"
%%%

Kerodon [Tag 06VG](https://kerodon.net/tag/06VG)

:::theorem "kerodon_9_5_7_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfield_isReflectiveSubcategory, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldLocalObjects_isPresentable, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject")
Kerodon Theorem 9.5.7.1（[Tag 06VH](https://kerodon.net/tag/06VH)）。対応表の状態：本体にある。

*主張*　呈示可能な無限圏の小さい射の族 $`W` に対して、$`W`-局所対象の充満部分圏は Bousfield 局所化である。

仮定：presentable な quasicategory C と小さい添字型で与えた辺の族。集合 W はその像で表せる（Kerodon と一致）。結論：W-local 頂点の部分∞圏が反射部分圏で presentable（原文の Bousfield 局所化と一致）。

:::

:::proposition "kerodon_9_5_7_2"
Kerodon Proposition 9.5.7.2（[Tag 06VJ](https://kerodon.net/tag/06VJ)）。対応表の状態：なし。

IsLocalizationの前合成は全関手準圏の型。原文の両側のcocontinuous全部分圏へ同じ射を制限した充満忠実性・像との比較を引用に持たない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldLocalizationFunctor_isLocalization_invertedEdges`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldLocalizationFunctor_isLocalization_generatedEdges`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization`

:::

:::proposition "kerodon_9_5_7_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfield_isReflectiveSubcategory, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfield_generatedEdges_eq_localEquivalences")
Kerodon Proposition 9.5.7.5（[Tag 06VL](https://kerodon.net/tag/06VL)）。対応表の状態：一部。

*主張*　呈示可能な無限圏 $`C` の充満部分圏が Bousfield 局所化であることは、ある小さい射の族 $`W` に対して $`W`-局所対象が張る充満部分圏であることと同値である。

小さい同じWからbousfield\_isReflectiveSubcategoryとbousfieldLocalObjects\_isPresentableによりW-local部分圏の反射性とaccessibilityを得る。包含のaccessibilityは別入力なので右⇒左の全体ではなく反射性・部分圏のaccessibilityの成分。

:::

:::corollary "kerodon_9_5_7_6"
Kerodon Corollary 9.5.7.6（[Tag 06VM](https://kerodon.net/tag/06VM)）。対応表の状態：なし。

IsLocalizationの全関手圏への前合成の充満忠実性は、原文のPrLの指定写像空間の(-1)-truncated比較と直接同じ型ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldLocalizationFunctor_isLocalization_invertedEdges`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversalConsequences.IsLocalization.precomposition_isFullyFaithful`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLMappingSpace`

:::

:::corollary "kerodon_9_5_7_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsPresentable.exists_presheafReflection, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheaf_isPresentable, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldLocalObjects_isPresentable")
Kerodon Corollary 9.5.7.8（[Tag 06VP](https://kerodon.net/tag/06VP)）。対応表の状態：一部。

*主張*　無限圏が呈示可能であることは、ある小さい無限圏 $`K` の空間値前層圏 $`\operatorname{Fun}(K^{\mathrm{op}},S)` で、小さい射の族 $`W` に関する局所対象の充満部分圏と同値であることと同値である。

W-local部分圏のpresentability、presheaf\_isPresentableと同値不変性から、原文のそのような小K,Wの表示が存在⇒Cがpresentableを直接得る。一般反射を小Wで表す逆向きは含まない。

:::

:::proposition "kerodon_9_5_7_10"
Kerodon Proposition 9.5.7.10（[Tag 06VR](https://kerodon.net/tag/06VR)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：指定の生成辺による反射局所化と、辺を反転する関手の延長はある。任意の余連続 H に対し、延長が保存的かつ余連続である形の分解をまとめる型は未確認。

:::

