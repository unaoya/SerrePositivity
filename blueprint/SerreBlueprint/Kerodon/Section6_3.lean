import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.SimplicialSet.Nonsingular
import Mathlib.CategoryTheory.Localization.Predicate
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.AdjointLocalization
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DeformationLocalization
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneralLocalization
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GroupoidCompletion
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InverseAttachmentUniversal
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Localization
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LocalizationResolution
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.PrecompositionCriterion
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Reflective
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveLocalization
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Saturation
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversalConsequences
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WeakDeformationSource

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "6.3 Localization" =>
%%%
number := false
tag := "kerodon-6-3"
%%%

Kerodon の 6.3 節（[Tag 01M4](https://kerodon.net/tag/01M4)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

*f-03-localization.html — 8. 局所化に関わる概念の整理*

- 概念　／　Dwyer–Kan 局所化との関係　／　所在
- Gabriel–Zisman 局所化（1 圏）　／　∞ 局所化のホモトピー圏　／　Mathlib。比較は \`fraction\_ho\_localization\`（KST/LocalizingInvariants、private）
- 分数の計算（Ore 条件）　／　局所化の写像空間を屋根で計算する道具　／　Mathlib（1 圏）。∞ 版は LI の Verdier 分数（第 5 章）
- 反射的局所化・Bousfield 局所化　／　特別な場合（右随伴が充満忠実）　／　InfinityCategories/Kerodon/AdjointFunctors/Localization・InfinityCategories/Kerodon/LargeInfinityCategories/PresentableInfinityCategories
- Verdier 局所化　／　特別な場合（安定 ∞ 圏で、cofiber が部分圏に入る射）　／　Stable の \`cofiberLocalizingEdges\`、\`IsVerdierSequence\`（第 4 章）
- hammock 局所化　／　普通の圏の局所化の模型（写像空間が具体的）　／　EInfinity/SimplicialLocalization → InfinityCategories/Kerodon/AdjointFunctors/Localization
- groupoid 完備化　／　すべての辺での局所化（結果は Kan 複体）　／　LI の GroupoidCompletion\*
- anodyne 局所化　／　単体的集合の 1 圏を anodyne 射で局所化（空間のホモトピー圏）。∞ 圏の局所化ではなく 1 圏の局所化　／　HomotopicalAlgebra/Simplicial の \`anodyneQ\`（第 2 章）
- モデル圏の左 Bousfield 局所化　／　背後の ∞ 圏で見れば Bousfield 局所化　／　HomotopicalAlgebra/Localization（モデル圏なので基盤では使わない）
- Drinfeld 商　／　dg 圏での Verdier 商の模型　／　Derived の \`dgQuotientNerve\`

:::definition "kerodon_6_3_0_1" (lean := "CategoryTheory.Localization.StrictUniversalPropertyFixedTarget")
Kerodon Definition 6.3.0.1（[Tag 01M5](https://kerodon.net/tag/01M5)）。対応表の状態：Mathlib にある。

仮定：通常の圏の関手 F:C→D、反転する射のクラス W、任意の試験圏 E（Lean は E を引数に取る）（Kerodon と一致）。結論：StrictUniversalPropertyFixedTarget は W を反転する各関手の厳密な因子化と一意性。任意の E について取れば原文の全単射（一致）。

:::

:::definition "kerodon_6_3_0_6" (lean := "CategoryTheory.Functor.IsLocalization, CategoryTheory.Localization.full_whiskeringLeft")
Kerodon Definition 6.3.0.6（[Tag 01M9](https://kerodon.net/tag/01M9)）。対応表の状態：一部。

MathlibのFunctor.IsLocalizationからfull\_whiskeringLeftおよびfaithfulの既存instanceにより、原文の全試験圏への前合成の充満忠実性を直接得る。本質的像の全判定と普遍性からの逆は含まない。

:::

# 6.3.1 Localizations of ∞-Categories

%%%
number := false
tag := "kerodon-6-3-1"
%%%

Kerodon [Tag 01ME](https://kerodon.net/tag/01ME)

*f-03-localization.html — 4. 普遍性からすぐ出ること*

- 結果　／　宣言
- 前合成は充満忠実：$`\mathrm{Fun}(D, E) \to \mathrm{Fun}(X, E)` は（像の上で）充満忠実　／　\`IsLocalization.precomposition\_isFullyFaithful\`（InfinityCategories/Kerodon/AdjointFunctors/Localization/UniversalConsequences）
- 延長：$`W` を可逆に送る関手 $`G : X \to E` は、$`D` を経由する（自然同値を除いて）　／　\`IsLocalization.exists\_extension\`（同）、\`localizationDescend\`・\`localizationDescendIso\`（KST/LocalizingInvariants/LocalizationFactorization.lean:36・41）
- 一意性：同じ $`W` での二つの局所化（quasicategory）は同値　／　\`localizationComparisonEquivalence\`（KST/LocalizingInvariants/LocalizationUniqueness.lean:59）
- 飽和：局所化で可逆になる辺をすべて $`W` に加えても、局所化のまま　／　\`IsLocalization.saturate\`・\`of\_subset\_invertedEdges\`（InfinityCategories/Kerodon/AdjointFunctors/Localization/Saturation）
- 宇宙の移動　／　\`IsLocalization.ulift\`・\`of\_ulift\`・\`exists\_extension\_ulift\`（InfinityCategories/Kerodon/AdjointFunctors/Localization/Universe\*）

*f-03-localization.html — 5. 判定法：与えられた関手が局所化であることを示す*

存在定理は抽象的な $`Q` を作るだけなので、実際には「手元の具体的な関手 $`F : X \to D` が局所化である」と示したい場面が多い。
例：Verdier 商の射影、hammock 局所化への関手、反射。InfinityCategories/Kerodon/AdjointFunctors/Localization に、そのための判定法がある。

- 判定法　／　条件の形　／　宣言
- 延長による判定　／　前合成が充満忠実で、$`W` を可逆に送る関手がすべて延びる　／　\`isLocalization\_of\_fullyFaithful\_extensions\`（PrecompositionCriterion）
- 変形による判定　／　$`X` の中に、$`D` を「変形レトラクト」として実現する部分がある（例：cofibrant 置換のある状況）　／　\`isLocalization\_of\_deformation\`・\`isLocalization\_of\_weakDeformation\`（DeformationLocalization・WeakDeformationSource）
- 右 Kan 拡張による判定　／　局所的な極限の条件で右 Kan 拡張が存在する　／　\`isLocalization\_of\_rightKan\_local\_limits\`（RightKanCriterion）
- 反射による判定　／　右随伴が充満忠実（反射的部分圏への反射）　／　\`ReflectiveLocalization\`（InfinityCategories/Kerodon/AdjointFunctors/Localization）、\`AdjointLocalization.isLocalization\`（InfinityCategories/Kerodon/AdjointFunctors/Localization）

最後の「反射による判定」が、Bousfield 局所化を Dwyer–Kan 局所化の特別な場合にしている（§6）。

*sixff-foundations.html — 局所化*

局所化は余極限の側をすべて担う道具で、API は「構成」ではなく「判定法と普遍性」を中心に切る。極限 = 切断（安い）、余極限 = 局所化（高い）という非対称性が全体を通じて現れる。

*sixff-foundations.html — 局所化 — 定義と1-圏との比較*

C → C\[W⁻¹\] が Dwyer–Kan 局所化 ⇔ 任意の ∞-圏 D について Fun(C\[W⁻¹\], D) → Fun\_W(C, D)（W を同値に送る関手の充満部分圏）が圏同値。

- 1-圏版（Gabriel–Zisman）は射集合がジグザグの商。Mathlib には Riou による \`CategoryTheory.Localization\` がある。

- ∞ 版は写像空間がジグザグ全体の空間（ハンモック空間）で、高次の情報を保つ。

- ho(C\[W⁻¹\]) ≃ (ho C)\[W⁻¹\]。Mathlib の \`DerivedCategory\`（K(A) を擬同型で1-圏的に局所化したもの）は ∞ 版 D(A) のホモトピー圏とちょうど一致し、D6 の橋の半分はこの一般論から出る。

*sixff-foundations.html — 局所化 — 二種類の局所化*

- 種類　／　例　／　作り方　／　形式化の重さ
- 反射的（Bousfield）局所化　／　層化 PShv → Shv　／　充満部分圏 + 左随伴 L　／　軽い
- 一般の Dwyer–Kan 局所化　／　Ch(Λ) → D(Λ)、Corr\^fact → Corr、余極限　／　W を形式的に逆にする　／　重い

反射的局所化は W = \{f \| L(f) が同値\} の Dwyer–Kan 局所化。可能な限り反射的な形か具体的なモデルで実現する。D(Λ) は K-入射的複体の dg-nerve で作り、「Ch(Λ) → N\_dg(K-入射的複体) が擬同型での局所化」を示せば一般的な構成は要らない。

一般的な存在には、逆射の形式的な貼り付けと Joyal モデル構造での fibrant 置換が要り、これはまだ Mathlib にない（quasicategory の ∞-cosmos が未完なのと同じ根）。

*sixff-foundations.html — 局所化 — 判定法*

1. *充満忠実な右随伴があれば局所化*（反射的局所化。層化はこれで済む）。

2. *ファイバーが弱可縮なファイブレーション*：p: E → B が余デカルト（デカルト）ファイブレーションで各ファイバーが弱可縮なら、p はファイバー内の射での局所化。ファイバー内の射を逆にすると各ファイバーが可縮な ∞-亜群、つまり一点になる。B6 の Corr\^fact → Corr(C, E)（ファイバー Fact(f)）がこの形だが、文字通り仮定を満たすかは原典で確認が要る。

3. *Quillen の定理 A の ∞ 版*：各 b でコンマ ∞-圏 E\_\{/b\} が弱可縮なら p は共終。余極限の計算と局所化の判定の両方に使う。

*sixff-foundations.html — 局所化 — 余極限との関係*

- S 値：colim F ≃ \|∫F\|（すべての射で局所化）

- Cat\_∞ 値：colim F ≃ ∫F\[余デカルト射⁻¹\]（HTT 3.3.4）

- Set 値：π₀(∫F) はその0-切断

:::definition "kerodon_6_3_1_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors_quasicategory")
Kerodon Notation 6.3.1.1（[Tag 01MF](https://kerodon.net/tag/01MF)）。対応表の状態：本体にある。

仮定：単体集合 X、試験 ∞ 圏 E、X の辺の族 W（Lean が弱い：構成自体は E の ∞ 圏性を要しない）。結論：invertingFunctors X E W は W を可逆辺に送る関手を頂点とする Fun(X,E) の全部分複体（一致）。

:::

:::definition "kerodon_6_3_1_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition")
Kerodon Definition 6.3.1.9（[Tag 01MP](https://kerodon.net/tag/01MP)）。対応表の状態：本体にある。

仮定：単体集合の射 F:X→D、辺の族 W、同一宇宙の試験 ∞ 圏 E（Kerodon と一致）。結論：F が W を反転し、Fun(D,E)→invertingFunctors X E W が圏同値。原文の充満忠実性と指定本質像に対応（一致）。

*04-yoneda-adjunction-kan.html — 4. 局所化と反射的部分圏 — 局所化*

\`\`\`text
def IsLocalization \{X D : SSet.\{u\}\} (F : X ⟶ D) (W : Set (X \_⦋1⦌)) : Prop :=
  ∃ hF : InvertsEdges F W, ∀ (E : SSet.\{u\}) \[Quasicategory E\],
    IsQCatEquivalence (localizationPrecomposition F W hF E)
\`\`\`

*f-03-localization.html — 2. 局所化の定義*

単体的集合 $`X`、辺の集合 $`W \subseteq X_1`、写像 $`F : X \to D` について、$`F` が \*\*$`W` での局所化\*\*であるとは、次の二つが成り立つことをいう。

1. $`F` は $`W` の辺をすべて可逆な辺に送る。

2. すべての quasicategory $`E`（同じ宇宙）について、前合成
$$`F^* : \mathrm{Fun}(D, E) \longrightarrow \mathrm{Fun}_W(X, E)`
  が ∞ 圏の同値である。ここで $`\mathrm{Fun}_W(X, E)` は、$`W` を可逆に送る関手のなす充満部分 ∞ 圏。

\`\`\`text
def IsLocalization \{X D : SSet.\{u\}\} (F : X ⟶ D) (W : Set (X \_⦋1⦌)) : Prop :=
  ∃ hF : InvertsEdges F W, ∀ (E : SSet.\{u\}) \[Quasicategory E\],
    IsQCatEquivalence (localizationPrecomposition F W hF E)
\`\`\`

InfinityCategories/Kerodon/AdjointFunctors/Localization/Localization.lean:79。$`\mathrm{Fun}_W(X, E)` は \`invertingFunctors X E W\`。

定義の細かい点

- \*\*$`D` が quasicategory であることは要求しない。\*\*実際、§3 の証明の途中に出てくる「逆辺を貼り付けた単体的集合」は quasicategory ではないが、局所化の普遍性は満たす。

- \*\*普遍性を確かめる相手 $`E` は同じ宇宙 \`u\` に限る。\*\*宇宙を変える補題（\`IsLocalization.ulift\` など、InfinityCategories/Kerodon/AdjointFunctors/Localization/Universe\*）が別にある。

- これは *Dwyer–Kan 局所化*（一般の局所化）の定義である。Bousfield 局所化（反射的局所化）は、その特別な場合として §6 で扱う。

:::

:::proposition "kerodon_6_3_1_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversalConsequences.IsLocalization.precomposition_isFullyFaithful, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversalConsequences.IsLocalization.exists_extension, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.isLocalization_of_fullyFaithful_extensions") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_4_8_4_4, kerodon_6_3_1_9")
Kerodon Proposition 6.3.1.13（[Tag 01MS](https://kerodon.net/tag/01MS)）。対応表の状態：一部。

IsLocalizationは同じFの全準圏への指定localizationPrecompositionの同値性、すなわち原文(2)を直接条件にする。(3),(4)のcoreのπ₀からの逆を含む四条件のiffは含まない。

*04-yoneda-adjunction-kan.html — 4. 局所化と反射的部分圏 — 局所化*

$`F` が $`W` を反転し、任意の quasicategory $`E` について、前合成 $`\mathrm{Fun}(D,E)\to\mathrm{Fun}_W(X,E)`（$`W` を反転する関手の充満部分 ∞ 圏）が同値であること（Kerodon Prop. 6.3.1.13(2) の普遍性）。この定義は第 3 章の一般の底への帰着（first vertex 写像が局所化）で決定的に使われている。

:::

:::proposition "kerodon_6_3_1_21" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localization_all_isKan, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion_isLocalization, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertsAllEdges_toKan") (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_1_8_2, kerodon_4_4_3_23, kerodon_6_3_1_13")
Kerodon Proposition 6.3.1.21（[Tag 01MY](https://kerodon.net/tag/01MY)）。対応表の状態：一部。

localization\_all\_isKanは同じFの全辺の局所化から原文の標的DのKan性を直接返す。Fの弱ホモトピー同値と逆方向は含まない。

:::

:::proposition "kerodon_6_3_1_22" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localization_postcomp_precompositionEquivalence, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.isLocalization_of_weakDeformation")
Kerodon Proposition 6.3.1.22（[Tag 02LS](https://kerodon.net/tag/02LS)）。対応表の状態：一部。

W′=∅、F′を前合成同値に限るとlocalization\_postcomp\_precompositionEquivalenceは同じ合成F≫F′がW=W∪∅の局所化になると直接返す。一般の第二の辺集合の局所化ではない。

:::

:::corollary "kerodon_6_3_1_23" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization.of_subset_invertedEdges")
Kerodon Corollary 6.3.1.23（[Tag 02LT](https://kerodon.net/tag/02LT)）。対応表の状態：本体にある。

仮定：W で局所化する F と追加の辺の族（Lean が弱い：像が退化でなく可逆ならよい）。結論：W と追加の辺の和集合に対しても IsLocalization（一致）。

:::

# 6.3.2 Existence of Localizations

%%%
number := false
tag := "kerodon-6-3-2"
%%%

Kerodon [Tag 01MZ](https://kerodon.net/tag/01MZ)

*f-03-localization.html — 3. 存在：任意の辺の集合で局所化できる*

定理

任意の単体的集合 $`X` と辺の集合 $`W` について、quasicategory $`Q` と、$`W` での局所化 $`F : X \to Q` が存在する。

\`\`\`text
theorem exists\_quasicategory\_localization (X : SSet.\{u\}) (W : Set (X \_⦋1⦌)) :
    ∃ (Q : SSet.\{u\}) (F : X ⟶ Q), Quasicategory Q ∧ IsLocalization F W
\`\`\`

InfinityCategories/Kerodon/AdjointFunctors/Localization/LocalizationResolution.lean:41。選択した局所化に名前を付けたものが \`edgeLocalization X W\`・\`edgeLocalizationMap\`（InfinityCategories/Kerodon/AdjointFunctors/Localization/GeneralLocalization.lean）。

証明は三段で、どれも第 1・2 章の道具でできている。

*f-03-localization.html — 3. 存在：任意の辺の集合で局所化できる — 3.2 段 2：W の辺ごとに J を貼り付ける*

$`W` の各辺 $`w` について、$`\Delta^1 \xrightarrow{w} X` と $`\Delta^1 \to J` の pushout をとる（全部まとめて）。

$$`P \;=\; X \sqcup_{\coprod_{w \in W} \Delta^1} \coprod_{w \in W} J`

（\`inverseAttachment X W\`、InfinityCategories/Kerodon/AdjointFunctors/Localization/InverseAttachment.lean:47）。$`X \to P` は $`W` の辺を可逆な辺に送る。

*主張*：どの quasicategory $`Y` についても、制限写像 $`\mathrm{Fun}(P, Y) \to \mathrm{Fun}_W(X, Y)` は*自明 Kan fibration* である（\`inverseAttachmentRestriction\_trivialKanFibration\`、InfinityCategories/Kerodon/AdjointFunctors/Localization/InverseAttachmentUniversal.lean）。

理由は次のとおり。$`P` への関手は「$`X` への関手」と「各 $`J` への延長」の組である。
$`W` を可逆に送る関手なら、各 $`w` の像は $`Y` の可逆な辺で、可逆な辺は $`Y` の core（Kan 複体）に入る。
$`\Delta^1 \to J` は anodyne なので、Kan 複体への写像は延び、延長の空間は可縮になる。
境界からの延長の問題に直すと、ちょうど自明 Kan fibration の持ち上げ条件になる。

自明 Kan fibration は同値なので（§1）、$`X \to P` は局所化である（\`inverseAttachment\_isLocalization\`）。ただし $`P` は quasicategory とは限らない。

*f-03-localization.html — 3. 存在：任意の辺の集合で局所化できる — 3.3 段 3：quasicategory に置き換える*

$`P \to \ast` を「inner anodyne の後に inner fibration」に分解する（第 1 章 §1.4 の \`exists\_quasicategory\_resolution\_over\`）。

$$`P \xrightarrow{\ j\ (\text{inner anodyne})\ } Q \to \ast,\qquad Q \text{ は quasicategory}`

inner anodyne $`j` について、どの quasicategory $`Y` でも前合成 $`j^* : \mathrm{Fun}(Q, Y) \to \mathrm{Fun}(P, Y)` は同値である（\`isPrecompositionEquivalence\_of\_innerAnodyne\`）。
局所化に前合成同値を後ろから合成しても局所化なので（\`localization\_postcomp\_precompositionEquivalence\`）、$`X \to P \to Q` が求める局所化になる。

この証明の性格

- 使っているのは、Kan 置換、pushout、自明 Kan fibration、inner anodyne 置換だけで、モデル構造も straightening も使わない。

- 得られるのは*存在と普遍性*で、$`Q` の写像空間は分からない（$`J` を貼り付けて置き換えた後の形は具体的に計算しにくい）。写像空間の計算には、§5 の hammock 局所化や、第 5 章の分数を使う。

- この定理は InfinityCategories/Kerodon/AdjointFunctors/Localization にある（\`exists\_quasicategory\_localization\`、LocalizationResolution）。

:::proposition "kerodon_6_3_2_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.exists_quasicategory_localization, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.inverseAttachment_isLocalization")
Kerodon Proposition 6.3.2.1（[Tag 01N0](https://kerodon.net/tag/01N0)）。対応表の状態：本体にある。

仮定：単体集合 X と任意の辺の族 W（Kerodon と一致）。結論：Quasicategory Q と IsLocalization F W を満たす F:X→Q が存在（一致）。

*f-03-localization.html — 3. 存在：任意の辺の集合で局所化できる — 3.1 段 1：可逆な辺の「歩く版」を作る*

$`\Delta^1`（一本の辺）を Kan 置換したものを $`J` とする（\`walkingEquivalence := AnodyneKanReplacement.functor.obj Δ\[1\]\`、InfinityCategories/Kerodon/AdjointFunctors/Localization/WalkingEquivalence.lean:25）。

- $`J` は Kan 複体なので、すべての辺が可逆である。

- 包含 $`\Delta^1 \to J` は anodyne である。

つまり $`J` は「可逆な辺が一本ある、可縮な空間」で、$`J` から $`Y` への関手は「$`Y` の可逆な辺」と（ホモトピーを除いて）同じものになる。

:::

:::proposition "kerodon_6_3_2_4" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_5_3_19, kerodon_4_5_3_22, kerodon_4_5_3_28")
Kerodon Proposition 6.3.2.4（[Tag 05ZD](https://kerodon.net/tag/05ZD)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：上辺が局所化の四角で categorical pushout と下辺が像の辺を反転する局所化との同値。初頂点射の strict pushout の閉性は指定射の特別な場合。

:::

:::corollary "kerodon_6_3_2_5" (uses := "kerodon_1_1_0_6, kerodon_6_3_2_4")
Kerodon Corollary 6.3.2.5（[Tag 05ZG](https://kerodon.net/tag/05ZG)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：互いに重ならない指定辺を Δ⁰ へ潰す商の局所化性。inverseAttachment は各辺に walking equivalence を貼る別の pushout。

:::

:::corollary "kerodon_6_3_2_7" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_4_6_5, kerodon_6_3_2_5")
Kerodon Corollary 6.3.2.7（[Tag 05ZJ](https://kerodon.net/tag/05ZJ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Δ³ の二つの指定辺を縮約した Q→Δ⁰ の圏同値。walking equivalence の一点への同値はこの Q を比較しない。

:::

:::corollary "kerodon_6_3_2_8" (uses := "kerodon_6_3_2_7")
Kerodon Corollary 6.3.2.8（[Tag 05ZK](https://kerodon.net/tag/05ZK)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Δ³ の二辺を潰した Q に残る中央の辺 Δ¹→Q が全辺に関する局所化。KST の付着模型とこの Q の比較は未確認。

:::

:::corollary "kerodon_6_3_2_9" (uses := "kerodon_1_1_0_6, kerodon_6_3_2_4, kerodon_6_3_2_8")
Kerodon Corollary 6.3.2.9（[Tag 05ZL](https://kerodon.net/tag/05ZL)）。対応表の状態：なし。

inverseAttachmentはwalkingEquivalenceを貼るpushout。原文の指定Qを貼るpushoutとは別の対象・射であり、Qとの比較なしには同じ局所化の特殊形ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.inverseAttachment`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.inverseAttachment_isLocalization`

:::

:::proposition "kerodon_6_3_2_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.edgeLocalization, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.exists_quasicategory_localization") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_1_3_2, kerodon_6_3_2_9")
Kerodon Proposition 6.3.2.11（[Tag 05ZP](https://kerodon.net/tag/05ZP)）。対応表の状態：一部。

exists\_quasicategory\_localizationは原文の全ての(C,W)について準圏と局所化射の存在を直接返す。関手性とfiltered colimitの保存は含まない。

:::

:::corollary "kerodon_6_3_2_12" (uses := "kerodon_1_1_0_6, kerodon_4_8_8_11, kerodon_6_3_2_11")
Kerodon Corollary 6.3.2.12（[Tag 05ZQ](https://kerodon.net/tag/05ZQ)）。対応表の状態：なし。

引用はcolimitの単体集合c.ptに対する初頂点写像の局所化。原文のarrow categoryのcolimitとなる射との比較、指定辺集合Sが初頂点保存辺集合と一致する比較を型に持たない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap_isLocalization_of_sequential_colimit`

:::

:::proposition "kerodon_6_3_2_13" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_9_5_7, kerodon_6_3_2_9")
Kerodon Proposition 6.3.2.13（[Tag 05ZR](https://kerodon.net/tag/05ZR)）。対応表の状態：なし。

同じ宇宙の局所化の存在は、原文の指定κのessential smallnessが任意の局所化へ移る主張ではない。数値κへの評価と任意標的との比較を欠く。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.exists_quasicategory_localization`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.edgeLocalization`

:::

# 6.3.3 Reflective Localizations

%%%
number := false
tag := "kerodon-6-3-3"
%%%

Kerodon [Tag 02FY](https://kerodon.net/tag/02FY)

*04-yoneda-adjunction-kan.html — 4. 局所化と反射的部分圏 — 反射的部分圏*

\`\`\`text
structure ReflectiveSubcategory (X : SSet.\{u\}) \[Quasicategory X\] (P : X \_⦋0⦌ → Prop) where
  reflector : X ⟶ (fullSubcomplexOnVertices X P : SSet.\{u\})
  adjunction : QCatAdjunction reflector (fullSubcomplexOnVertices X P).ι
\`\`\`

頂点の条件 $`P` が張る充満部分 ∞ 圏への、包含の左随伴を指定したもの。ここから次が導かれる（F1B/Reflective\*）。

- 余単位は可逆で、$`L\circ L\simeq L`（\`counitIso\`、\`idempotentIso\`）

- 局所対象（単位が可逆な対象）は本質的像と一致する（\`isLocal\_iff\_essentialImage\`）

- 反射は、自身が反転する辺についての局所化（\`ReflectiveSubcategory.isLocalization\`）

一般の局所化の*存在*（Bousfield 局所化）は含まれていない。これは presentable の理論（第 6 章、P レーン）の範囲である。

*f-03-localization.html — 6. Dwyer–Kan 局所化と Bousfield 局所化*

*Bousfield 局所化*（反射的局所化）とは、充満部分圏 $`C_{\mathrm{loc}} \subseteq C` の包含が左随伴 $`L` を持つ状況である。このとき、次が成り立つ。

$$`L : C \to C_{\mathrm{loc}} \ \text{は}\ W_L = \{ f \mid L(f) \text{ が同値} \}\ \text{での局所化},\qquad \mathrm{Map}_{C[W_L^{-1}]}(x, y) \simeq \mathrm{Map}_C(x, Ly)`

抽象的な局所化を $`C` の中の部分圏として実現でき、写像空間が $`C` の写像空間で計算できる。これが Bousfield 局所化の利点である。
presentable な ∞ 圏と射の集合 $`S` に対しては、$`S`-局所的な対象への反射が存在する（HTT 5.5.4.15。InfinityCategories/Kerodon/LargeInfinityCategories/PresentableInfinityCategories/BousfieldReflection の \`bousfieldReflection\`）。
それが $`S` の生成する強飽和な集まりでの局所化であることは \`bousfieldLocalizationFunctor\_isLocalization\_generatedEdges\` にある。

逆に、一般の局所化は右随伴を持つとは限らない。例えば、小さい安定 ∞ 圏の Verdier 商は、ふつう右随伴を持たない（第 5 章）。

:::definition "kerodon_6_3_3_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization.saturate, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges")
Kerodon Definition 6.3.3.1（[Tag 04JG](https://kerodon.net/tag/04JG)）。対応表の状態：本体にある。

IsLocalization F WをWで存在量化すれば原文の定義そのもの。さらにIsLocalization.saturateでFが反転する全辺をWに選べる。専用のlocalization functorという名前がないことをpartial理由にしない。

:::

:::proposition "kerodon_6_3_3_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization.saturate, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges")
Kerodon Proposition 6.3.3.3（[Tag 04JH](https://kerodon.net/tag/04JH)）。対応表の状態：本体にある。

仮定：∞ 圏間の F（Lean が弱い：saturate 自体は単体集合間で成立）。結論：ある W について IsLocalization F W なら反転する全辺についても IsLocalization。逆は全辺を W に選ぶ（一致）。

:::

:::definition "kerodon_6_3_3_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.inclusion_fullyFaithful")
Kerodon Definition 6.3.3.4（[Tag 02G9](https://kerodon.net/tag/02G9)）。対応表の状態：一部。

Fを選んだReflectiveSubcategoryのreflectorに限ると、構造のadjunctionは同じFの右随伴が充満包含であると直接与える。任意Fを指定して定める述語全体は含まない。

:::

:::proposition "kerodon_6_3_3_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.isLocalization, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.isLocalization")
Kerodon Proposition 6.3.3.7（[Tag 04JL](https://kerodon.net/tag/04JL)）。対応表の状態：一部。

右随伴と可逆counitを指定した場合、QCatAdjunction.isLocalizationは同じFの局所化性を直接与え、右随伴の存在と合わせて原文(2)を返す。右随伴の充満忠実性からのcounit比較・逆方向は含まない。

:::

:::definition "kerodon_6_3_3_9"
Kerodon Variant 6.3.3.9（[Tag 04JR](https://kerodon.net/tag/04JR)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：充満忠実な左随伴を持つ右関手としての coreflective localization。AdjointLocalization は可逆余単位をもつ左関手側。

:::

# 6.3.4 Fiberwise Localization

%%%
number := false
tag := "kerodon-6-3-4"
%%%

Kerodon [Tag 02LU](https://kerodon.net/tag/02LU)

:::theorem "kerodon_6_3_4_1" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_6_3_4_2, kerodon_6_3_4_4")
Kerodon Theorem 6.3.4.1（[Tag 038U](https://kerodon.net/tag/038U)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：cocartesian fibration の四角でファイバー局所化と底の局所化から全空間の局所化を得る主張。通常の ∞ 圏の局所化はこの輸送条件を持たない。

:::

:::proposition "kerodon_6_3_4_2" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_5_8_1, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_5_1_4_17, kerodon_5_1_7_15, kerodon_5_3_6_9")
Kerodon Proposition 6.3.4.2（[Tag 02LW](https://kerodon.net/tag/02LW)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：同じ底上の cocartesian fibration 間でファイバーごとの指定辺を反転した局所化の比較。relativeFunctorPost の同値は各ファイバーが局所化である条件を使わない。

:::

:::corollary "kerodon_6_3_4_3" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_5_1_4_1, kerodon_6_3_1_21, kerodon_6_3_4_2")
Kerodon Corollary 6.3.4.3（[Tag 02LY](https://kerodon.net/tag/02LY)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：弱可縮なファイバーをもつ cocartesian fibration が垂直辺に関する局所化。Kan ファイバーの可縮性から同値を得る型では一般の垂直辺を反転しない。

:::

:::proposition "kerodon_6_3_4_4" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_1_3_3, kerodon_5_1_1_1, kerodon_5_1_1_9, kerodon_5_1_4_1, kerodon_5_3_6_1, kerodon_5_3_6_9, kerodon_5_6_7_2, kerodon_6_3_4_2")
Kerodon Proposition 6.3.4.4（[Tag 038W](https://kerodon.net/tag/038W)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：底の局所化を cocartesian fibration に沿って引き戻し、像が指定の辺となる cocartesian 辺を反転。任意の底変換での cocartesian 性だけでは局所化がない。

:::

:::corollary "kerodon_6_3_4_5"
Kerodon Corollary 6.3.4.5（[Tag 038X](https://kerodon.net/tag/038X)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：底の局所化を left fibration に沿って引き戻したときの局所化。Space 値分類の自然性は反転すべき辺を定めない。

:::

:::proposition "kerodon_6_3_4_6"
Kerodon Proposition 6.3.4.6（[Tag 02LV](https://kerodon.net/tag/02LV)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：積 K×F が K 側で退化する指定辺に関する局所化。precomposition equivalence の積安定性は局所化の対象となる関手の充満部分圏を指定しない。

:::

# 6.3.5 Universal Localizations

%%%
number := false
tag := "kerodon-6-3-5"
%%%

Kerodon [Tag 02LZ](https://kerodon.net/tag/02LZ)

:::definition "kerodon_6_3_5_1" (uses := "kerodon_1_1_0_6")
Kerodon Definition 6.3.5.1（[Tag 02M0](https://kerodon.net/tag/02M0)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：すべての底変換が、退化辺に写る辺に関する局所化となる universally localizing の定義。IsLocalization は単一の射と辺集合についての条件。

:::

:::proposition "kerodon_6_3_5_3" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_4_1_13, kerodon_3_4_1_16, kerodon_6_3_1_13")
Kerodon Proposition 6.3.5.3（[Tag 01N7](https://kerodon.net/tag/01N7)）。対応表の状態：なし。

引用は単体圏の初頂点写像を各頂点とする特定のcubeの局所化。原文の任意の二つのcategorical pushoutと指定Wの和集合の比較への型の対応がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap_isLocalization_of_isPushout`

:::

:::proposition "kerodon_6_3_5_4" (uses := "kerodon_1_1_0_6, kerodon_1_1_4_12, kerodon_1_4_0_1, kerodon_6_3_1_23, kerodon_6_3_2_12, kerodon_6_3_5_1, kerodon_6_3_5_3")
Kerodon Proposition 6.3.5.4（[Tag 02M1](https://kerodon.net/tag/02M1)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：各 Δⁿ 上の局所化と任意の底変換に対する局所化の条件の同値。頂点ごとの通常の pullback 比較は全単体を試す局所判定ではない。

:::

:::corollary "kerodon_6_3_5_5" (uses := "kerodon_1_1_0_6")
Kerodon Corollary 6.3.5.5（[Tag 02M2](https://kerodon.net/tag/02M2)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：universally localizing なら恒等底変換で退化像の辺の局所化になる帰結。IsLocalization の単調性には universally localizing の入力がない。

:::

:::proposition "kerodon_6_3_5_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DeformationLocalization.isLocalization_of_deformation") (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Proposition 6.3.5.9（[Tag 04JT](https://kerodon.net/tag/04JT)）。対応表の状態：一部。

sectionを持つfについて、指定した単体ホモトピーとその全成分をfが反転する条件を明示的に加えればisLocalization\_of\_deformationは同じfの局所化を直接返す。universalに要求される底変換のうち恒等底変換の成分だけで、任意底変換ではない。

:::

:::proposition "kerodon_6_3_5_10"
Kerodon Proposition 6.3.5.10（[Tag 02M6](https://kerodon.net/tag/02M6)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：universally localizing なら各次数で全射。dgUniversalCommaTarget\_degree\_surjective は特定の dg 比較写像だけの全射性。

:::

:::proposition "kerodon_6_3_5_11"
Kerodon Proposition 6.3.5.11（[Tag 02M7](https://kerodon.net/tag/02M7)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：任意の二つの universally localizing 射の合成安定性。一般の射のクラスの universally 構成と局所化クラスの合成との同定はない。

:::

:::corollary "kerodon_6_3_5_12"
Kerodon Corollary 6.3.5.12（[Tag 02M8](https://kerodon.net/tag/02M8)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：弱可縮な K を積に足した X×K→S が universally localizing。弱ホモトピー同値な射影の型に任意の底変換の辺の局所化はない。

:::

:::proposition "kerodon_6_3_5_13" (uses := "kerodon_1_1_0_6, kerodon_6_3_2_12, kerodon_6_3_5_4")
Kerodon Proposition 6.3.5.13（[Tag 02M9](https://kerodon.net/tag/02M9)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：arrow 圏で universally localizing 射がフィルター余極限に閉じること。初頂点写像の可算余極限は任意の引き戻しを量化しない。

:::

:::proposition "kerodon_6_3_5_14" (uses := "kerodon_1_1_0_6, kerodon_4_5_5_11, kerodon_6_3_5_3, kerodon_6_3_5_4")
Kerodon Proposition 6.3.5.14（[Tag 02MA](https://kerodon.net/tag/02MA)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：指定 pushout の三射が universally localizing なら残りの射も同様。pushout の anodyne 閉性では退化像の辺の局所化にならない。

:::

# 6.3.6 Subdivision and Localization

%%%
number := false
tag := "kerodon-6-3-6"
%%%

Kerodon [Tag 02MC](https://kerodon.net/tag/02MC)

:::theorem "kerodon_6_3_6_1"
Kerodon Theorem 6.3.6.1（[Tag 02MD](https://kerodon.net/tag/02MD)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：任意の単体集合 S に半順序の nerve から universally localizing 射があること。単体の圏の初頂点射の局所化は定義域が半順序とは限らない。

:::

:::proposition "kerodon_6_3_6_2" (uses := "kerodon_1_1_0_6, kerodon_1_1_4_12, kerodon_3_3_3_1, kerodon_3_3_4_3, kerodon_6_3_5_9, kerodon_6_3_5_13, kerodon_6_3_5_14")
Kerodon Proposition 6.3.6.2（[Tag 02ME](https://kerodon.net/tag/02ME)）。対応表の状態：なし。

sdとsubdivisionLastVertexMapは原文の射の構成まで。局所化・任意の底変換の局所化のいずれもこの型の結論にはない。

宣言：`SSet.sd`、`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionLastVertexMap`

:::

:::definition "kerodon_6_3_6_4"
Kerodon Variant 6.3.6.4（[Tag 04JU](https://kerodon.net/tag/04JU)）。対応表の状態：なし。

transportSimplexFirstVertexMapはN(Δ\_S)からSへの初頂点写像。原文はN(Δ\_S)からSd(S)への指定ψであり、始域が同じだけで別の射。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.transportSimplexFirstVertexMap_isLocalization`

:::

:::corollary "kerodon_6_3_6_5"
Kerodon Corollary 6.3.6.5（[Tag 04JV](https://kerodon.net/tag/04JV)）。対応表の状態：なし。

引用は初頂点写像の局所化。原文はSdを経由する最終頂点写像の合成で、同じ射に比較する型がない。局所化性とuniversal性の差に先立ち射が異なる。

*03-straightening.html — 4. 証明の経路 — 第二段：一般の底への帰着*

任意の単体的集合 $`B` に対し、単体の圏 $`\Delta_{/B}`（Lean では \`TransportSimplexCategory B\`）と、各単体をその*最初の頂点*に送る写像

$$`\mathrm{fv}\colon N(\Delta_{/B})\longrightarrow B`

を考える。鍵になるのは次の事実である。

*命題.* $`\mathrm{fv}` は、「始点を保つ辺」の集合 $`W` に関する局所化である。すなわち $`W` を反転する関手 $`N(\Delta_{/B})\to\mathcal E` は、$`B` からの関手に（同型を除いて一意に）降りる。

Lean：\`transportSimplexFirstVertexMap\_isLocalization\`（F1/TransportLocalizationAllBases）。証明は $`B` の骨格に沿った帰納法で、境界の次元、小さい余積、骨格の pushout、可算の逐次余極限の各段で局所化が保たれることを示す（F1/TransportLocalization\*）。$`B` に quasicategory であることは仮定しない。

*f-b-literature-yoneda.html — 9. straightening の構成と $`h_y` の関手性 — 9.5 St の第二段：一般の quasicategory の底*

- 対象　／　定義（コード）
- 単体の圏　／　TransportSimplexCategory B：対象は $`B` の単体 $`\sigma\in B_n`、射 $`\sigma\to\tau` は $`\theta\colon[m]\to[n]` で $`\theta^*\sigma=\tau`（制限）。普通の $`\Delta_{/B}` の反対（要素の圏）。この向きでのみ最初の頂点への写像が共変（普通の向きでは最後の頂点への写像が共変）
- $`\mathrm{fv}`　／　transportSimplexFirstVertexMap：制限の列 $`\sigma_0\to\cdots\to\sigma_k` の各 $`\sigma_i` の頂点 0 を $`\sigma_0` の中に戻した $`a_i=\theta_i(0)` は $`a_0\le\cdots\le a_k`（transportSimplexFirstVertexOrderHom）。$`\sigma_0` をこの単調列で制限した $`k` 単体を返す。$`B` は quasicategory でなくてよい
- $`W`　／　transportSimplexInitialEdges：最初の頂点を保つ制限（$`\theta(0)=0`）。$`\mathrm{fv}` はこれを退化辺に送る（transportSimplexFirstVertexMap\_inverts）

$`X` を $`\mathrm{fv}` で引き戻して第一段を適用すると $`W` を反転する関手が得られ、局所化の普遍性で $`B` に降りる。これが $`\mathrm{St}(X)`。

*f-b-literature-yoneda.html — 9. straightening の構成と $`h_y` の関手性 — 9.6 局所化（先に用意するもの）*

IsLocalization F W（F1B）：$`F\colon X\to D` が $`W` を可逆にし、すべての quasicategory $`E` について $`F^*\colon\mathrm{Fun}(D,E)\to\mathrm{Fun}_W(X,E)`（invertingFunctors）が ∞ 圏の同値。

*f-b-literature-yoneda.html — 9. straightening の構成と $`h_y` の関手性 — 9.7 $`\mathrm{fv}` が局所化であることの証明*

主定理 transportSimplexFirstVertexMap\_isLocalization。$`P(X)`：$`\mathrm{fv}_X` は $`W_X` での局所化。

- 部品　／　内容　／　ファイル
- 1. 標準単体　／　切断 $`s\colon\Delta^n\to N(\cdot)`（各頂点 $`i` に $`i` を最初の頂点にもつ単体、transportStandardSection）で $`\mathrm{fv}\circ s=\mathrm{id}`。$`s\circ\mathrm{fv}` と恒等の間の自然変換の成分が $`W` に入る（transportStandardSectionHomotopy）。$`s^*\mathrm{fv}^*=\mathrm{id}`、$`\mathrm{fv}^*s^*` は $`W` を反転する関手には可逆な自然変換で恒等と同型（transportStandardInvertingFamilyIso）。反射的局所化の型　／　StandardLocalization
- 2. 余積　／　$`\mathrm{Fun}(\coprod X_i,E)=\prod\mathrm{Fun}(X_i,E)`、単体の圏も余積　／　LocalizationCoproduct
- 3. 押し出し　／　単射に沿った押し出し。$`A` の部分は制限で閉じているので二つの部分をまたぐ射の列がなく、脈体も押し出しを保つ。$`\mathrm{Fun}(-,E)` は押し出しを isofibration に沿った引き戻しに送り、成分ごとの同値から全体の同値　／　LocalizationPushout
- 4. 列の余極限　／　isofibration の塔の極限で、各段が同値なら極限も同値　／　LocalizationSequential

*組み立て*（LocalizationAllBases）：0 次元の骨格（点の余積）から始め、$`n+1` 次元の骨格を $`\coprod\partial\Delta^{n+1}\to\coprod\Delta^{n+1}` に沿った押し出しとして得る。境界 $`\partial\Delta^{n+1}` は $`n` 次元の骨格なので帰納法の仮定（境界の次元帰納）、余積に部品 2、$`\Delta^{n+1}` に部品 1、貼り合わせに部品 3。最後に $`B=\operatorname{colim}_n\mathrm{sk}_nB` に部品 4。モデル圏は使わない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.transportSimplexFirstVertexMap_isLocalization`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.transportSimplexFirstVertexMap_ulift_isLocalization`

:::

:::definition "kerodon_6_3_6_6" (lean := "SSet.Nonsingular")
Kerodon Definition 6.3.6.6（[Tag 02MG](https://kerodon.net/tag/02MG)）。対応表の状態：Mathlib にある。

仮定：任意の単体集合 S（Kerodon と一致）。結論：Nonsingular S は各非退化単体の Yoneda に対応する Δⁿ→S が単射であること（一致）。

:::

:::corollary "kerodon_6_3_6_13"
Kerodon Corollary 6.3.6.13（[Tag 02MP](https://kerodon.net/tag/02MP)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：nonsingular S を半順序 nerve から universally localizing に解消。薄い nerve の内ファイブレーションにはこの存在条件がない。

:::

:::proposition "kerodon_6_3_6_14"
Kerodon Proposition 6.3.6.14（[Tag 02MQ](https://kerodon.net/tag/02MQ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：任意の S に対して nonsingular な始域を持つ universally localizing 射の存在。inner anodyne resolution は通常逆向き。

:::

:::lemma_ "kerodon_6_3_6_15"
Kerodon Lemma 6.3.6.15（[Tag 02MR](https://kerodon.net/tag/02MR)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：nonsingular 単体集合の極限での閉性。presheaf の点ごとの極限は非退化単体の頂点が相異なる性質を特定しない。

:::

:::definition "kerodon_6_3_6_17"
Kerodon Variant 6.3.6.17（[Tag 02MU](https://kerodon.net/tag/02MU)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：有限な S に対し有限半順序の nerve からの universally localizing な表示。一般の単体圏からの局所化は有限性と半順序性を同時に主張しない。

:::

