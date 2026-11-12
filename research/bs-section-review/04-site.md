# §4 prismatic site と HT 比較の定式化：リファクタの提案と、形式化の計画の提案（2026-11-12）

作成：ノートのチャット（形式化の調整役ではない）。§2・§3 と同じ形。**扱いは調整役が判断する。** 事実に推奨を添える。

- 基準：main 973ac15ab 前後。読み取りだけのエージェントがノートの加筆 3 本、コードの見直し 1 本（その中の drafts と本体の突き合わせ 1 本を含む）、件数の追加の調べ 1 本。宣言の位置は grep で確かめたもの。規模の見立ては推測。
- 「主定理の閉包」は `SerrePositivity.Paper.Statement` の import の推移閉包。
- 二種類の提案：**A. リファクタ（R4-1〜R4-7）**、**B. 形式化の計画（§3 の表）**。
- §4 の計画上の位置：`stage-ii-second-half.md` の ⑤∞ で、5∞-1（∞ 層の一般論 S1〜S8）は B3 と 3a-2〜3a-4（G8・G14・G9）の後、5∞-2（A0：site の RΓ、C^• が Δ を計算）は 5∞-1 と 3b-2（G10）の後。5∞-3（A1：HT 比較の組み立て、D68 の置き換え）は 3b-2・3b-4 の後で、5∞-2 には依らない。

## 0. 規模と配置（事実）

- `BhattScholze/Prismatic/` は平らなディレクトリで 320 本・42,712 行。B3 の配置案（`refactor/kerodon-layout` 枝の `formalization-plans/stage-ii/report-bulk-w1.md` :155–185、24151a43d）の仮の仕分けは Crystalline 204、CechAlexander 39、HodgeTate/Comparison 37、HodgeTate/Affine 16、Site 13、Envelopes 7、§7 へ 3（FiniteEnvelope*）、§2 へ 1（RelativeCompleteRegularity）。§4 の本体にあたるのは Site・CechAlexander・HodgeTate/Affine・Envelopes の約 75 本で、残り約 240 本は §5・§6。
- **本体と drafts の分かれ方**（確認済み）：§4 の 1 圏の部分（site の圏・平坦位相・構造環とその剰余の層条件、Čech–Alexander の組み立て・弱始性・余積・複体、affine 直線の小さい模型と項ごとの底変換、大きい模型との比較、多項式代数の HT 写像と Lemma 4.10、主張の型 `HodgeTateIsoStatement`）は本体に sorry なしで入っている。∞ の部分（D(A) 値の構造前層、層条件、site の RΓ、Δ ＝ Tot、κ 不変性、Lemma 4.20・4.22、Cor 4.12）は drafts だけ。本体には ∞ の層の層（`IsSheaf`・層化・`derivedGlobalSections`）がまだない。
- 本体の `HodgeTateIsoStatement`（`HodgeTateCompletedMap.lean:461`）は、Rem 4.19 の鎖複体の模型 `reducedModel`（`HodgeTateAffineModel.lean:93`）のコホモロジーについての主張で、site の RΓ についての主張ではない。site の RΓ と結ぶのは 5∞-2（模型が Δ を計算する）と D27（CAlg 値の比較）。

## 1. A. リファクタの提案（今あるコードを直す）

### R4-1 drafts/A0 の古典的な部分は本体に置き換わっている：⑤∞ の前に drafts を整理する【推奨：B3 か 5∞-2 の最初】

drafts/A0・A1 の宣言の約半分は、本体に同じ名前・同じ内容で sorry なしにある（drafts の側は sorry）。5∞-2 で drafts を本体に移すとき、二重にならないよう先に drafts から外すか、本体の宣言を指す形に書き換える。

| drafts | 本体（証明済み） | 種類 |
| --- | --- | --- |
| A0/CechAlexander の `cechIndex`:58・`cechIndexMap`:64・`cechFreeDelta`:71・`cechFreeDeltaMap`:77・`cechEval`:84・`cechKernel`:94・`generator_mem_cechKernel`:99・`HasEnvelopes`:109・`cechAlexanderObj`:133・`cechAlexander`:159・`cechAlexanderObj_weaklyInitial`:171・`cechAlexander_isCoproduct`:179・`smallCechNerveOfCoproducts`:187・`cechNerveData`:200・`cechSmall_weaklyTerminal`:204・`cechAlexanderComplex`:253・`cechAlexanderReducedComplex`:260（17 宣言） | `Prismatic/CechAlexanderEnvelopeData`・`FreeDelta`・`Assembly`・`Small`・`Complex` | 同じ |
| A0/CechAlexander の `cechAlexanderAffine_isCoproduct`:266・`cechAlexanderAffine_baseChange`:299 | `AffineCechSiteNerve:33`・`AffineCechPrismBaseChange:49`（drafts は `envelopeBaseChangeRing`、本体は `PrismCompletedTensor` を使う） | 同じ（型の書き方だけ違う） |
| A0/CechAlexander の `hasEnvelopes_of_polynomial`:122（任意の T） | `hasEnvelopes_of_finitePolynomial`（`BigCechSiteAffine:43`、有限変数） | 本体が特別な場合 |
| A0/FlatDescent の `isFaithfullyFlat_of_isIso`:135・`IsFaithfullyFlat.comp`:142・`exists_isPushout_isFaithfullyFlat`:152・`exists_boundedPrism_of_completelyFlat`:113 | `FlatCover:45・61`・`FlatTopologyPushout:43`・`Prism/Bounded/CompletelyFlatPrism:70` | 同じ |
| A0/FlatDescent の `structurePresheaf_isSheaf`:168・`reducedStructurePresheaf_isSheaf`:176、`isDiscrete_of_completelyFlat_boundedPrism`:94 | `FlatCechDescent:179・184`（大きい site）、`Prism/Bounded/CompleteFlatDiscrete:39`（`DerivedCategory.Minus` で） | 模型が違う（内容は証明済み） |
| A0/PrismaticSite の `PrismOver.IsFaithfullyFlat`:65、`structurePresheaf`:127・`reducedStructurePresheaf`:138、`flatTopology_refine`:115 | `FlatCover:40`、`structureRing`・`quotientStructureRing`（`FlatSiteSheaf`）、`flatCoverage`（`FlatSiteSheaf:36`、Cor 3.12 の押し出しから） | 同じ／模型が違う／置き換わった |
| A0/PrismaticEnvelope の `IsCompletelyRegularRel`:59、`envelopeBaseChangeRing`:63 と脚 :76・:80 | `RelativeCompleteRegularity:149`（本体の方が一般）、`PrismCompletedTensor`（`Prism/Bounded/CompletedTensor:63`）と左右の脚 | 置き換わった／同じ（改名） |
| A1/HodgeTateMap の `htOneData`:54・`betaSquareZero_of_line`:65、A1/HodgeTateComparison の `bockstein_sq_zero'`:358 | `hodgeTateMapOne_smul_d`（`HodgeTateOneDerivative:219`）、`bockstein_sq_zero`（`HodgeTateBocksteinSquare:65`、任意の有界向き付き基底で証明済み） | 薄い包み（消すだけでよい） |
| A1/HodgeTateComparison の `crystallineCoverMap_torAmplitude`:227・`_finiteTorAmplitude`:236 | `Prism/Basic/CrystallineCoverCompleteTor`（鎖複体版の振幅で証明済み） | 模型が違う（内容は証明済み） |
| A5/PerfectSite の `perfectPrism_hom_lift_unique`:229 | `Andre.existsUnique_perfectPrismHomLift_to_bounded`（`Prism/PerfectPrismHomLift:749`） | 一行の包み |
| Sheaves/CechConerveLimit の `IsWeaklyTerminal`:51・`CechNerveData`:57 | `CategoryTheory/CechNerveData:33・44`（欄も同じ） | 同じ |

- drafts にしかない（∞ の部分、5∞-1・5∞-2 で本体に入るもの）：A0/PrismaticSite の `essentiallySmall`:73・`PrismOverSmall`:87・`PrismaticSite`:93・小さい模型の `flatTopology`:106・`structurePresheafDerived`:171・`prismaticCohomology`:179・`hodgeTateCohomology`:190・`prismaticCohomologyFrobenius`:200・切り落としの包含 :209〜:225、`PerfectPrismaticSite`:159。A0/FlatDescent の ∞ の層条件 :187〜:222。A0/CechAlexander の `cechAlexander_isLimitCone_iff`:212・`prismaticCohomology_eq_cechAlexanderTot`:221・`prismaticCohomology_cutoff_invariant`:234・`cechAlexanderAffine_computes`:277。A0/BaseChange の :73・:103・:128。A1 の Cor 4.12・Prop 6.2・Thm 6.3 の型。Sheaves/ の S1〜S8。
- **site の大きさ**：本体の site は大きい `(PrismOver P R κ)ᵒᵖ` で、本体の他所は `[EssentiallySmall (PrismOver …)]` を仮定として取る（`CechAlexanderSmall:30`、`AffineCechSiteNerve:44`）。小さい模型と `essentiallySmall` は drafts だけ。結晶 site では本体が小さい版を証明している（`CrystallineSiteSmall:92`）。prismatic site にも同じ証明を入れれば、仮定が外せる（推測）。

### R4-2 site の位相の定義は原典どおりなので、設計書 D22 を直す【推奨：保守で設計書を直す。コードはそのまま】

- 本体の `flatTopology`（`FlatSiteSheaf.lean:40–50`）は `flatCoverage … .toGrothendieck` で、被覆族の引き戻しの公理を `exists_isPushout_isFaithfullyFlat`（Cor 3.12 の押し出し）で示している。原典の順（Cor 3.12 で site であることを示してから位相）と同じ。
- a0-design の D22（:227）と §2.2（:71）は「生成される最小の位相として定義し、site の公理を定義の段階で証明しなくてよい」としている。本体は D22 と違い、原典に近い。D22 を「取り下げ、原典どおり」と書き直すのがよい。
- drafts/A0/PrismaticSite の小さい模型の `flatTopology`:106 は sInf で定義した別物。5∞-2 で本体の版に置き換える。

### R4-3 設計書・地図の古い記述【推奨：調整役が設計書を直す】

- `design-status.md:124–126` は A0-3b（Lemma 3.7(2)(3)）を「未」、A0-3d（Cor 3.12）を「flatTopology_refine のみ」、A0-4 を「未」としているが、BS-W15 K4 で本体に入った（`CompleteFlatDiscrete:39`、`FlatTopologyPushout:43`、`FlatCechSheaf:49`、`FlatCechDescent:179`）。A0-4 も Tor 振幅だけは本体にある（`HomologicalAlgebra/CochainCompleteTorAmplitude:37`）。
- `a0-design.md` §1 の表（:32–34）と §2.6 は、Lemma 3.7(2)(3) と Cor 3.12 を drafts の宣言として挙げる。今の正本は本体。
- `a1-design.md` §1（:51）は Lemma 4.10 を「定理（Prop 6.2 の系）」とする。本体の `bockstein_sq_zero` は Prop 6.2 を経由しない直接の証明（p=2 では δ による余境界、奇素数では cup 積の次数付き可換性と 2 が単元であること）。D 番号のない原典との差として記録するか、a1-design を直す（ノートでは命題 4.2.2 の証明の囲みに両方の筋を書いた）。
- `PrismOver.lean:59` の docstring が `flatTopology_refine` を引くが、本体にその宣言はない（drafts だけ）。

### R4-4 Lemma 4.8 のファイルの名前空間・見出し・仮定・置き場所【推奨：B3（名前空間・見出し・置き場所）、保守（仮定）】

- `Prism/PerfectPrismHomLift.lean` は名前空間 `SerrePositivity.BhattScholze.Andre`（:61・:158・:235・:643）と `SerrePositivity.BhattScholze`（:388・:453・:518）が混ざる（§3 の R3-4 と同じ件）。節の見出しに「André A1-a」「旧 Andre/Remark715/…」「旧 Prism/Perfectoid/…」が 7 か所（:37・:135・:212・:380・:448・:510・:617）。
- 有界性の仮定 `hB` を `IsBoundedPrism` を使わずに書く（:712・:749）。R3-1 で `IsBoundedPrism` を Prism/ へ下ろせば置き換えられる。
- 置き場所：Lemma 4.8 は §4 の項目だが Prism/ の直下。推奨は `Prism/Perfectoid/` に置き、Thm 3.10 の充満忠実性と一緒にすること（Prismatic を import せず、使う側は §3・§7・A5）。
- 存在の本体 `exists_perfectPrismRingHomLift_nonunit`（:658）は private。δ 射であることの判定 `perfectSource_ringHom_isDeltaHom` は標的が p 進分離なだけで効き、有界性は要らない（原典の \(B^{\mathrm{perf}}\) の論法とは別の経路）。

### R4-5 二重の構成

- (a) `hodgeTate_iso_polynomial_Zp`（`HodgeTateCartierAssembly:212`）は `hodgeTate_of_deRham_cartier`（:180）を返すだけの別名で、docstring は Cor 5.5。B3 の案（:159）の「主題の側に一つだけ置き、5.5 も引く」に合わせて一つにする（保守）。
- (b) Čech–Alexander の模型が三つと比較：HasEnvelopes から組むもの（`CechAlexanderAssembly:61` ほか、Constr 4.17–4.18 の一般の選択）、大きい模型 BigCech*（`BigCechAlexander:45`、Constr 4.18 の関手的な選択）、affine の小さい模型 AffineCech*・AffineEnvelope*（Rem 4.19）、比較 `CechAlexanderBigComparison`・`AffineCechChosenComparison`。原典の三つの構成に対応するので文字どおりの重複ではない。drafts/A0/CechAlexander の版は R4-1 で本体に置き換える。
- (c) `isCoproduct` の同名（PrismaticFrameCoproduct:56 と CechAlexanderCoproduct:49）は台帳の BR39。変化なし。
- (d) 有限完全 Tor 振幅の定義が三つ：drafts/A0/BaseChange:60（任意の \(C\to C'\)）、drafts/A1/HodgeTateComparison:210（源を \(A\) に固定、中身は同じ。docstring に「A0 の版に一本化し、この定義は消す」）、本体の鎖複体版 `HasCochainCompleteTorAmplitude`（`HomologicalAlgebra/CochainCompleteTorAmplitude:37`、半自由模型の上）。本体の `crystallineCoverMap_torAmplitude`（c = 3）は鎖複体版を使う。鎖複体版と ∞ 版の同値はどこにもない（推測：Lemma 4.22 の前に要る）。台帳の BR40 にある。

### R4-6 置き場所（B3 の案への追加）

- §4 でないものが §4 の場所にある：Construction61Detection・Reflection（§6）、FiniteEnvelope* 3 本（§7、B3 の案にある）、RelativeCompleteRegularity（§2、B3 の案にある）。
- Cor 5.5 の `hodgeTate_iso_polynomial_Zp` は §5 の主張なので、R4-5 (a) と一緒に §5 の側へ。

### R4-7 docstring【推奨：B3 の docstring の回】

- `PrismOver.lean:48` の見出し「濃度の切り落とし（ノート D16）」（ノートを引く 22 か所の一覧に既出）、:51 の「a0-design §2.7」、:58 の「W9-I-11」（工程ラベル）。`CechAlexanderComplex` の module docstring の「G10 の後」（工程ラベル）。
- 件数の全数は §4 の追記（下）。

## 2. 台帳の項目の今の状態（§4 に関わるもの）

- **BR29**：変化なし。Rem 4.6 の圏同値は drafts の `perfectSiteEquivPerfectoidUnder`（A5/PerfectSite:267、sorry）。
- **BR39**：変化なし。
- **BR40**：R4-5 (d) の三つの Tor 振幅と `bockstein_sq_zero'`。本体の `bockstein_sq_zero` は一般の有界基底で証明済みなので、drafts の版は消すだけで済む（推測：型はノートの加筆で同じ `BetaSquareZero` と確認）。R4-1 の表を BR40 に足すとよい。
- **BR41**：Delta → `Prismatic.CrystallineTensorRegularity` の逆向きの import は §5 の側。
- 台帳にない新しい事実は R4-1〜R4-4。

## 3. B. 形式化の計画の提案（新しく形式化する項目）

前提（確認済み）：Mathlib に形式スキーム（Spf、FormalScheme）はない。スキームの小さいエタール site は Mathlib にある（`AlgebraicGeometry/Sites/Etale`・`AffineEtale`）。Lemma 2.18 のエタール部分（I 完全エタール射の δ 持ち上げ）は本体にない。

| 項目 | 今あるもの・要るもの | 規模 | 依存 | 推奨 |
| --- | --- | --- | --- | --- |
| Def 4.1 affine 版 | 本体は `PrismOver`（PrismOver.lean:68、κ つき・向き付き・\(R\) は任意の \(A/d\) 代数）、`flatTopology`、構造環とその剰余の環値の層。\(R\) の p 完備性は要求していない（原典の X は p 進形式スキーム） | 済 | — | 済。p 完備の仮定を足すかは任意 |
| Def 4.1 形式スキーム版 | p 進形式スキーム（Mathlib にない）、または affine の site の Zariski 局所な貼り合わせ。\(h_X\) を前層として \((*/A)_\Delta\) のスライスで書くのが一番軽い（Rem 4.3 の形） | 大 | 形式スキーム、Rem 4.3 | 入れない（E3 は affine だけで足りる） |
| prismatic site の本質的小ささ | 結晶 site の `CrystallineSiteSmall:92` と同じ証明 | 小 | — | **入れる**（本体の `[EssentiallySmall …]` の仮定が外れ、5∞-2 の小さい模型の土台になる） |
| Rem 4.3 slice 表示 | 全有界 prism の site（§3 の Cor 3.12 の絶対版、後回し）、\(h_X\) が層 | 中 | Cor 3.12 の絶対版 | 入れない |
| Construction 4.4 \(\nu_*\) | Lemma 2.18 のエタール部分、\(R\) のエタール site（affine なら `Algebra.Etale`）、層の押し出し。\(\nu_*F(U)=H^0((U/A)_\Delta,F)\) は 1 圏で書ける | 中〜大 | 2.18 | 入れない（a0-design §1 のとおり） |
| Rem 4.5 | 一般論の部分は drafts/Sheaves/GlobalSections の `derivedGlobalSections_of_le`:206（sorry）。原典の位相の比較は Rem 4.3 と \(\nu\) が要る | — | S2 | 一般論は 5∞-1 で。比較そのものは入れない |
| Rem 4.6 定義 | `PrismOver` の \(B\) が完全なものの充満部分圏（`ObjectProperty.FullSubcategory`）、誘導位相 | 小 | — | **入れる**（5∞-6 の A5 の前提。drafts/A0:159・A5/PerfectSite:65 を本体へ） |
| Rem 4.6 perfectoid との同値 | Thm 3.10 の圏同値の絶対版（§3 の B で「入れる」）と Lemma 4.8 の under 版への制限。**基底が完全な場合に限る**（ノートの加筆での見立て：基底が完全でないと完全 prism への射は mod I の射で決まらない） | 小〜中 | §3 の Thm 3.10 | 入れる（BR29、G-A5-4）。主張は基底が完全な場合で述べる |
| Rem 4.7 絶対 site | 一般の（向き付けのない）prism と Spf | 大 | 一般の prism（§3 の D5） | 入れない |
| Lemma 4.8 一般の標的 | 本体は標的が有界な向き付き prism（:749）。有界性は商の古典的 p 進完備性にだけ使う。一般の標的には (i) 導来完備だが分離的でない \(B\) での Witt・tilt の持ち上げ、または原典の変形理論（\(L_{A/\mathbb Z_p}\) の消滅）、(ii) 向き付けのない \((B,J)\) が要る | 中＋大 | 一般の prism | 入れない（site の対象は有界、D19） |
| Construction 4.9 一般の \(R\) | 本体は p 完備多項式 r 変数を Čech–Alexander 模型の上で（`hodgeTateMap`、HodgeTateCompletedMap:398、任意の有界向き付き基底、D27）。一般の \(R\) には site の RΓ、CAlg 値の RΓ と環構造（G-A1-11・G12）、\(\nu\)、smooth な \(R\) の \(\Omega^*\) | 大 | 5∞-2、G12、4.4 | 入れない（A2 は多項式代数からの Kan 延長） |
| Construction 4.9 site の \(H^*(\bar{\mathcal O})\) との一致 | 模型が Δ を計算すること（5∞-2）と CAlg 値の比較（D27、A2） | — | 5∞-2・5∞-4 | 計画済み |
| Lemma 4.10 | 本体で済（任意の有界向き付き基底の多項式代数、原典と違う直接の証明、R4-3） | 済 | — | 地図は 11-12 夜に直した |
| Thm 4.11（D68 の結晶基底以外） | 型は一般の基底で述べてある。証明は \((\mathbb Z_p,(p))\) だけ（:212）。一般の有界向き付き基底の多項式は drafts/A1 の Prop 6.2・Thm 6.3（`hodgeTate_iso`:350 ほか、sorry）。要るもの：Construction 6.1（本体の Prism/Basic にほぼある）、Lemma 4.20、導来 Nakayama（G-A1-4）、保存性 | 大 | 5∞-2（Lemma 4.20）、3b-2・3b-4 | **入れる（5∞-3、計画済み）**。「\(\bar\Delta\) は完全複体で \(H^i=\Omega^i\)」の前半は型にないので、5∞-3 で足すか決める |
| Thm 4.11 smooth な一般の \(R\) | Lemma 4.21、形式スキーム | 大 | 4.21 | 入れない |
| Cor 4.12 | drafts の `prismaticCohomology_baseChange'`（A1/HodgeTateComparison:365）と `PrismaticCohomologyBaseChangeStatement`（A1/HodgeTateMap:87、CAlg 値の Δ について）。導来 Nakayama と Thm 4.11 | 中 | 5∞-3 | 入れる（5∞-3、A2 の Construction 7.6(4) で使う） |
| Rem 4.13 Higgs | p ねじれなしの \(A\)、Frobenius の持ち上げ、E∞ 写像 | 中〜大 | site の RΓ、E∞ | 入れない |
| Rem 4.14・Prop 4.15 | 余接複体の基盤（Mathlib の余接複体は低次だけ、推測）。原典の証明も ALB19b に任せる | 大 | 余接複体、4.11・4.12 | 入れない |
| Notation 4.16 \(\Delta_{R/A}=R\Gamma\) | drafts の `prismaticCohomology`（A0/PrismaticSite:179）、`hodgeTateCohomology`:190、Frobenius:200。要るもの：S1（層条件）・S2（RΓ の型）・S4（層化）・S6（κ）・S7（G3）、本体の `flatTopology` と構造前層の D(A) 値（埋め込み J）。κ 不変性は HasEnvelopes を仮定（CechAlexander:234） | 中（S が済めば数百行） | 5∞-1 | **入れる（5∞-2、計画済み）** |
| Construction 4.17 | 本体で済（`cechAlexanderObj`、`cechSmall_weaklyTerminal`、余積） | 済 | — | — |
| Construction 4.18「C^• が Δ を計算」 | 本体は対象・余積・弱始性・交代余面複体まで。残りは脚注 10（S3）と G9・G10、Cor 3.12 の導来降下（本体の `FlatCechDescent` は 1 圏の層条件） | 中 | 5∞-1、3b-2 | **入れる（5∞-2）** |
| Construction 4.18 の \(\bar{\mathcal O}\) 版 | \(C^\bullet/dC^\bullet\) が \(\bar{\mathcal O}\) を計算すること（\(A/d\) は完全複体なので ⊗ と RΓ が交換） | 小〜中 | 同上 | 5∞-2 で一緒に |
| Rem 4.19 | 項ごとの底変換は本体で済（`cechAlexanderAffine_baseChange`、AffineCechPrismBaseChange:49、項ごとの導来底変換 AffineEnvelopeDerivedBaseChange:56・99）。Tot の底変換と「Δ を計算」は G10 の後 | 小 | 5∞-2 | 5∞-2 で |
| Lemma 4.20 | drafts/A0/BaseChange:103・128（多項式代数、比較の射を指定しない形、design-status:76）。要るもの：Lemma 4.22、Rem 4.19、本体の Tor 振幅（D4-04） | 中 | 4.22、5∞-2 | **入れる（5∞-2 か 5∞-3）**。比較の射を指定した形にするかは Prop 6.2 (b) の使い方で 5∞-3 の前に決める |
| Lemma 4.21 étale 局所化 | Lemma 2.18 のエタール部分と左随伴 F | 中〜大 | 2.18 | 入れない（D24） |
| Lemma 4.22 | drafts/A0/BaseChange:73（一般形、sorry）。本体には鎖複体版の振幅の定義と Construction 6.1 の c = 3（`CrystallineCoverCompleteTor:43`）。要るもの：D(A) の骨格による Tot の近似、完備底変換の ∞ 関手（drafts/DerivedGeneral、本体にない）、Koszul による振幅の評価 | 中（1〜2 千行） | 3b-2、DerivedGeneral | **入れる（5∞-2）**。定義は一つにする（R4-5 (d)、BR40） |

## 4. まとめ（推奨の順）

1. B3 の範囲で：R4-1 の方針（drafts/A0・A1 の古典的な部分を本体の宣言に置き換える）、R4-4（名前空間・見出し・置き場所）、R4-6、R4-7。5∞-2 が古い drafts の上に積まれないように。
2. 保守で：R4-2・R4-3（設計書の D22・design-status・a0/a1-design の更新）、R4-5 (a)。
3. 小さい補完（⑤∞ の前に入れておくと 5∞-2・5∞-6 が軽くなる）：prismatic site の本質的小ささ、Rem 4.6 の定義。
4. 計画済み（⑤∞）：Notation 4.16、Construction 4.18 の「Δ を計算」と \(\bar{\mathcal O}\) 版、Rem 4.19 の Tot、Lemma 4.20・4.22（5∞-2）、Thm 4.11 の一般の基底と Cor 4.12（5∞-3）、Rem 4.6 の同値（G-A5-4）。
5. 入れない：Rem 4.2〜4.4・4.7・4.13〜4.15、Lemma 4.21、形式スキーム版、Lemma 4.8 の一般の標的。理由は形式スキーム・余接複体・Lemma 2.18 のエタール部分・一般の prism という大きな基盤がないためで、E3 にも要らない。

## 5. ノートの側（参考）

1. ノート 04 章：§4 の全 22 項目を、見出しと主張・Lean・証明の囲みにした（番号は小節ごとの 4.k.n）。章末の項目の表と D 表は外し、D16〜D18 の評価を Def 4.1・Notation 4.16 の下に移した。冒頭の「方針（10-25・11-02・11-03）」の囲みは設計の決定の記録なので外し、a0-design への参照にした。
2. **読み方の見立て（ノートでは補った筋として扱った）**：Rem 4.6 の「完全 prismatic site は perfectoid 環の site と同値」は、基底が完全な場合（§8 で使う場合）の主張として読んだ。基底が完全でないと、完全 prism への射は mod I の射で決まらない（Lemma 4.8 の後の「双対は成り立たない」）。Notation 4.16 の「\(A=R/I\)」は \(R=A/I\) の誤植と判断した。
3. 地図 items.csv：1.7・4.6・4.10・4.11・4.17・4.18・4.19・4.20・4.22 を直した。

## 6. 追記：件数の調べ（主定理の閉包・未使用・工程ラベル）

対象は Prismatic/ の §4 にあたる 70 本（Crystalline*・PD* を除く）と `Prism/PerfectPrismHomLift.lean`。作業用のスクリプトはノートのチャットの作業用の場所にあり、数は確認済み。

- **主定理の閉包**（`Paper.Statement` から 1,841 モジュール、うち SerrePositivity 配下 1,142）：§4 の対象で入るのは `Prism/PerfectPrismHomLift` だけ。**Prismatic/ の 70 本はすべて閉包の外**（閉包に入る BS は Almost・Andre・Delta・Perfectoid*・Prism・Semiperfectoid だけ）。
- **葉**（集約と `scripts/audit_bhatt_scholze_stage2.lean` だけが import）：AffineCechChosenComparison、AffineCechCoefficientComplex、AffineCechSiteNerve、BigCechDerivedBaseChange、BigCechSiteAffine、CechAlexanderEnvelopeMaps、FlatCechDescent の 7 本。HodgeTateCartierAssembly は集約・監査のほかに drafts/A1 からしか import されない。
- **未使用の宣言**（公開 304 件を、名前の最後の成分で本体・drafts・scripts と照合）：どこからも参照されない 69 件（うち 24 件は自分のファイルの中でも使われない）、監査だけ 2 件（`wittQuotientHom_ext`:415・`existsUnique_wittQuotientHomLift`:459、PerfectPrismHomLift）。多いのは PerfectPrismHomLift 9/14、AffineCechChosenComparison 5/5、FlatCechComparison 5/13、HodgeTateCompletedMap 5/9（`completedHodgeTate`:237 ほか）、BigCechDerivedBaseChange 4/4、CechAlexanderBigComparison 4/5、FlatCechDescent 4/4（`structureRing_isSheaf`:179・`quotientStructureRing_isSheaf`:184。Cor 3.12 の層条件そのもの）。本体からは参照がなく drafts からだけ参照される宣言が 15 件（`cechAlexanderAffine_baseChange`、`cechKernel`、`BetaSquareZero`、`HTAlgebraMap`、`hodgeTate_iso_polynomial_Zp` など）。ありふれた名前（`map`・`Hom` など 17 件）は無関係な同名に当たるので、実際の未使用は 69 件より多いかもしれない。
- **推奨（R2-8・R3-7 と同じ）**：§4 の Prismatic/ はまるごと 5∞-2 の土台で、今は主定理から届かないのが当然なので、未使用でも消さない。原典の項目にあたる宣言（層条件、Čech–Alexander の比較など）は残す。消す候補は名前空間のずれた PerfectPrismHomLift の補助の補題（9 件）だけ。
- **docstring の工程ラベル**：11 件・7 ファイル（PrismOver 4：「（ノート D16）」:48・「a0-design §2.7」:51・「W9-I-11」:56 ほか、BigCechSiteAffine 2（D21）、CechAlexanderBounds 1（D16）、CechAlexanderComplex 1（「G10 の後」:17）、CechAlexanderEnvelopeData 1（D21）、AffineEnvelopeBaseChange 1（「K4 の自由 δ 環の底変換」）、PerfectPrismHomLift 1（「F4のWitt復元」:512））。「（旧 …）」は 7 件で全部 PerfectPrismHomLift（:37・:135・:212・:380・:448・:510・:617）、「Andre A1-a」が 4 件。drafts を指す docstring が 2 件（CechAlexanderEnvelopeData:87、AffineCechPrismBaseChange:48）。コードの名前に工程番号：HodgeTateCompletedMap:297・:300 の `local instance d68TargetBaseModule`・`d68TargetTower`。
- **drafts と本体の型の照合**：drafts の `bockstein_sq_zero'` と本体の `bockstein_sq_zero` は型が同じ（`BetaSquareZero P hP r`）で、drafts 側は sorry を含む写し。drafts の小さい模型の `flatTopology`（sInf）と本体の大きい圏の `flatTopology`（coverage から）は同名だが型が違い、圏の同値に沿って同じ位相を与えるかは未確認。
