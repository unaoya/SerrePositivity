# ∞ 圏の勉強ノートの赤い囲み（リファクタ候補）の原文

`exposition/ja/infinity/*.html` の `<div class="box refactor">` の中身を ba24dceb6 時点で写したもの（HTML の印を Markdown に直しただけで、文は変えていない）。見出しの「ファイル:行」は囲みの開始行。囲みの外（本文・表・調査ページ r8-duplication.html など）にある R の記述は写していない。一覧は `README.md`。

### 00-map.html:150

R1　ディレクトリ名と層の不一致

F1・F1B・F2 はレーン名で、F1 と F1B は互いに 64 回・119 回 import し合っている。数学的な主題（例：`Fibrations/`、`Straightening/`、`KanExtension/`、`Presentable/`）で分け直す案がある。ただしファイル数が数千あり、並行作業との衝突が大きいので、レーンが止まっている部分から段階的に行うのが現実的。

### 00-map.html:154

R2　基本定義の置き場所

`IsColimitCone` が Stable/Cocone に、`IsCocartesianEdge` が F1/CartesianEdge にある。`IsLimitCone`（Core/Limit）や Core の Cocartesian* と並べるべきもの。Core → Stable の依存を生む原因になりやすい。

### 00-map.html:158

R3　基盤から応用への依存

HomotopyLimits は KST.Spectra を 25 回 import している。BF スペクトルの模型など、本当は基盤に属する部分が KST に置かれている可能性が高い。

### 00-map.html:162

R4　細かすぎるファイル分割

平均 70 行で、入口ファイルの import 列が目次の役目を果たしていない。章ごとに「公開する主定理」と「途中の補題」を分け、途中の補題をまとめる余地がある。

### 01-quasicategories.html:261

R5　左右の双対を二度証明している

終対象と始対象の一意性（TerminalUniqueness 249 行、InitialUniqueness 230 行）、slice と coslice への持ち上げ（JoinLifting の前半と後半）、RelativeOuterHorn と RelativeOuterHornOp（各 202 行）などが、反対圏を使わずに左右それぞれ直接証明されている。`InitialUniqueness` の docstring にも「左右双対を直接構成する」とある。一方で、slice と反対圏の同型 `sliceOverOpIso` は Stable/SliceOpposite にあり、F1・F1B・Stable から使われている。この同型を Core に移し、片側を他方から導く形にすれば、Core の重複をかなり減らせる見込み。

### 01-quasicategories.html:265

R6　Core の中にある F1 の素材

Core/Cocartesian*（14 ファイル）を import しているのは F1 のファイルだけである。cocartesian fibration の層（第 3 章）に移すほうが層の境界がはっきりする。第 3 章を読んでから判断する。

### 01-quasicategories.html:269

R7　anodyne・fibration の定義の置き場所

右・左 anodyne の定義が JoinCells（join のホーン計算のファイル）に、trivial Kan fibration の定義が Terminal にある。§1 の表の概念は一つのファイル（たとえば `Core/Fibrations.lean`）にまとめ、そのファイルが入口になる形が読みやすい。

### 02-mapping-limits.html:204

R8　F1 と F1B の間でファイルが丸ごと複製されている（重要）

左右の写像空間の比較を追っていたところ、`F1/MappingSpaceIntervalComparison.lean` と `F1B/KanSectionMappingSpaceIntervalComparison.lean` が、名前空間（`KanSection`）と import の違いを除いて同一であることに気づいた。全体を機械的に調べると、正規化した本文が完全に一致する組が **17 組**（重複分 1,678 行）あり、すべて F1 と F1B の組だった（F1B 側は `KanSection*` という名前）。レーンを分けたときに複製したものと思われる。改名を伴うほぼ同一のものを含めると、さらに多い可能性がある。F1B 側を消して F1 側を参照させるのが、最も安全で効果がはっきりしたリファクタである。第 3〜4 章で F1・F1B を読むときに、全体を詳しく調べる。

### 02-mapping-limits.html:208

R9　写像空間の基本結果の置き場所

PinchedHom/ には定義と頂点の記述しかなく、Kan 性と \(\pi_0\) は Core/MappingSpace* に、左右の比較は F1/MappingSpaceModelEquivalence にある。写像空間に関する基本的な結果は一か所（たとえば `MappingSpace/`）にまとめたい。第 0 章で見た「Core → PinchedHom」という逆向きの依存も、これで解消する。

### 02-mapping-limits.html:212

R10　ホモトピー同値の三つの言い方

Kan 複体の間では `IsSimplicialHomotopyEquivalence` と `IsQCatEquivalence` が同値で、一般の射には `IsPrecompositionEquivalence` がある。今のところ使い分けは妥当だが、それぞれの補題（合成、二対三、二対六）が別々に証明されている（EquivalenceCalculus、FullyFaithfulCalculus、PrecompositionEquivalence）。片方から他方へ移す補題を整え、計算規則を一方にまとめる余地がある。優先度は低い。

### 03-straightening.html:168

R6（確定）　fibration の基本を一か所に

cocartesian 辺の定義は F1/CartesianEdge、fibration の定義は F1/CartesianFibration、外側ホーンの相対版の補題は Core/Cocartesian*（14 ファイル）と Core/RelativeOuterHorn* に分かれている。これらは一つの層（たとえば `Fibrations/`）にまとめるのが自然である。第 1 章の R7（anodyne・fibration の定義の置き場所）と一緒に行える。

### 03-straightening.html:172

R11　休止中の Cat∞ 値 straightening を分ける

F1/Cocartesian*（3.7 万行）は主経路に使われていないが、F1 の集約ファイルからビルドされている。`F1/Cocartesian/` のようなサブディレクトリに移し、集約からも外して独立の入口にすれば、F1 の主経路が読みやすくなり、ビルドも軽くなる。休止中の L2・L6 を Auxiliary として凍結した前例と同じ扱いになる。

### 03-straightening.html:176

R12　F1 の平らなディレクトリ

F1 は 2,314 ファイルが一つのディレクトリに並んでいる。§6 の表の役割ごとに、`Transport/`、`StraighteningLeft/`、`Coherent/`、`Weighted/` などのサブディレクトリに分けると、§4 の主経路がディレクトリ構造から読み取れるようになる。R8（F1/F1B の複製の解消）を先に行ってから取りかかるのがよい。

### 04-yoneda-adjunction-kan.html:174

R13　接頭辞 `Kan` の二重の意味

F1B では、556 ファイルの名前が `Kan` で始まる。しかしこれは「Kan 拡張」（KanLeft*、KanRight*、KanGlobal*）、「Kan 複体・Kan fibration」（KanFiber*、KanEquivalence*）、「レーン内の作業名」（KanSection*、KanScaffold*、KanCocartesian*）が混ざったものである。宣言名にも `kanNonempty_adjunction_iff_nerveAdjunction` のように、Kan 拡張と無関係なのに `kan` が付いたものがある。少なくともディレクトリは `KanExtension/`、`NerveComparison/` などに分け、宣言名の `kan` 接頭辞は意味のあるものだけに残したい。

### 04-yoneda-adjunction-kan.html:178

R14　随伴の基本補題の置き場所

`QCatAdjunction.toHoAdjunction`（ホモトピー圏への随伴）が Stable/AdjunctionHomotopyCategory にある。随伴の定義（F1B/Adjunction）の直後に置くべき基本的な結果である。R2（`IsColimitCone` が Stable にある）と同じ型の問題。

### 04-yoneda-adjunction-kan.html:182

R15　密度定理の置き場所

「任意の前層は表現可能前層の余極限」（`presheafElementsColimitCocone_isColimit`）が F2/Ind/ElementsDiagram にある。Ind とは独立した前層の基本定理なので、F1 の前層・Yoneda の層に置くのが自然。

### 05-gamma-bridges.html:111

R16　HomotopyLimits に presentable の素材が入っている

局所対象・S-同値・強飽和性（Local*、N-4 a〜e）と、PΣ・sifted 余極限（Sigma*、Sifted*、N-4 g）が HomotopyLimits/ に置かれている。担当レーン（N）の作業場所がそのままディレクトリになったためで、内容は HTT §5.5 の presentable の理論（第 6 章、F2/Presentable の範囲）に属する。γ 層（古典との橋）から切り離して、`Presentable/` または `Localization/` に移すのが自然である。

### 05-gamma-bridges.html:115

R17　条件付きの API が無条件の定理に追い越されている

F2/SpaceLimitShapes の `HasSpaceLimitsOfShape K`（「形 \(K\) の空間値図式はすべて極限を持つ」という仮定）と、それを仮定にとる `presheafInfinity_hasLimit_of_spaceLimitsOfShape` などが残っている。しかし現在は `hasLimit_coherentSpaceDiagram` によって、任意の小さい形について無条件に成り立つ。この仮定を一般の定理から導き、条件付きの版を削除するか単なる系にするのがよい（3 ファイルが使用）。並行作業で、先に条件付きの版を作り、後から無条件の版が別の場所で完成したことの名残と思われる。

### 05-gamma-bridges.html:119

R18　入口と命名

- `HomotopyLimits.lean` はモジュールの docstring がなく、1,147 個の import を並べているだけである。γ3・γ4 の主定理を示す入口が監査スクリプト（5,477 個の `#check`）しかない。

- `quillenCfBottomEndpoint_wrong` は「ある対象が端点 0 の対象ではない」という否定の命題だが、名前からは内容が読めない（たとえば `not_quillenCfEndpointObjects_zero_inr`）。

- `kanDiagramCoherentNerve`（strict な図式を coherent な図式に変える γ の基本構成）が F1/ にある。

### 06-catinfty-ind-presentable.html:141

R19　F2 最上位の分割

F2 最上位の 2,194 ファイルには、完成した Cat∞ の極限・lax pullback（数百ファイル）と、作業中の交換定理（Coherent* 約 650 ファイル）が同じディレクトリに並んでいる。`F2/CatInfinity/`（完成）と `F2/FilteredExchange/`（作業中）に分けるだけでも、どこまでが確定した API なのかがディレクトリから分かるようになる。

### 06-catinfty-ind-presentable.html:145

R20　仮定として渡している定理の一覧化

交換定理が未完成なので、`CoherentFilteredLimitExchangeShape K` や `IndFiniteLimitExchangeInput` を仮定にとる定理がある。仮定は明示されているので健全だが、a7 が完成したときに外すべき箇所がまとまっていない。R17（`HasSpaceLimitsOfShape`）も同じ型で、無条件の定理が完成した後も条件付きの版が残っている。「未証明の定理を仮定として受け取る構造体・述語」を一覧にし、完成したら機械的に外せるようにしておきたい。

### 06-catinfty-ind-presentable.html:149

R21　docstring の書式

README の規約（概要／方針／規約／使われ方）に従っている docstring の割合は、Core と F1B では 100% だが、F2 全体では約 27%、F2/Ind では 0% である。F2/Ind の docstring 1,630 個のうち 1,547 個は「元の」「実際の」「同じ」を含む一行の文で、「代用品ではなく元の対象について示した」ことを強調する作業時の言い回しになっている。HomotopyLimits（約 31%）、F1（約 49%）も同じ傾向がある。読み手にとっては、この強調よりも、命題を言葉で書き、証明の考え方を添えることのほうが役に立つ。

### 07-stable.html:113

R22　Stable/ にある一般論を下の層へ

Stable/ には、安定性と無関係な一般論がかなり含まれている。

- 余極限の定義 `IsColimitCone`（Stable/Cocone、R2）

- slice と反対圏の同型 `sliceOverOpIso`（Stable/SliceOpposite、R5）

- 随伴のホモトピー圏への降下 `toHoAdjunction`（Stable/AdjunctionHomotopyCategory、R14）

- 宇宙の持ち上げと極限 `hasLimit_iff_ulift`・`hasColimit_iff_ulift`（Stable/UniverseLimits）、図式の同型と極限の存在（Stable/ColimitDiagramIso）、有限極限・余極限のクラス `HasFiniteLimits`（Stable/Definition）

D レーンが安定性を作る途中で必要になった一般論を、自分のディレクトリに置いたものと思われる。極限・余極限の一般論は Core（第 2 章）に、随伴は F1B（第 4 章）に移すのが自然。

### 07-stable.html:124

R3（再確認）　Stable から KST への依存

Stable/PosetTerminalExtension が `KST.SConstruction.VertexPrescribedExtension` を、Stable/UniversalConeChoiceProjection が `KST.LocalizingInvariants.LimitProjectionExistence` を import している。基盤が応用を参照する逆向きの依存で、R8 で見た Stable ↔ KST の複製（4 組、約 470 行）と同じ根を持つ。共通部分を Stable 側（または Core）に置き、KST から参照する形に直したい。

### 08-dgnerve-derived.html:125

R23　Derived/ にある ∞ 圏の一般論

Derived/ にも、dg と無関係な一般論が置かれている。

- 局所化の判定：`IsLocalization.precomposition_isFullyFaithful`、`isLocalization_of_fullyFaithful_extensions`、`isLocalization_of_rightKan_local_limits`、変形による判定（Derived/LocalizationPrecompositionCriterion、LocalizationRightKanCriterion、DeformationLocalization）。局所化の定義は F1B/Localization にある（第 4 章）。

- 極限の存在の移送：`hasLimit_iff_of_functorIso`（Derived/LimitDiagramIso）、`hasLimit_of_leftCofinal`（Derived/CofinalLimitExistence）。**双対の `hasColimit_iff_of_functorIso` は Stable/ColimitDiagramIso にあり**、一組の双対な補題が二つのディレクトリに分かれている。

R22（Stable/ の一般論）と同じ型で、まとめて Core（極限）と F1B（局所化）に移すのが自然。

### 08-dgnerve-derived.html:134

R24　DGNerve と Derived の循環

DGNerve/SemifreeLimits が Derived/SemifreeClosure・SemifreeSubcategory を import していて、ディレクトリ単位で DGNerve ↔ Derived が循環している（第 0 章の行列）。semifree 複体についての結果は Derived 側（あるいは DifferentialGraded 側）に置くべきもの。

### 08-dgnerve-derived.html:138

R25　README の位置と範囲

`InfinityCategories/README.md` は、題が「dg nerve の規約と計算」で、中身も dg nerve の符号の規約と N0〜N6 の記録である。∞ 圏の層全体の README の位置にあるのに、内容は DGNerve/ のもの。DGNerve/README.md に移し、最上位の README は第 0 章のような全体地図（層、入口ファイル、監査スクリプト）にするのがよい。一方で符号の規約そのものは非常に有用で、この章の囲みはそこから要約した。

### 08-dgnerve-derived.html:142

R8（関連）　Derived 内の準重複

重複調査では、Derived/DGCommaAug*（53 ファイル）と DGModuleAugmentation*（76 ファイル）の間に、類似度が最大 0.96 の組が 17 組あった。また、未追跡の `Derived/DGKernelDerivedMapInvertible.lean` は既存のファイルと完全に一致していた（並行セッションの作業中と見られる）。

### f-01-simplicial-kan.html:143

注意：添字のずれ

`KanHomotopyGroup X n` は \(\pi_{n+1}\) である。群の構造を \(n\) について一様に定義するための選択だが、読むときに間違えやすい。本来の添字の版 `KanHomotopy` があるので、新しく書く主張ではこちらを使うのがよい（整備の後の R54 で名前を見直す候補）。

### f-05-verdier-quotient.html:71

注意：この定理は商の存在を仮定している

定理の仮定は `(h : IsVerdierSequence i q)` である。つまり「安定な商 \(C\) が与えられたときに、その写像空間を計算する」定理であって、商を作る定理ではない。
M2（局所化の安定性）の証明にこの機構を使うには、商が安定であることを仮定しない版を先に切り出す必要がある（計画の段 G、M2 の注）。
span の圏と groupoid 完備化の構成そのもの、および「span の像が局所化の写像空間に入る」部分は、どちらも安定性を使わないはずなので、そこを分けるのが最初の作業になる。

### f-06-straightening.html:129

提案する順序

- まず \(\mathcal Z\) を作る（A・B・D の共通部分）。

- 並行して fiberwise 判定 (a) を示す（A に必須、B・D でも役立つ）。

- \(\mathcal Z\) ができた時点で、A で仕上げるか B に切り替えるかを決める。既存コードを活かすなら A、参照の確かさと底の一般性なら B。

- C は \(\mathcal Z\) が予想以上に重かった場合の代替案。

### route-classification.html:449

**R27**（候補）：模型 3（\(\mathrm{Fun}(\Delta^1,\mathcal C)\) の fiber）を写像空間の定義として加え、pinched との同値を示す。今回の検索範囲では両者の比較は見つかっていない（未確認）。Kerodon・Riehl–Verity の定義に揃い、関手圏の写像空間や 1.6 の充満忠実性と同じ言葉で書けるようになる。

### route-yoneda.html:214

R58　Yoneda の閉包に入り込む応用側・無関係な層

旧番号 R26。R2 計画の R26 と衝突したため 2026-10-28 に改番。実施は R2 計画の R27（HL・F1 → KST.Spectra）と R37（Stable の汎用葉を下へ）で扱う。

Yoneda の補題の import の閉包は約 1,750 モジュールで、その中に KST.Spectra（8）、Stable（43）、HomotopicalAlgebra（167）が含まれる。最短の経路は次のとおり。

- KST：YonedaPresheafEvaluation ← RepresentableUnstraighteningEvaluation ← RepresentableUnstraighteningComparison ← LeftStraighteningInfinityReconstruction ← LeftStraighteningEssentialSurjectivity ← SmallUnstraighteningRepresentation ← CoherentRepresentationExtension ← SmallFiberWitnessContractible ← … ← F1/ContractibleKanTower → **KST.Spectra.FibrationTowerLimitCone**（可縮 Kan 複体の塔の極限という一般論が KST にある）

- Stable：YonedaPresheafEvaluation ← RepresentableUnstraighteningEvaluation ← F1/LeftFibrationInitialEvaluation → **Stable.IdentityCocone**（余錐の基本補題が Stable にある。R22）

どちらも、一般論を Core（または HomotopyLimits）へ移せば閉包から外れる。R3・R22 の具体例。

