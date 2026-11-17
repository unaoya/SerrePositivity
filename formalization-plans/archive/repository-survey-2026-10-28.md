# SerrePositivity/ 以下の全体調査（2026-10-28、HEAD cbb891432、読み取りのみ）

概要：ライブラリ全体（39,000 ファイル、約 240 万行）を、ディレクトリごとに次の観点で調べた。
- 規模・最終更新・主定理との関係
- 目的と主な宣言
- 状態（完成・作業中・休止・凍結・旧経路）
- 依存の向き

方法：機械集計（ファイル数・行数・宣言数・本文の sorry・import 行列・git の更新日）と、範囲を 4 つに分けたエージェントの読解による。
状態の根拠は各 README・formalization-plans の計画・docstring。数値は集計時点の概数。
使われ方：リファクタ（[refactoring-infinity.md](stage-i/refactoring-infinity.md) §0）と、第 II 段の計画を立てるときの地図として使う。

## 1. 主定理と残る穴

- 主定理は `main_statement`（[Paper/Statement.lean](../../SerrePositivity/Paper/Statement.lean)）。正則局所環 R 上の有限生成加群 M・N について、
  長さが有限で dim M + dim N = dim R ならば `0 < chi R M N`。
  - 剰余標数 p の場合は `Section5.positivity_of_residueCharP`（完備化 → 剰余体 → 加群 → 素イデアルの帰着を経て `core_of_complete_algClosed`）。
  - 剰余標数 0 の場合は `IntersectionMultiplicity/EqualCharZeroPositivity.chi_pos_of_residueCharZero`（Serre の対角議論、証明済み）。
- コメントを除いた本文に `sorry` は 4 つある。`axiom` 宣言はない（検索で引っかかったのは docstring の単語だけ）。

| sorry | 何の代わりか | 主定理の閉包 | 解消する計画 |
| --- | --- | --- | --- |
| `theorem_3_1_K0`（Inputs/Descent.lean） | 論文の定理 3.1 から出る (3.2)：有理的な supported K₀ 降下 | 入る（Lemma 3.5 → Lemma 5.2） | KST 経路の段階 1a（H = A）、第 II 段 |
| `supportedRankK0_descent`（Paper/Section4/SupportedDescent.lean） | 補題 4.6 と係数つきの定理 3.1 | 入る（RegularLengthAlgebraPositivity） | KST 経路の段階 1b（F5 で 4.6 を迂回、K-7 の非連結 K） |
| `exists_perfectoidizationInterfaceE3`（BhattScholze/Inputs/PerfectoidizationInterface.lean） | BS の Def 8.2〜Thm 10.11（導来 perfectoidization の E3 インターフェース） | 入る（BS → CLMST → 定理 2.5） | BS セッション（A 案） |
| `kanQuillen_model_exists`（Inputs/Homotopy/KanQuillen.lean） | Hovey Thm 3.6.5（Kan–Quillen モデル構造） | 入らない（ルートも import しない） | γ-B の決定で不要。主経路から外したまま |

- Inputs/ の仕組み：引用する結果を名前つきの定理として `sorry` で置き、使う場所で直接適用する。未証明の仮定を束ねた構造体は禁止。
  残りの Inputs/*.lean は、旧い公開名を保つための証明済みの互換入口。
- README は「主経路の入力は 3 つ」と書いており、上の表と整合する（KanQuillen は主経路の外）。

## 2. 規模と状態の一覧

最終更新は git の最終コミット日。「10-21 以降」は 10-21 以降のコミットで変更されたファイルの延べ数。

| ディレクトリ | ファイル | 行 | 最終更新 | 10-21 以降 | 状態 | 主定理への経路 |
| --- | ---: | ---: | --- | ---: | --- | --- |
| InfinityCategories/F2 | 4,629 | 29.1 万 | 10-26 | 7,697 | Ind・Compact・Idempotent・CatInfinity は完成。Presentable はほぼ完成。FilteredExchange は放棄された作業 | ルートが import しない |
| InfinityCategories/Derived | 4,153 | 27.3 万 | 10-27 | 3,473 | 大半が完成（Gluing 完了 10-27）。ClosureFunctoriality は停止。SuspensionAction は診断 | 主定理は使わない |
| EInfinity | 3,384 | 25.5 万 | 10-26 | 2,110 | E2 は停止（供給は完了）。比較射の一部が未完 | 使わない |
| KST/SConstruction | 3,122 | 23.1 万 | 10-28 | 1,989 | 作業中（LT の S 長方形） | 使わない |
| InfinityCategories/F1 | 2,626 | 19.7 万 | 10-26 | 4,170 | 完成。Cocartesian（Cat∞ 値 straightening）は休止 | 使わない |
| DifferentialGraded | 2,258 | 14.9 万 | 10-27 | 114 | M5 は完成（10-17）。∞ 側への供給は継続 | Module・Complexes など 119 本が入る |
| KST/LocalizingInvariants | 2,021 | 14.4 万 | 10-27 | 2,353 | 抽象 K-5 は完成。s3・s5・CoreFlag は作業中 | 使わない |
| KST/Spectra | 1,622 | 13.4 万 | 10-27 | 245 | Sp の安定性は条件つき。停止準備完了で、供給待ち | 使わない |
| HomotopicalAlgebra | 1,112 | 10.8 万 | 10-24 | 278 | 一般層は完成。Rectification は中断 | 使わない |
| BhattScholze | 124 | 10.2 万 | 10-26 | 3,256 | 別セッションが作業中 | 入る |
| InfinityCategories/HomotopyLimits | 1,096 | 9.5 万 | 10-25 | 817 | ほぼ完成（γ3・γ4 はすでに使われている） | ルートが import しない |
| InfinityCategories/F1B | 799 | 6.9 万 | 10-25 | 980 | 完成（R13 で再編） | 使わない |
| HomologicalAlgebra | 545 | 5.7 万 | 10-26 | 3 | 完成・安定 | 526 本が入る |
| KST/Fibration | 779 | 5.6 万 | 10-27 | 977 | K-6 完了（10-27） | 使わない |
| InfinityCategories/Stable | 702 | 5.0 万 | 10-26 | 461 | 完成（D-7 の判定法だけ未完） | 使わない |
| CommutativeAlgebra | 466 | 4.5 万 | 10-26 | 9 | 完成 | 入る |
| InfinityCategories/Core | 358 | 3.8 万 | 10-25 | 82 | 完成 | 使わない |
| KST/Comparison・ProExcision | 731 | 6.5 万 | 10-19 | 0 | 凍結（決定 16）。ただし helper は今も使われている | 使わない |
| KST/DerivedGeometry・DerivedBlowup・SchemeLemmas・Descent | 1,283 | 11.3 万 | 10-19（Blowup は 10-26 にリファクタのみ） | 1 | 第 II 段まで休止 | 使わない |
| Spectra | 283 | 2.5 万 | 10-16 | 0 | 旧経路（M4 の対称スペクトル）。pointed の層だけが今も KST で使われる | 使わない |
| KST/NonConnective | 266 | 2.3 万 | 10-27 | 305 | 固定入力版は公開済み。10-27 の設計変更で関手性を ∞ 側へ移した | 使わない |
| InfinityCategories/DGNerve・DoldKanComparison・Coherent・PinchedHom | 415 | 4.1 万 | 10-25 | 21 | 完成 | 使わない |
| CategoryTheory | 206 | 1.7 万 | 10-17 | 0 | 安定 | 69 本が入る |
| KTheory | 151 | 1.4 万 | 10-15 | 0 | 完成・凍結（Adams 作用素、G₀・K₀） | 140 本が入る |
| CLMST | 146 | 1.2 万 | 10-26 | 39 | 完成（BS の入力に相対的に、10-17） | 入る |
| PerfectComplex | 124 | 0.9 万 | 10-15 | 0 | 完成・凍結（supported K₀、正規化長さ） | 123 本が入る |
| Paper | 75 | 1.0 万 | 10-17 | 0 | 上の 2 つの sorry を除いて完成 | 本体 |
| Asymptotic・LengthAlgebra・FieldTheory・IntersectionMultiplicity・GroupTheory・LinearAlgebra | 216 | 2.4 万 | 10-14〜17 | 0 | 完成 | 入る |
| Inputs | 14＋ | 0.1 万 | 10-26 | 3 | 引用層 | 入る |

二つの層に分けると見通しがよい。
- **論文の層**（Paper・Inputs・可換代数・ホモロジー代数・PerfectComplex・KTheory・LengthAlgebra・Asymptotic・IntersectionMultiplicity・CLMST・BS）：
  10-17 までにほぼ完成しており、穴は上の 3 つの引用だけ。
- **基盤の層**（InfinityCategories・KST・EInfinity・DG・HomotopicalAlgebra）：第 I 段で作業中。主定理はまだこの層に依存していない。
  定理 3.1 の二つの sorry を KST の結果で置き換える作業は第 II 段（foundations.md §7 の II-1・II-2）。

## 3. 各ディレクトリの内容

### 3.1 InfinityCategories（quasicategory 模型）

- **PinchedHom**（4 本）：右 pinched な写像空間 `pinchedHom`。最下層。
- **Core**（358 本）
  - 内容：join・slice、終対象、極限（`JoinCone`・`IsLimitCone`・`HasLimit`）、`IsQCatEquivalence`、`IsFullyFaithful`、写像空間の π₀、左・右 fibration。
  - import するのは PinchedHom だけで、依存がきれい。
- **Coherent**（40 本）：coherent nerve は quasicategory（`simplicialNerve_quasicategory`、γ1）。
- **DGNerve**（214 本）：dg nerve（`dgNerve`、quasicategory であること、H⁰ との比較）。符号の規約は DGNerve/README。
- **DoldKanComparison**（157 本）：Dold–Kan で豊穣化した coherent nerve ≃ dg nerve（`coherentComparison_isQCatEquivalence`）。
  入口の docstring には「同値の証明が残る」とあるが、これは古い。
- **F1**（2,626 本）：fibration、cocartesian 辺、左 fibration の straightening、Yoneda、𝒮 と Cat∞
  （`CatInfinity`・`SpaceInfinity`・`PresheafInfinity`・`yonedaInfinityMap_isFullyFaithful`・`leftStraighteningInfinityMappingComparisonEquivalence`）。
  - Cocartesian（618 本、Cat∞ 値 straightening）は休止。入口は別にあり、そのうち 491 本はルートから届かない。
  - Diagrams の 102 本も、どこからも import されていない。
- **F1B**（799 本）：随伴、Kan 拡張、cofinality と Quillen 定理 A、局所化（`IsLocalization`・deformation による判定）。
- **HomotopyLimits**（1,096 本）：ホモトピー極限 = ∞ 極限、Bousfield–Kan、重み付き極限、Quillen 随伴の比較。
  ルートは import しておらず、654 本は届かない。KST（20 本）と DoldKanComparison → DGNerve → DG に依存する。
- **F2**（4,629 本）
  - CatInfinity（297 本）：lax pullback とその安定性。
  - Ind（740 本）：`ind_isStable_unconditional`、compact な生成。
  - Compact（93 本）・Idempotent（169 本）：完成。
  - Presentable（1,195 本）：随伴関手定理、Bousfield 局所化、対ごとの双対性。PrL ≃ PrR^op 全体は第 II 段。
  - FilteredExchange（2,129 本）：直接経路は 10-25 に放棄された。1,941 本が届かず、72 本はどこからも import されない。
  - **`F2.lean` が import しているのは CatInfinity と FilteredExchange の 2 つだけで、残りは `#check` 1,497 行である。**
    Ind・Presentable・Compact・Idempotent はどこからも import されず、監査スクリプトでしかビルドされない。
- **Stable**（702 本）：`IsStable`・`IsExactFunctor`・ホモトピー圏の三角構造・有限極限と余極限。
  `Stable.lean` の最初の import が `Derived.CoherentBar.Compact.All` で、層が逆転している。
- **Derived**（4,153 本）
  - 内容：D(S)・Perf・dg 加群・Drinfeld 商（`dgQuotientNerveProjection_isLocalization`）・`IsStableVerdierSequence`・Morita・κ-compact な生成。
  - Gluing（1,073 本）は D2 で完了した。ただし入口はどこからも import されていない。
  - CoherentBar（601 本）は完成した。ClosureFunctoriality（35 本）は停止。SuspensionAction（21 本）は診断（反例）。
- **ルートから届かないもの**：14,788 本のうち 5,506 本（F2 3,933、HomotopyLimits 654、F1 613、Derived 290 ほか）。

### 3.2 KST（Kerz–Strunk–Tamme 経路。決定 16 で Land–Tamme ⊙ に置き換え）

| ディレクトリ | 内容 | 主な宣言 | 状態 |
| --- | --- | --- | --- |
| SConstruction | ∞ 版の S•、連結 K、BF Ω スペクトル、加法性、Thomason cofinality、dg ⊙ と Land–Tamme | `kSpace`・`kOmegaSpectrum`・`objectSAdditivityMap_localized_isIso`・`Cofinality.kSpectrumMap_cofinality`・`dgOdotMilnorCompletedLandTamme_isPullback` | 作業中（S 長方形の 3 つの証明） |
| LocalizingInvariants | 安定 ∞ 圏、Verdier 列、Sp 値の局所化不変量。局所化・分数の API の正本。β6、pro スペクトル | `StableInfinity`・`IsVerdierSequence`・`IsLocalizingInvariant`・`exists_quasicategory_localization` | K-5 は完成、残りは作業中 |
| Spectra | γ-B：BF Ω スペクトルの coherent nerve `Sp`、π_n、fiber 列、filtered 余極限、Tot | `OmegaSpectrum`・`Sp`・`OmegaSpectrum.sp_isStable (hB)` | 安定性は条件 B つき。停止準備完了で、供給待ち |
| Fibration | Verdier 列に対する連結 K の fibration 定理 | `k6FibrationOfC5` など | K-6 完了（10-27） |
| NonConnective | BGT §9 の dg 版非連結 K | `dgNonconnectiveK`・`dgNonconnectiveKCocone_isColimit` | 固定入力版は公開済み。関手性・局所化不変量としての登録は未完 |
| Comparison・ProExcision | KST §2（群完備化）、§4（pro 切除） | `groupCompletionKanMap_localized_isIso`・`IsProIso` | 凍結。ただし Ex∞・BasedPathEndpoint・pro の形式は今も使われている |
| DerivedGeometry・DerivedBlowup・SchemeLemmas・Descent | D_qc(X;H)、導来 blow-up、古典 blow-up、§3 の降下（公理化した前層） | `Dqc`・`chartTransition`・`affineBlowup`・`orbitStep_pi_bijective` | 第 II 段まで休止。Descent の補助 55 本は `[ModelCategory SSet]` つき |

- 論文側は KST を何も import していない。
- KST の中では、ディレクトリ同士がほぼすべての組で互いに import し合っている。ディレクトリの境界はレーンの所有の境界であって、層ではない。
- KST の外から KST を import しているファイルは 321 本ある（InfinityCategories 251、EInfinity 61、DG 8、HomologicalAlgebra 1）。
- 計画文書 k-theory-kst-route.md の冒頭にある「Lean の実装はまだない」（10-18）は古い。

### 3.3 代数とホモトピー

- **EInfinity**（3,384 本）
  - 内容：Barratt–Eccles と surjection operad、table reduction、interval cut、E∞ 代数の転送モデル構造、Dwyer–Kan の hammock 局所化、perfectoidization インターフェース（G1′）。
  - 状態：E2 は停止。README は 307 KB あり、記録としては大きすぎる。
- **DifferentialGraded**（2,258 本）
  - 内容：dg 圏、dg 加群（semifree・perfect = compact）、テンソル、Drinfeld 商、Morita。M5 は 10-17 に完成。
  - 検査用のファイル：Checks 410 本に加えて、ほかのディレクトリに散らばった `Checks*` が 143 本ある。
  - ルートから届かないものが 964 本、どこからも import されないものが 555 本ある。
- **HomotopicalAlgebra**（1,112 本）
  - 内容：Quillen 随伴、転送、Smith の認識定理、左 Bousfield 局所化、射影・Reedy 構造、function complex。一般層は 10-14 に完成。
  - Rectification（415 本）は中断している。
  - `[ModelCategory SSet]` を仮定するファイルが 249 本ある。互換入口が 121 本ある。
- **HomologicalAlgebra**（545 本）：Koszul 複体、Auslander–Buchsbaum、導来完備化、局所コホモロジー。完成していて、すべて登録済み。
- **Spectra**（283 本）：対称スペクトル（M4）。γ-B によって旧経路になった。pointed SSet と smash の層だけが KST などで使われている。
- **KTheory**（151 本）・**PerfectComplex**（124 本）：supported K₀・G₀・Adams 作用素・正規化長さ。10-15 から変更はないが主経路上にあり、完成した部分である（旧経路ではない）。
- **CategoryTheory**（206 本）：三角圏の K₀、Verdier と Karoubi、t 構造、モノイダル。HomotopicalAlgebra/Rectification の互換入口が 25 本ある。

### 3.4 論文の層

- **Paper**（75 本）：節ごとの適用。
  - §2：`theorem_2_5`（長さ代数）、補題 2.1・2.2、系 2.6。
  - §3：補題 3.4・3.5。
  - §4：定理 4.7。
  - §5：帰着と core。
- **BhattScholze**（124 本、約 10 万行）：Delta、Prism、André（Thm 7.14）、Semiperfectoid、Perfectoidization、Almost。引用は E3 インターフェースだけ。
- **CLMST**（146 本）：Cai–Lee–Ma–Schwede–Tucker（`proposition_2_4_7_proved`・`corollary_4_0_4`）。
- **CommutativeAlgebra**（466 本）：adic 完備化、Cohen–Gabber、p 基底、非混合性、幾何的ファイバー、根の塔。
- **Asymptotic**（87 本）：§4 の列の圏と階数商。
- **LengthAlgebra**（58 本）：正規化長さと Serre 商。
- **IntersectionMultiplicity**（21 本）：`chi`、Adams による消滅、対角議論。
- **FieldTheory**（41 本）・**GroupTheory**（5 本）・**LinearAlgebra**（4 本）：p 基底、共役和、基底の摂動。

## 4. 依存の向き（ディレクトリをまたぐ import 辺、上位）

| 元 → 先 | 本数 | 備考 |
| --- | ---: | --- |
| KST → InfinityCategories | 1,990 | 順方向 |
| InfinityCategories → DifferentialGraded | 686 | Derived・DGNerve・DoldKan。HomotopyLimits も経由する |
| KST → DifferentialGraded | 444 | SConstruction 254 |
| EInfinity → InfinityCategories | 336 | |
| BhattScholze → HomologicalAlgebra | 201 | |
| **InfinityCategories → KST** | 175 | 逆向き（Derived/Gluing 44・HomotopyLimits 20・F2/PiCriterion 9 など） |
| KST → HomotopicalAlgebra | 153 | |
| CLMST → CommutativeAlgebra | 134 | |
| KST → EInfinity | 29 | β6・FrameHom・Hammock |
| DifferentialGraded → KST | 13 | 逆向き |

InfinityCategories の内部にも、ディレクトリ単位の循環がある：F1 → HomotopyLimits 83、F1 → F2 28、F1B → Stable 54、Stable → Derived 10 など（R2 計画 §1.1）。

## 5. 気づいた問題（リファクタ・保守の候補）

1. **ルートがビルドしない完成品がある。**
   - ルートは F2・HomotopyLimits・Coherent・DoldKanComparison を import していない。`F2.lean` も Ind・Presentable・Compact・Idempotent を import していない。
   - そのため、Ind・presentable・Bousfield・Pr 双対が `lake build` の既定の対象から外れ、監査スクリプトでしか確かめられていない。
   - 入口を正すこと（`F2.lean` の `#check` 1,497 行を監査ファイルへ移し、サブ入口を import する）を R 候補にすべき。
2. **放棄・休止した大きな領域が残っている。**
   - 放棄：F2/FilteredExchange（2,129）。
   - 休止：F1/Cocartesian（618）、HA/Rectification（415）、Derived/ClosureFunctoriality（35）。
   - 凍結：KST/Comparison・ProExcision（731）。
   - 旧経路：Spectra（283、M4）。
   - それぞれについて、診断として保持するか、archive へ移すか、一般論を抽出するかを決める（R33・R36 の延長）。
3. **どこからも import されないファイルが多い。** DG 555、HA 123、F1/Diagrams 102、FilteredExchange 72、DG の散在した Checks 143 など。R42・R43 と合わせて台帳化する。
4. **層の逆転**：InfinityCategories → KST が 175 本、→ DG が 686 本。∞ 層の外にある一般論はおよそ 2,800 本ある（[外部調査](infinity-outside-survey-2026-10-28.md)）。
5. **古くなった記述**
   - DoldKanComparison の入口の docstring。
   - foundations.md の「γ4 未着手」。
   - k-theory-kst-route.md の「Lean の実装はまだない」。
   - KST/Comparison の「plus と K の比較は残工程」（凍結済み）。
6. **入口の命名**：F1・F1B・F2 は歴史的なレーンの名前で、数学的な層を表していない（R40 の層規約で扱う）。

## 6. 論文の層から切り出せる一般論（10-28 追加調査）

分類：U は一般論で Mathlib に上げられるもの、G はプロジェクト内で共有する基盤、P は論文に固有のもの。
宣言はすべて `namespace SerrePositivity` の下にあるため、Mathlib に上げるときは改名が必要。

| 群 | 分類 | 規模 | 主な宣言 | 切り出しの障害 | Mathlib の現状 |
| --- | --- | --- | --- | --- | --- |
| Auslander–Buchsbaum（HA/AuslanderBuchsbaum） | U | 1 本・約 400 行 | `auslanderBuchsbaum` | なし（プロジェクト内の import は 0） | ない |
| 三角圏の K₀・t 構造の heart（CategoryTheory/TriangulatedK0・TStructureHeart） | U | 各約 140 行 | `TriangulatedK0`・`heartAbelian` | なし | ない（heart が abelian であることは Mathlib の TODO） |
| Koszul 複体（CA/Koszul・KoszulResolution、HA Koszul*） | U／G | 中核は約 900 行、周辺は 45 本 | `koszulComplex`・`isKoszulResolution_of_isWeaklyRegular` | なし | ない（Mathlib に TODO あり） |
| 三角圏の Karoubi 完備化・Verdier t 構造（CategoryTheory） | U | 約 1,000 行 | `karoubiPretriangulated`・`verdierTStructure` | なし | ない |
| 正則局所環・局所平坦性判定・極小分解（CA） | U | 約 25 本 | `IsRegularLocalRing.of_maximalIdeal_hasProjectiveDimensionLE`・`flat_of_torModule_one_residueField` | `RegularLocalRing.lean` が IntersectionMultiplicity を import している | 定義だけある |
| Hilbert–Samuel・次元定理（CA） | U | 約 35 本・約 3,000 行 | `natDegree_poly_eq_dim`・`IsSystemOfParameters` | `MultiplicityFormulas` が LengthAlgebra と IM を引き込む | HilbertPoly だけある |
| adic 完備化・剰余体の拡大（CA） | U | 約 70 本 | `flat_adicCompletion_of_flat`・`exists_complete_flat_local_extension` | なし | 一部ある |
| p 基底・Cohen–Gabber・係数体（FieldTheory・CA） | U | 閉包は約 12,000 行 | `IsPBasis`・`exists_cohen_gabber_normalization` | なし（大きい） | ない |
| 局所コホモロジー・導来完備化（HA） | U／G | 11＋89 本 | `LocalCohomologyKoszulComparison`・`IsComplete` | BS と共有している | 定義だけある |
| supported K₀・G₀、dévissage、Adams、χ の消滅（KTheory・PerfectComplex・IM） | U／G | 閉包は約 40,000 行 | `K0WithSupport`・`g0QuotientDevissageEquiv`・`SupportedAdams`・`intersectionVanishing_of_adams` | PerfectComplex↔KTheory の循環、LengthAlgebra の逆向き import、二つの K₀ API の併存 | ない |
| 正規化長さ（PerfectComplex/NormalizedLength など） | G | 約 15 本 | `NormalizedLength` | — | — |
| 長さ代数・Asymptotic・CLMST・Paper | P | — | `PaperSequenceCategory` など | — | — |

- **Paper/ に紛れている一般の補題**
  - Section2：PerfectApproximation、PerfectTower、PerfectConductor、PerfectBaseChange、TowerApproximation（1,052 行、「補題 5.4 の一般論」）。
  - Section5：PrimeReduction、ParameterQuotient、Core、GaloisNormalization。
  - そのほか：Section4/LengthHypotheses、Lemma3_5 の `radical_span_eq_maximalIdeal` など。
  - Asymptotic/NormalizedLimit。
- **命名の問題**
  - CA/RootTower（18 本）と LengthAlgebra/RootTowerLength（7 本）が、一般の構成なのに `namespace Section2` を使っている。
  - Asymptotic には `paper*` で始まる名前が約 100 個あるが、中身は一般の階数商と底変換である。
  - supported K₀ が二通りある：`K0Supported T z`（列で添字づけ）と `K0WithSupport Z`（閉集合で添字づけ）。
- **費用対効果の順**：Auslander–Buchsbaum → TriangulatedK0・heart → Koszul の中核 → Karoubi と Verdier t 構造 → 正則局所環（先に IM への import を切る）→ p 基底と Cohen–Gabber → K 理論と交点数の一式（循環の解消と K₀ API の統一が先）。

## 7. 論文の層と基盤の層の重複・並行 API（10-28 追加調査）

機械検査の結果：
- `check_duplicates.py --scope SerrePositivity`：33,721 本を調べたが、層をまたぐ完全一致はなかった。
- 完全修飾名が両方の層で定義されている宣言は 0 件だった。
- 依存の向きはほぼ「基盤 → 論文」である（CategoryTheory.Monoidal 111 回、HA Cochain*、PerfectComplex、TriangulatedK0、VerdierLift、K0Localization など）。

| # | 論文の層 | 基盤の層 | 性質 | 推奨 |
| --- | --- | --- | --- | --- |
| 1 | CA/Koszul（錐の反復） | KST/DerivedBlowup/ExteriorComplex（外積代数）・ProExcision/KoszulPro | 同じ数学を別の模型で書いている。橋 `koszulExteriorIso` は既にある | そのままでよい |
| 2 | HA の Cochain*・ConeLES・StupidTruncation | KST/LocalizingInvariants の Cochain*（50 本）・DG/Complexes | 同じ `CochainComplex` に対する並行の補題群 | KST 側の一般補題を HA へ移す（急がない） |
| 3 | PerfectComplex/ClosedSupportRelations `strictlyPerfectComplex_isKProjective` | DG/Perfect/StrictComplexProjective（同名） | 同名・同じ主張だが、担体の型が違う（`CochainComplex (ModuleCat R)` と `Complex A`） | 片方をもう一方から導く |
| 4 | PerfectComplex（`PerfSupp`・`PerfectHomotopy`・`SupportedPerfectHomotopyOn`） | DG/Perfect・Derived の PerfectHomotopy・SupportHomotopy・DGPerfectModulesInfinity | 同じ数学を三つの模型で書いている。橋はあるが、圏同値どまりで三角構造を保つことまでは示していない | 第 II 段の橋（#5）として整える |
| 5 | `K0Supported`・`K0WithSupport := TriangulatedK0 (…)`・`freeClosedSupportK0Equiv` | KST/SConstruction/TriangulatedKZeroEquiv（π₀K(X) ≃ `TriangulatedK0 (ho X)`）・Derived/SupportK0 | 部分的な橋。基盤側も論文の `TriangulatedK0` を使っている（よい点） | **第 II 段の要**：(a) `perfectSupportHomotopyCategory` に前三角構造を載せる。(b) `perfectSupportClosedEquivalence` が三角構造を保つことを示す。(c) supported Perf_Z の KST 入力を作る。(d) 底変換と G 作用との整合を示す |
| 6 | `supportedRankK0_descent`（Asymptotic の `PaperRankQuotient` の上） | 対応するものはない | — | docstring どおり、論文の層の中で `theorem_3_1_K0` と補題 4.6 から導く。基盤が供給すべきものは `theorem_3_1_K0` だけになる |
| 7 | CategoryTheory/VerdierLift・VerdierKaroubi・SerreDerivedQuotient（Mathlib の `trW` 局所化） | DG/Verdier・Quotient、Derived の DGQuotient*（151 本）、KST の `IsVerdierSequence` | 三角圏レベルの API と ∞ レベルの API が並行している。比較 `fraction_ho_localization`（KST/LocalizingInvariants/VerdierFractionComparison.lean:44）は **private** | 公開する（定理 3.1 の K₀ 局所化列で使う見込み） |
| 8 | HA/DerivedCompletion の Milnor 列・塔 | KST/ProExcision の `Tower`・`IsProIso`、KST/Spectra の非可換 lim¹ | 塔と lim¹ を三通りに符号化している | そのままでよい（必要になったら橋を作る） |
| 9 | CA/HilbertSamuelPolynomial の `ReesGraded` | KST/SchemeLemmas/Blowup（Mathlib の `reesAlgebra`、宣言名も同じ） | 同じ数学を別の担体で書いている | 優先度は低い |
| 10 | CategoryTheory/Monoidal（67 本）・NerveHomotopy・Quiver・Simplex・Enriched、GroupTheory/Coxeter | Spectra の Day 畳み込み・DG/Tensor・KST の CubicalDay | 論文の層のツリーにあるが、使っているのは基盤だけ | 基盤の層へ分類し直す |
| 11 | HA/ComplexLimits（3 本） | EInfinity/ComplexLimits（3 行の転送） | **逆転**：論文の層のファイルが `KST.LocalizingInvariants.CochainConnectiveLift` を import している。使っているのは EInfinity と ∞ 層だけ | EInfinity 側へ戻すか、CochainConnectiveLift を HA へ下ろす（R34 と同じ） |
| 12 | Inputs/Homotopy（KanQuillen・SimplicialLevel・ResolutionHom） | Spectra/ModelCategory・HA | 基盤の入力が論文の Inputs の下に置かれている | 論文の引用と分けて置き直す |
| 13 | CA/RegularSequence・KoszulResolution・GeometricFiber | KST/DerivedBlowup・Descent | 共有しているだけで、競合する定義はない | そのままでよい |
| 14 | — | F1/Universe/PinchedHom ↔ F1B/Localization/UniversePinchedHom | 基盤の内部で、本文 53 行が同一（名前空間だけが違う） | 一方を削除する |
