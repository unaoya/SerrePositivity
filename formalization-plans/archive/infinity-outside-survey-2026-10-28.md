# InfinityCategories の外にある ∞ 圏・Kan 複体の一般論（2026-10-28 調査、HEAD cbb891432、コード変更なし）

概要：KST・KTheory・Spectra・PerfectComplex・HomotopicalAlgebra・EInfinity・DifferentialGraded の 17,141 ファイルを調べ、
InfinityCategories に置くべき一般論がどれだけあるかを数えた。
方法：まず語彙で機械的に候補を抜き出した（コメントを除いた本文に ∞ 圏・安定・単体の語彙を含み、dg・K・スペクトル・環の語彙を含まないもの、5,817 本）。
次に、3 つのエージェントがファイル名の接頭辞で群に分け、群ごとに見本を読んで分類した。
分類：G は一般論、M は一般の核と K・スペクトル固有の包装が混在、S は語彙判定をすり抜けただけの固有の内容。
数は群の境界の取り方による概数である。
使われ方：[refactoring-verdier.md](stage-i/refactoring-verdier.md) と R 第 2 窓の候補選定に使う。

## 1. 総計

| 範囲 | G ファイル／宣言 | M | S |
| --- | --- | --- | --- |
| KST/Spectra・SConstruction | 1,055 ／ 4,884 | 245 ／ 1,117 | 1,289 ／ 6,849 |
| KST の残り（Fibration・LocalizingInvariants・Descent・Comparison など） | 1,053 ／ 4,784 | 489 ／ 2,228 | 186 ／ 867 |
| HomotopicalAlgebra・EInfinity・Spectra・KTheory・DG・PerfectComplex | 697 ／ 3,594 | 569 ／ 4,961 | 228 ／ 890 |
| **合計** | **約 2,800 ／ 13,300** | 約 1,300 ／ 8,300 | 約 1,700 ／ 8,600 |

参考として、InfinityCategories 本体は 14,788 ファイルある。外にある一般論は本体のおよそ 2 割にあたる。
DifferentialGraded・KTheory・PerfectComplex には、一般論はほぼない（S のみ）。

## 2. 主な群（G と M）

### KST/LocalizingInvariants・Fibration

| 群 | ファイル／宣言 | 内容 | 移し先 |
| --- | --- | --- | --- |
| L4 局所化の存在 | 40 ／ 179 | **任意の辺集合 W に対して quasicategory 局所化が存在する**（`exists_quasicategory_localization`、LocalizationResolution.lean:37。逆辺の貼り付けと inner anodyne 置換による）。`edgeLocalization`・`localizationDescend`・一意性・groupoid 完備化も含む | F1B/Localization（最優先） |
| L3 Verdier 分数 | 131 ／ 1,014 | `verdierFractionMappingComparison_isFullyFaithful`：B/A の写像空間は分母についての filtered 余極限になる（NS I.3、9 人論文 II 付録 A）。marked span の族は cocartesian | Stable/Verdier/Fractions |
| F2 W 分数 | 90 ／ 353 | W = q⁻¹(同値) に対する右 Ore 四角形、span の余極限としての写像空間 | 同上 |
| L2 Tamme | 23 ／ 91 | Tamme 商の Ore と分母。**F2 の Weak* とほぼ同じ証明の複製**（WeakOreSpanLift↔TammeOreSpanLift など 4 対） | 同上（統合する） |
| L1 lax・半直交 | 56 ／ 281 | lax pullback、半直交分解から Verdier 列を作る、普遍 lax 差（Tamme、Land–Tamme）。**InfinityCategories/Derived/Gluing がこれらを KST から import している** | Stable/Lax・Stable/Semiorthogonal |
| L6 安定の cofiber・完全 | 84 ／ 407 | 0・fib・cofib で閉じた充満部分圏は安定、cofiber の回転は完全、Σ は完全 | Stable |
| L7 quasicategory の道具 | 182 ／ 849 | 矢の圏の随伴、opposite の随伴、反射的部分圏の判定、自明 fibration の切断から作る随伴 | Core・F1B |
| L5 CoreFlag | 12 ／ 62 | diag(n ↦ core Fun(Δⁿ,C)) → C は弱同値 | F1 |
| F3 straightening・Kan | 209 ／ 743 | 左 straightening の点の追跡、strict Kan 完備化 ≃ groupoid 完備化、空間値図式の局所化による降下 | F1/StraighteningLeft・KanModels・Transport |
| F1 S• fibration | 406 ／ 1,812 | Verdier 列の S• は fiber 列（M。一般の部分は約 50 本） | KST に残し、一般部分は Stable/Verdier へ |

### KST/Spectra・SConstruction

| 群 | ファイル／宣言 | 内容 | 移し先 |
| --- | --- | --- | --- |
| Sp-S1 Kan 複体のホモトピー群 | 150 ／ 678 | π_n、Kan fibration の長完全列、Whitehead、anodyne は π_* 同型（GJ I.7–8） | 新設の Kan/、または HA/Simplicial |
| Sp-S2 pointed 単体的集合 | 223 ／ 993 | Σ ⊣ Ω、基点付き内部 Hom、道空間 fibration、ループの積 | 新設の Pointed/ |
| Sp-S3 塔 | 89 ／ 349 | Kan fibration の塔、Milnor 列、lim¹、Mittag–Leffler、skeleton による filtration | Kan/Towers |
| Sp-S4 重み付き極限（M） | 156 ／ 637 | pointed 版の Bousfield–Kan holim、Reedy、Tot | HomotopyLimits |
| Sp-S5 coherent nerve の計算 | 87 ／ 467 | 厳密な自然変換を coherent nerve の中のホモトピーに直す、パラメータ柱 | F1/Coherent |
| SC-C2 安定・余極限 | 81 ／ 375 | Fun(A,C) は安定、0 対象の空間は可縮、各点余極限、閉じた安定部分圏。**複製が多い**（§3） | Stable・Core |
| SC-C3 Kan 複体の整合性の道具 | 204 ／ 1,000 | ホモトピーの鎖の持ち上げ、柱の貼り合わせ、filler の空間は可縮 | Core（KanFibrationTools の隣） |
| SC-C4 pointed の豊穣 | 114 ／ 477 | smash・Σ の関手性、pointed pushout、Ex∞ の pointed 版 | Pointed/ |
| SC-C5 necklace・基本亜群 | 107 ／ 545 | Dugger–Spivak の necklace、単体的集合の基本亜群 | Coherent・Core |
| SC-C1 の一般部分（M） | 89 ／ 480 | 単体的集合の Quillen 定理 A、elements resolution | HomotopyLimits・Pointed |

### HomotopicalAlgebra・EInfinity

| 群 | ファイル／宣言 | 内容 | 移し先 |
| --- | --- | --- | --- |
| EI/SimplicialLocalization | 107 ／ 513 | Dwyer–Kan の相対圏、hammock 局所化とその coherent nerve。**モデル圏の ∞ 局所化**（`modelHammock_isLocalization`、`[ModelCategory SSet]` は不要）。right frame の Hom と pinchedHom の比較 | F1B/Localization/DwyerKan |
| EI/Hammock | 169 ／ 716 | 両側 bar、Thomason の定理、Ex∞ の豊穣 | Core・F1 |
| EI/FrameHom | 170 ／ 744 | Hovey の frame、Brown の分解、nerve の Quillen 定理 A、frame 圏の cofinality | F1B・HomotopyLimits |
| HA/Simplicial | 169 ／ 1,053 | Kan 複体、anodyne、Kan 置換、宇宙の持ち上げ、対角 | すでに ∞ 層の下で使われている。そのまま置くか Core へ |
| HA/HomotopyFunctionComplex | 74 ／ 526 | Hovey 5 章の function complex、Reedy | HomotopyLimits の入力層 |
| HA/Rectification（M、中断） | 367 ／ 3,952 | 210 ファイルが `[ModelCategory SSet]` を仮定している | 移さない |

## 3. 複製・類似（統合の候補）

- **∞ 層との複製**
  - SConstruction 側と ∞ 層側の対：`CoreTrivialFibration`↔F2/CatInfinity/CoreTrivialFibration、`TrivialFibrationStability`↔Stable/TrivialFibrationStability、
    `RelativeInitialExtension`↔F1B/FunctorCategories/RelativeInitialExtension（補題名も同じ）、`InitialBoundaryIso`↔F1B/Cofinality/InitialBoundaryIso、
    `PushoutTranspose`↔Stable/SquareTranspose、`EdgeTargetColimit`↔HomotopyLimits/EdgeTargetCocone。
  - `FunctorPointwiseColimit*` は Core/FunctorPointwiseLimit* の双対。
- **KST 内部・他ディレクトリとの複製**
  - LocalizingInvariants の `SuspensionExactFunctor`↔Stable/Suspension、`AdjunctionOfOpposite`・`OppositeAdjunction`↔Stable/AdjunctionOpposite。
  - Fibration の Weak*↔LocalizingInvariants の Tamme*（4 対、辺の集合だけが違う）。
  - Ex∞ が EInfinity/Hammock と KST/Comparison の二か所にある。
  - MappingCylinder が KST/Comparison・F1B/Diagrams・F1/MappingSpaces の三か所にある。
  - `localization_extension_exists`（EInfinity/FrameHom）↔F1B の `IsLocalization.exists_extension`。
- **Spectra との類似**
  - `Spectra/HomotopyProduct`≈HomotopyLimits/KanPiProducts、`LastHornContraction` が二か所。
  - `CoherentTrianglePathMinimum` が三か所（Spectra・F2/FilteredExchange・HomotopyLimits）。

## 4. 移すうえでの障害

1. **逆向きの import がある。** InfinityCategories のうち 135 ファイルが KST を import している（Derived 102、HomotopyLimits 20、F2 11、F1 2）。
   例として、HomotopyLimits/KanWhiteheadComparison は KST.Spectra.PointedKanWhitehead を、HomotopyLimits/SpectrumMappingDiagram は `Sp` を import している。
   Sp-S1・S2 を先に移せば、その大半が解消する。
2. **束ねた `StableCategory`・`ExactMap` が LocalizingInvariants にある。** L1〜L3・F2 は、これを含む基礎ブロック（refactoring-verdier R48）を移した後でないと移せない。
3. **∞ 層そのものが dg に依存している。** HomotopyLimits → DoldKanComparison → DGNerve → DifferentialGraded の経路があり、F1 の 4 ファイルも DGNerve を import している。
   また、hammock 局所化の閉包には E∞ への import（BarrattEccles）と Derived.CofinalLimitTransfer が 1 本ずつ入っている。
4. **pointed の基盤の置き場が決まっていない。** SerrePositivity/Spectra/PointedSimplicialSet と Spectra/Pointed は Sp-S2 と SC-C4 の土台である。∞ 層の下へ移すか、HA に置くかを決める必要がある。
5. **語彙判定の誤検出**
   - HA/HomotopyFunctionComplex/Reedy/FunctorData.lean:56 の `let dg := …` が dg と判定され、Reedy 系が「閉包が汚れている」扱いになった。
   - ModelCategory はモデル圏の一般論として G 側に数えた。ただし、主経路に `[ModelCategory SSet]` を置かない方針との整合は別途確認が必要。
