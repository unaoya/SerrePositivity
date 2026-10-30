# 伝達：CategoryTheory の下位ディレクトリと Nerve まわりの整理を ∞ 基盤の作業へ（2026-10-30）

宛先：∞ 基盤の整備（[infinity-foundation-plan.md](infinity-foundation-plan.md)、Codex の指示書 IF-Wn）を管理している側。
差出：論文の層の整理（[refactor-plan.md](refactor-plan.md)）のコーディネータ。
要旨：論文の層の見直しで CategoryTheory を調べたところ、下位ディレクトリ（104 本）と Nerve まわり（9 本）は ∞ 基盤の側しか使っていないことが
分かった。ユーザーの決定（2026-10-30）により、この整理は ∞ 基盤の指示書に含めて行う。論文の層の側ではこれらのファイルに触れない。
以下は調査結果と、決まっていることの引き渡し。R 番号への採番と、指示書のどの単位に入れるかはそちらで決めてほしい。

## 1. 範囲

- `SerrePositivity/CategoryTheory/` の下位ディレクトリすべて：Monoidal/（67）・Presentation/（15）・Quiver/（7）・Simplex/（6）・Enriched/（3）・
  LiftingProperties/・Limits/・Groupoid/・MorphismProperty/（計 104 本、約 8400 行）。
- トップ階層の Nerve まわり 9 本：NerveHomotopy・NerveHomotopyUniverse・NerveSimplexEndpoint・NerveSimplexStart・NerveSimplexFirstFunctor・
  NerveVertices・SimplexChainVertices・ElementsChainLifting・ElementsNaturalPrecomp。
- トップ階層の再エクスポートの殻 7 本：AnchoredChain*・ArrowContext・LabelledChain・SimplexChainParameter（HomotopicalAlgebra/Rectification を
  再エクスポートするだけ。importer は `scripts/audit/shared.lean`・`scripts/audit_homotopical_foundations.lean` だけ）。
- `Spectra/SymmetricSequence/` の殻 4 本（TensorPowers・TensorPermutations・AdjacentTranspositions・AdjacentBraid、各 10 行で Monoidal/* を再エクスポート）。

利用者はすべて Spectra・HomotopicalAlgebra（主に `HomotopicalAlgebra/GeneralTools` の再エクスポート経由）・EInfinity・KST・InfinityCategories。
**BhattScholze・CLMST・論文の層（Paper・Asymptotic・PerfectComplex・KTheory など）は import も名前の参照もしない。** BS の再ビルドは起きない。

## 2. 決まっていること（ユーザー、2026-10-30）

1. Nerve まわり 9 本を `HomotopicalAlgebra/Simplicial/` の側へ移す。今は NerveVertices が `HomotopicalAlgebra/Simplicial/VertexTuples` を、
   NerveSimplexFirstFunctor が `HomotopicalAlgebra/Simplicial/SimplexNerveAugmentation` を import し、後者は `CategoryTheory/SimplexChainVertices` を
   import していて、二つのディレクトリが互いに依存している。移せば解消する。利用者は HomotopicalAlgebra 14・EInfinity 10・KST 4・CategoryTheory 2。
2. 下位ディレクトリの整理は ∞ 基盤の指示書に含める（論文の層の側では行わない）。

## 3. 調査結果（2026-10-30、読むだけ）

### 3.1 死んだファイル

- Presentation/ の 15 本すべてと Quiver/WeightedPaths・WeightedPathMaps：各 24 行で、同名の `HomotopicalAlgebra/Rectification/CategoryTheory/…` を
  再エクスポートするだけ。importer なし、ルートの `SerrePositivity.lean` にもない。参照は `scripts/homotopical_generalization_manifest.json` だけ。
- §1 のトップ階層の殻 7 本と Spectra の殻 4 本。

### 3.2 統合案（104 → 約 35 ファイル）

| 新しいファイル | 元のファイル |
| --- | --- |
| Monoidal/Mod/Free | FreeModule |
| Monoidal/Mod/Limits | ModuleLimits・ModuleColimits・ModuleTransport |
| Monoidal/Mod/BalancedTensor | BalancedTensor・BalancedTensorModule・BalancedTensorIterated・TensorRightModule |
| Monoidal/Mod/Monoidal | BalancedTensor{Associator,LeftUnit,RightUnit,Triangle,Pentagon,Monoidal} |
| Monoidal/Mod/Symmetric | BalancedTensor{Symmetry,Hexagon,Symmetric} |
| Monoidal/Mod/FreeTensor | BalancedTensorFree{Left,Right,Pair,Unit,Associator}・FreeModuleMonoidal |
| Monoidal/Mod/InternalHom | ModuleInternalHom・…Action・…Functor |
| Monoidal/Mod/InternalHomFree | ModuleInternalHomFree*・…Transport* |
| Monoidal/Mod/Closed | ModuleClosed |
| Monoidal/TensorPower/Basic | TensorPowers・TensorPowerCoherence |
| Monoidal/TensorPower/Permutation | TensorPermutations・AdjacentTranspositions・AdjacentBraid・PermutationAction |
| Monoidal/TensorPower/Blocks | TensorPowerBlockGenerators・LeftBlock・BlockPermutations・FirstCrossing・FirstCrossingAction |
| Monoidal/TensorPower/FinBijection | PowerBijectionFunctor・PowerBijectionAppend |
| Monoidal/Action | ActionProductComparison・TensorActionTransport |
| Monoidal/Braided | BraidingPreservation・InternalHomExchange |
| Enriched/RepresentedMapping | Mapping{Adjunction,ParametrizedAdjunction,UnitLaws,Associativity,ArrowComposition,Whiskering}・RepresentedMappingEnrichment・RepresentedHomFunctor（今は Monoidal/ にあるが中身は豊穣圏） |
| Enriched/Transport | TransportOrdinaryEnrichment・TransportEnrichmentComparisons・LaxPointHom・ReverseComposition |
| Enriched/Simplicial | SimplicialHomLaws |
| Enriched/TensorCotensor | TensorCotensor・TensorUnit・EnrichedRepresentability |
| Adjunction/Comparison | ActionComparisonAdjunction・ActionUnitAdjunction・ActionComparisonNaturality・AdjunctionCompositeNaturality・HomEquivNaturality（モノイダル構造を使わない） |
| Quiver/FreePathComonad | FreePathComonad・PathObjectTransport |
| Quiver/PathMap | PathIntersections |
| Simplex/Prefix | Prefix・PrefixInterval |
| Simplex/GenRelEquivalence | PresentationDegeneracies・PresentationFaces・PresentationEquivalence（約 470 行） |
| Under | LiftingProperties/Under・MorphismProperty/UnderFactorization |
| Limits | Limits/InitialColimits・Limits/SequentialExtension・LiftingProperties/ParametrizedGeneration・Groupoid/ThinComponents |

### 3.3 Mathlib との重なり（固定版 2026-10-07 と最新版 2026-10-28 で差なし）

- `QuiverPaths.natTransOfEdges`（Quiver/PathNatTrans）= `Paths.liftNatTrans`（確度高）。
- `functor_ext_edges`・`prefunctor_hext`（Quiver/PathFunctorExt）= `Paths.ext_functor`（HEq の代わりに eqToHom、確度高）。
- Quiver/FreePathComonad の `comonad` ≈ `Quiv.adj.toComonad`（確度中〜高）、`mapPath` ≈ `Prefunctor.mapPath`（確度中）。
- `Simplex/Naturality.property` = `MorphismProperty.naturalityProperty`、証明は `SimplexCategory.morphismProperty_eq_top`（確度高）。
- `ActionComparisonAdjunction.rightIso`・`ActionUnitAdjunction.rightUnitIso` は `(a.ofNatIsoLeft e).rightAdjointUniq b`（確度高）。
- 豊穣化の作用は `MonoidalRightAction`、Transport* は `TransportEnrichment`・`enrichedOrdinaryCategory` と重なる見込み（確度中）。
- Mathlib にない（提出候補）：`SimplexCategoryGenRel ≌ SimplexCategory`（Mathlib に明示の TODO。最有力）、可換モノイド対象上の `Mod` の自由加群・
  極限・balanced tensor・対称モノイダル閉構造、Under 版の持ち上げ性質・分解、細い亜群と成分の同値、テンソル冪への置換群の作用。

### 3.4 その他

- 未使用の宣言：Enriched/TensorCotensor の自然性 5 つと `cotensor_triangle`、BalancedTensor 系の `_hom`・`_inv` 約 15 など（論文の層の計画
  §1.3.4 に一覧）。ファイルの中だけで使う約 120 の名前は private に。
- 104 本のうち 55 本が `backward.isDefEq.respectTransparency false` を設定。名前空間をファイル名から付けたもの（`SerrePositivity.HomEquivNaturality` など）に
  一般的な名前が入っている。`def …Law : Prop` で等式を包む書き方が多い。
- LiftingProperties/Under・UnderFactorization は Mathlib の名前空間に直接置いている。Mathlib を上げると衝突しうる（論文の層の計画 H に記録済み。
  この整理の間は Mathlib を上げない、ユーザー決定）。
- NerveHomotopy と NerveHomotopyUniverse はほぼ同じ（後者は `ULift` で宇宙を独立にしたもの）。NerveSimplexEndpoint と NerveSimplexStart は双対。

## 4. 論文の層の側の扱い

- 論文の層の計画の段階 0（殻と死んだファイルの一掃）からは、§1 のファイル（CategoryTheory の下位ディレクトリ・Nerve まわり・トップ階層の殻 7 本・
  Spectra の殻 4 本）を除いた。こちらでは触らない。
- CategoryTheory のトップ階層の残り（Karoubi・三角圏・t 構造・Euler・K₀ など）は論文の層の側で整理する。それらのファイルは §1 のファイルを import
  しない見込みだが、作業の前に互いに確かめる。
- 詳細の正本：`formalization-plans/refactor-plan.md` 第 1 章 §1.3（今後こちらでは更新しない。以後の正本はそちらの計画）。

## 5. 追加の伝達：HomologicalAlgebra/ComplexLimits/ の 3 本（2026-10-30）

ユーザーの決定により、次の 3 本も ∞ 基盤の側へ渡す。論文の層の側では触らない。

| ファイル | 行 | import | importer |
| --- | --- | --- | --- |
| HomologicalAlgebra/ComplexLimits/ExtendTruncationHom | 53 | `KST.LocalizingInvariants.CochainConnectiveLift`・Mathlib `Algebra.Homology.Embedding.Extend` | 下の 2 本、`EInfinity/ComplexLimits/ExtendTruncationHom` |
| HomologicalAlgebra/ComplexLimits/ExtendTruncationHomNaturality | 45 | 上の 1 本 | 下の 1 本、`EInfinity/ComplexLimits/ExtendTruncationHomNaturality` |
| HomologicalAlgebra/ComplexLimits/TruncationInclusionNaturality | 61 | 上の 1 本 | `EInfinity/ComplexLimits/TruncationInclusionNaturality`、`InfinityCategories/Derived/CoherentBar/Compact/PinchedCohomologyNaturality` |

- 名前空間は `SerrePositivity.EInfinity.ComplexLimits`。KST を import しているので、HomologicalAlgebra に置くと層が逆転する
  （論文の層の HomologicalAlgebra は ∞ 基盤より下）。
- `EInfinity/ComplexLimits/{ExtendTruncationHom, ExtendTruncationHomNaturality, TruncationInclusionNaturality}` は同名の再エクスポートの殻
  （commit fcc305646 で作られた互換ファイル）。実体を EInfinity/ComplexLimits/ へ移して殻と置き換えるのが自然。
- 論文の層の側（BhattScholze・CLMST・Paper ほか）は 3 本を import しない。`scripts/audit/shared.lean` が import しているので、移したら
  `python3 scripts/make_area_audits.py` で再生成する。
