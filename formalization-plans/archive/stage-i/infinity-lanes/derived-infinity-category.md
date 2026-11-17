# D(S)：semifree 複体の dg nerve としての導来 ∞ 圏（レーン D）

作成日：2026-10-17。更新：2026-10-19。状態：D1〜D10 完了。D7 の安定性と D3 の三角同値化を D レーンで完成。
全体の目標と依存関係の正本は [infinity-categories.md](infinity-categories.md) §0・§3。
dg nerve（レーン N）は [dg-nerve.md](dg-nerve.md)。

## 現在地

D1・D2（シフト、cone・fiber・余積・テンソル積・底変更の閉性を含む）・D3・D4・D5 は完了。
D4 は任意の四角形について標準 fiber への比較射の擬同型性との双方向の判定を持つ。
D6a は完了。指定四辺による distinguished triangle と全整数次数の Hⁱ の長完全列を持ち、
零次の射は D5d の H⁰ に一致する。接続射は D3 のシフト比較を通じて持ち上がる。
D6b は完了。加群の離散埋め込み J は充満忠実で、H⁰ の自然同型は D5b の増大射を使う。
D6c は完了。Hⁱ(x)=0（i≠0）と h D(S) での x≅J(H⁰x) の同値を持ち、
比較同型を表す可逆な辺も公開する。D7 は完了。実 coslice 充填による cofiber の普遍性、全四角形の双カルテジアン判定と `derivedInfinityCategory_isStable` を証明済み。実 suspension と複体シフトの自然同型、安定構造の全整数シフトとの整合性を構成し、標準 cofiber 三角形の D3 像が Mathlib の符号付き cone 三角形と同型であることを証明した。鎖写像代表と source の TR3 から全 distinguished triangle の保存・反映へ拡張し、逆関手と単位・余単位も含む `derivedStableHomotopyEquivalenceIsTriangulated` を公開した。

D8 は完了。Perf(S) は D(S) の実際の充満部分単体集合で、quasicategory・零対象を持つ。
シフト・cone・fiber・有限直和を正本の頂点上に構成し、D4 の擬同型判定を双方向に制限した。
標準包含 h Perf → h D(S) は充満忠実で、その本質像は有界有限射影複体の導来像である。
U13 の一対象 perfect dg 加群の H⁰ との圏同値も実装済み。公開入口は `Derived/Perfect.lean`。


D9 は完了。一般の D_Z(S) は各 Hⁱ の幾何学的台で定義する。主イデアルでは
各 Hⁱ が元ごとの a 冪ねじれであること、D5c の底変更 X ⊗^L S[1/a] が零になることと同値。
Perf_Z(S)=Perf(S)∩D_Z(S) は実際の全部分単体集合である。両者の quasicategory 性・零対象と
semifree モデルのシフト・cone・fiber・有限直和閉性を実装済み。
完全対象上では、台 ⟺ 局所化底変更で零 ⟺ scalarSupported の三条件が一致する。
この比較は有限射影代表の null-homotopy 定理を使い、可換環に Noether 条件を課さない。
一般には最後の同値は成立しない：S=ℤ、a=2、H⁰=⊕ₙ≥1 ℤ/2ⁿ は V(2) に台を持つが、
恒等射を消す共通の 2 の冪はない。一般の台条件を scalarSupported に置き換えない。
正本上のシフト・cone・fiber・有限直和と、D_{V(a)} の任意の小さい直和を構成した。
h Perf_Z は既存の SupportedPerfectHomotopyOn Z と圏同値で、有限生成イデアルでは
scalarSupported 版の圏とも同値。標準単体包含のホモトピー関手は充満忠実である。
既存の K₀WithSupport の代表と D5c の底変更の像をホモトピー同型で比較し、
Perf_{V(a)} の類の局所化による零化を示した。K₀Supported の有限自由版との比較は
任意環では写像、局所環では同型。既存 K₀ 局所化列の核・像と全射性の比較には
両環の Noether 性と有限射影解像度の仮定を保持する。
一般の dg 商の nerve 比較は N β3 待ちで主張に含めない。
D10 は完了。Moore 複体の同定は次のとおり。実際の pinched Hom の各単体の集合に線形構造を転送し、
忘却後の比較が各単体を変えないことを証明した。Moore 正規化と ULift の交換を示し、
任意 dg 圏で N(pinchedHomModule x y) ≅ ULift(τ≤0 Hom(x,y)) を複体として構成した。
全非負 chain 次数 n のホモロジーは ULift(H^{-n} Hom(x,y)) に同型で、零次数も含む。
D(S) への適用は derivedInfinityMooreIso。
K-L9a の充填による正次数ホモトピー群を Moore ホモロジーへ群同型で比較した。
境界定数単体を全ての面が零の元へ送り、充填関係と差が Moore 境界となる条件を同定する。
積は最後の二つの退化の和で計算し、群演算とホモロジーの加法の一致も証明した。
零写像を基点として π_{n+1} Map(x,y) ≅ H^{-(n+1)} Hom(x,y) ≅ Ext^{-(n+1)}(x,y)
を群同型で公開する。零次数は π₀ Map(x,y) ≃ H⁰ Hom(x,y) ≃ Ext⁰(x,y) の全単射。
Ext^i は通常の導来圏の Hom(X,Y[i]) と定義し、この段階だけ HasDerivedCategory を仮定する。
可換環に有界性・Noether 性・完全性を課さず、標準導来圏での具体化も検証済み。
D7 と dg 商の nerve 比較（β3）は D レーンで順に進め、D9・D10 の主張に含めない。

## 主要宣言

namespace は `SerrePositivity.InfinityCategories`。正確な型・前提は Lean ソースを正本とする。

| 範囲 | 公開宣言 |
| --- | --- |
| semifree と導来圏 | `complexSemifree`、`Semifree`、`semifreeDerivedEquivalence` |
| 閉性 | `complexSemifree_mappingCone`、`complexSemifree_biprodFiber`、`complexSemifree_tensor`、`complexSemifree_baseChange` |
| D(S) とホモトピー圏 | `derivedInfinityCategory`、`derivedInfinityCategoryQuasicategory`、`derivedInfinityHomotopyEquivalence` |
| 通常の nerve からの射 | `closedNerveInclusion` |
| 関手的解像度・離散埋め込み | `moduleSemifreeResolutionFunctor`、`discreteEmbedding`、`discreteEmbeddingHomologyZeroIso` |
| 底変更 | `semifreeBaseChangeDG`、`dgNerveRestrictScalarsIso`、`derivedInfinityBaseChange` |
| Hⁱ の基礎比較 | `derivedInfinityHomologyFunctor`、`derivedInfinityHomologyIso_naturality` |
| fiber の三角形 | `fiberProjection_eq_mappingCocone_fst`、`fiberComparisonDerivedTriangle_distinguished` |
| 指定脚の比較 | `derivedConeLegCompStruct`、`derivedConeLeg_pullback_bottom`、`derivedConeLeg_pullback_left` |
| 指定四辺の長完全列 | `derivedSquareFiberTriangle_distinguished`、`derivedSquareInfinityHomologyLongExact`、`derivedSquareInfinityHomology₂_f_zero`、`derivedSquareInfinityHomology₂_g_zero` |
| 接続射とシフト | `derivedSquareConnectingHomotopy_shift` |
| heart の充満忠実性 | `moduleHeartFunctor`、`moduleHeartHomEquiv`、`moduleHeartHZeroNatIso`、`moduleHeartHomEquiv_hZero` |
| 離散対象の特徴づけ | `derivedInfinityDisc`、`derivedInfinityDiscIso`、`derivedInfinityDisc_iff`、`derivedInfinityDiscEdge_invertible` |
| 完全対象 | `perfectInfinityCategory`、`perfectNerveModelIso`、`perfectSemifreeProperty_iff`、`perfectInfinityCategory_quasicategory`、`perfectInfinityZero_terminal`、`perfectInfinityZero_initial` |
| Perf の引き戻し判定 | `perfect_isPullbackSquare_iff_quasiIso` |
| h Perf の像と U13 | `perfectCanonicalHomotopyInclusion`、`perfectCanonicalHomotopyInclusion_essImage_iff`、`perfectInfinityU13Equivalence` |
| 台つき部分圏 | `derivedSupportCategory`、`perfectSupportCategory`、`perfectSupportSubcomplex_eq_inf` |
| 台と局所化 | `derivedSupport_iff_baseChange_isZero`、`perfectSupport_localization_scalar`、`perfectSupportCategory_baseChange_zero` |
| 台つき h 比較 | `perfectSupportClosedEquivalence`、`perfectSupportScalarEquivalence`、`perfectSupportBaseChangeIso` |
| 台つき K₀ | `perfectSupportK0Class_localize_zero`、`supportedFreeK0Equivalence`、`supportedK0_localization_kernel`、`supportedK0_localization_surjective` |
| 写像空間の Moore 複体 | `pinchedHomModule`、`pinchedHomModuleForgetIso_apply`、`pinchedHomMooreIso`、`derivedInfinityMooreIso` |
| Moore ホモロジー | `connectiveHomHomologyIso`、`pinchedHomMooreHomologyIso` |
| 写像空間の π・Ext | `modulePiMooreGroupEquiv`、`derivedInfinityPiCohomologyEquiv`、`derivedInfinityPiExtEquiv`、`derivedInfinityPiZeroExtEquiv` |
| H⁰ | `derivedInfinityHZeroFunctor`、`derivedInfinityHZeroIso`、`derivedInfinityHZeroMap` |
| 引き戻しの判定 | `derivedSquareFiberComparison`、`derived_isPullbackSquare_iff_quasiIso` |

過去の実施記録と公開型一覧は [アーカイブ](../../derived-infinity-category-log.md) に置く。
今後の検証経緯はコミットメッセージに、宣言名と型の一覧はアーカイブに記録する。

## 0. 目標

可換環 S に対し、semifree 複体の充満 dg 部分圏 Semifree(S) ⊆ Ch(S) の dg nerve として
導来 ∞ 圏 D(S) を定義し、そのホモトピー圏が Mathlib の導来圏 `DerivedCategory (ModuleCat S)` と
圏同値であることを証明する。

| 段 | 主張 | 依存 |
| --- | --- | --- |
| D2 | `HomotopyCategory S (Semifree S) ≌ DerivedCategory (ModuleCat S)` | なし（古典的） |
| D1 | `Semifree S := DGFullSubcategory (Complex S) (complexSemifree S)`、`D(S) := dgNerve S (Semifree S)`、quasicategory | N1・N2 |
| D3 | `HomotopyCategory₂ ((truncation 2).obj D(S)) ≌ DerivedCategory (ModuleCat S)` | N3・D2 |
| D4 | 四角形が ∞ 引き戻し ⟺ A → fib(B ⊕ C → D) が擬同型 | N7・α の A2・A3 |
| D5 | 通常の nerve からの射、関手的離散埋め込み、底変更、H⁰ | D1〜D4・N5 |
| D6 | 指定四辺の長完全列、heart の充満忠実性、離散対象の特徴づけ | D3〜D5・Mathlib の三角構造 |
| D8 | 完全導来 ∞ 圏 Perf(S) と閉性・引き戻し判定・ホモトピー圏の像 | D2・D3・D4、strictlyPerfectComplex |
| D7 | D(S) の cofiber の普遍性・安定性、D3 の三角同値への昇格 | 完了。cofiber の普遍性、任意四角形の双カルテジアン判定と IsStable。実 suspension 由来の全整数シフト、標準列の三射と cone 三角形の同型、全 distinguished triangle の保存・反映、逆関手・単位・余単位を含む D3 の三角同値 |

semifree を K-projective より優先する理由：cone・シフト・直和・テンソル積・底変更で閉じ、
D(S)^⊗ を対称モノイダル dg 圏の dg nerve として作れる。K-projective 版との同値は後の項目。

## 1. 数学的内容（D2）

- semifree 複体：部分複体の増大列 0 = P(−1) ⊆ P(0) ⊆ … で網羅的、各商 P(n)/P(n−1) が
  微分零の自由複体 ⊕ S⟨k⟩ の直和。
- semifree ⇒ K-projective（Hom^•(P, N) は N が acyclic なら acyclic）：段ごとの帰納と
  telescope の Milnor 列。
- 任意の複体 M に semifree 解像度 P → M（全射な擬同型）がある。
- K-projective どうしの擬同型はホモトピー同値。
- よって H⁰(Semifree(S)) → K(S) → D(S) は充満忠実（K-projective からの Hom は K と D で一致）
  かつ本質的全射（解像度）。

## 2. 既存資産

dg 加群層（`SerrePositivity/DifferentialGraded/`）は一点 dg 圏 `PUnit` 上の加群と複体の橋を
既に持つので、D2 はほぼ転送で済む。

| 宣言 | 場所 | 内容 |
| --- | --- | --- |
| `ringModuleEquivalence : ModuleCategory A PUnit ≌ Complex A` | `Module/Ring.lean` | 一点 dg 圏上の加群と複体の同値（`ringModule`、`ringModuleObjEquiv`） |
| `ModuleSemifreeFiltration`、`moduleSemifree` | `Module/Semifree/Basic.lean` | dg 加群の semifree filtration（`freeSphere` 余積、次数付き分裂、余極限） |
| `exists_semifree_resolution` | `Module/Semifree/Resolution.lean` | 任意の dg 加群の semifree 解像度（全射擬同型） |
| `moduleSemifree_homotopicallyProjective` | `Derived/SemifreeProjective.lean` | semifree ⇒ homotopically projective |
| `ringModule_homotopicallyProjective_iff` | `Module/RingProjective.lean` | 一点 dg 圏上の homotopically projective ⟺ Mathlib `IsKProjective` |
| `isKProjective_iff_homComplex_acyclic` | `Complexes/KProjectiveHom.lean` | `IsKProjective` ⟺ Hom 複体の acyclic 性 |
| `ringModuleQuasiIso_iff` | `Derived/Ring.lean` | 加群の擬同型と複体の擬同型の一致 |
| `complexHomotopyEquivalence : HomotopyCategory A (Complex A) ≌ HomotopyCategory (ModuleCat A) (.up ℤ)` | `Category/ComplexHomotopyComparison.lean` | 主 dg 圏の H⁰ と Mathlib のホモトピー圏 |
| `DGFullSubcategory`、`dgFullSubcategoryInclusion` | `Category/FullSubcategory.lean` | 充満 dg 部分圏（Z⁰・H⁰ で包含は充満忠実） |
| `ringDerivedEquivalence : DerivedModuleCategory A PUnit ≌ DerivedCategory (ModuleCat A)` | `Derived/Ring.lean` | 主導来圏と Mathlib の導来圏 |
| `complexHomotopyRingDerivedIso` | `Perfect/RingHomotopyDerivedComparison.lean` | `HasDerivedCategory.{w}` の扱いの手本 |
| `complexSphere`、`complexDisk`、`complex_quasiIso_of_boundary_lifting` | `Complexes/Cells.lean`、`CellCriterion.lean` | 複体の球面・円板と cell 判定 |
| Mathlib `DerivedCategory.KProjective.Qh_map_bijective`、`quasiIso_iff` | `Algebra/Homology/DerivedCategory/KProjective.lean` | K-projective からの Hom は K と D で一致、K-projective 間の擬同型はホモトピー同値 |

## 3. 工程

配置は `SerrePositivity/InfinityCategories/Derived/`、namespace `SerrePositivity.InfinityCategories`、
集約ファイル `SerrePositivity/InfinityCategories/Derived.lean` をルートに 1 行で追加する。
レーン N のディレクトリ `InfinityCategories/DGNerve/` と `InfinityCategories/README.md` は編集しない。

| 工程 | ファイル | 内容 |
| --- | --- | --- |
| D2a | `Derived/Semifree.lean` | `complexSemifree S : ObjectProperty (Complex S)` を `moduleSemifree S PUnit` の `ringModuleEquivalence` による転送で定義し、展開補題（filtration の各段が複体として何か）を付ける。`complexSphere` との対応 |
| D2b | `Derived/SemifreeKProjective.lean` | `complexSemifree S P → P.IsKProjective`（`moduleSemifree_homotopicallyProjective` と `ringModule_homotopicallyProjective_iff`） |
| D2c | `Derived/SemifreeResolution.lean` | `∀ M : Complex S, ∃ P q, complexSemifree S P ∧ QuasiIso q`（各次数全射も保持。`exists_semifree_resolution S PUnit` と `ringModuleQuasiIso_iff` の転送） |
| D2d | `Derived/SemifreeSubcategory.lean` | `Semifree S := DGFullSubcategory (Complex S) (complexSemifree S)`。`HomotopyCategory S (Semifree S)` から `HomotopyCategory (ModuleCat S) (.up ℤ)` への充満忠実関手（包含と `complexHomotopyEquivalence`） |
| D2e | `Derived/DerivedComparison.lean` | 関手 `HomotopyCategory S (Semifree S) ⥤ DerivedCategory (ModuleCat S)` := D2d ⋙ `Qh`。充満忠実は `Qh_map_bijective`、本質的全射は D2c と「`Q` は擬同型を同型に送る」。`semifreeDerivedEquivalence` |
| D2f | `Derived/DerivedComparisonShift.lean` | 同値のシフトとの両立（`CommShift`）。D4 の三角構造の一致に使う。任意 |
| D2g | `Derived/Checks.lean`、`scripts/audit_derived_infinity.lean` | `HasDerivedCategory.standard` での具体化と公理監査 |
| D2h | `Derived/SemifreeClosure.lean` | `complexSemifree` の閉性：零複体、`complexSphere S n`、シフト、semifree 間の射の mapping cone、余積（有限・任意）。D4 の fiber・cofiber と Perf ⊆ D(S) に使う（2026-10-17 追加） |
| D2i | `Derived/SemifreeTensor.lean` | 任意：semifree ⊗_S semifree は semifree、底変更 − ⊗_S T は semifree を保つ。δ・底変更の関手性に使う（2026-10-17 追加） |
| D1 | `Derived/InfinityCategory.lean` | N1 の完了が dg-nerve.md §5 に記録された後。`derivedInfinityCategory S := dgNerve S (Semifree S)`。quasicategory は N2 の後 |
| D3 | `Derived/HomotopyCategoryComparison.lean` | N3 の後。`HomotopyCategory₂` の同値と D2e の合成 |
| D4 | `Derived/PullbackCriterion.lean` | 標準 fiber 比較射による引き戻し判定。完了 |
| D5a〜d | `Derived/NerveInclusion.lean`、`DiscreteEmbedding.lean`、`BaseChange.lean`、`HZero.lean` | 通常の nerve、離散入力、底変更と H⁰。完了 |
| D6a | `Derived/FiberLongExactSequence.lean` | 引き戻しの四辺による A → B ⊕ C → D（右辺 − 下辺）を distinguished triangle にし、全整数次数の長完全列と H⁰ の射の一致を公開 |
| D6b | `Derived/HeartFullyFaithful.lean` | 加群の離散埋め込み J の Hom 全単射と H⁰ 比較との両立 |
| D6c | `Derived/DiscreteCharacterization.lean` | Hⁱ(x)=0（i≠0）なら h D(S) で x≅J(H⁰x)、同型を表す辺も公開 |
| D8 | `Derived/Perfect.lean` | Perf(S) の充満部分単体集合、quasicategory・各閉性、D4 の判定の制限、h Perf の本質像と U13 の H⁰ との同値。完了 |

## 4. 設計上の決定

- `HasDerivedCategory` は宣言では `[HasDerivedCategory.{w} (ModuleCat.{u} S)]` を変数にし、
  検査では `HasDerivedCategory.standard` を局所 instance にする（`Perfect/RingPerfectRepresentatives.lean` と同じ）。
- `complexSemifree` は転送で定義する。複体レベルの filtration 構造体は、テンソル積や底変更の
  保存を示す段階で必要になったときに追加し、転送定義との同値を証明する。
- 新しい `sorry`・公理・引用は導入しない。dg 層のファイルは編集せず、必要な補題は新規ファイルに置く。

## 5. 受入基準

1. 各ファイルがビルドし、公開宣言は標準 3 公理のみ。
2. docstring は README「Conventions」の形式。
3. 公開宣言名と正確な型はアーカイブへ記録し、検証経緯はコミットメッセージに書く。現在地は冒頭で更新する。
4. 主定理の経路には触れない。
