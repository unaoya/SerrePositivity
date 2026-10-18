# α2b：随伴・局所化・Kan 拡張

作成日：2026-10-18。正本は [infinity-core-F1.md](infinity-core-F1.md) の F1e〜F1g と
[foundations.md](foundations.md) §4。本計画は目標・型・設計・現在地・主要宣言を管理し、
実施の経緯はコミットメッセージに置く。

## 0. 目標と範囲

quasicategory の随伴、反射的局所化、cofinality、点ごとの左右 Kan 拡張を構成する。
Lean は `SerrePositivity/InfinityCategories/F1B/`、namespace は
`SerrePositivity.InfinityCategories`、集約は `InfinityCategories/F1B.lean`。
Core/・F1/・Stable/ は読むだけ。straightening に推移的にも依存しない。
sorry・追加公理・文献入力を使わず、監査で許す公理は
`propext`・`Classical.choice`・`Quot.sound` のみ。

## 1. 原典と工程

| 工程 | 成果 | 原典 | 状態 |
| --- | --- | --- | --- |
| B1 / F1e | 単位・余単位と h Fun の三角恒等式、自然な写像空間対応との特徴づけ、合成、随伴関手の一意性 | Kerodon [Def 6.1.1.1](https://kerodon.net/tag/02CG)、[§6.1.3](https://kerodon.net/tag/02D5)、[§6.1.5](https://kerodon.net/tag/02DM)、[Def 6.2.1.1・Prop 6.2.1.17](https://kerodon.net/tag/02EJ)、[Prop 6.2.6.1](https://kerodon.net/tag/02FV)・[Cor 6.2.6.5](https://kerodon.net/tag/02FX) / HTT §5.2 | 完了（全パラメータの族の前層による自然性の模型） |
| B2 / F1f | 充満部分 ∞ 圏への反射、局所対象、冪等性、局所化の普遍性の型と反射的な場合の構成 | Kerodon [§6.2.2](https://kerodon.net/tag/02F5)、[Cor 6.2.2.26](https://kerodon.net/tag/02FF)、[Def 6.3.1.9・Prop 6.3.1.13](https://kerodon.net/tag/01ME)、[Prop 6.3.3.7](https://kerodon.net/tag/02FY) / HTT §5.2.7 | 完了（同じ宇宙の標的に対する普遍性） |
| B3 / F1g 前半 | right cofinal、Quillen A、A2h の始対象による limit 計算の双対的回収 | Kerodon [Def 7.2.1.1](https://kerodon.net/tag/02N1)、[Thm 7.2.3.1](https://kerodon.net/tag/02NX) / HTT Thm 4.1.3.1 | 進行中（定義・始対象・cofinal ⇒ 弱同値・合成・anodyne 因子分解判定が済、Quillen A は未完） |
| B4 / F1g 後半 | slice の極限による左右 Kan 拡張、h での一意性、各点の存在、関手全体への組み立て | Kerodon [Notation 7.3.1.1・Def 7.3.1.2](https://kerodon.net/tag/02Y7)、§7.3.5 / HTT §4.3 | 未着手 |
| B5 | nerve による古典随伴・Kan 拡張の回収と監査 | 上記と通常の圏の随伴・Kan 拡張 | 未着手（監査スクリプトは稼働中） |

## 2. 設計上の決定

- 随伴は `SSet.QCat.strictBicategory` 上の双圏随伴。二胞体は
  h((ihom X).obj Y) の射であり、hX と hY の間の随伴で代用しない。
  A1c の `homotopyNatTrans` と A3a の `FunctorIso` に接続する。
- 写像空間は右 `pinchedHom` を使い、中間模型に区間写像空間を使う。
  各点で独立に選んだ同値だけや π₀ の全単射だけを自然な対応と扱わない。
  同値条件は各点の実際のホモトピー逆の存在で述べる。
- 自然性の入力は、全ての単体集合パラメータ A と非定値端点図式 a,b の
  ホモトピー族の集合値前層の、端点を保つ通常の自然変換とする。
  その型と coherent 矢印空間の比較との厳密な全単射を証明した。
  各点の比較はこの同じ自然変換の作用から回収する。
  全パラメータの Hom 全単射は追加仮定ではなく、各点の同値性からの帰結である。
- 空間値 Hom 関手自体は正本の別レーン F1h に属し、left fibration の
  straightening で構成する工程である。その空間値二変数 ∞ 関手の自然変換と
  今回の模型との比較定理は未形式化で、証明済みとは主張しない。
  B1 は上の明示した族の前層の模型で構成・判定・自然性を完結している。
- 反射は頂点条件 P の張る全部分複体への包含の左随伴として指定する。
  余単位の可逆性・冪等性・局所化の普遍性をフィールドに加えない。
  P の同型不変性は不要。局所対象は単位成分の可逆性で定義し、包含の本質的な像と同定する。
- 局所化は W を反転する関手の全部分 ∞ 圏への前合成の同値で述べる。
  標的は元の単体集合と同じ宇宙 u の quasicategory。
  一般の C[W⁻¹] の存在は F2 に委ね、ここでは反射の場合だけを構成する。
- right cofinal は colimit を計算する向き。始対象による limit 計算は双対の
  left cofinal と対応する。Quillen A の fiber 条件は弱可縮性であり、
  Kan 性や ∞ 圏としての可縮性へ強めない。
- Kan 拡張では点ごとの slice 極限と関手全体への組み立てを区別する。
  後者は A6 の関手 ∞ 圏の極限 API を確認してから接続する。
- 各保存単位で集約ビルド、公理監査、推移的 import の検査を行う。
  監査は生成宣言を含む F1B の全宣言を宣言元モジュールで抽出し、
  読み込んだリポジトリ内の straightening 系モジュールを拒否する。

## 3. 現在地と証明の接続

### B1：完了

`QCatAdjunction F G` は単位・余単位と二つの三角恒等式を保持する。
h Fun の表示全単射、A1c の自然変換との一致、随伴の合成と左右随伴の
h Fun での一意性を証明済み。

随伴から、パラメータ付き adjunct 全単射、その二変数・パラメータ自然性、
区間写像空間の比較と実際のホモトピー逆を構成した。
`PinchedInterval` の模型比較で右 pinched 模型へ移し、
`pinchedMap_naturality_left/right` を実際のホモトピーで公開している。

指定単位版は `UnitMappingSpaceCondition η` と
「η を単位とする随伴が存在すること」の同値として証明した。
各点の比較の同値性 → comma の始対象性 → 相対初期境界充填 → 自然な余単位比較
→ 同じ正方形から右三角恒等式、という経路を使う。
左 zigzag は各点の単射性から可逆で、右三角恒等式から冪等になるため恒等である。
**各点の等式から h Fun 全体の等式を直接推論しない。**

単位を入力に含めない `MappingArrowComparison` は F(x)→y の全矢印の空間から
x→G(y) の comma 空間への、両端を保つ一つの単体的な射である。
恒等矢印の族の像から単位を抽出する。
min(t,s) による始域固定の伸長の像の正方形により、任意の非定値端点の族への作用は
抽出単位と G による後合成の合成を表す。
各点の比較は標準単位比較に実際にホモトピックとなるので、
各点の同値条件だけで指定単位版へ渡せる。
逆方向では矢印空間全体で単位と普遍矢印を一度合成して比較を作り、
恒等矢印への制限で元の単位を h Fun 全体で回収する。

`NaturalMappingFamilyComparison` は非定値端点のホモトピー族の前層の自然変換。
`mappingArrowNaturalFamilyEquiv` が上の矢印比較との厳密な全単射を与え、
`transformation_app/transformation_h/intervalMap_family_h` が元の自然変換の作用を回収する。
`qcat_nonempty_adjunction_iff_exists_naturalPinchedFamilyComparison` が、この自然性の型での
各点の pinched 同値による随伴判定の両方向を与える。

### B2：完了

`ReflectiveSubcategory X P` は全部分複体への reflector と包含への随伴を保持する。
`localization` は reflector に包含を続けた自己関手 L、`unit` はその随伴単位。
`IsLocal x` は単位成分の可逆性であり、`isLocal_iff_essentialImage` は
包含の本質的な像との同値を与える。局所性は hX の同型で不変で、反射像は局所対象。
`localSubcomplex` は局所対象の全部分 ∞ 圏で、反射はそこへ厳密に持ち上がる。

`fullSubcomplexPinchedIso` は両端を部分圏に持つ pinched 単体を同じ単体のまま持ち上げる
写像空間の厳密な同型で、quasicategory 性や P の同型不変性は不要。
内部 Hom の全部分複体表示を使うと、任意のパラメータの関手 ∞ 圏でも包含は充満忠実。
通常の Hom 圏の後合成随伴と充満忠実な右随伴の定理から、元の余単位は可逆となる。
その余単位を前後合成して `idempotentIso : FunctorIso (L≫L) L` を構成した。
三角恒等式から、包含上の単位、反射で写した単位、反射像上の単位も自然同型になる。

`Localization.lean` の `IsLocalization F W` は、W を反転し、各 quasicategory E について
前合成が `Fun(D,E)` と W を反転する `Fun(X,E)` の全部分 ∞ 圏の同値を与える条件。
これは Kerodon Prop 6.3.1.13(2) の型であり、任意の W に対する存在宣言ではない。
反射では W を `invertedEdges reflector` と取る。
反射に沿う前合成の逆を包含に沿う制限として構成し、一方の合成は余単位から同型にする。
他方では反射が全単位成分を反転することを使い、W を反転する関手族の上で
単位による前合成を自然同型にする。全部分複体の関手圏での充満忠実性により同型を戻す。
`localizationPrecompositionEquivalence` は明示的な逆射と両合成の同型を保持し、
`ReflectiveSubcategory.isLocalization` が反射的な場合の普遍性を結論する。
これは Kerodon Prop 6.3.3.7 の反射的な場合に沿う構成である。

`reflectionMappingEquivalence` は部分圏の対象を標的とする写像空間の普遍性も与える。
その選んだ順射を X 内での単位による前合成の具体的な射と照合する補助 API は未追加。
B2 の局所対象・冪等性・局所化の普遍性の定理はこの補助 API を仮定せず成立する。

### B3：進行中

`cofinalFunctorSpace/pre` は内部 Hom の頂点 fiber と前合成による相対関手空間。
F1 の同じ構成は `LeftFiberKan` 経由で `LeftUnstraightening` を import するため、
一般の fiber・前合成・全境界の充填だけを F1B 内に再構成し、import を狭めた。
`IsLeftCofinal`・`IsRightCofinal` は Kerodon Def 7.2.1.1 の相対関手空間による条件。
元の底上の left/right fibration を全て検査し、制限写像そのものの
`IsSimplicialHomotopyEquivalence` を要求する。始域・標的の quasicategory 性や単射性は不要。
`cofinalFunctorPre_isSimplicialHomotopyEquivalence_of_leftAnodyne` は任意の底図式にも適用できる。
そこから left anodyne ⇒ left cofinal と、通常の圏の始対象の頂点包含の left cofinality を得た。
`initialRestriction_isQCatEquivalence` は二宇宙版 A2h の同じ制限写像に逆を与える。
一般の cofinality による極限不変性、およびその双対との統一は未完了。

弱同値は [Kerodon §3.1.7](https://kerodon.net/tag/00U1) に従い、全 Kan 標的 Z に対する
π₀ Fun(-,Z) の全単射で定義した。`IsWeaklyContractible` は点への射の弱同値性であり、
元の単体集合に Kan 性を要求しない。恒等・合成・二対三則、弱可縮性の移送を証明した。
写像空間の π₀ の等式から実際のホモトピーを回収することで、Kan 複体間の弱同値から
ホモトピー逆を構成した。逆方向は元の二対象の Kan 性なしに成立する。
これにより Prop 3.1.7.13 の判定と、既存 `IsContractibleKan` から弱可縮性への十分性を得た。
`IsWeakHomotopyEquivalence.precompose_kan` は
[Prop 3.1.7.17](https://kerodon.net/tag/03PJ) の写像空間自体の同値を与える。
各パラメータ K に対して Z^K を検査し、二重内部 Hom の交換で
K→Fun(B,Z) の後合成の π₀ の全単射へ移す。全パラメータの全単射から、
同じ逆射と実際の両ホモトピーを構成する。元の射の始域・終域の Kan 性は不要。
`isWeakHomotopyEquivalence_iff_precompose_kan` はこの判定の両方向。

right 側では左ホーンと境界の pairing を反転し、右ホーンと任意の単射の
pushout-product の right anodyne 性を得た。内部 Hom と相対内部 Hom の
right fibration 性、相対関手空間の Kan 性、right anodyne な制限の
trivial Kan fibration 性へ移し、`isRightCofinal_of_rightAnodyne` を証明した。
これらも元の底上の射・元の制限写像についての定理である。
`cofinalProductTestIso` は、Kan 標的 Z と底 B の積の射影への相対関手空間を
通常の内部 Hom と厳密に同定し、`cofinalProductTestIso_pre` は元の制限写像と可換。
この射影は左右の fibration なので、同じ構成から
`IsLeftCofinal.isWeakHomotopyEquivalence`・`IsRightCofinal.isWeakHomotopyEquivalence`
（[Prop 7.2.1.5(1)](https://kerodon.net/tag/02N5)）を得た。元の射の両端は任意の単体集合。

`cofinalFunctorBaseChangeIso` は引き戻した fibration への相対関手空間と
合成した底図式への相対関手空間との厳密な同型で、制限写像との可換性も持つ。
これから cofinality を任意の底図式に適用する `restrictDiagram`、合成 `comp`、
最初の因子と合成から後の因子を得る `cancel_left` を左右とも証明した。
`isInitialVertex_functorVertex_of_pointwise` は相対始点境界充填から、
点ごとに始対象となる関手の始対象性を得る。定値始対象関手から恒等関手への辺を
uncurry して実際の収縮を作り、`IsInitialVertex.isWeaklyContractible` を得た。
終対象の場合の収縮は逆向きなので、Kan 標的への前合成で自然同型を逆にして
`IsTerminalVertex.isWeaklyContractible` を証明した。
これは [Kerodon Cor 4.7.3.23](https://kerodon.net/tag/02P2) の内容。
`sliceUnder_isWeaklyContractible` は既存の恒等余錐の始対象性（Stable.IdentityCocone）に適用し、
Quillen A の必要性で使う D_{d/} の弱可縮性を得る。slice 自体の Kan 性は主張しない。

左右のホーンを小さい族に同定し、有限表示可能性から可算小対象論法を適用した。
`exists_leftAnodyne_leftFibration_factorization`・`exists_rightAnodyne_rightFibration_factorization`
は、任意の射の anodyne な単射と fibration への厳密な因子分解を与える。
`IsLeftCofinal.exists_anodyne_fibration_factorization` と right 版では、
cofinal な射の右因子も cofinal と分かる。

`nonempty_cofinalSectionHomotopy` は p 自身による相対関手の制限の同値から、
厳密な切断と、恒等射と p≫sectionMap の間の**両方向の底上のホモトピー**を構成する。
同じ相対 Kan 空間の同型とその逆の代表辺を使い、底への像を時間に定値な射として保持する。
`fiberContraction` はこのホモトピーを各頂点 fiber へ厳密に持ち上げる。
right fibration の場合は可縮な Kan fiber の Core の判定へ渡し、
left fibration の場合は逆向きのホモトピーと left prism で切断による充填の境界を補正する。
`IsLeftCofinal.trivialKanFibration`・`IsRightCofinal.trivialKanFibration` は
[Cor 7.2.1.14](https://kerodon.net/tag/02ND) の (1)⇒(3)・(2)⇒(3) を与える。

逆方向では、`cofinalFunctorOverPre` が底上の射の前合成を型の移送なしに保持する。
`cofinalFunctorOverPreHomotopy` は底を固定したホモトピーを相対関手空間の
前合成の実際のホモトピーへ移す。Kan 性を要求しない一般のパラメータ付き評価の構成である。
`CofinalSectionHomotopy.restriction_isSimplicialHomotopyEquivalence` は、
切断による前合成を逆とし、一方の合成は厳密に、他方は底上の逆向きの収縮で戻す。
trivial Kan fibration では切断と両方向の底上の収縮が存在するので、
`isLeftCofinal_of_trivialKanFibration`・right 版により Cor 7.2.1.14 の逆方向も得た。
`trivialKanFibration_iff_leftFibration_and_isLeftCofinal` と right 版が全体の判定。

これを因子分解に適用して、`exists_anodyne_trivialKan_factorization` を左右とも得た。
さらに、両因子の cofinality の合成から逆方向も得た。
`isLeftCofinal_iff_exists_anodyne_trivialKan_factorization` と right 版は
[Cor 7.2.1.15](https://kerodon.net/tag/02NE) の因子分解による特徴づけを両方向に証明する。
単射の場合は trivial Kan 右因子の持ち上げで左因子から左持ち上げ性を戻し、
`leftAnodyneExtensions_iff_mono_and_isLeftCofinal` と right 版を得た。
これは [Prop 7.2.1.3](https://kerodon.net/tag/02N3) の単射性を含む全体の判定。

Quillen A 本体、cocartesian fibration に沿う cofinality の pullback 安定性、
Kan な底への弱同値 ⇒ cofinal の逆方向（Prop 7.2.1.5(2)）、
left/right cofinality の opposite による比較は未完了。

### 次の工程

B3 の cofinality の pullback 安定性を証明し、弱可縮な coslice の判定による Quillen A へ進む。
B4 の各点の Kan 拡張、B5 の古典 nerve に戻る検査も未完了。
全体の α2b 目標は継続中。

対象ビルド2209 jobs、公理監査1951宣言（標準三公理のみ）が成功。
推移的 import のリポジトリ内540モジュールに straightening 依存なし。

## 4. 主要宣言

すべて namespace `SerrePositivity.InfinityCategories`。全宣言のチェックは監査スクリプトに保持する。

| 宣言・群 | 型・役割 | 状態 |
| --- | --- | --- |
| `QCatAdjunction`・`qcatCellEquiv`・`qcatHomFunctor` | QCat の随伴と h Fun の二胞体の表示 | 済 |
| `qcatCellOfHomotopy`・`functorCellToNatTrans_homotopy`・`qcatCellOfHomotopy_toNatTrans` | A1c の自然変換との一致 | 済 |
| `QCatAdjunction.comp`・`rightAdjointFunctorIso/leftAdjointFunctorIso` | 合成・左右随伴の一意性 | 済 |
| `QCatAdjunction.homEquiv`・`QCatFunctorHomCorrespondence.adjunctionEquiv` | 全パラメータの自然な h Fun の Hom 対応 | 済 |
| `intervalFamilyEdgeEquiv`・`intervalFamilyHom_surjective`・`intervalFamilyHom_eq_iff_homotopy` | 区間族・関手辺・h Fun の Hom と実際のホモトピー | 済 |
| `PinchedInterval.comparison_isQCatEquivalence`・`QCatAdjunction.pinchedHomEquivalence` | 模型比較と実際の pinched 写像空間の同値 | 済 |
| `QCatAdjunction.pinchedMap_naturality_left/right` | 二変数自然性の実際のホモトピー | 済 |
| `UnitMappingSpaceCondition`・`unitMappingSpaceCondition_iff_interval` | 各点の標準単位比較の同値条件と模型の交換 | 済 |
| `UnitMappingSpaceCondition.unitCommaInitialCondition`・`UnitCommaInitialCondition.initialBoundaryLifting`・`UnitMappingSpaceCondition.nonempty_counitData` | 各点の条件から comma 比較へ | 済 |
| `UnitCommaCounitData.right_triangle`・`UnitMappingSpaceCondition.left_triangle` | 同じ比較から h Fun 全体の三角恒等式 | 済 |
| `qcatAdjunctionOfUnitMappingSpaceCondition`・`qcat_exists_adjunction_unitHom_iff_unitMappingSpaceCondition` | 指定単位の局所判定の両方向 | 済 |
| `UnitMappingSpaceCondition.qcatUnitHomMap_bijective` | 全パラメータの Hom 全単射を帰結として回収 | 済 |
| `leftMappingArrow`・`leftMappingArrowLift/Homotopy`・`leftMappingArrowPrefixPath` | 全矢印の空間、族の表示、始域固定の伸長 | 済 |
| `MappingArrowComparison.unitHom/mapHomotopy_hom`・`intervalMap_unitIntervalMap_homotopy` | 単位抽出、全族の合成公式、標準比較との照合 | 済 |
| `MappingArrowComparison.adjunctionOfPointwiseEquivalence`・`ofUnitHom_unitHom` | 比較からの随伴と単位からの比較の回収 | 済 |
| `MappingArrowComparison.pinchedMapAdjunctionIso/pinchedMap_naturality_left/right` | 元の比較の保持と自然性 | 済 |
| `LeftMappingFamily/RightMappingFamily`・`leftMappingFamilyPresheaf/rightMappingFamilyPresheaf` | 全端点の族の集合値前層 | 済 |
| `NaturalMappingFamilyComparison`・`mappingArrowNaturalFamilyEquiv` | 自然な族の比較と矢印比較の厳密な全単射 | 済 |
| `NaturalMappingFamilyComparison.transformation_app/transformation_h/intervalMap_family_h` | 元の自然変換の成分の厳密な回収 | 済 |
| `qcat_nonempty_adjunction_iff_exists_naturalPinchedFamilyComparison` | 自然な族の比較の各点の pinched 同値による随伴判定 | 済 |
| `fullSubcomplexPinchedIso`・`isFullyFaithful_fullSubcomplexOnVertices_ι` | 全部分複体の写像空間の同型と充満忠実性 | 済 |
| `isFullyFaithful_fullSubcomplexFunctorInclusion`・`fullSubcomplexFunctorInclusionHoFullyFaithful` | 任意の関手圏でも包含の後合成は充満忠実 | 済 |
| `ReflectiveSubcategory`・`IsReflectiveSubcategory`・`localization/unit/IsLocal` | 選んだ反射、その単位、局所対象 | 済 |
| `ReflectiveSubcategory.reflectionMappingEquivalence` | 部分圏の対象への反射の写像空間の普遍性 | 済 |
| `bicategoryPostcompAdjunction`・`bicategory_counit_isIso_of_postcomp_fullyFaithful` | 各 Hom 圏の通常の随伴と余単位の可逆性 | 済 |
| `qcatPostcompFullyFaithfulOfHo`・`QCatAdjunction.counitHom_isIso_of_postcompFullyFaithful` | h Fun の充満忠実性を双圏へ接続 | 済 |
| `ReflectiveSubcategory.counitIso/idempotentIso`・`unitOnInclusionIso/reflectedUnitIso/unitOnLocalizationIso` | 余単位・冪等性・単位の制限と像の自然同型 | 済 |
| `functorCellToNatTrans_app_eq_evaluate`・`functorHomEvaluate_precomp/naturality` | 成分評価の自然変換との一致とパラメータ整合 | 済 |
| `ReflectiveSubcategory.isLocal_iff_essentialImage/isLocal_of_vertexIso/isLocal_localization` | 局所対象の本質的な像による特徴づけ・同型不変性 | 済 |
| `ReflectiveSubcategory.localSubcomplex/localizationToLocalSubcomplex_ι` | 局所対象の ∞ 圏と反射の厳密な持ち上げ | 済 |
| `InvertsEdges`・`invertingFunctors`・`localizationPrecomposition_ι`・`IsLocalization` | 局所化の普遍性の型と前合成の因子化 | 済 |
| `functorIsoRestrictedPrecompositionOfHomotopy` | 選んだ関手族上でだけ可逆となる前合成作用 | 済 |
| `ReflectiveSubcategory.unitComponent_mem_invertedEdges/invertingUnitPrecompositionIso` | 反射による単位の反転と反転関手族上の自然同型 | 済 |
| `ReflectiveSubcategory.localizationRestriction/localizationPrecompositionEquivalence/isLocalization` | 包含による明示的な逆と反射的局所化の普遍性 | 済 |
| `cofinalFunctorSpace/pre`・`cofinalFunctorPre_id/comp/trivialKanFibration` | straightening を import しない相対関手空間・制限・left anodyne による充填 | 済 |
| `IsLeftCofinal/IsRightCofinal`・`isLeftCofinal_id/isRightCofinal_id` | 元の底上の fibration への関手の制限による cofinality と恒等例 | 済 |
| `cofinalFunctorPre_isSimplicialHomotopyEquivalence_of_leftAnodyne`・`isLeftCofinal_of_leftAnodyne` | 任意の底図式の制限と left anodyne の十分性 | 済 |
| `nervePoint_isLeftCofinal`・`initialRestriction_isQCatEquivalence` | 二宇宙版 A2h と極限の向きとの接続 | 済 |
| `IsWeakHomotopyEquivalence/IsWeaklyContractible`・`comp/cancel_left/cancel_right/weaklyContractible_iff` | Kan 標的のホモトピー類による弱同値・二対三則・弱可縮性 | 済 |
| `nonempty_vertexIso_of_piZero_eq`・`functorVertex_piZero_eq_iff_homotopy` | Kan 複体の成分の等式から実際の同型・ホモトピーへの変換 | 済 |
| `functorIsoPrecompositionOfHomotopy_kan`・`IsSimplicialHomotopyEquivalence.isWeakHomotopyEquivalence` | 任意の単体集合のホモトピー逆は弱同値 | 済 |
| `IsWeakHomotopyEquivalence.isSimplicialHomotopyEquivalence`・`isWeakHomotopyEquivalence_iff_isQCatEquivalence`・`isWeakHomotopyEquivalence_iff_isSimplicialHomotopyEquivalence` | Kan 複体間の Whitehead 判定 | 済 |
| `IsPrecompositionEquivalence.isWeakHomotopyEquivalence`・`IsQCatEquivalence.isWeakHomotopyEquivalence` | 圏同値から弱同値への接続 | 済 |
| `IsContractibleKan.isWeaklyContractible`・`isContractibleKan_terminal/isWeaklyContractible_terminal` | 全境界の充填による十分性と一点の例 | 済 |
| `isSimplicialHomotopyEquivalence_of_postcomposition_piZero_bijective` | 全パラメータからのホモトピー類の全単射による Kan 複体の判定 | 済 |
| `IsWeakHomotopyEquivalence.precompose_kan`・`isWeakHomotopyEquivalence_iff_precompose_kan` | 全 Kan 標的への写像空間自体のホモトピー同値による弱同値判定 | 済 |
| `cofinalRightAnodyne_unionProd`・`cofinalRightAnodyne_pushoutObjObj_horn/left/right` | 右ホーンと単射の積・一般の right anodyne の積 | 済 |
| `cofinalIhom_map_rightFibration`・`cofinalRightFibration_pullbackObjObjπ` | 内部 Hom と相対内部 Hom の right fibration 性 | 済 |
| `cofinalTrivialKanFibration_relativeHom_of_rightAnodyne`・`cofinalFunctorSpace_right_kanComplex`・`cofinalFunctorPre_trivialKanFibration_of_rightAnodyne` | right 側の相対関手空間の Kan 性と制限の全境界充填 | 済 |
| `cofinalFunctorPre_isSimplicialHomotopyEquivalence_of_rightAnodyne`・`isRightCofinal_of_rightAnodyne` | right anodyne な射の right cofinality | 済 |
| `cofinalProductProjection_hasLiftingProperty_horn`・`cofinalProductProjection_leftFibration/rightFibration` | Kan 複体との積の射影を左右の検査対象にする | 済 |
| `cofinalProductTestIso/pre`・`cofinalProductTest_pre_isSimplicialHomotopyEquivalence` | 相対関手空間と通常の内部 Hom の厳密な同型・元の前合成との整合 | 済 |
| `IsLeftCofinal.isWeakHomotopyEquivalence`・`IsRightCofinal.isWeakHomotopyEquivalence` | 任意の単体集合の cofinal な射の弱同値性 | 済 |
| `cofinalFunctorCurry/Uncurry`・`cofinalFunctorUncurry_projection/curry/injective/naturality`・`cofinalFunctorPre_uncurry` | 相対関手空間への族と底上の図式の族の対応・制限との整合 | 済 |
| `cofinalFunctorBaseChangeForward/Backward/Iso`・`cofinalFunctorBaseChangeIso_pre` | 引き戻した射への相対関手空間と合成図式への相対関手空間の同型・制限との整合 | 済 |
| `IsLeftCofinal.restrictDiagram/comp/cancel_left`・`IsRightCofinal.restrictDiagram/comp/cancel_left` | 任意の底図式の検査・cofinality の合成と最初の因子の消去 | 済 |
| `isInitialVertex_functorVertex_of_pointwise` | 関手単体集合の点ごとの始対象性 | 済 |
| `isWeakHomotopyEquivalence_of_reverseHomotopyInverse` | 恒等から合成への向きの収縮も Kan 標的で弱同値を与える | 済 |
| `IsInitialVertex.terminalFrom_isSimplicialHomotopyEquivalence`・`IsInitialVertex.isWeaklyContractible`・`IsTerminalVertex.isWeaklyContractible` | 始対象・終対象を持つ単体集合の弱可縮性 | 済 |
| `sliceUnder_isWeaklyContractible` | 恒等余錐の始対象性から D_{d/} の弱可縮性 | 済 |
| `cofinalLeftHornFamily/cofinalRightHornFamily`・各 `_eq/_isSmall/_isCardinalForSmallObjectArgument/_hasSmallObjectArgument/_llp_rlp_le_monomorphisms` | 左右ホーンの小対象論法と単射性 | 済 |
| `exists_leftAnodyne_leftFibration_factorization`・`exists_rightAnodyne_rightFibration_factorization` | 任意の射の左右 anodyne な単射と左右 fibration への厳密な因子分解 | 済 |
| `IsLeftCofinal.exists_anodyne_fibration_factorization`・`IsRightCofinal.exists_anodyne_fibration_factorization` | cofinal な射では fibration 側も cofinal となる還元 | 済 |
| `cofinalFunctorVertex`・`exists_cofinalFunctorVertex` | 相対関手空間の頂点を厳密な底上の射で表す | 済 |
| `CofinalSectionHomotopy`・`nonempty_cofinalSectionHomotopy`・`IsLeftCofinal.nonempty_sectionHomotopy`・right 版 | 切断と両方向の実際の底上のホモトピーの構成 | 済 |
| `CofinalSectionHomotopy.fiberPoint/fiberContraction/fiber_isContractibleKan` | fiber の基点・収縮・可縮 Kan 性への接続 | 済 |
| `CofinalSectionHomotopy.trivialKanFibration_of_leftFibration/of_rightFibration`・`IsLeftCofinal.trivialKanFibration`・right 版 | cofinal な左右 fibration の全境界充填 | 済 |
| `IsLeftCofinal.exists_anodyne_trivialKan_factorization`・right 版 | cofinal な射の anodyne な単射と trivial Kan fibration への因子分解 | 済 |
| `cofinalLlp_of_mono_trivialKan_factorization`・`IsLeftCofinal.leftAnodyneExtensions`・right 版・`isLeftCofinal_iff_leftAnodyne_of_mono`・right 版 | cofinal な単射の左右 anodyne 性 | 済 |
| `cofinalMono_of_leftAnodyne`・right 版・`leftAnodyneExtensions_iff_mono_and_isLeftCofinal`・right 版 | 単射性を含む Prop 7.2.1.3 の全体の判定 | 済 |
| `cofinalFunctorOverPre/ι/id/comp`・`cofinalFunctorOverPreHomotopy` | 底上の射・ホモトピーの相対関手空間への前合成作用 | 済 |
| `CofinalSectionHomotopy.restriction_isSimplicialHomotopyEquivalence/isLeftCofinal/isRightCofinal` | 底上の収縮による元の制限写像の実際のホモトピー逆 | 済 |
| `nonempty_cofinalSectionHomotopy_of_trivialKanFibration`・`isLeftCofinal_of_trivialKanFibration`・right 版 | 任意の trivial Kan fibration の切断・底上の収縮・左右 cofinality | 済 |
| `trivialKanFibration_iff_leftFibration_and_isLeftCofinal`・right 版 | Cor 7.2.1.14 の三条件の同値 | 済 |
| `isLeftCofinal_iff_exists_anodyne_trivialKan_factorization`・right 版 | Cor 7.2.1.15 の anodyne・trivial Kan 因子分解による特徴づけ | 済 |
| B3 の Quillen A・B4〜B5 | §1 の残る工程 | 未完了 |
