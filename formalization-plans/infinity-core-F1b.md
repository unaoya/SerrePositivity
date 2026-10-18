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
| B3 / F1g 前半 | right cofinal、Quillen A、A2h の始対象による limit 計算の双対的回収 | Kerodon [Def 7.2.1.1](https://kerodon.net/tag/02N1)、[Thm 7.2.3.1](https://kerodon.net/tag/02NX) / HTT Thm 4.1.3.1 | 完了（左右の Quillen A と二宇宙版 A2h の同じ制限写像の回収） |
| B4 / F1g 後半 | slice の極限による左右 Kan 拡張、h での一意性、各点の存在、関手全体への組み立て | Kerodon [Notation 7.3.1.1・Def 7.3.1.2](https://kerodon.net/tag/02Y7)、Variant 7.3.1.5、§7.3.5 / HTT §4.3 | 進行中（指定自然変換の比較錐、各点の値・一意性、左右比較錐の選択不変性、左右の指定自然変換の h 不変性、h Fun の射への降下） |
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

### B3：完了

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

`leftFibration_lift_fixed_prism` は、任意の単射部分上を全時間で固定し、
時刻零から底の prism を left fibration に持ち上げる。
`rightAnodyneExtensions_of_fixed_terminal_homotopy` は、単射とその retraction、
部分を固定した恒等射から retraction 合成へのホモトピーから right anodyne 性を得る。
証明は終点ホーンと単射の pushout-product の arrow retract を明示する。
これにより、任意の定値族を固定する頂点への収縮を持つ底では、
`leftFibration_terminalFiber_rightAnodyne_of_fixed_contraction` が fiber 包含の
right anodyne 性を与える。標準単体の最後の頂点への収縮に適用した
`leftFibration_terminalFiber_rightAnodyne` と、頂点 fiber と通常の引き戻しの厳密な同型により、
`leftFibration_terminalPoint_pullback_rightAnodyne`・`..._isRightCofinal` を得た。
これは [Kerodon Example 7.2.3.12](https://kerodon.net/tag/02NX) の
left fibration・標準単体の場合である。一般の cocartesian fibration や
right anodyne な射の引き戻しの安定性は、これだけからは従わない。
`cofinalLastHornContraction` は最後以外の欠けた頂点が保たれることを検査し、
収縮を外側右ホーンへ制限する。両端と全ての終点定値族の固定を証明した。
`cofinalVertexFiberBaseChangeIso` は引き戻し前後の対応する fiber の厳密な同型で、
全空間への射影と両立する。`isRightCofinal_pullback_fst_of_vertexFibers` により、
二つの fiber 包含の cofinality から第一射影の cofinality を得る。
この比較とホーン・標準単体の収縮により、
`leftFibration_lastHorn_pullback_isRightCofinal/rightAnodyne` を証明した。
内側ホーンを含む全ての右ホーンについても、終点を固定する**二段の**収縮を構成した。
第一段の頂点列は j→max(j,k) で、k 以外の欠けた頂点が保たれる。
第二段は max(j,k)→last で、全ての出力が k 以上なので零が欠けたままである（k ≠ 0）。
二つの prism を単一の区間の射と同一視しない。
`rightFibration_lift_fixed_prism` と
`rightAnodyneExtensions_of_fixed_terminal_homotopies` は、任意の right fibration に
対する持ち上げ問題を終端から二段の prism に沿って戻して解く。
`leftFibration_terminalFiber_rightAnodyne_of_two_fixed_contractions` が
二段の底の収縮を終点 fiber を固定して持ち上げる。
これに `cofinalRightHornRaise/Finish` の両端・接続・定値族の固定の式を渡し、
`leftFibration_rightHorn_pullback_isRightCofinal/rightAnodyne` を証明した。
この定理は単射ごとの cofinality 判定を使い、Quillen A を前提としない。
一般の right anodyne な射への拡張では、通常の slice 圏の随伴を使う経路を採る。
`cofinalRightFibration_of_over_lifting` は通常の slice 内の右ホーンで検査した持ち上げ性を
元の right fibration 性へ戻す。`cofinalRightAnodyne_of_over_lifting` は、検査する右辺を
下辺へ引き戻すことで、slice 内の right fibration に対する持ち上げ性を元の right anodyne 性へ戻す。
`cofinalRightAnodyne_leftAdjoint_of_horns` は、通常の slice 間の左随伴が右ホーンを
right anodyne に送れば任意の right anodyne な射も保つことを証明する。
証明では右随伴が right fibration を保つことを生成元と持ち上げの随伴対応から先に得る。
`cofinalOverPullback_map_isPullback` で slice の引き戻し関手の射が引き戻し正方形をなすことを示し、
`leftFibration_overPullback_rightHorn_rightAnodyne` で元の全右ホーンの結果を適用した。

`leftFibration_overPullback_rightAnodyne_of_isLeftAdjoint` と
`leftFibration_pullback_rightAnodyne_of_isLeftAdjoint` の一般圏論の仮定は解消済み。
`cofinalOverArrowEquiv` は小さい OverArrows と Yoneda 射からの通常の slice の Hom を同定する。
引き戻し随伴の Hom 対応を通して各 fiber の全単射を得て、その作用が第一射影であることを示した。
二変数で自然性を検査した `cofinalPresheafPullbackRestrictionIso` により、slice の前層表示の下で
通常の引き戻しは制限関手に対応する。通常の右 Kan 拡張を右随伴とする制限関手の随伴から、
`cofinalPresheafPullback_isLeftAdjoint` を得た。∞ 圏の Kan 拡張や straightening は使わない。

Mathlib の slice の前層表示は Hom と値の宇宙が一致する形なので、まず
`AsSmall.{u} SimplexCategory` に添字圏を移す。
`cofinalOverMapPostIso` と map・pullback の随伴を共役し、右随伴の一意性を使う
`cofinalPullback_isLeftAdjoint_of_equivalence` により元の単体集合へ戻す。
`cofinalSSetPullback_isLeftAdjoint` は任意の `SSet.{u}` の射 p に成立し、fibration 性も不要。
宇宙を零へ固定せず、追加公理や「依存積がある」という入力も置かない。

これにより `leftFibration_overPullback_rightAnodyne`・
`leftFibration_pullback_rightAnodyne` は一般の right anodyne な射に対する無条件の引き戻し保存を与える。
閉包を生成する pushout・余極限を個別に仮定せず、持ち上げ性そのものを随伴で移す証明である。
right cofinal な射の right anodyne・trivial Kan 因子分解の各因子を引き戻し、
引き戻しの貼合せ同型で第一射影を戻すと `leftFibration_pullback_isRightCofinal` を得る。
これは Kerodon Prop 7.2.3.10 の left fibration の場合であり、一般の cocartesian fibration 版は未完。

`IsRightCofinal.cosliceProjection_isRightCofinal` は、coslice 射影の left fibration 性に適用した結果。
`IsRightCofinal.coslice_isWeaklyContractible` は、この射影の弱同値性で恒等余錐を持つ coslice の
弱可縮性を戻し、Quillen A の **right cofinality 側の必要性**を与える。
標的 B だけを quasicategory とし、元の始域 A と引き戻した coslice の Kan 性は要求しない。

`IsWeaklyContractible.isContractibleKan` は Kan 複体に限って弱可縮性を全境界充填へ移す。
全体で弱可縮性の定義を強めず、終対象への弱同値に Whitehead 判定を適用する。
`rightFibration_trivialKanFibration_of_weaklyContractible_fibers` がこの判定を Kan fiber に使う。

`cofinalPointJoinPrism` は点との join の円柱比較から、左包含に定値な端点と右包含を持つ prism を与える。
`IsInitialVertex.exists_fixed_coslice_section` は始対象下の coslice 射影の trivial Kan 性を使い、
指定頂点で恒等錐になる切断を選ぶ。これを uncurry して円柱を合成すると
`IsInitialVertex.exists_fixed_initial_prism` が定値始対象から恒等射への収縮を与える。
任意のパラメータの始対象への定値族を厳密に固定することも検査した。

この収縮を right fibration の終端から持ち上げ、fiber を全時間で固定すると
`rightFibration_initialFiber_isSimplicialHomotopyEquivalence` を得る。
これは bottom の Kan 性なしに実際の retraction とホモトピーを与える構成であり、
`rightFibration_initialFiber_isWeakHomotopyEquivalence` が弱同値性へ渡す。
coslice の恒等錐は始対象なので、coslice へ引き戻した right fibration に適用し、
底変換による fiber の同型を通して元の頂点 fiber の弱可縮性を得る。
`rightFibration_trivialKanFibration_of_weaklyContractible_coslices` はその結果。

`isRightCofinal_of_weaklyContractible_coslices` は一般の f を right anodyne な j と
right fibration p に因子分解する。各 coslice 射影は left fibration なので、j の引き戻しは
right anodyne、従って弱同値となり、f の弱可縮条件が p に移る。
p は上の判定で trivial Kan fibration、従って right cofinal となる。
j との合成から f の right cofinality を得た。
`isRightCofinal_iff_weaklyContractible_coslices` が **Quillen A の right 側の両方向**。
標的 B だけを quasicategory とし、始域 A は任意の単体集合。
Kerodon Thm 7.2.3.1 の原文の証明は inner fibration と cartesian fibration の局所化を使うが、
ここでは既に証明した left fibration に沿う right anodyne 性の保存を使って
right fibration への因子分解で閉じた。追加の存在仮定や straightening 依存はない。

`cofinalLeftFibration_op_rightFibration` と既存の逆側の反転により、左右の fibration を交換する。
反転関手の自己随伴の持ち上げ対応で anodyne 性を交換し、trivial Kan 性も保つことを示した。
anodyne・trivial Kan 因子分解を反転して cofinality を交換し、二重反転の矢の同型で
`isLeftCofinal_iff_isRightCofinal_op`・`isRightCofinal_iff_isLeftCofinal_op` を得た。

`IsWeaklyContractible.op` は、点への right anodyne・right fibration 因子分解で Kan 置換し、
Kan 複体内の全境界充填を反転して弱可縮性を移す。元の対象の Kan 性は不要。
`cofinalPointSliceOverOpIso` は Stable の slice 反転同型を固定図式の同型制限で正規化し、
射影との可換性を通常の Over 圏の同型として保持する。
`Δ[0].op` を `Δ[0]` と定義的に同一視せず、標準反転同型を明示する。
反転の pullback 保存で `cofinalSlicePullbackOpIso` を作り、一般の弱可縮性の反転判定と組み合わせた。
これにより `isLeftCofinal_iff_weaklyContractible_slices` が **Quillen A の left 側の両方向**を与える。
両側とも標的だけを quasicategory とし、元の始域や引き戻しの Kan 性を仮定しない。

`sliceOverRestrict_trivialKanFibration_of_isLeftCofinal` は任意の left cofinal な単射を
left anodyne と認識し、実際の slice 制限を trivial Kan fibration とする。
`sliceOverRestrict_trivialKanFibration_of_weaklyContractible_slices` は left 側の Quillen A を経由する版。
通常の圏の始対象の包含について、既存の `nervePoint_isLeftCofinal` からこの弱可縮条件を得て、
一般の制限定理へ渡す `initialCofinality_via_quillenA` を証明した。
A2h の `initialCofinality` と**同じ写像・同じ二宇宙の型**を回収する。
始対象の包含自体の cofinality の証拠は既存の nervePoint の定理を使い、その独立な再証明は主張しない。

これで B3 の指定範囲（左右の定義、Quillen A、A2h の回収）は完了。
補助的な一般化として、一般の cocartesian fibration に沿う cofinality の pullback 安定性、
Kan な底への弱同値 ⇒ cofinal の逆方向（Prop 7.2.1.5(2)）は未形式化。
これらを用いずに B3 の指定した結論を証明しており、B4・B5 の完了は別途必要。

### B4：進行中

`KanExtensionShapes` は右の添字を C_{c/} ×_C K、左を K ×_C C_{/c} とし、
slice の普遍錐の uncurry から F(c) を頂点とする標準錐・余錐を構成する。
`KanExtension` は指定した自然変換 α : Fδ → F₀、β : F₀ → Fδ に沿い、
標準錐・余錐を頂点を固定して輸送する族を保持する。
`rightKanConeTransport_nonempty`・`leftKanCoconeTransport_nonempty` は、
D の quasicategory 性だけからこの輸送の存在を証明する。

`IsRightKanExtension`・`IsLeftKanExtension` は、各点でこの輸送の終端・始端が
極限錐・余極限錐になるという条件。独立に選んだ値だけを条件にはしない。
`limitValue`・`colimitValue` は F(c) がその極限・余極限の頂点であることを示し、
両者の `valueIso` は同じ F₀ の拡張の値の hD における同型を与える。

`KanTransportUniqueness` は始点と基底の辺を固定した cocartesian な持ち上げの
可縮な空間から、基底の終点の厳密な fiber への評価射を構成する。
`exists_kanTransportEndVertexIso` は同じ基底の辺を持つ二つの cocartesian な辺の
終点が同じ fiber 内で同型になることを示す。
`KanComparisonCocartesian` は右比較錐の輸送を錐の制限の cocartesian な辺と認証し、
`coneFamily_iso` によって固定図式上の錐の圏での同型を得る。
`RightKanConeTransport.isLimitCone_iff` は右側の輸送の選択不変性、
`isRightKanExtension_iff_forall_transport` は一つの輸送での極限性と全ての輸送での極限性の同値。
元の圏 hD で頂点が同型というだけの議論は使わない。

`KanComparisonCartesian` は左比較余錐の輸送を余錐の制限の cartesian な辺と認証する。
反転した制限射が cocartesian fibration になる既存 API と `vertexFiberOpIso` を用い、
`coconeFamily_opIso` が固定図式上の余錐の圏の反転での同型を与える。
`LeftKanCoconeTransport.isColimitCone_iff` が左側の輸送の選択不変性、
`isLeftKanExtension_iff_forall_transport` が全ての輸送による同値な判定を与える。

`KanTransportBaseFiber` は基底の終点だけを固定した cocartesian な輸送の空間を構成する。
基底の写像空間への射影は trivial Kan fibration で、その充満忠実性により基底の同型を持ち上げられる。
`KanCosliceHomotopy` は基底の辺の h での等式を恒等終辺を持つ二単体へ戻し、
coslice の固定終点 fiber 内の辺・同型にする。F1 の広い coslice fiber 比較は
straightening を import するため使用せず、Core の join・coslice API で直接証明する。
`KanTransportEdgeHomotopy` はこれを cocartesian な持ち上げの終点の同型に移す。

`KanRightHomotopyInvariant` の `coneFamily_iso_of_homMk_eq` は、
指定自然変換 α と β が h Fun(K,D) で等しい場合の、右比較錐の固定図式上の同型。
`isRightKanExtension_iff_of_homMk_eq` は右 Kan 拡張条件の h での不変性を与える。
slice での制限の自然性を使い、異なる端点表示の照合は h の射の Arrow 表示の等式で扱う。

`KanLeftHomotopyInvariant` の `coconeFamily_opIso_of_homMk_eq` は、
指定自然変換が h Fun(K,D) で等しい場合の左比較余錐の固定図式上の反転同型。
`isLeftKanExtension_iff_of_homMk_eq` により左 Kan 条件の h 不変性も証明済み。
辺の類の反転は Core の左右ホモトピーの比較から直接扱う。

`KanExtensionHom` は A1c の `functorHomHomotopy` により、
`IsRightKanExtensionHom`・`IsLeftKanExtensionHom` を h Fun の射に対する条件として定義する。
`..._iff_of_representative` は元の射を表す任意のホモトピーによる判定との一致、
`..._homotopy` は実際のホモトピーの類を入力したときの元の条件との一致を与える。

**B4 は未完了。**
h Fun(C,D) での大域的一意性、極限からの点ごとの存在と大域的組み立てが残る。
各点の `valueIso` を大域的な同型の証明とは扱わない。

### 次の工程

点ごとの Kan 条件から h Fun 全体の普遍写像性（Kerodon Prop 7.3.6.1 の左右版）を導き、
Remark 7.3.6.6 の大域的一意性へ接続する。
普遍写像性だけの条件は一般には点ごとの Kan 条件より弱い（§7.3.6 冒頭・Cor 7.3.6.5）。
点ごとの定義と無条件に同値だとは主張しない。存在・組み立ても未完了。
A6 の `exists_pointwiseLimitCone`・`hasLimit_of_hasPointwiseLimits`・
`isLimitCone_iff_pointwise_of_hasPointwiseLimits` は到着済みで型を確認した。
点ごとの極限の存在条件から自然な錐を作る API であり、単に成分の錐を選んだだけの自然性は仮定しない。
B5 の古典 nerve に戻る検査も未完了。
全体の α2b 目標は継続中。

対象ビルド2288 jobs、公理監査2263宣言（標準三公理のみ）が成功。
推移的 import のリポジトリ内617モジュールに straightening 依存なし。

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
| `leftFibration_lift_fixed_prism` | 単射部分を固定した底の prism の持ち上げ | 済 |
| `cofinalLastHorn_prism_factorization`・`rightAnodyneExtensions_of_fixed_terminal_homotopy` | 固定した終端収縮を持つ単射の right anodyne 性 | 済 |
| `cofinalVertexFiberι_mono`・`cofinalPrismLastContraction_const` | fiber の単射性と終点収縮による任意の定値族の固定 | 済 |
| `leftFibration_terminalFiber_rightAnodyne_of_fixed_contraction`・`leftFibration_terminalFiber_rightAnodyne/isRightCofinal` | 固定した頂点への収縮から fiber 包含の判定、標準単体の場合 | 済 |
| `cofinalVertexFiberPullbackIso`・`cofinalVertexFiberPullbackIso_hom_fst` | 頂点 fiber と標準 pullback の同型・包含との整合 | 済 |
| `leftFibration_terminalPoint_pullback_rightAnodyne/isRightCofinal` | 終点包含の left fibration に沿う引き戻し | 済 |
| `cofinalLastHornVertex`・`cofinalLastHornContraction`・`..._zero/_one/_const` | 外側右ホーンに制限した固定終点収縮 | 済 |
| `cofinalVertexFiberBaseChangeIso`・`..._hom_ι` | 引き戻し前後の頂点 fiber の同型・包含との可換性 | 済 |
| `isRightCofinal_pullback_fst_of_vertexFibers` | 二つの fiber 包含の cofinality から第一射影への消去 | 済 |
| `leftFibration_lastHorn_pullback_isRightCofinal/rightAnodyne` | left fibration に沿う外側右ホーンの引き戻し | 済 |
| `rightFibration_lift_fixed_prism` | 任意の単射上を固定した終端からの相対 prism の持ち上げ | 済 |
| `rightAnodyneExtensions_of_fixed_terminal_homotopies` | 二段の固定した終端収縮から単射の right anodyne 性 | 済 |
| `leftFibration_terminalFiber_rightAnodyne_of_two_fixed_contractions` | 二段の底の収縮から終点 fiber 包含の right anodyne 性 | 済 |
| `cofinalHornRaiseOrderHom/FinishOrderHom`・`cofinalRightHornVertex/Raise/Finish`・両端と定値族の固定の式 | 全右ホーンの二段の固定終点収縮 | 済 |
| `leftFibration_rightHorn_pullback_isRightCofinal/rightAnodyne` | left fibration に沿う全右ホーンの引き戻し、k ≠ 0 | 済 |
| `cofinalRightFibration_of_over_lifting`・`cofinalRightAnodyne_of_over_lifting` | 通常の slice 内の持ち上げ性と元の単体集合の性質の接続 | 済 |
| `cofinalRightFibration_rightAdjoint_of_horns`・`cofinalRightAnodyne_leftAdjoint_of_horns` | 生成元の像の条件から随伴による一般の right anodyne な射への移送 | 済 |
| `leftFibration_rightHorn_isPullback_rightAnodyne`・`cofinalRightHorn_isPullback_rightAnodyne` | 全右ホーンの定理の任意の引き戻し正方形への移送 | 済 |
| `cofinalOverPullback_map_isPullback`・`leftFibration_overPullback_rightHorn_rightAnodyne` | slice の引き戻し関手の射の正方形と生成元での検査 | 済 |
| `leftFibration_overPullback_rightAnodyne_of_isLeftAdjoint`・`leftFibration_pullback_rightAnodyne_of_isLeftAdjoint` | 通常の引き戻し関手の右随伴の存在を仮定した一般の引き戻し保存 | 中間定理・仮定は無条件版で解消済み |
| `cofinalOverArrowEquiv/left`・`cofinalPresheafPullbackFiberEquiv/val` | 前層の小さい fiber と slice の Hom、引き戻し第一射影による計算 | 済 |
| `cofinalPresheafPullbackRestrictionIso`・`cofinalPresheafPullback_isLeftAdjoint` | slice の前層表示の下での制限関手との同型・通常の右 Kan 随伴 | 済 |
| `cofinalOverMapPostIso`・`cofinalPullback_isLeftAdjoint_of_equivalence` | 引き戻し関手の右随伴の存在の圏同値による移送、異なる宇宙も許す | 済 |
| `cofinalSSetPullback_isLeftAdjoint` | 任意の宇宙の単体集合の引き戻し関手の右随伴の存在 | 済 |
| `leftFibration_overPullback_rightAnodyne`・`leftFibration_pullback_rightAnodyne` | left fibration に沿う一般の right anodyne な射の引き戻し保存、追加条件なし | 済 |
| `leftFibration_pullback_isRightCofinal` | left fibration に沿う一般の right cofinal な射の引き戻し保存 | 済 |
| `IsRightCofinal.cosliceProjection_isRightCofinal/coslice_isWeaklyContractible` | Quillen A の right 側の必要性、標的だけが quasicategory | 済 |
| `IsWeaklyContractible.isContractibleKan`・`isWeaklyContractible_iff_isContractibleKan` | Kan 複体に限った弱可縮性と全境界充填の同値 | 済 |
| `rightFibration_trivialKanFibration_of_weaklyContractible_fibers` | 弱可縮な Kan fiber による right fibration の trivial 性 | 済 |
| `cofinalPointInterval`・`cofinalPointJoinPrism/zero/one/naturality` | 点との join から得る、二端と自然性を保つ prism | 済 |
| `cofinalPointInclusion_mono`・`IsInitialVertex.exists_fixed_coslice_section/exists_fixed_initial_prism` | 恒等錐を固定した切断と始対象を固定する収縮、底の quasicategory 性は不要 | 済 |
| `rightFibration_initialFiber_isSimplicialHomotopyEquivalence/isWeakHomotopyEquivalence` | right fibration の始対象上の fiber と全空間の実際のホモトピー同値 | 済 |
| `rightFibration_vertexFiber_isWeaklyContractible_of_coslices`・`rightFibration_trivialKanFibration_of_weaklyContractible_coslices` | coslice 引き戻しの弱可縮性から fiber の弱可縮性・trivial 性への還元 | 済 |
| `isRightCofinal_of_weaklyContractible_coslices`・`isRightCofinal_iff_weaklyContractible_coslices` | Quillen A の right 側の十分性と両方向の判定、標的だけが quasicategory | 済 |
| `cofinalLeftFibration_op_rightFibration`・`cofinalRightAnodyne_op_of_leftAnodyne/cofinalLeftAnodyne_op_of_rightAnodyne`・`cofinalTrivialKanFibration_op` | 反転による左右の fibration・anodyne 性と trivial Kan 性の移送 | 済 |
| `isLeftCofinal_of_isIso/isRightCofinal_of_isIso`・`IsLeftCofinal.of_arrow_iso/IsRightCofinal.of_arrow_iso` | 同型の cofinality と矢の同型による移送 | 済 |
| `IsLeftCofinal.op/IsRightCofinal.op`・`isLeftCofinal_iff_isRightCofinal_op/isRightCofinal_iff_isLeftCofinal_op` | 左右の cofinality の反転による両方向の判定 | 済 |
| `IsWeaklyContractible.op`・`isWeaklyContractible_of_op/isWeaklyContractible_op_iff` | 一般の単体集合の弱可縮性の反転による保存・検出 | 済 |
| `cofinalPointSliceOverOpIso/cofinalSlicePullbackOpIso`・`cofinalWeaklyContractible_slice_iff_op_coslice` | 射影と可換な slice の反転と pullback の弱可縮条件の移送 | 済 |
| `isLeftCofinal_iff_weaklyContractible_slices/isLeftCofinal_of_weaklyContractible_slices`・`IsLeftCofinal.slice_isWeaklyContractible` | left 側の Quillen A、標的だけが quasicategory | 済 |
| `sliceOverRestrict_trivialKanFibration_of_isLeftCofinal/of_weaklyContractible_slices` | left cofinal な任意の単射・Quillen A 条件による図式の slice 制限の判定 | 済 |
| `nervePoint_initial_quillen_slice_condition`・`initialCofinality_via_quillenA` | 始対象の包含の Quillen A 条件と A2h の同じ写像・二宇宙の型の回収 | 済 |

| `rightKanShape/leftKanShape`・`rightKanProjection/leftKanProjection`・`rightKanDiagram/leftKanDiagram` | 実際の slice 引き戻しと制限図式 | 済 |
| `rightKanCanonicalCone/leftKanCanonicalCocone`・`..._vertex` | 標準比較錐・余錐と F(c) という頂点 | 済 |
| `RightKanConeTransport/LeftKanCoconeTransport`・`cone/cocone`・`cone_vertex/cocone_vertex` | 指定自然変換と両立する頂点固定の輸送とその端点 | 済 |
| `rightKanConeTransport_nonempty/leftKanCoconeTransport_nonempty` | 標的の quasicategory 性による輸送の存在 | 済 |
| `IsRightKanExtension/IsLeftKanExtension` | 指定自然変換の比較錐の極限性・余極限性 | 定義済・左右の輸送の選択不変性は済 |
| `IsRightKanExtension.limitValue/IsLeftKanExtension.colimitValue`・両者の `valueIso` | 各点の値の公式と hD の同型 | 済・大域的一意性は未完了 |

| `kanTransportTarget/Choice/EdgeChoice`・`kanTransportEdgeChoice_target_val` | cocartesian な持ち上げの可縮な選択空間と終点評価 | 済 |
| `kanTransportTargetIso`・`exists_kanTransportEndVertexIso` | 同じ基底の辺を持つ持ち上げの終点の厳密な fiber 内の同型 | 済 |
| `RightKanConeTransport.edge/edge_cocartesian` | 比較錐の輸送の錐の制限に対する cocartesian 性 | 済 |
| `RightKanConeTransport.coneFamily_iso/isLimitCone_iff` | 右比較錐の固定図式上の同型と極限性の選択不変性 | 済 |
| `isRightKanExtension_iff_forall_transport` | 右 Kan 条件の全ての輸送による同値な判定 | 済 |

| `LeftKanCoconeTransport.edge/edge_cartesian/edge_op_cocartesian` | 比較余錐の輸送の cartesian 性と反転による cocartesian 性 | 済 |
| `LeftKanCoconeTransport.coconeFamily_opIso/isColimitCone_iff` | 左比較余錐の固定図式上の反転同型と余極限性の選択不変性 | 済 |
| `isLeftKanExtension_iff_forall_transport` | 左 Kan 条件の全ての輸送による同値な判定 | 済 |

| `kanTrivialFibration_vertexFiberMap` | trivial Kan fibration の同じ基底上の fiber への制限 | 済 |
| `kanTransportBaseFiber/Map/Target`・`kanTransportBaseFiberMap_trivialKanFibration`・`kanTransportBaseFiber_kanComplex` | 基底の終点のみを固定した輸送の空間と射影の全境界持ち上げ | 済 |
| `kanTransportBaseFiberTargetIso`・`kanTransportChoiceToBaseFiber/map_val` | 基底の写像空間の同型の持ち上げと具体的な輸送の埋め込み | 済 |
| `kanCosliceFiberEdge`・`kanCosliceFiber_nonempty_edge_of_homotopicL/nonempty_iso_of_homMk_eq` | 基底の辺の h の等式から固定終点の写像空間の同型 | 済 |
| `kanTransportBaseFiberTarget_nonempty_iso_of_homMk_eq` | 終点固定の輸送の基底ホモトピー不変性 | 済 |
| `kanTransportBaseEdge/Vertex`・`kanTransportBaseEdgeVertex_target_val/base_edge` | 実際の cocartesian な辺の終点固定の輸送空間での表示 | 済 |
| `exists_kanTransportEndVertexIso_of_homMk_eq` | 基底の辺の h の等式から元の終点 fiber 内の同型 | 済 |
| `RightKanConeTransport.coneFamily_iso_of_homMk_eq`・`isRightKanExtension_iff_of_homMk_eq` | 指定自然変換の h での等式に対する右比較錐の同型と右 Kan 条件の不変性 | 済 |

| `kanHomMk_edgeOp_eq_of_eq` | 辺の h での等式の反転による保存 | 済 |
| `LeftKanCoconeTransport.coconeFamily_opIso_of_homMk_eq`・`isLeftKanExtension_iff_of_homMk_eq` | 指定自然変換の h の等式による左比較余錐の反転同型と左 Kan 条件の不変性 | 済 |
| `IsRightKanExtensionHom/IsLeftKanExtensionHom` | h Fun の指定した射に対する左右 Kan 条件 | 済 |
| `isRightKanExtensionHom_iff_of_representative/isLeftKanExtensionHom_iff_of_representative`・`..._homotopy` | 任意の代表による判定と元の点ごとの定義との一致 | 済 |
