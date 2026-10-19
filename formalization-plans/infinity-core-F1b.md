# F1b（旧 α2b）：随伴・局所化・Kan 拡張 → F2-lite

> **v2 の位置づけ（2026-10-19）**：foundations.md §6 の F1b → F2-lite。B4・B5 の後、Cat_∞ を ∞ 圏として（Kerodon 5.5）、Cat_∞ の極限、lax pullback。

## 引き継ぎ（2026-10-19）

### 現在地

- B1〜B3 は明示した模型・宇宙で完了。B4 進行中、B5 未着手。両工程の後は [F2 計画](infinity-core-F2.md) 第 1 部。
- B4：任意の指定変換の相対 join 表示、両端の同時厳密化、h Fun の類の保存、
  元の左右 Kan 条件と厳密化後の局所極限・余極限性の同値まで証明。
- 同じ宇宙の quasicategory K・C・D と任意の δ : K→C、F₀ : K→D に対し、左右 Kan 拡張の存在を
  全頂点 c の標準局所図式の余極限・極限の存在と同定。指定変換つきの関手全体を構成する。
- 構成経路：`F1B.kanLeftComma δ` の cocartesian 射影、標準局所形から fiber への単射な前合成同値、
  相対指数の cartesian 性で普遍余錐を組み立て、図式・頂点を固定する円柱比較で局所輸送へ移す。
- 右の存在：coslice と反転図式の slice の同型、反転関手の二乗の恒等性で対象・射・普遍性を戻す。
- `kanRelativeCoconeRestriction` の持ち上げは部分余錐・元の図式・U による像を保つ延長と同値。
  U が inner／自明 Kan fibration なら比較も同じ性質。`KanRelativeCoconeLifting` は比較の始点境界充填条件。
  終対象上では通常の余極限性と同値。底の余錐が余極限なら、この相対条件から元の余極限性を回収。
- 標準の `IsRelativeColimitCone`（通常の coslice の相対始対象性）と操作的な相対余錐充填は U が inner なら同値。
  余錐頂点で可逆な輸送の後合成による保存と、標的の fiber 同型で固定図式の条件を全空間へ移送。
- inner fibration の相対始対象性と厳密な始点境界充填は同値。底変換と最初の頂点の始対象性の反映で証明。
- 指定可逆辺の可逆区間への厳密な延長と終点・像固定の持ち上げ、相対内部 Hom の順序交換から、
  V′ の局所余錐の境界固定の延長と相対普遍性を構成済み。
- `KanEquivalenceLifting U` は inner 性と終点・像指定の可逆辺の持ち上げと同値。相対 path 比較の自明 Kan 性で証明。
  この右持ち上げ条件は任意の単射による相対内部 Hom へ移る。
- 上の isofibration の二条件の下で、局所の標準 U 余極限から元・標的の図式を厳密に保つ大域図式を構成。
- 任意の U の path 置換は右持ち上げを持ち、定値 path の切断は同値。coslice の自明 Kan 性で相対余極限性を比較。
  任意の U 上で指定部分を保つ大域図式・そこで定値な可逆 path・全 fiber の U 余極限性を構成。
- 境界の最初の頂点の標準 U 余極限性から、元・境界・標的の図式を固定して相対境界を延長。
- 相対 join の通常の関手圏の相対制限について、始点境界充填・右 pinched 写像空間の同値を証明。
  局所 U 余極限図式の全部分 ∞ 圏からの制限は充満忠実で、必要な局所相対余極限が存在すれば自明 Kan。
- 円柱の変形で右端への制限と底射影による前合成の h Fun 上の随伴・相対 join の Hom 全単射を構成。
  円柱の quasicategory 性は不要。実際の制限の公式・後合成自然性・逆対応の単位との合成公式も証明。
- 右端の単位と標準 prism の指定変換の h Fun の類の一致を証明し、標準変換の Hom 普遍性へ接続。
  comma 上の Hom と元の添字上の Hom の全単射、両逆、後合成自然性、候補の指定変換の類を同定。
- 局所余極限から左 Kan 条件と Hom 普遍性を同時に持つ候補を構成し、任意の指定 β 自身へ移送済み。
  同じ宇宙の quasicategory K・C・D と任意の δ に対し、`IsLeftKanExtension` から `LeftKanHomUniversal`。
- 局所普遍余錐の Hom 全単射から、指定変換に両立する比較射の各点での可逆性・大域的同型・一意性を証明。
- 反転 Hom 全単射と指定変換・合成・前合成との両立から、右側も Hom 普遍性と大域的一意性を証明。
- 相対左 Kan 条件を標準 U 余極限で定義し、輸送の選択・指定変換の h Fun の類に対する不変性を証明。
  comma 候補の条件は全 fiber の相対余極限性と同値。任意の指定変換も厳密化後の局所 U 余極限性で判定。
- F1 の scaffold 比較は straightening に依存。再構成は `F1B.kanScaffoldBaseChange_overPullbackMap`。
- 最終検証：F1・F1B 同時ビルド成功（3842 jobs）、同時 import 検査成功（F1 7018・F1B 4351 宣言）。
  公理監査成功（4355 宣言、標準三公理のみ、1184 モジュールに straightening なし）。ソース名衝突 0。

### 残り（依存順、実作業時間の概算）

- 1. 全部分 ∞ 圏からの相対 Kan 拡張の写像空間の制限定理。
  Kerodon Prop 7.3.5.5・Prop 7.3.6.7・Cor 7.3.6.9／HTT §4.3。24〜60 時間。
  絶対的な左右の存在は完了。原典 7.3.6.7 は isofibration U の上の相対的な存在を使う。
  V′ の局所余錐の充填と相対普遍性は操作的な境界条件で証明済み。標準 U 余極限との同値も U が inner なら証明済み。
  相対的な組み立ては `KanEquivalenceLifting U` を持つ一般の U に拡張済み。任意の U の path 置換はこの条件を持つ。
  局所余錐から指定された大域図式上の相対図式を構成し、通常の関手の制限の相対始点境界充填も証明。
  任意の U 上の可逆 path つき図式構成と、isofibration の二条件の下での厳密な図式構成は完了。
  相対 join の全部分圏の制限は充満忠実、局所存在の下で自明 Kan。局所 Kan 条件の比較は完了し、元の制限への移送が残る。
- 2. B5：通常の圏の nerve で古典随伴・Kan 拡張を回収し最終監査。
  Kerodon §6.1.1・Def 7.3.1.2・Variant 7.3.1.5／HTT §5.2・§4.3。12〜32 時間。
- 右円柱比較の前合成同値は未証明。局所極限判定には不要。必要なら Kerodon Prop 5.2.4.5 の双対で証明。

### 主要宣言（名前のみ）

- `QCatAdjunction` / `qcat_nonempty_adjunction_iff_exists_naturalPinchedFamilyComparison`
- `RightKanRelativeJoinRealization.Strictification.isRightKanExtension_iff_local_limits`
- `LeftKanRelativeJoinRealization.Strictification.isLeftKanExtension_iff_local_colimits`
- `kanFiberwiseHom` / `kanFiberwiseHomFiberIso` / `kanRelativeJoinCoconeFiber_initialBoundary`
- `F1B.kanInitialBoundaryLifting_of_fiber_map` / `F1B.exists_kanRelativeJoin_diagram_extension_of_colimits`
- `F1B.kanLeftCommaProjection_cocartesianFibration` / `F1B.kanLeftKanShapeToCommaFiber_isPrecompositionEquivalence`
- `kanFiberwiseHomProjection_cartesianFibration` / `F1B.kanRelativeJoinBaseProjection_cocartesianFibration`
- `F1B.exists_kanLeftExtension_iff_local_colimits` / `F1B.exists_kanRightExtension_iff_local_limits`
- `F1B.kanIsRelativeColimitCone_equivalencePathReplacement_iff` / `F1B.exists_kanGlobalRelative_diagram_with_equivalencePath`
- `F1B.kanEquivalenceLifting_iff_inner_and_invertibleTargetLifting` / `F1B.KanEquivalenceLifting.relativeInternalHom`
- `F1B.kanRelativeJoinRelativeColimitRestriction_isFullyFaithful` / `F1B.kanRelativeJoinRelativeColimitRestriction_trivialKanFibration`
- `F1B.kanRelativeJoinRightHomEquiv` / `F1B.kanRelativeJoinTransformation_homUniversal`
- `F1B.kanLeftCommaCandidate_isRelativeLeftKanExtension_iff`
- `F1B.IsRelativeLeftKanExtendedFrom` / `F1B.kanRelativeLeftStrictification_iff_local_relativeColimits`
- `F1B.kanRightKanExtension_homUniversal` / `F1B.kanRightKanExtensionIso`
- `F1B.kanRelativeInitialVertex_iff_initialBoundary` / `F1B.kanRelativeCoconeLifting_iff_isRelativeColimitCone`

### 依存と提供

- Core/・F1/・Stable/ は読み取り専用。pullback の余極限保存、join・slice、h Fun、相対骨格・充填、
  反転、錐の輸送を使う。straightening に推移的にも依存しない。
- 提供：F1B 集約、随伴・反射的局所化・Quillen A、Kan の点ごとの条件と相対 join 還元、
  変動する局所形の族の普遍性・条件付き組み立て。一般の局所化の存在は F2、Hom 関手は F1h。

### 未コミット

- なし（本保存単位：相対余極限の添字・同型移送、相対左 Kan 条件、comma・厳密化の局所判定、集約・監査・本書）。

### 既知の問題

- F1 側の import 循環・timeout は修正済み。同時ビルドと同時 import の検査を保存前に実行する。
- 保存 `43c25ad6` は D レーンの 9 ファイルも同梱。履歴は変更せず、以後 `git commit --only` で所有パスを限定。
- F1B のソースに `ModelCategory` 仮定なし。各定理の前提は Lean を正本とする。
- cocartesian な p の `kanFiberwiseHom` は cartesian。制限 V 自体は未証明だが B4 では Kerodon 7.1.5.19 で迂回。
- B1 は全パラメータの集合値前層の模型。空間値二変数比較は未形式化。B2 は同じ宇宙で、一般の局所化の存在は含まない。

### 次の一手

- `IsRelativeLeftKanExtendedFrom U δ F` から元の関手圏の相対制限の始点境界充填を証明する。
  comma 候補・厳密化の局所条件との比較は実装済み。次は図式の族として比較し、F と δ による制限を保って戻す。
  全部分圏包含 δ の通常の相対写像空間と右側へ移送し、原典 7.3.6.7・7.3.6.9 を閉じる。

作成日：2026-10-18。正本は [infinity-core-F1.md](infinity-core-F1.md) の F1e〜F1g と
[foundations.md](foundations.md) §6・§8。本計画は目標・型・設計・現在地・主要宣言を管理し、
実施の経緯はコミットメッセージに置く。

## 0. 目標と範囲

quasicategory の随伴、反射的局所化、cofinality、点ごとの左右 Kan 拡張を構成する。
Lean は `SerrePositivity/InfinityCategories/F1B/`、namespace は
新規・再構成は `SerrePositivity.InfinityCategories.F1B`、既存の親名前空間 API は保持。集約は `InfinityCategories/F1B.lean`。
Core/・F1/・Stable/ は読むだけ。straightening に推移的にも依存しない。
sorry・追加公理・文献入力を使わず、監査で許す公理は
`propext`・`Classical.choice`・`Quot.sound` のみ。

## 1. 原典と工程

| 工程 | 成果 | 原典 | 状態 |
| --- | --- | --- | --- |
| B1 / F1e | 単位・余単位と h Fun の三角恒等式、自然な写像空間対応との特徴づけ、合成、随伴関手の一意性 | Kerodon [Def 6.1.1.1](https://kerodon.net/tag/02CG)、[§6.1.3](https://kerodon.net/tag/02D5)、[§6.1.5](https://kerodon.net/tag/02DM)、[Def 6.2.1.1・Prop 6.2.1.17](https://kerodon.net/tag/02EJ)、[Prop 6.2.6.1](https://kerodon.net/tag/02FV)・[Cor 6.2.6.5](https://kerodon.net/tag/02FX) / HTT §5.2 | 完了（全パラメータの族の前層による自然性の模型） |
| B2 / F1f | 充満部分 ∞ 圏への反射、局所対象、冪等性、局所化の普遍性の型と反射的な場合の構成 | Kerodon [§6.2.2](https://kerodon.net/tag/02F5)、[Cor 6.2.2.26](https://kerodon.net/tag/02FF)、[Def 6.3.1.9・Prop 6.3.1.13](https://kerodon.net/tag/01ME)、[Prop 6.3.3.7](https://kerodon.net/tag/02FY) / HTT §5.2.7 | 完了（同じ宇宙の標的に対する普遍性） |
| B3 / F1g 前半 | right cofinal、Quillen A、A2h の始対象による limit 計算の双対的回収 | Kerodon [Def 7.2.1.1](https://kerodon.net/tag/02N1)、[Thm 7.2.3.1](https://kerodon.net/tag/02NX) / HTT Thm 4.1.3.1 | 完了（左右の Quillen A と二宇宙版 A2h の同じ制限写像の回収） |
| B4 / F1g 後半 | slice の極限による左右 Kan 拡張、h での一意性、各点の存在、関手全体への組み立て | Kerodon [Notation 7.3.1.1・Def 7.3.1.2](https://kerodon.net/tag/02Y7)、Variant 7.3.1.5、§7.3.5 / HTT §4.3 | 進行中（指定自然変換の比較錐、各点の値・一意性、左右比較錐の選択不変性、左右の h 不変性、普遍写像性を仮定した大域的一意性、相対 join 表示、指定変換の類の保存、部分パラメータを固定した相対充填、slice の相対 join への局所比較、左条件の局所余極限表示への還元、標準右指定変換の局所極限表示との同値、任意の右指定変換の円柱比較つき相対 join 表示、厳密化後の局所極限判定への合成、左右 Kan 拡張の存在と局所余極限・極限の存在の同値） |
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
- F1 からの再構成は `SerrePositivity.InfinityCategories.F1B` 名前空間に置く。
  保存前に `lake build SerrePositivity.InfinityCategories.F1 SerrePositivity.InfinityCategories.F1B` と
  `lake env lean scripts/audit_infinity_f1_f1b.lean` で同名宣言の衝突がないことを確認する。
- 各保存単位で集約ビルド、公理監査、推移的 import の検査を行う。
  監査は生成宣言を含む F1B の全宣言を宣言元モジュールで抽出し、
  読み込んだリポジトリ内の straightening 系モジュールを拒否する。

## 記録の所在

実施記録・現在地の詳細・型一覧は [archive/infinity-core-F1b-log.md](archive/infinity-core-F1b-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
