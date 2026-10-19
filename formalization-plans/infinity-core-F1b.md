# F1b（旧 α2b）：随伴・局所化・Kan 拡張 → F2-lite

> **v2 の位置づけ（2026-10-19）**：foundations.md §6 の F1b → F2-lite。B4・B5 の後、Cat_∞ を ∞ 圏として（Kerodon 5.5）、Cat_∞ の極限、lax pullback。

## 引き継ぎ（2026-10-19）

### 現在地

- B1・B2・B3 は本文に明示した模型・宇宙の範囲で完了。B4 進行中、B5 未着手。
  v2 の F1b レーンとして、B4・B5 の後は [F2 計画](infinity-core-F2.md) の第 1 部へ進む。
- B4：任意の δ と指定変換の相対 join 表示、両端の同時厳密化、h Fun の類の保存、
  元の左右 Kan 条件と厳密化後の局所極限・余極限性の同値まで証明。
- `kanFiberwiseFunctor`：底の単体ごとに変動する局所形 F 上の図式の族の全空間を構成。
  全単体の通常の余極限を保つ F について、任意のパラメータ上の図式との全単射を証明。
  実際の pullback 関手への適用 `kanFiberwiseHom` は、逆像上の図式を厳密に表現する。
- 局所形の自然変換による制限を構成し、図式の持ち上げと族の持ち上げの同値を証明。
  相対始点境界充填を使う相対骨格の組み立てと、fiber の余極限性からの充填条件の導出を証明。
  相対 join の関手の族と実際の図式の延長まで接続済み。Kan 条件への接続と一般の存在は未完。
- `kanFiberwiseHom` の fiber を `Fun(K_c,D)` と厳密に同定し、元の図式の制限との自然性を証明。
  相対 join の fiber は `K_c ⋆ Δ⁰`、その関手の族の制限は `coconeRestriction` に一致する。
  普遍余錐から、この fiber の射と全空間の射に対する相対始点境界充填まで証明。
- 射影の持ち上げ問題を逆像上の図式の延長と同定し、inner fibration 性の必要十分条件を証明。
  標準単体上の cocartesian fibration の最終 fiber への厳密な retraction と、そこで固定された輸送を構成。
  射影の終点指定の辺の持ち上げ（任意次元の最後の頂点版も）を証明。
- cocartesian section の全部分単体集合を構成し、inner fibration の場合の quasicategory 性を証明。
  前合成の関手性、一般の strict transport の図式と fiber 評価射、任意パラメータの族の curry・uncurry を構成。
  部分パラメータと始対象の評価を同時に固定した延長、評価の自明 Kan fibration 性と ∞ 圏同値を証明。
- 一般の universal scaffold を構成し、各 fiber の自明 Kan fibration 性と水平辺の cocartesian 性を証明。
  有限鎖の帰納と底についての局所性で、任意の通常の圏の nerve 上の scaffold の全空間の前合成同値を証明。
  universal scaffold も、内ホーンを含む任意の単体集合への底変換後に前合成同値となる。
- cocartesian fibration に沿う内ホーンと任意の inner anodyne 射の引き戻しの前合成同値を証明。
  `kanFiberwiseHom` の射影は inner fibration、底と標的が quasicategory なら全空間も quasicategory。
- 終端辺上の cocartesian 辺を可逆化する図式の外ホーン逆像からの延長を、任意の pullback 表示で証明。
  終端辺の逆像への制限で条件を確認し、可逆化する図式の表す相対指数の辺の cartesian 性を証明。
  終点指定の特殊持ち上げと合わせ、`kanFiberwiseHomProjection` の cartesian fibration 性まで証明。
- join の inner fibration 性に加え、cocartesian な p の相対 join の底への cocartesian fibration 性を証明。
  左包含は任意の底変換後も cocartesian 辺を保存。相対指数の制限は任意の cartesian 辺を保存する。
- cocartesian fibration 間の単射による相対指数の制限は inner fibration。相対 join の制限 V にも適用済み。
- 余錐制限と相対 join 制限の各 fiber の cartesian fibration 性を証明。縦合成の比較射の pullback 分解も証明。
- 両射影の輸送を保つ inner fibration では、fiber の相対始点・終点境界充填を全空間へ移せる。
- 対象の族の各頂点に必要な余極限だけで、普遍余錐全体からの引き戻しは自明 Kan fibration。図式を延長できる。
- 任意の関手 δ に対し、既存 comma の反転 `F1B.kanLeftComma δ` を構成。底への射影は cocartesian fibration。
  恒等矢印の包含、指定変換 δ(k)→c、fiber の反転表示と既存の矢印空間への比較を証明。
- 最終検証：F1・F1B 同時ビルド成功（3430 jobs）、同時 import 検査成功（F1 5684・F1B 3571 宣言）。
  公理監査成功（3575 宣言、標準三公理のみ、974 モジュールに straightening なし）。ソース名衝突 0。

### 残り（依存順、実作業時間の概算）

- 1. 点ごとの余極限からの相対 join の図式の存在を、一般の δ と Kan 条件へ接続する。
  Kerodon Lemma 7.3.4.5–6・Prop 7.3.4.7・Prop 7.3.5.5／HTT §4.3。24〜60 時間。
  fiber の充填の全空間への移送、実際の図式の延長、対象の族の点ごとの余極限だけによる存在は証明済み。
  構成済み oriented fiber product の fiber を局所添字と比較し、任意の δ に沿う存在へ接続する。
- 2. 全部分 ∞ 圏からの相対 Kan 拡張の写像空間の制限定理。
  Kerodon Prop 7.3.6.7・Cor 7.3.6.9／HTT §4.3。1 の後に 16〜40 時間。
  原典は相対 Kan 拡張の存在（Prop 7.3.5.5）を使う。局所境界充填から直接は結論しない。
- 3. 点ごとの Kan 条件から大域的 Hom の全単射と h Fun の大域的一意性へ接続。
  Kerodon Prop 7.3.6.1・Remark 7.3.6.6／HTT §4.3。2 の後に 6〜16 時間。
- 4. B5：通常の圏の nerve で古典随伴・Kan 拡張を回収し最終監査。
  Kerodon §6.1.1・Def 7.3.1.2・Variant 7.3.1.5／HTT §5.2・§4.3。12〜32 時間。
- 右円柱比較の前合成同値そのものは未証明。局所極限判定への合成には不要だった。
  必要なら Kerodon Prop 5.2.4.5 の双対として別途証明。

### 主要宣言（名前のみ）

- `QCatAdjunction` / `qcat_nonempty_adjunction_iff_exists_naturalPinchedFamilyComparison`
- `RightKanRelativeJoinRealization.Strictification.isRightKanExtension_iff_local_limits`
- `LeftKanRelativeJoinRealization.Strictification.isLeftKanExtension_iff_local_colimits`
- `kanFiberwiseFunctorHomEquiv` / `exists_kanFiberwise_extension_of_initialBoundary`
- `kanFiberwiseHom` / `kanFiberwiseHomFiberIso` / `kanRelativeJoinCoconeFiber_initialBoundary`
- `KanCocartesianScaffold.isPrecompositionEquivalence` / `kanUniversalScaffold_overPullback_isPrecompositionEquivalence`
- `kanCocartesianFibration_pullback_innerAnodyne_isPrecompositionEquivalence`
- `F1B.kanInitialBoundaryLifting_of_fiber_map` / `F1B.exists_kanRelativeJoin_diagram_extension_of_colimits`
- `F1B.kanLeftCommaProjection_cocartesianFibration` / `F1B.kanLeftCommaFiberIso`
- `kanFiberwiseHomProjection_cartesianFibration` / `F1B.kanRelativeJoinBaseProjection_cocartesianFibration`
- `F1B.kanRelativeJoinRestriction_preservesCartesianEdges` / `F1B.kanRelativeJoinRestriction_innerFibration`

### 依存と提供

- Core/・F1/・Stable/ は読み取り専用。F1 の pullback の余極限保存、join・slice、
  h Fun、相対骨格・充填、反転、錐の輸送を使う。straightening に推移的にも依存しない。
- 提供：F1B 集約、随伴・反射的局所化・Quillen A、Kan の点ごとの条件と相対 join 還元、
  変動する局所形の族の普遍性・条件付き組み立て。一般の局所化の存在は F2、Hom 関手は F1h。

### 未コミット

- なし（本保存単位：反転 comma の cocartesian な置き換え、fiber と指定変換の比較、集約・監査・本書）。

### 既知の問題

- F1/F1B の同時ビルドと同時 import の検査を保存前に実行する。全体 `lake build` は未実行。
- 保存 `43c25ad6` は D レーンの 9 ファイルも同梱。履歴は変更せず、以後 `git commit --only` で所有パスを限定。
- F1B のソースに `ModelCategory` 仮定なし。各定理の前提は Lean を正本とする。
- `kanFiberwiseHom` の cartesian fibration 性は cocartesian な p について証明済み。
  制限 V 自体の cartesian fibration 性は未証明。B4 の充填には不要で、Kerodon 7.1.5.19 の経路で移送済み。
- 大域的 Hom 普遍性を仮定した一意性は証明済みだが、点ごとの Kan 条件からの導出は未完。
- B1 の自然性は全パラメータの集合値前層の模型。空間値二変数 ∞ 関手との比較は未形式化。
  B2 は同じ宇宙の標的に対する普遍性。一般の C[W⁻¹] の存在は主張しない。

### 次の一手

- `kanLeftCommaProjection δ` は既存 comma の反転による cocartesian な射影。元の K の包含は射影すると δ。
  次は `kanLeftCommaFiberIso` の反転 comma の fiber と `leftKanShape δ c` の図式を比較する。
  余極限を移して点ごとの存在定理へ渡し、指定変換を元の K へ制限する（Kerodon 7.3.4–5）。

作成日：2026-10-18。正本は [infinity-core-F1.md](infinity-core-F1.md) の F1e〜F1g と
[foundations.md](foundations.md) §6・§8。本計画は目標・型・設計・現在地・主要宣言を管理し、
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
| B4 / F1g 後半 | slice の極限による左右 Kan 拡張、h での一意性、各点の存在、関手全体への組み立て | Kerodon [Notation 7.3.1.1・Def 7.3.1.2](https://kerodon.net/tag/02Y7)、Variant 7.3.1.5、§7.3.5 / HTT §4.3 | 進行中（指定自然変換の比較錐、各点の値・一意性、左右比較錐の選択不変性、左右の h 不変性、普遍写像性を仮定した大域的一意性、相対 join 表示、指定変換の類の保存、部分パラメータを固定した相対充填、slice の相対 join への局所比較、左条件の局所余極限表示への還元、標準右指定変換の局所極限表示との同値、任意の右指定変換の円柱比較つき相対 join 表示、厳密化後の局所極限判定への合成） |
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
