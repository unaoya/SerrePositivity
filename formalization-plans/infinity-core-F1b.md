# F1b（旧 α2b）：随伴・局所化・Kan 拡張 → F2-lite

> **v2 の位置づけ（2026-10-19）**：foundations.md §6 の F1b → F2-lite。B4・B5 の後、Cat_∞ を ∞ 圏として（Kerodon 5.5）、Cat_∞ の極限、lax pullback。

## 引き継ぎ（2026-10-19）

### 現在地

- B1・B2・B3 は本文に明示した模型・宇宙の範囲で完了。B4 進行中、B5 未着手。
  B4・B5 の後は [F2 計画](infinity-core-F2.md) の第 1 部へ進む。
- B4：任意の指定変換の相対 join 表示、両端の同時厳密化、h Fun の類の保存、
  元の左右 Kan 条件と厳密化後の局所極限・余極限性の同値まで証明。
- 同じ宇宙の quasicategory K・C・D と任意の δ : K→C、F₀ : K→D に対し、
  左右 Kan 拡張の存在と全頂点 c の標準局所図式の余極限・極限の存在との同値を証明。
  各点の余錐を独立に選ぶだけでなく、指定変換つきの関手全体を構成する。
- 構成経路：comma の反転 `F1B.kanLeftComma δ` の射影は cocartesian fibration。
  局所形からその fiber への標準比較は単射な前合成同値で、反転による比較と厳密に一致。
  相対指数 `kanFiberwiseHomProjection` の cartesian 性と境界充填の移送を使い、
  局所余極限から相対 join 上の図式と全 fiber の普遍余錐を coherent に組み立てる。
- 右端から候補と指定変換を抽出。候補の標準局所輸送の余錐と、fiber の普遍余錐を
  標準比較へ制限した余錐を、図式・頂点を固定する比較円柱で結ぶ。
  始端・終端を厳密に同定し、全余錐の関手同型による余極限性の移送で左 Kan 条件を得る。
- 双対化：coslice の反転と反転図式の slice の同型を構成し、余錐ごとの余極限性と
  反転した錐の極限性の同値を証明。反転した右輸送の終端へ普遍性を移し、左 Kan 条件を右へ移す。
  標準の二重反転同型の各次数の成分が恒等写像であることから、反転関手の二乗と恒等関手の
  外延的な等式を証明。対象と射を同時に元へ戻し、一般の右 Kan 拡張の存在へ接続済み。
- 相対余錐制限 `kanRelativeCoconeRestriction` を構成。持ち上げは部分パラメータ上の余錐、
  元の図式、U による余錐全体の像を同時に保つ延長と同値。U が inner／自明 Kan fibration なら比較も同じ性質。
  `KanRelativeCoconeLifting` はこの比較の始点境界充填条件。終対象上では通常の余極限性と同値。
  底の余錐が余極限なら、この相対条件から元の余極限性を回収できる。
- 相対関手の境界充填は、指定部分の外の単体の始点だけの相対普遍性で成立する。
  境界を固定した標準単体上の族では最初の頂点だけで足りる。相対余錐制限へも適用済み。
  二段階の相対内部 Hom の順序交換の始域・標的の同型と比較射の可換性を証明済み。
  境界を固定する関手 V′ の相対余錐条件へ移送し、最初の境界余錐だけの条件から
  境界・元の図式・底の全余錐を保つ局所延長と、その転置の相対普遍性を構成済み。
  変動する添字に対する全空間の相対的な組み立ては未完。
- F1 の scaffold 比較は straightening に依存するため import しない。
  再構成した補題は `F1B.kanScaffoldBaseChange_overPullbackMap`。新規宣言も F1B 名前空間。
- 最終検証：F1・F1B 同時ビルド成功（3626 jobs）、同時 import 検査成功（F1 6282・F1B 3933 宣言）。
  公理監査成功（3937 宣言、標準三公理のみ、1074 モジュールに straightening なし）。ソース名衝突 0。

### 残り（依存順、実作業時間の概算）

- 1. 全部分 ∞ 圏からの相対 Kan 拡張の写像空間の制限定理。
  Kerodon Prop 7.3.5.5・Prop 7.3.6.7・Cor 7.3.6.9／HTT §4.3。24〜60 時間。
  絶対的な左右の存在は完了。原典 7.3.6.7 は isofibration U の上の相対的な存在を使う。
  V′ の局所余錐の充填と相対普遍性は操作的な境界条件で証明済み。
  変動する Kan 添字の全空間の相対比較を作り、局所条件からの相対的な組み立てへ接続する。
- 2. 点ごとの Kan 条件から大域的 Hom の全単射と h Fun の大域的一意性へ接続。
  Kerodon Prop 7.3.6.1・Remark 7.3.6.6／HTT §4.3。1 の後に 6〜16 時間。
- 3. B5：通常の圏の nerve で古典随伴・Kan 拡張を回収し最終監査。
  Kerodon §6.1.1・Def 7.3.1.2・Variant 7.3.1.5／HTT §5.2・§4.3。12〜32 時間。
- 右円柱比較の前合成同値は未証明。局所極限判定には不要。必要なら Kerodon Prop 5.2.4.5 の双対で証明。

### 主要宣言（名前のみ）

- `QCatAdjunction` / `qcat_nonempty_adjunction_iff_exists_naturalPinchedFamilyComparison`
- `RightKanRelativeJoinRealization.Strictification.isRightKanExtension_iff_local_limits`
- `LeftKanRelativeJoinRealization.Strictification.isLeftKanExtension_iff_local_colimits`
- `kanFiberwiseFunctorHomEquiv` / `exists_kanFiberwise_extension_of_initialBoundary`
- `kanFiberwiseHom` / `kanFiberwiseHomFiberIso` / `kanRelativeJoinCoconeFiber_initialBoundary`
- `kanCocartesianFibration_pullback_innerAnodyne_isPrecompositionEquivalence`
- `F1B.kanInitialBoundaryLifting_of_fiber_map` / `F1B.exists_kanRelativeJoin_diagram_extension_of_colimits`
- `F1B.kanLeftCommaProjection_cocartesianFibration` / `F1B.kanLeftKanShapeToCommaFiber_isPrecompositionEquivalence`
- `kanFiberwiseHomProjection_cartesianFibration` / `F1B.kanRelativeJoinBaseProjection_cocartesianFibration`
- `F1B.exists_kanLeftExtension_iff_local_colimits` / `F1B.exists_kanRightExtension_iff_local_limits`
- `F1B.kanRelativeCoconeRestriction` / `F1B.exists_kanRelativeCocone_extension_of_first_vertices`
- `F1B.kanRelativeHomInterchangeIso` / `F1B.exists_kanCocone_boundary_extension_of_first_colimit`

### 依存と提供

- Core/・F1/・Stable/ は読み取り専用。F1 の pullback の余極限保存、join・slice、
  h Fun、相対骨格・充填、反転、錐の輸送を使う。straightening に推移的にも依存しない。
- 提供：F1B 集約、随伴・反射的局所化・Quillen A、Kan の点ごとの条件と相対 join 還元、
  変動する局所形の族の普遍性・条件付き組み立て。一般の局所化の存在は F2、Hom 関手は F1h。

### 未コミット

- なし（本保存単位：相対内部 Hom の順序交換、比較射の同定、V′ の局所余錐の延長と相対普遍性、集約・監査・本書）。

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

- `exists_kanRelativeCocone_boundary_extension` とその絶対的な特殊例で、V′ の局所余錐の
  境界固定の延長と相対充填性は構成済み。次は変動する Kan 添字の全空間へ組み立てる。
  `kanFiberwiseHom` に標的の射 U による後合成を定義し、底への射影・curry・前合成との自然性を証明する。
  相対 join の制限と後合成から相対比較を作り、その fiber を `kanRelativeCoconeRestriction` と同定する。
  全空間の相対境界充填へ移し、相対的な存在と写像空間の制限定理へ進む。
  標準の coslice による U-colimit との比較は未証明。操作的な充填条件との同値を仮定しない。

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
