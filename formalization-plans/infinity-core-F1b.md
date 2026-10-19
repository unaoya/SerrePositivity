# F1b（旧 α2b）：随伴・局所化・Kan 拡張 → F2-lite

> **v2 の位置づけ（2026-10-19）**：foundations.md §6 の F1b → F2-lite。B4・B5 の後、Cat_∞ を ∞ 圏として（Kerodon 5.5）、Cat_∞ の極限、lax pullback。

## 引き継ぎ（2026-10-20）

### 現在地

- B1〜B5 は明示した模型・宇宙で完了。[F2 計画](infinity-core-F2.md) 第 1 部の F2L-1 も完了。F2L-2 進行中。
- B1：全単体集合パラメータの族の集合値前層による自然性の模型。双圏の単位・余単位・三角恒等式と自然な Hom 対応を比較。
- B2：同じ宇宙の標的に対する反射的局所化。一般の局所化の存在は F2 の範囲。
- B3：左右の Quillen A、弱可縮な comma 条件、二宇宙版の始対象による極限計算を回収。
- B4：元の指定左右変換の相対 join 表示と両端の厳密化、局所普遍性、各点の存在からの組み立て、Hom 普遍性と一意性を証明。
  充満忠実な inner 単射に沿う標準相対 Kan 制限、像・元の図式を保つ厳密な存在、任意 U の path 置換と写像空間の引き戻し比較も構成。
- B5：通常の関手圏の nerve と元の Fun の同型、自然変換の全単射と前後合成、指定単位・余単位を保つ古典随伴の双方向比較を証明。
  通常の Kan の大域的な Hom 普遍性と、指定単位・余単位の pointwise 条件を区別し、それぞれ左右とも双方向に比較。
  Under・Over と左右 comma の添字同型、錐・余錐の頂点と脚・普遍性・存在の双方向比較、標準局所錐の厳密な一致を構成。
  指定自然変換の実ホモトピーと頂点を固定した錐・余錐の族から、通常の指定局所錐そのものを native な左右の輸送で表示。
- 最終検証：F1・F1B 同時ビルド成功（4081 jobs）、同時 import 検査成功（F1 7451・F1B 5169 宣言）。
  公理監査成功（5175 宣言、標準三公理のみ、1428 モジュールに straightening なし）。ソース名衝突 0。
- F2L-1：F1 の既存 coherent nerve の頂点・辺・coherent Hom 比較を再利用。
  任意の頂点・辺の往復、端点固定の関手の全単射、恒等・合成三角形、Cat_∞ の写像空間と ULift した core Fun の同値を整備。
  比較の零単体と豊穣自然性、辺の類の一致と関手同型の存在、可逆辺と関手の同値の双方向判定を証明。
  Cat_∞ 内の引き戻しの指定可換性との照合・lax pullback は未完了。
- F2L-2：可逆 path による引き戻し候補と quasicategory 性、二射影・可換関手同型、指定 path を保つ全パラメータの lift を構成。
  任意 K の Fun との交換、inner fibration の引き戻しと core の交換を厳密な同型で証明。
  全 K の関手 core の置換後の厳密な引き戻し表示と元の二射影の一致まで完了。
  置換の始域射影の core の同値性、終点写像とその全内部 Hom の core の Kan fibration 性を証明。
  QCat の実際の豊穣後合成を core Fun の後合成と同定し、全豊穣 Hom の極限性で
  置換後の cospan の Cat_∞ の native な極限錐を証明。頂点は catPullbackObject p q と厳密に一致。
  自然変換の二宇宙の coherent 円柱と成分を構成し、定値 path の切断で元と置換後の図式の同型を証明。
  同値な形状への slice 制限の充填性を使い、元の p、q の cospan の native な極限錐を構成。
  頂点は catPullbackObject p q と厳密に一致。指定可逆辺・ホモトピーの厳密な持ち上げも構成。
  元の錐を追跡可能な相対輸送から選び直し、全錐の可逆ホモトピーを公開。頂点側は定値、
  図式側は切断の coherent 円柱と全時刻で厳密に一致。native な各脚と指定対角辺を関手へ読み戻し、
  共通の対角関手を通る上下の指定三角形から catPullbackConeLegSectionIso を構成。
  二射影の比較同型もこの構成へ更新し、存在命題からの個別選択を除いた。
  coherent 二単体を指定辺と同型へ読み、native な錐の三角形から catPullbackConeNativeCommutativity を構成。
  coherent 三単体の精密化の合成を共通の Hom で揃え、四面の指定同型の前後合成則を証明。
  任意の指定境界関手への輸送が元の同型を保つことも証明し、strict な錐の三つの境界射を回収。
  最初の比較三単体の六辺を固定し、catPullbackFirstTetrahedron_relation で上側の比較の整合を証明。
  残り二つの比較三単体の合成関係は未完了。共有面の最初の指定内部同型は構成済み。
  三角形の円柱の共有面・上下の面・六つの側面を二単体として厳密に同定。
  全錐と引き戻し錐の指定円柱の実際の三単体を構成し、元と置換後の錐の三角形を上下の面から回収。
  各辺の比較正方形の上下の三角形の三辺も同定。二脚の指定比較同型と指定 path の整合式は未完了。
- F2 の検証：F1・F1B・F2 同時ビルド成功（6391 jobs）、F2 の公理監査成功（699 宣言、標準三公理のみ）。
  F1/F1B 同時 import とソース名衝突 0 を再確認。F2 の主経路に ModelCategory・sorry・追加公理なし。

### 残り（依存順、実作業時間の概算）

- F2L-2：Cat_∞ の引き戻しと全試験 ∞ 圏からの写像空間による普遍性。Kerodon §5.5.3、HTT §3.3.3。40〜100 時間。
- F2L-3：Fun(Δ¹,−) と端点評価による lax pullback と普遍性。Tamme §1 Definition 5・Remark 6。24〜60 時間。
- F2L-4：同値辺上の全部分圏による引き戻しとの比較、安定性・exact 関手への接続。Tamme §1 Remark 7・Lemma 8。24〜60 時間。
- Ind・compact・冪等完備化は N、presentable 以降は I-b の分担。F2 の正本を参照する。

### 主要宣言（名前のみ）

- `QCatAdjunction` / `F1B.kanNonempty_adjunction_iff_nerveAdjunction`
- `RightKanRelativeJoinRealization.Strictification.isRightKanExtension_iff_local_limits`
- `LeftKanRelativeJoinRealization.Strictification.isLeftKanExtension_iff_local_colimits`
- `F1B.exists_kanLeftExtension_iff_local_colimits` / `F1B.exists_kanRightExtension_iff_local_limits`
- `F1B.kanRelativeLeftMappingPullbackComparison_equivalence` / `F1B.kanRelativeRightMappingPullbackComparison_equivalence`
- `F1B.kanNerve_leftKanHomUniversal_iff` / `F1B.kanNerve_rightKanHomUniversal_iff`
- `F1B.kanNerve_isLeftKanExtensionHom_iff_pointwise` / `F1B.kanNerve_isRightKanExtensionHom_iff_pointwise`
- `F1B.kanNerveLeftCoconeTransport_cocone` / `F1B.kanNerveRightConeTransport_cone`
- `F2.catInfinityVertexEquiv` / `F2.coherentEdgeHom_edge`
- `F2.catInfinityMappingEquivalence` / `F2.catInfinityEdge_isInvertible_iff`
- `F2.catPullbackObject` / `F2.catPullbackFunctorIso` / `F2.catPullbackFunctorCoreIso`
- `F2.qCatHom_postcomp` / `F2.catPullbackReplacementCone_isLimit`
- `F2.catPullbackReplacementDiagramIso` / `F2.catPullbackCone_isLimit` / `F2.catPullbackCone_vertex`
- `F2.catPullbackConeHomotopy_apex` / `F2.catPullbackConeHomotopy_diagram`
- `F2.catPullbackConeLegSectionIso` / `F2.catPullbackConeFstIso` / `F2.catPullbackConeSndIso`
- `F2.catInfinityTriangleIso` / `F2.catPullbackConeNativeCommutativity` / `F2.catPullbackFirstTetrahedron_relation`

### 依存と提供

- Core/・F1/・Stable/・HomotopyLimits/ の必要な閉包を読み取り専用で使用。F1B は推移的にも straightening に依存しない。
- 提供：F1B 集約、随伴・反射的局所化・Quillen A、左右 Kan の局所判定・相対制限・組み立て・一意性・古典比較。
- F2 は F1 の CatInfinity と γ1 を再利用し、N の Ind・compact・冪等完備化と分担。既存 Cat_∞ を再定義しない。

### 未コミット

- F2 共有計画の第 1 部の進捗更新。N 節の既存未コミット変更を巻き込まないため保存対象外。
  本保存単位：同型の輸送・側面の同定、最初の比較三単体の指定合成関係、集約・監査と本書。

### 既知の問題

- 保存 `43c25ad6` は D レーンの 9 ファイルも同梱。履歴は変更せず、以後 `git commit --only` で所有パスを限定。
- F1/F1B の同名宣言衝突は `efdd0fb3` で修正済み。保存前に同時ビルド・同時 import・ソースの衝突検査を行う。
- 新規・再構成は F1B 名前空間。F1B のソースに `ModelCategory` 仮定なし。前提は Lean が正本。
- B1 の空間値二変数 Hom 関手との比較は F1h の範囲で未形式化。B2 は一般の局所化の存在を含まない。
- 右円柱の前合成同値は未証明だが B4・B5 の局所判定には不要。必要なら Kerodon Prop 5.2.4.5 の双対で構成する。
- F2 の共有計画の N 節を保持し、Cat_∞ の strict pullback と ∞ 圏内の引き戻しを区別する。

### 次の一手

- 中央と最後の比較三単体の図式側の共通の対角関手と上下の指定同型を構成し、残り二つの合成関係を証明する。
  catPullbackFirstTetrahedron_relation と合わせて各脚の整合式を導き、strict な面を簡約して指定 path と照合する。

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
| B4 / F1g 後半 | slice の極限による左右 Kan 拡張、h での一意性、各点の存在、関手全体への組み立て | Kerodon [Notation 7.3.1.1・Def 7.3.1.2](https://kerodon.net/tag/02Y7)、Variant 7.3.1.5、§7.3.5 / HTT §4.3 | 完了（同じ宇宙の quasicategory に対する局所判定・存在・Hom 普遍性と一意性。充満忠実 inner 単射に沿う相対厳密存在・制限定理、任意 U の写像空間の homotopy pullback を右 Kan fibration 上の厳密な引き戻しへの実際の比較同値で実現） |
| B5 | nerve による古典随伴・Kan 拡張の回収と監査 | 上記と通常の圏の随伴・Kan 拡張 | 完了（同じ宇宙の小さい圏。指定単位・余単位を保つ随伴、通常の Kan の大域的普遍性、pointwise な左右 Kan 条件を区別して双方向に比較。集約・公理・import・名前衝突を監査） |

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
