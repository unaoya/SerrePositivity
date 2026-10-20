# F1b（旧 α2b）：随伴・局所化・Kan 拡張 → F2-lite

> **v2 の位置づけ（2026-10-19）**：foundations.md §6 の F1b → F2-lite。B4・B5 の後、Cat_∞ を ∞ 圏として（Kerodon 5.5）、Cat_∞ の極限、lax pullback。

## 引き継ぎ（2026-10-21、第 2 部）

### 現在地

- B1〜B5 は明示した模型・宇宙で完了。[F2 計画](infinity-core-F2.md) 第 1 部の F2L-1〜F2L-4 も完了。担当した第 1 部の受入条件を照合済み。
- B1：全単体集合パラメータの族の集合値前層による自然性の模型。双圏の単位・余単位・三角恒等式と自然な Hom 対応を比較。
- B2：同じ宇宙の標的に対する反射的局所化。一般の局所化の存在は F2 の範囲。
- B3：左右の Quillen A、弱可縮な comma 条件、二宇宙版の始対象による極限計算を回収。
- B4：元の指定左右変換の相対 join 表示と両端の厳密化、局所普遍性、各点の存在からの組み立て、Hom 普遍性と一意性を証明。
  充満忠実な inner 単射に沿う標準相対 Kan 制限、像・元の図式を保つ厳密な存在、任意 U の path 置換と写像空間の引き戻し比較も構成。
- B5：通常の関手圏の nerve と元の Fun の同型、自然変換の全単射と前後合成、指定単位・余単位を保つ古典随伴の双方向比較を証明。
  通常の Kan の大域的な Hom 普遍性と、指定単位・余単位の pointwise 条件を区別し、それぞれ左右とも双方向に比較。
  Under・Over と左右 comma の添字同型、錐・余錐の頂点と脚・普遍性・存在の双方向比較、標準局所錐の厳密な一致を構成。
  指定自然変換の実ホモトピーと頂点を固定した錐・余錐の族から、通常の指定局所錐そのものを native な左右の輸送で表示。
- F2L-1：F1 の既存 coherent nerve の頂点・辺・coherent Hom 比較を再利用。
  任意の頂点・辺の往復、端点固定の関手の全単射、恒等・合成三角形、Cat_∞ の写像空間と ULift した core Fun の同値を整備。
  比較の零単体と豊穣自然性、辺の類の一致と関手同型の存在、可逆辺と関手の同値の双方向判定を証明。
- F2L-2 完了：可逆 path による引き戻し対象と quasicategory 性、二射影・指定可換同型を構成。
  全パラメータの指定 path を保つ lift と一意性、任意 K の Fun との交換を証明。
  全 K の関手 core を置換後の core の厳密な引き戻しとして表示し、元の二射影との一致を証明。
  置換の始域射影の core の同値性と終点・全内部 Hom の core の Kan fibration 性を証明。
  全豊穣 Hom の極限性から元の cospan の Cat_∞ 内の native な極限錐を構成。頂点は候補と厳密に一致。
  頂点固定・図式側で切断の coherent 円柱と全時刻で一致する全錐の比較と、同じ円柱から二射影の指定比較を構成。
  三つの比較三単体の四面の合成則と strict な面の定値性から各脚の整合式を証明。
  可縮 fiber の射の一意性で、元の path 置換の同型を切断上で標準同型へ簡約。
  catPullbackCone_projection_commutativity で二射影の指定比較と候補の元の指定 path の最終整合を証明。
- F2L-3 完了：Fun(Δ¹,C) の両端評価を二点への制限として表示し、inner 性と単射な前合成同値の右持ち上げ性を証明。
  lax pullback 対象と quasicategory 性、二射影・矢印の族の端点、指定データを保つ全パラメータの lift と一意性を構成。
  定義式と同じ順序の引き戻しへの同型、native な極限錐と候補の頂点・両脚の一致を証明。
  任意 K の関手 core の引き戻し表示・二成分の一致・両端評価の全内部 Hom の core の Kan fibration 性を証明。
  laxPullbackVertexEquiv で頂点と二対象・指定矢印の三つ組の厳密な全単射を証明。
  右 pinched Hom と引き戻し・直積との交換を構成。両端の等式を輸送し下辺を p_* × q_* と厳密に同定。
  Tamme Remark 6 の正方形の IsPullback と右辺の Kan fibration 性を証明。
  γ3 の既存の空間の極限判定を使い、元の対象間写像空間を頂点とする 𝒮 の native な極限錐と元の両脚の一致を証明。
- F2L-4 完了：Remark 7 の同値矢印の全部分複体と catPullback の同型・厳密な引き戻し表示は二射影と元の指定 path を保持。
  零保存二関手から零頂点を構成し、両射影の零保存・成分ごとの零対象判定を証明。
  錐族の引き戻し・直積表示、反転同型と指定評価の一致から、元の指定錐・余錐の成分による十分条件を証明。
  錐族・余錐族の同値持ち上げと貼り合わせで、選んだ両入力の全錐・全余錐を保つ極限・余極限の存在を構成。
  入力の存在と保存の下で成分判定は同値。有限版で HasFiniteLimits・HasFiniteColimits と両射影の判定を供給。
  元の IsStable・IsExactFunctor から実際の span 余極限・cospan 極限の保存を導き、四角形と全錐の一致で成分判定へ接続。
  零枝の span の入力の存在から零角の押し出し性を成分で判定し、両射影の IsExactFunctor を証明。始域の安定性は仮定しない。
  零源の cospan の極限を反転と枝の交換で構成。元の指定射を保つ全 fiber・cofiber の存在と零角の条件の一致を証明。
  laxPullback_isStable は元の三圏の安定性と二関手の完全性のみから安定性を構成し、両射影も完全。
- 第 2 部：全 path 座標を保つ標準同型、任意の strict Kan cospan の native な引き戻し・filtered 比較を証明。
  余錐空間から全空間内部 Hom への比較同値、元の単位との整合と全 fiber 標的への前合成同値から native 余極限性を証明。
  任意の有限標的射を元の一値で検出。全相対境界を保つ模型本体の同時輸送と元の値への反映を構成し、反映後の境界値を厳密に保持。
  相対ホーン充填・境界定値な反転と合成、中央の全境界円柱を保持する zigzag 合成を証明。
  共通境界付き二入力の同時検出から、任意の有限標的射の相対有限検出・全空間 Kan 比較への持ち上げを構成。
  任意の Kan 境界への持ち上げと境界移動の除去も構成。全標準境界の path 置換充填から、元の Kan 引き戻し比較の弱同値性・ホモトピー逆を証明。
  元の引き戻し全空間を native 極限錐の頂点に構成。元の比較辺と恒等図式辺を持つ可逆な全錐比較・各脚の自然性を保持。
  区間錐の指定比較の自然性を切断・通常の錐の等式へ輸送。左右の像比較と同じ中心脚の整合、中心比較の消去と native 可換性の整合も証明。元の path 円柱と三座標の往復を保持。
  一般 coherent 図式の HasColimit、共通境界付き同時検出、元の全空間 Kan 積比較の弱同値性・ホモトピー逆を証明。引き戻し交換・Ind は残る。
  各 fiber と元の三値の path 引き戻しの厳密な同型、三座標を保つ包含と元の値による境界固定の相対有限検出を証明。
  検証：三集約同時ビルド 7600 jobs、公理監査 3378 宣言・同時 import 成功。標準三公理のみ、名前衝突なし。

### 残り（依存順、実作業時間の概算）

- 第 1 部は完了。10-20 に旧 N の F2N-1〜5 を引き取り、正本 F2 計画 §3 の順に進める。
  filtered・Ind・compact・冪等完備化・Ind の安定性と compact 生成。その後 presentable・随伴関手定理。

### 主要宣言（名前のみ）

- `QCatAdjunction` / `F1B.kanNonempty_adjunction_iff_nerveAdjunction` / `RightKanRelativeJoinRealization.Strictification.isRightKanExtension_iff_local_limits`
- `LeftKanRelativeJoinRealization.Strictification.isLeftKanExtension_iff_local_colimits` / `F1B.exists_kanLeftExtension_iff_local_colimits` / `F1B.exists_kanRightExtension_iff_local_limits`
- `F1B.kanRelativeLeftMappingPullbackComparison_equivalence` / `F1B.kanRelativeRightMappingPullbackComparison_equivalence` / `F1B.kanNerve_leftKanHomUniversal_iff` / `F1B.kanNerve_rightKanHomUniversal_iff`
- `F1B.kanNerve_isLeftKanExtensionHom_iff_pointwise` / `F1B.kanNerve_isRightKanExtensionHom_iff_pointwise` / `F1B.kanNerveLeftCoconeTransport_cocone` / `F1B.kanNerveRightConeTransport_cone`
- `F2.catInfinityMappingEquivalence` / `F2.catInfinityEdge_isInvertible_iff` / `F2.catPullbackObject` / `F2.catPullbackFunctorIso` / `F2.catPullbackFunctorCoreIso`
- `F2.catPullbackReplacementDiagramIso` / `F2.catPullbackCone_isLimit` / `F2.catPullbackCone_vertex` / `F2.catPullbackConeHomotopy_apex` / `F2.catPullbackConeHomotopy_diagram`
- `F2.catPullbackConeLegSectionIso` / `F2.catPullbackConeFstIso` / `F2.catPullbackConeSndIso`
- `F2.laxPullback` / `F2.laxPullbackCone_isLimit` / `F2.laxPullbackCone_arrow` / `F2.laxPullbackCone_inputs`
- `F2.laxPullbackVertexEquiv` / `F2.laxPullbackMappingProduct_isPullback` / `F2.laxPullbackMappingEndpointMap_fibration`
- `F2.laxPullbackFst_isExactFunctor` / `F2.laxPullbackSnd_isExactFunctor` / `F2.laxPullback_isStable`

- `F2.fiberwisePullbackNativeCone_isLimit` / `F2.fiberwisePullbackNativeCone_vertex` / `F2.fiberwisePullbackNativeConeHomotopy_apexEdge`

### 依存と提供

- Core/・F1/・Stable/・HomotopyLimits/ の必要な閉包を読み取り専用で使用。F1B は推移的にも straightening に依存しない。
- 提供：F1B 集約、随伴・反射的局所化・Quillen A、左右 Kan の局所判定・相対制限・組み立て・一意性・古典比較。
- F2N-1〜5 は F1b へ移管。N の HomotopyLimits と F1 の成果を読み取り専用で再利用する。

### 未コミット

- 所有パスの未コミットなし（本保存後）。他レーンの変更は保存対象外。

### 既知の問題

- 保存 `43c25ad6` は D レーンの 9 ファイルも同梱。履歴は変更せず、以後 `git commit --only` で所有パスを限定。
- F1/F1B の同名宣言衝突は `efdd0fb3` で修正済み。保存前に同時ビルド・同時 import・ソースの衝突検査を行う。
- 新規・再構成は F1B 名前空間。F1B のソースに `ModelCategory` 仮定なし。前提は Lean が正本。
- B1 の空間値二変数 Hom 関手との比較は F1h の範囲で未形式化。B2 は一般の局所化の存在を含まない。
- 右円柱の前合成同値は未証明だが B4・B5 の局所判定には不要。必要なら Kerodon Prop 5.2.4.5 の双対で構成する。
- 旧 N の詳細は F2 の archive へ保持。Cat_∞ の strict pullback と ∞ 圏内の引き戻しを区別する。

### 次の一手

- F2N-1：置換の元の path の指定同型・切断上の簡約を構成し、交換則で像比較と intervalPullbackPathIso を照合。coherent 余極限錐へ接続する。

## 0. 目標と範囲

正本は [infinity-core-F1.md](infinity-core-F1.md) の F1e〜F1g と [foundations.md](foundations.md) §6・§8。
本計画は目標・設計・現在地・主要宣言を管理し、実施記録はコミットメッセージに置く。

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

## 第 1 部の完了監査（2026-10-20）

| 受入条件 | 現在の証拠（F2 名前空間、B4・B5 は F1B 集約） |
| --- | --- |
| B4・B5 | 左右 Strictification の局所判定、元の変換を保つ存在・Hom 普遍性、nerve の指定随伴・Kan 比較を監査で再読込 |
| F2L-1 | catInfinityMappingEquivalence、catInfinityEdgeEquiv、catInfinityEdge_isInvertible_iff。F1 の coherent nerve を再利用 |
| F2L-2 | catPullbackCone_isLimit・vertex、全 K の catPullbackFunctorCoreIso、catPullbackCone_projection_commutativity |
| F2L-3 | laxPullbackCone_isLimit・arrow・inputs、laxPullbackVertexEquiv、laxPullbackMappingSpaceCone_isLimit と両脚の式 |
| F2L-4 | 同値矢印の全部分複体との射影・path を保つ同型、任意形状の極限・余極限の存在と成分判定、有限版、laxPullback_isStable、完全な両射影 |
| 保存条件 | F1・F1B・F2 同時ビルド、公理・import 監査、同名ソース宣言 0、新規 4 モジュールは各 100 行・100 桁以内。sorry・追加公理・ModelCategory 仮定なし |

N の第 2 部と I-b の presentable 以降は本監査の完了対象外。証明の仮定と宇宙は Lean の型が正本。

## 記録の所在

実施記録・現在地の詳細・型一覧は [archive/infinity-core-F1b-log.md](archive/infinity-core-F1b-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
