# I-1 a7：X レーン（交換定理）の正本

> **v3 停止追記（2026-10-25 17:53 JST）**：
> **Ind の d′ で完了、X の部分成果は未使用の補助**。
> Ind の厳密経路 `f350dce62`（15:21）で I-1 a7 は完了。X は保存後に停止する。
> a7 の計画・現在地の正本は本ファイル。Ind 全体の正本は infinity-core-F1.md。
> 着手時の48時間上限は、17:53 のユーザー停止指示により解除。

## 所有範囲と完了条件

- 着手：2026-10-25 13:07:39 JST。17:53 の指示により証明開発を終了。
- 所有：F2/FilteredExchange/ の今回新設した葉、
  scripts/audit_infinity_f2_exchange.lean、および本計画ファイル。
- F2/Ind・Compact・Idempotent・F1・F1B・Core は読み取り専用。
  既存の集約と scripts/audit_infinity_f2.lean は変更しない。
- foundations.md §6・§8、foundations-progress.md の Ind I-1、
  infinity-core-F1.md と本ファイルの凍結時引き継ぎを読了。
- 当初の X 担当は直接経路の a③・a④・b①（cospan 形状の交換）。停止により不要。
  全有限形状への帰納 b② と公開 b③ は Ind の I-2 d′ に移管する。
  strict 図式や端点の一致だけで完了とはしない。指定比較・全パラメータを保持する。
- sorry・追加公理・文献を仮定にした入力は使わない。
  許す公理は propext・Classical.choice・Quot.sound のみ。
- b① の引き渡しは不要。未追跡の補助15葉をビルド可能な形で保存して停止。
- 2026-10-25 14:44 のユーザー承認による分担変更：Ind は P の poset 交換の
  ℵ₀ 特殊化による代替経路 I-2 d′ を並行実施。その後17:53に停止・上限解除。

## 三段目（14:44 分担変更・17:53 停止指示反映）

| 番号 | 工程・所有 | 完了条件 | 現在地 |
| --- | --- | --- | --- |
| 1 | X：a③ Ncomp | 元の零面値・終点比較・raw 二辺値比較の因子式 | 停止・未使用の補助のみ |
| 2 | X：a④ 普遍三角形の一致 | Nlong と Ncomp を代入し、同じ零面値を消去 | 不要・未着手で停止 |
| 3 | X：b① cospan 形状の交換 | 指定二三角形・path を保つ全錐比較と保存、直接経路の cospan 交換 | 不要・未着手で停止 |
| 4 | Ind：b② 有限形状帰納と交換入力の実証拠化 | 部分極限・接着の同時帰納、全有限形状の交換定理 | Ind の d′ で完了 |
| 5 | Ind：b③ 公開・集約・監査 | 公開し、IndFiniteLimitExchangeInput に渡せることを検証 | Ind の d′ で完了 |

工程1〜3は不要となった。工程4・5は Ind の所有で完了。
X は保存対象のビルド・専用監査だけを行い、新たな証明開発は行わない。

## 現在地：停止・補助成果の保存

**Ind の d′ で完了、X の部分成果は未使用の補助**。
Ind の `f350dce62` にある公開定理
`SerrePositivity.InfinityCategories.F2.Ind.indFiniteLimitExchangeInput` を確認した。
`coherentFilteredLimitExchangeShape_finite` から全有限形状の交換入力を構成しており、
交換入力を仮定する宣言ではない。X の a③・a④・b① の継続は不要。
48時間上限は解除。未追跡ファイルを破棄せず15葉とも保存した。

今回保存した補助の主要公開名（名前空間は F2）：
- `triangleRightConeParameter_eq_simplexCone`：元の右 prism 三角形と標準錐の全体の一致。
- `simplexConeParameter_index_naturality`：係数付き錐の添字自然性。
- `triangleRightConeParameter_first`・`_last`・`_long`：元の実三辺の回収。
- `coherentRightSliceAppendEdge_back`：同じ追加射の実終端面と元の後合成の一致。
- `coherentCompositionConeTetrahedron_face013` と `_precomp`：013 面全体と
  元の合成三角形の一致、任意の同時係数制限での保持。

保存検証：`CompositionConePostFace` の対象ビルド2198 jobsで通過。
専用監査10240宣言で通過、標準三公理のみ。停止コミット本文にも記録する。
推移的 import は2214プロジェクトモジュール、他レーンの未保存依存は0。
全15葉が検証対象の import 閉包に入り、各葉100行・100桁以内。
既存の集約・既存 audit_infinity_f2・読み取り専用の各領域は変更していない。

X 側の Ncomp 本体は未証明。012・013 面の同定は補助として保存したが、
023・123 面の元の合成図式への接続と指定評価比較の一致は未完。
a④・b①は未着手で停止。X の直接経路の完了とは扱わない。
以下は停止前の構成・不足の履歴であり、今後の作業指示ではない。

凍結時の a①・a② は完了。長辺の因子式 Nlong も
`coherentColimitApexLongEvaluationComparison_heq_value_composite` で完成済み。
二辺については `coherentColimitApexZeroCompositeValue_heq_two_evaluation` がある。
今回の `coherentColimitApexZeroCompositeValue_heq_triangle_iff` は Ncomp を
次の二つの**元の指定同型の HEq**へ帰着する。帰着先はまだ未証明。

- `pointedHomTwoMorphismEvaluationComparison f g`
- `pointedHomCompositeMorphismEvaluationComparison f g`

固定評価の作用と指定値の後合成との一致を構成済み。
`pointedValueFamilyTwoStageIso` と `pointedValueFamilyCompositeIso` は
同じ端点を持つが、両者の等式はまだ証明していない。
`pointedRightFamilyEvaluation_comp` の端点等式をその代用にしない。

今回、最後の対象への後合成を coherent 単体の全 Hom 上で構成した。
右 slice の実際の単体写像へ組み立て、元の合成 prism と canonical Hom 比較に
対する厳密自然性まで対象ビルドが通過した。主要な公開名は以下。
名前空間はいずれも SerrePositivity.InfinityCategories.F2。

- `coherentSimplexLastPost` / `coherentSimplexLastPost_comp`
- `coherentSimplexAppendMorphism_face_last`
- `coherentCompositionSimplex_last_post`
- `coherentSimplexLastPost_reindex`
- `coherentRightSlicePost` / `coherentRightSlicePost_projection`
- `coherentRightSlicePost_comp`
- `coherentCompositionPrism_post`
- `coherentHomSliceComparison_post`
- `coherentRightSlicePostFiber_comp` / `coherentHomSliceFiberComparison_post`

初回報告後も続行し、同じ底上の fiber 射へ降ろした。
元の Hom 比較の fiber 内の厳密可換式と合成則は1783 jobsで対象ビルド通過。
専用公理監査も9358宣言で通過（標準三公理のみ）。
この式から指定輸送比較の合成則への接続は引き続き未完。

続行分として、同じ底を保つ全空間の射で相対延長空間を後合成する
`relativeExtensionPost` と、その終点 fiber 評価の厳密可換式
`relativeExtensionFiberEndpoint_post` を構成した。
`relativeExtensionFiberEndpoint_witnessIso_post` は元の二実延長の指定比較を
fiber 射へ後合成すると、同じ二延長の像の指定比較そのものになることを証明する。
さらに `leftFibrationPrism_diagonalTransportIso_post` は元の実 prism の指定比較と、
元の普遍 prism の像の指定比較を貼ると、像の実 prism の元の指定比較になる等式。
比較を新しく選んだものへ置換していない。Ncomp 自体はなお未完。

さらに元の slice 反転同型で共役した `coherentReverseSlicePost` を構成。
`coherentCompositionReversePrism_post` は元の反転合成 prism 全体の厳密自然性、
`coherentReverseSliceFiberComparison_post` は元の反転 Hom 比較の fiber 内の厳密自然性。
`coherentCompositionReverseSpecified_post` は同じ元の指定対角比較を、
後合成の像である元の実反転合成 prism の指定比較へ値まで移す。
統合ビルド2788 jobs、専用監査9496宣言（標準三公理のみ）で通過。
これで終域後合成に関する指定比較の移送まで完成したが、Ncomp の二射合成則とは別。

現在の追加接続：元の合成四角形の持ち上げを `TransportSquareLift` に保持し、
同じ三辺・上二頂点の境界式を公開した。
`transportSquareCanonicalComparison_eq_transportIso` は、元の選択済み持ち上げの
三辺の指定比較を貼った式が元の `TransportIntervalSquare.transportIso` そのものであること。
`diagonalFiberTransport_sourceIso_heq_action` は元の sourceIso の代表辺を同じ全区間作用へ戻す。
`diagonalFiberTransport_sourceIso_trans` はその指定合成則。
`relativePrismNativeEndpointIso_heq_sourceIso` は元の native 終点像を同じ sourceIso へ同定する。
三対象統合ビルド3225 jobsで通過。Ncomp は引き続き未完。

**次の一手**：同じ実右 slice 写像と元の合成 prism の自然性を、
元の指定普遍輸送比較へ移す。`relativePrismSpecified_naturality`、
`pointedHomMorphismValueComparison_heq_prism`、
`pointedValueFamilyTransportIso_at_right` に接続し、指定同型の合成則を証明する。
新しい比較を選び直したり、その合成則を入力仮定に加えたりしない。
後合成に関する指定対角比較の一般式を、同じ右 slice の反対左 coslice へ適用し、
元の Hom 合成 prism の比較をその像へ移す部分まで今回完成した。
左反転 Hom 側は最終対象が一点に固定された元の逆合成 prism なので、
右 Hom 側の終域後合成と混同せず、同じ三射の高次整合で両側を照合する。
次は元の零面・最後辺の指定自然性と、この移送式との接続を照合する。
直近の具体手順：底辺の同じ普遍 prism を固定した二つの実四角形の相対延長比較を取り、
三辺の指定自然性と `sourceIso_trans` で中間頂点像を消去する。
任意の `TransportSquareLift.comparison` と元の transportIso の一致はまだ未証明。
今回回収したのは元の canonical な持ち上げについての厳密な定義式である。
その選択照合後、元の coherent 合成四角形の実持ち上げで二段比較を計算する。
`pointedReverseKanCompositionTransportFamily` は逆豊穣圏の一点を終対象に固定するため、
終域後合成の自然性だけから二射の指定評価比較の一致を結論しない。
Ncomp が閉じてから、`spaceCompositionZero_morphism_coherence` と Nlong で a④へ進む。
`TargetEndpointIso_trans_universal` や反映判定は未証明の値式の代用にしない。

## 検証と保存

- 保存 009f79677：固定評価・二段指定比較・Ncomp 帰着。7199 jobs、9142 宣言監査通過。
- 保存 58f9c4d47：単体の後合成・一辺追加。1694 jobs、9193 宣言監査通過。
- 今回の個別対象：元の合成 prism の自然性1780 jobs、
  canonical Hom 比較の自然性1779 jobs、右 slice 後合成則1778 jobs、いずれも成功。
- 追加分の三対象統合ビルド1784 jobsで成功。
  専用公理監査9349宣言で通過（標準三公理のみ）。
- 相対延長の後合成自然性：四モジュールの対象ビルド2651 jobs、
  専用監査9390宣言で通過（標準三公理のみ）。
- 元の指定対角比較の後合成貼り合わせ：二モジュールの対象ビルド2691 jobsで成功。
  これを含む専用監査9416宣言で通過（標準三公理のみ）。
- 元の持ち上げ四角形の三辺比較の回収2072 jobs、native 像と sourceIso の一致3219 jobs、
  指定 sourceIso 合成則2684 jobs。三対象統合3225 jobsで成功。
  新規七葉を含む専用監査9553宣言で通過（標準三公理のみ）。
- 専用監査は読込済み FilteredExchange の生成宣言を含む全宣言を宣言元で選別し、
  推移的な依存公理を検査する。上記の監査は標準三公理のみ。
- 以後のコミット本文には、構成した宣言と公開名・検証対象と jobs 数・監査結果を記録する。
- 他レーンの変更は含めず、所有パスを明示してコミットする。

## 旧 F1b の完了記録（X の作業対象外）

以下は B1〜B5 と F2 第1部の完了記録。旧 F1B の straightening 非依存という制約は
その旧構成についての記録であり、X が読み取り専用の F1 API を利用することを妨げない。
凍結時の詳細は本ファイルの X 着手前の履歴と末尾の archive に保持される。

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

実施記録・現在地の詳細・型一覧は [archive/infinity-core-F1b-log.md](../../infinity-core-F1b-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
