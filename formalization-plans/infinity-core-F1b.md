# I-1 a7：X レーン（交換定理）の正本

> **v3 追記（2026-10-25）**：凍結中の I-1 a7 を X が担当する。
> a7 の計画・現在地の正本は本ファイル。Ind 全体の正本は infinity-core-F1.md。
> 旧 v3 の「Ind に統合・8時間上限」は凍結時の記録であり、今回の上限は
> 着手から48時間（2026-10-27 13:07:39 JST）とする。

## 所有範囲と完了条件

- 着手：2026-10-25 13:07:39 JST。上限で未完なら不足を記録して停止する。
- 所有：F2/FilteredExchange/ の今回新設した葉、
  scripts/audit_infinity_f2_exchange.lean、および本計画ファイル。
- F2/Ind・Compact・Idempotent・F1・F1B・Core は読み取り専用。
  既存の集約と scripts/audit_infinity_f2.lean は変更しない。
- foundations.md §6・§8、foundations-progress.md の Ind I-1、
  infinity-core-F1.md と本ファイルの凍結時引き継ぎを読了。
- X は直接経路の a③・a④・b①（cospan 形状の交換）を証明する。
  全有限形状への帰納 b② と公開 b③ は Ind の I-2 d′ に移管する。
  strict 図式や端点の一致だけで完了とはしない。指定比較・全パラメータを保持する。
- sorry・追加公理・文献を仮定にした入力は使わない。
  許す公理は propext・Classical.choice・Quot.sound のみ。
- b① が閉じたら公開名を報告し、Ind の有限形状帰納へ渡す。
- 2026-10-25 14:44 のユーザー承認による分担変更：Ind は P の poset 交換の
  ℵ₀ 特殊化による代替経路 I-2 d′ を並行実施。48時間の上限と他規約は維持。

## 三段目（依存順、2026-10-25 14:44 分担変更反映）

| 番号 | 工程・所有 | 完了条件 | 現在地 |
| --- | --- | --- | --- |
| 1 | X：a③ Ncomp | 元の零面値・終点比較・raw 二辺値比較の因子式 | 作業中 |
| 2 | X：a④ 普遍三角形の一致 | Nlong と Ncomp を代入し、同じ零面値を消去 | 未着手 |
| 3 | X：b① cospan 形状の交換 | 指定二三角形・path を保つ全錐比較と保存、直接経路の cospan 交換 | 未着手 |
| 4 | Ind：b② 有限形状帰納と交換入力の実証拠化 | 部分極限・接着の同時帰納、全有限形状の交換定理 | I-2 d′ へ移管 |
| 5 | Ind：b③ 公開・集約・監査 | 公開し、IndFiniteLimitExchangeInput に渡せることを検証 | I-2 d′ へ移管 |

X は工程1〜3の各段階で対象ビルドと専用公理監査を行う。
工程4・5は Ind の所有であり、X の完了条件には含めない。

## 現在地：1 a③ の指定評価比較の合成則

14:44 分担変更後も工程1を続行中。同じ固定底辺を持つ任意の
`TransportSquareLift` の比較値が、元の `TransportIntervalSquare.transportIso` と
一致する補題を構成・検証した（3251 jobs）。専用監査は9723宣言で通過、
標準三公理のみ。公開名はいずれも F2 名前空間の
`TransportSquareLift.comparison_eq` と
`TransportSquareLift.comparison_eq_transportIso`。
固定初期図式上の終点比較の恒等性、元の区間比較の始点正方形、左右・上辺の
指定自然性から、中間の頂点比較を消去した。全パラメータと元の指定同型を保持。
さらに固定底辺の条件を外し、左下角だけを固定した任意の実四角形について
`TransportSquareDiagram.comparison_eq` と
`TransportSquareDiagram.comparison_eq_transportIso` を構成した（3264 jobs）。
専用監査は9831宣言で通過、標準三公理のみ。
下辺の指定比較を右辺に沿って輸送し、四つの元の指定比較を貼った値を使う。
元の普遍 prism の区間比較が恒等であることも
`leftFibrationPrism_transportIntervalIso_universal_refl` で確認した。
係数制限についても、元の選択済み sourceIso・四辺比較・四角形全体の比較の
値を保つ自然性を構成した。公開名は
`diagonalFiberTransport_sourceIso_precomp_heq`、
`TransportSquareDiagram.comparison_precomp_heq`、
`transportIntervalSquare_transportIso_precomp_heq`（3309 jobs）。
専用監査は9852宣言で通過、標準三公理のみ。
元の始点同型の自然性も
`transportIntervalSquare_transportIso_source_naturality` で証明した（3317 jobs）。
専用監査は9881宣言で通過、標準三公理のみ。
同じ普遍始点比較から関手空間上の `transportIntervalSquareSourceActionIso` を作り、
その全成分が元の transportIso に一致することを確認した。係数は任意の単体集合。
定値終辺の元の指定消去についても、係数・始点同型の自然性を証明した。
公開名は `transportIntervalSquare_constantTopIso_source_naturality`。
元の Kan 合成へ戻し、
`coherentKanRightCompositionMovingIso_source_naturality` と
`coherentKanRightCompositionDiagonalIso_heq_moving` を構成した。
右 Hom の点評価比較の元の逆も
`pointedRightFamilyTransportIso_symm_heq_moving` で同じ moving 比較へ戻した。
両対象の統合ビルド5697 jobs、専用監査9921宣言で通過、標準三公理のみ。
同じ実三角形の三本の実辺から、元の指定合成比較を回収する
`TransportTriangleDiagram.constantTopIso_eq` を証明した。
`transportTriangleDiagramOfSimplex` と `transportTetrahedronFaceOfSimplex` は
同じ実二単体・四面体の実頂点と実三辺を保つ。別々の面の充填は選ばない。
`exists_simplexInitialLift` は任意の底の実単体族を、元の初期値を固定して
left fibration に持ち上げる。`simplexSharedFacePrism` は隣接面の共有辺の
厳密等式、`transportTriangleSimplex_bottomPrism`・`_leftPrism`・`_rightPrism` は
折り畳み後の実三辺が元の面の制限そのものであることを保証する。
`leftFibrationPrism_transportIntervalIso_shared_prism_heq` で、共有する実辺の
射影から底の族の等式を導き、元の選択済み区間比較の値も保持した。
対象ビルド3341 jobs、専用監査10006宣言で通過、標準三公理のみ。
推移的 import は2123プロジェクトモジュール、他レーンの未保存依存は0。
さらに同じ実四面体の六本の共有辺の底の族と元の指定比較を照合した。
`TransportTetrahedronDiagram.shared_curve01`〜`shared_curve23` と
`shared_comparison01`〜`shared_comparison23` は、実辺の等式からの帰結。
四面の元の指定合成比較は `comparison012`・`comparison013`・`comparison023`・
`comparison123` で共通六辺上に表示し、`comparisonAlong_heq` が元の値を保持する。
`TransportTetrahedronDiagram.comparison_coherence` で四面の合成則を証明した。
元の始点自然性と四面の実三辺貼り合わせ式から中間因子を消去しており、
高次整合性の新しい仮定はない。`exists_transportTetrahedronDiagram` は
任意の底の実四面体族について、元の初期値を固定する同じ実全四面体を与える。
統合ビルド3360 jobs、専用監査10118宣言で通過、標準三公理のみ。
推移的 import は2142プロジェクトモジュール、他レーンの未保存依存は0。
元の合成四角形の全図式も `coherentCompositionSquare_triangle_recovery` と
`coherentCompositionSquare_triangle_recovery_precomp` で、同じ三角形の折り畳み
から厳密に回収した。右 join prism の先頭制限の計算によるもので、四辺一致
だけへの弱化ではない。`transportTriangleBaseOfLift_eq_coherentKanSquare` により、
元の Kan 三角形を被覆する実三角形の底を元の合成四角形そのものへ戻した。
`coherentSimplexAppendMorphism_face_penultimate` は追加した射の直前の面を
元の後合成へ同定する。`coherentSimplexAppendMorphism_reindex` はその追加を
二重の最終点固定添字制限に関して全 Hom ごと自然にする。
統合ビルド3407 jobs、専用監査10137宣言で通過、標準三公理のみ。
推移的 import は2161プロジェクトモジュール、他レーンの未保存依存は0。
最後を保つ任意の制限（零次元も含む）へ追加操作の自然性を拡張した。
公開名は `coherentSimplexAppendMorphism_lastPreserving`。
`coherentSimplexAppendMorphism_terminalEdge_of_eq` により、元の追加射の終辺全体を
固定した。`coherentRightSliceAppendCone` は元の全錐と指定射を同時に保持し、
全添字自然性と元の前面・終辺の厳密回収を持つ。
`coherentRightSliceAppendEdge` で同じ射の辺上の slice への実写像に束ねた。
`coherentRightSliceAppendEdge_front` は任意の元の全錐族を始端側の実全面から戻す。
`coherentCompositionAppendTetrahedron` で元の二 Hom 全係数と同じ追加射を持つ
単一の実四面体族を構成した。四面の元の合成図式への同定はまだ未証明。
統合ビルド2159 jobs、専用監査10192宣言で通過、標準三公理のみ。
推移的 import は2181プロジェクトモジュール、他レーンの未保存依存は0。
元の合成三角形へ終点を追加する `coherentCompositionConeTetrahedron` も構成し、
`coherentCompositionConeTetrahedron_face012` で 012 面全体を元の三角形へ同定した。
`coherentCompositionConeTetrahedron_face012_precomp` は全同時係数制限でも保持する。
対象ビルド2173 jobs、専用監査10211宣言で通過、標準三公理のみ。
推移的 import は2185プロジェクトモジュール、他レーンの未保存依存は0。
Ncomp 本体は未完。残る 013・023・123 面を元の合成図式へ同定する。
係数付きの標準三角形錐と元の右 join prism 三角形の一致も次の計算対象。
その後、証明済みの四面体則から元の二段評価と合成評価の指定値へ接続する。
a④・b① は未着手であり、これらの補題だけで完了とは主張しない。


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

実施記録・現在地の詳細・型一覧は [archive/infinity-core-F1b-log.md](archive/infinity-core-F1b-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
