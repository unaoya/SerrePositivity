module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.Generators
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CompactEndpoints
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndCandidate
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSource
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.SequentialPieces
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CompactFactorization

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageCandidates
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.SourceCosliceColimits

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CompactPartialColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CompactIndCandidates
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.RefinementCardinals

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.EndpointCompactCardinals
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceEdges

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ArrowEndpoints
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageSpanColimits

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImagePushout

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageEdges
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceInitial
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceArrows
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageCommonPresentations
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageSmallCoproducts
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageCoproductColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.SourceArrowFiber
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceFiberPullback
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceFiberEquivalence
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageAllFiniteColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageCancellation
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CompactCoconeFactorization
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CompactFactorizationTriangle
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedArrowEvaluation
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceProjection
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceTransport
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceFiniteColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceCoproducts
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceFilteredColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageSourceCandidates
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceTerminalExtension
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceTerminalMapping
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.SequentialColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceTerminalCoslice
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceRetractionSpace
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedTargetIdentityTerminal
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageSmallColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceSmallColimits

/-!
概要：P-f レーンの独立集約と引き継ぎ。既存の Presentable 集約は編集しない。
方針：N の局所対象を再利用し、小さい生成辺族を明示する。
規約：局所置換の存在を未証明の入力で置き換えて完成扱いしない。
使われ方：HTT 5.5.4.15 の実装作業。

## 現在の工程（2026-10-25、ユーザーが設計変更を採用して再開）

三段目：f1 [x] 生成元の局所性と compact 端点、f2 [ ] 飽和射クラスの小生成と
presentable 性、f3 [ ] 固定始域の終対象＝局所置換の存在、f4 [ ] 反射関手と普遍性、
f5 [ ] 強飽和性との同定・監査・引き継ぎ。
f2 の検証済み範囲：元の飽和射圏の小余極限、全小余極限を保存する全部分包含、
周囲で compact な射の小さい模型、その包含先での compact 性。
元の圏・射圏の共通正則 accessible 濃度、生成射と両端点の compact 性、
全生成射を含む小さい compact 候補まで構成した。
その候補の包含を全自然同型で回収する実 Ind 比較も構成済み。
f3 の準備：固定始域の全 coslice 部分圏と、同じ始域から閉包内の実辺を回収する入口。
5.5.4.13 の添字側：seed と増大可算列の和集合の filtered 性・列の final 性・小ささ。
各段階の compact 源からの任意の指定 coslice 点を、同じ余錐脚の上の実辺で因子化する入口。
compact な始対象像を持つ left fibration の指定点を、同じ余錐脚の上で一段へ因子化した。
これを小さい compact 図式の余極限始対象へ適用し、その全余錐の一段への因子化も証明した。
既存の部分余錐を固定する相対延長は未構成。
指定した元の辺を合成辺、元の filtered 余錐脚を後半辺とする実二単体も回収した。
二つの実表示を結ぶ coherent 交互列と共通部分余極限は未構成。
全射の filtered 生成性・飽和射圏全体の accessibility は未証明。
P のコミット 1381907fe の引数分離済み indComparison_isFullyFaithful_of_compact を使用。
未証明の presentation を渡さず、実比較の充満忠実性と同型飽和した実像の
κ-accessibility・元の射圏での κ-filtered 余極限閉性・包含の保存性を構成した。
同じ濃度で compact な閉包内の全射と元の全生成射を含む実像も構成済み。
実像の各頂点を厳密な頂点とする単一 filtered 表示と、周囲で compact な Yoneda 像を
保持する実比較も構成した。その表示の全項の周囲での compact 性も保存する。
濃度変更境界を明示すると、compact な閉包内射の小さい poset 余極限は
同じ compact 性と閉包への所属を保ち、その全部分圏にも実際に余極限が存在する。
指定濃度からの交換境界を持つ、生成射・両端点・元の圏と射圏の共通濃度も構成済み。
P の公開済み compact 保存濃度を二つの端点評価に使い、周囲で compact な
全候補射の両端点も compact となる共通濃度を構成した。生成射だけの条件ではない。
固定始域圏の任意の指定辺は、終域射影で元の強飽和生成閉包に属する。
周囲で compact な Yoneda 像と全 compact 閉包射の被覆を持つ実像について、
有限 poset 全図式の指定余極限閉性を、実 Ind の単一表示と全普遍余錐族から証明した。
その実像内の有限 poset 余極限の存在と、包含の指定全余錐の保存性も構成済み。
元の標準 span ホーンにも同じ閉性・余極限の存在・保存性を厳密な形状同型で移した。
同じ濃度で端点評価二本と恒等射図式を compact 保存にし、元の全対象上の
恒等射を実像に回収した。元の任意の pushout 四角形を、二本の恒等射と
下辺・上辺からなる射圏内の実 pushout へ写し、辺クラスの pushout 保存も証明した。
可逆な元の辺を、区間最小値の指定ホモトピーで始点の恒等射と射圏内で同型にした。
実像を元の辺集合として読み、生成閉包への包含と全可逆辺の所属も証明した。
元の恒等射は固定始域の閉包内 coslice に入り、その圏の実始対象となる。
全余錐族から元の飽和射圏への関手を作り、各頂点の指定脚と終域射影を保持した。
P-10 の公開コミット 49c7fee8e の共通 filtered 添字を使い、小さい辺族の
compact 表示を同じ添字へ揃えた。全余錐の元の頂点・普遍性・全項の compact 性を保持する。
各成分の全図式と普遍余錐を一つの関手圏内の図式・普遍余錐にまとめ、
非可算正則 μ で μ-small な離散形状について、元の指定余積の実像への所属を証明した。
compact な閉包内射の任意の小さい余積を、有限部分余積の全左 Kan 図式と
濃度変更後の部分余極限から実像に回収した。これと共通 filtered 表示を合わせ、
任意の実像対象の全小余積閉性、その実像内での存在、包含の指定余積保存を構成した。
同じ濃度の無限冪の評価には IsCardinalChangeBound aleph0 μ を明示する。
固定始域からの射の全族の始点評価は、元の指定始点へ厳密に定値である。
全 coslice と周囲の射圏の厳密な始点 fiber の同値を、公開 vertexFiberSquareIso と
全余錐模型の同値から構成し、元の全射族の回収も証明した。
閉包内射への比較も厳密な始点 fiber に持ち上げ、周囲の全比較の実際の引き戻しと
証明した。さらに厳密な fiber を周囲の fiber の全部分圏として表示し、公開の
isQCatEquivalence_fullSubcomplexRestriction から元の同じ比較の同値性を証明した。
この比較だけでは固定始域圏の余完備性・accessibility はまだ得られない。
強飽和射圏の全部分包含と各端点評価の同値持ち上げ性、各評価の小余極限保存性も構成した。
固定始域 coslice の閉包条件の同型不変性、包含と終域射影の同値持ち上げ性も構成した。
終域射影の inner fibration 性も回収した。left fibration 性は主張しない。
閉包内の指定終域辺に沿う全 coslice の標準輸送辺を、固定始域の閉包内射圏へ持ち上げた。
終対象を仮定した場合、その同じ辺の戻り辺を同じ圏内で回収し、元の終域辺が
ホモトピー圏で split mono となることも証明した。終対象の存在と局所対象性は未証明。
閉包内辺の任意の pushout とその分裂を使い、終対象の終域への写像をホモトピー圏で延長した。
任意の閉包内辺による前合成は同じホモトピー圏で全射となる。写像空間全体の判定は未構成。
終対象への全写像空間の可縮 Kan 性を、包含の充満忠実性で周囲の全 coslice 圏へ移した。
周囲の任意の閉包内の指定余錐も扱い、同じ全写像空間による終対象性の判定も得た。
終対象へ向かう指定余錐を反復 coslice の終対象とし、終対象の恒等余錐への
全写像空間が可縮な Kan 複体であることも、coslice の元の fiber から証明した。
反復 coslice から元の終域の coslice への比較を構成し、その充満忠実性を元の
全部分圏の引き戻しと全 coslice の left fibration から証明した。元の終域から出る
任意の閉包内辺を比較の像へ厳密に回収し、その retraction の全空間の可縮 Kan 性を得た。
その終域を新たな指定始域とすると、元の恒等射が閉包内射圏の終対象となることも証明した。
任意の始域からの局所性へ戻す pushout の写像空間比較はまだ未構成。
弱可縮な小さい通常圏の nerve の始点 join への右包含の cofinal 性を証明し、
全 coslice の同じ指定余錐の普遍性を終域で保ち反映する比較へ接続した。
その形状の固定始域の閉包内射の余極限閉性・内部での存在・包含の保存を構成した。
元の恒等射の始対象性と標準 span を有限セル帰納へ渡し、固定始域圏の大宇宙の
全有限余極限の存在・包含の指定余錐保存・周囲での閉性まで証明した。
有限離散 nerve とその宇宙持ち上げの有限性を非退化単体で検証し、有限部分余積の
全左 Kan 図式と filtered 余極限から、固定始域圏の全小余積・包含の保存・周囲での閉性も構成した。
P の公開コミット 06c0eeae2 の point-fiber 版を使い、同じ固定始域圏と通常の点引き戻しの
同値を、元の全脚族を回収する等式付きで構成した。任意の正則 κ で小 κ-filtered 余極限が
存在し、全脚族が同じ余極限を保存する。accessibility の filtered 生成表示は未構成。
同じ公開 fiber 候補構成を、既に accessible な実 Ind 像の始点評価にも適用した。
任意の指定始域で、全成分 compact 点を被覆する充満忠実な小さい native compact 候補を得た。
この実像 fiber の候補にも filtered 生成性はまだ付けていない。
P-s の公開コミット a8dc9eb19 の望遠鏡の一般入口を使い、Ind 実像と固定始域圏に
元の可算列の保存余極限を構成した。固定始域の周囲の指定可算余極限の閉性も保持する。
全小余積と標準 span を公開の有限セル帰納へ接続し、大宇宙の任意の有限単体集合
形状の余極限の存在・包含の指定余錐保存・周囲での閉性を証明した。有限 poset に限定しない。
元の合成三角形を、最初の辺・中間対象の恒等射・合成辺・最後の辺からなる
射圏内の実 pushout へ送り、最初の辺と合成辺が実像に入れば最後の辺も入ると証明した。
この向きの左消去は検証済みだが、合成閉性と反対向きの消去はまだ未証明。
P-11 の公開コミット 95f5a8f2e の有限余極限・小余積の一般生成入口を使い、
実 Ind 像の全小余極限の存在・包含による指定余錐保存・周囲での閉性を証明した。
同じ実像の既存の accessibility と合わせ、その presentable 性も得た。
二対三則・生成閉包全体との一致はまだ未証明。
固定始域の全 coslice の小余完備性は、反復 coslice と小さい展開形状から構成済み。
同じ P-11 に固定始域圏の小余積・有限余極限を渡し、その全小余極限の存在・
包含の保存・周囲の指定余極限での閉性も証明した。固定始域圏の accessibility と
強飽和射圏全体の accessibility はまだ未証明。P の未公開葉は使用していない。
未証明事項は以下の旧記録のまま残す。「未採用」は旧停止時の状態を表す。

## 旧停止時の引き継ぎ（2026-10-25、設計変更提案時点）

現在地：f1 の生成族・全パラメータ Hom 判定と生成系の比較を検証済み。
f2 の準備として、全生成辺の両端点に共通の正則 compact 濃度を検証済み。
局所置換・反射の存在・局所対象圏の presentable 性は未証明。P-1 f は未完了。

設計変更案：f2 の直接の小対象論法を、原典の飽和射圏経路に変更する。
通常の小対象論法は通常圏の厳密な lifting を構成するため、ho(C) への適用では
全写像空間の局所性を得られない。モデル圏用の LocalFibrantApproximation は
ModelCategory SSet 等を要求し、主経路の入力には使えない。
この案は未採用で、以下の存在性を新たな仮定として追加していない。

残り（依存順、見積もりは実装・ビルド状況により再評価）：
* f2a：強飽和生成閉包の辺を対象とする全射圏の presentable 性
  （5.5.4.13–14、16–40 時間）。compact な射の小さい全部分模型と Ind 表示を構成し、
  pushout・三角形の同時細分で像の強飽和性を証明する。
* f2b：固定始点 x の閉包内射の圏の presentable 性
  （5.5.5.11・14、8–20 時間）。source 評価の fiber を元の coslice と比較する。
  並行 P の e5 の引き戻し accessibility は公開後に読み取り専用で利用する候補。
* f2c：その圏の終対象から、元の x を始点とする閉包内の辺を取り出し、
  pushout と Hom fiber で終点の局所性を証明（5.5.5.12–14、8–20 時間）。
* f3：N の LocalReplacementReflection に接続し、coherent な反射を構成。
  局所対象の accessibility と反映による余完備性から、その presentable 性も証明
  （5.5.4.2・15(2)(3)、8–20 時間）。
* f4：N の LocalReplacementSaturation で生成閉包との一致を得て、同じ反射が
  反転する元の辺との同値を証明（5.5.4.15(4)、4–10 時間）。
* f5：独立集約・監査・主経路の仮定検査・閉包 digest の検査と保存（1–3 時間）。

主要宣言：isLocalObject_range_iff、isLocalObject_range_iff_constantHom_bijective、
localEquivalenceHom_range_iff_constantHom_bijective、localEquivalences_eq_iff_generators、
localEquivalences_eq_iff_localObjects、exists_regular_compactEndpoints。

依存と提供：LocalEquivalences・LocalHomCriterion・Definition・ObjectCompactCardinals を
読み取り専用で利用。公開済みの N の条件付き反射・強飽和性は再実装しない。
一般の任意辺局所化・分数 API を新設する案ではなく、presentable 圏の存在部分に限定する。
禁止 import：Inputs/Homotopy/KanQuillen。既存の Presentable・HomotopyLimits は変更禁止。
所有はこの Localization/ と scripts/audit_infinity_presentable_localization.lean の新規分だけ。
保存対象は All・Generators・CompactEndpoints と独立監査の4ファイル。
既知の問題：存在部分が未実装であり、条件付き N の再包装では解消しない。
次の一手：設計変更案の判断後、f2a の元の射圏と小さい compact 全部分模型から着手する。
-/
