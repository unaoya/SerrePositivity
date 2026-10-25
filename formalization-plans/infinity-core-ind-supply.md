# Ind-S 供給計画 v3

## 引き継ぎ（2026-10-25 20:11 JST、Ind-S (8) 完了）

- 所有：F1/・F1B/・Core/ の新規の葉と、対応する三監査スクリプトの末尾追記。
- 既存の深層ファイルは編集しない。F2/ は読み取り専用。K-B・Sp・EInfinity は import しない。
- 今回：(8) E2-S (7) 向け、豊穣表現可能関手の coherent 全図式比較。計画正本は本ファイル。
  `infinity-core-F1.md` は Ind 所有なので編集しない。
- (5)：`d4062a19f` で L3 指定型の全族写像・厳密な底・全 fiber 回収を供給済み。
  同じ写像について指定点の値照合から fiber 内の頂点同型を反映する公開補題も供給済み。
  K-B 所有の具体的な恒等点への代入は未検証であり、K-B-S 全体の完成とは数えない。
- (4)：`5686de2be` で内ホーン閉包と小模型、`14923a0d5` で指定逆三角形の保持と
  大きい標的への延長を保存済み。境界・可逆 path の同じ小模型への因子化を接続し、
  `IsLocalization.ulift`・`isLocalization_ulift_iff` まで対象ビルドが通過。
- 現在地：(8) 完了。全図式主定理 `representableHomCoherentIso` の対象ビルド
  （4168 jobs）、要求型への直接適用、8葉120宣言の公理・依存・禁止仮定監査、F1 全監査が通過。
- 主要宣言：`representableHomFunctor`・`representableHomCoherent`・
  `representableHomCoherentIso`・`representableHomCosliceIdentity_value`。
- 依存と提供：2026-10-25 ユーザー承認で、(8) の新規 F1 葉に限り、指定された既存
  HomInfinityBifunctor と分類側の4入口経由の KST.Spectra の推移的 import を許可。
  新規葉の KST 直接 import、EInfinity、F2 は禁止。F1B 監査へは登録しない。
  提供先は E2-S (7)。公開名・コミット・import 入口をユーザー経由で中継する。
- 未コミット：なし（自身の対象は本コミットで保存）。他レーンの作業は触らない。
- 既知の問題：既存の逆方向 import 4経路の分割は第 I 段終了時の停止窓に R が行う。
  レーン時間中の深層編集はしない。x を動かす全比較の自然性は今回は未公開（任意追加項目）。
- 残り：(8) の必須供給残件なし。x 方向の追加自然性と R の上流整理は上記の通り。
- 次の一手：公開名・コミット・import 入口をユーザーへ報告し、E2 へ中継して停止する。
- 停止条件は foundations §8 に従う。ビルド失敗だけで停止しない。
  以後のコミット本文には変更・検証・残件の実施記録を書く。

## 所有と依存

- 新規葉は既存の Core/F1/F1B 公開界面を使う。既存モジュールへの逆流を作らない。
- 許可済み逆方向 import：D の `Derived.FunctorIsoConstantEdges`・
  `PinchedSliceCompositionRealization`・`ConstantEdgeFamily` を閉包外の新規 F1 葉から
  読み取り専用で利用可。第 I 段終了時に R が整理する。
- Ind に許可済みの `Stable.PosetSubtypeNerve`・`Stable.FinitePosetNerve` は
  読み取り専用の供給経路。今回の (4)/(5) の追加葉では未使用。
- (4) は no-straightening を守る。`Stable.UniverseVertexIso` は直接 import 不可。
  軽量な準重複 `Core.UniverseEdgeTransport` の `UniverseEdge.invertible_up/down` を使う。
- P の `nerveOrderIso`・`spaceUniverseDiagram...` は F2 を含む閉包の循環により不可。
- 追加の ModelCategory 仮定・供給結論そのものの存在仮定・新公理は導入しない。

## (5) 三段目と公開界面

1. [x] 相対関手空間で scaffold 全族を降下し、重み付き Kan 単位を構成する。
2. [x] 同じ族を小さい空間値 unstraightening へ写し、底の厳密等号を保つ。
3. [x] 全ての底頂点で、同じ全族写像の fiber 制限を標準値回収により元の Kan 単位へ戻す。
4. [x] 同じ fiber 回収同型から、あらかじめ指定された点との値同型を頂点同型へ反映する。
   K-B の具体的な恒等点との値同型の代入・接続は K-B 側で未検証。
5. [x] L3 の要求型を Lean で再検査し、対象ビルド・葉公理監査・F1 全監査を通して保存する。

公開名（`SerrePositivity.InfinityCategories` 以下。正確な namespace は各葉参照）：

- `exists_cocartesianKanUnstraighteningUnit`
  (`F1/Diagrams/CocartesianKanUnstraighteningUnit`)。
  元の cocartesian fibration `p`、Kan 置換関手 `R`、単位 `η` から同じ `f` と
  `hf : f ≫ projection = p` を構成し、全ての `c` で
  `fiberMap(f,hf,c) ≫ canonicalValue ≫ R.map(evaluate p c)` と
  `η.app(vertexFiber p c)` の FunctorIso を供給する。
  本体には `η` の anodyne 性すら不要。
- `cocartesianKanUnstraighteningUnit_pointIso`
  (`F1/Diagrams/CocartesianKanUnstraighteningUnitPoints`)。
  `η` の anodyne 性のもと、上の同じ `f/hf` と fiber 回収同型を入力し、
  指定点 `v` の標準値と元の点 `x` の Kan 単位値の VertexIso から
  `VertexIso (fiberMap(f,hf,c)(x)) v` を返す。点を選び直さない。
- `cocartesianKanUnitEvaluation_isQCatEquivalence`：点反映に使う評価比較の同値性。
- `relativeFunctorPre_isQCatEquivalence_of_firstVertexLocalization`：
  追加の相対初頂点補題（`5221e4db3`、既に K-B 消費済み）。

検証済み：最終対象ビルド、L3 指定型の直接適用例、公開主定理の公理、
最終追加葉 35 宣言の公理監査、F1 全監査。許容公理は propext・Classical.choice・Quot.sound。
残り：K-B 所有の `weakIdentityQuotientFiberPoint` 等を同じ全族写像に代入する消費側接続。
この残件を一般 F1 の不足と混同しない。

## (4) 順方向の三段目と公開界面

1. [x] 小さい像・小さい和と、有限単体集合の像が増大列の一段に入る補題。
2. [x] ambient quasicategory 内で小さい内ホーン充填閉包を構成する。
3. [x] 閉包を小さい quasicategory に縮小し、同じ包含で全小図式を厳密因子化する。
4. [x] 逆辺と二つの逆三角形を種に追加し、指定可逆辺を保存する小模型を作る。
5. [x] 大きい標的への局所化延長と、全前合成の充満忠実性を小模型から回収する。
6. [x] `IsLocalization` の ULift 持ち上げと既存降下を合わせた iff を公開し、監査・保存する。

保存済みの公開名（namespace `SerrePositivity.InfinityCategories.SmallSubcomplex`）：

- `small_range`・`small_iSup`・`exists_range_le_stage`
  (`Core/SmallSubcomplexStages`)。
- `innerHornClosure`・`le_innerHornClosure`・`small_innerHornClosure`・
  `innerHornClosure_quasicategory` (`Core/SmallInnerHornClosure`)。
- `model`・`modelIso`・`model_quasicategory` (`Core/SmallSimplicialModel`)。
- `Hull`・`hull` (`Core/SmallQuasicategoryHull`)。
  `Hull.factor` は `range f ≤ seed` を満たす任意の持ち上げた小さい源の図式を、
  同じ小模型と同じ包含に対して厳密に因子化する。

既存の供給済み降下：`IsLocalization.of_ulift`・`invertsEdges_ulift_iff`
(`F1B/Localization/UniverseDescent`)。
段目 3 の小模型だけでは ambient での可逆性を反映しないため、段目 4 を経由する。
最初の Core 4 葉の対象ビルドと 72 宣言公理監査は通過済み。

段目 4〜5 の追加公開名：

- `inverseWitnessSeed`・`small_inverseWitnessSeed`・`inverseWitnessSeed_reflects_edge`
  (`Core/SmallInverseWitnessSeed`)：同じ逆辺と二つの実三角形を保持する。
- `markedHull`・`markedHull_reflects_edge` (`Core/SmallMarkedQuasicategoryHull`)。
- `exists_small_inverting_factorization` (`F1B/Localization/SmallMarkedFactorization`)：
  元の持ち上げた図式を厳密に因子化し、指定辺の反転を保持する。
- `LocalizationUniverse.functorIso_ulift` (`F1B/Localization/UniverseMorphismUp`)：
  同じ実関手同型を持ち上げる軽量入口。
- `IsLocalization.exists_extension_ulift` (`F1B/Localization/UniverseExtension`)：
  任意の大きい quasicategory を標的とする反転関手の実延長。
- `LocalizationUniverse.fullyFaithful_ulift`・`precomposition_fullyFaithful_ulift_target`
  (`F1B/Localization/UniverseFaithfulUp`)：小さい標的を持ち上げた場合の充満忠実性。
- `isFullyFaithful_of_positive_boundary`
  (`F1B/FunctorCategories/PositiveBoundaryFaithful`)：正次元境界の持ち上げからの判定。

追加の Core 二葉 14 宣言、延長三葉 11 宣言の公理・no-straightening 監査通過。
Core 全監査、F1B 全監査（延長三葉まで）も通過。

最終公開名（`F1B/Localization/UniverseAscent`）：

- `IsLocalization.precomposition_isFullyFaithful_ulift`：任意の大きい標的での全前合成の充満忠実性。
- `IsLocalization.ulift`：`IsLocalization F W` から
  `IsLocalization (SSet.uliftFunctor.map F) (ULift.up '' W)`。
- `isLocalization_ulift_iff`：上の持ち上げと元の局所化性の iff。

源・標的の quasicategory 性、ModelCategory、局所化の追加存在証明は仮定しない。
証明は `Core/SmallHullFactorization`・`EquivalencePathReplacementNaturality` と
`F1B/FunctorCategories/SmallTargetDiagrams`・`SmallTargetBoundary` の新規葉へ隔離。
元の正次元境界とその二関手族・可逆 path 族・底単体を同じ marked 小模型へ移し、
小さい標的での充填を元の正方形へ厳密に戻す。

最終検証：UniverseAscent 対象ビルド 1680 jobs、元の要求型の直接適用例と iff、
主定理の公理確認、最終 Core 8 宣言・F1B 13 宣言の葉監査、Core/F1B 全監査が通過。
追加閉包は no-straightening、許容公理は標準三つのみ。F1 全監査は (5) 保存時に通過済み。

## (6) 弱変形による局所化源の移送

1. [x] 規約・既存の変形局所化界面・要求型を確認する。
2. [x] 指定辺を保つ制限と、反転関手圏上の全変形同型を構成する。
3. [x] 相互逆の制限同値を既存局所化の前合成同値へ合成し、本体を公開する。
4. [x] 恒等射から合成への逆向き H・K の版を同じ葉で公開する。
5. [x] 対象ビルド・三監査・公開型・禁止仮定を検査し、本文記録付きで保存する。

要求：i : A ⟶ B、r : B ⟶ A が WA・WB を相互に保ち、
H : Homotopy (r ≫ i) (𝟙 B)、K : Homotopy (i ≫ r) (𝟙 A) の点辺が WB・WA に入るとき、
IsLocalization q WA → IsLocalization (r ≫ q) WB。H・K が逆向きの場合も供給する。
源・標的の quasicategory 性、ModelCategory、局所化の追加存在仮定を加えない。
配置：新規 `F1B/Localization/WeakDeformationSource`。no-straightening を維持する。

公開名（namespace `SerrePositivity.InfinityCategories`）：

- `isLocalization_of_weakDeformation`：合成から恒等射への H・K による移送。
- `isLocalization_of_weakDeformation_reverse`：恒等射から合成への H・K による移送。
- `WeakDeformationSource.restriction`・`restriction_ι`：反転関手全族の制限と厳密な包含照合。
- `WeakDeformationSource.restrictionEquivalence`：全関手同型を保持する相互逆の制限同値。

両主定理の引数は i・r・q・WA・WB・相互保存・H・K・点辺所属・hq。
A・B・D の quasicategory 性は仮定しない。逆向き版は元のホモトピーを逆転させず、
反転関手族上で作った全同型を逆にして同じ普遍性を使う。
追加葉は `DeformationLocalization` のみを import し、既存定理を変更しない。

検証：対象ビルド 1980 jobs、要求された両向きの型への直接適用、両主定理の公理確認、
葉24宣言の公理・禁止依存・公開型中の ModelCategory 検査、Core/F1/F1B 三監査が通過。
許容公理は propext・Classical.choice・Quot.sound のみ。F1B 監査登録は末尾追記のみ。

## (7) 内ホーン充填閉包の濃度評価

1. [x] 規約・既存の閉包・暫定型を確認する。
2. [x] 有限個の面でホーン写像を数え、充填一段の非退化単体数を評価する。
3. [x] 各既存 innerHornStage と可算和の既存 innerHornClosure の μ-small 性を証明する。
4. [x] 既存 model・canonical hull と、Small 仮定不要の有界 Hull の存在へ移す。
5. [x] 対象ビルド・公開型・公理・禁止依存・三監査を通し、実施記録付きで保存する。

仮定は正則 μ と ℵ₀ < μ。強極限性は仮定しない。非退化表示から各次数を評価し、
ホーンからの射を有限個の面の Yoneda 値へ単射に送る。充填像は次数ごとに有限で、
充填添字と全段階の可算和を正則性で評価する。既存 Small の証明は不変。
F2 の IsKappaSmall は `Cardinal.mk K.N < μ` の定義だけなので、P は Core の同型の不等式を
定義展開で使える。F2 からの import、他レーンの証明のコピー、新しい小ささ述語は導入しない。
任意の Hull が μ-small とは主張せず、既存 canonical hull とその同じ包含・因子化を保持する。

公開名（namespace `SerrePositivity.InfinityCategories.SmallSubcomplex`）：

- `hasCardinalLT_innerHornData`・`hasCardinalLT_innerHornStep`・`hasCardinalLT_innerHornStage`
  (`Core/InnerHornClosureCardinal`)：同じ充填試験族・一段・各段の濃度評価。
- `hasCardinalLT_innerHornClosure`・`cardinal_innerHornClosure_lt`（同じ葉）：
  宇宙多相な HasCardinalLT と、同じ宇宙での `Cardinal.mk (innerHornClosure A).toSSet.N < μ`。
- `hasCardinalLT_model`・`hasCardinalLT_hull_obj` (`Core/SmallHullCardinal`)：
  既存 model と既存 canonical hull の対象の μ-small 性。
- `hullOfCardinalBound`・`hasCardinalLT_hullOfCardinalBound_obj`・`exists_hull_hasCardinalLT`
  （同じ葉）：濃度から宇宙的 Small を放電し、既存 Hull の構造全体と μ-small 性を得る。

補助葉 `Core/SimplicialCardinalBounds` は非退化単体から各次数への評価と、その可算和による逆向きを供給する。
HasCardinalLT は mathlib の宇宙多相な既存述語。既存 F2 の定義を複製しない。
公開型の直接適用例は F2 の定義だけを読み、閉包・全段・model・Hull の既存 IsKappaSmall を検査した。
本体の import 閉包には F2・KST・EInfinity・straightening はない。

検証：SmallHullCardinal 対象ビルド 1409 jobs、同じ宇宙の IsKappaSmall に対する
閉包・各段・model・Hull の直接適用、宇宙を分けた閉包・model・Hull の直接適用、
18宣言の公理・禁止依存・ModelCategory／強極限仮定監査、Core/F1/F1B 三監査が全て通過。
許容公理は標準三つのみ。既存の深層三ファイルは不変、監査登録は Core 末尾への追記のみ。

## (8) 三段目と公開界面

1. [x] 規約・要求型・既存の相対 Hom 比較と分類界面を確認する。
2. [x] 元の豊穣合成の curry を持つ Hom 関手と、小さい coherent nerve 上の全実現を構成する。
3. [x] 同じ恒等射の点から coslice → unstraightening の全空間比較を作り、
   実際の fiber 制限を全高次の豊穣作用と照合して同値を示す。
4. [x] 始点固定 twisted arrow の分類との全図式 FunctorIso を公開する。
5. [x] 同じ全空間比較の恒等点を厳密に回収する。x を動かす全比較の自然性は未公開。
6. [x] 8葉120宣言と F1 を最終監査。所有分を本コミットで保存し、公開名・入口を報告して停止する。

要求型：D : Type u、Category.{u} D、SimplicialCategory D、全 sHom Kan。
始域は uliftNC(D)、値域は SpaceInfinity、各単体の作用は s.down.comp SSet H_x。
終域図式は homInfinityCovariant (coherentNerveVertex x)。値同値だけからは導いていない。

公開名（namespace SerrePositivity.InfinityCategories）：

- `representableHomFunctor`：元の Hom の Kan 対象と `curry (eComp SSet x y z)` の作用。
  `_obj`・`_map` は厳密な等式（Coherent/RepresentableHomFunctor）。
- `representableHomCoherent`：指定された全単体での後合成。
- `representableHomCoherentIso`：この全実現から指定された共変 Hom 全図式への FunctorIso
  （Coherent/RepresentableHomInfinity）。`_app`・`_vertex` も供給。
- `representableHomCosliceComparison_isQCatEquivalence`：恒等点から作った一つの大域射の同値性。
- `representableHomIdentityCoefficient_value`・`representableHomCosliceIdentity_value`：
  同じ恒等係数と始点 fiber の値は元の豊穣恒等射の零単体を厳密に回収する。
  これらは対象宇宙を持ち上げた圏上で使う（Coherent/RepresentableHomCoslice）。
- `KanCosliceComparison.map`・`projection`・`identity`・`fiber_actionIso`：
  指定点からの全空間写像・厳密な底・恒等錐・全反転 Hom 上の作用の照合。
- `CoherentObjectLift.nerveIso`・`nerveIso_vertex`・`realization`：Hom を変えない対象宇宙の表示変更。
- `covariantHomIsoOfCosliceEquivalence`・`covariantHomIsoOfDisplayedCosliceEquivalence`：
  同じ全空間同値から、元の共変 Hom 全図式への分類と表示変更。

主経路：対象宇宙だけの持ち上げ → 同じ恒等点からの全 coslice 比較 →
全 Hom 上の作用と豊穣単位則 → 同じ全空間の同値 → 小さい表示への降下 →
始点固定 twisted arrow の分類 → 元の homInfinityCovariant。
同型の成分が別に指定された homInfinityCovariantValueEquivalence の逆射と一致するとは主張しない。

2026-10-25 ユーザー承認の import 例外（(8) の新規 F1 葉のみ）：

新規 Yoneda/CovariantCosliceClassification の既存上流への入口は次の4本。
これらを経由する KST.Spectra の推移的 import を許可し、直接 import は禁止する。

- F1/MappingSpaces/HomInfinityBifunctor。
- F1/Yoneda/YonedaSourceBaseChange。
- F1/TwistedArrow/SourceInitial。
- F1/StraighteningLeft/LeftStraighteningEssentialSurjectivity。

R の第 I 段終了時の停止窓での分割対象（レーンでは変更しない）：

- F1/Limits/ContractibleKanTower → KST/Spectra/FibrationTowerLimitCone。
- F1/Limits/InverseSequenceQuasicategory → KST/Spectra/FibrationTowerLimitCone。
- HomotopyLimits/FibrationComponentTransport → KST/Spectra/FibrationIntervalLifting。
- HomotopyLimits/FibrationComponentTransport → KST/Spectra/FiberComponents。

監査 (8) の項に例外を明記。新規葉のソースの直接 KST import、EInfinity/F2 閉包、
Spectra 以外の KST 閉包を拒否し、全宣言の標準3公理・ModelCategory 不使用を検査する。
F1B/Core の監査は変更しない。
ログ：`/tmp/ind-s8-final-build.log`・`/tmp/ind-s8-final-public-type.log`・
`/tmp/ind-s8-final-leaf-audit.log`・`/tmp/ind-s8-final-f1-audit.log`。
