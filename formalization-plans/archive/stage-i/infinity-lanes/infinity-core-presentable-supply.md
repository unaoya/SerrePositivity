# P-s レーン：P-11・P-12 と中継依頼の専任供給

## 引き継ぎ（2026-10-26）

### 現在地
- 状態：ユーザー指示で P-12 を第 II 段／R へ保留。最終 compact 判定は未供給。
- P-f は P-12 を使わず P-1 f を 00:15 に完了。現在の P-12 消費者はいない。
- P-11 と P-13 は完了。P の e8 を阻む Supply の局所 instance 名衝突の修正後に停止。
- P-14 の割り当てはユーザー指示で取り消し。反射を構成済みの P-f が f4 を閉じる。
- curry と第一変数評価の可換性は全関手空間の厳密な等式。
  Hom の比較も同じ指定射の異種等式であり、対象ごとの同型の存在ではない。
- `HomWeightUnitEvaluation` の curry 評価・端点移送を公開済み。
- `JointComparisonComposition` で共同三点族を構成し、三つの面を元の比較族と
  同定した。同じ三辺の合成三角形と全 Hom の合成式を公開。
- 指定底変換同型の初頂点制限の回収と、前合成による同型等式の反映を公開。
- 指定同型の curry の合成保存、および既存 realizationIso の合成保存を公開。
- 標準反復 pullback 比較の相対切断の厳密同型・全高次相対射の自然性を公開。
- 元の底変換比較の合成を共同比較の等式へ束ね、三つの既存 realizationIso の
  合成が一度の底変換比較の実現同型と一致することを証明。
- 共同比較の豊穣前合成と、元の既存実現同型の関手前合成の全自然な等式を公開。
- 共同比較の添字制限も元の指定実現同型の値域制限へ、全図式の同型として同定。
- 元の相対切断底変換の実現同型・転置後の指定同型の添字制限との両立を公開。
- 切断底変換の指定実現同型の合成式を保存。straightening への降下は未完了。
- 最新 Supply.All は 8705 jobs で成功、独立監査は 726 宣言で標準三公理のみ。
  追加の ModelCategory 仮定なし。所有外ファイルは変更していない。
- Supply の匿名局所 instance 14 個に葉ごとの固有名を付け、監査で
  `CosliceBaseChangePreservation` との同時 import も監査で成功。衝突は解消済み。

### 残り（依存順、見積もり）
- 指定底変換同型の合成則と、共同 Hom 単位の固定始点制限の照合（4〜8 時間）。
- `homWeightYonedaUnit` の左 Kan 普遍性、実 end 比較の同値性と
  G に全自然な極限錐族（HTT 5.3.4.9、4〜8 時間）。
- 既存の点ごと余極限・poset 交換への接続、追加仮定なしの compact 判定（2〜4 時間）。

### 主要宣言
- `preservesSmallColimits_of_coproducts_finite`
- `hasPreservedColimit_of_coproducts_finite`
- `stableJoinAssociator_hom_eq_joinAssociator`
- `stableJoinAssociator_hom_eq_joinAssociator_point_point`
- `functorEndCoefficient_preservesKappaFilteredColimits`
- `isKappaCompact_functorVertex_of_endFamily`（追加の全自然 end 錐族を要求する還元）
- `twistedFunctorHomToEndSections`（実比較射。同値性は未証明）
- `functorEndSectionsYonedaHomEquivalence`
- `functorHomToHomWeightDiagramEquivalence`
- `homWeightYonedaUnit`
- `exists_homWeightYonedaLeftKan`
- `leftClassificationHom_baseChange`
- `leftClassificationSquareHom_naturality`
- `covariantHomComparison_homUniversal`
- `twistedSourceHomUnit_homUniversal`
- `functorSpaceCurryMap_evaluate_first`
- `curryFunctorHom_evaluate_first`
- `homWeightYonedaUnit_heq_curry`・`curryFunctorHom_evaluate_heq`
- `jointComparisonTrans`・`jointComparisonTriangleFamily_first`
- `jointComparisonTriangleFamily_second`・`jointComparisonTriangleFamily_long`
- `jointComparisonEdge_compStruct`・`jointComparisonEdge_hom_trans`
- `straighteningBaseChangeIso_firstVertex`・`functorIso_precomp_injective`
- `functorIsoCurry_hom`・`functorIsoCurry_trans`
- `jointRealizationIso_normalized`・`jointRealizationIso_trans`
- `relativeBaseChangeForward_comp`・`iteratedPullbackInv_relativeFunctorPullback`
- `sectionBaseChangeCompComparison`・`sectionBaseChangeComposite_eq`
- `sectionBaseChangeCompositeRealizationIso_eq`・`jointRealizationIso_precompose`
- `jointRealizationIso_reindex`・`functorIsoCurry_precompose_first`
- `relativeSectionBaseChangeRealizationIso_reindex`・`relativeSectionDiagramInfinityBaseChangeIso_reindex`
- `sectionBaseChangeCompRealizationIso`・`relativeSectionBaseChangeRealizationIso_comp`

### 依存と提供
- P の `PreservedColimitGeneration`・`SmallTwistedArrowShapes` は `acf4bc691` を継承。
  `hasPreservedColimit_smallCoproduct`・`hasPreservedColimit_of_coproducts_preservedRealizations`・
  `isKappaSmall_twistedArrow` は読み取り専用で使い、複製しない。
- e2 の点ごと余極限、P の poset 交換を `cardinalChangeBound_aleph0` で使う。
- P-11 は `95f5a8f2e`、P-13 は `1e7d9538d` で公開済み。
- 直前 `3a8981e34`：始点固定の指定単位の左 Kan Hom 普遍性。
- 提案・依頼・供給名の報告は必ずユーザー経由。別チャットへ直接送信しない。

### 未コミット
- なし。他セッションの変更は対象外。

### 既知の問題
- 元の共同単位を固定始点へ制限する段階で、指定底変換同型の合成との両立が未証明。
- 既存の `leftClassificationHom_baseChange` は同じ底の全空間射についての自然性。
  異なる底写像を二段で合成する上記の両立は、その結論には含まれていない。
- `homWeightYonedaLeftKan_valueIso` は対象ごとの別の同型であり、
  `homWeightYonedaLeftKanComparison` の可逆性をそれだけから推論してはいけない。
- `YonedaEvaluationJointSource` も固定対象での比較だけで、全二変数の同型ではない。
- 大きい C の余完備性や ModelCategory SSet の仮定を追加して迂回しない。

### 第 II 段／R の再開手順（現在は実行しない）
- 全比較データと指定転置後同型の添字制限を単体添字関手へ特殊化する。
- 端点正規化を介して単体切断比較の合成へ移し、初頂点回収と
  前合成の忠実性で指定 straightening 底変換同型の合成を降下する。
- 標準 pullback 比較の分類像と節の共同標準比較を全図式の Hom として照合する。
- 下記の合成則を同じ実 pullback 比較と同じ指定 straightening 同型で証明する。
- `homWeightYonedaUnit_heq_curry` と一般の curry 評価式を接続する。
  具体的な評価後の異種等式への直接適用は kernel timeout を起こすため、
  大きな端点の展開を避ける表示で接続する（未検証宣言は残していない）。
- 合成則を使い、共同単位の固定始点制限と `twistedSourceHomUnit` を
  指定した始点・延長図式の同型で照合する。
- `leftKanHomUniversal_of_unit_iso_square` で各前層評価の普遍性を移し、
  実左 Kan 比較の各評価での可逆性から全比較の可逆性へ進む。
- 完成した全自然 end 錐族を `isKappaCompact_functorVertex_of_endFamily` に渡す。

## 保留設計：指定底変換の合成則（第 II 段／R）

P-12 の要求する全自然な比較は、選んだ分類同型を保持する必要がある。
未接続部分を次の合成則に切り分けた。ユーザー指示により第 II 段／R へ保留。
所有外の straightening 実装は変更しない。分担変更が必要な提案はユーザー経由とする。

`U = SSet.uliftFunctor`、`St(p) = leftStraighteningInfinityDiagram p`、
`δ(p,k) = leftStraighteningInfinityDiagram_baseChangeIso p k` と書く。
`p : E ⟶ B` は left fibration、`k : D ⟶ B`、`l : T ⟶ D` とする。
`q = pullback.snd p k`、`r = pullback.snd p (l ≫ k)`、
`s = pullback.snd q l` とし、`c = (pullbackLeftPullbackSndIso p k l).inv` を
一度の pullback から反復 pullback への標準同型の実写像とする。
公開すべき結論は次の指定 Hom の等式（関手の結合・U の合成等式で端点を正規化）：

```text
δ(p,l ≫ k).hom ≫ leftClassificationHom r s c hc
  = precomposeFunctorHom (U.map l) δ(p,k).hom ≫ δ(q,l).hom
```

- 公開名の案：`leftStraighteningInfinityDiagram_baseChange_comp`（まだ未宣言）。
- 全体の FunctorIso の合成則でもよいが、上記の元の射の式を回収できること。
- 点のファイバーの同値や、未指定の同型の存在だけに弱めない。
- 最小の使用例は始点固定包含と `F.op ⊗ F` の可換正方形。
  一般式から二つの同じ合成底写像を比較し、固定始点単位の正方形を得る。
- 既存の実 pullback・transport simplex 切断比較・局所化前合成の充満忠実性から
  証明する方針。`relativeSectionBaseChangeComparison` の豊穣比較と共同実現の
  合成両立を先に示し、指定 `preimageVertexIso` で降下する。
  一般の合成両立を局所 Yoneda の計算に隠さない。
- この供給を P-12 の仮定へ追加しない。供給後に追加仮定なしで閉じる。

## P-11 三段目（HTT 4.4.2.6–7）

- [x] s11.1 保存余錐の既存入口と所有 import 閉包の確認。
- [x] s11.2 可算列の余積・pushout 表示と指定余錐の保存。
- [x] s11.3 有限骨格から幾何学的実現の構成と保存。
- [x] s11.4 既存の実現版を再利用して要求された全小形状の入口を公開。
- [x] s11.5 Supply.All と独立公理監査、公開名報告。

## P-12 三段目（HTT 5.3.4.9）

- [x] s12.1 twisted arrow の κ-small 性と継承入口の確認。
- [ ] s12.2 Fun の写像空間の end 表示とその全自然比較。
- [x] s12.3 κ-filtered 余極限の点ごと計算との比較（評価・各脚の Hom）。
- [ ] s12.4 `cardinalChangeBound_aleph0` による交換と compact 判定。
- [ ] s12.5 Supply.All と独立公理監査、公開名報告。

## 担当範囲の変更

- P-14（f4 の前倒し）は 2026-10-26 のユーザー指示で取り消し。
- P-f が構成した反射を既存の `LocalReplacementSaturation` に代入して f4 を閉じる。
- P-s は P-12 に専念し、P-14 の供給葉・代入の系は作らない。

## 検証・コミットの規約

- 新規葉 `F2/Presentable/Supply/`、その `All`、所有監査、本計画だけを編集する。
- 既存 Presentable・Duality・Localization・HomotopyLimits・Ind・Compact・Idempotent・
  F1・F1B・Core は読み取り専用。深層の実装は変更しない。
- 新規 sorry・公理・引用を導入しない。docstring は概要・方針・規約・使われ方。
- 自分の Supply.All と独立監査だけをビルドする。根の集約ビルドと .lake 削除は禁止。
- `set -o pipefail` を使い、明示した所有ファイルだけ `git commit --only` する。
- 他セッションの変更を stage しない。実施記録はコミット本文、計画は現在地。
- 停止理由は供給項目の完了・設計変更提案・所有 import 閉包破損・稼働 24 時間。
