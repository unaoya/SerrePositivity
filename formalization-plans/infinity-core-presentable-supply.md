# P-s レーン：P-11・P-12 と中継依頼の専任供給

## 引き継ぎ（2026-10-25）

### 現在地
- 状態：設計変更提案で停止（下記の指定底変換合成則を独立基盤供給に切り出す案）。
- P-11 と P-13 は完了。P-12 の最終 compact 判定は未供給、P-14 は未着手。
- 前回の補助宣言供給後のターン終了には停止理由がなかった。今回は再開し、
  指定 Yoneda 単位と共同 Hom 単位の curry の比較、および一般の curry 評価式を得た。
- curry と第一変数評価の可換性は全関手空間の厳密な等式。
  Hom の比較も同じ指定射の異種等式であり、対象ごとの同型の存在ではない。
- 新規葉 `HomWeightUnitEvaluation` を公開。Supply.All は 8688 jobs で成功、
  独立監査は 582 宣言で標準三公理のみ。追加の ModelCategory 仮定なし。
- 設計変更案：指定 straightening 底変換の合成則を、P-12 内の局所照合から
  独立した基盤供給として切り出す。具体的な供給仕様は本文に記す。
  最終定理への追加仮定にはしない。所有外ファイルは変更していない。

### 残り（依存順、見積もり）
- 指定底変換同型の合成則と、共同 Hom 単位の固定始点制限の照合（4〜8 時間）。
- `homWeightYonedaUnit` の左 Kan 普遍性、実 end 比較の同値性と
  G に全自然な極限錐族（HTT 5.3.4.9、4〜8 時間）。
- 既存の点ごと余極限・poset 交換への接続、追加仮定なしの compact 判定（2〜4 時間）。
- P-14：反射を引数とする強飽和閉包と反転辺の一致（HTT 5.5.4.15(4)）。

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
- `homWeightYonedaLeftKanComparison_fac`
- `leftClassificationHom_baseChange`
- `leftClassificationSquareHom_naturality`
- `covariantHomComparison_homUniversal`
- `twistedSourceHomUnit_homUniversal`
- `functorSpaceCurryMap_evaluate_first`
- `curryFunctorHom_evaluate_first`
- `homWeightYonedaUnit_heq_curry`・`curryFunctorHom_evaluate_heq`

### 依存と提供
- P の `PreservedColimitGeneration`・`SmallTwistedArrowShapes` は `acf4bc691` を継承。
  `hasPreservedColimit_smallCoproduct`・`hasPreservedColimit_of_coproducts_preservedRealizations`・
  `isKappaSmall_twistedArrow` は読み取り専用で使い、複製しない。
- e2 の点ごと余極限、P の poset 交換を `cardinalChangeBound_aleph0` で使う。
- P-11 は `95f5a8f2e`、P-13 は `1e7d9538d` で公開済み。
- 直前 `3a8981e34`：始点固定の指定単位の左 Kan Hom 普遍性。
- 提案・依頼・供給名の報告は必ずユーザー経由。別チャットへ直接送信しない。

### 未コミット
- なし（今回の所有四ファイルを同じコミットに収録）。他セッションの変更は対象外。

### 既知の問題
- 元の共同単位を固定始点へ制限する段階で、指定底変換同型の合成との両立が未証明。
- 既存の `leftClassificationHom_baseChange` は同じ底の全空間射についての自然性。
  異なる底写像を二段で合成する上記の両立は、その結論には含まれていない。
- `homWeightYonedaLeftKan_valueIso` は対象ごとの別の同型であり、
  `homWeightYonedaLeftKanComparison` の可逆性をそれだけから推論してはいけない。
- `YonedaEvaluationJointSource` も固定対象での比較だけで、全二変数の同型ではない。
- 大きい C の余完備性や ModelCategory SSet の仮定を追加して迂回しない。

### 次の一手
- 下記の合成則を基盤供給として独立させ、同じ実 pullback 比較と同じ指定
  straightening 同型で証明する。供給元・分担の変更はユーザー経由で調整する。
- `homWeightYonedaUnit_heq_curry` と一般の curry 評価式を接続する。
  具体的な評価後の異種等式への直接適用は kernel timeout を起こすため、
  大きな端点の展開を避ける表示で接続する（未検証宣言は残していない）。
- 合成則を使い、共同単位の固定始点制限と `twistedSourceHomUnit` を
  指定した始点・延長図式の同型で照合する。
- `leftKanHomUniversal_of_unit_iso_square` で各前層評価の普遍性を移し、
  実左 Kan 比較の各評価での可逆性から全比較の可逆性へ進む。
- 完成した全自然 end 錐族を `isKappaCompact_functorVertex_of_endFamily` に渡す。

## 設計変更案：指定底変換の合成則を独立供給にする

P-12 の要求する全自然な比較は、選んだ分類同型を保持する必要がある。
今回の curry 評価公式により、未接続部分は次の合成則に切り分けられる。
所有外の straightening 実装を変更する要求ではなく、新規葉での公開定理の供給案。
供給元はコーディネータ判断とし、P-s から直接依頼は送信しない。

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

## P-14（P-12 の後、ユーザー判断による f4 の前倒し）

- HTT 5.5.4.15(4)。反射を N の `LocalReplacementReflection` の形の引数に取り、
  `LocalReplacementSaturation` で生成元の強飽和閉包と反射の反転辺の一致を公開する。
- P-f の f3 で反射が完成したら、代入した系を置く。新規 Supply 葉に限定する。
- P-14 の公開名を報告して停止する。P-12 完了前に着手しない。

## 検証・コミットの規約

- 新規葉 `F2/Presentable/Supply/`、その `All`、所有監査、本計画だけを編集する。
- 既存 Presentable・Duality・Localization・HomotopyLimits・Ind・Compact・Idempotent・
  F1・F1B・Core は読み取り専用。深層の実装は変更しない。
- 新規 sorry・公理・引用を導入しない。docstring は概要・方針・規約・使われ方。
- 自分の Supply.All と独立監査だけをビルドする。根の集約ビルドと .lake 削除は禁止。
- `set -o pipefail` を使い、明示した所有ファイルだけ `git commit --only` する。
- 他セッションの変更を stage しない。実施記録はコミット本文、計画は現在地。
- 停止理由は供給項目の完了・設計変更提案・所有 import 閉包破損・稼働 24 時間。
