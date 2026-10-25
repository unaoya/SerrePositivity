# P-s レーン：P-11・P-12 の専任供給

## 引き継ぎ（2026-10-25）

### 現在地
- 運用 v3 と P・P-f の進捗、P 計画の冒頭を確認した。
- P の二葉を `acf4bc691` のユーザー中継後に読み取り専用で接続した。
- 可算 spine の外の非退化単体を有限頂点集合で表示し、最小番号の次の点の
  挿入・削除の正則な inner pairing を構成した。順位は番号の幅と頂点数。
- 望遠鏡の strict pushout と元の spine の同型、可算 nerve への同じ写像の
  inner anodyne 性を構成した。宇宙変更後の全余錐比較も得られる。
- 元の小余積の存在・保存と全有限図式の保存余極限から、元の可算列の
  保存余極限と任意の指定全余錐の保存を公開した（s11.2）。
- 可算形状の有限増大列、各単体の最小所属段階とその単調性を構成した。
- 段階関手のコンマ圏と有限段階の反対単体圏の同値、元の包含との厳密な
  可換性を構成した。幾何学的実現の添字の全単体の可算性も確認した。
- 最後の頂点写像への制限による保存余極限の検出を、宇宙変更後に公開した。
- Supply.All は 8217 jobs で成功。独立監査は 209 宣言、標準三公理のみ。
- P-11 の全小形状の最終命題と P-12 の compact 判定は未供給。

### 残り（依存順、見積もり）
- P-11：有限骨格と可算列による実現、その保存と全小形状への接続
  （HTT 4.4.2.6–7、4〜8 時間）。
- P-12：Fun の写像空間の κ-small end 表示と全自然比較
  （HTT 5.3.4.9、4〜8 時間）。
- P-12：点ごと余極限・交換・compact 判定（HTT 5.3.4.9、2〜4 時間）。
- 各供給の集約ビルド・監査・公開名報告（各 30 分）。

### 主要宣言
- `hasPreservedColimit_iff_rightCofinalRestriction`
- `hasPreservedColimit_of_localLeftKan`
- `discreteProductNerveCofan_isColimit`
- `sequentialTelescopeShape`、`sequentialTelescopeToNerve`
- `sequentialTelescopeFinalVertices_isRightCofinal`
- `hasPreservedColimit_sequentialTelescopeIntervals`
- `hasPreservedColimit_sequentialTelescopeShape`
- `sequentialNerveSupportEquiv`、`sequentialSpinePairing`
- `sequentialSpine_inclusion_innerAnodyne`
- `sequentialTelescopeToSpine_isIso`、`sequentialTelescopeToNerve_innerAnodyne`
- `hasPreservedColimit_sequential_of_coproducts_finite`
- `preservesSequentialColimits_of_coproducts_finite`
- `countable_geometricRealizationShape_simplices`
- `countableFiniteStage_finite`、`iSup_countableFiniteStage`
- `countableSimplexStage_le_iff`、`countableSimplexStageFunctor`
- `countableStageCommaEquivalence`、`countableStageSimplexToComma_proj`
- `countableFiniteStageCocone_isColimit`
- `hasPreservedColimit_iff_lastVertexRestriction`

### 依存と提供
- 所有：`F2/Presentable/Supply/` の新規葉と `Supply/All`、
  `scripts/audit_infinity_presentable_supply.lean`、この計画（300 行以内）。
- 読み取り専用：Presentable の既存葉・親集約・親監査、Duality・Localization、
  HomotopyLimits、F2/Ind・Compact・Idempotent、F1・F1B・Core。
- `PreservedColimitGeneration`・`SmallTwistedArrowShapes` は P の所有であり複製しない。
- P-f への供給名と依頼はユーザー経由で中継する。他チャットへ直接送らない。

### 未コミット
- なし（s11.3 前半の五葉・Supply.All・独立監査・本計画を供給コミットへ記録）。

### 既知の問題
- 継承二葉の待機は解消。複製はせず、小余積段階に P の公開入口を使う。
- 可算列の供給だけでは P-11 は閉じない。有限部分形状の列を用いて幾何学的
  実現の存在・保存を構成し、P の既存の実現版へ接続することが残る。
- P-12 の接続前の試作は `/tmp/p-s-TwistedArrowLimitContinuity.lean` に退避。
  未検証であり供給・集約・コミットに含めない。

### 次の一手
- コンマ圏の比較と最後の頂点写像の自然性を結び、局所左 Kan 図式の
  保存余極限を有限段階の保存余極限から得る。可算列の余極限と合成して
  可算形状を閉じ、既存の実現版へ接続する。

## P-11 三段目（HTT 4.4.2.6–7）

- [x] s11.1 保存余錐の既存入口と所有 import 閉包の確認。
- [x] s11.2 可算列の余積・pushout 表示と指定余錐の保存。
- [ ] s11.3 有限骨格から幾何学的実現の構成と保存。
- [ ] s11.4 既存の実現版を再利用して要求された全小形状の入口を公開。
- [ ] s11.5 Supply.All と独立公理監査、公開名報告。

## P-12 三段目（HTT 5.3.4.9）

- [x] s12.1 twisted arrow の κ-small 性と継承入口の確認。
- [ ] s12.2 Fun の写像空間の end 表示とその全自然比較。
- [ ] s12.3 κ-filtered 余極限の点ごと計算との比較。
- [ ] s12.4 `cardinalChangeBound_aleph0` による交換と compact 判定。
- [ ] s12.5 Supply.All と独立公理監査、公開名報告。

## 検証・コミットの規約

- 深層モジュールは編集せず、新規 sorry・公理・引用を導入しない。
- ModelCategory SSet 等の instance 仮定を主経路に入れない。
- docstring は概要・方針・規約・使われ方を記す。
- 自分の Supply.All と独立監査だけをビルドする。根の集約はビルドしない。
- `set -o pipefail` を使い、明示した所有ファイルだけ `git commit --only` する。
- 実施記録はコミット本文。計画は現在地を更新する。
- 停止条件は供給完了・設計変更提案・所有 import 閉包破損・稼働 24 時間。
