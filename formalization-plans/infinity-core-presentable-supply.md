# P-s レーン：P-11・P-12 の専任供給

## 引き継ぎ（2026-10-25）

### 現在地
- 運用 v3 と P・P-f の進捗、P 計画の冒頭を確認した。
- Supply.All と独立監査を新設。P の二つの途中成果はコミット番号の中継後に接続する。
- 独立部分：離散区間族の strict 余積表示、端点に沿う望遠鏡形状、
  可算 nerve への写像と二側の厳密な制限を構成した。
- 小余積・有限余極限の保存から望遠鏡形状上の保存余極限を構成した。
  cofinal 制限の同時輸送と局所左 Kan 合成も供給する。
- Supply.All は 6305 jobs で成功。独立監査は 33 宣言、標準三公理のみ。
- P-11・P-12 の最終命題は未供給。望遠鏡から可算 nerve への共終性は未証明。

### 残り（依存順、見積もり）
- P-11：構成した望遠鏡から可算 nerve への共終性（HTT 4.4.2.6、4〜8 時間）。
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

### 依存と提供
- 所有：`F2/Presentable/Supply/` の新規葉と `Supply/All`、
  `scripts/audit_infinity_presentable_supply.lean`、この計画（300 行以内）。
- 読み取り専用：Presentable の既存葉・親集約・親監査、Duality・Localization、
  HomotopyLimits、F2/Ind・Compact・Idempotent、F1・F1B・Core。
- `PreservedColimitGeneration`・`SmallTwistedArrowShapes` は P の所有であり複製しない。
- P-f への供給名と依頼はユーザー経由で中継する。他チャットへ直接送らない。

### 未コミット
- なし（独立部品の供給コミットで所有七ファイルを記録する）。

### 既知の問題
- 初回確認時は P の二葉が未追跡。Git 上では後に `acf4bc691` を確認したが、
  ユーザーの中継待ちの指示に従い Supply の import から外した。複製はしていない。
- 望遠鏡形状上の余極限だけでは元の可算列の余極限にはならない。
  `sequentialTelescopeToNerve` の共終性を次の独立した証明義務として残す。
- P-12 の接続前の試作は `/tmp/p-s-TwistedArrowLimitContinuity.lean` に退避。
  未検証であり供給・集約・コミットに含めない。

### 次の一手
- 望遠鏡の有限区間を標準単体と比較し、全体から可算 nerve への共終性を証明する。
  末尾の辺の付加には既存の join の相対境界の inner anodyne 性を再利用する。

## P-11 三段目（HTT 4.4.2.6–7）

- [ ] s11.1 保存余錐の既存入口と所有 import 閉包の確認。
- [ ] s11.2 可算列の余積・pushout 表示と指定余錐の保存。
  望遠鏡形状・離散区間族の余積表示・その形状上の保存余極限は完了。
  元の可算 nerve への共終性が残る。
- [ ] s11.3 有限骨格から幾何学的実現の構成と保存。
- [ ] s11.4 既存の実現版を再利用して要求された全小形状の入口を公開。
- [ ] s11.5 Supply.All と独立公理監査、公開名報告。

## P-12 三段目（HTT 5.3.4.9）

- [ ] s12.1 twisted arrow の κ-small 性と継承入口の確認。
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
