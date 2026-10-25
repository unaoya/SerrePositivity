# P-d レーン：P-1 e6 presentable ∞ 圏の双対性

## 引き継ぎ（2026-10-25）

### 現在地
- e6 は未完了。目標は元の `PrL` と `PrR.op` の全 ∞ 圏としての同値。
- e1 の実際の `PrLFunctorSpace`・`PrRFunctorSpace` の頂点に d の随伴関手定理を接続した。
- 左右の随伴を選び、その保存条件を証明して、反対方向の元の関手圏の頂点に戻した。
- 両往復の元の関手との `FunctorIso` を証明した。
- 専用集約 `Duality.All` のビルド成功（8,492 jobs）。専用監査は31宣言で標準3公理のみ。
- 停止理由：設計変更の提案。頂点の選択と h Fun の同型から高次の対応を導く工程を、
  随伴対応空間の構成・両射影の同値性・合成との整合性に具体化する必要がある。

### 残り（依存順）
1. 随伴を持つ関手の対応空間を元の全関手圏の core 上に構成（e6-3、8〜24 時間の暫定見積もり）。
2. 対応空間の両射影の同値性と高次の恒等・合成整合性（e6-3〜4、8〜24 時間の暫定見積もり）。
3. 元の `PrL` と `PrR.op` の全同値、専用監査と P への引き継ぎ（e6-5〜6、4〜12 時間）。
   以上は HTT 5.5.3.4。e5・e7 の成果には依存しない。

### 主要宣言
名前空間：`SerrePositivity.InfinityCategories.F2.Presentable.Duality`。
- `leftVertex_exists_rightAdjoint`、`rightVertex_exists_leftAdjoint`
- `chosenRightAdjoint`、`chosenRightAdjunction`、`chosenRightAdjoint_condition`
- `chosenLeftAdjoint`、`chosenLeftAdjunction`、`chosenLeftAdjoint_condition`
- `rightAdjointVertex`、`leftAdjointVertex`
- `leftRoundtripIso`、`rightRoundtripIso`

### 依存と提供
- 読み取り専用の直接 import：`Presentable.PrInfinity`、`Presentable.AdjointFunctorTheorem`。
- e1 の定義と d の随伴判定はコミット済みで、両直接依存に未保存の変更はない。
- プロジェクト内の推移閉包 4,847 モジュールに他レーンの未保存依存なし（初回検証時）。
- P の e5 の未保存成果は使用していない。
- P の e8 が後で `Duality.All` を集約・監査へ含める。現段階で e6 完了にはしない。
- 他チャットへの送信は行っていない。引き継ぎは本計画と停止報告を使う。

### 未コミット
- なし（本引き継ぎを含む所有ファイルのみを限定コミット）。

### 既知の問題
- `PrL`・`PrR` は元の保存関手圏の core を豊穣 Hom とする coherent nerve。
  ホモトピー圏の反変同値や対象ごとの往復同型では目標を満たさない。
- `QCatAdjunction.rightAdjointFunctorIso`・`leftAdjointFunctorIso` は h Fun の同型を返す。
  既存の `QCatAdjunction.intervalMap` は固定した随伴の対象間の写像空間比較であり、
  随伴関手そのものが変動する対応空間の射ではない。
- F1・F1B・F2 の既存随伴 API の調査では、随伴を忘れる射影の自明 fibration 性や、
  随伴関手を取り出す高次の対応を公開する入口は確認できなかった。
- `QCatAdjunction` の証拠を頂点に付けるだけ、または二つの関手圏の積の全部分複体を取るだけでは、
  高次の mate の整合性と両射影の同値性は得られない。

### 次の一手
- 下記設計変更案を確定してから、所有する新規葉で e6-3 の対応空間を構成する。
  深層編集・既存の Pr 定義の変更・同値の存在仮定の追加は行わない。

## 三段目（初回確定、6 項目）

- [x] e6-1. e1 の保存関手圏と d の随伴存在判定の接続。
- [x] e6-2. 左右の随伴選択と保存条件、元の関手圏への回収、両往復の一意性比較。
- [ ] e6-3. 随伴対応の全高次単体への拡張。
- [ ] e6-4. 恒等・合成との高次の整合性。
- [ ] e6-5. 元の `PrL` と `PrR.op` の全 ∞ 圏の同値の公開。
- [ ] e6-6. 完成後の専用集約・公理監査・P の e8 への引き継ぎ。

## 設計変更案

e6-3 を「随伴を選んで各次元に写す」から、次の具体的な対応構成へ変更する。

1. presentable な C・D に対し、全高次の随伴対応を表す Kan 空間を作る。
   左射影は `PrLMappingSpace C D`、右射影は `PrRMappingSpace D C` へ向かう。
   頂点上では実際の二つの関手の `QCatAdjunction` を回収する。
2. 両射影を `IsQCatEquivalence` として証明する。
   d の随伴関手定理は頂点の存在に使用し、高次の延長性・選択の可縮性は別に証明する。
3. 対応の合成を構成し、右側の合成順序の反転と、単位・結合の全高次の整合性を証明する。
   Hom ごとの同値だけで Pr 全体の同値が得られたとはしない。
4. 対応の全体から coherent nerve 間の同値を構成し、元の `PrL`・`PrR.op` へ接続する。

これは未実装の設計案であり、上の性質を Lean の仮定や公理として追加していない。
一般の随伴対応を上流へ依頼する場合は、コーディネータ経由で所有レーンに依頼する。
P-d 内で構成を進める場合も、新規葉に限定する。

## 検証

- ビルド：`lake build SerrePositivity.InfinityCategories.F2.Presentable.Duality.All`。
- 監査：`lake env lean scripts/audit_infinity_presentable_duality.lean`。
- 結果：集約 8,492 jobs 成功、所有31宣言の再帰的公理依存は標準3公理のみ。
- 主経路の公開名を `#check @...` で検査し、追加 instance 引数なし。
- 根のビルド、既存 Presentable 集約・監査、`.lake` の削除は行わない。
- 主経路に `ModelCategory SSet` 等の instance 仮定を導入しない。
- 実施記録と最終検証件数は限定コミットの本文に保存する。

## 規約

- 所有：`F2/Presentable/Duality/` の新規葉と集約、本計画、専用監査のみ。
- 新規 sorry・公理・引用なし。既存ファイル、深層モジュールは読み取り専用。
- docstring は概要・方針・規約・使われ方。
- `set -o pipefail` のうえ所有ファイルのみ `git commit --only`。
- 停止は e6 完了・設計変更提案・所有 import 閉包の破損・稼働24時間。
