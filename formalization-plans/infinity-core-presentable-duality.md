# P-d レーン：P-1 e6 presentable ∞ 圏の双対性

## 引き継ぎ（2026-10-25）

### 現在地
- e6 は未完了。目標は元の `PrL` と `PrR.op` の全 ∞ 圏としての同値。
- e1 の実際の `PrLFunctorSpace`・`PrRFunctorSpace` の頂点に d の随伴関手定理を接続した。
- 左右の随伴を選び、その保存条件を証明して、反対方向の元の関手圏の頂点に戻した。
- 両往復の元の関手との `FunctorIso` を証明した。
- 15:05 ユーザー採用の設計で続行中。全体の対応 quasicategory と両単体射影の構成が目標。
- 二対象間の実単位を coslice に保持する `AdjointUnitMappingSpace`、その Kan 性、
  元の左右の写像空間への単体射影と頂点上の全射性を構成した。
  全 Pr 上の対応 quasicategory はまだ未構成。
- 前合成の全パラメータ Hom 全単射、前合成作用の転置と評価の厳密な等式も検証済み。
- 両局所射影は inner fibration、固定ファイバーは Kan。右ファイバーから
  全関手圏の固定右 coslice の core への単体比較射は元の単位・左関手を保持する。
- 固定右の coslice–comma 比較は元の単位辺を保つ QCat 同値。
  指定実単位の随伴条件と coslice の始対象性を同値にし、
  `RightAdjointUnitSubspace` とその core `RightAdjointUnitSpace` の可縮性を証明済み。
  元の `adjointUnitRight` の固定ファイバーとの厳密な同型 `rightUnitFiberIso` を構成し、
  元の右ファイバーの全高次の可縮性まで証明済み。
- 母空間の両関手が動く辺について指定単位条件の不変性を証明した。
  両局所射影は Kan fibration。右射影は trivial Kan fibration・QCat 同値として公開済み。
  左射影の同値性と全 Pr 上の対応 quasicategory はまだ未構成。
- 最新の専用集約は8,540 jobs 成功、専用監査320宣言は標準3公理のみ。

### 残り（依存順）
1. 随伴を持つ関手の全体の対応 quasicategory と両単体射影を構成（e6-3）。
2. `PrL`・`PrR.op` への両射影の QCat 同値性（e6-4）。
3. 一方の射影の逆との合成による全同値の公開（e6-5）。
4. 完成後の専用監査と P の e8 への引き継ぎ（e6-6）。
   以上は HTT 5.5.3.4。全体20〜60時間の暫定見積もり、e5・e7 の未保存成果には依存しない。

### 主要宣言
名前空間：`SerrePositivity.InfinityCategories.F2.Presentable.Duality`。
- `leftVertex_exists_rightAdjoint`、`rightVertex_exists_leftAdjoint`
- `chosenRightAdjoint`、`chosenRightAdjunction`、`chosenRightAdjoint_condition`
- `chosenLeftAdjoint`、`chosenLeftAdjunction`、`chosenLeftAdjoint_condition`
- `rightAdjointVertex`、`leftAdjointVertex`
- `leftRoundtripIso`、`rightRoundtripIso`
- `AdjointUnitMappingSpace`、`adjointUnitLeft`、`adjointUnitRight`、`adjointUnitAdjunction`
- `adjointUnitVertex`、`adjointUnitLeft_surjective`、`adjointUnitRight_surjective`
- `adjointUnitCoreIso`、`adjointUnitAdjunction_unitHom`
- `adjointUnitLeft_innerFibration`、`adjointUnitRight_innerFibration`
- `adjointUnitLeftFiber_kanComplex`、`adjointUnitRightFiber_kanComplex`
- `rightUniversalUnitSpace_isContractibleKan`
- `rightUnitCosliceComparison_isQCatEquivalence`、`rightUnitCoslice_hasInitial`
- `adjointUnitRightFiberToCoslice`、`adjointUnitRightFiberToCore_ι`
- `qcatAdjunctionChangeLeft`・`qcatAdjunctionChangeRight` と各 `unitHom` の回収公式
- `rightUnitVertex_isInitial`、`rightUnit_condition_iff_isInitial`
- `rightAdjointUnitSubspace_isContractibleKan`、`rightAdjointUnitSpace_isContractibleKan`
- `rightFiberToAdjointUnitSpace`、`rightAdjointUnitToFiber`、`rightUnitFiberIso`
- `adjointUnitRightFiber_isContractibleKan`
- `rawUnitCondition_of_vertexIso`、`adjointUnitLeft_fibration`、`adjointUnitRight_fibration`
- `adjointUnitRight_trivialKanFibration`、`adjointUnitRight_isQCatEquivalence`
- `adjointUnitRightMappingEquivalence`（二対象間の局所写像空間の同値）
- `precompositionHomEquiv`、`precompositionMap_transpose_evaluate`
- `rightMateIntervalMap`、`rightMateIntervalMap_family`（写像の構成まで。同値性は未証明）

### 依存と提供
- 読み取り専用：`Presentable.PrInfinity`、`Presentable.AdjointFunctorTheorem`、
  Core の coslice・実ホモトピー、F1B の内部 Hom 転置・指定単位の随伴判定。
- e1 の定義と d の随伴判定はコミット済みで、両直接依存に未保存の変更はない。
- プロジェクト内の推移閉包 4,896 モジュールに他レーンの未保存依存なし（今回検証時）。
- P の e5 の未保存成果は使用していない。
- P の e8 が後で `Duality.All` を集約・監査へ含める。現段階で e6 完了にはしない。
- 他チャットへの送信は行っていない。引き継ぎは本計画と停止報告を使う。

### 未コミット
- `PrecompositionUnit.lean`（左側の指定単位候補。集約への import とビルドは次工程）。

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
- inner fibration の可縮ファイバーだけでは射影の同値性は結論できない。
  辺の持ち上げまたは充満忠実性も証明する。

### 次の一手
- 左側には前合成の全 QCat 随伴と普遍単位の模型を接続する。
  全パラメータ Hom 全単射 `precompositionHomEquiv` と転置・評価の式は検証済み。
  それを指定単位の判定または自然な Hom 対応へ接続する工程が残る。
- その写像空間側の構成を全体の対応 quasicategory と両射影へ接続する。
  深層編集・既存の Pr 定義の変更・同値の存在仮定の追加は行わない。

## 三段目（初回確定、6 項目）

- [x] e6-1. e1 の保存関手圏と d の随伴存在判定の接続。
- [x] e6-2. 左右の随伴選択と保存条件、元の関手圏への回収、両往復の一意性比較。
- [ ] e6-3. 全体の随伴対応 quasicategory と両単体射影の構成。
- [ ] e6-4. `PrL`・`PrR.op` への両射影の QCat 同値性。
- [ ] e6-5. 元の `PrL` と `PrR.op` の全 ∞ 圏の同値の公開。
- [ ] e6-6. 完成後の専用集約・公理監査・P の e8 への引き継ぎ。

## 採用された設計（15:05）

全体の対応を quasicategory として構成し、両単体射影を QCat 同値にする。
一方の射影の逆との合成から元の Pr の全同値を得る。
恒等・合成との高次整合は対応 quasicategory と単体射影の構成に含まれるため、
別個の mate 整合の証明を完了条件にしない。

1. 写像空間側では presentable な C・D に対し、全高次の実単位の Kan 空間を作る。
   左射影は `PrLMappingSpace C D`、右射影は `PrRMappingSpace D C` へ向かう。
   頂点上では実際の二つの関手の `QCatAdjunction` を回収する。
2. 両射影を `IsQCatEquivalence` として証明する。
   d の随伴関手定理は頂点の存在に使用し、高次の延長性・選択の可縮性は別に証明する。
3. 全体の対応 quasicategory と両射影を構成する。
   Hom ごとの同値だけで Pr 全体の同値が得られたとはしない。
4. 両射影が QCat 同値であることから元の `PrL`・`PrR.op` の同値を構成する。

全体の対応と両射影の同値性はまだ未実装であり、その存在を仮定や公理として追加していない。
一般の随伴対応を上流へ依頼する場合は、コーディネータ経由で所有レーンに依頼する。
P-d 内で構成を進める場合も、新規葉に限定する。

## 検証

- ビルド：`lake build SerrePositivity.InfinityCategories.F2.Presentable.Duality.All`。
- 監査：`lake env lean scripts/audit_infinity_presentable_duality.lean`。
- 検証済み：専用集約8,540 jobs 成功、所有320宣言の再帰的公理依存は標準3公理のみ。
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
