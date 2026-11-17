# P-d：presentable 二対象の随伴双対性

## 引き継ぎ・現在の範囲

- 2026-10-25、ユーザーによる設計提案への回答で範囲を変更。
- 全体の対応 quasicategory と `PrL ≃ PrR.op` は第 II 段／R へ回す。
- 双 Cartesian fibration の一般分類・straightening の新工程は設けない。
- 今回の完了条件は presentable C・D に対する元の全関手 ∞ 圏の対ごとの同値
  `PrLFunctorSpace C D ≃ (PrRFunctorSpace D C).op`（HTT 5.2.6.2）の公開。
- 非可逆な自然変換と全高次単体を含むことを検証する。core の同値では代用しない。
- 対ごとの全同値を公開済み。専用集約のビルドと最終監査は成功した。限定コミットに記録して停止する。
- 旧設計で提案した一般分類の工程分割は不採用。承認待ちには戻らず今回の範囲で続行する。

## 三段目（範囲変更後）

1. p1. 全単位族の表現可能性から元の全関手圏間の反変作用を構成する。
2. p2. 構成した同じ反変作用の充満忠実性と本質的全射性を証明する。
3. p3. 元の全関手圏の対ごとの反変同値を公開する。
4. p4. 専用監査と第 II 段／R への残件記録を行い停止する。

- [x] p1：`pairRightAdjointFunctor` は元の全関手圏から反対全関手圏への実際の単体写像。
  元の全単位族とその共変 Yoneda 像の全自然な比較同型も構成した。
- [x] p2：同じ射の充満忠実性・本質的全射性と各値の実際の随伴を証明した。
- [x] p3：`presentableAdjointFunctorEquivalence` を公開した。
- [x] p4：最終監査成功。第 II 段／R の残件と P-e8 の集約・監査への引き継ぎを記録した。

## 検証済みの局所入力（範囲変更前から）

名前空間：`SerrePositivity.InfinityCategories.F2.Presentable.Duality`。

- e1 の元の保存関手圏の頂点に d の随伴関手定理を接続した。
- `chosenRightAdjoint`・`chosenRightAdjunction`・`chosenRightAdjoint_condition`。
- `chosenLeftAdjoint`・`chosenLeftAdjunction`・`chosenLeftAdjoint_condition`。
- `rightAdjointVertex`・`leftAdjointVertex` は元の反対方向の全関手圏の頂点。
- `leftRoundtripIso`・`rightRoundtripIso` は元の関手との h Fun の同型。
- `AdjointUnitMappingSpace` は二対象の元の core 上に実単位を保持する Kan 空間。
- `adjointUnitLeft`・`adjointUnitRight` は元の両写像空間への単体射影。
- `adjointUnitAdjunction` と `adjointUnitAdjunction_unitHom` は指定単位を回収する。
- `rightUnit_condition_iff_isInitial`・`leftUnit_condition_iff_isInitial`。
- 固定左・右の単位条件を始対象性と同定し、全高次の単位空間の可縮性を証明した。
- `rightUnitFiberIso`・`leftUnitFiberIso` は元の局所射影のファイバーとの厳密な同型。
- `adjointUnitRight_trivialKanFibration`・`adjointUnitLeft_trivialKanFibration`。
- `adjointUnitRight_isQCatEquivalence`・`adjointUnitLeft_isQCatEquivalence`。
- `adjointMappingEquivalence` は二対象の core の同値で、全関手圏の同値ではない。
- `precompositionAdjunction` は元の前合成 `pre R ⊣ pre L` の全 QCat 随伴。
- `precompositionAdjunction_unitComponent_identity` は恒等関手で元の指定単位を回収する。
- `adjointUnitLeft_extend`・`adjointUnitRight_extend` は任意の mono に沿う相対延長。
- `adjointUnitLeftSection`・`adjointUnitRightSection` は元の局所射影の厳密な単体切断。
- `rightAdjointMappingFamily`・`leftAdjointMappingFamily` と各 `isQCatEquivalence`。
- 各 `MappingFamilyAdjunction` は選んだ全単体族の各頂点の実際の随伴を回収する。
- 以上の保存：`8779a0da8`（両局所射影）、`0a67459d5`（相対延長と族の選択）。

## 現在の二対象の全関手族の構成

- `TwistedPairFamilies.lean`：標準単体 K の twisted arrow 上で、左族 K→A と
  右族 K→B.op を共同評価し、指定射影への実際の持ち上げを保持する。
- `twistedPairLift` は面・退化写像と両関手則を証明した一つの単体集合。
- `twistedPairLiftLeft`・`twistedPairLiftRight` は A と B.op への単体射影。
- `PairUnitCorrespondence.lean`：元の `PrLFunctorSpace`・`PrRFunctorSpace` の
  全包含と実合成 `pairUnitComposition`、実単位を持つ `PairRawUnitCorrespondence`。
- `pairUnitComposition_core` は旧局所合成を厳密に回収する。
- `TwistedPairVertices.lean`：`twistedZeroIso`、零頂点評価と単位の射影公式。
- `TwistedPairVertexConstruction.lean`：指定両頂点と指定単位から母対応の頂点を作り、
  左・右・単位を厳密に回収する。
- `PairAdjointCondition.lean`：指定単位の条件を課した `PairAdjointCorrespondence`。
  core は取らず、充填性はまだ主張していない。
- `pairAdjointLeft`・`pairAdjointRight` は元の全関手圏と反対全関手圏への単体射影。
- `pairAdjointVertexAdjunction` は各頂点の元の二関手と指定単位から随伴を回収する。
- `PairAdjointVertices.lean`：元の随伴の持ち上げ、指定辺の回収、
  `pairAdjointLeft_surjective`・`pairAdjointRight_surjective`。
- `MateTransformationEquivalence.lean`：`adjointTransformationEquivalence` は
  `Map(L₁,L₂) ≃ Map(R₂,R₁)` を非可逆な変換と全高次を含む区間模型で与える。
  後合成随伴と前合成随伴を同じ `id→L₂R₁` 空間で合成する。
  これは対応射影の Hom 作用の同値性自体とはまだ同定していない。
- `PairUnitHomFamily.lean`：元の coslice の left fibration を全保存関手圏の積へ
  引き戻し、既存の空間値分類で `pairUnitHomBifunctor`・`pairUnitHomFamily` を構成。
  一般の Cartesian 分類の新工程や新しい存在仮定は追加していない。
- `PairUnitHomRestriction.lean`：元の左関手への制限と curry の頂点の厳密な同定。
  `pairFixedLeftBase_composition` と分類の底変換同型。
- `PairFixedLeftCoslice.lean`：全単位族の固定左制限を保存条件付きの同じ coslice に
  引き戻しの貼り合わせで比較する。

- `PairUnitClassifications.lean`：固定左の全単位族と保存条件付き coslice の全分類同型。
- `PairLeftRepresentability.lean`：`pairUnitHomAtLeft_representationIso` は元の右随伴による
  固定左値の全自然な表現可能性。元の全右保存関手圏を底にする。
- `PairCovariantYoneda.lean`：共変 Yoneda の実単体写像・充満忠実性・元の単位族の本質像所属。
- `PairAdjointFunctor.lean`：`pairRightAdjointFunctor` とその持ち上げ、
  `pairRightAdjointFunctorLifted_yonedaIso` による元の全単位族との全自然な比較。
- 直接の反変単体写像を構成したので、その同値性を主経路で証明する。
  母単位対応の quasicategory 性は補助の残件であり、それを完成したとはしない。

- `PairAdjointFunctorVertices.lean`：元の実反変関手の指定右随伴との頂点同型と
  `pairRightAdjointFunctor_isEssentiallySurjective`。
- `PairAdjointFunctorMeaning.lean`：`pairRightAdjointValue` と
  `pairRightAdjointFunctorAdjunction` は同じ射の各値が元の左関手の実際の右随伴であること。
- `PairFunctorVertexEvaluation.lean` と `pairCovariantYonedaPreimageVertexIso` は
  実装を構成した不透明な評価・逆像で、複雑な関手の型の正規化を局所化する。公理ではない。
- `PairUnitRightRestriction.lean`・`PairRightRepresentability.lean`：同じ全単位族の右固定制限と
  `pairUnitHomAtRight_representationIso` による元の左随伴の全自然な表現可能性。
- `PairInitialRestriction.lean`・`PairPreservingUnitVertices.lean`：指定単位は左右の
  保存条件付き coslice でも始対象。元の単位と左右の底頂点を厳密に保持する。
- `PairUnitFiberComparison.lean`：両 coslice の固定 fiber を同じ実単位空間へ厳密に比較。
- `PairUnitRelativeEvaluation.lean`：元の始単位での相対評価は自明 Kan fibration。
  `pairUnitPointHomFamily` は同じ実単位空間への QCat 同値。
  この評価を下記の pointed 比較で実反変関手の Hom 作用に接続した。
- `PairClassifierPointedDisplay.lean`：元の left fibration を同じ分類図式上の
  pointed-space に送り、同じ実際の fiber 作用が各点で QCat 同値であることを証明。
- `PairUnitPointedRestrictions.lean`：同じ全単位の pointed 比較を左右の固定単位空間へ
  制限し、元の二変数族の各固定値の上にある厳密な射として構成した。

## 全同値の公開と証明

- `PairPointedRestrictionFibers.lean`・`PairPointedRightRestrictionFibers.lean`：
  左右の固定単位空間からの同じ pointed 比較の実 fiber 射がともに QCat 同値。
- `PairUnitSharedPoint.lean`：指定随伴単位の左右の包含は全単位空間内で同じ頂点。
- `PairUnitUnstraightening.lean`・`PairCanonicalUnitPoint.lean`：固定左の単位を
  同じ分類関手の unstraightening の始対象へ送り、左右で同じ pointed 点を回収する。
- `PairTransformationEvaluation.lean`：その始点での全変換空間の評価は同値で、
  実 Hom 作用の評価後の普遍輸送と全パラメータで関手同型。
- `PairEvaluatedTransport.lean`：固定右の始単位からの輸送を同じ pointed 比較へ移す。
- `PairHomFamilyFullyFaithful.lean`：同じ関手の区間後合成の合成則と評価比較を使い、
  `pairUnitHomFamily` の実 pinched Hom 作用の同値、従って充満忠実性を証明する。
- `PairDuality.lean`：共変 Yoneda との比較から同じ反変関手の充満忠実性を回収し、
  同じ射の本質的全射性と合わせる。独立な Hom 同値の存在で代用しない。

主公開名（上記名前空間内）：

- `pairRightAdjointFunctor_isFullyFaithful`。
- `pairRightAdjointFunctor_isQCatEquivalence`。
- `presentableAdjointFunctorEquivalence C D`：
  `QCatEquivalence (PrLFunctorSpace C D) (PrRFunctorSpace D C).op`。
- `presentableAdjointFunctorEquivalence_hom`：順方向は元の `pairRightAdjointFunctor`。
- `presentableAdjointFunctorEquivalence_adjunction v`：同じ同値の右関手値は v の実際の右随伴。

`QCatEquivalence` は元の単体写像、逆写像、両往復の関手同型を持つ。
元の全保存関手圏を使用し、非可逆な自然変換と全高次単体を含む。
補助の `PairAdjointCorrespondence` の quasicategory 性を今回の公開定理の仮定にしない。

## 第 II 段／R への残件

- 三つの presentable 対象を経由する随伴の合成と、今回の対ごとの同値の整合。
- 恒等と合成を全単体で保持する全体の対応 quasicategory と両単体射影。
- 元の `PrL` と `PrR.op` の全 ∞ 圏としての同値（HTT 5.5.3.4）。
- 一般分類・straightening の必要性と供給方法は第 II 段／R で判断する。
  今回その工程を新設せず、同値の存在を仮定や公理として追加しない。
- P の e8 への `Duality.All` の集約・監査追加は、今回の完了時に公開名と範囲を報告する。
  P-e8 は `Presentable.Duality.All` と専用監査の公開定理を含める。
  全 Pr の同値が完成したとは報告しない。

## 検証と規約

- 所有：`F2/Presentable/Duality/` の新規葉と集約、本計画、専用監査のみ。
- 既存の Presentable・HomotopyLimits・F1・F1B・Core・Ind・Compact・Idempotent は読み取り専用。
- P の e5 はコミット済みの依存だけを使用する。
- 専用集約8,618 jobs 成功、専用監査894宣言は標準3公理のみ。
- 所有 import 閉包は直近確認で4,974モジュール、他レーンの未保存依存なし。
- 自分の集約：`lake build SerrePositivity.InfinityCategories.F2.Presentable.Duality.All`。
- 自分の監査：`lake env lean scripts/audit_infinity_presentable_duality.lean`。
- 新規 sorry・公理・引用なし。主経路に ModelCategory SSet 等の instance 仮定なし。
- 根のビルド、既存 Presentable 集約・監査、`.lake` の削除は行わない。
- docstring は概要・方針・規約・使われ方。
- `SourceTransport.lean` の不透明な値は実装と仕様を構成済みであり、公理ではない。
- 実施記録と最終検証件数は限定コミット本文に保存する。
- `set -o pipefail` のうえ所有ファイルのみ `git commit --only`。
- 停止は今回の工程完了・設計変更提案・所有 import 閉包の破損・稼働24時間。
