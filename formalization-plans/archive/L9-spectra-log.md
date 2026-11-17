# L9-spectra の記録（2026-10-19 に本文から移動）

## 16. 主要宣言

以下は検証済みの宣言だけを記載する。
名前の共通接頭辞は `SerrePositivity.KST.Spectra`。
最初の表の宣言は `SerrePositivity/KST/Spectra/HomotopyGroups.lean` に置く。
補助の幾何的構成と全自然数次数の界面は後続の四モジュールに分割する。

| 宣言 | 内容 |
| --- | --- |
| `simplexRel` | 最後の面の単位積による関係 |
| `simplexSetoid` | Kan 性から同値関係を実証 |
| `shiftRelStruct` | 隣接する面の関係を前へ移す |
| `unshiftRelStruct` | 隣接する面の関係を後ろへ移す |
| `nonempty_relStruct_iff_zero` | RelStruct の存在の面添字独立性 |
| `simplexRel_iff_relStruct` | 商の関係と任意の RelStruct の比較 |
| `KanHomotopyGroup` | 次数 n + 1 のホモトピー類の商 |
| `KanHomotopyGroup.mk_eq_iff` | 商の等式と充填関係の同値 |
| `KanHomotopyGroup.sound` | 任意の RelStruct を類の等式へ送る |
| `KanHomotopyGroup.mul_unique` | 積の充填の類の一意性 |
| `KanHomotopyGroup.mul_congr_left` | 左代表の独立性 |
| `KanHomotopyGroup.mul_congr_right` | 右代表の独立性 |
| `KanHomotopyGroup.mul_eq` | 指定した充填による積の計算 |
| `KanHomotopyGroup.exists_left_inverse` | 外側ホーンによる左逆元 |
| `KanHomotopyGroup.instGroup` | 商の群構造 |
| `mapSimplex` | 基点を保つ後合成 |
| `mapRelStruct` | 関係の充填の後合成 |
| `mapMulStruct` | 積の充填の後合成 |
| `KanHomotopyGroup.map` | 誘導群準同型 |
| `KanHomotopyGroup.map_id` | 恒等射の保存 |
| `KanHomotopyGroup.map_comp` | 合成の保存 |

追加の主要宣言：

| ファイル | 宣言（共通接頭辞は同じ） | 内容 |
| --- | --- | --- |
| `HomotopyDegreeZero.lean` | `KanHomotopyZero` | RelStruct₀ の商による零次数 |
| 同上 | `KanHomotopyZero.equivPiZero` | Mathlib の π₀ との全単射 |
| 同上 | `KanHomotopyZero.equivPiZero_map` | π₀ との比較の自然性 |
| `HomotopyInvariance.lean` | `RelativePrism.sectionRel` | prism の隣接断面の RelStruct |
| 同上 | `KanHomotopyGroup.eq_of_relativeHomotopy` | 相対ホモトピーを類の等式へ送る |
| 同上 | `KanHomotopyGroup.map_eq_of_basedHomotopy` | 基点固定ホモトピーによる群準同型の不変性 |
| 同上 | `KanHomotopyGroup.equivOfBasedHomotopyInverse` | ホモトピー逆が誘導する群同型 |
| 同上 | `KanHomotopyZero.map_eq_of_homotopy` | 零次数のホモトピー不変性 |
| `Commutativity.lean` | `AdjacentProduct.flip` | 隣接する面の積の反転の充填 |
| 同上 | `FourStruct.exists_fill` | 四面の指定を持つ Kan 充填の存在 |
| 同上 | `FourReduction.class_eq` | 四面から積の式を得る |
| 同上 | `FourComparison.compare` | 正順・逆順の充填の比較 |
| 同上 | `KanHomotopyGroup.mul_comm` | 二以上の次数での可換性 |
| `HomotopyIndexing.lean` | `KanHomotopy` | 実際の自然数次数で添字付けした π_n |
| 同上 | `KanHomotopy.map` | 全自然数次数の誘導写像 |
| 同上 | `KanHomotopy.map_id`、`map_comp` | 全次数の関手性 |
| 同上 | `KanHomotopy.map_point` | 全次数の基点保存 |
| 同上 | `KanHomotopy.map_eq_of_basedHomotopy` | 全次数のホモトピー不変性 |

L9b の公開入口は `FibrationSequence.lean`。fiber と連結射の実構成は
`FibrationBoundary.lean`、完全性は `FibrationExactness.lean`、自然性は
`FibrationNaturality.lean`、群準同型性は `FibrationMultiplication.lean` に分ける。

| 宣言 | 内容 |
| --- | --- |
| `fibration_pullback_snd` | ホーンの RLP による fibration の引き戻し閉性 |
| `KanFiber`、`fiberι`、`fiberPoint` | 点からの実際の引き戻しとその基点 |
| `fiberLift`、`fiber_hom_ext` | fiber の普遍性 |
| `BoundaryLift`、`boundaryLift_nonempty` | 定数ホーンの相対持ち上げの存在 |
| `BoundaryLift.boundary` | 最後の面を fiber の代表へ送る |
| `BoundaryLiftComparison.rel` | 二つの持ち上げの境界を fiber 内の RelStruct で結ぶ |
| `BoundaryLift.boundary_class_eq` | 持ち上げの選択独立性 |
| `BoundaryLift.transport` | 底の RelStruct に沿う境界保存の持ち上げ |
| `connecting` | π_(n+1)(B) → π_n(fiber) の商上の写像 |
| `connecting_eq` | 任意の持ち上げによる連結写像の計算 |
| `connecting_one` | 連結写像の基点保存 |
| `fiber_map_connecting` | 包含の誘導写像と連結射の合成は基点に定数 |
| `connecting_map` | 射影の誘導写像と連結射の合成は基点に定数 |

L9b の追加の公開宣言：

| 宣言 | 内容 |
| --- | --- |
| `ZeroRelations.symm`、`trans` | 二次元ホーンから零次数の関係の対称性・推移性 |
| `KanHomotopyZero.mk_eq_iff` | 零次数でも単一の RelStruct₀ で商の等式を検出 |
| `KanHomotopy.mk_eq_iff_relStruct` | 全自然数次数で商の等式と RelStruct の存在の同値 |
| `exact_connecting_fiber_all` | fiber の零次数を含む全次数の完全性 |
| `exact_fiber_total_all` | 全空間の零次数を含む全次数の完全性 |
| `exact_total_base_all` | 底の全正次数の完全性、π₁(B) → π₀(fiber) を含む |
| `FibrationSquare.fiberMap` | 可換四角形から fiber 列の射を作る |
| `FibrationSquare.connecting_natural` | 全次数の連結写像の自然性 |
| `ConnectingProduct.exists_product_lift` | fiber の積を境界に持つ相対持ち上げ |
| `connecting_mul` | 標的が正次数の連結写像の積保存 |
| `connectingHom` | π_(n+2)(B) → π_(n+1)(fiber) の群準同型 |
| `fiberLongExact` | 零次数を含む全箇所の完全性の集約定理 |

原像は零ホモトピーの相対充填によって実際に構成する。
群の法則、完全性、自然性を入力構造に移していない。
L9b の完了は、Kan fibration の具体的な fiber 列のホモトピー長完全列の完成を意味する。
スペクトルの fiber 列への昇格は L9c の工程であり、まだ主張しない。

`KanHomotopy X (n + 1) x` は群、`KanHomotopy X (n + 2) x` は可換群。
正次数の群準同型としての界面は `KanHomotopyGroup.map`。
零次数には群を付けない。
相対ホモトピーから類の等式への向きと、任意の面添字の RelStruct との比較を証明済み。
一般の相対写像のホモトピー類との圏論的同定はここでは主張しない。

検証コマンド：

```sh
set -o pipefail
lake build SerrePositivity.KST.Spectra
lake env lean scripts/audit_kst_spectra.lean
```

L9a 保存時の結果：対象ビルド成功。監査は私有宣言を含め 367 宣言、5 モジュールで標準三公理のみ。
L9b の連結写像の保存時：対象ビルド成功。476 宣言、6 モジュールで標準三公理のみ。
L9b の正次数の完全性の保存時：対象ビルド成功。517 宣言、7 モジュールで標準三公理のみ。
L9b 完了時：対象ビルド成功。631 宣言、11 モジュールで標準三公理のみ。
工程区切りの全体ビルドも終了コード 0、8370 jobs で成功。
ルートには指定の public import 一行を追加済み。
ルートは他レーンの未コミット変更を含むので、この保存ではコミット対象から外す。

## 21. L9c の切断写像空間の構成部品

`TruncatedMapping.lean` に境界比較射を持つ点つき写像空間の塔を構成した。
これは具体的な単体集合の射 `step` に対する一般構成である。
スペクトルの suspension が誘導する `step` の実装は次の工程に残る。
一般構成をもってスペクトルの写像空間の実装完了とはしない。

| 主要宣言 | 内容 |
| --- | --- |
| `TruncatedMapping.stage` | 切断写像空間と最終段の評価を同時に帰納構成 |
| `TruncatedMapping.space` | 切断写像空間の基礎単体集合 |
| `TruncatedMapping.evaluation` | 最終段への評価 |
| `TruncatedMapping.restriction` | 引き戻しの第二射影による遷移 |
| `TruncatedMapping.evaluation_condition` | 境界比較との整合条件 |
| `TruncatedMapping.restriction_fibration` | 単射の制限を引き戻した遷移の fibration 性 |
| `TruncatedMapping.total` | 全切断の整合族の単体集合 |
| `TruncatedMapping.total_projection_fibration` | 初段への射影の fibration 性 |
| `TruncatedMapping.total_kanComplex` | 源の構造単射・標的各段 Kan による極限の Kan 性 |

参照：BF 1978 §2、HTT A.3.3。
保存単位の対象ビルド 1524 jobs 成功。
私有宣言を含む 14 モジュール 688 宣言で標準三公理のみ。
次は suspension・loop の随伴と、実際のスペクトルからの境界比較射を実装する。

## 22. L9c の Ω スペクトルの対象と具体的写像空間

`SuspensionLoop.lean` に円との smash、円からの内部 Hom と随伴を接続した。
`HomotopyIsomorphism.lean` に全基点での π_* 同型を全単射性の述語として定義した。
この述語は既に構成したホモトピー群の誘導写像に関する条件である。
`OmegaSpectrum.lean` の対象は、各段 Kan・構造射単射・随伴構造射 π_* 同型を保持する。
構造射から具体的な `mappingStep` を構成し、切断写像空間の一般構成に代入した。
この写像空間の Kan 性まで証明済み。

| 主要宣言 | 内容 |
| --- | --- |
| `suspension` | 単体的円との reduced smash |
| `loopSpace` | 単体的円からの点つき内部 Hom |
| `loopSpace_kanComplex` | Kan な標的の loop は Kan |
| `suspensionLoopEquiv` | suspension・loop の通常の Hom 随伴 |
| `suspensionHom` | suspension が誘導する写像空間の射 |
| `suspensionHom_curry'` | 通常の射への suspension の作用との一致 |
| `KanPiIsomorphism` | 全基点・全自然数次数の π_* 同型という条件 |
| `KanPiIsomorphism.id` / `.comp` | 恒等・合成に関する閉性 |
| `PointedKanComplex` | 点つき Kan 複体 |
| `OmegaSpectrum` | 承認済み BF 方式の対象 |
| `OmegaSpectrum.mappingStep` | 実際の構造射からの境界比較 |
| `OmegaSpectrum.truncatedHom` | 切断写像空間 |
| `OmegaSpectrum.mappingSpace` | 全切断の整合族 |
| `OmegaSpectrum.mappingSpace_kanComplex` | 構成した写像空間の Kan 性 |
| `TruncatedMapping.totalEvaluation_condition` | 各段の評価の厳密な境界整合性 |

参照：BF 1978 §2、HTT A.3.3、HA §1.4.2。
保存単位の対象ビルド 1556 jobs 成功。
私有宣言を含む 17 モジュール 747 宣言で標準三公理のみ。
既存 Spectra の通常の圏論的な円・smash・内部 Hom の構成を借りている。
安定モデル構造や HT-KQ は import していない。
未完了：厳密なスペクトルの射との同定、厳密合成、単体的圏、coherent nerve。
未完了：loop のホモトピー群の次数移動、整数次数 π_*、段の選択独立性。
未完了：置換補題、スペクトルの fiber 列と長完全列、L9d・L9e。
次は構成した写像空間の各段評価と通常の点つき射との比較を証明する。

## 23. L9c の厳密射と写像空間の零次単体

等化子で構成した源の制限と、点つき閉構造から得る pre が一致することを証明した。
随伴を構成する Hom 同値は命題として比較し、定義的な一致を仮定しない。
切断写像空間の極限へ整合族を持ち上げる普遍性を任意の単体集合パラメータで証明した。
全段への評価による極限への射の一意性も証明済み。
厳密可換なスペクトルの射を定義し、段ごとの合成で通常の圏を構成した。
その射と構成済みの Kan 写像空間の零次単体を実際の同値で比較した。

| 主要宣言 | 内容 |
| --- | --- |
| `PointedMapping.prePointed` | 源の制限を点つき射として扱う |
| `PointedMapping.smashCurry_pre` | smash 第一変数と源の制限の随伴の自然性 |
| `PointedMapping.prePointed_eq_closedPre` | 等化子の制限と閉構造の pre の一致 |
| `PointedMapping.curry'_pre` | 頂点表示への源の制限の作用 |
| `TruncatedMapping.familyStage` | 整合族の切断への持ち上げ |
| `TruncatedMapping.familyLift` | 任意のパラメータから極限への持ち上げ |
| `TruncatedMapping.familyLift_evaluation` | 持ち上げの評価の計算 |
| `TruncatedMapping.total_hom_ext` | 全段評価による極限への射の一意性 |
| `pointedHomVertexEquiv` | 点つき射と点つき内部 Hom の頂点の同値 |
| `OmegaSpectrum.Hom` | 構造射と厳密可換な点つき射の族 |
| `OmegaSpectrum.category` | 段ごとの合成による通常の圏 |
| `OmegaSpectrum.evaluation` | 写像空間から段ごとの Hom への評価 |
| `OmegaSpectrum.mappingStep_vertex` | 境界比較の頂点への作用 |
| `OmegaSpectrum.homOfVertex` | 写像空間の頂点から厳密な射を復元 |
| `OmegaSpectrum.vertexOfHom` | 厳密な射を整合族の頂点へ移す |
| `OmegaSpectrum.vertex_ext` | 全段評価による頂点の一意性 |
| `OmegaSpectrum.homVertexEquiv` | 厳密な射と写像空間の零次単体の同値 |

参照：BF 1978 §2、HTT A.3.3。
保存単位の対象ビルド 1561 jobs 成功。
私有宣言を含む 21 モジュール 821 宣言で標準三公理のみ。
未完了：単体的合成の極限への持ち上げと単位律・結合律、γ1 の適用。
整数次数群・置換・fiber 列・有理化・hG・Tot は引き続き未完了。
次は各段の点つき Hom の単体的合成を構成し、極限の普遍性で写像空間へ持ち上げる。

## 24. L9c の各段の単体的合成と suspension の豊穣性

点つき閉 smash の自己豊穣を、忘却の lax monoidal 関手で単体的豊穣へ移した。
その Hom と零次単体の同値は既存の等化子・頂点表示と一致する。
源と標的への豊穣作用を、相対充填に使った pre と後合成に比較した。
左テンソルの写像対象への作用が豊穣合成を保つことを一般の閉モノイダル圏で証明した。
これを suspension に特殊化し、単体的豊穣関手として構成した。
構造射と整合する二つのパラメータ付き写像の合成の整合性も一般に証明した。

| 主要宣言 | 内容 |
| --- | --- |
| `PointedEnrichment.simplicialCategory` | 点つき単体集合の単体的圏 |
| `PointedEnrichment.hom_eq` | 等化子による Hom との一致 |
| `PointedEnrichment.vertexEquiv_eq` | 点つき射と頂点の同値との一致 |
| `PointedEnrichment.whiskerRight_eq` / `.whiskerLeft_eq` | 源と標的への作用の比較 |
| `TensorMapping.map` | 一般の閉モノイダル圏での左テンソルの写像対象への作用 |
| `TensorMapping.comp` | 一般の左テンソルの豊穣合成保存 |
| `suspensionHom_id` / `suspensionHom_comp` | 点つき豊穣の単位・合成の保存 |
| `suspensionHom_simplicial_comp` | 単体的豊穣の合成保存 |
| `suspensionEnrichedFunctor` | 単体的豊穣関手としての suspension |
| `enriched_comp_middle` | 中間の射の前合成と後合成の整合性 |
| `enriched_compatible_comp` | 構造射との整合条件の合成に関する閉性 |

参照：BF 1978 §2、HTT A.3.3。
保存単位の対象ビルド 1573 jobs 成功。
私有宣言を含む 25 モジュール 844 宣言で標準三公理のみ。
次はこの合成の整合性をスペクトルの評価族へ適用し、極限へ合成を持ち上げる。
スペクトルの単体的圏と coherent nerve の構成は引き続き未完了。

## 25. L9c の局所 Kan な単体的圏と coherent nerve

各段の単体的合成を切断写像空間の極限へ持ち上げた。
構造整合性は豊穣関手としての suspension と中間の射の移動から証明した。
全段評価による外延性で単位律と結合律を証明した。
通常の厳密な射の恒等・合成との比較を行い、単体的圏に束ねた。
構成済みの Kan 写像空間に N レーンの γ1 を適用した。
`Sp := SimplicialNerve OmegaSpectrum` の quasicategory 性を証明済み。

| 主要宣言 | 内容 |
| --- | --- |
| `OmegaSpectrum.compositionFamily` | 各段評価後の単体的合成 |
| `OmegaSpectrum.compositionFamily_condition` | 合成の構造射との整合性 |
| `OmegaSpectrum.mappingComposition` | 極限へ持ち上げた合成 |
| `OmegaSpectrum.mappingComposition_evaluation` | 合成の各段評価 |
| `OmegaSpectrum.mappingIdentity` | 恒等射の終対象パラメータによる単位 |
| `OmegaSpectrum.mappingIdentity_evaluation` | 単位の各段評価 |
| `OmegaSpectrum.mappingIdentity_comp` / `.mappingComposition_identity` | 左右の単位律 |
| `OmegaSpectrum.mappingComposition_assoc` | 結合律 |
| `OmegaSpectrum.vertexOfHomMap_comp` | 通常の合成と単体的合成の一致 |
| `OmegaSpectrum.mappingEnrichedCategory` | 単体集合に豊穣化した圏 |
| `OmegaSpectrum.simplicialCategory` | 通常の射と接続した単体的圏 |
| `Sp` | BF 方式の Ω スペクトルの coherent nerve |
| `sp_quasicategory` | γ1 による quasicategory 性 |

参照：BF 1978 §2、HTT A.3.3、HTT 1.1.5.10、Kerodon 2.4.5.1、HA §1.4.2。
保存単位の対象ビルド 1618 jobs 成功。
私有宣言を含む 29 モジュール 876 宣言で標準三公理のみ。
Sp の構成の区切りで全体ビルドも実行したが終了コード 1。
L9 の import 閉包外の `InfinityCategories/F1.lean:1` で
`F1/CoherentOrderDiagrams.olean` が見つからないというエラーだった。
他レーンを編集せず、L9 自身の対象ビルド成功と区別して記録する。
導来写像空間を持つ正しい Sp との比較は主張しない。これは γ3 後の工程。
未完了：loop のホモトピー群の次数移動、整数次数 π_* と段の選択独立性。
未完了：cofibrant・Kan 置換、スペクトルの fiber 列と長完全列。
L9d の telescope 有理化、L9e の hG・Tot・有理 Shapiro も未完了。
次は path space の fiber 列と収縮から loop の次数移動を証明する。

## 26. L9c の path fibration の構成

始点を基点とする区間と、零次球面からの終点包含を構成した。
終点包含の単射性は、各次数の自由基点の二成分の像を頂点値で比較して証明した。
区間からの点つき Hom を path space とし、終点の制限と閉構造の単位同型を合成した。
標的が Kan のとき終点評価は Kan fibration である。

| 主要宣言 | 内容 |
| --- | --- |
| `pointedInterval` | 始点を基点とする Δ[1] |
| `intervalEndpoint` | 点つき零次球面からの終点包含 |
| `coprod_simplex_cases` | 余積の単体の二成分への分解 |
| `intervalEndpoint_mono` | 終点包含の単射性 |
| `basedPathSpace` | 基点に始まる path の単体集合 |
| `basedPathSpace_kanComplex` | Kan 標的の path space の Kan 性 |
| `pathEndpoint` | 終点評価 |
| `pathEndpoint_fibration` | 終点評価の Kan fibration 性 |

参照：Goerss–Jardine I §7、Kerodon §§3.1.3、3.2.5。
保存単位の対象ビルド 1620 jobs 成功。
私有宣言を含む 31 モジュール 895 宣言で標準三公理のみ。
未完了：path space の収縮、終点 fiber と loopSpace の同定、次数移動の同型。
次は既存 Core の標準単体の先頭頂点への収縮を借りて path space を収縮する。
§25 の対象ビルドの jobs 数はログの実数 1618 に訂正した。

## 27. L9c の path space の基点固定収縮

任意の単体集合パラメータから点つき Hom への curry を等化子で構成した。
Core の区間の先頭頂点への収縮を借り、全時刻で基点を固定することを検査した。
path の区間変数を収縮する再パラメータ付けと評価を合成した。
これを curry して path space の収縮を作った。
時刻零が定数 path、時刻一が恒等射、全時刻で定数 path の基点を固定する。
基点生成部分複体に相対的なホモトピーに移し、全自然数次数のホモトピー類を消去した。

| 主要宣言 | 内容 |
| --- | --- |
| `PointedMapping.paramCurry` | 基点を保つパラメータ付き写像族の curry |
| `PointedMapping.uncurry_basepoint` | 評価の源の基点での定数性 |
| `PointedMapping.uncurry_parameter_basepoint` | 定数写像のパラメータ上の評価 |
| `intervalContractionMap` / `intervalContraction` | 区間の基点固定収縮 |
| `intervalContraction_zero` / `.intervalContraction_one` | 区間の収縮の端点 |
| `pathReparametrization` | path の区間変数の収縮 |
| `pathEvaluation` | curry 前の path の評価 |
| `pathContractionBody` | 再パラメータ付けした評価族 |
| `pathContraction` | path space の収縮写像 |
| `pathContraction_zero` / `.pathContraction_one` | path space の収縮の端点 |
| `pathContraction_constant` | 定数 path の基点の固定 |
| `KanHomotopy.map_const` | 定数射の全次数の誘導写像 |
| `pathContraction_basedHomotopy` | 基点生成部分複体に相対的な収縮 |
| `basedPathSpace_homotopy_eq_point` | 全自然数次数のホモトピー類の自明性 |
| `basedPathSpace_homotopy_subsingleton` | 零次数を含む一元性 |

参照：Goerss–Jardine I §7、Kerodon §3.2.5、HTT A.3.3。
保存単位の対象ビルド 1643 jobs 成功。
私有宣言を含む 38 モジュール 943 宣言で標準三公理のみ。
未完了：終点 fiber と loopSpace の同定、次数移動の同型、整数次数群と段の独立性。
次は終点 fiber を円からの点つき Hom に同定する。

## 28. L9c の loop と path 終点 fiber の同定

区間の境界を、終点と始点の余積と全単体次数で同定した。
二端点を潰した cofiber と標準の単体的円の点つき同型を構成した。
一般の点つき射の基礎 cofiber が点つき pushout になることを証明した。
内部 Hom の反変関手の極限保存と基点忘却の右随伴性から、Hom の pullback を得た。
零対象からの Hom の終対象性と、単位からの Hom の同型を使って path の終点 fiber に移した。
円からの点つき Hom とこの fiber は実際の単体集合として同型である。
L9b の fiberPoint を用いる形への基点の移送も行い、定数 loop の基点保存を証明した。

| 主要宣言 | 内容 |
| --- | --- |
| `intervalBoundaryMap` | 二端点の余積から境界への自然な射 |
| `intervalBoundaryMap_isIso` | 全次数の単射・全射性による同型性 |
| `endpointCircleIso` | 二端点の商と標準の円の点つき同型 |
| `pointedCofiberProjection` / `.pointedCofiberDesc` | 点つき商と降下 |
| `pointedCofiber_isPushout` | 点つき cofiber の pushout 表示 |
| `cofiberMappingFunctor_preservesLimitsOfShape` | 反変 Hom の極限保存 |
| `cofiberMapping_isPullback` | cofiber からの Hom の pullback 表示 |
| `homPointIsTerminal` | 零対象からの点つき Hom の終対象性 |
| `endpointCircleMapping_isPullback` | path の終点評価の基点上の pullback |
| `loopPathFiberIso` | loop と基点上の path fiber の同型 |
| `fiberIsoOfEq` | fiber の基点の等式による移送 |
| `loopBasedPathFiberIso` | L9b の fiber と一致する形の同型 |
| `loopBasedPathFiberIso_basepoint` | 定数 loop と fiberPoint の基点の一致 |

参照：Goerss–Jardine I §7、Kerodon §3.2.5、HTT A.3.3。
保存単位の対象ビルド 1648 jobs 成功。
私有宣言を含む 43 モジュール 1023 宣言で標準三公理のみ。
次は構成済みの path fiber 列と収縮から連結射の全単射性と loop の次数移動を導く。
整数次数群・段の選択独立性・置換とスペクトルの fiber 列は未完了。

## 29. L9c の正次数の loop 同型と段の比較

単体集合の同型と全基点 π_* 同型から、指定基点の群同型を作る界面を構成した。
全空間の隣接二次数の群が自明な場合、長完全列から連結準同型の全単射性を導いた。
これを path fibration に適用し、正次数の loop の次数移動を群同型として証明した。
Ω 条件の随伴構造射の群同型と合成し、スペクトルの隣接段の正次数の比較を得た。
次段の二以上の次数へ移すことで、各段の一次も含む全ての正次数の群の可換性を得た。
元の群演算を保持し、可換群構造を付けた。

| 主要宣言 | 内容 |
| --- | --- |
| `KanHomotopy.equivOfIso` | 零次数を含む同型によるホモトピー類の同値 |
| `KanHomotopyGroup.equivOfIso` | 指定基点の正次数の群同型 |
| `KanHomotopyGroup.equivOfPiIsomorphism` | 全基点 π_* 同型からの群同型 |
| `connectingHom_bijective_of_total_subsingleton` | 長完全列による連結準同型の全単射性 |
| `connectingHomEquivOfTotalSubsingleton` | 連結準同型による群同型 |
| `loopPositiveHomotopyEquiv` | π_(n+1)(ΩY) ≃ π_(n+2)(Y) |
| `OmegaSpectrum.positiveTransition` | π_(n+1)(X_k) ≃ π_(n+2)(X_(k+1)) |
| `OmegaSpectrum.levelHomotopy_mul_comm` | 各段の一次を含む正次数の可換性 |
| `OmegaSpectrum.levelHomotopyCommGroup` | 元の演算による可換群構造 |

参照：Goerss–Jardine I §7、Kerodon §3.2.5、BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 1652 jobs 成功。
私有宣言を含む 47 モジュール 1050 宣言で標準三公理のみ。
零次数の loop 比較はまだ未完了。正次数の核と像だけから零次数の全単射性を推論しない。
次は path space の全境界充填から零次数の連結写像の単射性も幾何的に証明する。

## 30. L9c の零次数・整数次数と群への関手

区間の始点の包含が anodyne であることをホーンから証明した。
pushout product の持ち上げ対応により、path space の終対象への射は全単射に対して RLP を持つ。
全境界を面の余等化子として貼り合わせ、指定された全ての面を持つ単体を構成した。
零次数の連結写像の像が等しい場合、二つの境界持ち上げと fiber の道を三角形の全境界に貼る。
その充填から基底の一次の類の等しさを得て、零次数の連結写像の単射性を証明した。
長完全列の全射性と合わせ、π₀(ΩY) ≃ π₁(Y) を得た。
定数 loop は単位へ移ることも証明した。
Ω 条件と合成し、スペクトルの各段の零次数にも可換群構造を移した。
隣接段の比較はこれで全自然数次数で群同型となった。
整数次数 j の標準段を |j|+1 とし、隣接比較の反復で任意の k≥−j の表示との群同型を構成した。
標準段の正次数の誘導準同型から、整数次数ごとに可換群への関手を構成した。
段の比較の合成整合性と射に関する自然性は引き続き証明する。

| 主要宣言 | 内容 |
| --- | --- |
| `pointedInterval_basepoint_anodyne` | 区間の始点の anodyne 包含 |
| `basedHom_terminal_rlp_monomorphisms` | anodyne 源の点つき Hom の全境界充填 |
| `BoundaryFaces.isColimit` / `.desc` | 全境界の面の貼り合わせ |
| `BoundaryFaces.exists_filler` | 全境界 RLP による指定面の充填 |
| `connecting_zero_injective` | 零次数の連結写像の単射性 |
| `loopZeroHomotopyEquiv` | π₀(ΩY) ≃ π₁(Y) |
| `loopHomotopyEquiv` | 全自然数次数の loop 比較 |
| `OmegaSpectrum.zeroTransition` | 零次数から次段の一次への群同型 |
| `OmegaSpectrum.levelNaturalCommGroup` | 各段の零次数を含む可換群構造 |
| `OmegaSpectrum.transition` | 全次数の隣接段の群同型 |
| `OmegaSpectrum.iterateTransition` / `.compareLevels` | 隣接比較の反復と共通段での比較 |
| `OmegaSpectrum.homotopyGroup` / `.homotopyGroupEquivAt` | 整数次数の群と任意の許される段での計算 |
| `OmegaSpectrum.homotopyFunctor` | Ω スペクトルから可換群への関手 |

参照：Goerss–Jardine I §7、Kerodon §3.2.5、BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 1665 jobs 成功。
私有宣言を含む 56 モジュール 1166 宣言で標準三公理のみ。
L9c は未完了。置換、スペクトルの fiber 列と長完全列が残る。

## 31. L9c の π_* 同型と置換の基礎補題

整数次数の π_* 同型の性質を構成済みの群準同型の全単射性として定義した。
各段の全基点 π_* 同型から整数次数の π_* 同型が従うことを証明した。
基点固定ホモトピーの相対表示と、点つき射の全自然数次数の誘導写像を整理した。
各段の基点固定ホモトピーから整数次数の準同型の等式を得た。
全ての単射に対する RLP を持つ射では、基点を保つ切断と垂直ホモトピーを実際に充填した。
anodyne な射では Kan な源へのレトラクションと、包含上で固定されたホモトピーを充填した。
両端が Kan の場合、それぞれ全基点 π_* 同型であることを L9 のホモトピー類で証明した。
ホーンの Kan 置換を点つき関手と自然な単位に拡張した。
元の対象が Kan ならその単位は全基点 π_* 同型である。
境界の小対象論法による分解も点つき対象に移した。
標的が Kan なら中間対象は Kan、左因子は単射、右因子は全基点 π_* 同型である。
これは置換の各段に用いる基礎補題であり、スペクトル全体の置換はまだ構成していない。
coherent nerve の導来写像空間との比較は引き続き γ3 後に扱う。

| 主要宣言 | 内容 |
| --- | --- |
| `OmegaSpectrum.PiIsomorphism` | 全整数次数の誘導準同型の全単射性 |
| `OmegaSpectrum.PiIsomorphism.groupEquiv` | その各次数の群同型 |
| `OmegaSpectrum.piIsomorphism_of_levelwise` | 各段の π_* 同型からの帰結 |
| `pointedRelativeHomotopy` | 全区間の基点固定式から相対ホモトピーへ |
| `OmegaSpectrum.homotopyMap_eq_of_levelHomotopy` | 各段の基点固定ホモトピーによる不変性 |
| `kanPiIsomorphism_of_monoRight` | 全ての単射への RLP から全基点 π_* 同型 |
| `kanPiIsomorphism_of_anodyne` | Kan 複体間の anodyne 射の全基点 π_* 同型 |
| `PointedKanReplacement.functor` / `.unit` | 点つき Kan 置換と自然な比較射 |
| `PointedKanReplacement.obj_kanComplex` | 置換の値の Kan 性 |
| `PointedKanReplacement.unit_piIsomorphism` | 元が Kan の場合の単位の π_* 保存 |
| `PointedFactorization.middle` / `.left` / `.right` | 点つき射の境界による分解 |
| `PointedFactorization.right_rlp` | 右因子の全ての単射への RLP |
| `PointedFactorization.middle_kanComplex` | 標的が Kan の場合の中間対象の Kan 性 |
| `PointedFactorization.right_piIsomorphism` | 右因子の全基点 π_* 同型性 |

参照：Goerss–Jardine I §7、Kerodon §3.2.1、BF 1978 §2、HTT A.3.3、HA §1.4.2。
保存単位の対象ビルド 1832 jobs 成功。
私有宣言を含む 62 モジュール 1221 宣言で標準三公理のみ。
L9c は未完了。段の比較の整合性、列全体の置換、スペクトルの fiber 列と長完全列が残る。

## 32. L9c の Kan Ω 列の cofibrant 置換

構造射に単射性を要求しない `KanSequence` と、その随伴構造射による Ω 条件を定義した。
厳密な列の射は随伴構造射に関しても可換であることを証明した。
零段を元の段とし、各後続段で前段の比較射を suspension して元の構造射と合成する。
その射の境界の小対象論法による分解を取り、中間対象を次の段、左因子を新しい構造射とした。
写像柱に続けて単射化する代わりに、同じ BF の単射条件を境界 cell 分解で直接実現した。
対象と Hom と Ω 条件の承認済み仕様に変更はない。
元の標的段が Kan なので各中間段も Kan、各比較射は全ての単射への RLP を持つ。
比較射は全基点 π_* 同型である。
点つき Hom の後合成も全ての単射への RLP を保つことを相対積の充填から証明した。
したがって比較射を loop に移しても全基点 π_* 同型である。
随伴構造射の可換正方形と後の射の打ち消しから、置換した列の Ω 条件を証明した。
構造射が単射でない Kan Ω 列から、承認済みの BF 対象への実際の置換が得られた。
元がすでに Ω スペクトルの場合は厳密な比較射をスペクトルの射として束ねた。
その比較射の全整数次数の π_* 同型性を証明した。
また、L9b の fiber に点つき構造を付け、点つき包含と普遍的な持ち上げを構成した。
スペクトルの fiber 列の Ω 条件と整数次数長完全列はまだ未完了。
Kan でない列全体の fibrant 置換の構造射への接続も未完了。

| 主要宣言 | 内容 |
| --- | --- |
| `KanSequence` / `.OmegaCondition` | 単射性を要求しない Kan 列と Ω 条件 |
| `KanSequence.replacementStage` | 境界 cell 分解による各段の帰納構成 |
| `KanSequence.cofibrantReplacement` | 構造射が単射な Kan 列への置換 |
| `KanSequence.replacementProjection` | 元の列への厳密な比較射 |
| `KanSequence.replacementProjection_piIsomorphism` | 各段の全基点 π_* 同型 |
| `PointedMapping.post_rlp_monomorphisms` | 点つき Hom の後合成による RLP 保存 |
| `KanPiIsomorphism.of_comp` | 後の π_* 同型の打ち消し |
| `KanSequence.Hom.adjoint_comm` | 随伴構造射に関する可換性 |
| `KanSequence.Hom.omegaCondition_of_target` | RLP 比較射による Ω 条件の移送 |
| `KanSequence.cofibrantOmegaSpectrum` | Kan Ω 列から BF 対象への置換 |
| `OmegaSpectrum.cofibrantProjection_piIsomorphism` | 置換比較の全整数次数の π_* 同型 |
| `pointedFiber` / `pointedFiberι` / `pointedFiberLift` | 点つき fiber と普遍性 |

参照：Goerss–Jardine I §7、BF 1978 §2、HTT A.3.3、HA §1.4.2。
保存単位の対象ビルド 1840 jobs 成功。
私有宣言を含む 67 モジュール 1320 宣言で標準三公理のみ。
L9c は未完了。次は段ごとの fiber を列にして Ω 条件と長完全列へ接続する。

## 33. L9c の fiber の Kan 列と正次数の比較

点つき fiber の包含と元の射の合成が零射であることを証明した。
零合成からの点つき持ち上げを用意し、suspension が零射を保つことを左随伴性から得た。
各段が Kan fibration である列の射について、各段の fiber の suspension 構造射を構成した。
各 fiber は Kan なので、単射性と Ω 条件をまだ要求しない Kan 列を得た。
包含は列の厳密な射である。
さらに、可換性を要求しない群の二つの完全な五項列について五項補題を証明した。
全空間と底の全基点 π_* 同型を、L9b の自然な長完全列の五項へ適用した。
その結果、fiber 間の誘導写像は全ての正次数で全単射であることを証明した。
零次数の fiber の比較は未完了であり、正次数の五項補題からは推論しない。
fiber の Ω 条件と整数次数長完全列もまだ完了扱いにしない。

| 主要宣言 | 内容 |
| --- | --- |
| `pointedFiberι_comp` | fiber 包含と元の射の零合成 |
| `pointedFiberLiftOfZero` | 零合成から点つき fiber への持ち上げ |
| `KanSequence.Hom.fiberSigma` | fiber の suspension 構造射 |
| `KanSequence.Hom.fiber` | 各段の fiber を束ねた Kan 列 |
| `KanSequence.Hom.fiberInclusion` | 全空間の列への厳密な包含 |
| `group_five_lemma` | 非可換群でも有効な五項補題 |
| `KanHomotopyGroup.map_square` | 基点を明示した群の可換正方形 |
| `FibrationSquare.fiberMap_positive_bijective` | 全空間・底の π_* 同型から fiber の正次数の全単射 |

参照：Goerss–Jardine I §§7–8、Kerodon §3.2.6、BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 1844 jobs 成功。
私有宣言を含む 71 モジュール 1341 宣言で標準三公理のみ。

## 34. L9c の段の比較の合成整合性

整数次数 j の許される最小段を (−j).toNat とした。
その段から各段への隣接比較の反復を共通の源とし、各段同士の比較を定義した。
標準の計算段 |j|+1 と整数次数群の定義は変わらない。
比較の恒等法則、逆法則、三段の合成法則を証明した。
整数次数群から任意段への表示も、この合成法則を満たす。
射に関する自然性と隣接構造射との計算式は引き続き扱う。

| 主要宣言 | 内容 |
| --- | --- |
| `OmegaSpectrum.initialLevel` | 最小の許される計算段 |
| `OmegaSpectrum.initialLevel_admissible` / `.initialLevel_le` | 非負次数と最小性 |
| `OmegaSpectrum.compareLevels_refl` | 同じ段の比較は恒等 |
| `OmegaSpectrum.compareLevels_symm` | 逆向きの比較は逆同型 |
| `OmegaSpectrum.compareLevels_trans` | 三段の比較の合成整合性 |
| `OmegaSpectrum.homotopyGroupEquivAt_canonical` | 標準段の表示は恒等 |
| `OmegaSpectrum.homotopyGroupEquivAt_trans` | 任意段での表示と段の比較の整合性 |

参照：BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 1845 jobs 成功。
私有宣言を含む 72 モジュール 1359 宣言で標準三公理のみ。
L9c は未完了。loop と段の比較の自然性、零次数の fiber 比較、fiber の Ω 条件、
Kan でない列の置換の構造射への接続、整数次数長完全列が残る。

## 35. L9c の loop・隣接比較・任意段表示の自然性

長完全列の自然性を、標的の指定基点の等式による移送を含む界面へ延ばした。
path の終点評価と、loop の円の表示・fiber 表示が標的の射に関して自然であることを証明した。
path の連結写像による同値を全自然数次数の集合の同値としてまとめた。
連結同値、loop の fiber 同型、標的の基点への移送の三つの可換図式を合成した。
これにより π_n(ΩY) ≃ π_(n+1)(Y) の自然性を零次数も含めて証明した。
随伴構造射の可換式と合成し、Ω スペクトルの隣接段の全次数の比較の自然性を得た。
零次数で移した群演算が、元の連結成分の誘導写像で保たれることをこの自然性から証明した。
各段・各自然数次数の可換群への関手は、順写像として元の KanHomotopy.map を持つ。
反復比較、添字の等式の移送、逆比較へ自然性を延ばした。
整数次数群の任意の許される段による表示を、可換群への関手の自然同型として束ねた。
その帰結として、整数次数の誘導写像の全単射性は任意の許される段の誘導写像で検証できる。

| 主要宣言 | 内容 |
| --- | --- |
| `FibrationSquare.fiberMapAt` / `.connecting_natural_at` | 指定基点の fiber 射と連結写像の自然性 |
| `pathEndpoint_natural` / `pathFiberMap` | path fibration の自然な可換正方形 |
| `loopBasedPathFiberIso_natural` | loop の fiber 表示の自然性 |
| `pathConnectingEquiv` / `.pathConnectingEquiv_natural` | path の全次数の連結同値と自然性 |
| `loopHomotopyEquiv_natural` | 零次数を含む loop の次数移動の自然性 |
| `OmegaSpectrum.transition_formula` / `.transition_natural` | 隣接比較の計算式と自然性 |
| `OmegaSpectrum.levelMap` / `.levelFunctor` | 零次数を含む各段の可換群への関手 |
| `OmegaSpectrum.iterateTransition_natural` | 反復比較の自然性 |
| `OmegaSpectrum.compareLevels_natural` | 任意の二段の比較の自然性 |
| `OmegaSpectrum.homotopyFunctorIsoAt` | 整数次数群と任意段の群の関手の自然同型 |
| `OmegaSpectrum.homotopyMap_bijective_iff_levelMap` | π_* 同型性の任意段での検証 |

参照：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 1851 jobs 成功。
私有宣言を含む 78 モジュール 1425 宣言で標準三公理のみ。
L9c は未完了。零次数の fiber 比較、fiber の Ω 条件、Kan でない列の構造射を含む置換、
整数次数長完全列、反復比較の隣接構造射との添字正規化が残る。

## 36. L9c の構造射を含む段ごとの Kan 置換

Kan 性をまだ要求しない `PointedSequence` を定義した。
anodyne な点つき射に沿う Kan 標的への延長を、元の基点を保つ点つき射として構成した。
元の構造射を次段の Kan 置換へ合成し、その随伴を次段の loop に取った。
この loop は Kan なので、anodyne な現段の置換単位に沿って随伴構造射を延長できる。
uncurry によって置換した二段の suspension 構造射を得た。
置換単位との厳密可換性を、延長の制限式と随伴の逆関係から証明した。
任意の点つき列から、構造射を持つ Kan 列への実際の比較射を得た。
延長の選択に列の関手性は主張しない。
任意の入力について Ω 条件が成立するとは主張しない。
元の段が Kan である場合は、比較射の全基点 π_* 同型性を証明した。

| 主要宣言 | 内容 |
| --- | --- |
| `PointedExtension.exists_extension` / `.extend` | anodyne 射に沿う点つき延長 |
| `PointedSequence` / `.Hom` | Kan 条件を持たない列と厳密射 |
| `PointedSequence.kanReplacementAdjoint` / `.kanReplacementSigma` | 延長された随伴と構造射 |
| `PointedSequence.kanReplacement_unit_comm` | 単位と構造射との厳密可換性 |
| `PointedSequence.kanReplacement` / `.kanReplacementUnit` | Kan 列への置換と比較射 |
| `PointedSequence.kanReplacementUnit_piIsomorphism` | 元の段が Kan の場合の π_* 保存 |

参照：Goerss–Jardine I §7、BF 1978 §2、HTT A.3.3。

## 37. L9c の fiber の零次数と全基点 π_* 比較

零次数の基点付きの類と基点を選ばない連結成分の界面を整えた。
全基点 π_* 条件から連結成分の全単射性を得る際には、源の指定頂点の存在を明示した。
全空間の参照頂点を任意に選び直し、固定 fiber の連結成分へ値を持つ連結写像を定義した。
零次数の完全性と自然性をこの表示へ移した。
fiber の零次数比較の単射性では、第一の原像の頂点を参照基点に取った。
底の基本群からの連結写像で第二の原像を表示し、標的の全空間の基本群へ戻した。
全空間の基本群の全射性と底の基本群の単射性を使って、元の連結成分が一致すると示した。
全射性では、先に全空間の連結成分を持ち上げた。
底の連結成分の単射性と零次数の完全性で源の fiber の頂点を選び、参照基点をそこへ移した。
標的の残りの成分を底の基本群の全射性と連結写像の自然性で持ち上げた。
この零次数の全単射性と正次数の五項補題を合わせ、fiber の全基点・全次数の π_* 同型性を得た。
任意の包含と可換な fiber 射にも、普遍性の一意性で移せる形にした。

| 主要宣言 | 内容 |
| --- | --- |
| `KanHomotopyZero.map_bijective_iff_piZero` | 基点付き零次数と連結成分の全単射性の同値 |
| `KanPiIsomorphism.piZero_bijective_at` | 指定頂点を持つ源での連結成分の全単射性 |
| `componentConnecting` | 固定 fiber の連結成分への連結写像 |
| `componentConnecting_exact` / `.componentConnecting_kernel` | 参照基点を変えられる零次数の完全性 |
| `componentFiber_exact` | 全空間の連結成分の位置での完全性 |
| `FibrationSquare.componentConnecting_natural` | 固定 fiber の連結写像の自然性 |
| `FibrationSquare.fiberMap_piZero_bijective` | fiber の連結成分の全単射性 |
| `FibrationSquare.fiberMap_piIsomorphism` | fiber の全基点 π_* 同型 |
| `FibrationSquare.fiberMapOver_piIsomorphism` | 包含と可換な固定 fiber 射での比較 |

参照：Goerss–Jardine I §§7–8、Kerodon §3.2.6、BF 1978 §2。
保存単位の対象ビルド 1859 jobs 成功。
私有宣言を含む 86 モジュール 1494 宣言で標準三公理のみ。
L9c は未完了。次は loop と fiber の比較を用いて fiber 列の Ω 条件を証明する。
整数次数長完全列と反復比較の隣接構造射との添字正規化も残る。

## 38. L9c の fiber の Ω 条件と BF 対象

点つき fiber の既存の普遍性から kernel fork の極限性を証明した。
円からの点つき内部 Hom は右随伴なので、この kernel を保存する。
これにより fiber の loop と loop した射の fiber の点つき同型を構成した。
この同型は全空間への包含と可換である。
また、基点包含とホーンの pushout product の充填から、点つき Hom の後合成が
Kan fibration を保つことを証明した。
各段が Kan fibration である Ω 列の射について、fiber の随伴構造射を上の同型へ合成した。
全空間と底の随伴構造射の π_* 同型性を、fiber の全基点比較定理へ適用した。
その合成は π_* 同型であり、厳密同型を打ち消して fiber 自身の Ω 条件を得た。
fiber の Kan 列へ単射置換を施し、承認済みの BF 対象として fiber を定義した。
全空間への包含は厳密なスペクトルの射で、各段で元の射との合成が零である。
置換した fiber の各段から実際の fiber への比較射は全基点 π_* 同型である。
現時点の fiber 構成は各段が Kan fibration である射に対して与える。
任意のスペクトルの射をその形へ置換する工程と、整数次数長完全列は引き続き扱う。
Sp の ∞ 極限という主張は含めず、γ3 後に扱う。

| 主要宣言 | 内容 |
| --- | --- |
| `pointedFiberKernelIsLimit` | 点つき fiber の kernel としての普遍性 |
| `loopPointedFiberIso` / `.loopPointedFiberIso_hom_ι` | loop と fiber の厳密な同型と包含との可換性 |
| `PointedMapping.post_hasLiftingProperty` | 基点とパラメータの pushout product による後合成の充填 |
| `PointedMapping.post_fibration` | 後合成による Kan fibration の保存 |
| `KanSequence.Hom.fiber_omegaCondition` | fiber の全基点 Ω 条件 |
| `KanSequence.Hom.fiberOmegaSpectrum` | fiber の Kan 列から BF 対象への置換 |
| `OmegaSpectrum.fiber` | 段ごとの Kan fibration の fiber 対象 |
| `OmegaSpectrum.fiberLevelProjection_piIsomorphism` | 実際の段の fiber への全基点 π_* 同型 |
| `OmegaSpectrum.fiberInclusion` / `.fiberInclusion_comp_app` | 厳密な包含と各段の零合成 |

参照：Goerss–Jardine I §§7–8、Kerodon §3.1.3、BF 1978 §2、HTT A.3.3、HA §1.4.2。
保存単位の対象ビルド 1863 jobs 成功。
私有宣言を含む 89 モジュール 1523 宣言で標準三公理のみ。
L9c は未完了。整数次数長完全列、任意の射の段ごとの fibration への置換、
反復比較の隣接構造射との添字正規化が残る。

## 39. L9c の整数次数の連結準同型と長完全列

整数次数群の正次数の段による表示を整理した。
置換した fiber の段から実際の fiber の群への同型を、実際の fiberPoint を基点に構成した。
整数次数の包含と射影が、これらの表示で段の実際の fiber 列の射へ移ることを証明した。
連結射 δ_j : π_(j+1)(Y) → π_j(fiber) は、段 |j|+2 の正次数の連結準同型を移して定義した。
底と fiber の計算次数はそれぞれ boundaryIndex j + 2 と boundaryIndex j + 1 である。
全ての整数 j で群準同型が使える。
単なる定義に留めず、段の連結準同型で計算する式を証明した。
群同型によって核と像の完全性を移す一般補題を証明した。
これを段の完全列の fiber・全空間・底の三つの位置へ適用した。
整数次数の長完全列は全ての整数で完全であり、隣接射の合成も自明である。
対象の fiber は単射置換を挟んだ BF 対象で、射は元のホモトピー群の誘導準同型である。
現時点では各段が Kan fibration である射についての長完全列である。

| 主要宣言 | 内容 |
| --- | --- |
| `OmegaSpectrum.positiveStageEquiv` | 整数次数群の正次数の段表示 |
| `OmegaSpectrum.fiberPositiveStageEquiv` | 整数次数の fiber 群と実際の段の fiber 群の同型 |
| `OmegaSpectrum.fiberPositiveStageEquiv_inclusion` | 包含との可換性 |
| `OmegaSpectrum.positiveStageEquiv_projection` | 基点を像へ移した射影との可換性 |
| `OmegaSpectrum.boundaryStage` / `.boundaryIndex` | 連結準同型を計算する段と次数 |
| `OmegaSpectrum.stableConnectingHom` | 全整数次数の連結準同型 |
| `OmegaSpectrum.stableConnectingHom_compute` | 実際の段の連結準同型による計算式 |
| `group_exact_of_equivalences` | 群同型で可換に対応する完全性の移送 |
| `OmegaSpectrum.stableFiberLongExact` | 全整数次数の三つの位置での核と像の一致 |
| `OmegaSpectrum.stableConnectingHom_inclusion` / `.stableConnectingHom_projection` | 連結準同型との零合成 |
| `OmegaSpectrum.homotopyMap_fiberInclusion` | 包含と射影の零合成 |

参照：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 1867 jobs 成功。
私有宣言を含む 93 モジュール 1574 宣言で標準三公理のみ。
L9c は未完了。任意の射の段ごとの fibration への置換と、
反復比較の隣接構造射との添字正規化を引き続き進める。

## 40. L9c の隣接構造射と任意段表示の一致

段と次数の等式による移送の合成と、隣接比較との可換性を証明した。
k+r=l を使って前進比較を指定した反復回数で表示した。
減算を含む添字を等式の移送の内部で書き換える代わりに、この表示で正規化した。
前進比較を一段延ばす式を、構造射の比較とその後の次数の移送の合成として証明した。
最小段からの比較を打ち消し、隣接する二段の比較が構造射の隣接比較に一致すると示した。
終点の段に関する帰納により、任意の前進比較は既存の二段比較と一致する。
構造射の反復も、次数を整えると任意段の比較と一致する。
これで整数次数群の段の選択独立性は、合成整合性・自然性・実際の構造射との一致まで揃った。

| 主要宣言 | 内容 |
| --- | --- |
| `OmegaSpectrum.levelHomotopyCongr_trans_apply` | 二回の添字移送の合成 |
| `OmegaSpectrum.transition_congr_apply` | 添字移送と隣接比較の可換性 |
| `OmegaSpectrum.advanceTo_eq_iterate` | 指定反復回数による前進比較の表示 |
| `OmegaSpectrum.advanceTo_self` / `.advanceTo_succ` | 前進比較の開始点と後続式 |
| `OmegaSpectrum.compareLevels_succ` | 隣接二段の比較と構造射の一致 |
| `OmegaSpectrum.advanceTo_eq_compareLevels` | 前進比較と任意段比較の一致 |
| `OmegaSpectrum.iterateTransition_eq_compareLevels` | 反復構造射と任意段表示の一致 |

参照：BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 1868 jobs 成功。
私有宣言を含む 94 モジュール 1597 宣言で標準三公理のみ。
L9c の残りとして、任意の射を段ごとの Kan fibration へ置換する。
自由な区間の mapping path と、単射置換の比較射に対する cofibrant な源からの持ち上げを使う方針。


## 41. L9c の自由な path と cofibrant な源からの持ち上げ

自由な基点を加えた区間と二つの端点包含を構成した。
両端点の基礎射は anodyne であり、基点追加と余積の持ち上げで証明した。
単射と恒等射との余積の単射性も、境界生成の左クラスの押し出し閉性から証明した。
自由区間からの点つき内部 Hom を自由な path space とした。
端点評価は全ての単射に対する RLP を持ち、特に Kan fibration である。
定数 path の両端点の評価は厳密に恒等射である。
別に、構造射が単射な Kan 列から、各段で全単射への RLP を持つ射へ厳密に持ち上げる構成を証明した。
零段は基点包含、後続段は構造射を左辺として充填する。
これに Ω 条件は必要ない。
任意の射の mapping path を単射置換した後にも、元の射の厳密な因子分解を得るために使う。

| 主要宣言 | 内容 |
| --- | --- |
| `freeIntervalEndpoint_anodyne` | 自由な区間の両端点の anodyne 性 |
| `mono_coprod_map_id` | 基点追加による単射の保存 |
| `PointedMapping.anodyne_prePointed_rlp` | anodyne 制限の全単射への RLP |
| `freePathSpace` / `freePathEndpoint` | 自由な path と端点評価 |
| `freePathEndpoint_rlp` | 端点評価の全単射への RLP |
| `freeConstantPath_endpoint` | 定数 path の両端点の計算 |
| `pointedSquareLift` / `pointedMapLift` | 点つきの相対持ち上げ |
| `KanSequence.liftHom` / `.liftHom_fac` | 単射な構造射を持つ列からの厳密な持ち上げ |

参照：Goerss–Jardine I §7、BF 1978 §2、HTT A.3.3。
保存単位の対象ビルド 1873 jobs 成功。
私有宣言を含む 97 モジュール 1652 宣言で標準三公理のみ。
L9c は未完了。両端点同時評価の fibration 性と、path 列の構造射を続けて構成する。


## 42. L9c の自由な path 列と両端点の同時評価

閉 braided 圏で K ⊗ Hom(A,Y) → Hom(A,K ⊗ Y) を構成した。
内部 Hom の源の制限・標的の後合成に関する自然性を証明した。
単位からの内部 Hom の標準同型を評価射で表示し、交換射がこの同型と可換であることも示した。
これを使って、任意の点つき対象 A からの内部 Hom を Kan 列の各段に施した列を構成した。
源の制限と標的の後合成はいずれも厳密な列の射となる。
特に自由な path 列、二つの端点評価、定数 path が厳密な列の射として得られた。
自由区間の境界は点つき単位二つの余積で、その包含は単射である。
反変内部 Hom の極限保存により、境界からの写像空間を標的の二項積へ同定した。
境界への制限とこの同型の合成が、両端点の同時評価の Kan fibration を与える。
二つの射影が既存の始点・終点評価に一致することまで計算した。

| 主要宣言 | 内容 |
| --- | --- |
| `HomTensorStrength.map` | テンソルと内部 Hom の交換射 |
| `HomTensorStrength.natural_pre` / `.natural_post` | 両変数についての自然性 |
| `HomTensorStrength.map_unit` | 単位の内部 Hom の標準同型との整合性 |
| `KanSequence.mapping` / `.mappingPre` / `.mappingPost` | 内部 Hom の列と厳密な射 |
| `KanSequence.freePathEvaluation` / `.freePathConstant` | path 列の端点と定数 path |
| `KanSequence.freePathConstant_evaluation` | 定数 path の厳密な端点計算 |
| `freeBoundaryIsColimit` | 自由な境界の点つき余積の普遍性 |
| `freeBoundaryEvaluationIso` | 境界からの Hom と標的の二項積の同型 |
| `freePathEndpoints_fibration` | 両端点同時評価の Kan fibration 性 |
| `freePathEndpoints_fst` / `.freePathEndpoints_snd` | 二つの射影の計算 |

参照：Goerss–Jardine I §7、BF 1978 §2、HTT A.3.3。
保存単位の対象ビルド 1876 jobs 成功。
私有宣言を含む 100 モジュール 1728 宣言で標準三公理のみ。
L9c は未完了。段ごとの引き戻しを用いて任意の射の mapping path 列を構成する。


## 43. L9c 完了：任意の射の fibration 置換と homotopy fiber の長完全列

段ごとの Kan fibration に沿う引き戻しを点つき圏で取り、Kan 列として束ねた。
構造射は二つの射影から普遍性で作り、射影と持ち上げは厳密な列の射である。
自由な path の始点評価を任意の射に沿って引き戻して mapping path を構成した。
源への射影は全単射への RLP を持つ。
終点射のホーン充填は、まず元の源の成分を充填し、次に両端点を同時に充填して証明した。
定数 path による比較射と終点射の合成は厳密に元の射である。
源が Ω 条件を持つと、中間列も源への射影の RLP を通して Ω 条件を持つ。
この列を境界 cell 分解で単射置換し、元の cofibrant な源から厳密に持ち上げた。
従って元の任意の射は、段ごとの全基点 π_* 同型と段ごとの Kan fibration の厳密な合成となる。
中間対象は本レーンで固定した BF cofibrant–fibrant 対象である。
元の源への厳密な射影も構成し、整数次数群では比較射の逆写像になることを証明した。

置換した右因子の fiber を単射置換し、任意の射の homotopy fiber を BF 対象として定義した。
包含は置換後の fiber 包含と元の源への射影の合成であり、実際の厳密なスペクトルの射である。
連結射は置換後の段の連結準同型から来る。
比較群同型を通して、fiber・全空間・底の三つの位置の完全性を元の射の誘導準同型へ移した。
全ての整数次数で核と像が一致し、隣接射の合成が自明である。
Sp の ∞ 極限としての普遍性、正しい導来写像空間との比較はこの主張に含めていない。
これらは承認済みの仕様どおり γ3 後の別工程である。
L9c の本工程は完了とし、L9d の telescope 有理化へ進む。

| 主要宣言 | 内容 |
| --- | --- |
| `pointedPullback_isPullback` / `.pointedPullback_snd_rlp` | 基礎引き戻しと全単射 RLP の保存 |
| `KanSequence.pullbackSequence` / `.pullbackLift` | Kan 列の引き戻しと厳密な普遍射 |
| `mappingPathProjection_fibration` | 任意の点つき Kan 射の終点射の相対ホーン充填 |
| `KanSequence.mappingPathSequence_omegaCondition` | mapping path 列の Ω 条件 |
| `OmegaSpectrum.fibrationReplacement` | BF 対象としての中間対象 |
| `OmegaSpectrum.fibrationReplacement_fac` | 元の射の厳密な因子分解 |
| `OmegaSpectrum.fibrationReplacementProjection_fibration` | 右因子の各段の Kan fibration 性 |
| `OmegaSpectrum.fibrationReplacementUnit_piIsomorphism` | 左因子の全整数次数 π_* 同型 |
| `OmegaSpectrum.fibrationReplacementRetraction` | 元の源への厳密な射影 |
| `OmegaSpectrum.homotopyFiber` / `.homotopyFiberInclusion` | 任意の射の homotopy fiber と包含 |
| `OmegaSpectrum.homotopyFiberBoundary` | 全整数次数の連結準同型 |
| `OmegaSpectrum.homotopyFiberLongExact` | 任意の射の三つの位置での長完全性 |
| `OmegaSpectrum.homotopyFiberBoundary_inclusion` / `.homotopyFiberInclusion_projection` / `.homotopyFiberBoundary_projection` | 隣接射の零合成 |

参照：Goerss–Jardine I §§7–8、BF 1978 §2、HTT A.3.3、HA §1.4.2。
保存単位の対象ビルド 1881 jobs 成功。
私有宣言を含む 105 モジュール 1819 宣言で標準三公理のみ。
工程区切りの全体ビルド 9543 jobs 成功。
L9d・L9e は未完了であり、全体目標の完了は主張しない。


## 44. L9d の filtered colimit と Kan 性・ホモトピー群

有限な相対写像データを一つの後続段へ移す補題を証明した。
有限個の制限の等式は、定義域の有限余積を使って同時に移せる。
有限ホーンからの射を段へ下ろして充填することで、Kan 複体の filtered colimit の Kan 性を示した。
遷移射の単射性は仮定していない。
境界定数単体は基点を含む相対因子分解で後続段に実現できる。
RelStruct は隣接二面と残りの定数面を同時に指定して後続段へ移せる。
従って零次数を含む全自然数次数で、全ての類が段から来て、類の等式が後続段で成立する。

点つき diagram の π_n の図式と cocone を実際に構成した。
基点忘却が filtered colimit を保存することから、点つき余極限の Kan 性を証明した。
代表と関係の有限性から、ホモトピー類の cocone が型の圏の余極限であることを証明した。
正次数については群準同型の図式を作り、群の filtered colimit の普遍性と比較群同型を構成した。
比較同型を各段に制限した準同型は、元の cocone 射の誘導準同型に一致する。
π_1 の非可換性を許す群の圏で主張しており、零次数は集合として扱う。
`Rationalization.lean` を L9d の集約入口とした。
有理化対象、telescope との比較、ℚ テンソルの計算は引き続き未完了。

| 主要宣言 | 内容 |
| --- | --- |
| `finite_relative_factorization` / `.finite_equations_factorization` | 有限な境界条件・面条件を保つ後続段への因子分解 |
| `kanComplex_of_filtered_isColimit` | Kan 複体の filtered colimit の Kan 性 |
| `ptSimplex_filtered_factorization` | 基点を保つ代表単体の有限段での実現 |
| `relStruct_filtered_factorization` | ホモトピー関係の有限段での実現 |
| `homotopy_filtered_surjective` / `.homotopy_filtered_eq_eventually` | 全自然数次数の代表と等式の後続段での実現 |
| `pointedFilteredColimit_kanComplex` | 点つき filtered colimit の Kan 性 |
| `pointedHomotopyIsColimit` | 全自然数次数のホモトピー類と filtered colimit の可換性 |
| `pointedHomotopyGroupIsColimit` | 正次数群の余極限の普遍性 |
| `pointedHomotopyGroupColimitIso` / `.pointedHomotopyGroupColimitIso_ι` | 比較群同型と各段での計算 |
| `filteredPointedHomotopyGroupIso` | 選ばれた点つき余極限の正次数群の比較同型 |

参照：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 1888 jobs 成功。
私有宣言を含む 109 モジュール 1864 宣言で標準三公理のみ。
次は有限な源からの点つき内部 Hom と filtered colimit の比較を進め、loop と colimit を整合させる。


## 45. L9d の有限な内部 Hom と loop の filtered colimit 保存

有限な点つき源と有限パラメータの写像族を uncurry した。
基点包含に対する相対因子分解により、基点条件を保つ写像族を一つの段に実現できる。
二つの族が余極限で一致すれば、有限なテンソル積からの射の等式を後続段へ移せる。
ここには Kan 性も遷移射の単射性も不要である。

各単体次数で Yoneda の同値を使い、これらの二つの事実から写像空間の余極限性を証明した。
基点忘却の同型反映で点つき圏へ戻し、有限な源からの内部 Hom が filtered colimit を保存すると示した。
標準単体の境界を潰した球面は、有限な対象の押し出しとして有限である。
特に単体的円が有限なので、点つき loop 関手は filtered colimit を保存する。
loop 対象の余極限と余極限の loop 対象との標準同型、および各段での計算式を構成した。
この同型は通常の点つき単体集合の同型であり、Sp の ∞ 余極限の普遍性を先取りしない。

| 主要宣言 | 内容 |
| --- | --- |
| `PointedMapping.finite_basedHom_factorization` | 基点条件を保つ有限な写像族の後続段での実現 |
| `PointedMapping.finite_basedHom_eq_eventually` | 写像族の等式の後続段での実現 |
| `PointedMapping.finite_basedHom_isColimit` | 各次数の写像空間の余極限性 |
| `PointedMapping.finite_basedHom_preservesColimit` | 有限な点つき源からの内部 Hom の filtered colimit 保存 |
| `pointedSphere_finite` | 境界を潰した単体的球面の有限性 |
| `loop_preservesFilteredDiagram` | loop 関手の filtered colimit 保存 |
| `loopFilteredColimitIso` / `.loopFilteredColimitIso_ι` | loop と余極限の比較同型と各段の計算 |

参照：Goerss–Jardine I §7、BF 1978 §2、HTT A.3.3、HA §1.4.2。
保存単位の対象ビルド 1891 jobs 成功。
私有宣言を含む 112 モジュール 1880 宣言で標準三公理のみ。
次は段ごとの全基点 π_* 同型の filtered colimit 保存を示し、Ω 条件を移す。
有理化の対象、telescope の比較、ℚ テンソルの計算は引き続き未完了。


## 46. L9d の全基点 π_* 同型と filtered Ω 列の整数次数群

まず点つき Kan 図式の指定基点のホモトピー類の自然変換を構成した。
段ごとの全単射は自然同型となり、余極限の射も全単射になることを実証した。
任意の余極限の頂点を一段から取った後、その段の under 圏で後続段に基点を付けた。
under 圏からの forget の final 性により元の余極限を保つ。
これにより、段ごとの全基点 π_* 同型が filtered colimit で保存されることを証明した。
零次数を含む。空な段があっても追加の非空仮定を置かない。

Ω スペクトルの図式を各段の点つき Kan 図式へ評価した。
suspension が余極限を保存することから、段ごとの Kan 余極限に構造射を入れた。
各元のスペクトルからこの Kan 列への射は厳密である。
随伴構造射は、元の随伴構造射の余極限と loop の比較同型の合成に厳密に一致する。
全基点 π_* 同型の保存をこの式へ適用し、余極限列の Ω 条件を証明した。
構造射には境界 cell 分解の単射置換を施し、BF 対象を得た。

各整数次数の群の図式と、任意の許容正次数の段の群の図式との自然同型を構成した。
段の群と filtered colimit の可換性、単射置換の各段の比較同型を合成した。
結果として、構成した BF 対象の全整数次数の群は、元の整数次数群の図式の余極限と同型である。
この比較を各段から計算する式も証明した。
これらは通常の段ごとの構成と π_* の計算であり、Sp の ∞ 余極限としての普遍性は含まない。
有理化用の乗法射の列、homotopy telescope と通常の余極限の比較、ℚ テンソルの計算はまだ未完了。

| 主要宣言 | 内容 |
| --- | --- |
| `pointedHomotopyMap_bijective_of_filtered` | 指定基点の段ごとの π_n 同型の保存 |
| `pointFromStage` / `.pointFromStageCocone` / `.pointFromStageIsColimit` | under 圏での任意基点の後続段への移送 |
| `kanPiIsomorphism_of_filtered` | 全基点・全次数の π_* 同型の filtered colimit 保存 |
| `pointedColimMap_kanPiIsomorphism` | 点つき余極限射への適用 |
| `OmegaSpectrum.filteredKanSequence` / `.filteredKanInjection` | 段ごとの Kan 余極限列と厳密な射 |
| `OmegaSpectrum.filteredAdjoint_formula` | 余極限の随伴構造射の計算 |
| `OmegaSpectrum.filteredKanSequence_omegaCondition` | 全基点での Ω 条件 |
| `OmegaSpectrum.filteredOmegaSpectrum` | 単射置換した BF 対象 |
| `OmegaSpectrum.spectrumHomotopyDiagramStageIso` | 整数次数群の図式と段表示の自然同型 |
| `OmegaSpectrum.filteredLevelComparison_piIsomorphism` | 単射置換の各段の π_* 比較 |
| `OmegaSpectrum.filteredSpectrumHomotopyIso` | 全整数次数の群と群の filtered colimit の比較同型 |
| `OmegaSpectrum.filteredSpectrumHomotopyIso_ι_stage` | 比較同型の各段での計算 |

参照：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 1896 jobs 成功。
私有宣言を含む 117 モジュール 1955 宣言で標準三公理のみ。
L9d は進行中。次は有理化の telescope に対応する群の局所化の計算を進める。


## 47. L9d の乗法列の群の局所化と ℚ テンソル

2,3,4,… の整数乗法を遷移とするアーベル群の列を構成した。
二段間の係数は整数区間の積であり、零段からの係数は (i+1)! に一致する。
任意の非零整数は十分先の遷移係数を割ることを証明した。
直極限の代表と等式の検出から、非零整数倍が直極限で全単射になることを示した。
元の群のねじれを仮定しない。

零段からの標準射について、整数の非零元による加群の局所化の三条件を証明した。
有理テンソル積の標準射も同じ局所化なので、普遍性から線形同型を得た。
この同型は零段の a を a⊗1 に送り、加法準同型に関して自然である。
直極限の cocone がアーベル群の圏の余極限を与えることも証明した。
これにより圏論的な乗法列の余極限も A⊗ℚ と同定できる。

| 主要宣言 | 内容 |
| --- | --- |
| `RationalTelescope.coefficient_comp` / `.coefficient_zero` | 遷移係数の合成則と階乗表示 |
| `RationalTelescope.exists_dvd_integerCoefficient` | 任意の非零整数の後続段での可除性 |
| `RationalTelescope.additiveLimit_smul_bijective` | 直極限での非零整数倍の全単射性 |
| `RationalTelescope.additiveLimit_isLocalizedModule` | 零段の標準射の局所化条件 |
| `RationalTelescope.additiveLimitTensorEquiv` | 直極限と A⊗ℚ の線形同型 |
| `RationalTelescope.additiveDiagramTensorIso` / `.additiveDiagramTensorIso_zero` | 群の圏の余極限の比較と零段の計算 |
| `RationalTelescope.limitMap` | 加法準同型の直極限への誘導と関手法則 |
| `RationalTelescope.additiveLimitTensorEquiv_natural` | テンソル比較の自然性 |

参照：BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 2319 jobs 成功。
私有宣言を含む 122 モジュール 2019 宣言で標準三公理のみ。
L9d は進行中。スペクトルの実際の乗法射と telescope の構成および比較は未完了。
群の計算だけでスペクトルの有理化の完成を主張しない。


## 48. L9d の filtered BF 対象への射と置換比較

元の各対象の cofibrant 性を使い、各段の余極限への射を BF 置換へ厳密に持ち上げた。
段ごとの比較射へ戻すと元の余極限の標準射に一致する。
この式と正次数の段表示の自然性により、整数次数の余極限同型が選んだ射を誘導すると証明した。
持ち上げの選択の厳密な自然性は要求しないが、π_* 上では cocone の自然性が成立する。

図式の自然変換から、段ごとの Kan 余極限列の厳密な射も構成した。
その射を標的の BF 置換へ持ち上げ、実際の Ω スペクトル間の比較射を得た。
元の自然変換が各段で全基点 π_* 同型なら、この比較射も各段および全整数次数で π_* 同型である。
通常の余極限模型を置換して比較するための結果であり、∞ 余極限の普遍性は含まない。

乗法射の実現のため、π_* 同型である Kan fibration の fiber の消滅も長完全列から証明した。
零次数を含む任意の fiber 基点で全ホモトピー類は一元である。
対応する境界定数単体の RelStruct も存在する。
この消滅から実際の境界充填を導く逆向きの Whitehead 補題は後続部分で実証する。

| 主要宣言 | 内容 |
| --- | --- |
| `OmegaSpectrum.filteredSpectrumInjection` | 元の各対象から BF 余極限対象への厳密な射 |
| `OmegaSpectrum.filteredSpectrumInjection_comparison` | 各段の余極限射との整合性 |
| `OmegaSpectrum.filteredSpectrumHomotopyIso_ι` | 群の余極限同型の各段での計算 |
| `OmegaSpectrum.filteredSpectrumInjection_natural` | 誘導する整数次数群の写像の自然性 |
| `OmegaSpectrum.filteredKanMap` / `.filteredSpectrumMap` | 自然変換からの Kan 列と BF 対象の比較射 |
| `OmegaSpectrum.filteredSpectrumMap_levelwise` / `.filteredSpectrumMap_piIsomorphism` | 段ごとおよび整数次数の π_* 同型の保存 |
| `fiberHomotopy_eq_point` / `.fiberHomotopySubsingleton_at` | acyclic fiber の零次数を含む全類の一意性 |
| `fiberRelStruct_nonempty` | acyclic fiber の境界定数単体間の関係の存在 |

参照：Goerss–Jardine I §§7–8、Kerodon §3.2.6、BF 1978 §2、HTT A.3.3、HA §1.4.2。
保存単位の対象ビルド 2322 jobs 成功。
私有宣言を含む 125 モジュール 2046 宣言で標準三公理のみ。
L9d は進行中。次はホモトピー類の消滅を境界の充填へ戻す幾何的補題を進める。


## 49. L9d の消滅からの実際の境界充填と相対 Whitehead

標準単体の単体を、区間の値が零の間は元の値、その後は最後の頂点とする収縮を構成した。
この収縮は最後のホーンを保つ。ホーンの収縮を相対区間充填で境界全体へ延長する。
その結果、任意の Kan 値の境界射を最後のホーン上で定数となる射へホモトピーで移せる。
最後の面は PtSimplex となり、その類が零なら定数単体との RelStruct が全境界の充填を与える。
さらに、境界のホモトピーを標準単体へ延長し、元の境界の充填へ戻せる。

従って、非空な Kan 複体で全基点・全自然数次数の類が一元なら、終対象射は全単射 RLP を持つ。
単射への拡張には境界 cell 分解に対する RLP の閉性だけを使った。
Kan fibration の π₀ 全射性から頂点そのものの全射性を、RelStruct の辺の持ち上げで証明した。

相対版では、底の標準単体の収縮を境界で持ち上げた。
終点での境界は一つの fiber 内に入り、その fiber の充填後、区間の相対延長で元の底へ戻す。
これにより、全ての fiber の終対象射が全単射 RLP を持てば、元の fibration 自身も全単射 RLP を持つ。
長完全列からの fiber の消滅と合わせ、非空な Kan 複体間の Kan fibration の π_* 同型性と全単射 RLP の同値を実証した。
HT-KQ の引用も新しい弱同値公理も用いない。

| 主要宣言 | 内容 |
| --- | --- |
| `SimplexLastContraction.map` / `.homotopy` | 標準単体の明示的な区間収縮 |
| `LastHornContraction.map` / `.homotopy` | 最後のホーンへの制限と端点の式 |
| `BoundaryNormalization.exists_normalization` | 境界のホーン上での定数化と実ホモトピー |
| `BoundaryNormalization.lastSimplex` | 正規化した境界の最後の面の PtSimplex 表示 |
| `BoundaryNormalization.exists_filler_of_lastSimplex` | 最後の面の類の消滅からの充填 |
| `terminal_rlp_of_homotopySubsingleton` | 全ホモトピー類の消滅から全単射 RLP |
| `fiber_terminal_rlp_of_piIsomorphism` | acyclic fiber の実際の充填性 |
| `exists_fibration_interval_lift` | 指定始点からの区間の持ち上げ |
| `fibration_surjective_vertices_of_zero` | π₀ 全射性からの頂点の全射性 |
| `exists_boundary_lift_of_fiber_lifting` | fiber の充填から相対境界充填 |
| `fibration_rlp_of_piIsomorphism` / `.fibration_piIsomorphism_iff_rlp` | Kan fibration の相対 Whitehead |

参照：Goerss–Jardine I §§7–8、Kerodon §§3.2.2・3.2.6、BF 1978 §2。
保存単位の対象ビルド 2331 jobs 成功。
私有宣言を含む 132 モジュール 2102 宣言で標準三公理のみ。
L9d は進行中。任意の Kan 射の π_* 同型からの逆射の実現と乗法 telescope は引き続き未完了。


## 50. L9d の一般の Kan Whitehead と内部 Hom の π_* 保存

基点を固定しない指数 path 対象を構成し、端点評価が全単射 RLP を持つことを証明した。
ホモトピーをこの対象へ転置すると、両端点で元の二つの射を得る。
端点の全基点 π_* 同型を打ち消すことで、一般の区間ホモトピーによる同型性の不変性を得た。
ここでは異なる終点基点の類の写像が同じだとは主張しない。

点つき Kan 射の mapping path は、源への射影と二つの端点評価で比較できる。
元の射が全基点 π_* 同型なら、mapping path の終点射もそうである。
相対 Whitehead により終点射が全単射 RLP を持ち、点つき切断を選べる。
二つの RLP 射の下で等しい射の間の相対ホモトピーを構成した。
これらから元の射の点つき逆射と、両方向で基点を固定する実際の区間ホモトピーを得た。

点つき内部 Hom の標的変数についても全基点 π_* 同型の保存を証明した。
mapping path の源射影と終点射の RLP を内部 Hom へ移し、切断と源射影の厳密な合成を打ち消す。
源となる点つき対象に有限性や Kan 性は不要である。

| 主要宣言 | 内容 |
| --- | --- |
| `KanPath.evaluation_rlp` / `.evaluation_piIsomorphism` | 基点を固定しない path の端点の比較 |
| `KanPath.transpose` / `.transpose_zero` / `.transpose_one` | 一般のホモトピーの転置と端点の計算 |
| `kanPiIsomorphism_iff_of_homotopy` | 基点を固定しないホモトピーによる π_* 同型性の保存 |
| `mappingPathProjection_piIsomorphism` / `.mappingPathProjection_rlp_of_piIsomorphism` | Kan 射の fibration 置換の全単射 RLP |
| `exists_pointedHomotopy_of_comp_eq` | RLP 射の下で等しい点つき射間の相対ホモトピー |
| `exists_pointedHomotopyInverse` | 点つき Kan Whitehead の実際の逆射と両方向の基点固定ホモトピー |
| `PointedMapping.post_piIsomorphism` | 点つき内部 Hom の標的変数の π_* 同型の保存 |

参照：Goerss–Jardine I §§7–8、Kerodon §§3.2.1・3.2.6、BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 2335 jobs 成功。
私有宣言を含む 136 モジュール 2125 宣言で標準三公理のみ。
L9d は進行中。次は二つの内部 Hom の交換と Kan 列の Ω 条件を整合させる。


## 51. L9d の cotensor の BF 対象と loop の整数次数群

閉 braided 圏の二つの内部 Hom を、二重 curry と源の braiding により同型で交換した。
二重評価での計算式を証明し、テンソル交換による列の構造射の随伴が、元の随伴構造射の Hom と交換同型の合成に一致すると示した。
標的変数の π_* 同型保存をこの式へ適用し、任意の点つき源 A からの内部 Hom の Kan 列の Ω 条件を得た。
構造射は境界 cell 分解で単射に置換し、本レーンの BF 対象を実際に構成した。

源の射による制限を、cofibrant な BF 対象から比較射へ持ち上げた。
各段で実際の内部 Hom の制限と可換する。
源の射が anodyne なら、この射は各段および全整数次数で π_* 同型である。
この結果には源の Kan 性や有限性を要求しない。

任意の許容正次数の段で cotensor の整数次数群を実際の内部 Hom の群へ表示した。
円を源とする場合、loop の群の同型を用いて π_j(cotensor(S¹,X))≃π_{j+1}(X) と計算した。
零段を落とす通常の厳密な関手 tail も構成し、π_j(tail X)≃π_{j-1}(X) と示した。
この二つの操作を合成した対象は元と同じ整数次数群を持つ。
群の同型から対象間の厳密な同型や射を推論しない。
∞ 圏での cotensor や suspension の普遍性は γ3 後の比較へ留保する。

| 主要宣言 | 内容 |
| --- | --- |
| `InternalHomExchange.iso` / `.uncurry_uncurry_hom` | 二つの内部 Hom の交換同型と二重評価式 |
| `InternalHomExchange.curry_strength` | 構造射の随伴と交換同型の整合性 |
| `KanSequence.mapping_adjoint` / `.mapping_omegaCondition` | 内部 Hom の Kan 列の随伴構造射と Ω 条件 |
| `OmegaSpectrum.cotensor` / `.cotensorProjection` | cotensor の BF 対象と元の Kan 列への比較 |
| `OmegaSpectrum.cotensorPre` / `.cotensorPre_comparison` | 源の射による厳密な比較射と段の計算 |
| `OmegaSpectrum.cotensorPre_piIsomorphism_of_anodyne` | 源の anodyne 置換の全整数次数での保存 |
| `OmegaSpectrum.cotensorStageEquiv` / `.cotensorLoopHomotopyEquiv` | 段表示と円による一次数移動 |
| `OmegaSpectrum.tailFunctor` / `.tailHomotopyEquiv` | 零段を落とす関手と整数次数の計算 |
| `OmegaSpectrum.tailCotensorLoopHomotopyEquiv` | 二つの操作の整数次数群の相殺 |

参照：BF 1978 §2、HTT A.3.3、HA §1.4.2。
保存単位の対象ビルド 2341 jobs 成功。
私有宣言を含む 141 モジュール 2183 宣言で標準三公理のみ。
L9d は進行中。次は円の Kan 置換上の実際の自己射と、その写像空間の群への作用を進める。


## 52. L9d の球面の単体表示と円の Kan 置換上の実際の自己射

境界を潰す実際の cofiber の普遍性により、点つき球面からの射と PtSimplex の同値を構成した。
基点の表示を頂点の定数射へ直し、後合成についての自然性も証明した。
この同値には標的の Kan 性を仮定しない。

円の Kan 置換の単位が定める基本群の指定類を取った。
その自然数 m 乗の代表を選び、球面の射へ戻した。
Kan 置換単位の anodyne 性に沿って延長し、円の Kan 置換上の点つき自己射を実際に構成した。
単位へ前合成すると選んだ代表に厳密に一致する。
誘導準同型が指定類を m 乗へ送り、任意の Kan 値の点つき射の後でも同じ計算となることを証明した。

ここでは指定類の計算だけを実証している。
基本群全体の巡回性、高次写像空間の群への m 倍作用、スペクトルの有理化の完成は主張しない。
後続部分で写像空間の類との比較を進める。

| 主要宣言 | 内容 |
| --- | --- |
| `SphereSimplex.equiv` / `.equiv_comp` | 球面からの点つき射と境界定数単体の同値と自然性 |
| `CirclePower.space` / `.unit` / `.generator` | 円の Kan 置換と指定した基本類 |
| `CirclePower.representative_class` | 指定基本類の冪の実際の単体の代表 |
| `CirclePower.powerMap` / `.unit_powerMap` | 円の Kan 置換上の自己射と単位上の厳密な計算 |
| `CirclePower.powerMap_generator` | 指定基本類の冪への作用 |
| `CirclePower.evaluateGenerator_power` | 任意の Kan 値の後合成後での指定基本類の計算 |

参照：Goerss–Jardine I §7、Kerodon §§3.2.2–3.2.3、BF 1978 §2。
保存単位の対象ビルド 2343 jobs 成功。
私有宣言を含む 143 モジュール 2208 宣言で標準三公理のみ。
L9d は進行中。次は RelStruct を実際の球面のホモトピーへ移す幾何的補題を進める。


## 53. L9d の RelStruct の実際の相対ホモトピーによる表示

隣接する穴の位置の二つの単調埋め込みを、区間の値に応じて切り替える prism を構成した。
端点は i.succ の面と i.castSucc の面である。
各境界面の制限を、切り替え位置の前・後・一致に分けて計算した。
前後の面は低次元の prism を経由し、一致する面では区間変数が消える。

RelStruct の充填単体へこの prism を後合成した。
各境界面は RelStruct の定数面、または二つの指定単体の共通境界へ入り、基点に固定される。
任意の境界単体を一つの面から因子分解して、全区間の相対条件を実証した。
零次元では境界が空なので同じ構成が成立する。
この構成自体には標的の Kan 性は不要である。
Kan 複体の正次数では、ホモトピー類の等式と境界固定ホモトピーの存在が同値になることを証明した。

| 主要宣言 | 内容 |
| --- | --- |
| `AdjacentFacePrism.map` / `.zero` / `.one` | 隣接二面の明示的な prism と端点の式 |
| `AdjacentFacePrism.face_of_lt` / `.face_of_gt` / `.face_self` | 各境界面への制限の三場合 |
| `relStruct_prism_face` | RelStruct の prism の各面の定数性 |
| `relStructHomotopy` | RelStruct から境界固定の実区間ホモトピーへの変換 |
| `KanHomotopyGroup.mk_eq_iff_relativeHomotopy` | 正次数の類の等式と相対ホモトピーの同値 |

参照：Goerss–Jardine I §7、Kerodon §3.2.2。
保存単位の対象ビルド 2346 jobs 成功。
私有宣言を含む 146 モジュール 2275 宣言で標準三公理のみ。
L9d は進行中。次はこれらの相対ホモトピーを球面の商へ降ろし、写像空間の連結成分と比較する。


## 54. L9d の球面と円からの写像空間の成分の計算

境界固定の単体ホモトピーを、球面の cofiber の積の pushout に沿って降ろした。
写像空間の頂点と点つき射の同値、辺と基点固定ホモトピーの相互変換を構成した。
Kan 複体の同じ成分の二頂点を一つの辺で結び、成分の等式と点つきホモトピーの存在を比較した。
これにより球面からの写像空間の π₀ と通常の正次数のホモトピー群の集合の同値を証明した。

円の Kan 置換の単位への制限は anodyne な源の置換なので、同じ比較を Kan 置換した円へ移した。
指定基本類の像による表示と一致し、powerMap m の前合成がすべての成分で m 乗になる。
球面と円の成分比較は標的の点つき射について自然である。
内部 Hom の交換についても最初の源の制限自然性を二重評価により証明した。
高次群での powerMap の作用と有理化の対象の完成はまだ主張しない。

| 主要宣言 | 内容 |
| --- | --- |
| `SphereSimplex.homotopy` / `.pullHomotopy` | 球面の商と境界固定ホモトピーの往復 |
| `PointedMapping.familyVertexEquiv` | 実際の点つき射と写像空間の頂点の同値 |
| `PointedMapping.edgeOfHomotopy` / `.homotopyOfEdge` | 基点固定ホモトピーと写像空間の辺の比較 |
| `PointedMapping.piZero_eq_iff_pointedHomotopy` | 成分の等式と基点固定ホモトピーの存在の同値 |
| `SphereSimplex.componentEquiv` / `.componentClass_natural` | 球面からの写像空間の成分と通常のホモトピー群 |
| `CirclePower.componentEquiv` / `.componentEquiv_pre_power` | 円の Kan 置換の写像空間の成分と冪の作用 |
| `CirclePower.componentEquiv_natural` | 円の成分比較の標的に関する自然性 |
| `InternalHomExchange.natural_pre_left` | 交換同型と最初の源の制限の可換性 |

参照：Goerss–Jardine I §7、Kerodon §§3.2.2–3.2.3、BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 2353 jobs 成功。
私有宣言を含む 153 モジュール 2346 宣言で標準三公理のみ。
L9d は進行中。次は loop を値とする写像の群演算と高次ホモトピー群の演算を比較する。


## 55. L9d の実際の loop の積と次数射の全正次数での計算

円の Kan 置換を値とする内部 Hom への点つき射のホモトピー類に群構造を与えた。
パラメータ源の制限は群準同型となり、零射の類は単位元となる。
第二の源の制限と内部 Hom の交換の自然性も証明し、円の次数 m の自己射が
任意のパラメータを持つ loop の類に m 乗で作用することを実証した。

二つの射影の類の積の代表を選び、loop の積を表す実際の単体的な射を構成した。
その左右の軸への制限は恒等射と点つきホモトピックである。
直積の RelStruct を成分ごとに組み合わせ、直積のホモトピー類を二つの射影で識別した。
これにより直積への誘導像を二つの軸の積に分解した。
積の射の誘導作用は、RelStruct・MulStruct から構成した通常の群の積に一致する。
反復積の実際の自己射と円の次数射を点つきホモトピー類で比較し、
円の Kan 置換の次数 m の自己射の前合成がすべての正次数の群に m 乗で作用すると証明した。
これは特定の基本類だけの計算ではなく、通常の群のすべての元に対する計算である。

| 主要宣言 | 内容 |
| --- | --- |
| `LoopMappingClasses.classEquiv` / `.groupEquiv` | loop 値の写像の類と基本群の同値と群構造 |
| `LoopMappingClasses.preHom` / `.preHom_classOf` | パラメータ源の制限準同型と実際の射の前合成 |
| `InternalHomExchange.natural_pre_right` | 第二の源の制限についての交換同型の自然性 |
| `LoopMappingClasses.classOf_zero` / `.post_power` | 零射の類と任意のパラメータでの円の冪作用 |
| `KanHomotopyGroup.prod_kanComplex` / `.prod_map_injective` | 直積の Kan 性と射影による類の識別 |
| `pointedGroupMap_prodLift` | 直積への誘導像の二つの軸による分解 |
| `LoopMappingClasses.multiplication` / `.classOf_pair_multiplication` | 類の積を表す実際の射 |
| `LoopMappingClasses.groupMap_pair_multiplication` | 通常の正次数群での積の作用 |
| `LoopMappingClasses.groupMap_pre_power` | 円の次数射の全正次数の群での冪作用 |

参照：Goerss–Jardine I §7、Kerodon §§3.1・3.2.2、BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 2360 jobs 成功。
私有宣言を含む 160 モジュール 2406 宣言で標準三公理のみ。
L9d は進行中。次は BF cotensor へこの作用を移して整数次数の telescope を構成する。


## 56. L9d の実際の BF telescope の対象と全整数次数のテンソル比較

円の Kan 置換の次数射の前合成を BF cotensor へ持ち上げた。
比較射との厳密な可換式を任意段表示へ送り、全整数次数の群で m 乗になることを証明した。
この実際の厳密な自己射を次数 2,3,4,… の順に並べ、自然数の圏の関手を構成した。
長い遷移射は厳密な合成であり、群では区間係数の冪となる。
AsSmall ℕ に添字を拡大して universe を合わせ、filtered Kan 余極限と cofibrant 置換を適用した。

群の図式の cocone を整数乗法の加法直極限へ構成した。
代表の存在と等式の後続段での検出から、集合および群の圏で余極限であることを実証した。
filtered スペクトルの群の比較と整数乗法直極限の局所化を合成し、loop telescope の群を計算した。
円の anodyne な置換単位、loop の次数移動、tail の次数補正により、
実際に構成した対象の全整数次数群と元の群の ℚ テンソルとの群同型・ℤ 線形同型を得た。
loop telescope の零段の実際の注入射が a↦a⊗1 を誘導することも証明した。

現時点で `rationalization` はこの実際の BF 対象の名称である。
この名称から ∞ 圏の局所化の普遍性を主張しない。
元の X からの標準射は、元と同じ群を持つ loop 模型の群同型からは得られない。
L9d の完了条件である元の X からの有理化写像と自然性は、引き続き実構成が必要である。
工程は未完了のままとし、L9e にはまだ進まない。

| 主要宣言 | 内容 |
| --- | --- |
| `OmegaSpectrum.cotensorStageEquiv_pre` | BF cotensor の任意段表示と源の制限の整合 |
| `OmegaSpectrum.cotensorPre_power_homotopyMap` | 円の次数射の全整数次数の冪作用 |
| `OmegaSpectrum.rationalSequence` / `.rationalDiagram` | 実際の厳密な自己射の有理化図式 |
| `OmegaSpectrum.rationalDiagram_homotopyMap` | 長い遷移射の区間係数の冪の式 |
| `OmegaSpectrum.rationalLoopTelescope` | 段ごとの Kan 余極限の BF 置換 |
| `OmegaSpectrum.rationalGroupCoconeUnderlyingIsColimit` | 群の図式の underlying での余極限性 |
| `OmegaSpectrum.rationalGroupCoconeIsColimit` | 群の圏の余極限性 |
| `OmegaSpectrum.rationalLoopTensorEquiv` | loop telescope の整数次数群の有理テンソル比較 |
| `OmegaSpectrum.rationalLoopTensorEquiv_injection_zero` | 零段の実際の射の a⊗1 の式 |
| `OmegaSpectrum.rationalization` | 次数を補正した実際の BF telescope 対象 |
| `OmegaSpectrum.rationalizationHomotopyEquiv` / `.rationalizationTensorEquiv` | 全整数次数の群同型・ℤ 線形同型 |

参照：BF 1978 §2、HTT A.3.3、HA §1.4.2。
保存単位の対象ビルド 2365 jobs 成功。
私有宣言を含む 165 モジュール 2441 宣言で標準三公理のみ。
L9d は進行中。次は次数補正した模型からの実際の射と、元の X からの標準射を扱う。


## 57. L9d の次数補正した模型からの実際の射の計算

零段を落とす tail の整数次数群の比較は、厳密なスペクトルの射に関して自然である。
同じ正次数を表す元の一段先の表示へ移し、既存の任意段表示の自然性で検証した。
これにより次数補正した loop 模型から有理化対象への実際の厳密な射を構成し、
始域の群を元の X の群へ同定した下で a↦a⊗1 を誘導すると証明した。

この模型からの射と元の X からの射を区別する。
群同型だけから両対象の間の厳密な射を得ることはできない。
次は元の X とこの模型を結ぶ実際の比較を構成するため、loop の符号を扱う。

| 主要宣言 | 内容 |
| --- | --- |
| `OmegaSpectrum.tailHomotopyEquiv_natural` | tail の群の比較の厳密な射についての自然性 |
| `OmegaSpectrum.rationalizationModel` / `.rationalizationModelHomotopyEquiv` | 次数を合わせた loop 模型と元の整数次数群の表示 |
| `OmegaSpectrum.rationalizationModelMap` | loop 模型から有理 telescope への厳密な射 |
| `OmegaSpectrum.rationalizationModelMap_homotopy` | 全整数次数の a⊗1 の計算 |

参照：BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 2367 jobs 成功。
私有宣言を含む 167 モジュール 2449 宣言で標準三公理のみ。
L9d は進行中。元の X からの標準射と自然性は未完了。


## 58. L9d の整数次数射と構造射の符号変更の実際の比較

円の Kan 置換の指定基本類を任意の基本群の元へ送る実際の自己射を構成した。
これを整数冪へ適用し、負の次数も含む円の自己射と、その全正次数群での整数冪の作用を証明した。
loop の逆元を表す実際の射を選び、その誘導準同型が通常の逆元になることを検査した。
符号反転の二回合成は恒等射と基点固定でホモトピックになる。
自己合成から全基点の同型性を検出する補題により、符号反転は全基点の π_* 同型である。
これは定数 loop の基点だけの計算ではない。

厳密な自己射 r により構造射を σ_n≫r_(n+1) に変える一般の Kan 列を構成した。
n 段の比較射に r の n 回反復を使えば、厳密な比較射が得られる。
対合性を厳密な等式で要求する必要はない。
r が各段の全基点 π_* 同型なら、変更後も Ω 条件が保たれる。
変更後の列を cofibrant に置換し、元の単射構造射に沿って比較を持ち上げた。
この BF 対象間の比較射は、各段および全整数次数で π_* 同型である。
loop cotensor の符号反転へ適用し、構造射の符号を変えた実際の BF 模型への比較を得た。

| 主要宣言 | 内容 |
| --- | --- |
| `CirclePower.classMap` / `.integerPowerMap` | 指定基本類および整数次数を実現する円の自己射 |
| `LoopMappingClasses.post_integerPower` | 任意のパラメータでの整数冪の作用 |
| `LoopMappingClasses.inversion` / `.groupMap_inversion` | 実際の逆元の射と通常の正次数群の逆元 |
| `LoopMappingClasses.groupMap_pre_integer` | 円の整数次数射の全正次数群での作用 |
| `LoopMappingClasses.pre_neg_one_twice_homotopy` / `.pre_neg_one_piIsomorphism` | 符号反転の対合性と全基点の同型性 |
| `KanPiIsomorphism.of_self_comp` | 自己合成から全基点の同型性を検出 |
| `KanSequence.twist` / `.twistMap` / `.twist_omegaCondition` | 構造射の変更と反復による厳密比較、Ω 条件の保存 |
| `OmegaSpectrum.twistComparison` / `.twistComparison_piIsomorphism` | 変更後の BF 対象への厳密な π_* 同型 |
| `OmegaSpectrum.negatedCotensor` / `.negatedCotensorComparison_piIsomorphism` | 符号を変えた loop 模型の実際の比較 |

参照：Goerss–Jardine I §7、Kerodon §3.2.3、BF 1978 §2、HTT A.3.3、HA §1.4.2。
保存単位の対象ビルド 2375 jobs 成功。
私有宣言を含む 175 モジュール 2502 宣言で標準三公理のみ。
L9d は進行中。次はホモトピー可換な段の比較を厳密な射へ直す相対充填を扱う。


## 59. L9d のホモトピー可換な段の比較の厳密化

単射な点つき部分対象上の基点固定ホモトピーを、指定した始点を保って全体へ延長した。
延長したホモトピーの基点の固定は、部分対象の基点から回収される。
通常のパラメータ族による頂点と点つき閉構造による頂点を、smash の非基点側の単位の評価で比較した。
この二つの頂点表示は厳密に一致する。
その結果、射の成分の等式は前合成・後合成・suspension で保たれる。

単射な構造射を持つ源から Kan 列への段ごとの比較について、
成分での構造可換式から実際の厳密な列の射を構成した。
零段を保ち、修正した n 段を固定するように次段のホモトピーを延長する。
各段は指定した元の射と同じ成分を保ち、全基点の π_* 同型性も保つ。
標的が Ω 列なら、さらに cofibrant 置換へ持ち上げ、実際の BF 対象間の π_* 同型を得られる。

この一般補題を元の X の有理化写像へ適用するには、
符号を調整した loop 模型への随伴構造射の成分での可換性の幾何的な証明がまだ必要である。
特に二つの円の変数の交換と符号反転を実際のホモトピーで比較する部分を残している。
この未証明の条件を追加公理や入力構造として有理化の完成に組み込まない。

| 主要宣言 | 内容 |
| --- | --- |
| `PointedExtension.exists_homotopy_from_zero` / `.exists_adjustment` | 始点を保つ相対ホモトピー延長と制限を厳密にする修正 |
| `PointedMapping.pointFamily_closed` / `.familyVertex_eq_pointedHomVertex` | 頂点の二つの表示の厳密な一致 |
| `PointedMapping.componentOf_suspension` | suspension による成分の等式の保存 |
| `KanSequence.rectify` / `.rectify_component` | 段ごとのホモトピー可換な比較の厳密化 |
| `KanSequence.rectify_levelwise` | 厳密化による全基点の同型性の保存 |
| `OmegaSpectrum.rectifyInto` / `.rectifyInto_projection` | 標的の BF 置換への実際の射と因子分解 |
| `OmegaSpectrum.rectifyInto_piIsomorphism` | 厳密化した BF 射の全整数次数の同型性 |

参照：Goerss–Jardine I §7、BF 1978 §2、HTT A.3.3、HA §1.4.2。
保存単位の対象ビルド 2380 jobs 成功。
私有宣言を含む 180 モジュール 2543 宣言で標準三公理のみ。
L9d は進行中。次は二つの円の変数の交換の符号を幾何的に比較する。


## 60. L9d の二つの三角形による符号比較の幾何的な補助対象

区間の正方形への上側・下側の三角形の射と共通の対角辺を構成した。
座標の交換は二つの三角形を厳密に交換し、両三角形の中間の面は同じ対角辺となる。
ホーン Λ[2,1] を潰した相対三角形を作り、残る辺を円からの点つき射として構成した。
この相対三角形の基点包含は anodyne であり、Kan 値の点つき写像空間は全単射への RLP を持つ。
さらにその写像空間の恒等射と零射を結ぶ、基点固定の実際の収縮も充填した。

ホーンに欠けた面を引き戻すとその面の境界になることを全次元で証明した。
ホーンと欠けた面の和が全境界となることを使い、境界を二つの部分の pushout として表示した。
共通部分を面の境界へ戻す射を作り、ホーンを潰して残る面を球面へ送る付着写像を構成した。
二次元で円へ cell を付けた対象と相対三角形を、通常の点つき同型で比較した。
この同型から対角辺の円からの射の単射性が従う。
よって相対三角形から対角 loop への写像空間の制限は Kan fibration である。

二つの三角形を共通の対角辺で貼り合わせた表示と、そこでの交換の逆元の計算は未完了である。
これを証明して元の X からの標準射へ適用するまで L9d は進行中とする。

| 主要宣言 | 内容 |
| --- | --- |
| `SquareTriangles.upper` / `.lower` / `.upper_diagonal` / `.upper_swap` | 正方形の二つの三角形と対角辺・交換 |
| `triangleDisk` / `triangleDiskDiagonal` | ホーンを潰した相対三角形と対角辺の円 |
| `triangleDiskHom_terminal_rlp` / `triangleDiskHom_exists_contraction` | Kan 値写像空間の全単射 RLP と基点固定の収縮 |
| `preimage_horn_face` / `hornBoundaryPushout` | 欠けた面との交わりと全境界の pushout 表示 |
| `boundaryFaceCollapse` / `boundaryFaceCollapse_face` | ホーンを潰す付着写像と残る面での計算 |
| `triangleCellIso` | 相対三角形と円への二次元 cell 付着の同型 |
| `triangleDiskDiagonal_mono` / `triangleDisk_restriction_fibration` | 対角辺の単射性と写像空間の Kan fibration |

参照：Goerss–Jardine I §7、Kerodon §§3.1・3.2.3、BF 1978 §2、HTT A.3.3。
保存単位の対象ビルド 2389 jobs 成功。
私有宣言を含む 189 モジュール 2624 宣言で標準三公理のみ。
L9d は進行中。次は正方形の二つの三角形の貼り合わせと交換の符号を計算する。

## 61. L9d の正方形の厳密な三角形分割

二つの三角形の包含の単射性を、頂点の座標の和から回収した。
区間値の二つの単調写像は一方が他方以下となるため、全ての正方形の単体はどちらかの三角形に属する。
両方に属する単体は共通の対角辺から来ることも示した。
各単体次数での pullback と被覆から型の pushout を得て、評価関手によって単体集合の pushout へ戻した。
外側の四辺を座標軸の射として厳密に計算した。

| 主要宣言 | 内容 |
| --- | --- |
| `SquareTriangles.upper_mono` / `.lower_mono` | 二つの三角形の包含の単射性 |
| `SquareTriangles.upper_lower_cover` | 全単体次数での二つの三角形の被覆 |
| `SquareTriangles.upper_lower_intersection` | 交わりの対角辺への因子分解 |
| `SquareTriangles.app_isPullback` / `.app_isPushout` | 単体次数ごとの普遍性 |
| `SquareTriangles.isPushout` | 正方形の厳密な三角形分割 |
| `SquareTriangles.upper_face_zero` / `.lower_face_last` | 外側の辺の座標表示 |

参照：Goerss–Jardine I §7、Kerodon §3.2.3、BF 1978 §2。
保存単位の対象ビルド 2394 jobs 成功。
私有宣言を含む 194 モジュール 2660 宣言で標準三公理のみ。
L9d は進行中。次は外側の境界を潰した点つきの貼り合わせを構成する。

## 62. L9d の正方形の境界の二方向の商

境界で定数な単体のパラメータ族を球面との積へ降ろす一般構成を作った。
商射上での復元と球面の基点での定数性を厳密に計算した。
パラメータの指定部分での定数性も降下後に保たれ、この指定部分の射には単射性を要しない。
この構成を二度適用して正方形の四辺を潰し、二つの円の積からの reduced map を得た。
両軸の定数性から smash 積からの実際の点つき射へ降ろした。
二つの商射と smash の商射を前合成すると元の正方形の写像へ戻る。

| 主要宣言 | 内容 |
| --- | --- |
| `SphereSimplex.productDesc` | 境界定数な単体の族の球面への降下 |
| `SphereSimplex.quotient_productDesc` / `.base_productDesc` | 商射上の復元と基点条件 |
| `SphereSimplex.productDesc_parameter_constant` | パラメータの指定部分の定数性の保存 |
| `SphereSimplex.squareDesc` / `.squareDesc_quotient` | 正方形から円の積への降下と復元 |
| `SphereSimplex.squareDesc_base_left` / `.squareDesc_base_right` | 両軸での定数性 |
| `SphereSimplex.squareSmashDesc` / `.squareSmashDesc_quotient` | smash 積への点つき降下と復元 |

参照：Goerss–Jardine I §7、Kerodon §3.2.3、BF 1978 §2。
保存単位の対象ビルド 2396 jobs 成功。
私有宣言を含む 196 モジュール 2685 宣言で標準三公理のみ。
L9d は進行中。次は相対三角形の貼り合わせとの比較の存在と一意性を示す。

## 63. L9d の正方形上での一意性の判定

境界の頂点を使い、円の商射が全射であることを pushout の全射性から証明した。
閉構造の積関手が全射を保つことにより、二つの円の商射の積も全射となる。
smash の商の普遍性と合わせて、二つの円の smash 積からの点つき射は正方形上で判定できる。
また境界との積からの射を、境界の各面との積上で判定する補題を構成した。

| 主要宣言 | 内容 |
| --- | --- |
| `circleQuotient_epi` / `squareCircleQuotient_epi` | 円の商射とその積の全射性 |
| `squareSmash_hom_ext` | 正方形上での smash 積からの射の一意性 |
| `boundary_tensor_hom_ext` | 境界との積における面ごとの等式判定 |

参照：Goerss–Jardine I §7、Kerodon §3.2.3。
保存単位の対象ビルド 2398 jobs 成功。
私有宣言を含む 198 モジュール 2692 宣言で標準三公理のみ。
L9d は進行中。次は二つの相対三角形から貼る写像の四辺の条件を検証する。

## 64. L9d の相対三角形の二つの写像の貼り合わせ

相対三角形の外側の二辺が基点へ潰れることを、ホーンの cofiber の式から証明した。
正方形の境界の四つの端点パラメータを、三角形分割の外側の面と座標射影で表示した。
第二変数に境界を持つ積の射についても各面で判定する補題を構成した。
共通の対角辺で一致する二つの点つき写像を、正方形の pushout により貼り合わせた。
その写像の四辺が基点へ写ることを証明し、円の smash 積からの実際の点つき射を得た。
座標の交換は二つの三角形の写像の交換となり、smash へ降ろした写像は正方形上で元に戻る。

| 主要宣言 | 内容 |
| --- | --- |
| `triangleDiskQuotient_outer_face` | 相対三角形の外側の辺の消滅 |
| `SquareTriangles.first_endpoint_zero` / `.second_endpoint_one` | 正方形の境界と三角形の外側の面の対応 |
| `tensor_boundary_hom_ext` | 第二変数の境界との積の面ごとの判定 |
| `trianglePairSquare` / `upper_trianglePairSquare` / `lower_trianglePairSquare` | 二つの相対三角形の貼り合わせと復元 |
| `trianglePairSquare_boundary_left` / `trianglePairSquare_boundary_right` | 貼った写像の四辺の消滅 |
| `trianglePairSmash` / `trianglePairSmash_quotient` | 円の smash 積への点つき射と正方形での復元 |
| `trianglePairSquare_swap` | 座標交換と二つの相対三角形の交換 |

参照：Goerss–Jardine I §7、Kerodon §3.2.3、BF 1978 §2。
保存単位の対象ビルド 2401 jobs 成功。
私有宣言を含む 201 モジュール 2718 宣言で標準三公理のみ。
L9d は進行中。次は正方形から相対三角形へ制限する逆構成を証明する。

## 65. L9d の円の smash 積の相対三角形による厳密な pushout

四辺で定数な正方形の写像について、外側の四辺の定数性を三角形の面の条件へ移した。
二つの三角形のホーンを潰し、相対三角形からの点つき射へ制限した。
両制限は共通の対角辺で厳密に一致する。
制限して貼る往復と、貼ってから両方へ制限する往復が厳密な等式であることを証明した。

二変数の reduced map を正方形へ引き戻すと四辺で定数となることを実証した。
円の smash 積の恒等写像の reduced 表示にこれを適用し、正方形の標準商射から両相対三角形の包含を作った。
共通の対角辺の可換条件、任意の標的への貼り合わせの両脚での復元、一意性を合わせた。
結果は点つき単体集合の圏での厳密な pushout であり、導来性や ∞ 普遍性の主張は含まない。

| 主要宣言 | 内容 |
| --- | --- |
| `square_upper_horn_constant` / `square_lower_horn_constant` | 四辺の消滅から両ホーンの消滅 |
| `squareUpperRestriction` / `squareLowerRestriction` / `squareRestrictions_diagonal` | 二つの相対三角形への制限と対角辺の一致 |
| `trianglePairSquare_restrictions` / `squareUpperRestriction_pair` / `squareLowerRestriction_pair` | 制限と貼り合わせの厳密な往復 |
| `reducedSquare_boundary_left` / `reducedSquare_boundary_right` | reduced map の正方形への引き戻しの境界条件 |
| `circleSmashSquareQuotient` / `circleSmashUpper` / `circleSmashLower` | 正方形の商射と両相対三角形の包含 |
| `circleSmashTriangles_hom_ext` / `circleSmashUpper_pair` / `circleSmashLower_pair` | 両脚での判定と任意の貼り合わせの復元 |
| `circleSmashTriangles_isPushout` | 円の smash 積の二つの相対三角形による厳密な pushout |

参照：Goerss–Jardine I §7、Kerodon §3.2.3、BF 1978 §2。
保存単位の対象ビルド 2406 jobs 成功。
私有宣言を含む 206 モジュール 2769 宣言で標準三公理のみ。
L9d は進行中。次は写像空間の pullback 表示と、両三角形の交換の成分での逆元の比較を行う。

## 66. L9d の二重円の写像空間と三角形の交換

相対三角形の pushout に反変内部 Hom 関手を適用した。
二つの円の smash 積の写像空間は、相対三角形の写像空間二つを対角辺の写像空間上で引いた厳密な pullback となる。
Kan 値では対角辺への制限が fibration なので、上側への制限も Kan fibration となる。
正方形の座標交換を円の smash の交換へ降ろす等式を証明した。
smash の交換は上側・下側の包含を厳密に交換する。
相対三角形の写像空間の収縮と、この交換が成分の逆元に対応する計算の合成は継続する。

| 主要宣言 | 内容 |
| --- | --- |
| `circleSmashMapping_isPullback` | 二重円の写像空間の相対三角形による pullback 表示 |
| `circleSmashUpper_restriction_fibration` | 上側の相対三角形への制限の Kan fibration |
| `circleSmashSquareQuotient_swap` | 正方形の商射と smash の交換の可換性 |
| `circleSmashUpper_swap` / `circleSmashLower_swap` | 両相対三角形の包含の交換 |

参照：Goerss–Jardine I §7、Kerodon §§3.1.3・3.2.3、BF 1978 §2。
保存単位の対象ビルド 2408 jobs 成功。
私有宣言を含む 208 モジュール 2777 宣言で標準三公理のみ。
L9d は進行中。次は連結写像の逆元の三角形を fibration に沿って持ち上げる。

## 67. L9d の自己 pullback の交換と基本群の逆元の幾何的な比較

底の左逆元を表す三角形の零面に元の辺の持ち上げ、一面に基点の定数辺を置いた。
fibration のホーン持ち上げで二面を取り出すと、基点から元の持ち上げの始点へ向かう逆向きの辺が得られる。
この辺は底で左逆元の辺へ写る。
同じ左逆元の通常の連結射の持ち上げと組にすると、自己 pullback 内に実際の辺を構成できる。
その両端点は、逆元の連結射の fiber 点と、元の連結射の fiber 点の二因子を交換した点になる。

零単体からの射の成分を Yoneda で定義し、この辺を π₀ の等式へ送った。
Kan 複体の左逆元の三角形の存在により任意の基本群の元で比較できる。
代表によらない連結射の式へ戻し、自己 pullback の交換は連結射の像上で基本群の逆元に対応すると証明した。
この一般式は全空間の収縮可能性を使わず、全空間と底の Kan 性と fibration 性だけを仮定する。

| 主要宣言 | 内容 |
| --- | --- |
| `exists_inverse_edge` | 逆元の三角形からの逆向きの辺の持ち上げ |
| `selfPullbackFiberInclusion` / `selfPullbackSwap` | fiber の第一因子への包含と二因子の交換 |
| `selfPullback_exists_inverse_edge` | 交換と逆元の二つの代表を結ぶ自己 pullback 内の辺 |
| `zeroMapComponent` / `zeroMapComponent_edge` | 零単体の射の成分と辺の両端点の一致 |
| `selfPullback_swap_inverse_representative` | 任意の代表に対する逆元の代表での比較 |
| `selfPullbackConnecting` / `selfPullbackConnecting_eq` | 自己 pullback へ向かう連結射とその代表の計算 |
| `selfPullbackConnecting_swap` | 二因子の交換と基本群の逆元の代表によらない式 |

参照：Goerss–Jardine I §7、Kerodon §§3.2.3・3.2.5。
保存単位の対象ビルド 2413 jobs 成功。
私有宣言を含む 213 モジュール 2798 宣言で標準三公理のみ。
L9d は進行中。次は連結な全空間の場合にこの連結射の全射性を示す。

## 68. L9d の自己 pullback の全成分と loop の整数冪の後合成

底の成分が一つの fibration の fiber 包含は成分で全射となることを零次数の完全列から示した。
これを自己 pullback の第二射影に適用し、第二因子を基点に固定した元の fiber が全成分を代表すると証明した。
全空間が連結なら元の連結射も全 fiber 成分を代表するため、自己 pullback への連結射は全射である。
この全射性は収縮可能性より弱い連結性だけを使う。

fibration の可換四角形が自己 pullback と fiber の包含に誘導する射を作った。
連結写像の自然性を自己 pullback の成分へ移し、基点の等式の移送も明示した。
底の基本群で逆元に作用する基点を保つ自己四角形は、自己 pullback の全成分で二因子の交換と一致する。
別に内部 Hom の源二つの交換同型を使い、loop の整数冪の射の後合成は任意のパラメータを持つ写像空間の正次数群に整数冪で作用すると証明した。
これらを相対三角形の写像空間へ適用する部分は継続する。

| 主要宣言 | 内容 |
| --- | --- |
| `fiberInclusion_piZero_surjective` / `fiberInclusion_piZero_surjective_at` | 連結な底の上の fiber 包含の成分での全射性 |
| `selfPullbackFiberInclusion_surjective` / `selfPullbackConnecting_surjective` | 連結な全空間の自己 pullback の全成分の代表 |
| `selfPullbackMap` / `selfPullbackFiberInclusion_natural` | 可換四角形の自己 pullback への作用と包含の自然性 |
| `selfPullbackConnecting_natural` / `selfPullbackConnecting_natural_fixed` | 連結射の自然性と基点の移送 |
| `selfPullbackMap_eq_swap_on_components` | 逆元に作用する射と二因子の交換の全成分での一致 |
| `LoopMappingClasses.groupMap_post_integer` | loop の整数冪の後合成の正次数群での作用 |

参照：Goerss–Jardine I §7、Kerodon §§3.2.5・3.2.6、BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 2418 jobs 成功。
私有宣言を含む 218 モジュール 2814 宣言で標準三公理のみ。
L9d は進行中。次は相対三角形の写像空間に交換と逆元の一般式を適用する。

## 69. L9d の loop 値の二重円の変数交換と符号反転

相対三角形の写像空間の実際の収縮から、連結成分が一つであることを証明した。
二重円の写像空間と自己 pullback の厳密な同型を取り出し、変数交換が両因子の交換となる可換式を示した。
標的の写像の後合成についてもこの同型は自然である。
これらに自己 pullback の全成分での逆元の比較を適用した。

標的が円の Kan 置換からの内部 Hom である場合、二つの通常の円の交換は標的の loop の符号反転の後合成と π₀ 上で一致する。
一般の自己 pullback の基本群の基点を零写像の基点と照合する等式の移送を明示した。
別に二つの Kan 円を源とする写像では、どちらの円の整数次数射も同じ整数冪に作用することを証明した。
通常の円から Kan 円への二変数の比較、および元のスペクトルの随伴構造射への適用は継続する。

| 主要宣言 | 内容 |
| --- | --- |
| `triangleDiskHom_piZero_subsingleton` | 相対三角形の Kan 値写像空間の連結性 |
| `circleSmashMappingPairIso` / `circleSmashMappingPairIso_swap` | 自己 pullback の同型と変数交換の可換性 |
| `PointedMapping.pre_post_comm` / `circleSmashMappingPairIso_post` | 源の制限と後合成の可換性と同型の自然性 |
| `circleSmashLoop_swap_components` | loop 値の二重円の交換と標的の符号反転の成分での一致 |
| `LoopMappingClasses.pre_integer` / `.pre_integer_eq_post_integer` | 二つの Kan 円のいずれの次数射も同じ整数冪に作用 |

参照：Goerss–Jardine I §7、Kerodon §§3.2.3・3.2.5、BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 2423 jobs 成功。
私有宣言を含む 223 モジュール 2829 宣言で標準三公理のみ。
L9d は進行中。次は二つの円の smash の写像と反復内部 Hom の比較を実装する。

## 70. L9d の反復 curry と通常の円から Kan 円への二変数の比較

テンソルの結合子で左随伴を比較し、右随伴の一意性から反復内部 Hom の自然同型を構成した。
その順写像が評価射を二度 curry した射であり、Mathlib の `ihomCurryIso` と一致すると証明した。
標的の写像の後合成に関する自然性を取り出し、テンソルの braiding が既存の内部 Hom の交換と一致することも示した。

二つの Kan 円を通常の円へ制限する実際の点つき射を作った。
源の anodyne な制限の全単射 RLP と標的の π_* 同型の内部 Hom での保存により、この射は全基点 π_* 同型となる。
二つの源の同時の制限は源の交換と標的の後合成に関して自然であり、通常の円と Kan 円の間の可換式を得た。
これらの同型と自然性を用いて、loop 値の二重円の交換と標的の符号反転の一致を、反復内部 Hom で記述し直した。
二つの Kan 円の交換についても同じ π₀ の式が成立する。

| 主要宣言 | 内容 |
| --- | --- |
| `InternalHomTensor.natIso` / `.iso` / `.hom_eq` | 反復 curry の自然同型と評価射による明示式 |
| `InternalHomTensor.iso_eq_ihomCurryIso` / `.natural_post` / `.natural_swap` | Mathlib の同型との一致、後合成と交換の自然性 |
| `doubleCircleRestriction` / `doubleCircleRestriction_piIsomorphism` | Kan 円から通常の円への二変数の制限と全基点 π_* 同型性 |
| `InternalHomExchange.restrictBoth_exchange` / `.restrictBoth_post` | 同時の源の制限と交換・後合成の自然性 |
| `doubleCircleRestriction_exchange` / `doubleCircleRestriction_post` | 二つの円の制限と交換・後合成の厳密な可換式 |
| `ordinaryDoubleCircleLoop_exchange` / `kanDoubleCircleLoop_exchange` | loop 値の反復内部 Hom の交換と符号反転の成分での一致 |

参照：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 2429 jobs 成功。
私有宣言を含む 228 モジュール 2853 宣言で標準三公理のみ。
L9d は進行中。次は標的の loop の符号を源の loop 変数の符号へ移す。

## 71. L9d の Ω 条件からの二つの Kan 円の交換の符号

内部 Hom の交換を標的についての自然同型としてまとめ、その成分が既存の交換同型と一致することを証明した。
これを使い、loop 値の類と写像空間の基本群の比較について標的の自然性を得た。
標的自身の loop の整数次数射と、類を定める loop の整数次数射は同じ整数冪に作用する。
したがって loop 値の二つの Kan 円の交換は内側の円の符号反転と成分で一致する。

通常の円による loop への射を Kan 円による loop へ持ち上げる実際の点つき射を作った。
円の anodyne な制限は全単射への RLP を持ち、持ち上げは元の射へ厳密に制限される。
元の射が全基点 π_* 同型なら持ち上げも同型である。
二重の内部 Hom の標的の π_* 同型による後合成は成分で単射なので、
Kan loop へ同型で写る対象にも交換の符号の式を反映できる。
特に承認済みの通常の円の Ω 条件を持つ対象で、交換は内側の Kan 円の符号反転として計算できる。

| 主要宣言 | 内容 |
| --- | --- |
| `InternalHomExchange.naturalIso` / `.naturalIso_app` / `.natural_post` | 交換の標的の自然性と既存の成分との一致 |
| `LoopMappingClasses.classEquiv_post` | loop 値の類と基本群の比較の標的の自然性 |
| `LoopMappingClasses.post_target_integer` / `.target_integer_eq_inner_integer` | 標的の loop の整数冪と内側の loop の整数冪の一致 |
| `kanLoop_exchange_sign` | loop 値の二つの Kan 円の交換と内側の符号反転 |
| `kanLoopLift` / `kanLoopLift_comparison` / `kanLoopLift_piIsomorphism` | Kan 円の loop への実際の持ち上げ、制限の可換式、同型性 |
| `delooped_exchange_sign` / `omega_exchange_sign` | Kan loop への π_* 同型または通常の Ω 条件からの交換の符号 |

参照：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 2434 jobs 成功。
私有宣言を含む 233 モジュール 2872 宣言で標準三公理のみ。
L9d は進行中。次は任意の源のパラメータを反復内部 Hom の内側へ移す比較を実装する。
ここまでの π₀ 上の自己射の等式だけから、任意の源の写像空間での等式は推論しない。

## 72. L9d の任意の源のパラメータを保つ交換の符号

反復 curry はテンソルの第一・第二因子の任意の制限に関して自然であることを二重評価で証明した。
外側のパラメータ A を二つの源の内側へ移す自然同型を構成した。
二つの源を一つのテンソルへ戻してから A と交換し、再び curry する構成である。
この同型は二つの源の交換、内側の源の制限、外側の源の制限、標的の後合成と厳密に可換となる。

通常の Ω 条件から、任意の源の写像空間への Kan 円による実際の delooping 射を構成した。
標的の π_* 同型の後合成による保存と源の交換の同型から、この射も全基点 π_* 同型である。
パラメータを標的の側へ移し、その写像空間の Ω 条件に交換の符号の式を適用した。
結果として任意の源 A からの二重 loop 値の写像でも、円の交換と内側の符号反転は同じ成分となる。
この主張は π₀ 上の自己射の等式を無条件に後合成へ持ち上げたものではなく、上記の実際の同型の可換式で証明した。
また suspension–loop 随伴の逆は成分の等式を保つことを、suspension と評価の後合成から証明した。

| 主要宣言 | 内容 |
| --- | --- |
| `InternalHomTensor.natural_pre_left` / `.natural_pre_right` | 反復 curry の二つの源の制限の自然性 |
| `InternalHomExchange.pairNatIso` / `.pairIso` / `.pairIso_hom` | パラメータを二つの源の内側へ移す同型と明示式 |
| `InternalHomExchange.pairIso_post` / `.pairIso_swap` / `.pairIso_pre_inner` / `.pairIso_pre_outer` | パラメータの移動と後合成・交換・制限の可換性 |
| `mappingKanDelooping` / `mappingKanDelooping_piIsomorphism` | 任意の源の写像空間の Kan 円による Ω 条件 |
| `omega_exchange_sign_parameterized` / `omega_exchange_sign_component` | 任意のパラメータを保つ交換と符号反転の成分での一致 |
| `PointedMapping.componentOf_uncurry` / `.componentOf_of_curry` | 随伴側の成分の等式から suspension 側へ戻す補題 |

参照：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 2439 jobs 成功。
私有宣言を含む 238 モジュール 2896 宣言で標準三公理のみ。
L9d は進行中。次は随伴構造射から符号を調整した loop 列への比較を組み立てる。

## 73. L9d の段ごとの同型を持つ BF 射の逆方向の厳密な比較

各段で全基点 π_* 同型の BF 射の mapping path の終点射は、各段で全単射に対する RLP を持つ。
cofibrant な標的の列から恒等射をこの終点射へ持ち上げ、厳密な列の切断を構成した。
元の源への射影を合成することで逆方向の厳密な BF 射を得た。
切断の合成が恒等射であることと源射影の RLP から、逆方向の射も各段で全基点 π_* 同型となる。
従って全整数次数でも π_* 同型である。

全単射 RLP 射への合成が等しい二つの点つき射は同じ成分を持つことを、基点を固定する垂直ホモトピーから示した。
これを mapping path の終点射と源射影に適用し、各段で左右の合成は恒等射と同じ点つき成分になることを証明した。
スペクトル全体の enriched ホモトピーや coherent nerve での同値とはまだ同定しない。
符号を調整した loop 模型から元の有理化の loop 模型へ戻す実際の射に用いる。

| 主要宣言 | 内容 |
| --- | --- |
| `PointedMapping.componentOf_eq_of_comp_eq_rlp` | 全単射 RLP 射への同じ合成による点つき成分の一致 |
| `OmegaSpectrum.inversePathTarget_rlp` / `.inversePathSection` / `.inversePathSection_target` | mapping path の終点射の RLP と厳密な列の切断 |
| `OmegaSpectrum.levelwiseInverse` / `.levelwiseInverse_levelwise` | 逆方向の厳密な BF 射と各段の全基点 π_* 同型性 |
| `OmegaSpectrum.levelwiseInverse_left_component` / `.levelwiseInverse_right_component` | 各段での左右の合成と恒等射の成分の一致 |
| `OmegaSpectrum.levelwiseInverse_piIsomorphism` | 逆方向の射の全整数次数の同型性 |

参照：Goerss–Jardine I §7、BF 1978 §2、HTT A.3.3、HA §1.4.2。
保存単位の対象ビルド 2441 jobs 成功。
私有宣言を含む 240 モジュール 2911 宣言で標準三公理のみ。
L9d は進行中。次は二つの随伴構造射の合成を符号を変えた loop 列の構造射と比較する。

## 74. L9d の随伴構造射から符号を調整した BF loop 模型への実際の射

任意の源を持つ反復 loop 値の射で、内側の loop の符号を二度反転すると同じ成分へ戻ることを整数冪の作用から証明した。
Kan 円への二つの随伴の射を合成し、通常の円への制限を源の交換と前合成の自然性で移した。
二つの円の交換から来る符号と構造射の後に加える符号は、この二回の符号反転の式により打ち消し合う。

Kan 列の一段の添字移動と厳密な射の添字移動を作った。
Kan 円の内部 Hom 列の構造射の後に符号を反転して一段をずらした列は Ω 条件を満たす。
各段の元の随伴構造射を Kan 円の loop へ実際に持ち上げた。
上記の符号の計算から、これらは符号を調整した loop 列に対して成分で構造可換となる。
随伴側の等式を uncurry により元の suspension 構造射の成分の等式へ戻した。

単射な構造射を用いる既存の相対充填でこの比較を厳密化し、cofibrant 比較射へ持ち上げた。
元の Ω スペクトルから符号を調整した BF loop 模型への実際の厳密な射を得た。
この射は各段で全基点 π_* 同型であり、全整数次数でも同型である。
通常の有理化の loop 模型への比較、および telescope への元の対象からの単位写像は次に合成する。

| 主要宣言 | 内容 |
| --- | --- |
| `PointedMapping.componentOf_nested_neg_one_twice` | 任意の源のパラメータを保つ二回の符号反転の消去 |
| `signed_adjoint_composition` | 二つの随伴構造射の合成と符号を変えた loop 構造の比較 |
| `KanSequence.tail` / `.tailHom` / `.tail_omegaCondition` | Kan 列と射の一段の移動と Ω 条件 |
| `KanSequence.signedLoopTail` / `.signedLoopTail_omegaCondition` / `.signedLoopTail_adjoint` | 符号を調整した loop 列とその随伴構造射 |
| `KanSequence.kanAdjoint` / `.kanAdjoint_comparison` / `.kanAdjoint_piIsomorphism` | Kan 円へ持ち上げた随伴構造射と各段の同型性 |
| `KanSequence.kanAdjoint_signedLoopTail_comm` | 符号を調整した列への成分での構造可換性 |
| `OmegaSpectrum.signedLoopModel` / `.signedLoopProjection` / `.signedLoopUnit` | 符号を調整した BF 模型と元の対象からの実際の厳密な射 |
| `OmegaSpectrum.signedLoopUnit_levelwise` / `.signedLoopUnit_piIsomorphism` | 比較射の各段と全整数次数の π_* 同型性 |

参照：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2、HTT A.3.3。
保存単位の対象ビルド 2446 jobs 成功。
私有宣言を含む 245 モジュール 2938 宣言で標準三公理のみ。
L9d は進行中。次は通常の一段先の cotensor 模型との実際の比較を合成する。

## 75. L9d の元の対象からの実際の有理化写像と全整数次数の単位の公式

通常の一段先の cotensor 模型から実際の内部 Hom 列へ射影し、
段ごとの符号反転の反復による twist の比較を合成した。
この比較を符号を調整した BF loop 模型の cofibrant 比較射へ持ち上げ、
二つの BF 模型の間の実際の各段 π_* 同型を構成した。
その逆方向の厳密な比較と、元の対象から符号を調整した模型への随伴の比較を合成した。
元の X から有理化に用いる通常の loop 模型への実際の厳密な各段 π_* 同型が得られた。

この射を telescope の零段からの射へ合成し、元の X を始域とする有理化の単位写像を構成した。
従来の loop 模型の群の表示と実際の比較射の誘導同型の差は群の自己同型として明示した。
その逆のテンソルを既存のテンソル同型へ合成し、実際の単位に適合する群の表示を得た。
その表示の下で、全整数次数の単位は a を a⊗1 へ送る。
加法群の標準の ℤ 加群構造による線形表示も構成した。

ここでは射を群の同型から推論しておらず、随伴・相対充填・mapping path・telescope の実際の射を合成している。
射の自然性は未完了のため L9d をまだ完了としない。
自然性を検証するため、単射置換前の内部 Hom 列の図式と既存の BF telescope の比較を次に構成する。

| 主要宣言 | 内容 |
| --- | --- |
| `signedLoopRawComparison` / `signedLoopRawComparison_levelwise` | 通常の loop 模型と符号を変えた Kan 列の厳密な比較 |
| `signedLoopComparison` / `signedLoopComparison_projection` / `signedLoopComparison_levelwise` | BF 模型の比較と各段の全基点 π_* 同型性 |
| `originalLoopModelMap` / `originalLoopModelMap_levelwise` / `originalLoopModelMap_piIsomorphism` | 元の X から通常の loop 模型への実際の厳密な同型比較 |
| `originalLoopModelEquiv` | 実際の比較射の誘導する全整数次数群の同型 |
| `rationalizationUnit` | 元の X から telescope への実際の厳密な単位写像 |
| `rationalizationUnitCoefficientEquiv` | 従来の群の表示と実際の比較の差を記す自己同型 |
| `rationalizationUnitHomotopyEquiv` / `rationalizationUnitTensorEquiv` | 単位に適合する全整数次数の乗法・加法・線形のテンソル表示 |
| `rationalizationUnit_homotopy` | 実際の単位が全整数次数で a を a⊗1 へ送る公式 |

参照：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2、HTT A.3.3。
保存単位の対象ビルド 2449 jobs 成功。
私有宣言を含む 248 モジュール 2960 宣言で標準三公理のみ。
L9d は進行中。次は置換前の Kan 列の関手的な telescope の比較と単位の自然性を扱う。

## 76. L9d の Kan 列の図式と自然変換の実際の BF 比較

厳密な Kan 列とその射を圏に束ねた。
filtered 余極限の Ω 条件の証明は、図式の値の単射性を使わない形に分離した。
各対象の Ω 条件だけを明示的に仮定し、Kan 列の余極限を単射置換する。
自然変換は余極限の Kan 列の厳密な射を誘導する。
それを cofibrant な始域から標的の全単射 RLP 比較射へ持ち上げ、実際の BF 射を得た。
成分ごとの全基点 π_* 同型は各段と全整数次数で保存される。

BF 図式を Kan 列へ忘れた場合、この構成は既存の filtered BF 対象と定義的に一致する。
既存の有理化対象を取り替えることなく、置換前の厳密な図式との比較に利用できる。
この一般化だけでは有理化の単位の自然性はまだ示していない。

| 主要宣言 | 内容 |
| --- | --- |
| `KanSequence.levelEvaluation` | Kan 列の圏とその段評価関手 |
| `KanSequence.filteredOmegaSpectrum` | 各対象の Ω 条件を仮定した Kan 図式の BF 余極限対象 |
| `OmegaSpectrum.forgetToKan` | BF 対象から Kan 列への忘却関手 |
| `OmegaSpectrum.filteredOmegaSpectrum_forget` | 忘却後の構成と既存の対象との等式 |
| `KanSequence.filteredKanMap` | 自然変換が誘導する Kan 余極限列の厳密な射 |
| `KanSequence.filteredSpectrumMap` / `filteredSpectrumMap_comparison` | BF 置換への持ち上げと段ごとの厳密な比較式 |
| `KanSequence.filteredSpectrumMap_levelwise` / `filteredSpectrumMap_piIsomorphism` | 成分の π_* 同型性の保存 |

参照：Goerss–Jardine I §7、BF 1978 §2、HTT A.3.3、HA §1.4.2。
保存単位の対象ビルド 2454 jobs 成功。
私有宣言を含む 253 モジュール 3013 宣言で標準三公理のみ。
L9d は進行中。次は円の前合成とスペクトルの後合成から厳密な有理化図式を作る。

## 77. L9d の置換前の厳密な有理化図式と実際の射への作用

円の Kan 置換の次数 2,3,4,… による前合成を、単射置換前の内部 Hom の Kan 列で並べた。
元のスペクトルの射は各段の後合成で作用し、前合成と厳密に可換する。
これにより有理化の Kan 列の図式の厳密な自然変換が得られた。
既存の cotensor の図式からは単射置換の射影による自然変換を構成した。
その成分は全て各段で全基点の π_* 同型である。

filtered BF 比較を使い、既存の telescope から関手的な図式の telescope への実際の各段 π_* 同型を得た。
次数移動の後で標的の比較射の逆方向の BF 射を構成し、元の f : X→Y に実際の X_ℚ→Y_ℚ を対応させた。
これは群の同型による写像の移送だけではなく、実際のスペクトルの射の合成である。
誘導準同型の関手法則・単位の自然性は継続して検証する。

| 主要宣言 | 内容 |
| --- | --- |
| `rawRationalSequence` / `rawRationalDiagram` | 置換前の内部 Hom の厳密な有理化図式 |
| `rawRationalSequenceMap` / `rawRationalDiagramMap` | スペクトルの射の後合成による厳密な自然変換 |
| `rationalDiagramProjection` / `rationalDiagramProjection_levelwise` | 既存の cotensor 図式からの各段 π_* 同型比較 |
| `rawRationalLoopTelescope` / `rawRationalLoopMap` | 関手的な図式の BF 対象と実際の射 |
| `rationalLoopProjection` / `rationalLoopProjection_levelwise` | 既存の telescope からの比較と各段の同型性 |
| `rationalizationProjection` / `rationalizationProjection_levelwise` | 次数移動後の比較 |
| `rationalizationMap` | 既存の有理化対象間の実際の厳密な射 |

参照：BF 1978 §2、Goerss–Jardine I §7、HTT A.3.3、HA §1.4.2。
保存単位の対象ビルド 2456 jobs 成功。
私有宣言を含む 255 モジュール 3032 宣言で標準三公理のみ。
L9d は進行中。次は単位写像の段ごとのホモトピー可換性と誘導群準同型の自然性を示す。

## 78. L9d の loop 模型と telescope 注入の自然性

Kan 円への随伴構造射の持ち上げは、通常の円への制限を通して成分で自然になる。
符号を変えた BF 模型への単位を置換前へ射影すると、その随伴構造射と同じ成分になることも示した。
自己射の反復と可換する射の一般的な補題により、段ごとの符号の補正は後合成に対して厳密に自然になる。
元の X から通常の loop 模型への実際の比較は、各段の成分で自然であり、全整数次数の群準同型でも自然である。

telescope の零段注入を関手的な図式の段の Kan 余極限へ射影すると、cotensor の射影と標準の注入の合成になる。
元の射の後合成と余極限の誘導射は厳密に整合するため、零段注入の各段の成分での自然性を得た。
全基点 π_* 同型への後合成の打ち消しと、同じ成分の BF 射の全整数次数でのホモトピー不変性も一般補題にまとめた。

| 主要宣言 | 内容 |
| --- | --- |
| `PointedMapping.componentOf_cancel_post_piIsomorphism` | 全基点 π_* 同型への後合成の成分での打ち消し |
| `KanSequence.kanAdjoint_natural` | Kan 円への随伴構造射の成分での自然性 |
| `signedLoopUnit_projection_component` | BF 単位の射影と随伴構造射の同じ成分 |
| `homotopyMap_eq_of_levelComponent` | 各段で同じ成分の BF 射の整数次数の誘導準同型の等式 |
| `KanSequence.iterateHom_natural` / `twistMap_natural_app` | 構造変更の比較の厳密な自然性 |
| `cotensorPost` / `cotensorPost_comparison` | 標的変数の実際の BF 射と射影後の計算 |
| `originalLoopModelMap_natural_component` / `originalLoopModelMap_natural` | 元の X から通常の loop 模型への実際の比較の自然性 |
| `rationalLoopInjection_projection` | 零段注入の Kan 余極限への厳密な射影式 |
| `rationalLoopInjection_natural_component` | telescope の零段注入の各段の成分での自然性 |

参照：Goerss–Jardine I §7、BF 1978 §2、HTT A.3.3、HA §1.4.2。
保存単位の対象ビルド 2463 jobs 成功。
私有宣言を含む 262 モジュール 3061 宣言で標準三公理のみ。
L9d は進行中。次はこれらの自然性を実際の有理化の単位で結合し、テンソル表示の自然性を検証する。

## 79. L9d 完了：実際の単位・射と全整数次数の自然な有理テンソル表示

元の X から既存の有理化対象への単位と、f : X→Y に対する実際の X_ℚ→Y_ℚ の射について、
各段の点つき写像空間の成分で自然性を証明した。
したがって全整数次数の誘導準同型で単位は自然である。

加法準同型が有理数倍を保存することを用い、有理テンソル群の準同型は a⊗1 上で決まることを実証した。
これを単位の自然性と単位のテンソル公式に適用した。
実際の射への作用は全整数次数の単位に適合するテンソル表示で π_*(f)⊗id_ℚ を与える。
その一意性から、実際の射の誘導準同型が恒等・合成を保つことも示した。
対象間の選んだ持ち上げ自体の厳密な関手法則や ∞ 普遍性は主張しない。

L9d の完了条件である、実際の telescope 対象・単位・射、Ω 条件、全整数次数のテンソル同型、
単位の a⊗1 の公式、自然性、加法性、誘導準同型の恒等・合成法則を全て検証した。
L9e の有限群の作用、段ごとの hG と Tot、有理自明作用の比較へ進む。

| 主要宣言 | 内容 |
| --- | --- |
| `rationalizationUnit_natural_component` / `rationalizationUnit_natural` | 実際の単位の各段の成分と全整数次数での自然性 |
| `rationalTensor_addHom_ext` | a⊗1 上での像による有理テンソル群の準同型の一意性 |
| `rationalTensor_realization_natural` / `rationalTensor_realization_ext` | 単位に適合する実際の準同型のテンソル表示と一意性 |
| `rationalizationUnitTensorEquiv_unit` | 加法・線形表示での実際の単位の公式 |
| `rationalizationUnitTensorEquiv_natural` | 実際の有理化の射が元の射の ℚ テンソルを誘導する公式 |
| `rationalization_homotopyMap_ext` | 実際の単位の像上での準同型の一意性 |
| `rationalizationMap_homotopy_id` / `rationalizationMap_homotopy_comp` | 実際の射への作用の π_* 上の恒等・合成法則 |

参照：Goerss–Jardine I §7、BF 1978 §2、HTT A.3.3、HA §1.4.2。
保存単位の対象ビルド 2468 jobs 成功。
私有宣言を含む 267 モジュール 3077 宣言で標準三公理のみ。
工程区切りの全体ビルドは共有ルートで F1 と F1B の relativeFunctorVertex の重複により失敗。
K-L9 の import 閉包は通っているため、回避策も他レーンの編集もせず L9e を継続する。

## 80. L9e の開始：群作用、段ごとの Kan end、有理平均化と係数の比較

厳密な群作用を通常の圏の End への準同型として与え、各段・Kan 列・全整数次数の群への作用を関手で構成した。
N レーンの Bousfield–Kan の重み付き end を読み取り専用で借り、基点の錐から点つき end を構成した。
その実際の射は恒等・合成を保ち、係数が Kan なら既存のホーン充填によって Kan になる。
群圏は対象の宇宙が小さいため AsSmall を挟み、hG の各段の実際の点つき Kan 複体と射を得た。
余単体 BF 対象についても同じ方法で homotopy totalization の各段の点つき Kan 複体と射を得た。
通常の Reedy 型の Tot との比較と BF 構造への束ね直しは未完了。

有限群の位数が ℚ で非零かつ可逆であることを明示した。
norm を位数で割る実際の平均化作用素を構成し、像の不変性・不変元での恒等性・冪等性を示した。
Mathlib の平均化による射影性と bar resolution–Ext の比較を使い、正次数の群コホモロジーの零対象性を証明した。
この比較は Mathlib の係数と群の宇宙が同じである制約を避けて扱えるよう、ℚ を含む標数零の体に一般化している。

点つき Whitehead と写像空間の成分の対称性から、L9 の全基点 π_* 同型を実際の単体的ホモトピー同値へ移した。
逆方向は N の可逆 path の二つの全単射 RLP 射と切断の分解から L9 の誘導写像の全単射性を示した。
この比較と N の path 分解による係数のホモトピー不変性から、点つき end が L9 の全基点 π_* 同型を保存すると証明した。
N の別定義の π_n や Sp の ∞ 極限性をこの段階の主張には用いていない。

| 主要宣言 | 内容 |
| --- | --- |
| `GroupAction` / `diagramFunctor` / `levelFunctor` / `homotopyFunctor` | 厳密な群作用と段・π_* の作用 |
| `PointedHomotopyLimit.obj` / `map` / `kanComplex` / `functor` | 基点を持つ Bousfield–Kan end と Kan 性・関手性 |
| `homotopyFixedLevel` / `homotopyFixedLevel_kanComplex` / `homotopyFixedLevelMap` | hG のレベルごとの実際の構成 |
| `homotopyTotalizationLevel` / `homotopyTotalizationLevel_kanComplex` | 余単体対象のレベルごとの Kan 模型 |
| `finiteGroupOrder_ne_zero` / `finiteGroupOrder_isUnit` | 平均化の分母の非零性と可逆性 |
| `rationalAverage` / `rationalAverage_invariant` / `rationalAverage_idempotent` | 実際の有理平均化の射影 |
| `rationalGroupCohomology_isZero` | 有限群・標数零の正次数群コホモロジーの消滅 |
| `pointed_piIsomorphism_homotopyEquivalence` / `kanPiIsomorphism_of_qCatEquivalence` | L9 の全基点 π_* 同型と既存の実際の path 充填の比較 |
| `PointedHomotopyLimit.map_piIsomorphism` | 段ごとの end による L9 の全基点 π_* 同型の保存 |

参照：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2、Kerodon 4.8.4.1、7.5.4.6。
保存単位の対象ビルド 3631 jobs 成功。
私有宣言を含む 274 モジュール 3113 宣言で標準三公理のみ。
L9e は進行中。次は内部 Hom と end の交換を構成し、hG・Tot を Kan Ω 列と BF 対象へ束ねる。
有理 Shapiro のスペクトルの実際の比較と π_* 同型性は未完了。

## 81. L9e の点つき閉構造による end と loop の交換

内部 Hom と end の交換、および一般の右随伴と end の交換を、射影と随伴の Hom 同値で実際に構成した。
これにより点つき end を忘れた後の end と、点つき内部 Hom を end に送った図式を計算できる。
既存の自由基点の追加と smash の基礎構成を読み取り専用で借り、自由基点を加えた源からの点つき Hom と通常の Hom の自然同型を得た。
さらにその順射を元の余積成分への制限として固定し、逆射を新しい基点で定数となる延長で構成した。
両逆関係と源・標的の自然性は、tensor した余積の二成分での計算で実証した。

自由基点を加えた重みを源として、点つき閉モノイダル圏の enriched end を構成した。
通常の Kan end との underlying 同型を二変数の図式の自然同型から作り、Kan 性を移した。
内部 Hom と end を交換した後、二重内部 Hom の二つの源を交換すると、係数図式に内部 Hom を施した end との点つき同型になる。
この同型は重み・係数に Kan 性を要求しない通常の圏の同型であり、loop と end の交換に使用する。

| 主要宣言 | 内容 |
| --- | --- |
| `EndInternalHom.iso` | 閉モノイダル圏の内部 Hom と end の実際の同型 |
| `EndRightAdjoint.iso` | 一般の右随伴と end の実際の同型 |
| `FreePointedHom.natIso` | 自由基点の Hom を二つの随伴の比較で同定する自然同型 |
| `FreePointedHomRestriction.restrict` / `extend` / `iso` | 元の成分への制限と基点での定数延長の具体的な同型 |
| `FreePointedHomRestriction.natural_pre` / `natural_post` | 具体的な比較の両変数の自然性 |
| `PointedWeightedEnd.obj` / `underlyingDiagramIso` / `underlyingIso` / `kanComplex` | 点つき enriched end と underlying Kan end の比較 |
| `PointedWeightedEnd.cotensorDiagramIso` / `cotensorIso` | 点つき内部 Hom・loop と end の交換同型 |

参照：HA §1.4.2、BF 1978 §2、Kerodon 7.5.4.6。
保存単位の対象ビルド 3638 jobs 成功。
私有宣言を含む 280 モジュール 3194 宣言で標準三公理のみ。
L9e は進行中。次は点つき end の係数への作用と π_* 同型保存を整え、Ω 条件を証明して BF 対象へ束ねる。
有理 Shapiro と通常の Tot との比較は引き続き未完了。

## 82. L9e の hG・homotopy Tot の Kan Ω 列と実際の BF 対象

点つき enriched end の係数への作用を各射影の後合成から実際に構成した。
underlying Kan end との比較同型の射影式と自然性を示し、全基点 π_* 同型の保存を点つき模型へ移した。

Kan 列の図式の各段で点つき Bousfield–Kan end を取り、元の随伴構造射の自然変換を end に送った。
loop と end の交換同型の逆を合成して随伴構造射を作り、uncurry して実際の Kan 列の構造射を定義した。
各対象の Ω 条件は end の全基点 π_* 同型保存で移り、交換同型との合成も同型である。
したがって各段の end は Kan Ω 列になり、単射置換を最後に一度施して BF 対象へ束ねられる。
置換の標準比較は各段で零次数を含む全基点の π_* 同型である。

実際の群作用図式へ適用して homotopy fixed points の BF 対象を構成した。
同様に余単体 BF 図式から homotopy totalization の BF 対象を構成した。
BF 対象の構成に群の有限性は不要である。
通常の Reedy Tot との比較、有理自明作用の実際の標準射と π_* 同型性はまだ主張しない。

補助の enriched インスタンスには全て固有名を付け、同じ namespace の複数モジュールを一緒に import しても名前が衝突しないようにした。
この修正は自レーン内の補助宣言だけであり、借用先を編集していない。

| 主要宣言 | 内容 |
| --- | --- |
| `PointedWeightedEnd.map` / `map_π` | 係数の自然変換が誘導する実際の点つき end 射 |
| `PointedWeightedEnd.underlyingIso_π` / `underlyingIso_natural` | underlying Kan end との射影式と自然性 |
| `PointedWeightedEnd.map_piIsomorphism` | 点つき enriched end による全基点 π_* 同型保存 |
| `KanSequence.homotopyLimitAdjoint` / `homotopyLimit` / `homotopyLimit_omegaCondition` | 段ごとの end の実際の Kan Ω 列 |
| `KanSequence.homotopyLimitSpectrum` / `homotopyLimitProjection_levelwise` | BF 置換と各段の同型比較 |
| `OmegaSpectrum.homotopyLimit` | BF 図式から段ごとの Kan end によって得る実際の BF 対象 |
| `homotopyFixedPointsKan` / `homotopyFixedPoints` | 群作用の hG の Kan 列と BF 対象 |
| `homotopyFixedPointsProjection` / `homotopyFixedPointsProjection_levelwise` | hG の置換前の列への実際の比較と各段の同型性 |
| `homotopyTotalization` | 余単体 BF 図式の homotopy Tot の実際の BF 対象 |

参照：HA §1.4.2、BF 1978 §2、HTT A.3.3、Kerodon 7.5.4.6。
保存単位の対象ビルド 3641 jobs 成功。
私有宣言を含む 283 モジュール 3230 宣言で標準三公理のみ。
L9e は進行中。次は厳密な錐から end への比較を構成し、自明作用から hG への標準射を BF 射にする。
有理 Shapiro と通常の Tot との比較は引き続き未完了。

## 83. L9e の自明作用から hG への実際の標準射

自由基点を加えた重みを smash の単位へ潰し、各対象の元を重み全体で定数な族へ送る点つき射を構成した。
標的と重みの源に関する自然性を示し、任意の厳密な点つき錐から enriched end への標準比較を得た。
この比較は極限錐の仮定を必要としない。

二重内部 Hom の単位での整合性を二重 uncurry と単位子の計算で示した。
これにより定数族は loop の交換と整合し、end への標準比較は内部 Hom と係数の双方に自然となる。
Kan 列の錐を各段で評価して end へ送り、随伴構造射との可換性から厳密な Kan 列の射に束ねた。

BF 図式の厳密な錐では、その始域の単射構造射を使い、比較を標的の BF 置換へ持ち上げた。
自明作用の図式は元の X を頂点とする厳密な定数錐を持つ。
その錐を使い、元の X から (自明 G 作用の X)^{hG} への実際の BF 射を構成した。
比較を置換前へ射影すると、Kan end の定数族の標準比較そのものになる。
射の構成には有限性・有理性を仮定していない。
有限群・有理係数での π_* 同型性は後続で証明する。

| 主要宣言 | 内容 |
| --- | --- |
| `InternalHomExchange.natural_unit_inv` | 二つの内部 Hom の交換と単位の逆同型の整合性 |
| `PointedWeightedEnd.constantFamily` / `constantFamily_pre` / `constantFamily_post` | 重みの変数を忘れた実際の定数族と自然性 |
| `PointedWeightedEnd.coneComparison` / `coneComparison_π` | 厳密な錐から end への標準比較と各射影の式 |
| `PointedWeightedEnd.coneComparison_natural` / `coneComparison_cotensor` | 標準比較と係数・内部 Hom の自然性 |
| `KanSequence.homotopyLimitCone` | 厳密な Kan 列の錐から段ごとの homotopy end への厳密な射 |
| `OmegaSpectrum.homotopyLimitConeComparison` / `homotopyLimitConeComparison_projection` | BF 置換へ持ち上げた標準比較と射影式 |
| `trivialActionCone` | 元の X を頂点とする自明作用図式の実際の厳密な錐 |
| `homotopyFixedPointsUnit` / `homotopyFixedPointsUnit_projection` | 自明作用の hG への実際の標準射と置換前の公式 |

参照：HA §1.4.2、BF 1978 §2、HTT A.3.3、Kerodon 7.5.4.1。
保存単位の対象ビルド 3647 jobs 成功。
私有宣言を含む 289 モジュール 3281 宣言で標準三公理のみ。
L9e は進行中。次は end と Kan 列の射への関手性を整え、有理係数の π_* 比較を進める。
有理 Shapiro と通常の Tot との比較は引き続き未完了。

## 84. L9e の end・hG の射への作用と標準射の自然性

点つき weighted end の恒等射・合成の法則と cotensor 交換の自然性を証明した。
各段へ適用し、図式の自然変換から homotopy limit の Kan 列の厳密な射を構成した。
各対象・各段で全基点 π_* 同型な自然変換は、この Kan 列でも各段の同型を誘導する。

BF 置換の持ち上げを使い、hG と homotopy Tot の間の実際の BF 射を構成した。
置換への射影との可換式を示し、厳密な錐からの標準比較の自然性を各段のホモトピー成分で証明した。
これを全整数次数の π_* の等式へ移した。
特に自明作用の標準射は元のスペクトルの射に自然である。

| 主要宣言 | 内容 |
| --- | --- |
| `PointedWeightedEnd.functor` / `cotensorIso_natural` | end の係数の関手性と loop 交換の自然性 |
| `KanSequence.homotopyLimitMap` / `homotopyLimitMap_levelwise` | Kan 列への実際の射と各段の同型保存 |
| `KanSequence.homotopyLimitMap_id` / `homotopyLimitMap_comp` | 置換前の厳密な関手法則 |
| `KanSequence.homotopyLimitSpectrumMap_piIsomorphism` | BF 置換後の全整数次数の同型保存 |
| `OmegaSpectrum.homotopyLimitMap` / `homotopyLimitMap_projection` | BF 図式の射への作用と置換への射影式 |
| `OmegaSpectrum.homotopyLimitConeComparison_natural` | 錐からの比較の π_* の自然性 |
| `homotopyFixedPointsMap` / `homotopyTotalizationMap` | hG・homotopy Tot の実際の BF 射 |
| `homotopyFixedPointsUnit_natural_component` / `homotopyFixedPointsUnit_natural` | 自明作用の標準射の自然性 |

参照：HA §1.4.2、BF 1978 §2、HTT A.3.3。
保存単位の対象ビルド 3652 jobs 成功。
私有宣言を含む 294 モジュール 3316 宣言で標準三公理のみ。
L9e は進行中。有理 Shapiro と通常の Tot との比較は引き続き未完了。

## 85. L9e の余単体 Kan 複体の実際の Reedy 置換

通常の Tot のため、horn の小対象論法を一般の Reedy 関手的因子分解へ適用した。
simplex 圏は次数ごとにただ一つの対象を持つので、次数の単射性・全射性を具体的に与えられる。
左射は相対 latching anodyne、右射は相対 matching horn RLP である。
この構成は Kan–Quillen モデル構造を仮定しない。

matching と latching での持ち上げ類の閉性から、それぞれの条件は各段にも移る。
終図式への射を実際に因子分解して Reedy 置換関手と自然な単位を得た。
置換の各値は Kan 複体で、単位の各値は anodyne である。
元の各値も Kan なら、単位は零次数を含む全基点 π_* 同型である。

置換の自然な単位で基点を移し、点つき余単体図式の置換関手も構成した。
余単体構造・射・関手法則・単位の自然性はいずれも厳密である。
Reedy 置換だけから通常の Tot の Kan 性や BF 対象との比較を結論していない。
そのためには標準単体の重みと horn の積の相対 latching 条件を続けて証明する。

| 主要宣言 | 内容 |
| --- | --- |
| `CosimplicialHornFactorization.factorization` | 余単体図式の実際の関手的 Reedy horn 因子分解 |
| `CosimplicialHornFactorization.right_app` / `left_app` | 相対条件から各段の horn RLP・anodyne への移送 |
| `CosimplicialKanReplacement.functor` / `unit` | 終図式への因子分解で作る Reedy 置換と自然な比較 |
| `CosimplicialKanReplacement.reedy_terminal_rlp` | 置換の相対 matching の充填条件 |
| `CosimplicialKanReplacement.kanComplex` / `unit_anodyne` / `unit_piIsomorphism` | 各段の Kan 性と比較射の性質 |
| `PointedCosimplicialKanReplacement.obj` / `unitApp` | 点つき余単体図式の実際の置換 |
| `PointedCosimplicialKanReplacement.functor` / `unit` | 点つき置換の関手性と自然な単位 |

参照：Goerss–Jardine VII §4、HTT A.3.3。
保存単位の対象ビルド 3717 jobs 成功。
私有宣言を含む 298 モジュール 3362 宣言で標準三公理のみ。
L9e は進行中。有理 Shapiro と通常の Tot との比較は引き続き未完了。

## 86. L9e の通常の Tot と Reedy horn 充填

標準単体の余単体図式の latching 射を、境界包含と arrow 圏の同型で同定した。
このため標準単体の全ての latching 射は単射である。
有限単体表示を右 tensor 関手で送ることで、パラメーター付きの境界も実際の境界の tensor と同定した。
この同型のパラメーターの射に関する自然性を各余極限射で証明した。

相対境界の押し出しを比較して、標準単体と任意のパラメーターの射の相対 latching 射を
境界包含との pushout-product と同定した。
従って anodyne なパラメーターの射は Reedy anodyne な余単体射を誘導する。
この計算にモデル圏構造は不要である。

通常の Tot を標準単体から係数への内部 Hom の end として実際に定義した。
射とパラメーター付き自然変換との curry・uncurry の往復公式を証明した。
Reedy fibrant な係数では、パラメーターの horn を Reedy 次数帰納で持ち上げ、
その持ち上げを curry して Tot の horn filler を得た。
従って通常の Tot は Kan であり、Reedy horn RLP な係数の射は Tot 上の Kan fibration を与える。

点つき図式では基点の一定な族を Tot の基点に選ぶ。
係数の自然変換はこの基点を保つので、通常の点つき Tot の実際の関手も得た。
任意の図式を Reedy 置換した後の通常の点つき Tot は Kan 複体である。
既存の Bousfield–Kan end による BF スペクトルとの π_* 比較はまだ結論していない。

原典の番号を実物で確認し、今回の Reedy 構成は Goerss–Jardine VII §4、
通常の Tot は VIII §1（式 (1.1)）に対応させた。
§85 とその実装の参照も同じ番号へ修正した。
原典：<https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/Goerss-Jardine2.pdf>。
これは実証済みの Lean の構成の出典を記すもので、引用を証明の入力に追加するものではない。

| 主要宣言 | 内容 |
| --- | --- |
| `StandardSimplexLatching.boundaryArrowIso` / `mono` | 標準単体の latching 射と境界包含の同定・単射性 |
| `SimplexTensorBoundary.iso` / `iso_natural` | パラメーター付きの境界表示と自然性 |
| `SimplexTensorBoundary.relativeLatchingProductArrowIso` | 相対 latching 射の pushout-product 表示 |
| `SimplexTensorBoundary.map_reedy_anodyne` | anodyne なパラメーターの Reedy anodyne 性 |
| `CosimplicialTotalization.obj` / `lift` / `uncurry` | 通常の Tot の実際の単体集合とパラメーター表示 |
| `CosimplicialTotalization.kanComplex` | Reedy 条件からの Tot の実際の horn 充填 |
| `CosimplicialTotalization.map_fibration` | 相対 matching horn RLP の Kan fibration への移送 |
| `CosimplicialTotalization.functor` | 通常の Tot の係数に関する関手 |
| `PointedTotalization.obj` / `functor` | 点つき Tot の対象と射 |
| `PointedTotalization.replacementObj` / `replacementObj_kanComplex` | Reedy 置換後の通常の Tot の点つき Kan 模型 |

参照：Goerss–Jardine VII §4、VIII §1、HTT A.3.3。
保存単位の対象ビルド 3746 jobs 成功。
私有宣言を含む 305 モジュール 3444 宣言で標準三公理のみ。
L9e は進行中。有理 Shapiro と通常の Tot から BF 模型への比較は引き続き未完了。

## 87. L9e の通常の Tot の相対 Whitehead

二つの境界包含の pushout-product を部分複体の積の和の包含と同定し、単射性を証明した。
このため境界をパラメーターにした標準単体の射は Reedy 単射である。
相対 matching が全ての単射に RLP を持つ係数の射は、通常の Tot 上でも全ての単射に RLP を持つ。
両 Tot が Kan なら、この射は本レーンの全基点 π_* 同型である。

さらに、各段で全基点 π_* 同型な Reedy fibration を扱った。
低次数での相対 matching の単射 RLP を matching 対象へ送り、引き戻しの射にも移す。
その引き戻しの射と元の成分の π_* 同型から、現在の相対 matching 射の π_* 同型を得る。
Kan fibration の相対 Whitehead で現在の次数の単射 RLP が従い、次数帰納が閉じる。
この証明では各段の始域の頂点を明示する。
これは空な始域で全基点条件が空虚になる場合を扱いに混ぜないために必要である。
点つき図式では各基点を使ってこの仮定を満たせる。

従って、各段の全基点 π_* 同型である Reedy fibration は Kan な通常の Tot でも全基点 π_* 同型である。
これは Reedy fibration という相対条件を持つ射についての結果であり、一般の係数同型の保存はまだ結論していない。
次は一般の射を二つの Reedy fibration へ因子分解して比較する。

| 主要宣言 | 内容 |
| --- | --- |
| `SimplexTensorBoundary.productSquareArrowIso` | 同じ二辺から作る pushout-product の arrow 同型 |
| `SimplexTensorBoundary.boundaryMap_reedy_mono` | 境界のパラメーターによる標準単体の Reedy 単射性 |
| `CosimplicialTotalization.map_hasLiftingProperty` | パラメーター付きの持ち上げから Tot の持ち上げへの移送 |
| `CosimplicialTotalization.map_rlp_monomorphisms` | 相対 matching の単射 RLP の Tot による保存 |
| `CosimplicialRelativeWhitehead.matching_rlp_of_levelwise` | 各段の π_* 同型である Reedy fibration の相対 Whitehead |
| `CosimplicialTotalization.map_piIsomorphism_of_reedyFibration` | Reedy fibration の Tot における全基点 π_* 同型保存 |
| `PointedTotalization.map_piIsomorphism_of_reedyFibration` | 基点を参照頂点にした点つき版 |

参照：Goerss–Jardine VII §4、VIII §1。
保存単位の対象ビルド 3750 jobs 成功。
私有宣言を含む 309 モジュール 3461 宣言で標準三公理のみ。
L9e は進行中。有理 Shapiro と通常の Tot から BF 模型への比較は引き続き未完了。

## 88. L9e の通常の Tot の一般のホモトピー不変性

Reedy horn の右類を、相対 latching anodyne の RLP と同定した。
これにより右類は合成で閉じ、Reedy Kan な対象との積からの射影も右類になる。
選択された終対象と各段が終対象の一定図式との間では、終射の Reedy 条件は同値である。

任意の余単体射 f のグラフ (f, id) を horn 因子分解した。
中間図式への比較は各段で anodyne で、始域と終域への二つの射影を持つ。
比較と始域への射影の合成は厳密に恒等射、終域への射影との合成は厳密に f である。
元の両図式が Reedy Kan なら二射影は Reedy fibration で、中間図式も Reedy Kan である。
各段の全基点 π_* 同型の前側の消去を、参照頂点と実際の Whitehead 逆によって証明した。
これを使い、f が各段で同型なら二射影も各段で同型となる。

二射影の Tot 上での相対 Whitehead と厳密な切断の式から、通常の Tot は一般の各段の同型を保つ。
f 自体が Reedy fibration であるという §87 の条件は不要になった。
始域の各段の頂点は引き続き明示し、点つき版では各基点を用いた。

Reedy 置換関手も各段の π_* 同型を保つことを単位の自然性と前側の消去で示した。
このため任意の点つき Kan 図式を Reedy 置換してから通常の Tot を取る関手は、各段の同型を保つ。
元から Reedy Kan な図式では、通常の Tot から置換後の Tot への自然な標準射も π_* 同型である。
これらは通常の Tot の実際の模型についての結果で、Bousfield–Kan end との比較はまだ結論していない。

| 主要宣言 | 内容 |
| --- | --- |
| `CosimplicialHornFibration.right_eq_rlp` / `comp` / `prod_fst` / `prod_snd` | Reedy horn fibration の RLP 表示と閉性 |
| `CosimplicialHornFibration.terminal_iff` | 二つの終図式での Reedy 条件の同値 |
| `KanPiIsomorphism.cancel_left_atVertex` | 参照頂点を明示した全基点 π_* 同型の前側の消去 |
| `CosimplicialTwoProjections.obj` / `inclusion` / `sourceProjection` / `targetProjection` | 実際のグラフの因子分解と二射影 |
| `CosimplicialTwoProjections.sourceProjection_levelwise` / `targetProjection_levelwise` | 二射影の各段の全基点 π_* 同型 |
| `CosimplicialTotalization.map_piIsomorphism` / `PointedTotalization.map_piIsomorphism` | 通常の Tot の一般のホモトピー不変性 |
| `CosimplicialKanReplacement.map_piIsomorphism` | Reedy 置換の各段の同型保存 |
| `PointedTotalization.replacementFunctor` / `replacementMap_piIsomorphism` | 任意の点つき Kan 図式の置換した通常の Tot と同型保存 |
| `PointedTotalization.replacementUnit` / `replacementUnit_piIsomorphism` | Reedy Kan な入力での実際の標準比較の π_* 同型 |

参照：Goerss–Jardine VII §4、VIII §1、Kerodon 4.8.4.1。
保存単位の対象ビルド 3760 jobs 成功。
私有宣言を含む 317 モジュール 3513 宣言で標準三公理のみ。
L9e は進行中。有理 Shapiro と通常の Tot から BF 模型への比較は引き続き未完了。

## 89. L9e の群作用の実際の余単体 cochain 図式

点つき end の重みの射に関する前合成を、end の各射影で実際に構成した。
重みの射の合成は end の射の逆順の合成へ移り、重みの反対圏からの関手になる。
係数の後合成との可換性も各射影で示した。
このため、任意の単体的な重みと点つき係数から余単体 cochain 図式を作れ、係数に関して関手的である。

Mathlib の classifyingSpaceUniversalCover を借り、EG_n = G^(n+1) の自由 G 集合の単体的図式を使った。
各値を離散的な単体集合にして作用図式に移し、AsSmall で一対象圏の宇宙を揃えた。
この単体的な重みから群作用の各スペクトル段の余単体 cochain 図式を実際に得た。
同変な BF 射はこの余単体図式の間の厳密な自然変換を誘導する。
顔・退化の恒等式は通常の関手の法則から成立する。

各次数の G^(n+1) は、左正則作用の G と自明作用の G^n との積に同型である。
Mathlib の斉次・非斉次座標の作用の同型を離散重みへ送り、さらに点つき end の同型へ移した。
これにより cochain の各次数を自由軌道の重みで表示できる。
Kan 性にはこの自由軌道の同変内部 Hom を通常の関数空間と比較する証明が続けて必要である。
この段階では各値の Kan 性、Tot と hG の同型、有理 Shapiro の π_* 同型を主張しない。

| 主要宣言 | 内容 |
| --- | --- |
| `PointedWeightedEnd.preMap` / `preMap_comp` / `weightFunctor` | 重みの前合成と実際の反変関手 |
| `PointedWeightedEnd.map_preMap` | 重みの前合成と係数の後合成の可換性 |
| `weightedCochains` / `weightedCochainsFunctor` | 単体的な重みから作る実際の余単体図式と係数の関手性 |
| `GroupActionCochains.actionWeightFunctor` / `universalCoverWeight` | G 集合の離散重みと EG の単体的重み |
| `GroupActionCochains.level` / `levelFunctor` / `levelMap` | 群作用の各段の余単体 cochain と厳密な同変射への作用 |
| `GroupActionCochains.universalCoverFreeIso` / `cochainFreeIso` | 自由 G × G^n の重みとその end への同型 |

参照：Goerss–Jardine VIII §§1–2、HA §1.4.2。
保存単位の対象ビルド 3766 jobs 成功。
私有宣言を含む 323 モジュール 3546 宣言で標準三公理のみ。
L9e は進行中。有理 Shapiro と通常の Tot から BF 模型への比較は引き続き未完了。

## 90. L9e の自由作用の end の内部 Hom 表示と cochain の各値の Kan 性

自由 G 集合 G × S の重みから作用図式へのパラメーター付き自然変換を扱った。
第一座標が 1 の部分へ制限すると、通常の S とパラメーターとの直積から係数への射になる。
逆にこの族へ第一座標の群作用を施すことで、同変な自然変換を構成した。
図式の自然性を第一座標 1 で評価し、制限と拡張が両逆であることを証明した。
パラメーターの射による前合成との可換性も示した。

end への射の普遍性、同変族の同値、curry の随伴を合成した。
この同値はパラメーターに自然なので、Yoneda の充満忠実性から実際の単体集合の同型を得た。
自由作用の重みを持つ同変 end は、離散的な S から係数への通常の内部 Hom と同型である。
従って係数が Kan ならこの end も Kan である。
忘却と点つき end の比較同型によって、この Kan 性を点つき模型へ移した。

§89 の EG_n の自由軌道の表示へ適用して、群作用の余単体 cochain の各値が Kan であることを証明した。
これは任意の群について成立し、有限性や有理性を使わない。
図式の各値の Kan 性だけから厳密 Tot の Kan 性を結論してはいない。
Tot の Kan 性や hG との比較には、重みの全体の比較または相対 matching の充填が続けて必要である。

| 主要宣言 | 内容 |
| --- | --- |
| `FreeActionFamily.restrict` / `extend` | 第一座標 1 への制限と群作用による同変拡張 |
| `FreeActionFamily.equiv` / `restrict_pre` / `extend_pre` | パラメーター付き同変族の同値と自然性 |
| `FreeActionFamily.homEquiv` / `homEquiv_pre` | 自由作用の end への Hom と内部 Hom への Hom の自然な同値 |
| `FreeActionFamily.endIso` | 自由作用の end と通常の内部 Hom の実際の同型 |
| `FreeActionFamily.end_kanComplex` / `pointedEnd_kanComplex` | 自由作用の end の Kan 性と点つき模型への移送 |
| `GroupActionCochains.level_kanComplex` | 群作用の各スペクトル段・各余単体次数の点つき Kan 性 |

参照：Goerss–Jardine VIII §2、HA §1.4.2。
保存単位の対象ビルド 3771 jobs 成功。
私有宣言を含む 328 モジュール 3569 宣言で標準三公理のみ。
L9e は進行中。有理 Shapiro と通常の Tot から BF 模型への比較は引き続き未完了。

## 91. L9e の自由作用の end と cochain の係数の同型保存

自由軌道への制限は係数の同変射の後合成と可換である。
これを end の Hom の同値へ移し、内部 Hom との比較同型の係数への自然性を証明した。
始域の参照頂点から実際の Whitehead 逆へ移り、通常の内部 Hom の後合成の同値性を使った。
従って自由作用の end は係数の全基点 π_* 同型を保つ。

点つき係数では基点を参照頂点として、この同型保存を忘却比較の自然性で点つき end へ移した。
群の有限性は不要である。
任意の点つき単体集合の群作用について、余単体 cochain の関手を定義した。
これは BF 作用スペクトルの一段を取る場合を含み、loop を施した係数も同じ形で扱える。
各次数の自由軌道への比較は係数の同変射に自然である。
従って点つき Kan 係数の全基点 π_* 同型は、cochain の全ての次数でも全基点 π_* 同型を誘導する。

BF 作用スペクトルの同変射についても指定したスペクトル段の同型保存へ移した。
この結果は各余単体次数の主張であり、Tot への同型保存や hG との比較をこの段階では追加主張しない。

| 主要宣言 | 内容 |
| --- | --- |
| `FreeActionFamily.endIso_natural` | 自由作用の end と内部 Hom の比較の係数への自然性 |
| `FreeActionFamily.endMap_piIsomorphism` | 自由作用の通常の end の全基点 π_* 同型保存 |
| `FreeActionFamily.pointedEndMap_piIsomorphism` | 基点を参照頂点にした点つき自由作用の end の同型保存 |
| `PointedActionCochains.obj` / `functor` / `map` | 任意の点つき作用の実際の cochain 関手 |
| `PointedActionCochains.freeIso` / `freeIso_natural` | 各次数の自由軌道への比較と係数への自然性 |
| `PointedActionCochains.obj_kanComplex` / `map_piIsomorphism` | 各次数の Kan 性と係数の全基点 π_* 同型保存 |
| `GroupActionCochains.levelMap_piIsomorphism` | BF 作用スペクトルの指定段の同型の各 cochain 次数への移送 |

参照：Goerss–Jardine VIII §2、HA §1.4.2、Kerodon 4.8.4.1。
保存単位の対象ビルド 3777 jobs 成功。
私有宣言を含む 334 モジュール 3589 宣言で標準三公理のみ。
L9e は進行中。有理 Shapiro と通常の Tot から BF 模型への比較は引き続き未完了。

## 92. L9e の cochain の余単体 Kan Ω 列

点つき end と内部 Hom の交換が重みの前合成にも自然であることを、各射影で証明した。
これを単体的な重みの cochain 全体の自然同型へ束ね、係数の図式にも自然な同型にした。
作用の係数図式を取る操作と後合成の交換を合成して、作用の cochain と内部 Hom の交換を得た。
比較は余単体図式の実際の同型で、係数の同変射にも自然である。

作用スペクトルの随伴構造射は、群の各元のスペクトル射との随伴可換式によって同変である。
この実際の同変射を cochain へ送り、loop 交換の逆を合成した。
これが一段の cochain から次段の loop への余単体自然変換である。
元の Ω 条件、cochain の係数の同型保存、交換同型から、各余単体成分で全基点 π_* 同型となる。

各余単体次数の各スペクトル段を束ね、随伴構造射を uncurry して Kan 列を作った。
この列は Ω 条件を満たす。
余単体の随伴射の自然性を uncurry し、余単体の射が Kan 列の厳密な構造可換射になることを示した。
従って実際の余単体 Kan Ω 列を得た。
各次数の列は単射構造射の置換で BF 対象へ移せる。
ここでの BF 置換は各対象の構成であり、BF 置換全体の厳密な余単体関手性は主張しない。

| 主要宣言 | 内容 |
| --- | --- |
| `PointedWeightedEnd.cotensorIso_preMap` | end と内部 Hom の交換の重みへの自然性 |
| `WeightedCochains.cotensorIso` / `cotensorNatIso` | 通常の図式の cochain と内部 Hom の交換 |
| `FreeActionFamily.pointedCoefficientsPostIso` | 作用の係数図式と後合成の自然な比較 |
| `PointedActionCochains.cotensorNatIso` / `cotensorIso` / `cotensorIso_natural` | 作用の cochain と loop を含む内部 Hom の自然な交換 |
| `GroupAction.adjointMap` / `adjointMap_piIsomorphism` / `adjointMap_natural` | 元の随伴構造射の同変な形と自然性 |
| `GroupActionCochains.adjointTransformation` / `adjointTransformation_piIsomorphism` | cochain の実際の余単体随伴構造射と全基点 π_* 同型 |
| `GroupActionCochains.sequence` / `sequence_omegaCondition` | 各余単体次数の実際の Kan Ω 列 |
| `GroupActionCochains.diagram` | 厳密な余単体 Kan Ω 列の図式 |
| `GroupActionCochains.spectrum` | 各余単体次数の BF 対象への実際の置換 |

参照：Goerss–Jardine VIII §2、HA §1.4.2、BF 1978 §2。
保存単位の対象ビルド 3784 jobs 成功。
私有宣言を含む 341 モジュール 3634 宣言で標準三公理のみ。
L9e は進行中。有理 Shapiro と通常の Tot から BF 模型への比較は引き続き未完了。

## 93. L9e の群圏の over nerve と EG の重みの比較

宇宙を揃えた一対象群圏の over 圏を、群の元を対象とする codiscrete 圏と比較した。
over の対象は終点への射の群の元で表示され、任意の二対象間の射は除法で一意に定まる。
対象を復元する厳密な等式と平行射の一意性から、両 nerve の実際の同型を得た。
射の宇宙が異なるため、nerve の射は各次数の composable arrows の関手として構成した。

codiscrete nerve の単体を頂点列に移し、EG の完全な単体集合と同定した。
群圏の射の後合成は全座標への左乗法となるため、これは重みの図式の自然同型である。
点つき end の重みに関する反変関手へ送り、hG の BK end と EG の同変 end の厳密な同型を得た。
係数の射への自然性と、任意の厳密な錐からの標準射を保存する等式も証明した。
通常の Tot との同定は次の工程であり、この重みの比較だけから有理 Shapiro を主張しない。

| 主要宣言 | 内容 |
| --- | --- |
| `GroupOverCodiscrete.toCodiscrete` / `fromCodiscrete` | over 圏と群の codiscrete 圏の具体的な比較 |
| `GroupOverCodiscrete.nerveIso` | 両 nerve の実際の同型 |
| `discreteLevels` | 単体集合の図式の各次数の離散化 |
| `GroupActionCochains.universalCoverDiagram` | 完全な EG の作用図式 |
| `GroupActionCochains.universalCoverWeight_eq_discreteLevels` | cochain の離散重みとの厳密な同定 |
| `GroupActionCochains.bousfieldKanUniversalCoverIso` | BK 重みと EG の重みの自然同型 |
| `GroupActionCochains.universalCoverEndIso` / `universalCoverEndIso_natural` | 点つき end の比較と係数への自然性 |
| `PointedWeightedEnd.coneComparison_preMap` | 錐の標準射の重みへの自然性 |
| `GroupActionCochains.coneComparison_universalCoverEndIso` | 比較が錐の標準射を保存する等式 |

参照：Goerss–Jardine VIII §§1–2、HA §1.4.2。
保存単位の対象ビルド 3790 jobs 成功。
私有宣言を含む 346 モジュール 3670 宣言で標準三公理のみ。
L9e は進行中。有理 Shapiro と通常の Tot から BF 模型への比較は引き続き未完了。


## 94. L9e の通常の Tot と完全な重みの end の密度比較

標準単体上の整合するパラメーター付きの族を恒等単体で評価し、単体集合の射へ貼り合わせた。
逆に、射から重みの単体の制限で族を作り、両者が厳密な両逆であることを証明した。
重み・係数・パラメーターへの自然性を示し、共通の添字圏上の図式に束ねた。

各 cochain 次数で end を uncurry すると、この図式上の族を得る。
逆に族を各次数で end へ持ち上げ、二つの添字の自然性を交換することで余単体自然変換を得た。
両逆とパラメーターへの自然性から、Yoneda の完全忠実性によって通常の Tot と完全な重みの end の実際の同型を構成した。
この比較には Kan 条件も Reedy 置換も不要である。

点つき end の忘却の比較が重みの前合成に自然であることも証明し、点つき cochain の基礎図式を通常の cochain と比較した。
これを密度の同型に合成し、点つき Tot と点つき end の基礎単体集合の同型を得た。
EG に適用して群圏の BK 重みの同型を合成し、群 cochain の通常の Tot と hG の BK end の基礎単体集合を同定した。
従って Kan 係数なら、Reedy 置換なしの通常の Tot 自体が Kan である。

この保存単位では比較の基点保存と Ω 構造との整合性はまだ主張しない。
有理 Shapiro の π_* 同型と、一般の余単体 BF 図式の通常の Tot との比較は引き続き未完了。

| 主要宣言 | 内容 |
| --- | --- |
| `SimplexDensity.Family` / `diagonal` / `expand` / `familyEquiv` | 標準単体上の整合する族と射との厳密な両逆 |
| `SimplexDensity.DiagramFamily` / `diagramFamilyEquiv` | 添字圏上の図式に対する密度の同値 |
| `PointedWeightedEnd.underlyingIso_preMap` | 点つき end の忘却の重みへの自然性 |
| `UnderlyingWeightedCochains.pointedUnderlyingIso` | 点つき cochain の忘却の余単体図式の同型 |
| `SimplexDensity.fromCochains` / `toCochains` / `cochainFamilyEquiv` | 二添字の族と cochain への自然変換との同値 |
| `SimplexDensity.totalizationEndHomEquiv` / `totalizationEndHomEquiv_pre` | Tot と完全な重みの end への Hom の自然な同値 |
| `SimplexDensity.totalizationEndIso` | 通常の Tot と完全な重みの end の実際の同型 |
| `SimplexDensity.pointedUnderlyingTotalizationEndIso` | 点つき Tot と end の基礎単体集合の同型 |
| `GroupActionCochains.underlyingTotalizationEndIso` | 群 cochain の通常の Tot と群圏の BK end の基礎の同型 |
| `GroupActionCochains.totalization_kanComplex` | Kan 係数での群 cochain の通常の Tot の Kan 性 |

参照：Goerss–Jardine VIII §1、式 (1.1)、VIII §2、HA §1.4.2。
保存単位の対象ビルド 3801 jobs 成功。
私有宣言を含む 357 モジュール 3770 宣言で標準三公理のみ。
L9e は進行中。Sp の ∞ 極限性は γ3 の後に扱い、ここでは追加主張しない。


## 95. L9e の点つき密度比較と通常の群 Tot の Kan Ω 列

密度の同型が厳密な錐の標準射を保存することを恒等単体での具体的な評価で証明した。
自由基点からの Hom の基点を元の成分へ制限すると基点の定数族になることを示した。
点つき end の忘却の比較の基点も各係数の基点の錐の標準射として計算した。
この式と錐への密度の整合式から、通常の Tot と点つき end の密度比較が基点を保存することを証明した。
従って群 cochain の通常の Tot と群圏の BK end は点つき単体集合として厳密に同型である。

一般の Kan 列について、指定された段の点つき同型を介して随伴構造射を共役する構成を追加した。
この構成は元の列への厳密な比較射を持ち、元の Ω 条件を保つ。
群 cochain の通常の Tot の各段へ BK end の構造をこの構成で移し、実際の Kan Ω 列を得た。
構造射はこの指定した密度の同型による移送で定義する。
先に作った余単体随伴構造射を通常の Tot に直接送る別の定義との一致は、この保存単位では追加主張しない。

単射構造射の置換で通常の Tot の BF 対象を得た。
この BF 対象から hG の Kan end への厳密な比較射は各段で全基点 π_* 同型である。
hG の BF 対象との比較は、この同じ Kan end を介する具体的な zigzag で与えられる。

| 主要宣言 | 内容 |
| --- | --- |
| `SimplexDensity.coneFamily` / `totalizationEndIso_cone` | 錐の標準射に対する密度の整合性 |
| `FreePointedHomRestriction.basepoint_restrict` | 自由基点 Hom の基点の制限の具体式 |
| `PointedWeightedEnd.underlyingIso_basepoint` | end の忘却比較の基点の定数族による表示 |
| `SimplexDensity.pointedTotalizationEndIso` | 通常の Tot と完全な重みの点つき end の同型 |
| `GroupActionCochains.totalizationEndIso` | 群 cochain の通常の Tot と BK end の点つき同型 |
| `KanSequence.changeLevels` / `changeLevelsProjection` / `changeLevels_omegaCondition` | 指定した段の同型による Ω 構造の移送 |
| `GroupActionCochains.totalizationKan` / `totalizationKan_omegaCondition` | 通常の群 cochain Tot の段を持つ実際の Kan Ω 列 |
| `GroupActionCochains.totalizationSpectrum` | 通常の群 Tot の BF 対象 |
| `GroupActionCochains.totalizationSpectrumComparison` / `totalizationSpectrumComparison_levelwise` | hG の Kan end への厳密な比較と各段の π_* 同型 |

参照：Goerss–Jardine VIII §§1–2、BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 3807 jobs 成功。
私有宣言を含む 363 モジュール 3804 宣言で標準三公理のみ。
L9e は進行中。有理 Shapiro と一般の余単体 BF 図式の通常の Tot の比較は引き続き未完了。
Sp の ∞ 極限性と導来写像空間の比較は γ3 の後に扱う。


## 96. L9e の通常の群 Tot の係数への自然性と厳密な関手性

通常の cochain の係数の自然変換を構成し、点つき cochain の忘却比較がこれと可換であることを示した。
密度の族の係数への後合成を図式に束ね、通常の Tot と完全な重みの end の密度比較の係数への自然性を証明した。
点つき cochain と end の忘却比較を合成し、点つき密度の同型も係数に自然であることを確認した。

重みの前合成を係数の end 関手の自然変換に束ねた。
これにより重みから係数関手の圏への反変関手を得た。
この関手に EG の重みの同型を送り、密度の自然同型と関手の段階で合成した。
群の比較の各成分をこの自然同型から取り出す形へ整理した。
各成分を直接展開する証明はカーネルの検証時間上限に達したため、検証時間の設定を変えずに、この関手的な合成へ分解して検証を閉じた。

段の同型による Kan 列の移送の逆比較を作り、移送した列と元の列の厳密な同型を構成した。
同変射の BK end の射をこの同型で共役し、通常の Tot の Kan Ω 列の厳密な射を得た。
その各段は、元の余単体 cochain の射から誘導する通常の Tot の射そのものであると証明した。
従って通常の Tot の列は同変射に関する厳密な関手であり、BK end への厳密な比較も自然である。

| 主要宣言 | 内容 |
| --- | --- |
| `UnderlyingWeightedCochains.map` / `pointedUnderlyingIso_natural` | 通常の cochain の係数の射と点つき忘却比較の自然性 |
| `SimplexDensity.totalizationEndIso_natural` | 通常の密度の係数への自然性 |
| `SimplexDensity.pointedTotalizationEndIso_natural` | 点つき密度の係数への自然性 |
| `PointedWeightedEnd.preTransformation` / `weightToFunctor` | 重みから係数 end 関手の圏への反変関手 |
| `SimplexDensity.pointedTotalizationEndNatIso` | 点つき密度の係数関手の自然同型 |
| `GroupActionCochains.universalCoverEndNatIso` / `totalizationEndNatIso` | 群の二つの比較の関手的な合成 |
| `GroupActionCochains.totalizationEndIso_natural` | 通常の群 Tot と BK end の比較の係数への自然性 |
| `KanSequence.changeLevelsInverse` / `changeLevelsIso` / `changeLevelsMap` | 段の同型による列全体の同型と射の移送 |
| `GroupActionCochains.totalizationKanMap` / `totalizationKanMap_app` | 厳密な Kan 列の射と通常の Tot の射の一致 |
| `GroupActionCochains.totalizationKanFunctor` / `totalizationKanComparison_natural` | 通常の Tot の列の厳密な関手性と BK 比較の自然性 |

参照：Goerss–Jardine VIII §§1–2、HA §1.4.2、BF 1978 §2。
保存単位の対象ビルド 3816 jobs 成功。
私有宣言を含む 372 モジュール 3841 宣言で標準三公理のみ。
L9e は進行中。有理 Shapiro と一般の余単体 BF 図式の通常の Tot の比較は引き続き未完了。


## 97. L9e の各 cochain 次数の正次数 π_* の関数群表示

各次数で集合 S からの関数を取る単体集合を構成した。
評価と族の lift を定義し、各座標でホーンを充填して Kan 性を証明した。
境界定数単体と同じ面添字の RelStruct を座標ごとに束ねた。
これにより、関数複体の正次数ホモトピー群から各座標の群の関数群への評価の準同型が単射となる。
各座標で代表単体を選んで束ねることで全射性も示し、実際の群同型を得た。
添字集合の有限性は不要で、座標ごとに異なる基点も許す。

離散集合を源とする内部 Hom の通常の普遍性を具体的な関数の評価で書いた。
パラメーターへの自然性から Yoneda を使い、この内部 Hom と関数複体の単体集合の同型を得た。
cochain の自由軌道の end の比較にこれを合成し、各次数を Fin n → G 上の関数複体と同定した。
Mathlib の自由軌道の比較は連続する座標の比による非斉次座標を使う。

各 cochain 次数の任意の基点での正次数 π_* は、像の基点での係数の群の関数群と同型である。
さらに自由基点の制限・自由軌道の第一座標での評価・離散内部 Hom の各具体式を使い、標準基点は全ての関数座標で元の係数の標準基点に送られることを示した。
従って標準基点で係数の同じ群の関数群への同型を得た。
この保存単位は次数ごとの計算であり、余単体構造との整合性や Tot の π_* をまだ計算していない。
有理群 cohomology の消滅だけから Shapiro を結論することはしない。

| 主要宣言 | 内容 |
| --- | --- |
| `SimplicialFunctionComplex.obj` / `eval` / `lift` / `kanComplex` | 関数複体の具体的な単体集合と座標ごとの Kan 充填 |
| `SimplicialFunctionComplex.simplex` / `relStruct` | 境界定数単体と関係充填の座標ごとの束ね |
| `SimplicialFunctionComplex.homotopyMap` / `homotopyEquiv` | 正次数 π_* の関数群への評価の準同型と群同型 |
| `DiscreteInternalHom.iso` / `comp_iso` | 離散内部 Hom と関数複体の同型と評価の式 |
| `FreeActionFamily.comp_endIso` | 自由作用の end の比較のパラメーター付きの式 |
| `PointedActionCochains.functionIso` / `homotopyFunctionEquiv` | 各 cochain 次数の関数複体とその正次数 π_* の表示 |
| `PointedActionCochains.functionIso_basepoint` / `functionIso_basepoint_vertex` | 標準基点の座標ごとの保存 |
| `PointedActionCochains.basedHomotopyFunctionEquiv` | 標準基点での正次数 π_* の係数の関数群への同型 |

参照：Goerss–Jardine I §7、VIII §2、Kerodon §3.2.3、HA §1.4.2。
保存単位の対象ビルド 3823 jobs 成功。
私有宣言を含む 379 モジュール 3898 宣言で標準三公理のみ。
L9e は進行中。有理 Shapiro と一般の余単体 BF 図式の通常の Tot の比較は引き続き未完了。


## 98. L9e の非斉次関数 cochain の余単体図式と座標式

自由軌道 G×T から G×S への同変射が関数複体へ誘導する前合成を具体的に定義した。
軌道代表 (1,t) の像の第一成分を係数へ作用させ、第二成分で元の関数を評価する。
同変族の自由拡張と軌道代表への制限が両逆であることから、この式が自由作用の end の前合成と可換であることを証明した。
前合成の恒等・合成法則も示した。

EG の各次数を連続する座標の比の自由軌道へ移し、顔・退化を共役して単体的な自由軌道の図式を作った。
標準 EG との単体的自然同型を構成した。
これに関数の前合成を適用し、非斉次関数複体の実際の余単体図式を得た。
点つき係数の作用では各前合成が座標ごとの基点を保つことを示し、点つき図式へ持ち上げた。

単体的な重みの同型が点つき cochain 全体の同型を誘導する一般的な構成を追加した。
自由軌道の点つき end の関数表示とその重みへの自然性を束ね、元の点つき群 cochain と非斉次関数複体の点つき余単体図式の自然同型を得た。
従って対象ごとの比較だけでなく、全ての顔・退化と基点を保つ比較がある。

さらに任意の単体射の自由軌道の構造射を部分積と隣接座標の比で展開した。
これを関数の前合成へ代入して、係数の群作用を含む余単体構造射の具体式を得た。
この単位は単体集合の余単体図式の比較であり、Tot の π_* の計算をまだ主張しない。

| 主要宣言 | 内容 |
| --- | --- |
| `FreeActionFamily.functionPre` / `functionPre_eval` | 軌道代表の像による関数の前合成の座標式 |
| `FreeActionFamily.functionIso` / `functionIso_pre` | 自由作用の end の関数表示と重みへの自然性 |
| `GroupActionCochains.freeUniversalCover` / `universalCoverFreeNatIso` | 非斉次座標の単体的な自由軌道図式と EG との自然同型 |
| `GroupActionCochains.functionCochains` | 非斉次関数複体の余単体図式 |
| `SimplicialFunctionComplex.pointedObj` | 全座標を元の基点にした点つき関数複体 |
| `FreeActionFamily.pointedFunctionPre` / `pointedFunctionIso` / `pointedFunctionIso_pre` | 基点を保つ自由軌道の関数表示と自然性 |
| `WeightedCochains.weightIso` | 単体的な重みの同型による cochain 図式の同型 |
| `GroupActionCochains.pointedFunctionCochains` / `freeFunctionNatIso` | 点つき非斉次図式と自由軌道 cochain の同型 |
| `PointedActionCochains.functionNatIso` | 元の点つき群 cochain 全体の非斉次関数図式への同型 |
| `GroupActionCochains.freeUniversalCover_map_apply` / `functionCochains_map_apply` | 任意の単体射の部分積と隣接座標の比による具体式 |

参照：Goerss–Jardine VIII §2、HA §1.4.2。
保存単位の対象ビルド 3832 jobs 成功。
私有宣言を含む 388 モジュール 3939 宣言で標準三公理のみ。
L9e は進行中。有理 Shapiro と一般の余単体 BF 図式の通常の Tot の比較は引き続き未完了。


## 99. L9e の cochain の π_* の余単体群の図式の同定

任意の点つき Kan 図式に正次数のホモトピー群を適用する一般的な界面を追加した。
添字圏の filtered 性を要求せず、その対象と射の宇宙も係数から独立にした。
図式の自然変換と同型も群の図式の自然変換と同型へ送る。
これを点つき群 cochain と非斉次関数図式の同型へ適用した。

自由軌道の前合成の評価との可換式を境界定数単体上で計算し、π_* の各関数座標に対する作用の具体式を証明した。
軌道代表の像の群成分が係数のホモトピー群へ誘導する作用と、添字の変更になる。
点つき Kan 係数の正次数 π_* の作用を一対象群圏の図式への π_* の適用で構成した。

一般の群の圏の作用を係数に取り、非斉次関数群の前合成を準同型として定義した。
離散的な単体集合の関数の式から恒等・合成法則を移し、余単体群の図式にした。
関数複体の座標ごとの π_* の同型を、前合成の座標式の自然性で束ねた。
従って群 cochain の正次数 π_* の余単体群は、係数の π_* の作用の非斉次 cochain の図式と自然に同型である。
これは各次数の同型に加えて全ての顔・退化を保持する。

| 主要宣言 | 内容 |
| --- | --- |
| `KanHomotopyGroup.diagram` / `diagramMap` / `diagramIso` | 任意の点つき Kan 図式への正次数 π_* の適用 |
| `PointedActionCochains.homotopyDiagramIso` | cochain の非斉次比較を π_* の余単体群へ送る同型 |
| `SimplicialFunctionComplex.pointedHomotopyEquiv` | 基点を固定した関数複体の π_* の同型 |
| `FreeActionFamily.pointedFunctionPre_homotopy_coordinate` | 自由軌道の前合成の π_* の座標式 |
| `PointedActionCochains.homotopyAction` / `homotopyAction_ρ_apply` | 係数の正次数 π_* の群作用 |
| `GroupCoefficientCochains.pre` / `obj` | 群作用を持つ係数の非斉次関数群の余単体図式 |
| `GroupActionCochains.functionHomotopyNatIso` | 関数複体の π_* と群の非斉次 cochain の自然同型 |
| `PointedActionCochains.homotopyFunctionNatIso` | 元の群 cochain の正次数 π_* の余単体群全体の非斉次比較 |

参照：Goerss–Jardine I §7、VIII §2。
保存単位の対象ビルド 3838 jobs 成功。
私有宣言を含む 394 モジュール 3971 宣言で標準三公理のみ。
L9e は進行中。有理 Shapiro、線形 cochain の cohomology との比較、Tot の π_* の計算、一般の余単体 BF 図式の通常の Tot の比較は引き続き未完了。


## 100. L9e の線形 cochain 複体と群コホモロジーの比較

非斉次関数 cochain の任意の単体射の式を余面へ適用した。
零番目の余面は最初の群元の作用と tail への制限となる。
後続の余面は contractNth による隣接する群元の積の前合成となり、最後の座標を落とす場合も含む。
部分積の右逆と contractNth の補題を使い、これらを実証した。

加群の圏の作用を係数にした線形な非斉次 cochain の余単体図式を構成した。
同じ余面の式を線形写像へ移し、交代余面微分の座標式を計算した。
表現を入力した場合、この微分は Mathlib の inhomogeneousCochains.d と厳密に一致する。
整数の交代符号と係数環の交代符号を照合し、各次数の恒等同型を実際の cochain complex の同型に束ねた。
従って構成した交代余面複体のコホモロジーは標準の群コホモロジーと同型である。

有限群の標数零の体の係数では正次数のコホモロジーが零になる。
零次数は不変部分と同型であり、自明作用なら元の係数と同型である。
これらは代数的な cochain complex の主張であり Tot のホモトピー群をまだ計算していない。

また、二以上の次数のホモトピー群を可換群・加法的可換群の図式として束ねる界面を追加した。
余単体 Kan 図式の高次 π_* の交代余面複体も定義した。
この高次 π_* の加法的複体と線形係数の複体の比較、および Tot への橋渡しは後続の工程である。

| 主要宣言 | 内容 |
| --- | --- |
| `GroupActionCochains.functionCochains_δ_zero` / `functionCochains_δ_succ` | 標準の非斉次群 cochain の余面の式 |
| `LinearGroupCochains.pre` / `obj` | 加群の作用を係数とする線形な余単体 cochain |
| `LinearGroupCochains.coface_zero` / `coface_succ` / `alternating_d_apply` | 線形余面と交代微分の具体式 |
| `LinearGroupCochains.objD_eq_inhomogeneous` | Mathlib の非斉次群 cochain 微分との一致 |
| `LinearGroupCochains.complex` / `inhomogeneousIso` / `cohomologyIso` | 実際の cochain complex の比較と群コホモロジーへの同型 |
| `LinearGroupCochains.positive_cohomology_isZero` | 有限群の標数零の線形 cochain の正次数コホモロジー消滅 |
| `LinearGroupCochains.zeroCohomologyIso` / `zeroCohomologyIsoOfTrivial` | 零次数の不変部分と自明作用の元の係数への比較 |
| `KanHomotopyGroup.commDiagram` / `commDiagramIso` / `additiveDiagram` | 高次 π_* の可換群と加法的図式 |
| `KanHomotopyGroup.cochainComplex` | 余単体 Kan 図式の高次 π_* の交代余面複体 |

参照：Goerss–Jardine I §7、VIII §2。
保存単位の対象ビルド 3847 jobs 成功。
私有宣言を含む 401 モジュール 4012 宣言で標準三公理のみ。
L9e は進行中。有理 Shapiro、π_* の加法的 cochain と線形複体の比較、Tot の π_* の計算、一般の余単体 BF 図式の通常の Tot の比較は引き続き未完了。


## 101. L9e の自明作用の高次 π_* の cochain 計算

自明な点つき Kan 作用が正次数のホモトピー群へ誘導する作用は自明であることを証明した。
非斉次群 cochain の係数変更を関手に束ね、既存の余単体比較を自明係数へ移した。
関数群の Additive と加法群の関数の同型を用い、二以上の次数の π_* の余単体加法群を、指定した加群構造の線形 cochain の忘却と比較した。
交代余面複体と加法的関手の可換同型を構成し、この比較を実際の cochain complex の同型にした。
加群から加法群への忘却がホモロジーを保つ同型を使い、各次数のコホモロジーへ比較を移した。
有限群・標数零の体の指定係数で正次数は零となり、零次数は元の係数と同型である。
係数構造は現段階では入力であり、有理化スペクトルの各段への供給は次の保存単位で行う。
これは Tot の π_* の計算や有理 Shapiro をまだ含まない。

| 主要宣言 | 内容 |
| --- | --- |
| `additiveFunctionEquiv` | 関数群の加法表示と加法群の関数の同型 |
| `GroupCoefficientCochains.functor` | 非斉次群 cochain の係数に関する関手性 |
| `PointedActionCochains.homotopyTrivialIso` | 自明作用が誘導する π_* の作用の自明性 |
| `PointedActionCochains.trivialHomotopyFunctionNatIso` | 自明係数の非斉次 cochain への比較 |
| `TrivialHomotopyCochains.linearDiagramIso` | 高次 π_* の加法的図式と指定線形係数の比較 |
| `alternatingCofaceFunctorIso` | 交代余面複体と加法的関手の可換同型 |
| `TrivialHomotopyCochains.complexIso` / `cohomologyIso` | 実際の複体とそのコホモロジーの比較 |
| `TrivialHomotopyCochains.zeroCohomologyIso` | 自明作用の零次数 cohomology は元の係数 |
| `TrivialHomotopyCochains.positive_cohomology_isZero` | 有限群・標数零係数での正次数消滅 |

参照：Goerss–Jardine I §7、VIII §2。
対象ビルド 3854 jobs 成功。私有宣言を含む 408 モジュール 4069 宣言で標準三公理のみ。
L9e は進行中。有理 Shapiro、Tot の π_* の計算、一般の余単体 BF 図式の通常の Tot の比較は引き続き未完了。


## 102. L9e の実際の有理化スペクトルへの係数構造

有理化対象の全整数次数の安定群のテンソル積表示を対称同型で ℚ が左因子の表示へ移した。
この加法同型から ℚ 加群構造を移し、実際の有理化対象の π_* が有理係数を持つことを構成した。
任意段表示を安定次数 q+2-k に適用し、各段の実際のホモトピー次数 q+2 の群にもこの構造を移した。
従って各段の自明群 cochain の高次 π_* の複体について、係数構造を追加で仮定せずにコホモロジーを計算できる。
群の宇宙に合わせた ULift ℚ の作用を使い、大きい群の場合にも同じ宣言を適用する。
有限群なら正次数が消滅し、零次数は元の各段の係数となる。
Tot の π_* へ移すための塔の解析と収束の証明はまだ含まない。

| 主要宣言 | 内容 |
| --- | --- |
| `OmegaSpectrum.rationalizationAddEquiv` / `rationalizationLinearEquiv` | 有理化の群の ℚ が左因子のテンソル積表示 |
| `OmegaSpectrum.rationalizationHomotopyModule` | 有理化の全整数次数の群の ℚ 加群構造 |
| `OmegaSpectrum.positiveLevelStableEquiv` | 段 k の次数 q+2 の群と安定次数 q+2-k の群の比較 |
| `OmegaSpectrum.rationalizationLevelModule` | 有理化の各段の高次群の ℚ 加群構造 |
| `RationalLevelCochains.zeroCohomologyIso` | 有理化各段の自明 cochain の零次数の計算 |
| `RationalLevelCochains.positive_cohomology_isZero` | 有限群に対する正次数の消滅、係数構造の追加仮定なし |

参照：BF 1978 §2、HA §1.4.2、Goerss–Jardine VIII §2。
対象ビルド 3857 jobs 成功。私有宣言を含む 410 モジュール 4092 宣言で標準三公理のみ。
L9e は進行中。有理 Shapiro、Tot の π_* の計算、一般の余単体 BF 図式の通常の Tot の比較は引き続き未完了。


## 103. L9e の骨格の end の塔と厳密な極限

単体集合の射は次元 n 未満の骨格を同じ段の骨格へ写すことを生成単体の像から証明した。
骨格を関手に束ね、段に関する包含と元の対象への包含の自然性を与えた。
通常の n 骨格には Mathlib の skeleton (n+1) を使う。
重みの骨格の増加図式を点つき end の反変関手へ送り、塔と全体からの標準錐を構成した。
部分複体の上限の余極限から、重みの全体が有限骨格の図式の通常の余極限であることを証明した。

二変数図式の end 関手が通常の極限を保つことを、各成分の極限の持ち上げと end の整合式で実証した。
自由基点の左随伴性、反変な内部 Hom の極限保存、end の極限保存を組み合わせた。
これにより点つき重み付き end は重みの余極限を通常の極限へ送る。
従って全体の end から有限骨格の end の塔への標準錐は極限錐である。
この同型を Bousfield–Kan 重みと Kan 列の段へ適用し、実際の homotopy end の各段を復元した。

これらは厳密な通常の極限の結果である。
骨格の塔の段の Kan 性、遷移の fibration 性、π_* の計算と収束はこの保存単位ではまだ証明していない。
自明作用の場合は定値 weighted nerve と直積の同型を使って nerve からの写像空間へ移す工程を続ける。

| 主要宣言 | 内容 |
| --- | --- |
| `SkeletonFiltration.image_le` / `map` / `functor` | 骨格の射への関手性 |
| `SkeletonFiltration.inclusion` / `transition` | 骨格の段の包含と全体への自然変換 |
| `SkeletalWeightedEnd.weightDiagram` / `tower` / `cone` | 有限骨格の重みと点つき end の塔 |
| `SkeletalWeightedEnd.weightCoconeIsColimit` | 有限骨格の重みの余極限は元の重み |
| `EndLimitPreservation.isLimit` / `preservesLimit` | end 関手の通常の極限保存 |
| `PointedWeightedEnd.weightFunctor_preservesLimit` | 重みの余極限からの end の極限保存 |
| `SkeletalWeightedEnd.coneIsLimit` / `limitIso` | 全体の end と骨格の塔の厳密な極限の同型 |
| `KanSequence.homotopyEndLevelTower` / `homotopyEndLevelLimitIso` | 実際の Kan homotopy end の各段への適用 |

参照：Goerss–Jardine VIII §1、BF 1978 §2。
対象ビルド 3864 jobs 成功。私有宣言を含む 417 モジュール 4168 宣言で標準三公理のみ。
L9e は進行中。有理 Shapiro、Tot の π_* の計算、一般の余単体 BF 図式の通常の Tot の比較は引き続き未完了。


## 104. L9e の自明作用の写像空間表示と BG の Kan 塔

定値係数の weighted nerve と底の nerve と係数の直積が厳密に同型であることを証明した。
構成済みの直積からの射と最後の係数の評価を互いに逆とし、自然性で各初区間を最後の成分から復元した。
直積射影の切断空間と内部 Hom の同型を、切断の普遍性と curry の往復則で構成した。
これらを Bousfield–Kan end の切断表示へ合成し、定値図式の end を底の nerve からの写像空間と同定した。
同型の普遍評価の式と、定値図式への任意の一定の脚の錐の標準比較が定数族となる式も証明した。
特に基点の錐を適用することで、点つき定値 end の同型を得た。

自明な BF スペクトルの作用に適用し、置換前の hG の段 k は BG から X_k への定数基点つき写像空間となる。
BG は宇宙をそろえた AsSmall の一対象群圏の nerve を使う。
骨格からの写像空間の塔を実際に構成し、係数が Kan なら各段が Kan、各遷移が Kan fibration であることを指数版 pushout-product から証明した。
全体の写像空間から各段への制限も Kan fibration である。
定数基点が前合成で保存されることを示して点つき塔へ戻し、通常の極限による復元も証明した。
従って実際の自明作用の hG の各段は、この BG の骨格の点つき Kan 塔の極限と同型である。

これは群の有限性と有理性を使わない模型の表示である。
各 fiber の π_* と群 cochain の比較、微分の計算、塔の π_* の収束をまだ含まない。
有理 Shapiro の比較が π_* 同型であるという結論はまだ主張しない。

| 主要宣言 | 内容 |
| --- | --- |
| `constantWeightedNerveIso` | 定値 weighted nerve と底との直積の同型 |
| `productSectionsIso` | 直積射影の切断空間と内部 Hom の同型 |
| `constantHomotopyEndIso` / `constantHomotopyEndIso_uncurry` | 定値 end の写像空間表示と実際の評価式 |
| `constantHomotopyEndIso_cone` | 定値図式の標準比較は写像空間で定数族 |
| `constantPointedHomotopyEndIso` | 基点の定数族を保つ点つき end の同型 |
| `trivialFixedPointLevelIso` | 構成済みの自明作用の hG の各段の写像空間表示 |
| `SkeletalMapping.tower` / `map_fibration` / `coneIsLimit` | 骨格の Kan 写像空間の塔と通常の極限 |
| `UnbasedPointedMapping.tower` / `tower_map_fibration` / `coneIsLimit` | 定数基点の点つき Kan 塔と復元 |
| `trivialFixedPointLevelTower` / `trivialFixedPointLevelTower_fibration` | 自明作用の hG の実際の Kan fibration の塔 |
| `trivialFixedPointLevelLimitIso` | 置換前の hG の各段と BG の骨格の塔の極限の同型 |

参照：Goerss–Jardine I §7、VIII §§1–2、BF 1978 §2、Kerodon §§3.1.3・5.3.3。
対象ビルド 3876 jobs 成功。私有宣言を含む 427 モジュール 4223 宣言で標準三公理のみ。
L9e は進行中。有理 Shapiro、Tot の π_* の計算、一般の余単体 BF 図式の通常の Tot の比較は引き続き未完了。


## 105. L9e の塔の fiber と骨格のセルの相対 cofiber

点つき cofiber からの Hom と制限射の基点 fiber の引き戻しの同型を一般の点つき射に対して証明した。
全空間の基点の像を底とする pointedFiber の模型に移し、包含の単射性で基点保存を検査した。
点つき可換正方形が fiber の射を誘導する構成と、全空間・底の同型による fiber の同型も構成した。
自由基点からの Hom と定数基点の通常の写像空間の同型が前合成に自然であることを束ねた。
これらにより通常の源の射の制限の点つき fiber を、自由基点を加えた相対 cofiber からの Hom と同定した。

骨格の隣接包含に適用し、実際の塔の stageFiber が相対骨格の Hom となる点つき同型を与えた。
正次数の群の同型も、この実際の点つき同型から与えた。
付け加える d セルの添字が d 次元の非退化単体と同値であることを骨格の非所属から証明した。
Mathlib の相対セル分解の二つの段を通常の骨格と同定し、境界包含の余積を貼り付ける pushout を移した。
点つき pushout の対向する cofiber が同型になることを pushout の貼り合わせで証明した。
自由基点追加が保存する骨格の pushout に適用し、相対骨格の cofiber を境界包含の余積の cofiber に移した。
従って塔の各 fiber を、このセルの cofiber からの Hom として表示できる。

個々のセルの cofiber の Hom への積の分解、球面による次数移動、境界準同型の微分との一致と収束は後続の工程である。
正次数の群を相対骨格へ移しただけで、π_r の値を π_(r+d) の係数とまだ同定していない。

| 主要宣言 | 内容 |
| --- | --- |
| `cofiberMappingFiberIso` / `pointedCofiberMappingFiberIso` | 一般の点つき制限の fiber と cofiber の Hom の比較 |
| `PointedFiberComparison.map` / `iso` | 可換正方形の間の fiber の射と同型 |
| `UnbasedPointedMapping.freeHomIso` / `freeHomIso_pre` | 定数基点の写像空間と自由基点の Hom の自然同型 |
| `UnbasedPointedMapping.restrictionFiberIso` | 通常の制限の fiber の相対 cofiber 表示 |
| `UnbasedPointedMapping.stageFiberIso` / `stageFiberHomotopyEquiv` | 骨格の塔の fiber の点つき比較と正次数群の同型 |
| `SkeletalCellAttachment.cellEquiv` | 付け加えるセルと非退化単体の添字の同値 |
| `SkeletalCellAttachment.isPushout` | 実際の骨格のセルの pushout |
| `pointedCofiberPushoutIso` | pushout の対向辺の cofiber の同型 |
| `SkeletalCellAttachment.relativeCofiberIso` / `stageFiberCellIso` | 相対骨格の cofiber とセルの cofiber の比較、fiber への適用 |

参照：Goerss–Jardine I §7、VIII §1。
対象ビルド 3886 jobs 成功。私有宣言を含む 437 モジュール 4294 宣言で標準三公理のみ。
L9e は進行中。有理 Shapiro、Tot の π_* の計算、一般の余単体 BF 図式の通常の Tot の比較は引き続き未完了。


## 106. L9e のセルの Hom の関数複体への分解

点つき cofiber の零合成による降下と商写像での一意性を界面にした。
可換正方形とその同型を cofiber へ送る構成を与えた。
各 cofiber から射の余積の cofiber への包含と cofan の普遍性を実証し、cofiber が任意の小さい余積を保つ同型を構成した。
自由基点追加の余積保存の比較が射の族に自然であることを各包含で照合した。
この正方形を cofiber へ送って、自由基点を加えた境界包含の余積の cofiber を個々の cofiber の余積に移した。

関数複体が定値な族の通常の積であることを座標評価と持ち上げで実証した。
反変の内部 Hom が余積を積へ送る比較を関数複体へ合成し、各座標は各余積包含での制限であることを示した。
その座標式で基点を照合し、点つき余積の Hom と Hom の関数複体の点つき同型を得た。

単体の境界を潰した厳密な cofiber の模型 SimplexCell.sphere を定義した。
骨格のセルの cofiber をこの球面の余積に移し、塔の各 fiber が球面の Hom のセルごとの関数複体となる同型を得た。
関数複体の正次数群の既存の同型を適用し、fiber の正次数群を球面の Hom の正次数群の関数へ移した。
セルの添字は cellEquiv で非退化単体へ移せる。
この保存単位では、球面の Hom の群を元の係数の高い次数へ移す群同型と、塔の微分の計算はまだ含まない。

| 主要宣言 | 内容 |
| --- | --- |
| `pointedCofiberDescOfZero` / `pointedCofiber_hom_ext` | 零合成による降下と商による一意性 |
| `PointedCofiberComparison.map` / `iso` | 可換正方形からの cofiber の射と同型 |
| `PointedCofiberCoproduct.isColimit` / `iso` | 射の余積の cofiber と個々の cofiber の余積の同型 |
| `adjoinCofiberCoproductIso` | 自由基点を加える前の余積との比較 |
| `SimplicialFunctionComplex.fanIsLimit` / `productIso` | 関数複体と定値な族の積の同型 |
| `pointedCoproductHomIso` / `pointedCoproductHomUnderlyingIso_eval` | 点つき余積の Hom の関数複体と座標式 |
| `SimplexCell.sphere` / `SkeletalCellAttachment.cellCoproductIso` | 個々のセルの球面の模型と余積表示 |
| `SkeletalCellAttachment.stageFiberFunctionIso` | 塔の fiber の球面の Hom の関数複体による表示 |
| `SkeletalCellAttachment.stageFiberFunctionHomotopyEquiv` | fiber の正次数群のセルごとの関数表示 |

参照：Goerss–Jardine I §7、VIII §1。
対象ビルド 3895 jobs 成功。私有宣言を含む 445 モジュール 4369 宣言で標準三公理のみ。
L9e は進行中。有理 Shapiro、Tot の π_* の計算、一般の余単体 BF 図式の通常の Tot の比較は引き続き未完了。


## 107. L9e の球面の Hom の群の次数移動

SphereSimplex の成分比較が loop 値の球面の写像類の群演算を保つことを証明した。
loop の積を代表する射の正次数群への作用を二つの射影に分け、球面の射の後合成の自然性で計算した。
従って loop 値の球面の写像類の群と loop の高次ホモトピー群は群同型となる。
円の Kan 置換への制限の全基点 π_* 同型を通常の loop の群の次数移動へ合成した。
これと内部 Hom の交換で、球面の Hom の基本群から係数の高次群への群同型を得た。
さらに loop と内部 Hom の交換を反復し、正次元球面からの Hom のすべての正次数群の次数移動を構成した。

自由基点を加えて作る cofiber と元の射の商の二つの pushout の一意性を比較した。
既存 Spectra から借りるのはこの通常の点つき商の普遍性のみである。
この同型で SimplexCell.sphere を既存の境界を直接潰す球面の模型へ移し、同じ群の次数移動を得た。
骨格の fiber の関数表示へ合成し、セルの添字を非退化単体の型へ移した。
従って n 段の fiber の実際の π_(r+1) は、非退化 (n+1) 単体上の π_(n+r+2)(X) の関数群と同型である。

この保存単位では群の同型そのものを証明した。
係数射についての自然性、塔の境界準同型と交代微分の照合、球面の向きの符号の照合、塔の収束は引き続き必要である。

| 主要宣言 | 内容 |
| --- | --- |
| `LoopMappingClasses.sphereComponentHom` / `sphereComponentEquiv` | loop 値の球面の写像類と loop の高次群の群同型 |
| `CirclePower.positiveHomotopyEquiv` | 円の Kan 置換の Hom の群の次数移動 |
| `SphereSimplex.fundamentalHomotopyEquiv` / `positiveHomotopyEquiv` | 正次元球面の Hom の基本群と全正次数群の次数移動 |
| `adjoinCofiberIso` / `SimplexCell.sphereIso` | 自由基点の商と元の商の比較、セルの球面の標準模型への同型 |
| `SimplexCell.positiveHomotopyEquiv` | セルの球面の Hom の群の次数移動 |
| `SkeletalCellAttachment.stageFiberCoefficientEquiv` | fiber の正次数群と非退化単体上の高次係数の関数群の同型 |

参照：Goerss–Jardine I §7、VIII §1。
対象ビルド 3902 jobs 成功。私有宣言を含む 451 モジュール 4409 宣言で標準三公理のみ。
L9e は進行中。有理 Shapiro、Tot の π_* の計算、一般の余単体 BF 図式の通常の Tot の比較は引き続き未完了。


## 108. L9e の球面とセルの群の係数自然性

全次数の loop の自然性を通常の正次数の群同型へ移した。
円の Kan 置換の単位による前合成が係数射と可換であることを使い、置換した円の次数移動の自然性を得た。
loop 値の球面の写像類の比較、二重 Hom の交換、球面の基本群の比較をそれぞれ係数射と照合した。
球面の正次数群の構成の帰納式を界面にし、loop の逆同型の自然性と交換の正方形を群へ送って帰納した。
従って正次元球面の Hom の全正次数の次数移動は、実際の点つき係数射に自然である。
自由基点から作ったセルの球面についても、球面の比較同型の前合成の自然性を使って同じ可換式を得た。

これは塔の fiber の係数の群の表示へ接続するための自然性である。
塔の境界準同型と交代微分の一致、向きの符号、塔の収束はこの自然性だけでは導かれず、後続で証明する。

| 主要宣言 | 内容 |
| --- | --- |
| `loopPositiveHomotopyEquiv_natural` | loop の正次数の群同型の係数自然性 |
| `CirclePower.positiveHomotopyEquiv_natural` | 円の Kan 置換の Hom の群の係数自然性 |
| `SphereSimplex.fundamentalHomotopyEquiv_natural` | 球面の Hom の基本群の次数移動の自然性 |
| `SphereSimplex.loopSwap_natural` | loop と球面の Hom の交換の係数自然性 |
| `SphereSimplex.positiveHomotopyEquiv_succ` / `positiveHomotopyEquiv_natural` | 正次数の帰納式と全正次数の係数自然性 |
| `SimplexCell.positiveHomotopyEquiv_natural` | セルの球面の Hom の次数移動の係数自然性 |

参照：Goerss–Jardine I §7、VIII §1。
対象ビルド 3908 jobs 成功。私有宣言を含む 457 モジュール 4439 宣言で標準三公理のみ。
L9e は進行中。有理 Shapiro、Tot の π_* の計算、一般の余単体 BF 図式の通常の Tot の比較は引き続き未完了。


## 109. L9e の標準射の定数写像表示と π_* の単射性

自由基点からの定数族を元の成分へ制限すると、通常の内部 Hom の定数族となることを証明した。
点つき錐の end 比較を忘却した射が通常の weighted end の錐の比較と一致することを各射影で照合した。
定値図式の既存の end 比較に合成し、任意の点つきパラメーターからの標準比較を定数写像として同定した。
これを実際の自明作用の標準射の BF 射影の式に適用した。
従って homotopyFixedPointsUnit の各段は、BG の写像空間の表示へ移すと定数写像への標準射である。

単位単体集合からの写像空間の点つき評価同型と、選んだ点への制限を合成して評価射を構成した。
定数射の後の評価が恒等射であることを証明した。
BG の標準頂点で評価することで、実際の BF 標準射の各段に点つき射としての左逆を得た。
この段ごとの左逆がスペクトルの厳密な射であることは必要とせず主張していない。
各段の全正次数群の単射性を、自然な正次数の段表示を通じて全整数次数の π_* の単射性へ移した。
この単射性には群の有限性も係数の有理性も不要である。

有理 Shapiro の残る全射性は、有理係数の正次数の群コホモロジーの消滅だけではまだ得られていない。
塔の微分と cochain 微分の照合、向き、収束を引き続き証明する。

| 主要宣言 | 内容 |
| --- | --- |
| `PointedWeightedEnd.constantFamily_restrict` / `underlyingIso_coneComparison` | 定数族の制限と錐の比較の忘却後の式 |
| `constantPointedHomotopyEndIso_cone` / `constantPointedHomotopyEndIso_unit` | 定値点つき end の標準射の定数写像表示 |
| `homotopyFixedPointsUnit_mapping` | 実際の BF 標準射の BG の写像空間での式 |
| `UnbasedPointedMapping.constant` / `evaluation` / `constant_evaluation` | 定数射と点での評価による厳密な分裂 |
| `trivialFixedPointLevelRetraction` / `homotopyFixedPointsUnit_level_retraction` | BF 標準射の各段の左逆 |
| `homotopyFixedPointsUnit_level_groupMap_injective` | 各段の全正次数群の単射性 |
| `homotopyFixedPointsUnit_homotopyMap_injective` | 全整数次数の安定群の単射性 |

参照：Goerss–Jardine I §7、VIII §2、BF 1978 §2、HA §1.4.2。
対象ビルド 3914 jobs 成功。私有宣言を含む 463 モジュール 4462 宣言で標準三公理のみ。
L9e は進行中。有理 Shapiro の全射性、Tot の π_* の計算、一般の余単体 BF 図式の通常の Tot の比較は引き続き未完了。


## 110. L9e の実際の塔の fiber の微分

L9b の連結準同型を、標準基点での底の群から点つき fiber の群への準同型へ移した。
像の基点への恒等射による移送と ofVertex の基点の等式を明示している。
fiber の包含との合成、元の射の後の合成が自明となることを証明した。
三つの群同型で L9b の各位置の完全性を移し、標準基点での正次数群の完全列を与えた。
追加の完全性や境界射の仮定は導入していない。

点つき Kan fibration の塔の fiber の最初の微分を、前の fiber の包含と次の連結準同型の合成で構成した。
間に現れる連結射の後の包含の零合成から、微分の二乗の零性を証明した。
骨格の写像空間の実際の fibration の塔へ適用し、stageFiber の群の微分を得た。
さらに検証済みのセルの係数表示の群同型で共役し、非退化単体上の高次係数群の微分へ移した。
この群同型が両微分を交換することと、移された微分の二乗が零であることを証明した。

この保存単位の係数微分は実際の幾何的微分から構成されている。
通常の交代 cochain 微分との一致、その向きの符号、塔の収束はまだ含まない。
従って先に得た群 cohomology の消滅をこの微分の cohomology へまだ適用していない。

| 主要宣言 | 内容 |
| --- | --- |
| `pointedFiberGroupEquiv` / `pointedConnectingHom` | 標準基点での fiber の群と連結準同型 |
| `pointedConnectingHom_inclusion` / `pointedConnectingHom_projection` | 点つき長完全列の零合成 |
| `pointed_exact_connecting_fiber` / `pointed_exact_total_base` / `pointed_exact_fiber_total` | 標準基点での三つの位置の完全性 |
| `PointedFibrationTower.differential` / `differential_comp` | fibration の塔の fiber の最初の微分と二乗の零性 |
| `UnbasedPointedMapping.stageDifferential` / `stageDifferential_comp` | 骨格の実際の塔への適用 |
| `SkeletalCellAttachment.coefficientDifferential` / `stageFiberCoefficientEquiv_differential` | セルの係数への移送と群同型による可換式 |
| `SkeletalCellAttachment.coefficientDifferential_comp` | 移された係数微分の二乗の零性 |

参照：Goerss–Jardine I §§7–8、VIII §1。
対象ビルド 3919 jobs 成功。私有宣言を含む 468 モジュール 4492 宣言で標準三公理のみ。
L9e は進行中。有理 Shapiro の全射性、Tot の π_* の計算、一般の余単体 BF 図式の通常の Tot の比較は引き続き未完了。


## 111. L9e の fiber の可換性と有理線形な微分

セルの係数の実際のホモトピー次数は常に二以上である。
係数の関数群の可換性と fiber の群同型の単射性から、骨格の fiber の基本群も可換であることを証明した。
既存の群演算を維持して交換則を加えている。
係数の基本群自体が可換であることは仮定せず、一般の Kan 係数に対してこの fiber の可換性が成立する。

実際の有理化スペクトルの段の高次ホモトピー群の有理作用を、セルの関数群と fiber の群へ移した。
加法的なタグと関数群の加法の比較同型を使い、telescope 由来の作用を供給している。
加法群の準同型が有理加群の間では自動的に有理線形であることを用い、移された幾何的微分を有理線形写像にした。
二乗の零性も線形な微分の合成の零性として証明した。
係数の有理性や線形性の追加仮定は導入していない。

| 主要宣言 | 内容 |
| --- | --- |
| `SkeletalCellAttachment.coefficientGroupCommGroup` | 二以上の次数のセルの係数の可換性 |
| `SkeletalCellAttachment.stageFiberCommGroup` | fiber の基本群を含む全正次数群の可換性 |
| `SkeletalCellAttachment.rationalCoefficientModule` | 実際の有理化係数の関数群の有理作用 |
| `SkeletalCellAttachment.rationalStageFiberModule` | 実際の骨格の fiber の群の有理作用 |
| `SkeletalCellAttachment.rationalCoefficientDifferential` / `rationalCoefficientDifferential_comp` | 幾何的微分の有理線形な表示と零合成 |

参照：Goerss–Jardine I §7、VIII §1、BF 1978 §2。
対象ビルド 3921 jobs 成功。私有宣言を含む 470 モジュール 4508 宣言で標準三公理のみ。
L9e は進行中。通常の交代 cochain 微分との一致、符号、収束、有理 Shapiro の全射性、通常の Tot の比較は未完了。


## 112. L9e の実際の fiber と係数微分の自然性

参照頂点を明示して fiber の包含と可換な任意の射を扱う L9b の自然性の形を追加した。
これを標準基点の群同型の二つの正方形へ合成し、点つき可換正方形に対する連結準同型の自然性を得た。
隣り合う二つの正方形で fiber 包含の式を合成し、点つき fibration の塔の最初の微分の自然性を証明した。
通常の写像空間の後合成の点つき関手と骨格の塔の実際の射を構成した。
この射から stageFiberMap を作り、実際の骨格の微分がこれと可換であることを検証した。

cofiber の Hom の fiber 表示の包含後の式を界面にし、係数射との自然性を包含の一意性で証明した。
自由基点の Hom の比較の後合成自然性と合わせ、相対骨格の cofiber とセルの cofiber の Hom の比較を係数射と照合した。
関数複体の後合成と点つき座標評価を構成し、その群の座標表示が係数射に自然であることを証明した。
余積の Hom の関数表示の各座標は包含への前合成なので、同じ自然性が成り立つ。
これらを合成して stageFiberFunctionIso および正次数の関数群の表示の自然性を得た。

先に検証したセルの球面の次数移動の自然性を各非退化単体へ適用した。
従って実際の stageFiberMap の群の射は、高次係数の関数表示で元の係数射の π_* を座標ごとに施す射と一致する。
群同型の逆の可換式と実際の微分の自然性を合成し、coefficientDifferential の係数自然性も証明した。
ここまでで、幾何的微分とその係数表示・射がすべて自然に接続されている。
通常の交代微分の具体式との一致と向きの符号、塔の収束は引き続き後続の課題である。

| 主要宣言 | 内容 |
| --- | --- |
| `FibrationSquare.connectingHomOver_natural` / `pointedConnectingHom_natural` | 指定参照頂点の fiber と標準基点の連結準同型の自然性 |
| `PointedFibrationTower.differential_natural` | 塔の射に対する幾何的微分の自然性 |
| `UnbasedPointedMapping.towerPost` / `stageFiberMap` / `stageDifferential_natural` | 骨格の実際の塔の係数射と微分の可換式 |
| `pointedCofiberMappingFiberIso_natural` / `UnbasedPointedMapping.restrictionFiberIso_natural` | cofiber 表示と通常の制限の fiber の係数自然性 |
| `SimplicialFunctionComplex.pointedPost` / `pointedHomotopyEquiv_natural` | 関数複体の後合成と正次数群の座標表示の自然性 |
| `pointedCoproductHomIso_natural` / `SkeletalCellAttachment.stageFiberFunctionIso_natural` | 余積の Hom と実際の fiber の関数表示の自然性 |
| `SkeletalCellAttachment.stageFiberCoefficientEquiv_natural` | 非退化単体上の高次係数表示の自然性 |
| `SkeletalCellAttachment.coefficientDifferential_natural` | 移された実際の微分の座標ごとの係数射への自然性 |

参照：Goerss–Jardine I §§7–8、VIII §1。
対象ビルド 3934 jobs 成功。私有宣言を含む 483 モジュール 4563 宣言で標準三公理のみ。
L9e は進行中。通常の交代 cochain 微分との一致、符号、収束、有理 Shapiro の全射性、通常の Tot の比較は未完了。


## 113. L9e の比較先の通常の正規化 cochain

Mathlib の normalizedChainComplex と、各鎖群が非退化単体を添字とする余積である普遍性を借りた。
この既存の通常の鎖複体を前加法圏の係数への Hom に送り、正規化 cochain 微分を構成した。
余積の生成子への制限と延長が加法同型であることを証明し、非退化単体上の係数の関数群へ微分を移した。
任意の単体への生成子の射は退化単体で零となるため、関数の表示では退化面を零とする延長になる。
Mathlib の正規化鎖の生成子の微分式を適用し、移された微分が面の交代和である明示式を得た。
微分の二乗の零性は、通常の鎖複体の零合成から共役により移した。

二つの加法群の族を cochain 複体に束ね、Hom の複体と関数の複体の同型を構成した。
係数の Hom の後合成を各非退化単体で施す射と、その延長の可換性を証明した。
この射と通常の微分の自然性を検証し、cochain 複体の係数射を与えた。
H_* の理論や定理を所有範囲に追加するものではなく、正規化 cochain の比較先として Mathlib の鎖複体を借りるだけである。

この通常の交代微分と、実際の骨格の幾何的微分から移した coefficientDifferential はまだ別の構成である。
両者が一致することと球面の向きの符号は引き続き証明が必要である。

| 主要宣言 | 内容 |
| --- | --- |
| `NormalizedSimplicialCochains.extend` / `coefficientEquiv` | 正規化鎖群の Hom と非退化単体上の関数の加法同型 |
| `NormalizedSimplicialCochains.zeroExtend` / `inclusion_extend_all` | 退化単体で零となる全単体上の表示 |
| `NormalizedSimplicialCochains.differential_apply` / `differential_comp` | 通常の交代面の和の式と二乗の零性 |
| `NormalizedSimplicialCochains.homComplex` / `complex` / `complexIso` | Hom の複体と関数の複体の同型 |
| `NormalizedSimplicialCochains.post` / `differential_natural` / `complexMap` | 係数の後合成と通常の微分の自然性 |

参照：Goerss–Jardine III §2、VIII §1。Mathlib SimplicialSet/Homology/Nondegenerate の通常の構成を借用。
対象ビルド 3954 jobs 成功。私有宣言を含む 486 モジュール 4598 宣言で標準三公理のみ。
L9e は進行中。幾何的微分と交代微分との一致、符号、収束、有理 Shapiro の全射性、通常の Tot の比較は未完了。


## 114. L9e の係数の元を値とする cochain と正規化のホモトピー比較

Mathlib の ULift ℤ から係数群への射を一の像に送る加法同型を各座標へ適用した。
これにより正規化 cochain を係数の元を値とする関数群へ移し、退化面を零とする交代和の式と二乗の零性を証明した。
この群の族を複体へ束ね、Hom 係数の正規化 cochain からの複体同型を与えた。

通常の鎖複体の反対を加法的 Yoneda へ送る反変 Hom の cochain 関手を構成した。
鎖ホモトピー同値の順逆を交換して反対を取る構成と、加法関手のホモトピー保存を合成した。
従って係数が入射的であることを仮定せず、通常の鎖ホモトピー同値がこの cochain のホモトピー同値を与える。
Mathlib の通常の正規化鎖のホモトピー同値に適用し、生成子の二つの複体同型へ合成した。
これにより通常の全単体の整数鎖からの Hom の cochain と、非退化単体上の係数の元を値とする cochain はホモトピー同値である。
借用した鎖のホモトピー同値を cochain の比較へ使うだけであり、H_* の結果は追加していない。

群 cohomology の計算に接続するには、全単体の Hom の cochain を BG の通常の非正規化群 cochain と同定する必要が残る。
幾何的な骨格の微分との比較と収束も引き続き未完了。

| 主要宣言 | 内容 |
| --- | --- |
| `NormalizedValueCochains.coefficientEquiv` / `differential_apply` | 係数の元を値とする表示と退化面を零とする交代式 |
| `NormalizedValueCochains.complex` / `complexIso` | 通常の係数の正規化複体と Hom 係数からの同型 |
| `ContravariantChainHom.obj` / `map` / `homotopyEquiv` | 反変 Hom の cochain と鎖ホモトピー同値の保存 |
| `NormalizedSimplicialCochains.homComplexComparison` / `normalizationHomotopyEquiv` | 正規化の Hom の複体への比較と通常の鎖からの同値 |
| `NormalizedValueCochains.normalizationHomotopyEquiv` | 全単体の鎖の Hom と係数の元を値とする正規化 cochain のホモトピー同値 |

参照：Goerss–Jardine III §2、VIII §1。
対象ビルド 3958 jobs 成功。私有宣言を含む 490 モジュール 4629 宣言で標準三公理のみ。
L9e は進行中。幾何的微分と交代微分との一致、符号、収束、有理 Shapiro の全射性、通常の Tot の比較は未完了。


## 115. L9e の全単体の交代 cochain と正規化の同値

全単体上の Hom 係数の関数群を余単体図式にした。
面と退化の射は単体集合の作用への前合成であり、全ての functor の法則を検証している。
その通常の交代余面複体の微分を、全単体の各面に係数を評価する交代和として明示した。
全単体の鎖群の余積の普遍性で、通常の鎖の Hom と全単体上の関数群の加法同型を得た。
鎖の生成子の交代微分式により、この同型は反変 Hom の cochain と通常の交代余面複体の複体同型となる。

ULift ℤ からの射の係数表示を全単体の余単体図式へ適用した。
各座標で一の像を取る式が全ての面と退化の前合成と可換なので、余単体図式の自然同型を得た。
交代余面複体関手に送り、通常の係数の元を値とする全単体の cochain への複体同型を与えた。
この同型と既存の正規化の鎖ホモトピー同値の比較を合成した。
従って全単体上の通常の係数値の交代 cochain と、非退化単体上の正規化 cochain は通常の複体としてホモトピー同値である。

この時点では単体集合は任意であり、BG の全単体の図式と非斉次群 cochain の比較は次に行う。
幾何的微分からの交代式の計算および塔の収束は引き続き未完了。

| 主要宣言 | 内容 |
| --- | --- |
| `SimplicialHomCochains.coefficientEquiv` / `diagram` | 全単体の鎖の Hom の関数表示と余単体図式 |
| `SimplicialHomCochains.differential_apply` / `homComplexComparison` | 全単体の交代式と鎖の Hom の複体との同型 |
| `SimplicialHomCochains.normalizationHomotopyEquiv` | Hom 係数の通常の交代複体と正規化複体のホモトピー同値 |
| `SimplicialValueCochains.diagramIso` / `complexIso` | 整数の Hom 係数から元の係数への余単体自然同型と複体同型 |
| `SimplicialValueCochains.normalizationHomotopyEquiv` | 通常の係数値の全単体 cochain と正規化 cochain のホモトピー同値 |

参照：Goerss–Jardine III §2、VIII §2。
対象ビルド 3961 jobs 成功。私有宣言を含む 493 モジュール 4664 宣言で標準三公理のみ。
L9e は進行中。BG の非斉次群 cochain の比較、幾何的微分と交代微分との一致、符号、収束、有理 Shapiro の全射性、通常の Tot の比較は未完了。


## 116. L9e の BG の正規化 cochain の有理消滅

AsSmall した一対象群圏の nerve の単体を、隣接射の逆元の列へ送る同値を構成した。
SingleObj の合成は逆順の積なので、この逆元により通常の非斉次群 cochain の積の順序に合わせている。
隣接射の指定から functor を復元する Mathlib の構成を使い、全対象が一意であることと隣接射の一致で往復則を証明した。
面の頂点を飛ばす式を各隣接辺で計算し、最初の面は Fin.tail、残りの面は Fin.contractNth の積になることを証明した。
飛ばされた頂点を挟む場合は二辺の合成と積の逆元の式を使っている。

全単体上の係数の元の cochain の微分を最初の面と残りの面に分けた。
群座標での加法同型がこの微分と、自明係数の非斉次群 cochain の微分を交換することを証明した。
これにより BG の通常の全単体の cochain と、加法群へ忘却した線形群 cochain の実際の複体同型を得た。
正規化のホモトピー同値、群座標の複体同型、忘却の homology 比較を合成した。
その結果 BG の非退化単体上の正規化 cochain の cohomology は自明係数の群 cochain の cohomology と同型となる。
零次数は元の係数に同型であり、有限群の標数零の体の係数では正次数は零である。

実際の有理化スペクトルの各段の高次群の有理作用を入力し、正規化された BG の cochain に対する零次数の表示と正次数の消滅を得た。
この正規化 cochain は通常の交代微分で定義されている。
骨格の幾何的微分から移した coefficientDifferential と同定したわけではなく、その式と符号の照合は引き続き必要である。
塔の収束と有理 Shapiro の全射性もまだ未証明。

| 主要宣言 | 内容 |
| --- | --- |
| `GroupNerve.coordinatesEquiv` | BG の全単体と非斉次群座標の同値 |
| `GroupNerve.coordinates_face_zero` / `coordinates_face_succ` | 面が tail と contraction になる式 |
| `GroupNerve.linearComplexIso` | BG の全単体の cochain と自明係数の線形群 cochain の複体同型 |
| `GroupNerve.normalizedCohomologyIso` / `normalizedZeroCohomologyIso` | BG の正規化 cochain の群 cohomology による表示と零次数 |
| `GroupNerve.normalized_positive_cohomology_isZero` | 有限群と標数零の体で正規化 cochain の正次数が消滅 |
| `RationalLevelNormalizedCochains.zeroCohomologyIso` / `positive_cohomology_isZero` | 実際の有理化各段の高次群係数での正規化 cochain の計算 |

参照：Goerss–Jardine III §2、VIII §2、BF 1978 §2。
対象ビルド 3967 jobs 成功。私有宣言を含む 499 モジュール 4718 宣言で標準三公理のみ。
L9e は進行中。幾何的微分と交代微分との一致、符号、収束、有理 Shapiro の全射性、通常の Tot の比較は未完了。


## 117. L9e の球面的境界の交代関係

高次ホモトピー群の積について、最後の面だけでなく任意の面添字の MulStruct が同じ商上の積を計算することを証明した。
最後の添字から逆向きに帰納し、隣接する積の比較ホーンと可換性を使っている。
第二因子と積を指定したとき第一因子を得る外側ホーンの充填も構成した。

全ての面が境界定数単体である単体を SphericalBoundary として記録した。
面 p より前が定数のとき、面 p の逆元の積、元の境界、二つ後ろの面との積、および残りの面の退化を一つ高いホーンへ配置した。
各面を直接計算して互換性を確認し、Kan 充填の欠けた面を取った。
その境界では面 p が定数になり、面 p+2 が元の二面の類の積へ置き換わる。
二つ離れた面の符号は同じなので、この操作はホモトピー類の交代和を保つ。

先頭面を順に消し、最後に残る隣接二面を元の単体が与える RelStruct で比較した。
従って、任意の Kan 複体の二以上の次数の球面的境界ではホモトピー類の交代和が零である。
証明は全て実際のホーン充填による。交代関係を追加公理や未証明の界面として仮定していない。

この関係は幾何的な符号計算の普遍補題であり、骨格の coefficientDifferential の交代微分との一致そのものではない。
その同定、塔の収束、有理 Shapiro の全射性、通常の Tot の比較は引き続き未完了。

| 主要宣言 | 内容 |
| --- | --- |
| `KanHomotopyGroup.mul_eq_at` | 高次の任意の面添字の積の商上の計算 |
| `exists_left_factor` | 第二因子と積を指定した実際の Kan 充填 |
| `SphericalBoundary` | 全ての面が境界定数単体である実際の単体 |
| `SphericalBoundaryReduction.compatible` / `output_face` / `reduce` | 一面を二つ後ろへまとめるホーンとその境界の計算 |
| `SphericalBoundary.alternatingClass_reduce` | 一面の簡約による交代和の保存 |
| `SphericalBoundary.alternatingClass_eq_zero` | 球面的境界のホモトピー類の交代和は零 |

参照：Goerss–Jardine I §7、VIII §1、Kerodon §3.2.3。
対象ビルド 3971 jobs 成功。私有宣言を含む 503 モジュール 4852 宣言で標準三公理のみ。
L9e は進行中。幾何的微分と交代微分との一致、符号の写像空間への適用、収束、有理 Shapiro の全射性、通常の Tot の比較は未完了。


## 118. L9e の交代和による境界充填判定と幾何的 cocycle

最後の面を同じホモトピー類の代表へ変更する比較ホーンを構成した。
元の単体と最後の添字の RelStruct を二面に置き、他の面の退化を並べる。
互換性と欠けた面の全ての面を計算し、最後以外の面を厳密に保持することを証明した。

任意の球面的な面族の最後の面を除くホーンを充填した。
その交代和は零なので、元の族の交代和も零なら、二つの最後の面の加法的な類は同じになる。
共通の先頭部分の和を消し、最後の交代符号が整数の単元であることで類の等式を得ている。
比較ホーンで最後の面を元の指定へ直し、全ての面を持つ単体を実際に構成した。
従って球面的境界の充填の存在とホモトピー類の交代和の零性は同値である。
境界の面の余極限で面族を通常の境界射へ貼り合わせ、その射の全境界充填の同値にも移した。

単体集合の射が次数 n+1 で定数であるとき、次数 n+2 の各単体の像を境界定数単体として読む構成を与えた。
退化単体の像は代表そのものが定数であるため、そのホモトピー類の係数は正規化 cochain を与える。
次数 n+3 の単体の実際の像に交代境界関係を適用し、この通常の正規化 cochain の微分が零であることを証明した。
これで実際の単体的な射から交代微分の cocycle 条件を得た。
まだ骨格からの部分的な射の延長障害や coefficientDifferential の式そのものを同定したわけではない。

| 主要宣言 | 内容 |
| --- | --- |
| `SimplexFaces.rel_face` | RelStruct の全ての面の式 |
| `SphericalBoundaryLastFace.replace` / `exists_replace` | 最後以外の面を保持する代表の変更 |
| `SphericalBoundary.exists_horn_boundary` | 最後の面を変更した族の Kan 充填 |
| `SphericalBoundary.nonempty_iff_alternatingClass_eq_zero` | 球面的な全境界充填の交代和による判定 |
| `SphericalBoundary.boundaryMap` / `boundary_filler_iff` | 実際の境界射とその充填判定 |
| `SphericalCochain.simplexValue` / `simplexValue_degeneracy` | 低次元で定数の射の代表と退化での定数性 |
| `SphericalCochain.cochain` / `zeroExtend_cochain` / `differential_cochain` | 実際の射からの正規化 cochain と cocycle 関係 |

参照：Goerss–Jardine I §7、III §2、VIII §1、Kerodon §3.2.3。
対象ビルド 3975 jobs 成功。私有宣言を含む 507 モジュール 4916 宣言で標準三公理のみ。
L9e は進行中。骨格の延長障害、幾何的微分との一致、収束、有理 Shapiro の全射性、通常の Tot の比較は未完了。


## 119. L9e の骨格の厳密な延長障害と cochain の実現

通常の n+2 骨格上の射が次数 n+1 で定数のとき、全体 K の次数 n+2 単体を骨格へ持ち上げて正規化 cochain を構成した。
各 n+3 セルの全ての面の像は球面的な面族になる。
退化面の零性と交代式により、このセルの境界の交代和が通常の正規化微分のそのセルでの値と一致する。
従って、一つのセルの境界が充填できることと微分の値が零であることは同値である。

Mathlib の相対セル分解の付着写像と特徴射を元の単体の Yoneda 射へ比較した。
付着境界の各面を骨格内の面の Yoneda 射と同定し、具体的な球面的境界の貼り合わせと付着境界の像を一致させた。
全てのセルの微分が零なら各境界充填を選択し、セルの余積と骨格の pushout に貼り合わせることで次の骨格への実際の射を構成した。
逆に延長を各特徴射に制限すると充填が得られる。
従って、元の骨格上の値を厳密に保つ一段の延長の存在は、係数 cochain が通常の cocycle であることと同値である。

任意の次元 d と各非退化 d 単体に指定した境界定数代表について、それを各セルへ貼って骨格上の射を実現する構成も証明した。
低い骨格では厳密に定数であり、各セルでは指定した代表そのものに一致する。
高次ホモトピー類の商の代表を選ぶことで、任意の係数 cochain を骨格上の射で実現した。
さらに cocycle なら一つ高い骨格まで延長された射で実現できる。

これは通常の骨格の射の延長障害の計算であり、写像空間の正次数群の比較を通して coefficientDifferential 自体の式を証明したわけではない。
その接続、収束、有理 Shapiro の全射性、通常の Tot の比較は引き続き未完了。

| 主要宣言 | 内容 |
| --- | --- |
| `SkeletalSphericalCochain.cochain` / `differential_cochain_apply` | 骨格上の射の正規化 cochain と各セルの交代和の式 |
| `SkeletalSphericalCochain.cell_filler_iff` | 次のセルの充填の通常の微分による判定 |
| `SkeletalCellAttachment.cell_attachingMap_ι` / `cell_characteristicMap_ι` | セル付着の二射と元の単体の比較 |
| `SkeletalSphericalCochain.cell_attaching_boundary` | 付着境界の像と球面的な境界射の一致 |
| `SkeletalSphericalCochain.extension_iff_differential_eq_zero` | 骨格への一段の厳密な延長と cocycle 条件の同値 |
| `SkeletalSphericalRealization.exists_map` | 任意のセル代表の骨格上の射による厳密な実現 |
| `SkeletalSphericalRealization.exists_realization` / `exists_extended_realization` | cochain と cocycle の実際の骨格の射による実現 |

参照：Goerss–Jardine I §7、III §2、VIII §1。
対象ビルド 3979 jobs 成功。私有宣言を含む 511 モジュール 4951 宣言で標準三公理のみ。
L9e は進行中。幾何的な塔の群の微分との比較、収束、有理 Shapiro の全射性、通常の Tot の比較は未完了。



## 旧計画本文の保存（2026-10-19、π₀ 比較工程）

## 所有するもの・借りるもの

- 所有：Kan 複体の π_n とその群構造・自然性・ホモトピー不変性。
- 所有：Kan fibration の連結射とホモトピー長完全列。
- 所有：γ-B の Ω スペクトル、その単体的圏と coherent nerve。
- 所有：整数次数のスペクトルの π_n。
- 所有：有理化、hG、Tot の Kan 複体による実構成。
- 借用：Mathlib の EG の自由 G 集合の単体的図式と、斉次・非斉次座標の作用の同型。
- 借用：H_* は K-L2 が所有する。
- 借用：Mathlib の正規化鎖複体、非退化単体の余積表示、生成子の交代微分式。ここでは Hom による cochain の比較先の構成だけに使い、H_* の結果を追加しない。
- 借用：pro 形式は K-L6 が所有する。
- 借用：γ1 は N レーンの局所 Kan coherent nerve 定理。
- 借用：γ3 は N レーンのホモトピー極限と ∞ 極限の比較。
- 借用：N の HomotopyLimits の Bousfield–Kan end・ホーン充填による Kan 性・path 置換による係数のホモトピー不変性。
- この借用は段ごとの単体集合の実構成だけに使い、Sp の ∞ 極限性や導来写像空間の比較を主張しない。
- 借用：Core の pinched 写像空間とその Kan 性。
- 借用：既存 Pointed.CofiberPushout の通常の商の点つき pushout の普遍性。安定モデル構造は含まない。
- 既存 Spectra は比較用に読むだけで編集しない。
- 既存 Spectra の `PointedSimplicialSet.Basic` と `Pointed.InternalHom` の基礎定義を借りる。
- この借用は Under による点つき対象と等化子による Hom のみで、安定モデル構造は含まない。
- suspension・loop では既存 Spectra の円、smash、閉対称モノイダル構造の通常の圏論的構成も借りる。
- 借用：既存 Pointed の自由基点の追加、自由基点の smash と直積の同型、tensor した余積の普遍性。
- 豊穣構造の移送は既存 CategoryTheory の通常の lax monoidal 関手の補題を借りる。
- 既存 HomotopicalAlgebra は読むだけで編集しない。
- 借用：同ディレクトリの基点を含む指定部分を固定する垂直ホモトピー充填。
- 借用：`AnodyneKanReplacement` のホーンの小対象論法と `Generators` の境界生成定理。
- 借用：一般の Reedy 次数帰納による関手的因子分解、matching・latching の右類・左類閉性、simplex 圏の Reedy 構造。
- この借用は通常の因子分解と持ち上げ性だけであり、Reedy モデル圏や HT-KQ のインスタンスを用いない。
- これらはモデル構造を仮定しない充填と因子分解で、HT-KQ の import は含まない。
- 既存 InfinityCategories は読むだけで編集しない。

## 1. 正本と目的

作成日：2026-10-18。
状態：L9a・L9b・L9c・L9d 完了。L9e 進行中。
Sp、自然な任意段表示、置換、任意の射の homotopy fiber と整数次数の長完全列まで検証済み。
対象ビルド・511 モジュール 4951 宣言の公理監査成功。
直近の工程区切りの全体ビルド（L9d、12125 jobs）は共有ルートの他レーンの宣言重複で失敗。
`InfinityCategories.F1.RelativeFunctorVertices` と `F1B.RelativeFunctorHomotopyComposition` の
`relativeFunctorVertex` 重複。K-L9 の import 閉包と対象ビルドは成功。
最後に成功した全体ビルドは L9c、9543 jobs。
L9c の BF cofibrant–fibrant 方式への改訂を承認済み。
正本：[KST 経路](stage-i/kst-lanes/k-theory-kst-route.md) §5、§13 決定 3・4。
基盤の正本：[foundations](stage-i/infinity-lanes/foundations.md) §1 の F3・γ。
本文は実装順と検証状態を管理する。
実施の経緯はコミットメッセージに記録する。
証明できた宣言だけを完了表に記載する。
設計案は実装済み宣言と区別する。
全体の到達点は定理 3.1 の全次数 π_* 同型である。
本レーン単独で定理 3.1 全体を証明したとは主張しない。
`theorem_3_1_K0` の置換は合流先の仕事である。
`supportedRankK0_descent` の置換も合流先の仕事である。
本レーンはそのための Sp と π_* を供給する。

## 2. 編集範囲

Lean の作業場所は `SerrePositivity/KST/Spectra/`。
namespace は `SerrePositivity.KST.Spectra`。
集約入口は `SerrePositivity/KST/Spectra.lean`。
ルートへの変更はこの入口の public import 一行のみ。
監査入口は `scripts/audit_kst_spectra.lean`。
この計画以外のレーン計画を編集しない。
共有ファイルの既存の未コミット変更を保存する。
他者の新規ファイルをコミットしない。
他者の作業を修正してビルドを迂回しない。
import 閉包の破損はそのまま報告する。

## 3. 原典の対応

| 対象 | 原典 | 適用の範囲 |
| --- | --- | --- |
| Kan 複体 | Kerodon §3.1 | ホーンの充填 |
| pointed homotopy | Kerodon §3.2.1 | 基点を固定したホモトピー |
| π_n の定義 | Kerodon §3.2.2 | 境界が定数の単体の商 |
| π_n の積 | Kerodon §3.2.3 | 充填で定義する群構造 |
| 可換性 | Kerodon §3.2.3 | n ≥ 2 の二つの積の比較 |
| π_* による検出 | Kerodon Theorem 3.2.7.1 | Kan 複体の同値 |
| coherent nerve | HTT Proposition 1.1.5.10 | 局所 Kan から quasicategory |
| coherent nerve | Kerodon Proposition 2.4.5.1 | γ1 の既存実装 |
| pinched Hom | HTT Proposition 1.2.2.3 | 右写像空間 |
| pinched Hom | Kerodon Proposition 4.6.5.5 | Core の Kan 性 |
| spectra | HA §1.4.2 | spectrum objects |
| spaces の spectra | HA §1.4.3 | 安定ホモトピー群との接続 |
| 比較 | HTT Theorem 4.2.4.1 | γ3 後の ∞ 極限の比較 |
| 単体的 π_* | Goerss–Jardine, I §7 | 古典的ホモトピー群 |
| fiber の連結射 | Kerodon §3.2.5、Goerss–Jardine, I §§7–8 | 相対ホーンと完全性 |
| 長完全列 | Kerodon Theorem 3.2.6.1 | kernel と image の比較 |
| スペクトルの比較 | Bousfield–Friedlander, §2 | 古典的スペクトル |

原典の定理番号が未確認の場合は節番号を使う。
原典の主張を公理として持ち込まない。
原典への参照は証明義務の代わりにしない。
Mathlib の既存証明は依存公理まで監査する。

## 4. 全体の設計決定

γ は γ-B を採用する。
HT-KQ の引用を使わない。
`Inputs/Homotopy/KanQuillen` を import しない。
既存の対称スペクトルを Sp の定義に置き換えない。
Sp の入口は Mathlib の `SimplicialNerve`。
γ1 の既存定理で quasicategory を得る。
その前に豊穣 Hom の Kan 性を証明する。
Kan 性を新しい入力仮定として隠さない。
群の法則を未証明の入力構造にしない。
fiber 長完全列を仮説として構造に入れない。
有理化の π_* 計算を入力として構造に入れない。
π_* 同型が第 1 段の公開界面となる。
Sp の ∞ 極限という主張は γ3 後に分離する。

## 5. 次数と基点

Kan 複体の次数は自然数。
次数ゼロは pointed set で、一般には群でない。
群構造は正の次数だけに付ける。
可換群構造は二以上の次数に付ける。
基点は `X _⦋0⦌` の元。
射の像の基点は自然変換の零成分で与える。
基点を固定する射と、基点を動かす道を区別する。
ホモトピー不変性はまず基点固定で証明する。
非可換な π_1 の積の向きを明記する。
スペクトルの次数は整数。
負次数を自然数への切り捨てで定義しない。
段の選択への独立性を遷移同型で証明する。

## 6. L9a：代表と関係

Mathlib の `SSet.PtSimplex` を使う。
境界定数条件は `RelativeMorphism` の条件に従う。
本レーン固有の名前で商を定義する。
Mathlib の将来の `π_n` と衝突させない。
`RelStruct` のホーンによる関係を使う。
正次数では `MulStruct .const f g i` との比較を使う。
反射性は退化単体から得る。
対称性は `oneMulEqSymm` から得る。
推移性は `oneMulEqTrans` から得る。
各面添字の関係が一致することは別途証明する。
零次数は `PiZero` と照合する。
商の等式から関係の証人へ戻す補題を用意する。
代表の変更が積に影響しないことを先に証明する。

## 7. L9a：群構造

積の候補は `MulStruct.nonempty` から選ぶ。
選択の依存を商で消す。
積の候補の一意性は商でだけ主張する。
代表単体の一意性は主張しない。
単位元は定数単体の類。
左単位は `oneMul` から得る。
右単位は `mulOne` から得る。
結合則は `MulStruct.assoc` と `assoc'` を使う。
左逆元は `exists_left_inverse` から選ぶ。
群構造を商の上に構成する。
逆元の代表選択は群法則による一意性で処理する。
隣接する積の反転を四面の比較ホーンの充填で証明する。
四面の消去と正順・逆順の充填の比較により二以上の次数の可換性を得る。
可換性の具体的証明は Kerodon §3.2.3 の四面の議論に合わせる。
可換性に π_* の安定化を先取りしない。

## 8. L9a：自然性とホモトピー

単体集合の射による代表単体の後合成を定義する。
境界定数条件の保存を証明する。
`RelStruct` の後合成を定義する。
`MulStruct` の後合成を定義する。
商上の写像を定義する。
恒等射の保存を証明する。
合成の保存を証明する。
積の保存を証明する。
基点付き同型が誘導する群同型を構成する。
相対ホモトピーから代表単体間の関係を得る。
ホモトピーの両端の誘導写像が一致すると示す。
ホモトピー同値から群同型を得る。
ここまでを L9a の完了条件とする。

## 9. L9b：fiber と連結射

対象は Kan fibration。
基点は全空間で選び、底の基点へ送る。
fiber は基点への引き戻し。
fiber の Kan 性を引き戻しから証明する。
底の代表単体をホーンに沿って持ち上げる。
欠けた面が fiber の代表単体となることを示す。
持ち上げの選択が商上で独立であると示す。
連結射の基点保存を示す。
適切な正次数で群準同型性を示す。
fiber → 全空間 → 底の誘導射を定義する。
連続する射の合成が零となると示す。
各箇所で kernel = image を証明する。
π_1 と π_0 の端は pointed set の完全性で述べる。
fibration 間の射に対する自然性を示す。
ここまでを L9b の完了条件とする。

## 10. L9c：ループ空間

基点付き Kan 複体のループ対象を具体的に固定する。
区間の両端の制限の fiber とする候補がある。
Core の pinched Hom を使う候補もある。
二つの具体モデルを無言で同一視しない。
Kan 性は端点制限の fibration 性から得る。
基点は定数ループ。
ループ構成の関手性を証明する。
π_n(ΩX) と π_(n+1)(X) の比較を証明する。
比較は基点と積を保存する。
Ω の enriched functor としての振る舞いも必要となる。

## 11. L9c：スペクトルと写像空間

対象は点つき Kan 複体の列 X_n と構造写像 σ_n : ΣX_n → X_(n+1)。
σ_n は単射とし、随伴 X_n → ΩX_(n+1) は全基点で π_* 同型とする。
これは Bousfield–Friedlander 1978 の安定モデル構造の cofibrant–fibrant モデルである。
原典は Bousfield–Friedlander 1978 と HTT A.3.3。
厳密な構造同型 X_n ≅ ΩX_(n+1) は要求しない。
厳密同型を外した理由は、従来の Hom の厳密極限の Kan 性の証明が得られないため。
構造写像と可換な段ごとの点つき射をスペクトルの射とする。
豊穣 Hom は有限切断への写像空間の塔の極限とする。
各段の制限は Hom_*(X_(n+1),Y_(n+1)) → Hom_*(ΣX_n,Y_(n+1)) の引き戻し。
源の単射 σ_n と標的の Kan 性によりこの制限は Kan fibration。
Kan fibration の引き戻しと塔の極限についての閉性を RLP から証明する。
従って Hom(X,Y) → Hom_*(X_0,Y_0) は Kan fibration となる。
始段の Kan 性と合わせて Hom(X,Y) の Kan 性を得る。
この Kan 性の証明には Ω 条件を使わない。
Ω 条件はスペクトルの正しいホモトピー型を表すための条件である。
合成と単位は厳密な段ごとの合成と単位から作る。
Sp はこの単体的圏の coherent nerve とし、γ1 を適用する。
この nerve が導来写像空間を持つ正しい Sp であることの比較は γ3 後に扱う。
第 1 段の π_* の証明にその比較を使わない。
非単射の構造射は境界生成の cell 分解によって直接 cofibrant 置換する（§32）。
各段の Kan 置換には既存 AnodyneKanReplacement の実構成を使う。
両置換の存在と π_* の保存を本レーンで証明し、入力にしない。
fiber 列の各段の fiber は構造射の単射性を保つとは限らないので置換を挟む。
K 理論の反復 delooping もこの対象仕様に直接合わせる。
単射の cell 分解は Mathlib の relativeCellComplexOfMono により得る。
整数次数 π_* とその自然性を構成する。
fiber 列の定義と長完全列を実装する。
ここまでを L9c の完了条件とする。

## 12. L9d：有理化

自然数による乗法写像の telescope を構成する。
全ての正整数を反転する列を明示する。
通常の余極限と homotopy telescope を区別する。
構成した対象の Kan 性を証明する。
ループ構造との整合を示す。
π_* が必要な telescope と可換すると示す。
アーベル群の有理化との比較を構成する。
比較の対象は π_*(X) ⊗ ℚ。
自然性と加法性を証明する。
有理化写像の π_* を明記する。
ここまでを L9d の完了条件とする。

## 13. L9e：作用と Tot

有限群の作用を実際の作用図式として与える。
homotopy fixed points と通常の fixed points を区別する。
cosimplicial replacement の全ての構造射を構成する。
Tot は段ごとの Kan 複体で構成する。
Tot の Kan 性を Reedy 型の充填で証明する。
極限という語だけから Kan 性を主張しない。
有理係数の有限群コホモロジー消滅を実証する。
平均化に使う群の位数が可逆であることを明示する。
自明作用の有理スペクトル M の比較射を作る。
π_* 上で M → M^{hG} の同型を証明する。
任意の非有理 M に同じ結論を主張しない。
γ3 前は Sp の ∞ 極限の普遍性を主張しない。
ここまでを L9e の完了条件とする。

## 14. 検証と保存

保存単位ごとに対象の `lake build` を実行する。
保存単位ごとに専用の公理監査を実行する。
許容公理は `propext`、`Classical.choice`、`Quot.sound` のみ。
`sorryAx` を拒否する。
追加公理を拒否する。
HT-KQ への依存を認めない。
監査は公開定理だけでなく本レーンの全宣言を対象とする。
検証シェルでは `set -o pipefail` を指定する。
パイプを通したログの見かけの成功に依存しない。
工程完了時だけ全体ビルドを行う。
`git diff --check` を行う。
コミットは自分の検証済みファイルだけ。
`git commit --only` を使う。
ルートの既存変更を巻き込まない。
amend・rebase・reset を使わない。

## 15. 現在地

| 工程 | 状態 | 残る証明 |
| --- | --- | --- |
| 計画 | 作成 | 実装と同期する |
| L9a | 完了 | 全体ビルドも L9b の区切りで成功 |
| L9b | 完了・対象ビルド、公理監査、全体ビルド成功 | なし |
| L9c | 完了・対象ビルド、公理監査、全体ビルド成功 | γ3 後の導来 Sp・∞ 極限との比較は別工程 |
| L9d | 完了 | 実際の telescope 有理化・単位・射、全整数次数の自然なテンソル比較 |
| L9e | 進行中 | Tot、hG、有理自明作用の比較 |

## 17. 公開時の注意

工程の部分成果を全工程の完了として報告しない。
構造の定義だけを存在証明として報告しない。
入力された法則を証明したと報告しない。
有理化は実際の π_* の計算まで必要。
局所 Kan 性は γ1 の実質的な適用条件である。
π_* の長完全列は実際の連結射を伴う。
共有 import の破損時は依存箇所とエラーを報告する。
設計変更の提案時は変更箇所と理由を明記する。
通常の工程報告後は承認を待たず次の工程へ進む。

## 18. L9c の改訂仕様（ユーザー承認済み）

2026-10-18 のユーザー承認により §11 の BF cofibrant–fibrant 方式を採用した。
厳密な Ω 同型の仕様は置き換える。
全基点での π_* 同型、構造写像の単射性、Hom の塔の引き戻し表示を同時に保持する。
これらの条件を追加公理にせず、必要な存在・置換・充填を実証する。
π_j(X) は k ≥ −j に対する π_(j+k)(X_k) とし、段の選択独立性を証明する。
零次数が群となる点もループ構造と比較して証明する。

参照：

- Bousfield–Friedlander, *Homotopy theory of Γ-spaces, spectra, and bisimplicial sets*
  (1978), §2。安定モデル構造の cofibrant–fibrant モデル。
- [HTT](https://www.math.ias.edu/~lurie/papers/HTT.pdf), A.3.3。単体的図式のモデルと写像空間。
- [HA](https://www.math.ias.edu/~lurie/papers/HA.pdf), §1.4.2 と Proposition 1.4.3.6 の証明。
- [Kerodon の塔の補題](https://kerodon.net/tag/0194), Corollary 11.9.7.2
  （retired subsection の現行番号）。
- Mathlib `AnodyneExtensions/PushoutProduct.lean`, `fibration_pullbackObjObjπ`。
- Mathlib `Skeleton.lean`, `relativeCellComplexOfMono`。
- 既存 `HomotopicalAlgebra/Simplicial/AnodyneKanReplacement.lean`。

γ1 による quasicategory 性と、導来写像空間を持つ正しい Sp との比較を区別する。
後者は γ3 後の工程であり、第 1 段の主張には含めない。
HT-KQ は使わない。共有正本 §13-3 はユーザーが更新する。

## 19. L9c の写像空間の相対充填

`PointedMapping.lean` に次の補題を証明済み。

| 主要宣言 | 内容 |
| --- | --- |
| `PointedMapping.basepoint_mono` | 基点包含は単射 |
| `PointedMapping.restriction_fibration` | Kan な標的への指数の基点制限は fibration |
| `PointedMapping.basedHom_kanComplex` | 点つき Hom の Kan 性 |
| `PointedMapping.pre_restriction` | 点つき射の制限と基点評価の可換性 |
| `PointedMapping.pre` | 源に沿う点つき Hom の制限 |
| `PointedMapping.pre_hasLiftingProperty` | 基礎指数から点つき Hom への相対充填の移送 |
| `PointedMapping.pre_fibration` | 単射に沿う点つき Hom の制限は Kan fibration |

源の Kan 性や Ω 条件を用いず、指数版 pushout-product から証明した。
既存 Spectra の点つき対象と等化子の基礎定義のみを借りる。
既存の安定モデル構造の定理は import していない。
保存単位の検証：対象ビルド 1522 jobs 成功。
私有宣言を含む 12 モジュール 644 宣言で標準三公理のみ。
L9c 全体は未完了。次は fibration の塔の極限への相対充填を構成する。

## 20. L9c の塔の極限

`FibrationTower.lean` に自然数で添字づけた逆向きの塔の極限を構成した。
各次数の単体は、隣接段の遷移と整合する元の族である。
一般の厳密極限の Kan 性を仮定していない。

| 主要宣言 | 内容 |
| --- | --- |
| `FibrationTower.limit` | 次数ごとの整合族による単体集合 |
| `FibrationTower.projection` | 各段への自然な射影 |
| `FibrationTower.lift` | 整合する射の族の普遍的持ち上げ |
| `FibrationTower.hom_ext` | 射影による射の一意性 |
| `FibrationTower.stages` | 初段の指定充填からの帰納的な相対充填 |
| `FibrationTower.stages_comp` | 帰納的充填の遷移との整合性 |
| `FibrationTower.projection_zero_hasLiftingProperty` | 右持ち上げ性の初段射影への移送 |
| `FibrationTower.projection_zero_fibration` | fibration の塔の初段射影は fibration |
| `FibrationTower.limit_kanComplex` | 初段 Kan・遷移 fibration の塔の極限は Kan |

参照：Kerodon Corollary 11.9.7.2、HTT A.3.3、BF 1978 §2。
保存単位の対象ビルド 1523 jobs 成功。
私有宣言を含む 13 モジュール 672 宣言で標準三公理のみ。
L9c 全体は未完了。次は切断スペクトルの Hom の塔を実装する。

## 記録の所在

実施記録・現在地の詳細・型一覧は [archive/L9-spectra-log.md](archive/L9-spectra-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
