# F1b（旧 α2b）：随伴・局所化・Kan 拡張 → F2-lite

> **v2 の位置づけ（2026-10-19）**：foundations.md §6 の F1b → F2-lite。B4・B5 の後、Cat_∞ を ∞ 圏として（Kerodon 5.5）、Cat_∞ の極限、lax pullback。

## 引き継ぎ（2026-10-19）

### 現在地

- v2 の F1b レーンとして再開。B4・B5 の後は [F2 計画](infinity-core-F2.md) の第 1 部へ進む。
- B1・B2・B3 は本文に明示した模型・宇宙の範囲で完了。B4 は進行中、B5 は未着手。
- B4：任意の δ と右指定変換 α の円柱比較つき相対 join 表示、両端の同時厳密化、
  補正後の指定変換の h Fun の類と α の類の一致、右 Kan 条件の保存まで証明済み。
- 任意の右指定変換について、厳密化・類保存を標準局所極限判定へ合成済み。
  元の右 Kan 条件と厳密化後の全局所錐の極限性の同値、および類を保つ局所極限表示の存在を証明。
- 最終検証：`lake build SerrePositivity.InfinityCategories.F1B` 成功（2417 jobs）。
  `lake env lean scripts/audit_infinity_f1b.lean` 成功（2822 宣言、標準三公理のみ、746 モジュールに straightening なし）。
- 前回の実装の保存：`a391eac8`。`relativeFunctorVertex` は `1132823f` で `relativeExtensionVertex` へ改名済み。
  F1B と監査スクリプトに旧名は残っておらず、改名後の集約ビルド・監査も成功。

### 残り（依存順、実作業時間の概算）

- 1. 全部分 ∞ 圏からの相対 Kan 拡張の写像空間の制限定理を証明する。
  Kerodon Prop 7.3.6.7・Cor 7.3.6.9／HTT §4.3。24〜60 時間。新しい充填補題の量で変動。
- 2. 点ごとの Kan 条件から大域的 Hom の全単射を導き、h Fun の大域的一意性へ接続する。
  Kerodon Prop 7.3.6.1・Remark 7.3.6.6／HTT §4.3。1 の後に 6〜16 時間。
- 3. 各点の極限・余極限の存在から Kan 拡張の存在と全関手への組み立てを証明する。
  Kerodon Prop 7.3.5.1、A6 の点ごとの関手圏極限 API／HTT §4.3。24〜60 時間。
- 4. B5：通常の圏の nerve で古典随伴・Kan 拡張へ戻る検査と最終監査。
  Kerodon §6.1.1・Def 7.3.1.2・Variant 7.3.1.5／HTT §5.2・§4.3。12〜32 時間。
- 右円柱比較の前合成同値そのものは未証明。右表示の存在は左表示の存在の反転から直接得ており、
  現時点ではこの追加命題を使わずに局所極限判定への合成を完了。必要なら Kerodon Prop 5.2.4.5 の双対として別途証明。

### 主要宣言（名前のみ）

- `QCatAdjunction`
- `qcat_nonempty_adjunction_iff_exists_naturalPinchedFamilyComparison`
- `ReflectiveSubcategory`
- `isRightCofinal_iff_weaklyContractible_coslices`
- `initialCofinality_via_quillenA`
- `IsRightKanExtension` / `IsLeftKanExtension`
- `RightKanHomUniversal` / `LeftKanHomUniversal`
- `RightKanRelativeJoinRealization`
- `rightKanRelativeJoinStrictification_exists`
- `RightKanRelativeJoinRealization.Strictification.transformation_hom_eq`
- `RightKanRelativeJoinRealization.Strictification.isRightKanExtension_iff`
- `rightKanRelativeJoin_realization_preserving_class`
- `isRightKanExtension_relativeJoin_iff_local_limits`
- `RightKanRelativeJoinRealization.Strictification.isRightKanExtension_iff_local_limits`
- `IsRightKanExtension.exists_relativeJoin_local_limits`
- `LeftKanRelativeJoinRealization.Strictification.isLeftKanExtension_iff_local_colimits`
- `relativeExtensionVertex`

### 依存と提供

- Core/・F1/・Stable/ は読み取り専用。join・slice・h Fun・充填・反転・錐の輸送を利用。
- A6 の `Core/FunctorPointwiseLimitExistence.lean` は到着済み。変動する slice の組み立ては別に必要。
- 提供：F1B 集約、随伴・反射的局所化・Quillen A、左右 Kan の点ごとの型と相対 join 還元の証明部品。
- straightening に推移的にも依存しない。一般の局所化の存在は F2、空間値二変数 Hom 関手は F1h の担当。

### 未コミット

- 今回の保存単位：`KanRelativeJoinRightCriterion.lean`、F1B 集約、監査スクリプト、本書、F2 計画。
  保存コミット後の所有ファイルの変更はなし。他レーンの作業ツリー変更は保存・変更しない。

### 既知の問題

- 対象ビルド・監査に失敗なし。今回の停止検証で全体 `lake build` は実行していない。
- F1 の同名宣言との衝突は上記の改名で解消。F1B のソースに `ModelCategory` 仮定なし。
  定理ごとの `Quasicategory`・`KanComplex`・`Mono` 等の前提は Lean を正本とする。
- 大域的 Hom 普遍性を仮定した一意性は証明済みだが、点ごとの Kan 条件からの導出は未完了。
  各点の `valueIso` の族や、固定形の相対充填だけを大域的一意性・変動 slice の組み立てと扱わない。
- B1 の自然性は全パラメータの集合値前層の模型。空間値二変数 ∞ 関手の自然変換との比較は未形式化。
  B2 の局所化の普遍性は同じ宇宙の標的に対するもの。一般の C[W⁻¹] の存在は主張しない。

### 次の一手

- 全部分 ∞ 圏からの相対 Kan 拡張について、写像空間の制限定理の証明に着手する。
  Kerodon Prop 7.3.6.7・Cor 7.3.6.9 を読み、`KanRelativeConeFamilies.lean` の
  固定境界の充填と、変動するパラメータを含む制限写像の差を明確にする。

作成日：2026-10-18。正本は [infinity-core-F1.md](infinity-core-F1.md) の F1e〜F1g と
[foundations.md](foundations.md) §6・§8。本計画は目標・型・設計・現在地・主要宣言を管理し、
実施の経緯はコミットメッセージに置く。

## 0. 目標と範囲

quasicategory の随伴、反射的局所化、cofinality、点ごとの左右 Kan 拡張を構成する。
Lean は `SerrePositivity/InfinityCategories/F1B/`、namespace は
`SerrePositivity.InfinityCategories`、集約は `InfinityCategories/F1B.lean`。
Core/・F1/・Stable/ は読むだけ。straightening に推移的にも依存しない。
sorry・追加公理・文献入力を使わず、監査で許す公理は
`propext`・`Classical.choice`・`Quot.sound` のみ。

## 1. 原典と工程

| 工程 | 成果 | 原典 | 状態 |
| --- | --- | --- | --- |
| B1 / F1e | 単位・余単位と h Fun の三角恒等式、自然な写像空間対応との特徴づけ、合成、随伴関手の一意性 | Kerodon [Def 6.1.1.1](https://kerodon.net/tag/02CG)、[§6.1.3](https://kerodon.net/tag/02D5)、[§6.1.5](https://kerodon.net/tag/02DM)、[Def 6.2.1.1・Prop 6.2.1.17](https://kerodon.net/tag/02EJ)、[Prop 6.2.6.1](https://kerodon.net/tag/02FV)・[Cor 6.2.6.5](https://kerodon.net/tag/02FX) / HTT §5.2 | 完了（全パラメータの族の前層による自然性の模型） |
| B2 / F1f | 充満部分 ∞ 圏への反射、局所対象、冪等性、局所化の普遍性の型と反射的な場合の構成 | Kerodon [§6.2.2](https://kerodon.net/tag/02F5)、[Cor 6.2.2.26](https://kerodon.net/tag/02FF)、[Def 6.3.1.9・Prop 6.3.1.13](https://kerodon.net/tag/01ME)、[Prop 6.3.3.7](https://kerodon.net/tag/02FY) / HTT §5.2.7 | 完了（同じ宇宙の標的に対する普遍性） |
| B3 / F1g 前半 | right cofinal、Quillen A、A2h の始対象による limit 計算の双対的回収 | Kerodon [Def 7.2.1.1](https://kerodon.net/tag/02N1)、[Thm 7.2.3.1](https://kerodon.net/tag/02NX) / HTT Thm 4.1.3.1 | 完了（左右の Quillen A と二宇宙版 A2h の同じ制限写像の回収） |
| B4 / F1g 後半 | slice の極限による左右 Kan 拡張、h での一意性、各点の存在、関手全体への組み立て | Kerodon [Notation 7.3.1.1・Def 7.3.1.2](https://kerodon.net/tag/02Y7)、Variant 7.3.1.5、§7.3.5 / HTT §4.3 | 進行中（指定自然変換の比較錐、各点の値・一意性、左右比較錐の選択不変性、左右の h 不変性、普遍写像性を仮定した大域的一意性、相対 join 表示、指定変換の類の保存、部分パラメータを固定した相対充填、slice の相対 join への局所比較、左条件の局所余極限表示への還元、標準右指定変換の局所極限表示との同値、任意の右指定変換の円柱比較つき相対 join 表示、厳密化後の局所極限判定への合成） |
| B5 | nerve による古典随伴・Kan 拡張の回収と監査 | 上記と通常の圏の随伴・Kan 拡張 | 未着手（監査スクリプトは稼働中） |

## 2. 設計上の決定

- 随伴は `SSet.QCat.strictBicategory` 上の双圏随伴。二胞体は
  h((ihom X).obj Y) の射であり、hX と hY の間の随伴で代用しない。
  A1c の `homotopyNatTrans` と A3a の `FunctorIso` に接続する。
- 写像空間は右 `pinchedHom` を使い、中間模型に区間写像空間を使う。
  各点で独立に選んだ同値だけや π₀ の全単射だけを自然な対応と扱わない。
  同値条件は各点の実際のホモトピー逆の存在で述べる。
- 自然性の入力は、全ての単体集合パラメータ A と非定値端点図式 a,b の
  ホモトピー族の集合値前層の、端点を保つ通常の自然変換とする。
  その型と coherent 矢印空間の比較との厳密な全単射を証明した。
  各点の比較はこの同じ自然変換の作用から回収する。
  全パラメータの Hom 全単射は追加仮定ではなく、各点の同値性からの帰結である。
- 空間値 Hom 関手自体は正本の別レーン F1h に属し、left fibration の
  straightening で構成する工程である。その空間値二変数 ∞ 関手の自然変換と
  今回の模型との比較定理は未形式化で、証明済みとは主張しない。
  B1 は上の明示した族の前層の模型で構成・判定・自然性を完結している。
- 反射は頂点条件 P の張る全部分複体への包含の左随伴として指定する。
  余単位の可逆性・冪等性・局所化の普遍性をフィールドに加えない。
  P の同型不変性は不要。局所対象は単位成分の可逆性で定義し、包含の本質的な像と同定する。
- 局所化は W を反転する関手の全部分 ∞ 圏への前合成の同値で述べる。
  標的は元の単体集合と同じ宇宙 u の quasicategory。
  一般の C[W⁻¹] の存在は F2 に委ね、ここでは反射の場合だけを構成する。
- right cofinal は colimit を計算する向き。始対象による limit 計算は双対の
  left cofinal と対応する。Quillen A の fiber 条件は弱可縮性であり、
  Kan 性や ∞ 圏としての可縮性へ強めない。
- Kan 拡張では点ごとの slice 極限と関手全体への組み立てを区別する。
  後者は A6 の関手 ∞ 圏の極限 API を確認してから接続する。
- 各保存単位で集約ビルド、公理監査、推移的 import の検査を行う。
  監査は生成宣言を含む F1B の全宣言を宣言元モジュールで抽出し、
  読み込んだリポジトリ内の straightening 系モジュールを拒否する。

## 記録の所在

実施記録・現在地の詳細・型一覧は [archive/infinity-core-F1b-log.md](archive/infinity-core-F1b-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
