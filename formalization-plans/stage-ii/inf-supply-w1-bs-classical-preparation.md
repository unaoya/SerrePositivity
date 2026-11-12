# IS-W1 段0の洗い出し準備（⑤c、2026-11-12）

調整役の指示で IS-W1 §0〜§1 と参照文書を読んだ紙の準備。実装の開始・段0の完成報告ではない。KL-W1 の採取器の修正通知後は、まず BS の同じ18本の追従を再開する。現在の専用枝を維持し、新しい worktree の作成・キャッシュの温め・ビルドは行っていない。

## 読んだものと現在地

- `inf-supply-w1.md` §0〜§1、`infinity-g2-progress.md` 末尾二節、`infinity-codex-g2-finish.md` §1、`infinity-codex-g2.md` §1・§3・§4。
- BS の `drafts/Sheaves/SheafGenerators.lean`・`SpaceValued.lean`、`foundation-entry-points.md` §4・§4.1。
- KL-W1 後の main の下表の宣言・型・関連する本文を `git show` で閲覧した。作業枝へ main はまだ取り込んでいない。以下の配置は旧 F2 のパスからの推測ではなく、main の実ソースに基づく。

G8 別版そのものと、評価錐側の `sieveEvaluation_postcompose_homMk_eq` は既存。一方、選ばれた `rightFibrationMappingSection` の仕様は「x・c に関する自然性を仮定も主張もしない」と明記されている。したがって、既存の評価側の Ho 等式をそのまま G8 四角形の証明と見なさない。

## 対象・再利用・残り（型案を作る前の整理）

下表のパスは `SerrePositivity/InfinityCategories/` 以下。

| 順 | 狙う主張 | 既存の入口・配置 | 新しく証明すべき接続 |
| --- | --- | --- | --- |
| 1：G8 の② | 任意のパラメータを保持し、切断制限から G8 の指定極限への二経路を固定端点錐空間内で比較する | `Kerodon/LimitsAndColimits/LimitsAndColimitsOfSpaces/RightFibrationHomComparison` の自明 Kan fibration の射影・切断・比較。`Project/SetWeightedTensors/SetSectionsLimitNaturality` の `sectionsConeFamilyRestriction_fromSections`・`limitConeMap_homMk_eq_of_coneFamilyIso` | 錐の辺に沿う全族の比較を共通の自明 Kan fibration の span 上に作り、固定端点模型へ移す。さらに `coherentDiagramSectionsCone` と `spaceUniverseValueEquivalence`・`covariantRepresentableValueEquivalence` への接続を証明する。必要な全族同型を仮定に足さない |
| 2：G8 の①と四角形 | 篩包含について、上辺が `sieveTensorEdge` の前合成、下辺が `sieveSectionsMap` の後合成、縦辺が正本 `tensorSpaceFunctor_setWeightHomNatural` である四角形を Ho(Space) で閉じる | `Project/SetWeightedTensors/SetSectionsNaturality` の `elementsComparisonNatural`・`sectionsEquivalenceNatural`、同じ系列の `SetSectionsUnstraightening.relativePreIso` と既存の評価錐比較 | 底を固定した相対写像空間内で `elementsComparisonNatural` の自然性を構成し、`relativePreIso` と②を合成する。任意の前層 F と指定極限錐を保持し、F を層と仮定しない |
| 3：G14 | presentable E に、pinched Hom の後合成で同値を検出する `Type u` 添字の族を作る（E は `SSet.{u+1}`） | `Kerodon/LimitsAndColimits/LimitsAndColimits/ReflectiveModelLimitDetection` の `IsPresentable.exists_limitDetectingPresheafModel`。型側の `IsPresentable` は `HTT/PresentableInfinityCategories` へ export されている | 一点図式から辺の同値の評価検出へ渡す部分と、共通の評価関手を実際の `Map(g_a, −)` と比較する部分を洗う。検出族の存在を入力に置かない |
| 4：G9-1〜3 | left Quillen A、left cofinal の ulift 保存、`id → T ← const` からの nerve の縮約 | right 版は `Kerodon/LargeInfinityCategories/TensorProductsOfInfinityCategories/SiftedSimplexCategory`、反対向きの縮約は `Kerodon/KanComplexes/HomotopyGroups/WeakContractibleContractionSpan` | 既存の双対化・opposite・ulift の比較を先に洗い、同じ証明を複製しない。BS の `cechShape = uliftFunctor.map (nerveMap d.obj.rightOp)` と CostructuredArrow の向きに合わせる |

## 段0で次に確認すること

1. ①・②について、既存の比較の入力・出力を全て同じ図式と指定錐へ展開する。固定する底・端点・パラメータ単体集合を型案に書く。まず篩包含の場合を対象とし、一般の φ の完成まで広げない。
2. ②の共通 span と全族の持ち上げに必要な補題を、選んだ切断への自然性を仮定せずに作れるか確認する。頂点ごとの一致と全族の `FunctorIso` を区別する。
3. 全族の比較から、既存 G8 別版を構成する各同値への接続までを列挙し、どの同型を `limitConeMap_homMk_eq_of_coneFamilyIso` へ渡すか特定する。
4. G14 は小さい添字の宇宙と、評価を表現する対象の実構成を確認する。G9 は opposite による comma の同一視と宇宙変更を確認する。いずれも、未証明の比較を型の仮定に隠さない。
5. 型案が固まってから、新規ファイルの置き場所・不足補題・規模を見積もる。現時点では Lean の型検査・公理監査をしておらず、型の成立や行数の確定を報告しない。

新規 G8 の配置候補は `Project/SetWeightedTensors/`、right fibration に独立な比較は既存の Kerodon 側の隣。G14・G9 は上表の実入口の隣を候補とし、項目の所属は実装前に確かめる。旧名の deprecated alias や、古い指示書の `F2.lean`・`HomotopyLimits/` という綴りを新規 import に使わない。

G10 は段4の後に範囲を確認する項目。BS の Tot では全関手・射・指定錐までの比較が必要で、次数別ホモロジー同型だけで終わらせない。K の Sp 値でも使える一般性は型を決める際の確認事項とし、今回の紙の準備から実装範囲を拡大しない。BS の S3 は Quillen A の経路であり、G10 を S3 の前提に戻さない。

**今回は紙の準備のみ。Lean・drafts・入口・監査・改名ツールは無変更、ビルドと鍵の取得は0回。** 採取器の修正通知を待つ。
