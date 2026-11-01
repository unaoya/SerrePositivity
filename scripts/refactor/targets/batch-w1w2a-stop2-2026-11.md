# IF-W0-3 停止点2：保存比較の不一致（2026-11-01、§10.33）

**下流ビルドPASS、保存比較FAIL（69件）。停止点2で停止。verify未実行、今回のコミットなし。** main・宣言の本文・比較規則は変更していない。作業木は `../SerrePositivity-ifw0-3`、ブランチ `infra/if-w0-3`。

§10.33でround11のPASSを受理し、§10.32の新規ビルド数による停止を解除。収束の尺度は失敗モジュール数22→3→1→0。以下の保存不一致が残ったため、「downstream imports」「監査の追従」のコミットと全体verifyには進まない。

## 監査の追従（未コミット）

7監査の旧モジュール名325件を束の対応表に追従。splitの18項目はkeep/moved両側を列挙。必要な直接importを計8件追加。必須一覧の全モジュールの実在・到達性を静的確認。foundations/generalの禁止一覧、公理判定、verify.sh/runner、manifestは今回変更なし。KST spectraとlocalizing invariantsの定義元フィルターは移動先も検査するよう必須一覧を含めた。

| 監査 | moveの旧名 | split展開 | 追加import |
|---|---:|---:|---:|
| `scripts/audit_derived_infinity.lean` | 36 | 0 | 0 |
| `scripts/audit_homotopical_foundations.lean` | 27 | 4 | 3 |
| `scripts/audit_homotopical_general_tools.lean` | 27 | 4 | 3 |
| `scripts/audit_homotopical_rectification.lean` | 37 | 10 | 2 |
| `scripts/audit_infinity_stable.lean` | 34 | 0 | 0 |
| `scripts/audit_kst_spectra.lean` | 156 | 0 | 0 |
| `scripts/audit_localizing_invariants.lean` | 8 | 0 | 0 |

詳細は `batch-w1w2a-audit-followup.json`。監査自体の実行はverifyに含める予定だったため、未実行。

## 保存比較

| 項目 | before | after |
|---|---:|---:|
| モジュール | 3,020 | 3,033 |
| 採取した宣言行 | 30,828 | 30,829 |
| 比較件数（補助宣言を親にまとめる） | 17,180 | 17,181 |
| transient名 | 323 | 323 |
| transient行 | 335 | 335 |

全78群・3,033モジュールのafter採取は終了コード0、1546.940秒（25分46.94秒）。統合・比較は33.502秒、終了コード1。比較前の確認で停止した初回は1.340秒。全群のログを検索し、採取エラー0。巨大項38件。

§10.21〜10.22に従い `(宣言名, 定義元)` を対応表で照合し、同じname-mapとDAGハッシュを使用。生成private衝突12名（実名と定義元を保持）をtransientにし、人が書いたprivateの衝突は0名。`Hammock.Word.eq_empty_of_length_zero` はLengthZero/WordConsの2行をbefore/afterとも保持し、一致した。

統合前の確認で新たに `NecklaceShape.wedge.eq_1` の2帰属が見つかった。両行とも既存の外部定義生成補題の規則でtransient済み、型ハッシュも一致。環境のgetModuleIdxFor?を照会して帰属を統一した（一時統合ランナーの対象名を1つ追加、リポジトリ道具は未変更）。初回ログと判断記録を保持。これを処理した後にも以下の69件が残った。

| 不一致 | 件数 |
|---|---:|
| removed | 29 |
| added | 30 |
| type | 5 |
| body | 1 |
| auxiliaries | 4 |

公理・属性の不一致は0。ただし構造ハッシュの一致が受入条件なのでPASSとはしない。

## 不一致の分類と原因候補（修正していない）

1. **macro／unexpander生成名28組＝56件（removed28＋added28）**。`ModelBridge.{ChosenQuillenDerivedHom,ChosenQuillenFrameHom,QuillenDerivedHomComparison,QuillenLeftFrameAugmentation}` の生成名に、旧モジュールをunderscoreで埋め込んだ部分が残る。move後にその部分がModelBridgeへ変わった。既存のドット区切りの名前正規化では一致しない。private衝突12名の承認とは別の事象であり、独断で除外・正規化を追加しない。
2. **`doubleMappingCylinder_hom_ext` の定義元差＝2件**。beforeはDoubleMappingCylinderMap、afterはDoubleMappingCylinderDescとして採取された（型ハッシュは同じ）。ソースを読むとMap/Desc両方に同名の定理がbefore/afterとも存在する。Hammock同様の本物の重複が採取環境に隠れている可能性がある。現採取結果では両側1行しかなく、勝手に1行へ統合しない。再採取・規則追加は未実施。
3. **local無名instanceの追加＝1件**。`KST.SConstruction.instIsDGPretriangulatedDGOdotGluing_5`（DGOdotMilnorProjectionRectangle）。sourceのlocal instance（22–23行）はbefore/afterに存在し、本文は同じ。beforeの統合snapshotにはこの名前がない。環境の生成名／定義元による採取差が候補だが、未確定。
4. **型5件・本体1件**。使用定数の差は下表。import変更によりelaboration時に選ばれるinstance経路が変わった候補。定義的等価性は未確認であり、本文変更や比較の緩和をしない。

| 宣言（名前空間省略） | 種別 | 使用定数の差の例 |
|---|---|---|
| BoundaryFactorization.initial_left | type | instHasFiniteColimitsFunctor / instHasFiniteCoproductsFunctor → SimplicialObject.instHasColimits |
| kanTensorReplacement_isCofibrant | type | instHasFiniteCoproductsFunctor → finitaryExtensive_functor等 |
| kanTensorReplacement_isFibrant | type | instHasFiniteProductsFunctor → Functor.cartesianMonoidalCategory |
| kanTensorReplacement_left_isFibrant | type | instHasFiniteProductsFunctor → Functor.cartesianMonoidalCategory |
| EvaluationFamily.detected_inf | type | CompleteLattice→ConditionallyCompleteLattice→Lattice → CompleteLattice.toLattice |
| EvaluationFamily.generators | body | ConditionallyCompletePartialOrder経由のSupSet → CompleteSemilatticeSup経由のSupSet |

5. **補助宣言4件**。`Hammock.Direction` と `FiniteSpanVertex` のnoConfusion/noConfusionTypeにtype/body差。`SimplexInverseMatching.emptyMatchingTerminal` と `pointMatchingTerminal` の `_proof_1` にtype差。補助宣言の名前の増減はなし。生成過程・選択instanceの差が候補だが未確定。

証拠：`.lake/verify/batch-w1w2a/stop2/preservation.json`（69件全一覧）、`before-complete.json`、`after-complete.json`、`after-state.json`、`after-extra-owner-review.json`。構造JSONの再展開はしていない。

## 下流roundと層検査

| round | 新規成功 | 失敗モジュール | 秒 | 結果 |
|---:|---:|---:|---:|---|
| 1 | 5,837 | 14 | 3238.197 | FAIL |
| 2 | 1,731 | 9 | 715.557 | STOP_CORE_IMPORT |
| 3 | 3,059 | 28 | 1721.918 | FAIL |
| 4 | 187 | 3 | 193.824 | STOP_FORBIDDEN_CLOSURE |
| 5 | 58 | 2 | 189.714 | FAIL |
| 6 | 72 | 1 | 73.665 | FAIL |
| 7 | 1,378 | 4 | 567.412 | STOP_ROUND_BUILD_COUNT_INCREASE |
| 8 | 8,601 | 22 | 5132.899 | FAIL |
| 9 | 733 | 3 | 586.652 | FAIL |
| 10 | 78 | 1 | 103.846 | FAIL |
| 11 | 101 | 0 | 252.190 | PASS |

新規成功は警告付き成功も含め、round内では重複なし。全round合計21,835成功ジョブ・12,775.874秒（round間の再ビルドは重複計上）。round8〜11は9,513ジョブ・6,075.587秒。補充全体75利用元・83 import（今回承認のphaseは31 import）。監査の8 importは別集計。

停止点1→最終：直接違反296→294、禁止閉包W1=1→1、W2a/W2b=177→166。各補充の増加0、対象一覧1,285項目PASS。監査7本は中核グラフの外。キャッシュ増分は全round約255,113ファイル・12.807 GB（round8〜11は63,730ファイル・2.774 GB）。

## コミットと停止状態

今回の新しいコミットは0。監査の追従とdownstream importsは未コミットで保持。既存：W1 `749f7eaa2`、W2a `dcdab2c21`、追加split/BoundaryOne move `16e808ff6`、入口check移動 `999d292e3`、validator `9bc69dc79`、keep側7move `8dc0f29a0`。R75 `86f760485`、R79 `c4290092a`・`2c8a89952`。

verify未実行なので今回のverify summary（status/gate/counts）は存在しない。過去のsummaryを今回の結果として使わない。保存比較FAILの処置について判断を待つ。
