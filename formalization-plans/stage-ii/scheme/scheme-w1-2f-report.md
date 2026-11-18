# SC-W1 段 2f：停止点報告

2026-11-14。承認済みの射影・Čech 版の範囲で停止点 2f に到達した。最後の数学コミット **`32d8faeb7`**、全登録のコミット **`41350ee49`**。main は凍結中なので取り込まず、math/scheme だけで検証・コミットした。調整役の 11-14 の指示に従い、この報告の後は取り込みを待たず 2g の段 0 を作る。

## 1. 完成した範囲

零環を含めて環の実際の Frobenius 順極限を作り、nil な商と普遍同相な環準同型の不変性を証明した。有限射の中心外の同型から導手の冪の評価を得て、中心の商との四角形の短完全性を証明した。Stein 分解や代数空間の商は使わない。

射影版では R を Noether 環、p を素数、p=0 in R,A、G を R 代数 A の次数付けとする。A は有限個の変数の多項式環上有限で、指定した次数一の元が irrelevant ideal を覆うことを仮定する。Proj G→Spec R は全射で、V(I) の外で同型。これらは実際の幾何学的入力であり、求める H の同型や完全性を仮定に追加していない。

2e の有限性・核の評価・像の安定化を適用し、正次数の閉厚化への制限が Frobenius 順極限後に全単射となること、H⁰ と基底の中心を合わせた短完全性を得た。これらから、実際の増大全複体が Mathlib の Acyclic であることを証明した。

最後に、任意の実際の Cartesian な閉厚化 Y を取り、次数付き商の斉次局所化の環を Γ(Y,g⁻¹U) と比較した。この比較は環の同型で、制限・商の射・Frobenius と可換。次数付き商の Proj と Y のスキームとしての同一視を仮定していない。全複体をこの比較で移し、制限・スカラー・中心の各辺が実際の構造層・構造射の写像に一致することまで照合した。

## 2. 主な出口

名前空間は全て `SerrePositivity.AlgebraicGeometry`。全モジュールと明示した宣言の一行ずつの主張は [宣言一覧](scheme-w1-2f-declarations.md)。

| 段・宣言 | 主張 |
| --- | --- |
| F0 `frobeniusDirectLimitOf_eq_zero_iff`、`frobeniusDirectLimitOf_eq_iff` | 順極限の零と等式を有限段へ戻す。 |
| F1 `frobeniusDirectLimitQuotient_bijective` | nil イデアルによる商は実際の Frobenius 順極限上全単射。 |
| F2 `frobeniusDirectLimitUniversalHomeomorphism_bijective` | 普遍同相な環準同型は Frobenius 順極限上全単射。 |
| F3 `frobeniusFiniteModification_exact` | 有限な modification の導手の四角形は Frobenius 順極限後に短完全。 |
| F4 `projectivePerfCechH0Equiv` | 切断の等化子部分環の Frobenius 順極限と、実際の複体の Čech H⁰ を比較。 |
| F5 `projectiveCechSupport_power_annihilates` | 中心外で零になる射影 Čech H を I の冪で零化。 |
| F6 `reesClosedFrobeniusRingCechHomologyMap_bijective` | 正次数で実際の閉厚化の制限が全単射。 |
| F7 `projectivePerfCechH0_square_exact` | H⁰ と中心の四角形の最初の射の単射性・中央の完全性・最後の全射性。 |
| F8 `projectivePerfCech_blowupSquare_acyclic` | 固定した標準開の明示的な増大全複体は acyclic。 |
| `projectivePerfectCartesianTotalComplexIso` | 上の複体と、実際の Proj・Cartesian な閉厚化の構造層の複体の同型。 |
| `projectivePerfectCartesianSquare_acyclic` | 実際の閉厚化の構造層に移した全複体も acyclic。 |
| `projectivePerfectCartesianAugmentedSquare_restriction` | 制限の辺は実際の構造層の引き戻し。 |
| `projectivePerfectCartesianAugmentedSquare_scalar_apply` | 基底の辺は実際の大域スカラーを制限した環準同型の Frobenius 順極限。 |
| `projectivePerfectCartesianAugmentedSquare_center` | 中心の辺は実際の構造射から作った増大写像。 |

ここで F8 の「blowupSquare」という名前の入力は上記の射影的 modification の表示である。任意のブローアップをその表示に入れる Rees 環・ファイバー冪の接続は、2g の幾何学的判定法の入力を組み立てる仕事に含める。一般の固有射のコホモロジー有限性、Stein 分解、BST13 Lemma 3.6 の一般形・3.7 の商の存在は範囲外。

## 3. §9 の五つの比較と案 (b)

| 比較 | 今回までの宣言・到達点 |
| --- | --- |
| 共通アフィン細分 | `schemeStructurePerfectCechRefinement_quasiIsoAt`、`schemeStructurePerfectCommonAffineCechHomologyIso`、`projectivePerfectAffineCechHomologyIso`。分離的な場合の有限アフィン被覆の比較を実際の Frobenius 係数へ渡した。細分の選択独立性は `openCoverFrobeniusCechRefinement_homologyMap_eq`。 |
| 底変換・逆像 | `schemeStructurePerfectCechPullbackMap_refinement`、`schemeStructurePerfectAffineCechPullback_comparison_naturality`。アフィン射の実際の引き戻しと被覆比較が可換。`schemeStructurePerfectCechRefinedPullbackMap_apply` で各タプルが実際の appLE の順極限と一致。平坦でない射にも引き戻しは定義し、非平坦な射で H の同型性を主張しない。 |
| R/J 表示・閉厚化 | 2e の `reesClosedCoefficientAdicCechIso_module_naturality` に、今回の `reesClosedNativeSectionLinearEquiv`、`reesClosedNativeSectionRingIso` を接続。`reesClosedNativeSectionRingIso_projection`・`_naturality`、`reesClosedPerfectNativeCechIso_naturality` が実際の商・制限と比較を整合させる。全ての厚化指数 n で構成。 |
| Frobenius | `frobeniusRingDiagramMap_comp`、`frobeniusRingSequentialColimitIso_naturality`、`projectivePerfectNativeCechComplexIso_naturality`。環の射・次数を保つ射・閉厚化の射に同じ順極限を適用。 |
| filtered colimit | `projectiveFilteredComplexMap_quasiIsoAt`、`projectiveSequentialComplexMap_quasiIsoAt`、`projectiveIntCechSequentialComplexIso`、`openCoverSequentialCech_refinement_naturality`。有限交叉の係数、複体、H とその射を比較。 |

四角形の射の枠組みは `CechAugmentedSquare.Map`、合成・全複体の射・`CechAugmentedSquare.transportTotalComplexIso` にある。今回の実際の閉厚化の移送はこの枠組みに接続済み。共通被覆の比較は H と実際の射に関する自然な比較であり、任意の被覆変更に対する全複体の同型を主張するものではない。2g の二重 Čech と合成からの消去は既存 B1 を使う。

原典 BST13 Lemma 3.9・BS17 Lemma 4.6(i) の中間結果は導来大域切断を使う。今回の中間結果は承認された **Čech 版**であり、対応する docstring に原典の番号と「分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、この比較は形式化しない」を記した。被覆によらない H と射の比較は上表で供給する。導来関手 Hⁱ との比較を完成したとは主張しない。

最終出力 `SerrePositivity.Cech.AugmentedRingCechExact` と利用側の型は変更していない。有限加群の宇宙の移送には承認済みの `Module.Finite.small`・`Shrink.linearEquiv` を使える。

## 4. 許可された既存 API の一般化

係数環と加群の宇宙を分けた既存の **14 ファイル・69 宣言**、それぞれの追加元コミット、型変更の内容、全ての名前は [宇宙 API 報告](scheme-w1-2f-universe-api-report.md)。宣言名を保ち、元の宇宙を一致させた特殊化を狭めていない。

同報告の `git grep -n -F -f` で、本体 HEAD と main、および指定された `math/bs-impl`・`math/inf-supply`・`math/inf-supply-b`・`math/bs-m15` の各 SHA に対して、AlgebraicGeometry 外の Lean（BS・KST・追跡された drafts を含む）を照合し **各宣言とも外部利用 0**。その後に既存 API の追加の型変更はない。今回の入口ビルドで旧来の適用も通った。

## 5. 検証・規模

- 最後の対象と直接 importer：`lake build SerrePositivity.AlgebraicGeometry`、**4,780 jobs 成功**。
- 別実行の標準監査：`lake env lean scripts/audit_kst_scheme_lemmas.lean`、**10,642 宣言、propext・Classical.choice・Quot.sound のみ**。生成宣言・private・局所 instance も含む。
- 全 234 新規本体モジュールを入口に直接登録。ソースに明示した名前付き宣言は **752 件**で、監査の環境宣言数とは別。
- 停止点 2e の数学コミット `bf9767cdc` 以後：新規本体 **15,279 行**、入口追加 **453 行**、既存比較 API の追加 **48 行・削除 40 行**。追加の合計 **15,780 行**。文書・下書き・他レーンの数学は含めない。停止基準 **18,000 行以内**。半分の時点の報告は route に記録済み。
- 全ビルド・監査は共有 `with_build_lock.sh --wait 3600` を実行中だけ取得し、一回 30 分以内、待ちは一つ。heartbeat・再帰・探索の上限は引き上げていない。sorry・admit・新規公理を追加していない。差分の空白検査も通過。
- ログ・作業用スクリプトは worktree の `formalization-plans/stage-ii/scheme-drafts/`。この文書と一覧が追跡する成果の正本。

前の route に「凍結後まで入口登録を待つ」と書いた箇所は訂正する。凍結対象は main であり、自分の枝での登録・検証・コミットは許可されている。今回の登録・監査は math/scheme だけで行った。main への取り込み、SerrePositivity ルート・全下流のビルドは調整役が行う。

## 6. 次の段

直ちに [2g の段 0](scheme-w1-2g-route.md) を紙で作る。Rydh Thm 3.12、有限型 F_p の被覆模型、Thm 2.9 の複体版、既存 B1 と 2d・2e・2f の接続、不足と規模を分ける。2g 単独の見込みの上端が 20,000 行を超えるなら、11-14 の指示に従い Lean 着手前に報告して止める。
