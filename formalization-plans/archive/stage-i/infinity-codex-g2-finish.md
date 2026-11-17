# Codex 作業指示書 IF-G2-finish：G8 の四角形（篩包含）を区切りのよいところまで進めて main へ

作成：2026-11-05 夜（調整役）。宛先：∞ の数学の Codex（新しいチャットでよい）。段階 II に移る前の最後の束。
前提：[IF-G2](infinity-codex-g2.md) §1〜§4、進捗の記録 [infinity-g2-progress.md](infinity-g2-progress.md)（枝 `math/g2` から写したもの）、規則は [coordination.md](../../coordination.md) §2（小さなビルドだけ、全ビルドはしない、main の作業木では作業しない）。
**目標は四角形の完成ではなく、区切りのよいところまで進めて main に入れること**。段ごとに止めて報告し、通ったところまでを調整役が取り込む。

## 0. 準備

1. worktree `../SerrePositivity-ig1`（枝 `math/g2`、HEAD b60279c26）をそのまま使う。まず main（d26ec93a4 以降、F-2 と片付けを含む）を `math/g2` に merge する。衝突は main 側を正に。G2 の新規ファイルは変えない。**F-2 で名前空間が変わった宣言を使っていれば、改名表（`scripts/refactor/targets/f-namespace-map.json`）で新しい名前へ直す**（旧名は deprecated alias で残っているが、新しいファイルでは使わない）。
2. 旧 G8（`tensorSpaceFunctor_setWeightHom` 系）は deprecated になった。正本は `tensorSpaceFunctor_setWeightHomNatural`。

## 1. 数学の位置（記録の要約）

`Map(X ⋙ ⊗M, F) ≃ Map(M, Γ(X, F))`（G8 の別版、証明済み）の、X についての自然性を、篩の包含 `S.functorInclusion : S.functor ⟶ yoneda.obj U` の場合に示したい。同値は四段（集合値の重み → unstraightening との比較 → テンソルと Hom の随伴 → 指定極限錐）で、段 1・3 の自然性は証明済み。残りは：
- **①**：`sectionsEquivalenceNatural` の前合成を、`φ.mapElements` に沿う unstraightening の切断の制限へ移す（底を固定した相対写像空間の中で。`relativePreIso` で全パラメータの比較へ移せる）。
- **②**：その切断の制限を、`coherentDiagramSectionsCone` から指定極限錐への比較と `spaceUniverseValueEquivalence`・`covariantRepresentableValueEquivalence` を通して、`PinchedInterval.postcompose M [rφ]`（`rφ := sieveSectionsMap …`）と同定する。脚との可換性を示し、`sectionsConeMap_homMk_unique`（錐の圏での普遍辺の一意性、証明済み）で閉じる。
- 篩包含では h_U の要素の圏が始対象 (U, 𝟙) を持つので、評価錐が明示的に書ける（`SetSectionsSieveNaturality.lean` の `sieveEvaluationTriangle` の方針）。

## 2. 段と止めて報告する点

| 段 | 内容 | 止めて報告 |
| --- | --- | --- |
| **段 1（必須）** | WIP の 3 本（`F2/Tensor/SetSectionsUnstraightening`・`SetSectionsLimitNaturality`・`SetSectionsSieveNaturality`）のビルドを通す。既知のエラー：`SetSectionsUnstraightening` 35 行の `ofEq` の等式引数 `hx`・`hy` が推論できない（`realization_vertex` の等式の向き・形を合わせる）、102 行と `SetSectionsSieveNaturality` 191 行の `cases` の失敗。通ったら F2 の入口と `scripts/audit_infinity_f2.lean` に登録（監査で `importModules` を使うなら `import` 行にも書く）し、F2 監査を単独で流す | **停止点 1**：ビルドと監査の結果、sorry・公理 0。ここで調整役が取り込む |
| **段 2（目標）** | ② を篩包含の場合に独立の補題として示す（切断の制限 ＝ 指定極限錐への普遍射を、写像空間のホモトピー圏の等式として。頂点ごとの一致だけで閉じたとしない） | **停止点 2**：主張の型と証明の要点。取り込む |
| **段 3（届けば）** | ① を篩包含の場合に示し、②と合わせて四角形 `sieve_tensorSpaceFunctor_setWeightHomNatural_naturality`（名前は任意）を閉じる | **停止点 3**：四角形の主張。取り込み、BS に知らせる（S4 の生成辺が閉じる） |

- 時間の目安：段 1 は数時間、段 2・3 はそれぞれ半日〜1 日。**段 2 か段 3 で詰まったら、そこまでの補題（ビルドが通り sorry 0 のもの）をまとめて報告して止める**。未完の補題は新しい枝 `math/g2-wip` に残し、main には入れない。
- 各段で：新規ファイルだけ（G1・G2 の既存の宣言の本文・型・名前は変えない。G2 の WIP 3 本は直してよい）、sorry・公理・新しい引用を残さない、小さなビルドだけ（`ps` と鍵を確かめる）。
- 報告には、段ごとに：ビルドの結果、監査、追加した宣言の名前と主張（言葉で一行ずつ）、残っている一歩（数学的に）。

## 3. 終わったら

調整役が `math/g2` を main に取り込み、worktree `SerrePositivity-ig1` を外す。未完の部分は `math/g2-wip`（または進捗の記録）として段階 II の ∞ 供給レーンへ引き継ぐ。

## 4. 追記（2026-11-05 夜、停止点 1 の承認と段 2 の開始）

**承認**：段 1（408d87457）。調整役が main でルートと F2 監査対象のビルド、F2 監査を確認（エラー 0、3 本とも sorry 0）。
**段 2 に進む**（ユーザー決定）：② を篩包含の場合に独立の補題として示す。切断の制限 ＝ 指定極限錐への普遍射を、写像空間のホモトピー圏の等式として（段 1 の `limitConeMap_homMk_eq_of_coneFamilyIso`・`sectionsConeFamilyRestriction_fromSections`・`representableEvaluationConeMap` を組み合わせる）。
**取り込みの手順の確認**：段 1 では Codex が main を `math/g2` の先端まで fast-forward したが、以後は `math/g2` にコミットして停止点で報告し、main への取り込みは調整役が行う（main を直接動かさない）。
