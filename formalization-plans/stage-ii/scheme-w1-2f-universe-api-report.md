# SC-W1 段 2f：比較 API の宇宙の一般化と外部利用の確認

2026-11-14、調整役の条件に対する確認。⑥ の検証済み本体 `0deb4d5dc`。停止点 2f の完成報告ではない。

係数環と加群の宇宙を分離した **14 ファイル・69 件のソースに明示した既存宣言**を以下に列挙する。宣言名は変更していない。係数環と加群の宇宙を等しく特殊化すると以前の型になり、以前の適用を狭めていない。Mathlib・他レーンの宣言は変更していない。

## 変更した型と宣言

cone・filtered H・逆像：旧 `R : Type u`、`ModuleCat.{u} R` → 新 `R : Type v`、`ModuleCat.{u} R`。被覆の比較：旧 `R : Type v`、`ModuleCat.{v} R` → 新 `R : Type w`、`ModuleCat.{v} R`。環の宇宙以外の被覆・添字・次数・完全性等の仮定は維持する。filtered H の完全性の供給は新規 `ModuleCatFilteredExact` を使う。

開集合だけの五宣言（`cechOpenIntersection`、`cechOpenIntersection_antitone`、`cechOpenIntersection_refinement`、`cechOpenIntersection_refinement_union`、`openCoverCechRefinementHomotopy_support`）と、一般の圏の private 補題 `stage_square_inverse` は係数環を含まないため型変更の対象外。新たに追加した局所 instance は既存宣言の型変更には数えない。

### CechRefinementCone

⑥ での追加コミット：`eac527fbd feat(ag): add split affine Cech and refinement cone exactness`。

- `SerrePositivity.AlgebraicGeometry.cechRefinementConeTerm`
- `SerrePositivity.AlgebraicGeometry.cechRefinementConeDifferential`
- `SerrePositivity.AlgebraicGeometry.cechRefinementConeDifferential_squared`
- `SerrePositivity.AlgebraicGeometry.cechRefinementCone`

### CechRefinementConeMap

⑥ での追加コミット：`ecd5061a5 feat(ag): add affine Cech exactness and refinement comparison tools`。

- `SerrePositivity.AlgebraicGeometry.cechRefinementConeMapTerm`
- `SerrePositivity.AlgebraicGeometry.cechRefinementConeMapTerm_differential`
- `SerrePositivity.AlgebraicGeometry.cechRefinementConeMap`
- `SerrePositivity.AlgebraicGeometry.cechRefinementConeMapTerm_comp`
- `SerrePositivity.AlgebraicGeometry.cechRefinementConeMapTerm_id`
- `SerrePositivity.AlgebraicGeometry.cechRefinementConeMapTerm_zero`

### OpenCoverCech

⑥ での追加コミット：`ecd5061a5 feat(ag): add affine Cech exactness and refinement comparison tools`。

- `SerrePositivity.AlgebraicGeometry.openCoverCechDiagram`
- `SerrePositivity.AlgebraicGeometry.openCoverCechRefinementCochains`
- `SerrePositivity.AlgebraicGeometry.openCoverCechRefinementCochains_apply`
- `SerrePositivity.AlgebraicGeometry.openCoverCechRefinementCochains_differential`
- `SerrePositivity.AlgebraicGeometry.openCoverCechRefinementMap`
- `SerrePositivity.AlgebraicGeometry.openCoverCechCoefficientMap`
- `SerrePositivity.AlgebraicGeometry.openCoverCechRefinementCochains_naturality`
- `SerrePositivity.AlgebraicGeometry.openCoverCechRefinementCochains_id`
- `SerrePositivity.AlgebraicGeometry.openCoverCechRefinementCochains_comp`

### OpenCoverCechComparison

⑥ での追加コミット：`96e18ab78 feat(scheme): compare native projective Cech cohomology through common refinements`。

- `SerrePositivity.AlgebraicGeometry.openCoverCechRefinementH`
- `SerrePositivity.AlgebraicGeometry.openCoverCechCoefficientH`
- `SerrePositivity.AlgebraicGeometry.openCoverCechComparisonIso`
- `SerrePositivity.AlgebraicGeometry.openCoverCechComparisonIso_naturality`
- `SerrePositivity.AlgebraicGeometry.openCoverCechRefinementH_eq`
- `SerrePositivity.AlgebraicGeometry.openCoverCechComparisonIso_choice`
- `SerrePositivity.AlgebraicGeometry.openCoverCechComparisonIso_refine`
- `SerrePositivity.AlgebraicGeometry.openCoverCechComparisonIso_trans`

### OpenCoverCechEvaluation

⑥ での追加コミット：`ecd5061a5 feat(ag): add affine Cech exactness and refinement comparison tools`。

- `SerrePositivity.AlgebraicGeometry.openCoverCechEvaluateAt`
- `SerrePositivity.AlgebraicGeometry.openCoverCechEvaluateAt_single`
- `SerrePositivity.AlgebraicGeometry.openCoverCechEvaluateAt_restrict`
- `SerrePositivity.AlgebraicGeometry.openCoverCechEvaluateAt_boundary_single`
- `SerrePositivity.AlgebraicGeometry.openCoverCechEvaluateAt_boundary`
- `SerrePositivity.AlgebraicGeometry.openCoverCechEvaluateAt_naturality`

### OpenCoverCechRefinementHomotopy

⑥ での追加コミット：`ecd5061a5 feat(ag): add affine Cech exactness and refinement comparison tools`。

- `SerrePositivity.AlgebraicGeometry.openCoverCechRefinementHomotopyTerm`
- `SerrePositivity.AlgebraicGeometry.openCoverCechRefinementHomotopyTerm_zero`
- `SerrePositivity.AlgebraicGeometry.openCoverCechRefinementHomotopyTerm_boundary`
- `SerrePositivity.AlgebraicGeometry.openCoverCechRefinementHomotopyTerm_identity`

### OpenCoverCechRefinementIndependence

⑥ での追加コミット：`ecd5061a5 feat(ag): add affine Cech exactness and refinement comparison tools`。

- `SerrePositivity.AlgebraicGeometry.openCoverCechRefinementHomotopyComponent`
- `SerrePositivity.AlgebraicGeometry.openCoverCechRefinementHomotopyComponent_succ`
- `SerrePositivity.AlgebraicGeometry.openCoverCechRefinementHomotopy`
- `SerrePositivity.AlgebraicGeometry.openCoverCechRefinement_homologyMap_eq`

### OpenCoverCechRefinementNaturality

⑥ での追加コミット：`ecd5061a5 feat(ag): add affine Cech exactness and refinement comparison tools`。

- `SerrePositivity.AlgebraicGeometry.openCoverCechRefinementMap_naturality`
- `SerrePositivity.AlgebraicGeometry.openCoverCechRefinementMap_id`
- `SerrePositivity.AlgebraicGeometry.openCoverCechRefinementMap_comp`
- `SerrePositivity.AlgebraicGeometry.openCoverCechRefinement_homology_naturality`

### ProjectiveFilteredComplexStage

⑥ での追加コミット：`6039dfe45 feat(scheme): identify canonical finite-stage maps in filtered Cech H`。

- `SerrePositivity.AlgebraicGeometry.projectiveFilteredComplexStageIso`
- `SerrePositivity.AlgebraicGeometry.projectiveFilteredComplexShortComplexIso_ι`
- `SerrePositivity.AlgebraicGeometry.projectiveFilteredComplexHomologyIso_ι`
- `SerrePositivity.AlgebraicGeometry.projectiveFilteredComplexHomologyIso_ι_canonical`

### ProjectiveFilteredHomology

⑥ での追加コミット：`df7c1d105 feat(scheme): compare filtered Cech homology and localized coefficient diagrams`。

- `SerrePositivity.AlgebraicGeometry.projectiveFilteredShortComplexDiagram`
- `SerrePositivity.AlgebraicGeometry.projectiveFilteredShortComplexHomologyDiagramIso`
- `SerrePositivity.AlgebraicGeometry.projectiveFilteredShortComplexHomologyIso`
- `SerrePositivity.AlgebraicGeometry.projectiveFilteredComplexShortComplexIso`
- `SerrePositivity.AlgebraicGeometry.projectiveFilteredComplexHomologyIso`

### ProjectiveFilteredHomologyInclusions

⑥ での追加コミット：`c9430d14d feat(scheme): verify filtered Cech comparisons on colimit inclusions`。

- `SerrePositivity.AlgebraicGeometry.projectiveFilteredColimitInclusion`
- `SerrePositivity.AlgebraicGeometry.projectiveFilteredShortComplexHomologyInclusion`
- `SerrePositivity.AlgebraicGeometry.projectiveFilteredShortComplexHomologyIso_ι`

### ProjectiveFilteredHomologyNaturality

⑥ での追加コミット：`df7c1d105 feat(scheme): compare filtered Cech homology and localized coefficient diagrams`。

- `SerrePositivity.AlgebraicGeometry.projectiveFilteredShortComplexHomologyDiagramIso_naturality`
- `SerrePositivity.AlgebraicGeometry.projectiveFilteredShortComplexHomologyIso_naturality`
- `SerrePositivity.AlgebraicGeometry.projectiveFilteredComplexShortComplexIso_naturality`
- `SerrePositivity.AlgebraicGeometry.projectiveFilteredComplexShortComplexIso_inv_naturality`
- `SerrePositivity.AlgebraicGeometry.projectiveFilteredComplexHomologyIso_naturality`

### SchemeCechPreimage

⑥ での追加コミット：`96e18ab78 feat(scheme): compare native projective Cech cohomology through common refinements`。

- `SerrePositivity.AlgebraicGeometry.schemeCechPreimageCoefficientIso`
- `SerrePositivity.AlgebraicGeometry.schemeCechPreimageComplexIso`
- `SerrePositivity.AlgebraicGeometry.schemeCechPreimageRefinement_naturality`
- `SerrePositivity.AlgebraicGeometry.schemeCechPullbackMap`
- `SerrePositivity.AlgebraicGeometry.schemeCechPullbackMap_refinement`
- `SerrePositivity.AlgebraicGeometry.schemeCechPullback_homology_refinement`

### SchemeCechPullbackComparison

⑥ での追加コミット：`96e18ab78 feat(scheme): compare native projective Cech cohomology through common refinements`。

- `SerrePositivity.AlgebraicGeometry.schemeCechPullback_comparison_naturality`

## AlgebraicGeometry 外の利用

検索に使った 69 宣言の名前表は [名前表](scheme-w1-2f-universe-api-names.txt)。実行時は worktree の `scheme-drafts/2f-universe-api-names.txt` に同じ内容を置いて検索し、この報告とともに追跡済みの名前表にも保存した。

指定の全枝と main、自分の枝について、以下を各スナップショットのコミットで実行した。BS・KST・他レーンの本体、`formalization-plans/` の追跡済み `.lean` 下書きも検索対象である。境界を付けない固定文字列検索なので、完全修飾名・親宣言に付随する `.eq_def` や `_assoc` 等の利用も拾う。

```zsh
git grep -n -F -f formalization-plans/stage-ii/scheme-drafts/2f-universe-api-names.txt COMMIT -- '*.lean' ':(exclude)SerrePositivity/AlgebraicGeometry/**'
```

| 枝 | 確認したコミット | 外部の一致行数 |
| --- | --- | ---: |
| `HEAD` | `0deb4d5dc27624d7add3f066f006365f138d3da5` | 0 |
| `main` | `44f965234161ec914f69b157d712c1e3ee52f3ab` | 0 |
| `math/bs-impl` | `b33bd04101f1c63ff2bd83206458684b25b6693f` | 0 |
| `math/inf-supply` | `4f5a0fb55c23a6dd996e7b687e0f6791c544beb0` | 0 |
| `math/inf-supply-b` | `8b0cc264477131b78d1f9f4c4ef6aab2c040c034` | 0 |
| `math/bs-m15` | `f4ba76432a05c3a9ac6adcf0a5d19afdbca97d1d` | 0 |

**結果：外部利用の一致は 0 行。** 条件に反する外部利用は見つからなかったので、2f の接続を続ける。

69 件すべてを同じ固定文字列の名前表に入れて各枝を検索したため、一覧の各宣言について結果は同じく 0（上の表が 0 の場合）。文書の説明中の参照は Lean の利用とは区別する。作業用の未追跡ログ・監査・採取器は公開 API の利用先に数えず、検証済み本体と追跡済み drafts を git grep の対象としている。

## 検証と凍結の扱い

変更した API と直接 importer の対象ビルドは route の `56197ed3a`・`e4c45d499`・`5236a01a6` の束で成功。以後の native な比較の対象ビルドでもこれらを利用している。停止点では最新の対象と登録、段全体の監査を改めて記録する。

B3 の追記 §13 は「凍結するのは main だけ」と明記している。自分の枝での入口登録は許されるので、前の route で登録を凍結後とした記載は修正する。main の取り込み・root ビルドは調整役が行う。`SchemePowerBlowup` と `SchemeCompositionDomination` は今回の型変更の対象外。B4 でその属性と重なる編集があれば追従時に解消する。
