# Codex 作業指示書 IF-W0-3：対象一覧（JSON）の作成と R61b の読解

作成：2026-10-29（∞ 基盤の整備、管理は Claude）。宛先：Codex。
計画：[infinity-foundation-plan.md](infinity-foundation-plan.md) の R74（対象 JSON）、§5 の各段、§6「指示書の単位」の IF-W0-3。
**前提**：IF-W0-1（`88c477612`）と IF-W0-2（`8ff0012d8`）は main に取り込み済み。道具の使い方は `scripts/refactor/README.md` と `scripts/refactor/targets/README.md`。
**共通の前提**：[IF-W0-1](infinity-codex-w0-1.md) §0。worktree は `../SerrePositivity-ifw0-3`、ブランチは `infra/if-w0-3`（main の最新から作る）。main の作業木では作業もビルドもしない。

この指示書は窓ごとに **4 回止まって報告する**（§7）。各回で Claude が JSON を確認・承認してから次へ進む。

## 1. 目的と成果物

W1〜W2c で「どのモジュールをどこへ移すか、どう分割するか」を、確定した一覧として作る。`.lean` は変更しない（検査のためのビルドと、`validate_targets.py` が `.lake` に書く記録は除く）。

| 成果物 | 内容 |
| --- | --- |
| `scripts/refactor/targets/w1.json`・`w2a.json`・`w2b.json`・`w2c.json` | 窓ごとの対象一覧（書式は targets/README.md） |
| `scripts/refactor/targets/w1.md`・`w2a.md`・`w2b.md`・`w2c.md` | 各項目の根拠（どの規則で、どの計測から決めたか）、**保留の一覧**（閉包が規則に収まらず、Claude の判断が要るもの）、窓の終わりの閉包の試算 |
| `formalization-plans/archive/if-w0-3-r61b-reading-2026-10-29.md` | R61b の読解の記録（§5） |
| `scripts/refactor/targets_builder.py`（任意） | 閉包の計測と JSON の下書きを作る補助。作る場合は試験も付ける |

## 2. 所有範囲

変更・新規作成してよいもの：`scripts/refactor/targets/` の下、`scripts/refactor/targets_builder.py` とその試験、上の archive 文書。
それ以外（`.lean` の本文、集約ファイル、監査、計画文書、`layers.json`）は変更しない。`layers.json` の変更が必要だと思ったら、変更せずに報告する。

## 3. 共通の作り方

### 3.1 情報源

- 入口の辺と閉包：`python3 scripts/refactor/layer_check.py --report`（`.lake/verify/layers.json`）。
- 群の定義（接頭辞の一覧と判定）：[外部調査](archive/infinity-outside-survey-2026-10-28.md) §2（L1〜L7・F1〜F3・Sp-S1〜S6・SC-C1〜C5）、[Verdier 計画](refactoring-verdier.md) §1.2、[R2-A 詳細](archive/r2-a-layers-2026-10-27.md)（R26・R27 の参照先）、計画 §4（入口の辺の表）。
- 本文の内容（分割が要るとき）：対象ファイルを読む。宣言の一覧は `decl_snapshot.lean` で採る。

### 3.2 規則

1. **移し先の名前**：`SerrePositivity.InfinityCategories.<層>[.<小区分>].<元のファイル名>`。小区分は計画 §3 の木（Stable/Verdier・Stable/Exact・Stable/Infinity・Stable/Lax・Stable/Semiorthogonal・Kan/Pointed・F1B/Localization・F1B/Localization/DwyerKan・F2/Filtered・ModelBridge）。名前が衝突するときは項目を保留にして報告する。
2. **move か split か**（モジュール単位の閉包で決める）：
   - そのモジュールの推移閉包が、移し先の層が import してよい範囲（計画 §3 の順序と `layers.json` の禁止）に収まるなら `move`。
   - 収まらないとき、原因が末尾の節（`variable [ModelCategory …]` 以降など）や少数の宣言に限られるなら `split`（`moved` に純粋な部分、`keep` にそれ以外。R72 は逆に、Model の節を `moved` にして ModelBridge へ出す）。
   - どちらでもないときは JSON に入れず、`.md` の保留の一覧に「モジュール・閉包が規則を破る原因の辺・案」を書く。
3. **閉包の試算は窓を積み重ねて行う**：w2a.json の検査は `validate_targets.py w1.json w2a.json` のように、前の窓の JSON も同時に渡す（移動後のグラフを前提にするため）。
4. **宣言名・名前空間は変えない**。改名が必要に見えるものは保留にする。
5. **archive の置き場**：`SerrePositivity.Archive.InfinityCategories.F2.FilteredExchange.<元のファイル名>`（ルートにも集約にも登録しない）。
6. JSON の `note` には「規則 §3.2-2 の判定・閉包の計測値・出典の群名」を 1 行で書く。長い根拠は `.md` へ。
7. 各窓の `.md` の末尾に、`validate_targets.py` の出力から「層の組ごとの違反の前後」「tier ごとの禁止閉包の前後」「入口の辺の前後」を写し、計画 §6 の窓の終わりの条件（W1：中核に DG・EInfinity なし／W2a：KST・モデル圏もなし／W2b：層の違反 0／W2c：増えない）に照らして、**満たすか・何が残るか**を書く。満たさない場合も JSON は作り、残る原因を保留の一覧に書く。

## 4. 窓ごとの対象

### 4.1 w1.json（W1：段 A・B と閉包の切断）

| 候補 | 対象の決め方 | 移し先 |
| --- | --- | --- |
| R48 | LI の `StableCategories`・`ExactEnrichment`・`StableInfinity`・`VerdierSequence`・`VerdierDiagrams`・`AdjointVerdier`（6 本）、`AdjointLocalization`（1 本） | Stable/Verdier（前 4 本）・Stable/Infinity（`StableInfinity`・`VerdierDiagrams`）・F1B/Localization（`AdjointLocalization`）。`ExactEnrichment` は Stable/Infinity |
| R49a | Derived の `ExactFunctorCategory`・`ExactFunctorCategoryEquivalence`・`StableVerdierSequence` | Stable/Exact（前 2 本）・Stable/Verdier |
| R49b | Derived の `ExactFunctorDescent`・`RestrictedDeformationLocalization` と依存先 `CofiberBottomIsoTransport`・`FullSubcomplexHomotopyLift`・`HomotopyPrecompVertex`・`RestrictedDeformationHomotopy` | 閉包で決める（Stable/Exact・F1B/Localization・F1B など）。R26 の 2 本（下）を先に含める |
| R26 | layer_check の F1 → F2 の入口の辺 28 本の参照先（r2-a の 13 本に、`F2.CatInfinity.SpecifiedHomotopyLift`・`SpecifiedFunctorEdgeLift` を加える） | 閉包で Core・F1・F1B へ。F2 に残すべき専門の内容があれば保留 |
| R39 | Stable → Derived 10 辺・F2 → Derived 7 辺の参照先（`SliceEvaluationPinched`・`RightFibrationTerminalRepresentation`・`RoofTargetFunctor` を含む）。`Stable.lean` → `Derived.CoherentBar.Compact.All` は集約の import の修正なので JSON に入れず、`.md` に「W1 の手作業」として書く | 閉包で Core・F1・F1B・Stable へ。DG を含む参照先は split を検討 |
| R66 | `DoldKanComparison.UniverseHomotopy`・`UniverseKan`、`DGNerve.JoinSimplexInclusions`・`JoinSimplexFaces`・`JoinVertexSurjectivity` | Simplicial。閉包に DG が残るものは split（純粋な補題を `moved`） |
| R71 | `KST.SConstruction.EnrichedFunctorCollageNerve`・`ContractibleKanProducts`、F1 → Derived 4 辺・HL → Derived 3 辺の参照先 | 閉包で決める |
| R53 の前提 | `F2/Idempotent/Retracts.lean`（`retractClosure`） | Core（閉包が収まらなければ split） |

- R59（入口の修正）・R62（private の解除）・R63（HA/ComplexLimits 3 本を EInfinity の既存の stub と統合）は JSON の対象外。`.md` に「W1 の手作業」として、対象ファイルと手順の案を書く。
- R61a（本文がほぼ一致する重複）は JSON の対象外。§5 の読解の記録に「削除する側・残す側・置換の対応」を書く（W1 では `move_module.py` の redirects で処理する）。
- **ここで止めて報告する（§7-1）。**

### 4.2 w2a.json（W2a：モデル圏の切り離しと取り込み）

| 候補 | 対象の決め方 | 移し先 |
| --- | --- | --- |
| R72 (1)(2) | HA の 12 本（計画 §5 段 C の R72 の一覧）。各ファイルを読み、Model の節（`variable [ModelCategory …]` 以降、または `ModelCategory` を使う宣言）を `moved`、純粋な部分を `keep` にした split。純粋な部分が丸ごと移せるときは、さらに別項目で Simplicial・Kan へ move（同じファイルに二つの分割を作用させない規約があるので、**この窓では Model の節の切り出しだけ**とし、純粋な部分の移動は w2b 以降の保留として記録する） | ModelBridge（`SerrePositivity.InfinityCategories.ModelBridge.HA.<元の名前>`） |
| R72 (3) | HL の Quillen 系 42 本（本文に `ModelCategory` を含む HL のファイル。IF-W0-2 の層検査で `code_contains` により判定できる） | ModelBridge（move） |
| R64 | 出所：F1/Simplicial、F1/KanModels、F1B/KanComplex、HA/Simplicial（Rectification を import しないもの）、KST/Spectra の Sp-S1・S2・S3・S5、SConstruction の SC-C3〜C5、KST/Comparison の Ex∞ と単体的ホモトピー（C1）、`SerrePositivity/Spectra/PointedSimplicialSet`・`Pointed`。<br>**判定はモジュール単位の閉包で行う**：閉包 ⊆ Simplicial の範囲なら Simplicial、⊆ Simplicial ∪ Core ∪ Kan なら Kan（基点付きの内容は Kan/Pointed）、それ以上に出るものは保留（この指示書では宣言単位の分割はしない）。quasicategory との比較（Core/KanCharacterization など、Core にすでにあるもの）は対象外 | Simplicial・Kan・Kan/Pointed |
| R27 | HL・F1 → KST.Spectra 27 辺の参照先 21 本。汎用の 17 本は R64 の規則で Kan へ。`Spectrum*` の 5 本は `SerrePositivity.KST.Spectra.Limits.<名前>` へ move（KST の中の移動） | Kan・KST/Spectra/Limits |
| R56a | LI の `LocalizationResolution`・`GeneralLocalization`・`LocalizationFactorization`・`LocalizationUniqueness`・`InverseAttachment*`・`WalkingEquivalence*`・`ParametricDiagramGluing`・`CoreAnodyneLifting`（`*` は接頭辞で展開し、一覧を `.md` に書く） | F1B/Localization。w1.json を前提にした閉包で、F2・straightening が消えることを確かめる。残るなら保留 |
| R65 | EInfinity/SimplicialLocalization・Hammock・FrameHom のモジュールのうち、閉包に DG・KST・EInfinity の operad 系（BarrattEccles・Surjection・Operad・IntervalCuts・TableReduction）・モデル圏のコードを含まないもの | 相対圏と hammock → F1B/Localization/DwyerKan、Ex∞・Thomason → Simplicial、frame・Quillen 定理 A の一般部分 → F1B または HL。`modelHammock_isLocalization` などモデル圏を仮定するものは ModelBridge |

- **ここで止めて報告する（§7-2）。**

### 4.3 w2b.json（W2b：FilteredExchange と層の逆辺）

| 候補 | 対象の決め方 | 移し先 |
| --- | --- | --- |
| R73 | F2/FilteredExchange の全モジュール（PiCriterion を除く 2,096 本）を、「FilteredExchange の外から推移的に使われるか」で二分する（IF-W0-2 の層検査の方法と同じ。集約 `F2.FilteredExchange` は根に含めない）。<br>使われる 369 本：filtered の定義（`FilteredInfinity`・`IsKappaFiltered`・`FilteredEquivalence`・`FilteredCosliceCofinality`・`KappaFilteredCoslices` など）は F2/Filtered、それ以外は閉包で Core・HL・F2 へ。<br>使われない 1,727 本：archive。<br>PiCriterion 33 本：`SerrePositivity.InfinityCategories.Derived.PiCriterion.<名前>` へ move | F2/Filtered・Core・HL・F2・Archive・Derived/PiCriterion |
| R37 | F1B → Stable 54・HL → Stable 50・F1 → Stable 23 の参照先（和集合） | 閉包で Core・Kan・F1B・Simplicial へ。Stable に残すべきもの（安定性を本質的に使うもの）は保留に書く |
| R38 | HL → F2 84 辺・Stable → F2 42 辺の参照先 | 閉包で下の層へ。sifted・PΣ の適用は F2 に残す（保留ではなく「残す」として `.md` に書く） |

- **ここで止めて報告する（§7-3）。**

### 4.4 w2c.json（W2c：KST の一般部分）

| 候補 | 対象の決め方 | 移し先 |
| --- | --- | --- |
| R51 | `KST.SConstruction.StableSpanPushout` と、その閉包にある SConstruction の 2 本 | Stable |
| R52 | LI の `Verdier*`、KST/Fibration の `Weak*`・`Fraction*`・`FixedFraction*`、LI の `Tamme*`（接頭辞で展開し、外部調査 §2 の L3・F2・L2 の説明と照らして、分数・Ore・span に関するものだけを選ぶ。`Φ : StableInfinity ⟶ Sp` や BF を使うものは除く） | Stable/Verdier/Fractions |
| R68 | LI の `Lax*`・`IdentityLax*`・`PullbackStableCategory`・`SemiorthogonalDecomposition`（L1、約 56 本）。Sp に値をとる系は除く | Stable/Lax・Stable/Semiorthogonal |
| R69 | LI の L6（`Cofiber*`・`Exact*`・`Suspension*`・`FullStableClosure`・`ZeroCategory`・`FiberSquare*` など）と L7（`Arrow*`・`Adjunction*`・`Opposite*`・`Reflective*`・`Square*`・`Simplex*`・`Cocone*`・`Curry*`・`Relative*`）。BF fiber を使う約 20 本は除く | Stable・Core・F1B |
| R70 | KST/Fibration の F3（`Straightening*`・`Scaffold*`・`Transport*`・`Strict*`・`Small*`・`Space*`・`Kan*`・`Coslice*`・`FunctorIso*`・`Pointed*`・`GroupoidCompletionKan*`・`Localized*`）と LI の `CoreFlag/` | F1・F1B |
| R56b | LI の `GroupoidCompletion*`・`SimplexAttachment*` | F1B/Localization（w1〜w2b を前提にした閉包で決める。DG・KST.Fibration が残れば保留） |

- **ここで止めて報告する（§7-4）。**

## 5. R61b の読解の記録

`formalization-plans/archive/if-w0-3-r61b-reading-2026-10-29.md` に、次の組について書く。

| 組 | 片方 | もう片方 |
| --- | --- | --- |
| 1 | `InfinityCategories/F1/Universe/PinchedHom` | `F1B/Localization/UniversePinchedHom` |
| 2 | `KST/SConstruction/RelativeInitialExtension` | `F1B/FunctorCategories/RelativeInitialExtension` |
| 3 | `KST/SConstruction/CoreTrivialFibration` | `F2/CatInfinity/CoreTrivialFibration` |
| 4 | `KST/SConstruction/TrivialFibrationStability` | `Stable/TrivialFibrationStability` |
| 5 | `KST/SConstruction/PushoutTranspose` | `Stable/SquareTranspose` |
| 6 | `KST/SConstruction/InitialBoundaryIso` | `F1B/Cofinality/InitialBoundaryIso` |
| 7 | `KST/SConstruction/EdgeTargetColimit` | `HomotopyLimits/EdgeTargetCocone` |
| 8 | `LI/SuspensionExactFunctor` | `Stable/Suspension` |
| 9 | `LI/AdjunctionOfOpposite`・`OppositeAdjunction` | `Stable/AdjunctionOpposite` |
| 10 | `EInfinity/FrameHom/LocalizationExtension.localization_extension_exists` | `F1B/Localization/UniversalConsequences.IsLocalization.exists_extension` |
| 11 | Ex∞：`EInfinity/Hammock/ExInfinity*` | `KST/Comparison/ExInfinity*` |
| 12 | MappingCylinder：`KST/Comparison/MappingCylinder*` | `F1B/Diagrams/MappingCylinder*`・`F1/MappingSpaces/MappingCylinder*` |
| 13 | `KST/Spectra/CoherentTrianglePathMinimum` | `F2/FilteredExchange/CoherentTrianglePathMinimum`・HL に同名があれば |
| 14 | `KST/Spectra/LastHornContraction` | `F1B/Fibrations/LastHornContraction` |
| 15 | `KST/Spectra/HomotopyProduct` | `HomotopyLimits/KanPiProducts` |

各組について：両方の主な宣言とその主張（数学の言葉で 1〜2 行）、本文の一致率（コメントを除いた行の一致の割合）、判定（**同一**＝片方を削除して置換できる／**特殊化**＝一方が他方から導ける。どちらをどう導くか／**比較の定理が要る**＝型や模型が違う。段 G の M10 へ）、提案する処置。
組 1・2 は「同一」の見込みなので、置換の対応（削除する側の宣言名 → 残す側の宣言名）も書く。

## 6. 受入条件

1. `validate_targets.py` が、`w1.json`、`w1.json w2a.json`、`w1.json w2a.json w2b.json`、4 本すべて、の 4 通りで終了コード 0。各出力を `.lake/verify/targets-w*.json` に保存し、要点を各 `.md` に写す。
2. 各 `.md` に、規則 §3.2-7 の閉包の前後と、窓の終わりの条件の判定が書いてある。
3. 保留の一覧が、各 `.md` に理由つきで書いてある。
4. §5 の記録が 15 組すべてについて書いてある。
5. `git status` で、変更が §2 の所有範囲だけであること。`.lean` の差分がないこと。
6. `targets_builder.py` を作った場合は、その試験が通ること。

## 7. 止めて報告する点

1. w1.json と w1.md を作り、`validate_targets.py w1.json` が通った後。
2. w2a.json と w2a.md（w1 を前提）の後。
3. w2b.json と w2b.md の後。
4. w2c.json と w2c.md、§5 の記録、§6 の 1〜6 の後。この報告の後に Claude が承認してから §8 のコミットを行う。

各報告には、項目数（move／split／archive／保留の件数）、閉包の前後の表、保留の一覧の要約、判断が要る点を書く。

## 8. コミット

一つのコミットにする（§7-4 の承認の後）。

```bash
set -o pipefail
git commit --only scripts/refactor/targets formalization-plans/archive/if-w0-3-r61b-reading-2026-10-29.md \
  scripts/refactor/targets_builder.py scripts/refactor/test_targets_builder.py \
  -m "$(cat <<'MSG'
docs(refactor): target lists for windows W1-W2c and the R61b reading record (IF-W0-3)

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
MSG
)"
```

（`targets_builder.py` を作らなかった場合は、その 2 パスを外す。）

## 9. 禁止事項

- `.lean` の本文・集約・監査・計画文書・`layers.json` の変更。
- 閉包の規則に合わないものを、保留にせず JSON に入れること。
- 宣言名・名前空間の変更を前提にした項目を作ること。
- main の作業木での作業・ビルド。

## 10. 追記（2026-10-29、§7-1 の報告への判断）

§7-1 の報告（move 27・保留 22、W1 の終了条件は未達）を受けて、次を決めた。

### 10.1 判断

1. **R66 の移し先は Core に変える。** `DGNerve.JoinSimplexInclusions`・`JoinSimplexFaces`・`JoinVertexSurjectivity` は Core の join・pullback の補題を使うので Simplicial には収まらない（計画 §3 では「Core：join と slice」なので Core が正しい）。`DoldKanComparison.UniverseHomotopy` は、純粋な部分（`uliftHomotopy`・`ulift_homotopyEquivalence` など）を `Core.UniverseHomotopy` へ split し、残りは DoldKanComparison に残す。
2. **R61a の組 1**：`F1/Universe/PinchedHom` を残す（宇宙の持ち上げの置き場として正しい）。ただし import は閉包の小さい `F1B/Localization/UniversePinchedHom` のもの（`Core.UniverseSSetMaps`）に揃える（import 行だけの変更）。F1B 側は削除し、名前空間の違い（`LocalizationUniverse`）は `move_module.py` の symbols で対応する。
3. **後の窓で解消する保留は W1 から外す**：#4（`FilteredSpaceBridgeInput`）は R73 で PiCriterion が中核の外へ出れば消える（W2b）。#22（`EnrichedFunctorCollageNerve`）は、入口の `HL/QuillenCfCollage` が R72(3) の Quillen 系 42 本に含まれるなら W2a で消える（含まれるか確かめて報告）。#10 も、入口の HL 側が Quillen 系なら同様。
4. **分割の検証を許可する**：worktree の中で一時的に `split_module.py --apply --prune-imports` を行い、縮めた import・snapshot・保存検査・影響するモジュールのビルドの結果を取ってから、**元に戻す**。この証拠をもとに JSON に split を入れてよい。IF-W0-2 の試験 C と同じ扱い（終わったら復元、コミットしない）。

### 10.2 規則の追加（§3.2 に加える）

8. **入口の辺の切り方は三通りを比べる。** 中核のモジュール \(u\) が禁止側のモジュール \(v\) を import する辺 \(u \to v\) について：
   - **(a) 下ろす**：\(v\) と、\(v\) の閉包のうち移し先の層より上にあるモジュールの集合 \(S(v)\)（pull-down 集合）を一緒に下ろす。\(S(v)\) の各モジュールの閉包が DG・KST・モデル圏を含まないことが条件。\(|S(v)|\) を報告する。**\(|S(v)| > 60\) なら JSON に入れず報告だけにする。**
   - **(b) 上げる**：\(u\) を中核より上の層（Derived など、\(u\) の利用元と同じ層）へ移す。条件は、中核の中に \(u\) の利用元（推移的）がないこと。\(u\) の利用元の一覧を報告する。
   - **(c) 分ける**：\(u\) または \(v\) の少数の宣言だけが原因なら split（10.1-4 の証拠つき）。
   三つの候補の大きさ（移す本数・分割する宣言数）を並べ、最も小さいものを JSON に入れる。甲乙つけがたいときは保留にして両案を書く。
9. **手作業の影響も試算に入れる**：`targets_builder.py` に、import グラフから辺を除く模擬（`--remove-edges`。R39 の `Stable.lean` → `Derived.CoherentBar.Compact.All`、R59 の入口の変更など）と、後の窓の JSON を前提にする模擬を加え、W1 の終了条件（中核の閉包に DG・EInfinity なし）を**手作業を含めた状態で**判定する。
10. **validate_targets.py の拡張を許可する**：項目に任意の 9 番目のフィールド `"imports"`（split 後の両ファイルの import の一覧。10.1-4 の証拠から写す）を認め、模擬のグラフでその import を使う。`targets/README.md` と試験も合わせて直す。**所有範囲に `scripts/refactor/validate_targets.py`・`split_module.py`・`targets/README.md`・対応する試験を加える。**

### 10.3 保留 22 件の処置

| 番号 | 処置 |
| --- | --- |
| 1・2・3（Join 系） | 移し先を Core にして move（10.1-1） |
| 10（UniverseHomotopy） | 入口の HL 側が Quillen 系なら W2a へ。そうでなければ Core へ split（10.1-1、証拠つき） |
| 4 | W2b（R73）へ |
| 22 | 入口が Quillen 系なら W2a（R72）へ。そうでなければ規則 8 で比べる |
| 7・8・9（roof 系、Stable → Derived） | 規則 8 の (b) を優先して調べる：`Stable.SliceEvaluationNaturality`・`LoopCospanRepresentation`・`TerminalRightFibrationComparison` の中核内の利用元を列挙し、なければ Derived へ上げる案を出す。(a) の \(S(v)\) は 1,600 本規模なので、下ろす案は採らない |
| 5・6（F1・HL → Derived） | 規則 8 の (a)(b) を比べる |
| 11〜21（R26 の F2 参照先） | 規則 8 の (a)(b) を比べる。(a) の pull-down 集合は F2/CatInfinity・FilteredExchange の中で閉じるはずなので、その大きさを報告する。13・21 の split 案は 10.1-4 の証拠を取ってから判断する |
| 14・16（SpecifiedSimplexEdge・FunctorIsoWhiskerUnit が原因） | 原因のモジュール自身の閉包が Core に収まるなら、追加の move として入れてよい（規則 8 の (a) で \(|S| \le 60\)） |

処置の後に `validate_targets.py` を通し直し、規則 9 の模擬で W1 の終了条件を判定して、改めて §7-1 の報告をする。

### 10.4 追記（10-29、改訂版 §7-1 の途中停止への判断）

1. **所有範囲の追加**：`scripts/refactor/decl_snapshot.lean`・`compare_snapshots.py`・`prune_imports.py` と、それらの試験。この指示書の作業に必要な範囲で直してよい。
2. **空になる側の保存検査**：`decl_snapshot.lean` は、選択した宣言が 0 件でも例外にせず、空のスナップショット（`count: 0`）を書いて終了コード 0 にする。`compare_snapshots.py` は空のスナップショットを正しく比べる（消えた宣言・増えた宣言として扱う）。
3. **全部の宣言が移るなら split ではなく move**：`UniverseHomotopy` は 2 宣言とも純粋なので、`Core.UniverseHomotopy` への **move** にする。過大な import は `imports` フィールドで縮める。
   - `imports` フィールドは move の項目にも認める（移動後のモジュールの import の一覧）。
   - 証拠は、worktree でその場で `prune_imports.py` を当てる（モジュール名は変えない）→ ビルド → 前後の snapshot の比較 → 復元、の手順で取る。
4. **roof 系（Stable → Derived の 3 本）は宣言単位で分析する**。上げる案は条件を満たさない（中核の利用元 52〜55 本）ので、(c) 分ける案を調べる。
   - `decl_snapshot.lean` に、宣言ごとに「使っている定数が属するモジュールの集合」（`uses_modules`）を出力する機能を加える。
   - 入口側の各ファイル（`Stable.SliceEvaluationNaturality`・`LoopCospanRepresentation`・`TerminalRightFibrationComparison`）について、
     (i) 禁止側（Derived 以上）の定数を使う宣言の集合 \(D_{\mathrm{forb}}\)、
     (ii) 中核のモジュールから参照される宣言の集合 \(D_{\mathrm{core}}\)（中核のモジュールの本文で名前を検索する）、
     を求める。
   - \(D_{\mathrm{forb}} \cap D_{\mathrm{core}} = \varnothing\) なら、\(D_{\mathrm{forb}}\) を `Derived.<元の名前>Roof` などへ上げる split を JSON に入れる（証拠は 10.1-4 の手順）。
   - 交わるなら、どの中核の利用元がどの宣言を使い、その宣言が何を経由して Derived に届くかの鎖を報告して止める。
5. 同じ宣言単位の分析は、R26 の保留（11〜21）のうち (a)(b) がどちらも大きいものにも使ってよい。

### 10.5 追記（10-29、roof 系の鎖への判断）

宣言単位の分析で、`TerminalRightFibrationComparison`・`TerminalComparisonFiberTransfer` の中核から使われる宣言が、Derived の roof の一般論（`roofSliceEvaluationHomotopy_*`・`roofTargetSliceMap_*`）に本当に依存していることが分かった。
roof（slice の中の屋根）は dg と無関係な ∞ 圏の一般論であり（Derived の `Roof*`・`Pinched*`・`FunctorSlice*` など）、Verdier 計画 §2 でも Stable/Verdier/Fractions へ移す予定だったものである。そこで、**roof の塊ごと下ろす**方針で調べる。

1. **roof の塊の確定**：3 本の参照先（`SliceEvaluationPinched`・`RightFibrationTerminalRepresentation`・`RoofTargetFunctor`）から始めて、Derived の中の推移閉包をとる。各モジュールを、本文の語彙（`DG`・`dg`・`Cochain`・`Module`・`Complex` など。IF-W0-2 の層検査の `code_contains` の方式）で「dg を含まない」か判定し、含まないものの集合を roof の塊 \(C\) とする。\(|C|\) と、含むと判定されたモジュールの一覧を報告する。**規則 8 の 60 本の上限は、この分析には適用しない**（大きさを測ることが目的）。
2. **塊から外への漏れ**：\(C\) のモジュールが直接 import する、\(C\) の外の Derived・DG・DGNerve・DoldKanComparison・KST のモジュールを列挙する。それぞれについて、その import が本当に使われているか（`uses_modules` で、そのモジュールの定数を使う宣言があるか）を調べ、「縮められる（使っていない）」「使っている（どの宣言が）」に分ける。縮められるものは、その場で `prune_imports.py` を当てて確かめる（復元する）。
3. **移し先**：\(C\) 全体の閉包（漏れを縮めた後）が Core・Simplicial に収まれば `Core.Roof.<名前>`、F1・F1B が要るなら `F1B.Roof.<名前>`、Stable が要るなら `Stable.Verdier.Fractions.<名前>`。塊の中で層が分かれるなら、層ごとに分ける。
4. **判断の材料として報告する**：\(|C|\)、漏れの一覧（縮められる／使っている）、移し先の案、使っている漏れがある場合はその宣言と、それを切るための分割案。この報告の後に Claude が、塊を W1 に入れるか W2c（R52）に回すかを決める。
5. **他の作業は止めない**：roof 系の 3 辺は「分析中の保留」として w1.json の外に置き、残り（UniverseHomotopy の move、三案の比較、改訂 JSON の検査、手作業込みの W1 判定）を進めて、改訂版 §7-1 の報告をする。報告には roof の分析を別の節として含める。

### 10.6 追記（10-29、import の縮小で下流が壊れた件と roof の語彙判定）

1. **下流の直接 import の補充を道具に組み込む**：`prune_imports.py` は、縮めた後に影響する下流のモジュールをビルドし、`public import` の再公開に頼っていたために壊れた下流には、**使っている分の直接 import を足して**ビルドし直す。足した import は出力の計画（`downstream_imports`：モジュール → 追加した import の一覧）に記録する。証拠の試行（10.1-4）ではこの補充も含めて行い、復元する。
   - 対象 JSON には任意のフィールド `"downstream_imports"`（上と同じ形）を認め、`validate_targets.py` の模擬グラフでも使う。`targets/README.md` と試験を直す。
   - `UniverseHomotopy` の件は、`ResolutionComparisonEquivalence`（または実際に壊れた `ComparisonEquivalence`）への直接 import の追加で解消する見込み。試行で確かめて記録する。
2. **roof の語彙判定を直す**：10.5-1 で挙げた `Complex`・`Module` は部分一致で `FullSubcomplex`・`Subcomplex`（quasicategory の基本 API）に当たり、一般論を「dg を含む」と誤判定する。判定は**識別子の境界**で行い、次の語だけを dg の印とする：`DG` または `dg` で始まる識別子（`DGCategory`・`DGFunctor`・`dgNerve`・`dgClosedEdge` など。ただし `dg` 単独の綴りが別の語の一部になる場合は除く）、`Cochain`、`HomologicalComplex`、`ChainComplex`、`ModuleCat`、`CommRing`、`Bimodule`。`Subcomplex`・`FullSubcomplex`・`Simplex`・`Complex`（単独）は印にしない。この規則で \(C\) を取り直し、\(|C|\)・除外の一覧・漏れの辺を報告し直す。
3. 上の二つを直したうえで、10.5 の 2〜5 を進める。

### 10.7 追記（10-29、roof の判断と、外部定義の生成補題）

**roof の判断（§10.5-4 への回答）**
1. **prune 後に 3 入口が必要とする 15 本を W1 に入れる**（R39 の pull-down として）。移し先は閉包の表のとおり層ごとに決め、名前は統一して `<層>.Roof.<元の名前>`（`Core.Roof`・`F1B.Roof`・`Stable.Roof`）とする。`Stable.Verdier.Fractions` 案のものも当面は `Stable.Roof` に置く（R52 で Fractions へまとめるかは W2c で判断）。
2. 既存の W1 の move と重なる 6 本は、既存の項目を優先し、重複した項目は作らない。
3. 15 本に入らない C の残り（`SpanUnknownIndex`・`SpanIndexGeometry` を含む 8 本）と、`SpanSuffixIndex` の追加 split 案は、**W2c（R52）に回す**。w1.md の保留に「W2c へ」と書く。
4. 2 本の prune（`FirstTriangleIndex`・`RoofPinchedSlicePostcomp`）と、それに伴う下流の直接 import の補充は、`imports`・`downstream_imports` フィールドで JSON に入れる。
5. roof の 15 本を含めた状態で、手作業込みの W1 の終了条件を判定する。

**外部定義の生成補題（`functorEqIso.eq_1` など）**
6. 所有範囲に `scripts/refactor/lean_source.py` とその試験を加える。
7. 規則：ソースにない定数は、環境の中で「その名前の最長の真の接頭辞で、宣言として存在するもの」を親とする。
   - 親が**同じモジュール**のソースの宣言なら、その親の補助宣言として扱う（いままでどおり）。
   - 親が**別のモジュール**（リポジトリ内の他のファイル、または Mathlib）の宣言なら、「外部定義の生成補題」（`eq_n`・`eq_def` など、使った場所で遅延生成されるもの）として扱う。分割では止めずに無視し（どちらの側でも必要なら再生成される）、保存検査では比較の対象から外して、別の一覧 `transient` に名前だけ記録する。
   - 親が見つからないものだけを、いままでどおりエラー（STOP）にする。
8. この規則で `FunctorIsoChainTransport` の分割の試行をやり直す。

**時間について**
9. 直列の試験が 7 時間かかっている。試行のビルドは影響するモジュールに限り（`lake build <module>`）、verify の全体実行は最後の 1 回だけにする。

### 10.8 追記（10-29、import だけを変える項目の書式）

1. §10.7-4 の訂正：`FirstTriangleIndex` は 15 本に入らないので、その prune は W1 には不要。移動も prune も W2c（R52）に回す。W1 の JSON に入れる prune は、15 本の中にあるもの（`RoofPinchedSlicePostcomp` など）だけ。
2. **書式に action `reimport` を加える**：モジュールは移動せず、その import の一覧を `imports` に置き換える項目。`dest` は `module` と同じ、`moved`・`keep` は空。`downstream_imports` も使える。`validate_targets.py` は模擬のグラフでその import を使う。`targets/README.md` と試験を直す。
3. `reimport` は次にも使う：R39 の `Stable.lean` から `Derived.CoherentBar.Compact.All` を外す修正、R59 のルート・`F2.lean` の入口の変更（import の追加・削除）。これで「手作業」だった項目の多くが JSON で表せ、§10.2 の規則 9 の `--remove-edges` の模擬は不要になる（作ってあれば残してよい）。
4. 入口ファイル（`Stable.lean`・`F2.lean`・ルート）への `reimport` は、保存検査の対象にしない（宣言を持たないため）。ビルドと層検査だけで確かめる。

### 10.9 追記（10-30、verify の環境の失敗への対処）

93d84541e での全体 verify は、(a) `audit_f5.lean:33` の古い宣言名（main の問題。担当レーンに修正を依頼済み）と、(b) 環境の失敗 3 件（"Too many open files in system"、`failed to open file`、toolchain の olean を一時的に開けなかったもの）で FAIL になった。(b) は他のレーンのビルドと 3 並列の Lean が重なった瞬間の一時的なものなので、道具で吸収する。

1. **所有範囲に `scripts/refactor/verify.sh`・`verify_runner.py` とその試験を加える。**
2. **環境の失敗の再試行**：監査・sorry 閉包の失敗のうち、エラー文が次に当たるものを「環境の失敗」とする：`Too many open files`、`failed to open file`、`object file '…' of module … does not exist`（実行後にそのファイルが存在する場合）。環境の失敗は、並列の実行がすべて終わった後に**直列で 1 回だけ**やり直す。やり直しが通れば成功に数え、summary に `retried` として記録する。通らなければ失敗のまま。
3. **重い監査は直列にする**：`audit_axioms.lean` と sorry 閉包は、並列の pool に入れず、pool が終わった後に直列で実行する。
4. 再試行は gate を変えない（gate:true のまま）。ただし再試行が 1 回でも起きた実行は、summary に件数を残す。
5. 試験：環境の失敗を模した監査（存在しない olean を開こうとするものなど）で、再試行の分岐と記録を確かめる。

### 10.10 追記（10-30、§7-1 の承認と、attribute コマンド・無名 instance の扱い）

**承認**：§7-1（8e6e75d8e、全体 verify PASS・gate:true・retried 0）を確認し、w1.json（move 62・split 3・reimport 3）と w1.md の保留 13 件を W1 の対象一覧として承認する。

**W2a の停止（`attribute [local instance]`・`attribute [instance]`・無名の local instance）への規則**

1. **宣言の位置で対応づける**：`decl_snapshot.lean` に、各宣言のソース上の位置（`Lean.findDeclarationRanges?` による開始行・終了行）を出力させる。`lean_source.py` は、ソースのコマンドと環境の宣言名を位置で対応づける。これにより、無名の `instance : T := …` は環境が付けた名前（`inst…`）で扱える。対象 JSON の `moved`・`keep` にはその名前を書く。
2. **`attribute [...] 名前` コマンドの扱い**（`attribute [-simp] …` の消去も同じ）：
   - 名前が同じファイルの宣言なら、その宣言と同じ側へ行く。新しいファイルでは、その宣言の直後に置く（元の順序は保つ）。
   - 名前が外部（他のファイル・Mathlib）で、`local`・`scoped` の属性なら、分割した両方のファイルに写す（section の有効範囲に注意し、元と同じ section の中に置く）。
   - 名前が外部で、グローバルな属性（`attribute [instance] 外部名` など）なら、`keep` 側に残す。`moved` 側の宣言がその属性に依存している可能性があるときは、分割せずに STOP して報告する（二重登録を避けるため、両方に写さない）。
3. **`open … in`・`set_option … in`・`variable … in` などの前置きつきコマンド**は、その本体の宣言と同じ側へ行く。
4. 上の規則の試験を `lean_source.py`・`split_module.py` の試験に加える（無名 instance、ファイル内の名前への attribute、外部名への local attribute、外部名へのグローバル attribute が STOP になること）。
5. これで W2a の preflight（R72 の 12 本の分割の試行）をやり直し、§4.2 を進める。

### 10.11 追記（10-30、属性が生成する宣言の帰属）

`@[reassoc]`（`…_assoc`）、`@[simps]`（`…_fst` など）、`@[elementwise]`（`…_apply`）のように、属性が生成する宣言は「親.子」の形ではないので、§10.7 の接頭辞の規則では親が見つからない。帰属の規則を次の順に広げる。

1. **位置による帰属（最優先）**：ソースにない定数の宣言位置（開始行）が、ソースのある宣言の範囲（属性の行を含む）に入っていれば、その宣言の補助宣言とする。
2. **接頭辞による帰属**：1 で決まらないとき、§10.7 の規則（最長の真の接頭辞）。照合の前に private 名を正規化する（`_private.<Module>.0.` を外す）。
3. **接尾辞による帰属**：2 でも決まらないとき、名前が `<親>_<接尾辞>` の形で、`<親>` が同じモジュールのソースの宣言、`<接尾辞>` が `assoc`・`apply`・`symm_apply`・`fst`・`snd`・`coe`・`hom`・`inv`・`inj`・`injEq` のいずれかなら、その親の補助宣言とする。
4. 親が別のモジュールにあるものは §10.7 のとおり「外部定義の生成補題」（transient）。
5. 1〜4 のどれでも決まらないものだけ STOP。位置も取れない証明補助の 1 件がこれに当たるなら、その名前と、どの宣言の証明の中で生成されたと推定されるかを報告する。
6. 試験：`@[reassoc]` 付きの補題を持つ一時モジュールで、`_assoc` が親に帰属すること、分割で親と一緒に移ること、保存検査で前後が一致することを確かめる。
