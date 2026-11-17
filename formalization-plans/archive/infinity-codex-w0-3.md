# Codex 作業指示書 IF-W0-3：対象一覧（JSON）の作成と R61b の読解

作成：2026-10-29（∞ 基盤の整備、管理は Claude）。宛先：Codex。
計画：[infinity-foundation-plan.md](stage-i/infinity-foundation-plan.md) の R74（対象 JSON）、§5 の各段、§6「指示書の単位」の IF-W0-3。
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
- 群の定義（接頭辞の一覧と判定）：[外部調査](infinity-outside-survey-2026-10-28.md) §2（L1〜L7・F1〜F3・Sp-S1〜S6・SC-C1〜C5）、[Verdier 計画](stage-i/refactoring-verdier.md) §1.2、[R2-A 詳細](r2-a-layers-2026-10-27.md)（R26・R27 の参照先）、計画 §4（入口の辺の表）。
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

### 10.12 追記（10-31、preflight の模擬は束で一回のビルドにする）

R72 の preflight（`r72-trials-2`）は、1 モジュールごとに「split-prune → 影響する下流（約 5,600 本）の全ビルド → 保存検査 → 元に戻してビルド」を回している。実測は 1 試行 3〜5 時間（`DiagonalFrame` の split-prune 17,812 秒、`Basic` 8,873 秒）で、9 試行の合計は 1 日を超える。HA/Simplicial の土台に触ると下流がほぼ全部再エラボレートされるので、この費用は試行の回数に比例する。

**8 本目（`QuillenStandardFrame`）は最後（restored-build）まで終え、9 本目（`StandardCosimplicial`、移す宣言 2 個）は始めない**（10-31 ユーザー判断）。試行の繰り返し（`r72-trials-2`、pid は `trials/pid`）は、8 本目の `restored-build` が終了コード 0 で終わり state.json の 8 本目が PASS になったら止める。もし 9 本目の split-prune が始まってしまっていたら、その場で止めて `git status` に出た変更（分割元の編集と分割先の新ファイル）を `git checkout -- <file>`・削除で元に戻し、報告に書く。`StandardCosimplicial` は W2a の束の模擬に含めて確かめる。R72 の preflight の報告（8 本 PASS、1 本は束へ）を §5 の形式で出す。W2a 以降の模擬には次の規則を使う。

1. **束で一回**：対象一覧の split・move を全部適用してから、下流のビルドを一回だけ行う。prune で壊れた下流への直接 import の補充（§10.6）も、その一回のビルドの失敗から一括で求める。保存検査は束の前後で全モジュール分をまとめて比べる。
2. **失敗したら二分**：束のビルドが失敗し、原因のモジュールが失敗の出力から特定できないときだけ、束を半分に割って繰り返す。
3. **途中の確認は直接 importer まで**：個々の split の形だけを確かめたいときは、分割した 2 本とその直接 importer だけを `lake build <module>` で見る。下流の全ビルドは束の最後の一回に限る。
4. **他の worktree と同時に全ビルドしない**：10-31 は dgw1・ifw0-3・main の 3 つの全ビルドが同時に走り、どれも単独の 2〜3 倍遅くなった（lean プロセス 31 本・34 GB）。全ビルドの前に `ps -axo command= | grep '[l]ake build'` で他の全ビルドがないことを確かめ、あるなら終わるのを待つか、§5 の報告に「待ち」と書く。

### 10.13 追記（10-31、R72 preflight の停止の承認と、DG 優先中の ∞ 側の作業）

**承認**：R72 preflight の停止報告（8 本 PASS、`StandardCosimplicial` は W2a の束へ、8 本とも復元済み、385 コマンドで想定外の失敗 0、所有範囲外の差分なし）を確認した。

**DG-W1 の取り込みが終わるまで、∞ 側はビルドを伴う作業をしない**（10-31 ユーザー判断：DG を優先）。その間にできることは次の二つ。

1. **道具の変更をコミットする。** worktree に未コミットの道具の変更（`scripts/refactor/{compare_snapshots.py, decl_snapshot.lean, lean_source.py, prune_imports.py, split_module.py}` の 10 本の修正と、`scripts/refactor/` の試験 12 本・`targets/` の 17 本・`formalization-plans/archive/` の 1 本）がある。§10.9〜10.11 の実装分と試行の記録なので、infra/if-w0-3 に `git commit --only` でコミットする（Lean のソースは含まないのでビルド不要）。試験 `python3 -m pytest scripts/refactor` または既存の `test_*.py` を通してから。コミットは「道具」「試験」「記録（targets・report）」の 3 本に分ける。
2. **W2a の束の計画（`targets/w2a.json`）をビルドなしで作る。** R72 の 12 本の split（preflight の plan.json を使う。`StandardCosimplicial` も含める）、W2a の move・reimport を一つの対象一覧にまとめ、`validate_targets.py` を通す。各項目の `downstream_imports` は preflight で分かった分を写し、未知のものは空にして束のビルドで補う。`w2a.md` に、束の実行手順（§10.12：全適用 → DG-W1 後の main を取り込み → `.lake/build` を main から複製 → 統合先と下流を一回ビルド → 保存検査 → verify）と、模擬に要る時間の見積もり（下流の本数 × 直近の実測）を書く。

**main の merge・`.lake/build` の複製・束の実行は、Claude が「DG-W1 を main に入れた」と伝えてから。** 複製は §5a の手順（`ps` で他の `lake build` がないことを確かめ、`rsync -a --delete ../SerrePositivity/.lake/build/ .lake/build/`、終了コード 23・24 で消えたのが書き換え中の出力だけなら受け入れる）。

**IF-W0-4 の内容の変更（10-31）**：`merge_modules.py` と、全ビルドの排他（`with_build_lock.sh`）・`.lake/build` の温め（`warm_build_dir.sh`）の道具は DG の Codex が DG-W2(a) で作る。IF-W0-4 に残るのは R75（削除 29 本）、`layers.json` への CategoryTheory／Coxeter の基盤登録、verify runner のメモリ予算つき並列化（監査ごとの RSS の記録、長い順、予算 45 GB、未記録は 20 GB と仮定）。

### 10.14 追記（10-31、W2a 草案の validator FAIL への回答：分割先の import は「使う利用元にだけ」）

**承認**：道具・試験・記録の 3 コミット（3a0134b59・c6ed978e2・86fd55f38）、W1 のルート import の更新（786 → 785）、W2a 草案（move 1,197・split 9・reimport 2、R72 の 3 本は分割不要）を確認した。validator FAIL で止めた判断は正しい。

**原因の確認**：`split_module.prepare` は、分割元を `public import` する利用元のすべてに分割先の import を足す。R72 の分割先は ModelBridge なので、中核の利用元（`IC.F2.Compact.WeakUniverse`・`IC.HomotopyLimits.KanTensorFrameAdjunction`）が、使ってもいない Model 側の宣言のために ModelBridge への辺を持つ。本文に移動宣言の使用はない。

**方針（承認）**：分割先の import は「機械的に全利用元へ」ではなく、**使う利用元にだけ**足す。

1. **既定を変える**：分割元の利用元には、分割先の import を**足さない**（`keep` 側を import し続けるだけ）。束のビルドで失敗した利用元にだけ、失敗の出力から分割先の直接 import を補う（§10.6 の `downstream_imports` の仕組みと同じ）。validate_targets の合成も同じ規則にする（自動追加を合成しない。`downstream_imports` に書かれた分だけ合成する）。
2. **中核の利用元が失敗したら STOP**：補充先が中核（Simplicial・Core・Kan・Coherent・F1・F1B・HomotopyLimits・Stable・F2・StablePresentable）なら、その利用元は Model 側の宣言を本当に使っている。これは R72 の「Model の宣言」の分類の誤りか、その利用元自身が ModelBridge に属するべきかのどちらかなので、補充せず止めて報告する（利用元・失敗した宣言・使っている移動宣言の名前）。
3. **中核でない利用元**（HA・EInfinity・KST・Sp）への補充はそのまま行う（層の規則に反しない）。
4. 道具の変更（`split_module.py`・`validate_targets.py`・`targets/README.md`）と試験（中核の利用元に import が足されないこと、ビルド失敗からの補充が中核で止まること）を加え、w1.json＋w2a.json の静的検査を再実行する。禁止辺 2 本と閉包の増加が消えて PASS になるはず。それでも増える根があれば、その鎖を報告する。

**束の構成（提案、ユーザー確認待ち）**：W1 を未適用のまま W2a と一つの束にする案（草案の前提）に加えて、**R79（HA 約 600・CT 12・ArrowFactorization 3 の docstring の書き換え）と IF-W0-4 の R75（削除 29 本）も同じ束に入れる**。HA の docstring を変えると HA の下流（ほぼ全部）が再ビルドになるので、別の窓にすると全ビルドが一回増える。束の下流は約 20,000 本、単独なら 1 本 1.0〜1.5 秒として 6〜8 時間（草案の 12.56 時間は 3 セッション同時の実測に基づく過大な見積もり）。この束を適用してから verify を通すまで、main の HA・∞・KST・EInfinity 側には他セッションの取り込みを入れない（論文の層のコーディネータに 1 日の凍結を依頼する）。

**順序**：DG-W1 を main に入れる（10-31）→ ∞ 側は main を取り込み `.lake/build` を複製 → 上の 1〜4 を実装して静的検査 PASS → 束の適用 → 下流の一回ビルド（機械を独占。DG 側はその間、ビルドの要らない道具の作業 DG-W2(a)）→ 保存検査 → verify → 取り込み。DG-W2(b) の束のビルドは、その後。

### 10.15 追記（10-31、§10.14 の実装の承認と、束の構成の確定）

**承認**：§10.14 の実装（分割先 import の自動追加の廃止、`downstream_imports` だけの合成、中核への補充は STOP、`prune_imports.py` の補充経路への接続）、Python 試験 150 件 PASS、W1（68 項目）と W1＋W2a（1,276 項目）の静的検査 PASS、増加指標 2,410 → 0 を確認した。

**束の構成（ユーザー承認済み、10-31）**：R79 ＋ R75 ＋ W1 ＋ W2a を一つの束にする。順序と機械の使い方は §10.14 のとおり（DG-W1 の取り込み → main の merge → `.lake/build` の複製 → 束の適用 → 下流の一回ビルド → 保存検査 → verify）。論文の層のコーディネータには、束の適用から verify までの約 1 日、HA・CT・HotA・∞・KST・EInfinity・ルート・それらの監査への取り込みを止めてもらう（Claude が依頼済み。開始時刻は Claude が伝える）。

**DG-W1 の取り込みを待つ間にする作業（ビルドなし）**

1. §10.14 の道具・試験・記録（w2a.json・w2a.md）を infra/if-w0-3 に 3 コミットでコミットする（`git commit --only`）。
2. **R79 の準備**：[計画の R79 行](stage-i/infinity-foundation-plan.md) の規則で、`k-theory.md` を参照する docstring（HA 約 600・CT 約 20・Spectra 1 の `[plan]: …/formalization-plans/k-theory.md`）を `…/formalization-plans/archive/k-theory-v1.md#<§396 の見出しのアンカー>` へ、`k-theory-generalization-inventory.md` を参照する docstring（`[inventory]: …`、618＋16 件）を `archive/k-theory-generalization-inventory.md` へ（`#mNNNN`・`layout-execution` のアンカーはそのまま）、ArrowFactorization・ArrowFactorizationCategory・ArrowFactorizationTransport の 3 本も同じ規則で、書き換える**スクリプトを作り dry-run で件数を出す**（期待：618／618＋16／3。食い違えば報告）。相対パスの深さは保ち、`formalization-plans/<名前>.md` の部分だけを替える。DG の 530 本は対象外（DG 計画 D5）。アンカーは GitHub の規則で生成し、`archive/k-theory-v1.md` に §396 の見出しがあることを確かめる。実際の書き換えは束の適用のときに行い、文書ごとに 1 コミット（計 2 本＋ArrowFactorization は HA 側のコミットに含める）。
3. **R75 の準備**：[計画の R75 行](stage-i/infinity-foundation-plan.md)（CategoryTheory/Presentation の 15 本、Quiver/WeightedPaths・WeightedPathMaps、トップ階層の殻 8 本など計 29 本）の削除対象を一覧にし、**importer が 0 であること**（監査・集約・README の参照も含めて）を確かめる。importer があるものは報告して外す。削除は束の適用のときに `git rm` で行う（下流がないので再ビルドは起きない）。
4. **束の手順書**：`targets/batch-w1w2a.md` に、適用の順序（R75 の削除 → R79 の docstring → W1 の対象 → W2a の対象の順。split は `split_module.py`、move は `move_module.py`、reimport は入口の編集）、各段のコマンド、snapshot の採り方（全対象の before は適用前にまとめて採る。**この snapshot の採取だけは `lake env lean --run decl_snapshot.lean` で対象のビルドが要るので、DG-W1 の取り込み後、`.lake/build` を複製してから行う**）、下流ビルドの対象の集合、失敗時の二分の規則、止めて報告する点（適用後・下流ビルド後・verify 後の 3 か所）を書く。
5. 上の 1〜4 が終わったら止めて報告する。main の merge・`.lake/build` の複製・snapshot・束の適用は、Claude が「DG-W1 を main に入れた」と伝えてから。

### 10.16 追記（10-31、§10.15 の準備の承認と、R75 の参照元の処置）

**承認**：3 コミット（b0491d1fa・67c6ea7cb・21258b0d9）、R79 の dry-run（618＋1／618＋16／3、635 ファイル・1,253 箇所、アンカー `396-任意モデル源への一般化中断2026-10-17` を確認）、束の手順書 `batch-w1w2a.md`（停止点 3 か所）、Python 試験 157 件 PASS を確認した。新しい準備ファイル（`rewrite_r79_docs.py`・`check_r75.py`・試験・targets の記録）はコミットしてよい。

**R75：29 本すべてを削除する。** importer として数えないもの、参照元の処置は次のとおり。

1. **生成された領域の監査（`scripts/audit/shared.lean` など `make_area_audits.py` の出力）は利用者ではない。** 追跡中の全モジュールを機械的に import しているだけなので、削除の後に `python3 scripts/make_area_audits.py` で再生成する（DG-W1 の D0 と同じ。他の area の差分が出たら並行セッション由来なので戻して報告）。CategoryTheory の 25 本はこれで解消。
2. **`scripts/check_word_source_operators.lean` は削除する。** 削除する `Presentation.RetractWordPullback` の検査であり、verify の manifest にも scripts の他のファイルにも参照がない（確認済み）。削除を報告に記す。
3. **`Spectra/SymmetricSequence/AdjacentBraid`（殻）**：利用者 `Spectra/SymmetricSequence/SpherePowers.lean` の 3 行目を `public import SerrePositivity.CategoryTheory.Monoidal.AdjacentBraid`（殻が再エクスポートしている実体）に書き換えてから殻を削除する。SpherePowers の公開する名前は変わらない。
4. **∞ 側の監査の禁止モジュール一覧**（`audit_homotopical_foundations.lean`・`audit_homotopical_general_tools.lean` など）に削除するモジュール名が載っていれば、その行を外す（存在しないモジュールは禁止一覧に要らない）。manifest・個別チェックの名前参照も同じ。
5. **README の案内**（HotA の README の拡張子なしの案内 3 件、`CategoryTheory/Monoidal/README` など）は、削除したモジュールへの言及を消すか移動先に替える。短い宣言名だけの言及（`readme_name_mentions`）は移動先の同名宣言を指すので触らない。
6. 削除は束の中で R75 の段（最初）に行い、`git rm` と 1〜5 の編集を 1 コミットにする。下流がないので再ビルドは起きない。

これで束の構成は確定：R75（29 本＋検査 1 本）→ R79（2 コミット）→ W1（68）→ W2a（1,208）。DG-W1 の取り込みの通知を待つ。

### 10.17 追記（10-31 夜、暦 #2 の適用前の停止への回答：ルートの import 一覧を現 main に合わせる）

**承認**：止めた判断は正しい。w1.json のルートの `reimport` 項目の `imports[SerrePositivity]`（785 件）は古い main を基準に作ったもので、区切り 1-2・1-3（HA・CA・LA・PC・IM の統合）と DG-W1（DG の 12 行 → 1 行）で 247 件が存在しなくなった。

**処置（w2a.md の「W1 の計画上のルート import 修正」と同じ規則）**：
1. ルートの置換予定 import を、**現在の main のルート import（664 件）と、承認済みの ∞ 層の入口 5 本の和集合**に作り直す。W1・W2a で移動・分割する元モジュールがルートに直接 import されていれば、その行は入口の import に置き換わる（移動先はすべて入口の閉包に入る）ので外す。他の項目（move・split・非ルートの reimport・`downstream_imports`）は変えない。
2. 作り直した w1.json で、w1 単独と w1＋w2a の静的検査（`validate_targets.py`、保存済み snapshot）を再実行し、PASS と指標（禁止辺・閉包）が §10.14 の実装後と同じ（増加 0）であることを確かめる。件数（785 → 何件）を報告に書く。
3. この修正は 1 コミット（記録）。

**rsync**：nohup のランナーを介さず、**前景で直接**実行する（`rsync -a --delete ../SerrePositivity/.lake/build/ .lake/build/`、ログはファイルへ）。数分で終わる。終了コード 23・24 の扱いは §10.13 のとおり。`ps` が通常権限で拒否されるなら、権限を上げた実行でよい。

その後、before snapshot → R75 → R79 → W1 → W2a の適用 → **停止点 1 で報告**。

**（10-31 追記）R75 の段での小さな追加**：main の 4eb1f4d6b で、止まった Sp レーンの未追跡ファイル 4 本（`KST/Spectra/PointedParametricUncurry{Action,Pre}`・`PointedUncurry{ActionTensor,Composition}`）を `SerrePositivity/Archive/WIP/` に移した。`scripts/audit_kst_spectra_s3.lean`・`audit_kst_spectra_d3tail.lean` の名前の一覧（import ではない）に残る旧名 4 本を、R75 の段で外す（1〜2 行の編集、同じコミット）。

### 10.18 追記（11-01、before snapshot の群 38 が exit 137 で落ちた件：snapshot をハッシュだけにする）

**承認**：ルート import の作り直し（785 → 669）、静的検査 PASS（指標は §10.14 後と一致）、記録コミット 951df3de0、rsync（12 分、終了コード 0）、群 37 までの採取を確認した。群 38 の前で止めた判断は正しい。

**原因**：`decl_snapshot.lean` は各宣言の **type と body の構造 JSON を丸ごと**出力している（`("type", ty)`・`("body", toJson body)`、「name-map 比較のため」）。群 35 の出力が 3.6 GB、37 群で 19 GB。群 38（KST.SConstruction 64 本）は証明項が巨大で、JSON 化の途中でメモリを使い切り、73 分後に SIGKILL（137）された（スワップ 12 GB も使い切っていた）。同じ方式では SConstruction・IC/Derived の群は通らない。

**処置（道具の変更。∞ の Codex が行う）**：
1. **snapshot はハッシュだけにする。** `decl_snapshot.lean` で、type・body の JSON を出力せず、`compare_snapshots.py` の `normalize_expr` と同じ正規化（`--name-map` の写像の適用と、private 名の `_private.<Module>.<n>.` 接頭辞の正規化）を **Lean 側で構造に対して行ってから**ハッシュ（既存の `hash j.compress` でよい）を取る。出力は name・parent・module・kind・type_hash・body_hash・axioms・attributes・位置・uses_modules・transient（§10.11 の帰属に要るもの）。`--name-map` は before／after の両方に同じものを渡す（before では写像の定義域が空なので恒等）。
2. `compare_snapshots.py` は、構造が無い行では type_hash・body_hash で比べる（既存の全構造の行があれば従来どおり）。試験：小さな一時モジュールで、全構造版と新版のハッシュが一致すること、private 名の付け替えと name-map の写像で一致すること。
3. **`env.constants.toList.mergeSort` を全環境でやらない。** 先に対象モジュールの constants に絞ってから並べる（全環境は Mathlib を含めて百万単位で、メモリと時間の無駄）。
4. **群の大きさ**：KST.SConstruction・InfinityCategories.Derived・EInfinity の群は **16 本以下**に割る。各群は `lean -M 40000`（メモリ上限 40 GB）で走らせ、上限で止まったらさらに半分に割る（スワップで機械を止めない）。
5. **採り直し**：群 1〜37 の全構造の出力（19 GB）はハッシュ版に変換せず、**全群をハッシュ版で採り直す**（形式を一つにする。olean は温かいので、各群は環境の読み込み＋ハッシュだけで済むはず）。採り直しが終わったら 19 GB を消す。所要時間を報告に書く。
6. 採り直しの後、R75 → R79 → W1 → W2a の適用 → **停止点 1**。

道具の変更と試験は 1 コミット（道具）＋ 1 コミット（試験）。既存の DG 側の道具（`merge_modules.py` 等、infra/dg-w2）には触れない。

### 10.19 追記（11-01、巨大な項のハッシュ：旧ハッシュとの互換は不要、DAG で数える）

`dgOdotMilnorActualOuterKernelFrameComparison._proof_17`（KST.SConstruction）の型は、異なる部分式 1,844 個だが木として展開すると 56 GB になる（`Expr` は共有のある DAG で、木に展開すると指数的に膨らむ）。

1. **旧ハッシュとの互換は要らない。** §10.18-5 で全群をハッシュ版で採り直すので、群 1〜37 の旧形式の値と一致させる必要はない。56 GB のバイト列を分割して流す計算は**しない**。
2. **ハッシュは DAG 上で、共有部分式を一度だけ数える。** `Expr` を構造的に下りながら、部分式ごとのハッシュを `HashMap Expr UInt64`（構造的同値で引く）に覚え、親は子のハッシュを `mixHash` で合成する。名前の正規化（private 接頭辞、name-map）は葉（`.const`）で行う。計算量は異なる部分式の数（この項なら 1,844）に比例する。before／after は同じ関数で数えるので、共有の仕方が違っても値は一致する。
3. 試験：共有の多い項（例：`∀ x, f (f (f x)) = …` を `let` で畳んだもの）で、展開した木のハッシュと DAG のハッシュが別物でよいが、同じ項の二通りの共有表現で DAG ハッシュが一致すること。
4. **記録**：この宣言と同種の巨大な項（木の展開が 1 GB を超えるもの）が採取中に見つかったら、モジュール名・宣言名・異なる部分式の数・展開サイズを `targets/huge-terms-2026-11.md` に列挙する。これは証明の質の問題（自動生成の証明義務が膨らんでいる）で、窓の外（段 G・K-S• レーンの再開時）に直す候補。監査（`audit_infinity_f1` 等）の RSS 19 GB もこの種の項が原因の可能性があるので、一覧は IF-W0-4 の runner の計測と突き合わせる。

### 10.20 追記（11-01、Lake の成果物キャッシュを使う）

ユーザー決定（11-01）：Lake のローカル成果物キャッシュを全セッションで共有する（[coordination.md §2-3](../coordination.md)）。`~/.zshenv` に `LAKE_ARTIFACT_CACHE=true`・`LAKE_RESTORE_ARTIFACTS=true`・`LAKE_CACHE_DIR=~/.cache/lake` を設定済み。

1. **これからの `lake` の実行は、この 3 変数が入った shell で行う**（新しい shell を開くか `source ~/.zshenv`。`lake env | grep LAKE_ARTIFACT_CACHE` が `true` なら OK）。採取（`lake env lean --run decl_snapshot.lean`）・束の下流ビルド・verify のすべて。
2. 束の下流ビルド（約 20,000 本）をこの設定で走らせると、作った成果物がキャッシュに入り、**取り込み後の main は再ビルドなしで同じ成果物を使える**（rsync の温めが不要になる）。
3. verify.sh・runner は変更不要（`lake build`・`lake env lean` を呼ぶだけ）。`LAKE_RESTORE_ARTIFACTS=true` のおかげで `.lake/build` にも olean が復元される。
4. 試験的に確認済みの挙動：別の場所の同じソースは再コンパイルなしでビルド完了、ソースを変えると新しい版が追加され古い版も残る、既存の `.lake/build` は入らない（以後の分から）。

### 10.21 追記（11-01、DAG 版 snapshot の完了と、同名宣言の扱い）

**承認**：DAG 版 snapshot（124 群、2,967 本、34 分 21 秒、メモリ超過 0）、道具 a280a8f4e・試験 051597414（164 件＋実 Lean の保存試験、共有の仕方を変えてもハッシュ一致）、旧形式 20.3 GB の削除、巨大な項の一覧（3 モジュール 38 件、最大は `dgOdotMilnorRightAxisNuNativeRoof_comparison` の本体 2,635 部分式・76.8 GB）を確認した。一覧は R80 の材料としてコミットしてよい。

**同名宣言の規則（承認）**：snapshot の行の同一性は **(宣言名, 定義元モジュール)** の組とする。before／after の照合は、move・split・merge の対応表で定義元モジュールを写してから行う。
1. **型・本体のハッシュ・公理・属性・種類がすべて一致し、定義元モジュールだけが違う行**（34 名・transient の帰属のずれ）：環境の `getModuleIdxFor?` が返すモジュールを正とし、1 行にまとめる。帰属が群ごとに揺れたのは §10.11 の位置による帰属の副作用なので、`decl_snapshot.lean` では transient の `module` を環境の値で上書きする（道具の小さな修正。試験 1 件）。
2. **双方のソースに定義がある同名宣言**（`Hammock.Word.eq_empty_of_length_zero`：`EInfinity/Hammock/LengthZero.lean:23` と `WordCons.lean:27`）：**2 行のまま保持**し、それぞれの定義元モジュールで照合する。これは EInfinity の重複宣言（同じ主張を 2 か所で証明している）であり、束では触らない。`targets/duplicates-2026-11.md` に記録し、段 G（R80 と同じ扱い、証明を変える整理）の候補にする。
3. 再採取は不要（124 群の原本から統合し直す）。

このうえで R75 → R79 → W1 → W2a を適用し、**停止点 1** で報告する。下流ビルドは、承認後に Lake キャッシュの 3 変数が入った shell で。

### 10.22 追記（11-01、正規化で名前が衝突する private の生成定数は transient）

**承認**：提案どおりでよい。接頭辞の正規化で同じ保存名になる**異なる private 定数**（12 名。例：`Hammock.Word.source.match_1.eq_1` が `ZigzagFirstBoundaryObjects` と `ZigzagFirstBoundaryMaps` の両方で生成されている）は、使う側のモジュールで必要になったときに Lean が生成する補助定数で、親の宣言が保存されていれば決まるものなので、**保存比較からは transient として除外**し、記録には各定数の実名と定義元モジュールを保持し、一覧では正規化名ごとに 1 件にまとめる。定義元を恣意的に選ばない。

**ガード**：この扱いは**生成された名前**（`match_<n>`・`.eq_<n>`・`_proof_<n>`・`proof_<n>`・`_sunfold`・`_unsafe_rec`・`_cstage` などを含むもの）に限る。12 名の中に人が書いた private 宣言の衝突（二つのモジュールで同名の private を別々に定義）があれば、それは §10.21-2 と同じく**定義元ごとに別行で比較**する。該当があれば報告に書く。

**承認**：巨大項の一覧と重複宣言の記録（c40aa35f4）、単体試験 165 件。道具と試験の変更をコミットしてから、R75 → R79 → W1 → W2a を適用し、**停止点 1** で報告する。

### 10.23 追記（11-01、停止点 1 の承認：下流ビルドへ）

**承認**：停止点 1 の報告（R75 86f760485・R79 c4290092a／2c8a89952 の適用、W1・W2a の適用、import グラフが模擬と一致、層検査が模擬と一致（W2a／W2b の禁止閉包 178 → 177 は模擬の `ModelCategory` 語の判定が置換前のテキストを見ていたためで、実測が正しい）、private の生成定数 12 件の transient 扱い（人が書いた衝突 0）、道具 62723a321・試験 7bb821c24）を確認した。

1. **W1 と W2a を先にコミットする**（それぞれ 1 本、`git commit --only`）。下流ビルドで直接 import の補充が要ったら、その分は別のコミット（「downstream imports」）にする。
2. 他の全ビルドがないことを確かめ（DG・main は止まっている。`ps -axo command= | grep '[l]ake build'`）、Lake キャッシュの 3 変数が入った shell で**下流ビルド（20,192 本）**を開始する。夜間に走らせてよい。補充先が中核なら STOP（§10.14-2）。
3. ビルドの後に保存検査（before／after、§10.21〜10.22 の規則）→ **停止点 2** で報告（新規ビルドの本数と時間、補充した import の一覧、保存検査の結果、キャッシュに入った成果物の数の目安）。
4. 模擬の `ModelCategory` 語の判定（置換前のテキストを見る）は道具の小さな誤りなので、停止点 2 までに直して試験を 1 件足す（急がない）。

論文の層への連絡（Claude が行う）：R75 の shared 監査の再生成で、削除 25 本が外れ、ジェネレーターが拾う未掲載 35 本が加わった。bhatt_scholze・adams は復元済み。

### 10.24 追記（11-01、中核への補充の STOP 条件を正す：禁止辺になるときだけ）

**承認**：2 回目の下流ビルドの結果（非中核 11 本への補充と構文修正 3 本、新規 1,731 本、中核 2 本で停止）を確認した。止めたのは §10.14-2 の文言どおりで正しいが、規則の意図を狭く書いていた。

**規則の訂正**：補充（失敗した利用元への直接 import の追加）で STOP するのは、**その import が禁止辺になるとき**だけ——中核のモジュールから ModelBridge・KST・DG・EInfinity・HotA への辺、または中核の層の順序を逆向きに越える辺（例：Core → F1）。**中核から、それより下の中核の層への import（F1 → Core、F2 → Core・Kan・F1 など）は層の順序に沿った通常の補充**で、移動によって切れた推移的 import を直接 import に置き換えるものなので、止めずに補う。

今回の 2 件はどちらも補充先が Core なので補ってよい：
- `F1/MappingSpaces/HomSpanSectionFiberCoherence` ← `Core.FunctorIsoTransportAlgebra`（`F2.functorIso_postcomp_heq_of_heq`。名前空間 `F2` は R54 で付け替える名残で、宣言自体は Core のもの）
- `F2/FilteredExchange/FunctorIsoWhiskerCancellation` ← `Core.FunctorIsoChainTransport`（`functorIso_postcomp_heq_of_map_eq`）

補充のたびに `layer_check.py` の直接違反と禁止閉包が増えないことを確かめる（増えたら STOP）。補充は `batch-w1w2a-downstream-imports.json` に記録し、「downstream imports」の 1 コミットにまとめる（非中核 11 本・構文修正 3 本と一緒でよい）。再ビルドを続け、次の層の失敗も同じ規則で処理して、**停止点 2** で報告する。

### 10.25 追記（11-01、補充で中核の閉包にモデル圏のコードが戻った件：R72 の分割を広げる）

**承認**：停止は正しい。中核 2 件・Derived 2 件・Smith 1 件の補充自体は増加 0。増加（W2a／W2b の禁止閉包 177 → 179、組数 345,310 → 351,422）は、前回の非中核 11 本への補充のうち、**中核から到達する HotA のモジュール**（`Transfer/EvaluationFamily`・`Simplicial/LargeParameterHomotopy` など）に `ModelBridge.HA.Basic`・`HomotopyFunctionComplex.BoundaryOne` を import させたことによる。つまり、これらの HotA モジュールには R72 の分類から漏れた「モデル圏の宣言を使う宣言」が残っていて、中核がそのモジュールを使っている。これは W2a の完了条件（中核の閉包にモデル圏のコードなし）そのものなので、**補充ではなく R72 の分割を広げて直す**。

**手順（まず静的、ビルドなし）**
1. 補充で ModelBridge または BoundaryOne を import させた非中核モジュールのうち、**中核から到達するもの**を列挙する（`layer_check.py` のグラフ）。
2. その各モジュールについて、snapshot の `uses_modules`（宣言ごとの依存モジュール）と、失敗した宣言名から、**ModelBridge・BoundaryOne の宣言に依存する宣言**（と、それに依存する同じモジュール内の宣言）を `moved` とする分割計画を作る。`keep` 側が ModelBridge を import しなくて済むことを確かめる。分割先は `InfinityCategories/ModelBridge/HA/<basename>`（R72 と同じ）。
3. 分割の連鎖：`moved` 側の宣言を使う他の非中核モジュールには ModelBridge 側の新モジュールを import させる（これらが中核から到達するなら、そのモジュールも 2 の対象に加える）。中核のモジュールが `moved` 側の宣言を使っていたら、それは中核にモデル圏の依存があることを意味するので **STOP して報告**（宣言名と使用箇所）。
4. 分割の総数が **10 本を超える**、または 3 で中核の使用が出たら、適用せずに止めて報告する（その場合は、増加 2 件を W2a の既知の残りとして記録し、W2b で処理する案を Claude が判断する）。
5. 10 本以下なら、§10.21〜10.22 の規則で before snapshot（分割元）を採り、分割を適用し、`validate_targets.py`／`layer_check.py` で禁止閉包が **停止点 1 の値（177）以下**に戻ることを静的に確かめてから再ビルドを続ける。分割は `w2a.json` に追記し（candidate `R72(4)`）、「R72 追加分割」の 1 コミット。
6. **停止点 2** の報告に、分割した宣言の一覧と、閉包の前後を含める。

補足：`BoundaryOne` は R72 で「モデル側の塊、純粋部分の move は後の窓」と分類したモジュール。補充で BoundaryOne を要した宣言が純粋部分だけを使うなら、その宣言の側ではなく BoundaryOne の純粋部分を HotA に残す分割（R72 の未実施分の前倒し）でもよい。どちらが小さいかで選び、報告に書く。

### 10.26 追記（11-01、BoundaryOne は move、EvaluationFamily・LargeParameterHomotopy は分割）

**承認**：静的調査（`r72-additional-static-2026-11.md`）の結果を確認した。
1. **`HomotopyFunctionComplex/BoundaryOne`（5 宣言すべて純粋）は、モジュールごと `HomotopicalAlgebra.Simplicial.BoundaryOne` へ move する**（分割ではなく move 1 件。接頭辞 `HomotopyFunctionComplex` が禁止なので、純粋部分でも場所を変えないと閉包から出ない）。利用者の import は書き換え、w2a.md の「分割不要」の記録は「move に変更（11-01）」と直す。
2. **`Transfer/EvaluationFamily`** は候補どおり分割（moved 7・keep 9、分割先 `ModelBridge/HA/EvaluationFamily`）。連鎖の調査を §10.25-3 の規則で終えてから適用。
3. **`Simplicial/LargeParameterHomotopy`** も同じ手順（モデル圏の宣言に依存する宣言を moved に）。
4. 連鎖を含めて 10 本以下なら、§10.25-5 のとおり before snapshot → 適用 → 静的検査（177 以下）→ 再ビルド → 停止点 2。10 本を超えるか中核の使用が出たら止めて報告。

### 10.27 追記（11-01、F2 の入口の `#check`：清い閉包から届かないものは scripts の検査へ移す）

**承認**：16e808ff6（BoundaryOne の move、EvaluationFamily の分割、静的検査 PASS、禁止閉包 177 → **172**）、round 3〜4 の補充 29 件（各回の増加 0）。停止は正しい。

**判断**：層の入口（`InfinityCategories/F2.lean` など）の `#check` は、**その入口の清い閉包から届く宣言だけ**を列挙する。FilteredExchange のように、モジュールがまだ禁止閉包を含む（R73 は W2b）宣言の `#check` を入口に置いたままにすると、入口が禁止閉包を取り込むことになる。入口に import を足して解決する案は採らない（F2 入口の禁止閉包 0 → 141 は、まさに避けるべき変化）。

**手順**
1. F2 入口の 1,497 行の `#check` を静的に分類する：各宣言の定義元モジュール（snapshot）が入口の現在の閉包にあれば残す、なければ**移す**。失敗した 1 件だけでなく全件を一度に処理する。
2. 移す `#check` は、新しい検査ファイル `scripts/check_infinity_f2_pending.lean` に置く（`import` は必要なモジュールを直接。`scripts/` は層のグラフの外なので禁止辺にならない）。先頭の docstring に「F2 の入口から届かない宣言の受入検査。R73（W2b）で FilteredExchange が清くなったら F2 の入口へ戻す」と書く。`scripts/refactor/audit_manifest.txt` に登録して verify で走らせる（manifest の変更は意図を報告に書く）。
3. 他の層の入口（F1・F1B・HomotopyLimits・Stable・Kan など）にも同じ状況があれば同じ処置（まとめて 1 ファイル `scripts/check_infinity_pending.lean` でもよい）。
4. 未処理の補充 2 件（EvaluationFamily の rlp 用 import、`LargeParameterRelativeChoice`）は増加 0 を確かめて補う。
5. 再ビルドを続け、保存比較 → **停止点 2**。「downstream imports」「R72 追加分割」「入口の #check の移動」のコミットに分ける。

### 10.28 追記（11-01、`#check` の移し先の名前：verify.sh は変えない）

**判断**：verify.sh は束の最後の関門なので、同じ束の中で変えない。移し先のファイル名を既存の探索規則に合わせ、**`scripts/audit_infinity_f2_checks.lean`** とする（`scripts/audit_*.lean` に一致するので manifest に登録すれば走る）。中身は F2 の旧入口の `#check` 1,497 件と、必要な直接 import 769 本。先頭の docstring に「F2 の入口（`InfinityCategories/F2.lean`、import は `F2.CatInfinity` だけの清い入口）から届かない宣言の受入検査。R73（W2b）で FilteredExchange が清くなったら入口へ戻す」と書く。

- 残す 0 件・移す 1,497 件は想定の範囲：W1 の reimport で F2 の入口を清くした結果、旧来の目録は閉包全体に依存していたことが見えたということ。F2 の入口は docstring と `F2.CatInfinity` の import だけでよい。
- `audit_manifest.txt` に `scripts/audit_infinity_f2_checks.lean` を追加（意図を報告に）。この監査は F2 の閉包（769 本の直接 import）を読むので時間と RSS は `audit_infinity_f1` 級になりうる。計測は IF-W0-4 の runner に任せる。
- その後、再ビルド → 保存比較 → **停止点 2**。

### 10.29 追記（11-01、R72 の keep 側で禁止接頭辞の下に残るモジュール：中核から届くものは一度に move）

**承認**：999d292e3（`#check` の移動、manifest 99 → 100）、round 5〜6 の補充、`Generated/Basic`（R72 の keep 側、純粋な 2 宣言）を禁止接頭辞の外へ move する提案。停止は正しい。

**一般化（1 本ずつ round を回さない）**：R72 の keep 側で**禁止接頭辞**（`HomotopicalAlgebra.Generated`・`.Transfer`・`.HomotopyFunctionComplex` など `layers.json` の W2a 禁止一覧に当たるもの）の下に残っているモジュールをすべて列挙し（`Generated/Basic`・`Generated/FunctorClosure`・`Transfer/FullyFaithfulLifting`・`HomotopyFunctionComplex/{DiagonalFrame, QuillenStandardFrame, StandardCosimplicial}` など）、**中核から（直接または純粋な HotA を経由して）届くもの**を静的に判定する。届くものは、keep 側の中身が純粋であることを snapshot の `uses_modules` で確かめたうえで、`HomotopicalAlgebra/Simplicial/<内容を表す名前>`（禁止されない接頭辞）へ **move** する。利用者の import を書き換え、w2a.json に `R72(5)` として追記、「R72 keep 側の move」の 1 コミット。
- keep 側にモデル圏の依存が残っているもの（純粋でない）は move せず、報告に書く（再分割の候補）。
- 届かないものは動かさない（後の窓）。
- 件数が 10 を超えたら止めて報告。

その後、再ビルド（残りは小さいはず）→ 保存比較 → **停止点 2**。

### 10.30 追記（11-01、R72 keep 側 7 本の一括 move と validator の拡張）

**承認**：7 本（`Generated.Basic` 2・`Generated.FunctorClosure` 3・`Transfer.FullyFaithfulLifting` 1・`Transfer.EvaluationFamily` 9・`HomotopyFunctionComplex.DiagonalFrame` 6・`QuillenStandardFrame` 4・`StandardCosimplicial` 6 宣言）はすべて純粋で中核から到達。模擬で禁止閉包 172 → **166**、直接違反 296 → 294、増加 0。一括 move を承認する。

**validator の拡張（承認）**：`validate_targets.py` で、同一モジュールの重複登録のうち **「split の `module` と同じモジュールを `module` とする move」の組だけ**を許す。意味は「split を適用した後の keep 側を move する」で、適用順も split → move に固定する。他の重複（move 同士、split 同士、move の後の split など）は引き続き拒否。試験を 2 件（許す組、拒否する組）。模擬の import グラフも split → move の順で合成する。

- 移し先は `HomotopicalAlgebra/Simplicial/<内容を表す名前>`（調査記録の案でよい。既存の名前と衝突しないこと）。
- 道具の変更 1 コミット、「R72 keep 側の move」1 コミット（w2a.json の `R72(5)` 追記を含む）。
- その後 Generators の補充 → 再ビルド → 保存比較 → **停止点 2**。

### 10.31 追記（11-01、停止点 2 までの判断表：承認なしで進める処置と、止める条件）

§10.14〜10.30 で一つずつ決めてきた処置を一つの表にまとめる。**この表に当たる処置は承認を待たずに行い**、報告は停止点 2 でまとめる。停止点 2 の報告には、表のどの行を何件適用したかを数で書く。

| 失敗の型 | 処置（承認不要） | 条件 |
| --- | --- | --- |
| 推移的 import が切れて識別子・インスタンスが見つからない | 失敗した利用元に直接 import を補う（§10.6・§10.14・§10.24） | 補う import が禁止辺でない（中核 → ModelBridge・KST・DG・EInfinity・HotA、中核の層の逆向き、を作らない）。補充後の `layer_check.py` で直接違反と各 tier の禁止閉包が増えない |
| R72 の keep 側（純粋）が禁止接頭辞の下に残っている | `HomotopicalAlgebra/Simplicial/<内容を表す名前>` へ move（§10.26・10.29・10.30） | `uses_modules` で純粋であること。利用者の import を書き換える。w2a.json に `R72(5)` 追記 |
| 非中核のモジュールにモデル圏の宣言に依存する宣言が混在 | 依存する宣言を `ModelBridge/HA/<basename>` へ split（§10.25） | 中核が moved 側を使っていない。連鎖を含めて累計 10 本まで |
| 層の入口の `#check` が入口の閉包から届かない | `scripts/audit_<層>_checks.lean` へ移し manifest に登録（§10.27・10.28） | 入口の import は増やさない |
| 構文の崩れ（入口の import の位置など）、道具の小さな誤り | 直して試験を 1 件足す（§10.23-4・§10.28） | 道具の変更は別コミット |
| 同じモジュールに split と keep 側の move の両方 | validator の「split → move」の組として扱う（§10.30） | 他の重複は拒否 |

**止めて報告するのはこれだけ**：
1. 中核のモジュールがモデル圏の宣言（ModelBridge・BoundaryOne 系）を使っている。
2. 上の処置のどれでも消えない禁止閉包の増加。
3. 保存比較の不一致（transient・同名宣言の規則 §10.21〜10.22 を適用した後で残るもの）。
4. 宣言の本文・型・名前を変えないと直らない。
5. split の累計が 10 本を超える、または一つの round の新規ビルドが前の round より増える（収束していない）。

各 round の記録（新規ビルド数・時間・適用した処置の件数・層検査の値）は `batch-w1w2a-downstream-imports.json` と停止記録に残し、コミットは「downstream imports」「R72 追加分割」「R72 keep 側の move」「入口の #check の移動」「道具」に分ける。

**次の束への教訓**（DG-W2(b)・IF-W2a-2 の前に行う）：束の前に、snapshot の `uses_modules` から**宣言単位の到達性**を静的に検査し、(a) 推移的 import だけで届いている利用（移動で切れる候補）、(b) 禁止接頭辞の下に残る純粋なモジュール、(c) 入口の `#check` の到達性、を列挙して計画に織り込む。

### 10.32 追記（11-01、§10.31 条件 5 の訂正：move・split の直後の round は基準をやり直す）

**承認**：validator の拡張 9bc69dc79（170 試験 PASS）、keep 側 7 本の move 8dc0f29a0、Generators の補充、静的検査 PASS（禁止閉包 166、直接違反 294）。

**条件 5 の訂正**：「round の新規ビルドが前の round より増える」は、**補充（import の追加）だけを行った round どうし**で比べる。move・split・`#check` の移動のように**モジュールの集合や名前を変えた直後の round は、その変更の下流が再ビルドされるので新規が増えるのが正常**であり、その round を新しい基準にする。round 7（7 本の move の直後、1,333 本）はこれに当たるので停止の理由にならない。

そのまま続ける：未適用の補充 5 本（4 モジュール、各回の増加 0 を確認済み）を適用 → round 8 以降（補充だけの round は、直前の補充だけの round より新規が増えたら停止）→ 保存比較 → **停止点 2**。

### 10.33 追記（11-01、下流ビルド PASS：条件 5 の尺度、監査の追従、停止点 2・3 の進め方）

**承認**：下流ビルド PASS（round 8〜11、新規 8,601＋733＋78＋101、最終 round の失敗 0）、補充 31 件（束全体で 75 モジュール・83 import）、禁止閉包 166・直接違反 294・増加 0、対象一覧 1,285 項目 PASS。

1. **条件 5 の尺度**：補充だけの round どうしで比べるのは**失敗モジュールの数**（22 → 3 → 1 → 0 のように減ること）。新規ビルドの数は、前の round で上流が失敗して試されなかった下流が通り始めると増えるので、尺度にしない。今回の 78 → 101 は停止の理由にならない。
2. **監査 7 本に残る旧モジュール名 325 件**（`mods` の名前一覧など）は、束の対応表（move・split・merge）で**新しい名前に追従させる**。split したモジュールは keep 側と moved 側の両方を列挙する。存在しない名前が一覧に残ると監査が黙って検査を飛ばすので、放置しない。「監査の追従」の 1 コミット。
3. **保存比較**（§10.21〜10.22 の規則）を行い、不一致が 0 なら**停止せずに**「downstream imports」「監査の追従」をコミットして **verify**（`VERIFY_JOBS=3`、Lake キャッシュ有効、他の全ビルドがないことを確認）へ進む。停止点 2 の報告は停止点 3 の報告に含める。不一致があれば停止点 2 で止める。
4. **停止点 3** の報告：verify の summary（PASS・gate:true）、保存比較の結果（比較した宣言数、transient 数、同名宣言の扱い）、round ごとの表、補充の総数、層検査の前後（停止点 1 → 最終）、コミットの一覧。

### 10.34 追記（11-01、保存比較の不一致 69 件の処理）

**承認**：停止点 2 で止めた判断（保存比較 FAIL 69 件）、監査 7 本の追従（旧名 325 件、split 18 件を両側へ、import 8 件）。

**A. 生成名 56 件（28 組）**：`_aux_<モジュール名>___macroRules_…`・`___unexpand_…` は Lean が `macro_rules`／`unexpander` に付ける補助名で、**モジュール名を埋め込む**。private 接頭辞と同じく、対応表（move・split・merge）でモジュール名を写してから比べる規則を `compare_snapshots.py`（または Lean 側の正規化）に加える。写した後に型・本体のハッシュが一致すれば一致、しなければ一覧に残す。試験 1 件。

**B. `KST.Comparison.doubleMappingCylinder_hom_ext`**（`IC.Kan.DoubleMappingCylinderMap` から消え `…Desc` に現れた）：before／after のハッシュが一致するなら、split の `moved`／`keep` の実際の配置が計画と違っただけなので、対応表の記録を実際に合わせて一致扱い。一致しなければ D へ。

**C. `KST.SConstruction.instIsDGPretriangulatedDGOdotGluing_5`**（追加のみ）：無名 instance の自動番号。before の `instIsDGPretriangulatedDGOdotGluing_*` のうち型ハッシュが同じものがあれば番号の付け替えとして一致扱い（§10.10 の位置の規則で親を同定）。なければ D へ。

**D. 残り（型 5・本体 1・補助宣言 4、`BoundaryFactorization.initial_left`・`kanTensorReplacement_isCofibrant/_isFibrant/_left_isFibrant`・`EvaluationFamily.detected_inf/generators`・`Hammock.Direction`・`FiniteSpanVertex`・`SimplexInverseMatching.{empty,point}MatchingTerminal`）**：ハッシュだけでは判断できないので、**pretty print で前後を比べる**。
1. before の環境は、束の前のコミット（aacd82f41）の scratch worktree を作り、Lake キャッシュから復元する（`git worktree add ../SerrePositivity-ifw0-3-before aacd82f41`、該当モジュールだけ `lake build` → キャッシュに当たるので再コンパイルなし。`LAKE_RESTORE_ARTIFACTS=true` で olean が `.lake/build` に復元される）。after は現在の worktree。
2. 各宣言について `#print` と、`set_option pp.explicit true` での `#check` を before／after で出し、テキストで比べる。
   - **定理**：`pp.explicit false` の型が同じなら一致扱い（インスタンスや暗黙引数の経路の違い。公理も一致していること）。違えば **STOP**（差分を報告）。
   - **定義・インスタンス・補助宣言**：型と本体の pp が同じなら一致扱い。本体が違う定義（`generators`）は、違いがインスタンス項だけか（`pp.explicit true` で見える）を書き、それ以外の違いなら **STOP**。
   - 補助宣言（`Direction`・`FiniteSpanVertex`・`…MatchingTerminal` の auxiliaries）：どの補助（`rec`・`noConfusion`・`sizeOf`・`match_` 等）が違うかを列挙し、生成名の違いなら一致扱い。
3. 使い終わった scratch worktree は削除する。

**E. 報告**：13 件それぞれの処置を表にして**停止点 2′**で報告する。すべて一致扱いになれば、その報告のあと止まらずに「downstream imports」「監査の追従」「保存比較の規則」をコミットして verify へ（§10.33-3）。STOP が 1 件でもあれば止まる。

### 10.35 追記（11-01、残り 32 件：macro／unexpander の補助宣言は transient、before の復元は再コンパイルを許す）

**承認**：9 件の一致（B 2・D 7）、生成名の正規化と試験（171 件 PASS）。

**A の 28 組（`_aux_…___macroRules_…`・`…___unexpand_…`）**：本体の `Name.mkStr` にもモジュール名が埋め込まれているので、ハッシュでは一致しない。これらは `macro_rules`／`unexpander` が生成する**記法のための補助宣言**で、数学的な内容を持たず、正しく生成されたことはビルドが通ったことで示される。**transient（生成宣言）として保存比較から除外**し、組数と名前を記録に残す（§10.22 の生成名のガードに `_aux_` の `___macroRules_`・`___unexpand_` を加える）。本体のリテラルまで写す正規化は作らない。

**C の無名 instance `instIsDGPretriangulatedDGOdotGluing_5`**：無名 instance の自動番号は、環境に同じ基底名があると変わる（import の変化で付け替わる）。before では同じモジュールの `instIsDGPretriangulatedDGOdotGluing_<n>` のどれかが相手のはずなので、**番号を無視して (モジュール, 型の pp) で照合**する。D と同じ scratch で `#print` して比べる。

**D の未復元 4 件（`kanTensorReplacement_isCofibrant/_isFibrant/_left_isFibrant`＋C）**：scratch worktree でキャッシュに無い 165 本が再コンパイルされたのは、それらの before の成果物がキャッシュ採用（11-01）より前に作られていたからで、前提の違反ではあるが規則の違反ではない。**再コンパイルを許して復元を続ける**（数百本・数分の規模。全ビルドではないが、他の全ビルドがないことは確かめる）。復元できたら pp で比べる（定理は `pp.explicit false` の型が同じなら一致）。

**その後**：全件一致なら停止せずに「downstream imports」「監査の追従」「保存比較の規則（_aux_ transient、instance の番号無視）」をコミットし、verify へ（§10.33-3）。一致しないものがあれば停止点 2″ で差分を報告。scratch は削除。

### 10.36 追記（11-01、停止点 3：監査 2 本の import を直して再検証）

**承認**：保存比較 PASS（16,412 件、未解決 0）、ビルド 2 段と sorry 閉包の成功、監査 98／100、3 コミット（f66a5c24e・9406000cb・02971913f）、補充 75 モジュール・83 import、直接違反 296 → 294、禁止閉包 177 → 166。

**失敗した監査 2 本の処置**：どちらも、束で動かした定義に監査の `import` が届かなくなったもの。監査（`scripts/audit_*.lean`）は層のグラフの外なので、必要なモジュールを直接 import してよい。
1. `audit_homotopy_limits.lean`：R72(3) で `InfinityCategories/ModelBridge/` 直下へ移した HL の Quillen 42 本（w2a.json の実在する移動先。**`HL/` という下位ディレクトリはない**——§10.36 の初版の書き誤り、11-01 訂正）を import に加える（名前一覧の追従は 9406000cb で済んでいるので import だけ）。
2. `audit_infinity_f2.lean`：F2 の入口が `F2.CatInfinity` だけになったので、F2 の領域（FilteredExchange・Ind・Compact・Presentable など、`audit_infinity_f2_checks.lean` と同じ閉包）を直接 import する。
3. 両方を `lake env lean` で単独に通してから、「監査の import の追従」の 1 コミット。

**再検証**：全 100 本をもう一度 44 分かける代わりに、`VERIFY_CACHE=1 VERIFY_JOBS=3 zsh scripts/refactor/verify.sh` で走らせる。直前の実行で成功した 98 本は鍵（監査の本文と閉包の olean ハッシュ）が同じなのでキャッシュに当たり、直した 2 本だけが実行される。README の規約では gate:false になるが、**入力が同一であることは鍵が保証する**ので、この束ではこれを合否とする（coordination.md §5 に逸脱として記録。次の束からは IF-W0-4 の runner で短くなるので全実行に戻す）。summary で 2 本が成功し failures 0 なら **停止点 3′** で報告 → Claude が main へ取り込む。

### 10.37 追記（11-02、道具：証明無関係なハッシュ。DG-W2(b) の保存比較 2,585 件の原因）

**依頼（∞ の Codex、IF-W2a-2 の停止点 1′ の後、優先）**：DG-W2(b) の保存比較で 2,585 件の不一致が出た。内訳は、型 716・本体 908 のうち 1,595 件が **`_proof_*` の名前の違いだけ**、本体 4 件が **matcher（`match_N`）の参照先の違い**、型 1 件が **Prop のインスタンスの選択の違い**（`CategoryTheory.Abelian.hasBinaryBiproducts` → `ModuleCat.instHasBinaryBiproducts`）、追加 246 件のうち 242 件は親への束ね方の差。原因は、統合で複数ファイルが一つになると Lean が補助定数をファイル内で共有（重複排除）するため、同じ証明でも参照する補助定数の名前が変わること。いずれも証明無関係性で同一。

**`decl_snapshot.lean` の DAG ハッシュに次の規則を加える（`--proof-irrelevant`、既定で有効）**：
1. **定理への参照は型のハッシュ**：`.const n` で `n` が `thmInfo`（`_proof_*` の補助定理、`.eq_N` の等式補題、Prop 値のクラスのインスタンス（Lean は Prop のインスタンスを定理として作る）を含む）なら、名前ではなく**その定理の型**を同じ関数で下ったハッシュに置き換える。
2. **生成された定義への参照は値のハッシュ**：`n` が matcher（`Meta.Match.Extension.getMatcherInfo?` で分かる）、`_unsafe_rec`、`_cstage`、`._sunfold` など elaborator が生成した補助定義なら、名前ではなく**その値（本体）**のハッシュに置き換える。
3. 1・2 は再帰的（置き換え先の中の参照にも適用）。メモは `HashMap Expr UInt64` のまま（§10.19）。
4. 親への束ね方（追加 242 件）：auxiliaries の束ねを (親の名前) で行い、補助の実名は使わない。transient の判定も同じ。
5. 試験：同じ定義を 2 ファイルに書いて別々にビルドした場合と、1 ファイルにまとめてビルドした場合で、`_proof_*`・`match_*` の共有が起きてもハッシュが一致すること。Prop のインスタンスを別経路で解決した 2 つの項が一致すること。定義（非 Prop）の参照先が変われば一致しないこと（偽陽性の防止）。
6. 1 コミット（道具）＋ 1 コミット（試験）。main へは Claude が取り込む。DG の束は取り込み後に before／after を採り直す（before は束の前のコミットの scratch を Lake キャッシュから復元）。

**根拠**：定理は命題の証明であり、どの証明でも等しい（proof irrelevance）。matcher は定義の構造から決まる補助定義で、同じ構造なら同じ値。これらの**名前**は保存の対象ではなく、**型（または値）**が保存の対象。
