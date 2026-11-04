# IF-W2c 停止点 1（§3.0 草案）

基点は main `835af1c6a`、ブランチは `infra/if-w2c`。ビルド・適用は 0 回。既存の Lean 成果物から型と本体（証明と生成定数を含む）の参照先を採取した。実装・監査の Lean ソースが IF-W2b 検証コミットと同一であることを git で照合した。

**適用は保留。** 承認された spectrum 群の外に中核利用者が 1 本残る。群 B にも「移すだけ」で Stable に置けない分数モジュールがある。下表は草案の静的模擬で、保留した宣言を移した場合の予測は含まない。

| 模擬 | 中核層間順序違反 | 直接禁止辺 | W2a/W2b 禁止モジュール | affected core |
| --- | ---: | ---: | ---: | ---: |
| 現在 | 0 | 18 | 150 | 2,531 |
| 群 A 後 | 0 | 1 | 106 | 2,358 |
| 群 A と群 B の静的移動候補 111 本 | 0 | 1 | 106 | 2,366 |

### 群 A

5 本から出発して import の逆閉包（集約を除く）31 本を検査した。型・本体でこれらの宣言を使う spectrum 固有の 10 本を加え、承認された 15 本を同時に `KST/Spectra/Limits/` へ移す草案とした。群外でその群を直接 import する中核は `HomotopyLimits.SpectrumPoint` だけ。これは `SpectrumBinaryProduct` を経由しており、定義 `spectrumPoint` は `OmegaSpectrum` と `OmegaSpectrum.mk` を使う。次の判断案は、pointed 一点に関する 3 宣言を残し、`spectrumPoint` とその補助証明を KST へ split すること。この追加 split は未承認で、模擬にも含めていない。既存の直接利用者は HL 入口と群内の `SpectrumFiniteProducts`。

KST の一般部分 25 元モジュールに対し、丸ごとの move 12 と split 13 を計画した。置き先は Kan 4、F1 21。Kan・Core に置く候補全件の依存閉包は制限に適合し、F1B 入口の straightening 到達は 0。外部の pointed 基礎・HA を使うものを Kan には置いていない。HA の `ResolutionHom` と `AdjunctionHom` は純粋な定義を HL に切り出し、旧パスは移動先を再公開する案。各 split の宣言・属性・ヘッダーは対象 JSON に収録した。 [群 A 実施候補](w2c-a-plan.json)

直接 D は参照先モジュール自身が定義する定数（生成定数を含む）の数。0 でも再公開された定数・notation・instance が必要な場合がある。各定数の完全名、元の宣言、KST 内の依存閉包、移動／split の先を辺ごとに記録した。 [18 辺の証拠](w2c-a.json)

| HL の利用元 | 現行の直接 import | 直接 D | 草案の処置 |
| --- | --- | ---: | --- |
| AdjunctionFrameHomBifunctor | AdjunctionHom | 1 | AdjunctionHom（split）、ResolutionHom（split） |
| FibrationComponentTransport | FibrationIntervalLifting | 0 | 再公開を経由した実際の定義元を直接 import |
| IntervalHomBoundary | PointedInterval | 5 | PointedInterval（move） |
| KanTensorAdjunction | AdjunctionHom | 0 | 直接 import 削除候補 |
| KanWhiteheadComparison | PointedKanWhitehead | 1 | MonoRightHomotopyEquivalence（move）、PointedKanWhitehead（move） |
| LoopTowers | PostMappingFibration | 0 | SuspensionLoop（split） |
| MappingPathNaturality | MappingPathSpace | 9 | FreeInterval（split）、FreePathSpace（move）、MappingPathSpace（move）、PointedMappingNaturality（split） |
| MappingPathTargetLifting | PointedKanWhitehead | 2 | AcyclicFibrationLifting（split）、FreeInterval（split）、FreePathSpace（move）、MappingPathSpace（move）、MonoRightHomotopyEquivalence（move）、PointedKanWhitehead（move）、PullbackKanSequence（split） |
| PullbackFiberIso | PullbackKanSequence | 0 | 直接 import 削除候補 |
| RelativePointedHomLifting | PostMappingFibration | 0 | PointedMapping（move）、PointedMappingParameters（split） |
| SpectrumBinaryProductSequence | KanSequence | 13 | 15 本の群で KST/Spectra/Limits へ |
| SpectrumBinaryProductSequence | PointedGroupProduct | 1 | 15 本の群で KST/Spectra/Limits へ |
| SpectrumMappingDiagram | CoherentNerve | 0 | 15 本の群で KST/Spectra/Limits へ |
| SpectrumPullbackAdjoints | CofibrantOmegaSequence | 1 | 15 本の群で KST/Spectra/Limits へ |
| SpectrumPullbackAdjoints | PostMappingFibration | 1 | 15 本の群で KST/Spectra/Limits へ |
| SpectrumPullbackMonomorphisms | PullbackKanSequence | 6 | 15 本の群で KST/Spectra/Limits へ |
| SpectrumTowerSequence | CofibrantOmegaSequence | 1 | 15 本の群で KST/Spectra/Limits へ |
| TowerMatchingLifting | MonoRightHomotopyEquivalence | 1 | MonoRightHomotopyEquivalence（move） |

18 辺を単純に消す対照実験だけでも HA 90 本・影響 2,239 本が残る。実際の草案では HA 90 と KST 16 が残る。たとえば F1.Joins.CosliceTwistedHomEquivalence → HA.Simplicial.DiagonalLocalizedEquivalence → … → HA.HomotopyFunctionComplex.AdjunctionHom、F1.TwistedArrow.TwistedHomDiagonal → HA.Simplicial.DiagonalAdjunction → … → Reedy.SimplexResolution の経路がある。FreeInterval が必要とする boundaryGenerators_leftClass も HA.Simplicial.Generators から Transfer.EvaluationSmallness に到達する。残る全モジュールについて中核からの入口と経路を保存した。 [模擬結果](w2c-stop1.json)

### 群 B

IF-W0-3 §4.4 の接頭辞・ディレクトリで探索し、分数・lax の実参照から追加の支えを数えた。699 は探索対象であり、数学的に移動が確定した本数ではない。既存の R48 は移動元の消失と移動先の存在を 7/7 確認した。 [群 B 判定一覧](w2c-b-inventory.json)

| 項目 | 現行探索対象 | 草案に含む move | 保留 | 主な境界 |
| --- | ---: | ---: | ---: | --- |
| [R51](w2c-b-r51.json) | 3 | 3 | 0 | StableSpanPushout、PushoutCompletion、RelativeColimitCompletion の 3 本 |
| [R68](w2c-b-r68.json) | 91 | 1 | 90 | Sp 値の Invariant・OmegaSpectrum と、既存 F2 の LaxPullback 系を分ける |
| [R52](w2c-b-r52.json) | 324 | 6 | 318 | VerdierDenominatorOver は Derived/F2 を実参照。WeakOreSpanLift は後続 R69 の SquareArrowFamily を使う |
| [R69](w2c-b-r69.json) | 131 | 44 | 87 | BF/spectrum のデータを含む部分を残す。Core の制限と F1B の straightening を検査 |
| [R70](w2c-b-r70.json) | 137 | 54 | 83 | F3・CoreFlag の一般部分を F1 へ。分数の機構に依存するものは根拠付き保留 |
| [R56b](w2c-b-r56b.json) | 13 | 3 | 10 | 現行閉包で KST.Fibration に届く比較・適用 3 本を Derived へ。残り 10 本は一般部分との区別を保留 |

R52 の `fraction_ho_localization` は `VerdierFractionComparison` 内の private lemma。同じファイルのまま保留。そこからは `IntervalPrecompositionFamily`、`IntervalPostcompositionFamily`、`LocalizationHomotopyCategory` と後続 R69 の `ArrowPrecompositionSquare` が要る。R52 の split や段 G の一般化は提案していない。保留ごとの宣言・必要な定義元と、一般部分の split 候補を台帳に記録した。候補の partition は source 親単位で、validator 検査済み split とは区別する。

### 静的検査・下流

- `move_module.py` の dry-run は終了 0。全 138 move、353 ファイルを列挙し、applied=false。split 15 件はそれぞれ採取済み snapshot で validator の prepare と依存方向を検査。全体の循環 0。
- `validate_targets.py` は exit 1。模擬後の増加 ratchet 指標 26 件。W2b の独立した 3 条件では、順序違反 0・集計上限超過 0、承認外の直接禁止辺 1（SpectrumPoint → KST.Spectra.Limits.SpectrumBinaryProduct）で FAIL。群 B 候補だけでは既存の W2b enforcement は PASS、raw ratchet は 16 件増加、affected core は W2b 実測 2,531 に対し 2,539。基準を取り直していない。
- [統合した対象](w2c-combined-plan.json) の本番逆閉包は **10,305 本**、100 根でカバー。W2a-2 基準の概算 6,157 秒、キャッシュの温まった W2b 実績による参考値 1,349 秒。保留した探索候補の利用者まで数えた参考値は 10,396 本。今後追加する支えや HA の再配置によって変わる。

### 停止点 1 の判断事項

1. `SpectrumPoint` の追加 split を許すか。15 本の群の外からの直接辺を解消するのに必要。
2. 列挙した HA の間接経路を次の調査対象に含めるか。残る 90 本は、上の 1 辺を消した場合にも存続する。
3. 群 B の保留分では、前段階への一般補題の移動や F2/Derived の依存元の split が必要な例がある。R52 を「移すだけ」に保つ範囲と、後続束へ回す対象を決める。

この草案は静的検査まで。下流と verify は 2a・2b 後の合図待ち。生の宣言参照・snapshot・dry-run/validator 記録は当該 worktree の `.lake/verify/ifw2c-draft-835af1c6a/`。
