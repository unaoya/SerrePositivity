# IF-W2c 停止点 3

**下流・保存比較・層検査・verify PASS（gate:true）。** 検証 HEAD `ceda0bd3b`、ブランチ `infra/if-w2c`。取り込みは Claude。

main `45e12b933` を `eb16fee32` で取り込み（2a・2b・BS-W10 作業 A・pairCompletionH0Unit を含む）。衝突 0。main 作業木での作業・ビルド 0。既存の未追跡 W2b 停止記録 5 本を保持。

## 下流と保存比較

- 下流 **11,152/11,152 本、128/128 根**。round 2 PASS、未検証 0、失敗 0。round 1 は 10,920 本・123 根が検証済み、PointedGenerators 1 本で失敗し、未検証 5 根。実時間は round 1 2202.1 秒、round 2 39.7 秒。草案 129 根から、main 取り込み後の被覆は 128 根となった。
- 全ビルドは worktree 共通鍵のもとで実行。下流の補充は PointedGenerators への EvaluationSmallness の 1 import。原本（取り込んだ main）の候補 3 本を一時環境でビルドして before v3b を採取し、候補の小さなビルド後に補充コミット。宣言の本文・型・名前は変更 0。
- 停止点 2 の after snapshot を基準に、取り込み後の after v3b を再取得。public 5,482・private 込み 5,532 宣言記録。停止点 2 → 今回の新しい差と、補充モジュール・直接利用者 3 本の before/after の差は両方 0。
- 当初 before → 最終 after の生差は 58 件。停止点 2 で承認された個別照合 58 件を継承し、**未説明 0**。指紋・比較器の変更 0。

## 層検査と ratchet

| 指標 | W2c 前 | 停止点 2 | 停止点 3 |
| --- | ---: | ---: | ---: |
| 直接禁止辺 | 18 | 0 | 0 |
| W2a/W2b 禁止モジュール | 150 | 74 | 74 |
| affected core | 2,531 | 1,730 | 1,730 |
| W1 禁止 / affected | 0 / 0 | 0 / 0 | 0 / 0 |

中核の順序違反・新しい直接禁止辺・全体集計の増加はすべて 0。M16 の HA 66・ModelBridge 8 は承認済み集合と一致。F1B 入口と監査の straightening 到達はともに 0。ルート本番閉包 24,616 本、Archive 到達 0。
W2b 基準に対する個別増加 14 件は承認済み診断内。経路を JSON に収録。最終候補に対する --ratchet PASS（増加 0）を確認し、verify PASS 後に [w2c-layer-baseline.json](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/scripts/refactor/targets/w2c-layer-baseline.json) へ保存。既存の enforcement 上限・layers.json の例外は変更していない。

## 監査と verify

移動・分割先 **441 本**を移動先の領域の監査で列挙。既存の run_cmd の条件を保持し、必要モジュール一覧の 298 本を移動先へ移管した。標準三公理・型の ModelCategory 禁止・モジュールごとの宣言存在の検査も引き継いだ。Kan・ModelBridge・StablePresentable の監査 3 本を新設して manifest へ登録。cofinality の許可閉包の 3 項目は移動先名へ追従した。
private のみを持つ分割先 3 本も監査対象に含む。監査は従来の非 module 形式を保ち、通常の import を使う。この形式は private データも読み込むことを Lean の importModulesCore と 3 モジュール・private 4 宣言の小さな監査で確認した。初回 verify は監査へ誤って書いた import all の構文エラーで中断し、検査条件を変えずに import の綴りを修正した。2 回目は KST.Spectra と Rectification の監査 2 本が失敗した。分割後に KST に残る SimplexLastContraction.homotopy への明示 import と、HL へ全宣言を移した AdjunctionHom・ResolutionHom の定義元一覧 2 項目を補充し、小さな監査 2 本の PASS 後に全件を正式に再実行した。本番ソースの private 参照復旧 15 辺は変更していない。

| 監査 | #check 前→後 | #print axioms 前→後 |
| --- | ---: | ---: |
| audit_derived_infinity | 360 → 360 | 2313 → 2313 |
| audit_homotopy_limits | 5592 → 5481 | 5498 → 5387 |
| audit_infinity_core | 1737 → 1737 | 1892 → 1892 |
| audit_infinity_f1 | 9070 → 9100 | 140 → 170 |
| audit_infinity_f1b | 2127 → 2127 | 28 → 28 |
| audit_infinity_kan | 0 → 0 | 0 → 0 |
| audit_infinity_model_bridge | 0 → 0 | 0 → 0 |
| audit_infinity_stable | 374 → 391 | 2342 → 2359 |
| audit_infinity_stable_presentable | 0 → 0 | 0 → 0 |
| audit_kst_cofinality | 90 → 90 | 1 → 1 |
| audit_kst_core_flag | 37 → 5 | 37 → 5 |
| audit_kst_fibration | 0 → 0 | 0 → 0 |
| audit_kst_s_construction | 14409 → 14395 | 14409 → 14395 |
| audit_kst_spectra | 0 → 110 | 0 → 110 |
| audit_localizing_invariants | 0 → 0 | 0 → 0 |

| 宣言の移管 | 宣言数 前 | 宣言数 後 |
| --- | ---: | ---: |
| homotopy_limits → kst_spectra | 110 | 110 |
| homotopy_limits → infinity_f1 | 1 | 1 |
| kst_core_flag → infinity_f1 | 29 | 29 |
| kst_core_flag → infinity_stable | 3 | 3 |
| kst_s_construction → infinity_stable | 14 | 14 |

コマンドの移管 314 件。前後の総数は #check 33,796、#print axioms 26,660 で一致（変更した監査の合計）。対象宣言と移動先は [w2c-section7-audits.json](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/scripts/refactor/targets/w2c-section7-audits.json)。

正式なコマンド：`VERIFY_JOBS=6 VERIFY_MEMORY_GB=40 zsh scripts/refactor/verify.sh`。キャッシュで監査を省略する設定・非 gate 設定は使っていない。

`PASS build(success=2,failure=0,known=0) audit(success=102,failure=0,known=0) sorry(success=1,failure=0,known=0) preparation(success=1,failure=0,known=0) retried=0`

実時間 2658.8 秒、最大同時 RSS 32.89 GiB。スケジューラの待ち・同時 RSS・全ステージの実時間は [summary.json](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/.lake/verify/ifw2c-downstream/verify/summary.json) と [runner.json](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/.lake/verify/ifw2c-downstream/verify/runner.json)。

## import all で復旧した private 参照（段 F / R60）

本番ソースは **15 辺・15 利用元**。private を公開化せず、元の名前・意味を保存した。段 F では、公開 API にするか利用元を元ファイルへ戻すかを各項目で判断する。

| 利用元（SerrePositivity 以下） | import all の参照先 | private 宣言 |
| --- | --- | --- |
| `KST.LocalizingInvariants.RelativeFunctorCoreRestriction` | `IC.Stable.Quasicategory.RelativeFunctorCoreRestriction` | `comp_app_congr` |
| `KST.Fibration.ScaffoldWeightedResolutionPoint` | `IC.Stable.Transport.ScaffoldWeightedResolutionPoint` | `fiberPoint_ext` |
| `KST.Fibration.StraighteningBaseChangeChartComponents` | `IC.Stable.Straightening.StraighteningBaseChangeChartComponents` | `prependEq_heq` |
| `KST.Fibration.ScaffoldVertexBaseChange` | `IC.Stable.Transport.ScaffoldVertexBaseChange` | `pointNormalize` |
| `KST.Fibration.TransportRepresentationFiberPointHom` | `IC.Stable.Transport.TransportRepresentationFiberPointHom` | `component_reindex` |
| `KST.Fibration.StraighteningUnderSectionChart` | `IC.Stable.Straightening.StraighteningUnderSectionChart` | `mapNormalizeComposition` |
| `KST.Fibration.ScaffoldRestrictionChart` | `IC.Stable.Transport.ScaffoldRestrictionChart` | `normalizeValueComposition` |
| `KST.Fibration.ScaffoldBaseChangeLeftPoint` | `IC.Stable.Transport.ScaffoldBaseChangeLeftPoint` | `point_normalize_both_inv` |
| `KST.Fibration.StraighteningBaseChangeSectionCharts` | `IC.Stable.Straightening.StraighteningBaseChangeSectionCharts` | `mapNormalizeTriangle` |
| `KST.Fibration.ScaffoldBaseChangeCoefficientNaturality` | `IC.Stable.Transport.ScaffoldBaseChangeCoefficientNaturality` | `endpointSpan_heq`, `pointTriangle` |
| `KST.Fibration.ScaffoldBaseChangeRightPoint` | `IC.Stable.Transport.ScaffoldBaseChangeRightPoint` | `appendPointTriangle`, `point_normalize_inv` |
| `KST.Fibration.StraighteningBaseChangeVertex` | `IC.Stable.Straightening.StraighteningBaseChangeVertex` | `firstVertex_zeroSimplex` |
| `KST.Fibration.PointedLeftResolutionVertices` | `IC.Stable.Transport.PointedLeftResolutionVertices` | `uliftMapVertex`, `uliftOppositeVertex` |
| `KST.Fibration.StraighteningUnderRealizationChart` | `IC.Stable.Straightening.StraighteningUnderRealizationChart` | `mapNormalizeCompositionWithEq` |
| `KST.Fibration.ScaffoldCocartesianBaseChange` | `IC.Stable.Transport.ScaffoldCocartesianBaseChange` | `appendPoint`, `recoverPoint` |

## R45 と段 G の入力

向きを区別して再計測した。以下は ∞ 層 → KST 各領域の直接 import 辺で、旧計画の 24・19 を現行値として流用していない。

| 参照先 | W2c 前の実測 | 最終 | 中核発 | 参照元 |
| --- | ---: | ---: | ---: | --- |
| KST.LocalizingInvariants | 20 | 160 | 0 | Derived |
| KST.NonConnective | 19 | 19 | 0 | Derived |

LocalizingInvariants の 160 辺のうち 141 辺は今回の移動先から出ている。R52 79・R68 50・R69 6・R70 1・R56b 5、既存 Derived 19。一般の Verdier 分数・安定圏補題の正本を段 G で作った後に付け替え、BF・局所化不変量など K 固有のデータを使う適用は上層に残す。NonConnective の 19 辺は従来の Derived 17 利用元からで、DG の懸垂・Kappa・Yoneda 比較の一般部分を分離する候補、非連結 K 理論固有の入力は KST に保持する。W2c では新しい数学やこの追加分離を行っていない。

全辺・利用元・旧定義元・処置案、領域外への出辺の再計測も [w2c-section7-stage-g-input.json](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/scripts/refactor/targets/w2c-section7-stage-g-input.json) に収録。既存の [w2c-stage-g-input.json](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/scripts/refactor/targets/w2c-stage-g-input.json)（混在 367 の分類、保留 98、K 固有 211、R56b 一般補助）を保持する。M16 は CosliceTwistedHomEquivalence の Reedy 非依存の証明か F1 twisted arrow の再編。private 15 辺は同じ JSON の R60 入力に収録した。

## コミット

- `d9941f412` 群 A：辺の切断
- `cd4b4aa53` 群 A′：HA の入口
- `c68fdf421` 補充と分割スコープの整理（群 A 内部 round 2）
- `92401dd29` 補充（群 A 内部 round 3）
- `2297136d8` 補充（群 A 内部 round 4）
- `051fdc38c` 補充（群 A 内部 round 5）
- `c2eda1333` 補充（群 A 内部 round 6）
- `eb9e22101` 群 B：R51 の配置
- `a7604cfdd` 群 B：R68 の配置
- `e805ace85` 群 B：R52 の配置
- `866218b0e` 群 B：R69 の配置
- `55a630c81` 群 B：R70 の配置
- `ed53aeacb` 群 B：R56b の配置
- `9f0949ef9` 補充（群 B 内部 round 2）
- `e1e8ddf7c` 補充と生成名の復元（群 B 内部 round 3）
- `ca091dbdc` 補充（群 B 内部 round 4）
- `0a130c3c0` 補充（群 B 内部 round 5）
- `69a2c0fad` 補充（群 B 内部 round 6）
- `377713b67` 補充と private 参照の復旧（群 B 内部 round 7）
- `df60b4d55` IF-W2c §16：内部 round 7 の再発停止を記録
- `0a340e47f` IF-W2c：局所 instance 監査と停止記録を訂正
- `af0b57c8a` 補充の宛先を修正（群 B 内部 round 8）
- `555ed8bdc` IF-W2c 停止点2：内部検証と保存比較を記録
- `eb16fee32` IF-W2c：下流検証前に main を取り込み
- `4e4fdc38d` 補充（W2c 下流 round 2）
- `80ff7be93` IF-W2c：監査の追従
- `d52f1fc44` IF-W2c：監査の既存形式に合わせて import を修正
- `ceda0bd3b` IF-W2c：分割後の監査 import と定義元一覧を補充

この後のコミットは本報告・段 G 入力・最終 ratchet 基準のみ。証跡と実行スクリプトは /Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/.lake/verify/ifw2c-downstream。
