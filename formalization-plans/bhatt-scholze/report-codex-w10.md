# BS-W10 作業報告

## 停止点 A-1（2026-11-04）

基準 `d7ebde0e6`、ブランチ `codex/bs-w10-a`。新モジュールで直接証明の補題と `isIntegralPerfectoid_finPi` の型検査が通った。原典との定義の差はなく、p 正則性も仮定しない。

### 分割と到達性

- `Perfectoidization/CompletedTensor.lean` の名前を保ち、末尾の有限直積節と `Derived.IntegralExistence` の import を外した。前半 5 節の宣言・証明は基準コミットと文字列で一致した。
- `Perfectoid/FiniteProduct.lean` に有限直積節を移し、E3 を使っていた証明を削除した。`isIntegralPerfectoid_finPi` の名前・引数順と `finiteProduct_perfectoidization_exists_algEquiv` の証明を保った。
- BS ルートに新モジュールを登録した。利用側の変更は `ExcisionTor`・`FiniteComparisonExcision`・CLMST の `ConstantRank` の import 行だけ。`git status --short` の Lean 差分はこれら 6 ファイル、`git diff --check` は通過。
- 仕様 §2 の対象に沿って Lean ソースの import を再帰探索した。drafts の異なる起点 111 個のうち `Inputs.PerfectoidizationInterface` に到達するものは `[]`。`CompletedTensor` と `FiniteProduct` を個別の起点にしても到達しない。

### 型検査と残る証明

`not_isUnit_p_prod_left` は第 1 射影が単元を単元に送ることで証明済み。下表の 10 宣言に各 1 個の `sorry` が残る。各箇所に未実装の理由をコメントした。

| 宣言 | A-2 で埋める証明 |
| --- | --- |
| `isAdicComplete_span_p_prod` | p の冪ごとの合同を両座標に移し、各因子の分離性・完備性を使う。 |
| `modPProdEquiv` | 二つの商への射影の対が全単射であることを示す。 |
| `surjective_pow_p_modP_prod` | 各座標の p 乗根を商の直積同型で戻す。 |
| `perfectionProdEquiv` | Frobenius と両立する二つの係数列を対にする。 |
| `wittVectorProdEquiv` | Witt の射影の対に対して係数ごとの逆を検証する。 |
| `preTiltProdEquiv` | mod p の直積同型を用いて Perfection の射影の対が全単射であることを示す。 |
| `fontaineTheta_prod_compat` | 既存の `fontaineTheta_natural` を第 1・第 2 射影に適用する。 |
| `ker_fontaineTheta_prod_isPrincipal` | 成分の核の生成元の対を Witt 環の同型で引き戻す。 |
| `isIntegralPerfectoid_prod` | 零環因子を分け、非零の場合は上記の判定と擬一様化元の対を使う。 |
| `isIntegralPerfectoid_finPi` | 空積は零環。後続の場合は先頭座標を分離し、二項直積の定理を使う。 |

### ビルド実測と次の区切り

`ps` で他のビルドを確認し、`scripts/refactor/with_build_lock.sh --wait 0 -- lake build SerrePositivity.BhattScholze.Perfectoid.FiniteProduct` を実行。初回は IF-W2c が鍵を保持していたため終了 75、ビルド 0 本。鍵解放後に再確認し、指定 **1 本**が成功した。再試行の壁時計時間 **11.8 秒**、うち新モジュールのコンパイル **6.3 秒**。ほかの変更モジュール・直接 importer のビルドは A-2 に残る。全ビルド・verify・監査は未実施。

A-2 までの作業量は、積の完備性と三つの環構成の同型に 1–2 時間、θ・核・主定理と対象を絞ったビルドに 1–2 時間を見込む（ロック待ちを除く概算）。A-1 で停止し、Lean の差分は worktree に保持する。main への取り込みと作業 B は未着手。

## 停止点 A-2（2026-11-04）

実装コミット `fae7c9ca3`。A-1 の 10 件すべてを証明した。`FiniteProduct` の残る `sorry`・`admit` は 0 件、新しい公理は 0 件。原典との差および主定理の仮定の追加はない。

- 積での p の冪に関する合同を各座標の合同に分解して、分離性と前完備性を得た。mod p の商、Perfection、Witt ベクトルの積同型を構成し、`fontaineTheta_natural` を両射影に適用して θ の両立を示した。核の生成元は二つの生成元の対を Witt 環の同型で引き戻した元になる。
- 零環因子は射影の環同型で処理した。`isIntegralPerfectoid_finPi` は空積を零環とし、後続の場合に先頭座標を分離して二項直積の結果を使う。
- 基準と比較し、芯の前半 5 節、主定理の型と引数順、有限直積の比較同型の証明の一致を確認した。利用側 3 本の変更は import 行だけ。`ExcisionTor` は `CompletedTensor` の直接 import を `FiniteProduct` に置き換えた状態でビルドが通った。
- 仕様 §2 の到達性検査は drafts の 111 起点に対し `[]`。個別に `CompletedTensor` と `FiniteProduct` を起点としても `Inputs.PerfectoidizationInterface` への経路はなかった。
- `scripts/make_area_audits.py` の生成対象を BS・CLMST の 2 本に絞って再生成した。BS（145 モジュール）は新モジュールの import 1 行と `mods` 内の登録 1 件だけ。両方を除くと元ファイルと完全一致した。CLMST（18 モジュール）は再生成前後で同一。監査の実行、全ビルド、verify は 2b の担当範囲。

### 最終ソースの単体ビルド

各回 `ps` で競合ビルドがないことを確認し、`scripts/refactor/with_build_lock.sh --wait 0 -- lake build <module>` を実行した。指定対象のうち `ExcisionTor` が重複するので、異なる 11 本の終了コードがすべて 0。以下はロックの空き待ちを除く壁時計時間。

| モジュール（先頭の `SerrePositivity.` を省略） | 秒 |
| --- | ---: |
| `BhattScholze.Perfectoid.FiniteProduct` | 12.3 |
| `BhattScholze.Perfectoidization.CompletedTensor` | 16.7 |
| `BhattScholze.Perfectoidization.ExcisionTor` | 22.2 |
| `BhattScholze.Perfectoidization.FiniteComparisonExcision` | 17.9 |
| `CLMST.PerfectoidizationIsogeny.ConstantRank` | 23.4 |
| `BhattScholze` | 7.4 |
| `BhattScholze.Almost.Lemma103` | 4.2 |
| `BhattScholze.PerfectoidIdeal.CompletedQuotient` | 4.4 |
| `BhattScholze.Perfectoidization.CompletedBaseChange` | 4.4 |
| `BhattScholze.Perfectoidization.CompletedTensorComparison` | 4.1 |
| `BhattScholze.Perfectoidization.TensorCompatibility` | 9.4 |
| **合計** | **126.4** |

最終確認前には `FiniteProduct` の反復ビルドを 2 回行った。初回は 11.5 秒で型検査エラー、直積の標数インスタンス・完備性の構成・核の comap の式を修正した後は 12.5 秒で成功した。上表はその後の linter 修正を含む最終版の計測である。

作業 A の証明・指定単体ビルド・監査ファイルの再生成まで完了。作業 B（Lemma 10.12）は未着手。

## 停止点 B-1（2026-11-04）

**B-1 到達、ここで停止。** 基準は開始時 main `680c3f593`（A と下書き削除 `5a25042ca` を含む）、ブランチ `codex/bs-w10-b`、実装コミット `9a4437e34`。専用 worktree は `/private/tmp/SerrePositivity-bs-w10` を再利用した。B の変更は main 未取り込み。

### 配置と主張の形

新規ディレクトリの内部は次の 2 モジュールにまとめた。

- `CommutativeAlgebra/UniversalHomeomorphism/Basic.lean` に G-A8-4・5。普遍同相の定義は整性、Spec の全射性、Spec の単射性、各点での剰余体拡大の純非分離性からなる。
- `CommutativeAlgebra/EtaleStratification/Stratification.lean` に Z_(p) の構造射、noetherian 近似、一般点での分解、その広げ、層の具体的な環と射、Lemma 10.12 の結論を配置した。旧 `drafts/A8/Stratification.lean` は移設に伴い削除した。

定義は下書きの内容を保った。核の条件は **`RingHom.ker f ≤ nilradical A`** とし、核の各元が冪零であることを要求する。イデアルに共通の指数を要求する条件は加えていない。標数 p の判定のもう一方は `∀ b : B, ∃ n : ℕ, b ^ (p ^ n) ∈ f.range`。

最終定理は有限表示有限 R 代数 S と `hZp : ∀ q, q.Prime → q ≠ p → IsUnit (q : R)` を仮定し、次の三条件をすべて結論に含める。

1. 有限列 g の生成するイデアルが単位イデアル。
2. 各層の指定された射 `stratumMap (algebraMap R S) (earlierIdeal g i) (g i)` が有限エタール射と普遍同相の合成に分解し、後半の射は p を反転すると全単射。
3. 各層の基底環で p が零、または単元。

層の基底は `Localization.Away (Ideal.Quotient.mk I.radical g)`、標的側は **先に I を S に延長してから根基を取る**。分解の条件には `b.comp a = f` が入り、元の指定射との両立を明記している。原典と異なる定義や仮定の追加はない。

### 定義と定理の実装状況

`strataBaseMap` の局所化の前提は p 以外の素因数が単元になることから証明した。`stratumMap` の根基と局所化に関する前提も Mathlib の API で証明した。**定義・インスタンスの証明穴は 0 件**。下書きの `True` の仮置きは既に BS-D1 で具体化されており、移設後も 0 件。

`generic_structure` では標準射 `genericProductMap` の `toAlgebra` に対応する `Module R (GenericProduct R)` を局所的に明示した。既定の Pi 加群作用を選ぶことでテンソル積の環構造が推論できなくなる問題を解消するためで、構造射や定理の数学的内容は同じ。診断用の設定・trace は最終ソースから除いた。

B-1 の定理の証明穴は **11 件**。それぞれに理由を一行以上添えた。

| モジュール | 宣言 | 残る証明 |
| --- | --- | --- |
| UniversalHomeomorphism/Basic | `isUniversalHomeomorphism_baseChange` | 整性と一点の幾何学的ファイバーの底変換での保存 |
| 同上 | `isUniversalHomeomorphism_comp` | 整性・剰余体の純非分離性・Spec 全単射の合成 |
| 同上 | `isUniversalHomeomorphism_of_nil_kernel` | nil な核をもつ全射の Spec と剰余体の同定 |
| 同上 | `isUniversalHomeomorphism_iff_charP` | 標数 p の nil 核・元ごとの p 冪による判定 |
| 同上 | `isUniversalHomeomorphism_bijective_of_perfect_reduced` | 完全な始域での p 冪根と被約な終域を使う全単射性 |
| 同上 | `isUniversalHomeomorphism_of_isPurelyInseparable` | 純非分離体拡大の唯一の点での剰余体の同定 |
| EtaleStratification/Stratification | `etale_of_finite_separable` | 有限分離体拡大の有限表示性と形式的エタール性 |
| 同上 | `exists_noetherianApproximation` | 表示とモニック関係の係数を含む有限生成部分代数への降下 |
| 同上 | `generic_structure` | 全商環・有限被約代数の体積への分解と相対分離閉包 |
| 同上 | `spread_out_generic` | 有限個の関係の分母を払い、全極小点を含む主開集合へ広げる |
| 同上 | `exists_finiteEtaleStratification` | noetherian 帰納、底変換後の被約化、(pg_i,g_i) による細分 |

### ビルド実測

各実行の直前に `ps -axo command=` の結果で他のビルド・verify がないことを確認し、共通ロック `with_build_lock --wait 0` を取得して `lake build <module>` を実行した。対象は新規 2 本だけ。IF-W2c、2b、その他のビルドが動いている間は待機した。

最終ソースの結果は両方とも終了コード 0。

| モジュール（先頭の `SerrePositivity.CommutativeAlgebra.` を省略） | 秒 |
| --- | ---: |
| UniversalHomeomorphism.Basic | 3.9 |
| EtaleStratification.Stratification | 7.3 |
| 合計 | **11.2** |

型検査の反復は 10 回、各回同じ 2 対象。以下は各 `lake build` の壁時計時間で、ロック待ちは含まない。第 1–9 回は層別側で型検査エラー、第 10 回で両方成功した。

| 回 | UniversalHomeomorphism | EtaleStratification |
| --- | ---: | ---: |
| 1 | 5.8 | 6.7 |
| 2 | 5.8 | 6.5 |
| 3 | 3.8 | 6.2 |
| 4 | 3.6 | 8.1 |
| 5 | 3.6 | 7.5 |
| 6 | 4.1 | 6.8 |
| 7 | 4.4 | 10.5 |
| 8 | 4.4 | 11.9 |
| 9 | 4.4 | 73.7 |
| 10 | 3.9 | 7.3 |

反復全体は **189.0 秒**。第 9 回は型クラス推論の診断ログを取得したため 73.7 秒を要した。
初回は不足 import と商写像 API の適用も修正した。最終版には `sorry` 警告と `generic_structure` 内の長い行に関する linter 警告 1 件が残る。全ビルド・verify・監査は今回実行していない。

### 差分と次の停止点

変更は新規 2 本、旧下書きの削除、本報告の追記に限る。`git diff --check` は通過。B-2 は普遍同相側 6 件の証明で、剰余体の射の両立と標数 p の判定が中心になる。概算は 2–4 作業窓（8–16 時間、ビルド待ちを除く）。B-1 の主張の形の検収を待って停止する。
