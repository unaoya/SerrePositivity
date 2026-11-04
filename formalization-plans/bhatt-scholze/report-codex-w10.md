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

## B-2 作業中の保存（2026-11-04）

B-1 は承認済み。承認された定義・主張は維持している。消失防止の中間実装コミットは `7feaa4051`（**未検証、B-2 停止点ではない**）。合成・nil 核全射・純非分離体拡大・完全環から被約環への全単射性の証明、Spec の普遍単射性との比較を介した底変換の証明を書いた。標数 p の判定は逆方向と順方向の nil 核条件を書き、順方向の元ごとの p 冪条件を残している。完全環からの全単射性はこの未完の判定定理に依存するため、まだ証明済みとは数えない。

ビルド初回は `UniversalHomeomorphism.Basic` のみ実行され、6.6 秒で型検査エラー。nil 核全射は通過したが、合成の API と剰余体写像の書き換え等を修正中。以後の単体ビルドは `ps` と共通ロックの空きを待機している。この保存時点では新版のビルド成功を確認していない。

**取り込み方針の更新（ユーザー追記）**：B-3 が完了し全 11 件の `sorry` が 0 になっても、Codex 自身は main に取り込まない。`codex/bs-w10-b` にコミットしたところで停止・報告する。CA 監査の再生成と論文の層の B4 との衝突確認、および main への取り込みは調整役が行う。作業途中もこのブランチへこまめにコミットする。

### 中間保存の追記

- 実装の追加保存は `f04ffbb21`。新しい `UniversalHomeomorphism/PowerClosure.lean` に p 冪閉包と導手、その根基性を置いた。この補助モジュールは第 2 回の単体ビルドで型検査を通った（コンパイル 3.7 秒、軽微な linter 警告はその後修正）。本体には単射な中間環への因子化と、導手の逆像が極大イデアルを含む場合の全射性の補題も書いた。
- 第 2 回の `UniversalHomeomorphism.Basic` ビルドは壁時計 12.3 秒でエラー。剰余体と Spec の比較、標数の補題の名前・引数等を修正した。最新版を検査する第 3 回は、他作業のビルドと共通ロックの空きを待機中。したがって **`f04ffbb21` 全体のビルド成功は未確認**。
- 明示的な `sorry` は普遍同相側 1 件（標数 p 判定の順方向）、層別側 5 件。これは証明済み宣言数の報告ではない。完全環からの全単射性は未完の判定に依存し、新しく書いた補題も再検証が必要。
- 残る順方向の方針：p 冪閉包を中間環とし、有限部分代数に帰着する。導手の逆像の極小素イデアルで局所化し、導手の根基性から局所補題の仮定を得る。局所全射性と有限生成元の共通分母から、導手に属しつつその素イデアルには属さない元を作って矛盾させる。局所化後の p 乗根閉性、普遍同相の移送、有限生成元の分母払いの Lean 実装はまだ完了していない。

**B-2 は未到達。** 全ビルド・verify・監査・main への取り込みは行っていない。


### W2c 停止点 2 までのビルド休止（2026-11-04）

ユーザー指示により、W2c 群 B の内部検証を優先し、**W2c 停止点 2 の連絡まで BS-W10 のビルドを休止する**。次のビルド予約は残していない。休止指示と待機解除の行き違いで第 5 回が開始したが、13.9 秒で終了したことを確認した。以後、新しいビルドは起動していない。

今回の中間実装コミットは `f3d1941b7`、その後の型検査エラーを修正した保存は `9bc0cc85a`。いずれも `codex/bs-w10-b` のみで、main は変更していない。

- `Localization.lean` を追加し、p 乗根閉性の局所化、導手の逆像の局所化に関する包含、有限個の加群生成元の分母払いを実装した。この補助モジュールは第 4・5 回で型検査を通過し、第 5 回では linter 警告もない。
- 順方向の証明は最後まで記述した。p 冪閉包を中間環に取り、一元生成有限部分代数に帰着する。導手の逆像の極小素イデアルで局所化し、局所的な全射性と有限生成元の共通分母から矛盾を導く。
- 中間環の radicial 性は無条件に仮定していない。今回の整な塔では上段も整であり、包含の単射性から上段の Spec は全射になる。この全射性で点を持ち上げ、剰余体の塔の純非分離性と合わせて下段の radicial 性を示す `isUniversalHomeomorphism_tower_bot` を明示した。
- 普遍同相ディレクトリのソース上の明示的な `sorry` は 0 件になった。ただし **本体のビルドはまだ成功していないため、6 件の証明完了とは報告しない**。層別側の 5 件は未着手で維持している。

追加の単体ビルド実測（いずれも実行前の `ps` 確認、`with_build_lock --wait 0` 使用、待機時間を除く）：

| 回 | 対象 | 秒 | 結果 |
| --- | --- | ---: | --- |
| 3 | UniversalHomeomorphism.Basic | 12.6 | PowerClosure 成功、Localization の型検査エラー |
| 4 | UniversalHomeomorphism.Basic | 13.7 | Localization 成功、本体の型検査エラー |
| 5 | UniversalHomeomorphism.Basic | 13.9 | Localization 成功、本体に 5 箇所の型検査エラー |

第 5 回の残りは Spec の剰余体比較 2 箇所、局所化のスカラー作用 1 箇所、素イデアルの型推論 1 箇所、像への所属の変換 1 箇所。`9bc0cc85a` ではこれらを修正したが、**ビルド休止のため再検証していない**。直接 importer の `EtaleStratification.Stratification` は本体成功後に検査する。全ビルド・verify・監査の実行はない。

これは消失防止の中間報告であり、**B-2 停止点には未到達**。W2c から鍵が解放された後、最新ソースの単体ビルドと必要な修正を再開する。


### ビルド休止中の B-3 編集（2026-11-04）

ユーザーから、再開連絡まではビルドせず、B-3 の証明編集と中間コミットを進めてよいとの指示を受けた。**この追記に対応するビルドは 0 回**。再開連絡後は、指定どおり `UniversalHomeomorphism.Basic`、`UniversalHomeomorphism.PowerClosure` の単体ビルドから再開する。B-2 の完了報告はその検証後に行う。

未検証の編集を `164d31833` に保存した。承認済みの主張・定義は変更していない。

- `etale_of_finite_separable` の証明を記述した。分離拡大の形式的エタール性と、体上の有限型代数の有限表示性を使う。
- 有限個の係数を含む有限生成 noetherian `StrataBase p` 部分代数を取る補題を書いた。`exists_noetherianApproximation` 全体のモデル構成・有限性はまだ残る。
- 極小点の有限性、`hZp` と p の可逆性から剰余体の標数 0 を得る補題、有限体拡大の相対分離閉包による有限エタール・純非分離分解を書いた。標数 0 の場合の後半の全単射性も記述した。
- `generic_structure` の後半でこれらを使用した。未完の部分は、全商環の剰余体積との同定と、有限被約代数を基底の極小点で添字付けられた有限体拡大の積へ分解する部分。

層別側の明示的な `sorry` は **4 件**：noetherian 近似、一般点での上記の環分解、分解の主開集合への広げ、最終的な有限層別。普遍同相側はソース上 0 件だが本体は再検証待ち。今回の編集も型検査未実施のため、B-2・B-3 とも完了扱いにはしない。main・監査ファイルは変更していない。


## 停止点 B-2（2026-11-04）

**B-2 到達。** 普遍同相側の当初の 6 件をすべて証明し、指定の単体ビルドが成功した。実装コミットは `b1bc9d7cb`、ブランチは `codex/bs-w10-b`。main への取り込みは行っていない。最新のユーザー指示に従い、この報告を保存した後、層別側の単体ビルドへ進む。

### 証明と配置

- `UniversalHomeomorphism.Basic`：承認済みの普遍同相の定義を維持し、底変換、合成、nil な核を持つ全射、標数 p の判定、完全環から被約環への全単射性、純非分離体拡大の場合を証明した。
- `UniversalHomeomorphism.PowerClosure`：元ごとの p 冪閉包、部分環の導手、p 乗根閉性から導手の根基性を得る補題。
- `UniversalHomeomorphism.Localization`：p 乗根閉性の局所化、導手の逆像の局所化に関する包含、有限個の加群生成元の分母払い。

標数 p の判定の順方向は、p 冪閉包を中間環に取り、一元生成の有限部分代数へ帰着する。中間環への radicial 性の継承は、整な上段の Spec 全射と剰余体の塔を使って明示的に証明した。有限の場合は導手の逆像の極小素イデアルで局所化し、剰余体の純非分離性と導手の根基性から局所全射性を得る。有限生成元の分母を同時に払うことで、導手に属しながらその素イデアルには属さない元を作って矛盾させる。

核の条件は引き続き **`RingHom.ker f ≤ nilradical A`** であり、イデアルとしての冪零性は仮定していない。定義・当初の定理の主張を弱めていない。新しい公理や原典との差分はない。

普遍同相ディレクトリ 3 本の明示的な `sorry` は **0 件**。今回は本体の型検査も成功しており、以前の「ソース上 0 件だが未検証」とは区別する。層別側は B-3 の編集中であり、残る `sorry` は 4 件。

### ビルド実測

再開許可後も各実行直前に `ps -axo command=` で他のビルド・verify を確認し、共通鍵 `with_build_lock --wait 0` を使用した。鍵が占有されている間は待機し、CA の新規モジュール以外は対象に指定していない。以下は壁時計時間で、鍵待ちを除く。

| 回 | 対象 | 秒 | 結果 |
| --- | --- | ---: | --- |
| 6 | UniversalHomeomorphism.Basic | 17.7 | Spec 比較のタイムアウトと局所化の型クラス推論エラー |
| 7 | UniversalHomeomorphism.Basic | 8.2 | 局所化 API の名前・インスタンス指定エラー |
| 8 | UniversalHomeomorphism.Basic | **8.3** | **成功、警告なし** |
| 8 | UniversalHomeomorphism.PowerClosure | **3.9** | **成功、警告なし** |

最終の指定 2 本は合計 **12.2 秒**。`Localization` は第 5 回で成功したソースのまま、今回の `Basic` の依存として確認されている。Spec の比較には自然性補題の引数を明示し、heartbeat 上限の引き上げをせずにタイムアウトを解消した。ビルドラッパー自身のコマンドを検出する「existing lake build」の表示は出るが、実行前の確認で他のビルドがないことを確かめている。

全ビルド・verify・監査は実行していない。`git diff --check` は通過。CA の監査再生成・B4 との衝突確認・main への取り込みは、B-3 完了後も調整役に委ねる。

### 次の作業

`EtaleStratification.Stratification` の単体ビルドを行い、休止中に記述した有限分離拡大・一般点・相対分離閉包まわりの証明を検証する。残りは noetherian 近似、一般点の環分解、主開集合への広げ、有限層別の構成。大きい補題が残るため B-3 は複数作業窓を見込み、最初の検証結果を見て見積もりを更新する。W2c の下流・verify 開始の連絡があれば、再びビルド待機を解除する。


### B-2 直後の直接 importer と B-3 編集の検証（2026-11-04）

指示どおり、B-2 の報告保存後に `EtaleStratification.Stratification` へ進んだ。第 1 回は 6.5 秒で、有限型から有限表示への含意の向きと、標数 0 の判定補題の引数指定の 2 箇所にエラーが出た。修正後、W2c の round 終了を待ち、再び `ps` 確認と `with_build_lock --wait 0` を経て第 2 回を実行し、**12.4 秒で成功**した。

鍵待ち中には、モニック多項式の係数が部分代数に含まれれば整性をその部分代数上に降ろせる補題と、有限個の整な生成元の関係式の係数を一つの有限集合へまとめる補題を追加した。これらと既知エラーの修正は `2fbe55bab` に保存済み。第 2 回はこのコミットのソースを検証している。

これにより、有限分離体拡大のエタール性、極小点の有限性、p 可逆な剰余体の標数 0、相対分離閉包による分解、有限生成 noetherian 部分代数の選択、上記の整性の係数補題は型検査を通過した。B-3 の `sorry` は引き続き **4 件**（noetherian 近似の全体、一般点の環分解、主開集合への広げ、有限層別）。このため **B-3 完了ではない**。

第 2 回の警告は残る 4 件の `sorry` と、補助定理 `exists_integrality_coefficients` の `[Fintype ι]` を `[Finite ι]` に弱められるという linter 警告 1 件。追加のビルド枠をこの軽微な改善だけに使わず、次の B-3 編集時に処理する。

B-2 本体と指定された `PowerClosure` に加え、直接 importer の `Stratification` も成功を確認済み。普遍同相側 0 件・層別側 4 件の状態で `codex/bs-w10-b` に保存し、main には取り込んでいない。この追記時点でビルド待機処理は終了しており、BS-W10 は鍵を保持していない。


### W2c main 取り込み後の B-3 中間保存（2026-11-04）

ユーザーから W2c の main 取り込み `c2979a262` と小さなビルドの再開許可を受け、B-3 を再開した。worktree の基準を勝手に更新せず、既存の `codex/bs-w10-b` 上で続行している。

- `2a7dcc636`：noetherian 近似の証明を最後まで記述した。有限表示の関係式と各生成元のモニック関係の係数を含む有限生成部分代数を選び、生成元の像が作る部分代数を有限モデルとする。Mathlib の `Presentation.ModelOfHasCoeffs` の底変換同型と比較して、選んだ有限モデルも元の代数へ戻ることを示す。
- 同コミットで `GenericPoints.lean` を追加。極小点の定義を移し、被約 noetherian 環の全商環を極小点の剰余体積として記述する証明を書いた。極小素イデアルを分離する元を使って、成分ごとの分数表示の分母を一つにまとめる。
- `cbe9431f1`：`FiniteFieldProduct.lean` を追加。体の有限積上の有限代数の被約化を極大イデアルによる有限体積へ分け、各体への構造射が基底のどの体を経由するかを明示した。`generic_structure` へ接続済み。
- その後、全極小点を含む開集合の中に、全極小点を含む主開集合を選ぶ補題を追加した。主開集合へ広げる段階に用いる。

**この中間保存の追加証明は未検証**。再開後の単体ビルドは `ps` の確認と共通鍵の空きを待っており、確認時には G1 worktree の `warm_build_dir.sh` が鍵を保持していた。鍵を迂回した実行はしていない。

ソース上の明示的な `sorry` は層別側 2 件（`spread_out_generic` と `exists_finiteEtaleStratification`）になったが、これは B-3 の検証済み進捗件数ではない。残りの数学的な実装は、一般点の分離部分の逆像として有限部分代数を取り、エタール locus・導手や有限生成関係の分母払いにより主開集合へ広げる部分と、noetherian 帰納・底変換・被約化・p による細分で有限層別を作る部分である。B-3 は未完了であり、main への取り込みは行っていない。

### B-3 再開後の補助証明と共有鍵待ち（継続中）

- 単体ビルド `bsw10-b3-03` は 8.3 秒で失敗。`GenericPoints` の素イデアル instance と
  有限 inf の型指定、`FiniteFieldProduct` の積の Algebra instance を修正した。
- `bsw10-b3-04` は 8.0 秒で失敗。体積の分解部分は通った。`GenericPoints` の
  `I` が `Submodule` として推論された箇所は `Ideal.IsPrime I` と明記して修正した。
  その後の拡張を含む現行版はまだ未検証。
- 次の `Stratification` 単体ビルドは、`ps -axo command=` と共有鍵の空きを確認する
  待機処理に置いている。G1 の検証および B4 の待機と競合しており、現時点では未起動。
  起動時には `with_build_lock --wait 0` を使う。
- 待機中に、残る二つの主証明で使う以下の補題を書いた（すべて現行版はビルド未確認）。
  - `NoetherianInduction`：真のイデアルの外に元を選ぶ操作から有限列を構成。
  - `GenericVanishing`：有限加群の消滅、全射性、エタール locus を全極小点を残す主開集合へ延長。
  - `GenericModel`：局所化後の部分代数の逆像が有限モデルになり、再局所化で元へ戻る。
  - `GenericNil`：有限生成イデアルの生成元の冪零関係について共通分母を選ぶ。
  - `UniversalHomeomorphism.NilDiagonal`：乗法射の nil な核による普遍同相の判定とその逆。
    `Basic` に体値点の一意性からの判定を追加。B-2 の既存証明・主張は変更していない。
  - `ReducedEtale`：任意の被約基底上の有限エタール代数が被約であること。
  - `FiniteFieldProduct` に積の成分への有限エタール射と、成分ごとの有限エタール性の積を追加。
- 中間保存 `7dae5c5ff`、`146012af2`。明示的 `sorry` は `spread_out_generic` と
  `exists_finiteEtaleStratification` の二つが残っており、B-3 完了とは報告していない。
  main には一切取り込んでいない。

### B-3 補助証明の追加保存（単体ビルド 05 の開始待ち）

- `Factorization` に被約主開層・分解の定義を移し、p 反転の関手性、同型に沿う分解の移送、
  `(p g, g)` による標数の細分を追加。承認済みの定義・主張の型は変更していない。
- `StratumQuotient`：R/I の被約初層と R の I 上の層の標準同型。
- `GenericEtale`：微分加群と第一余接ホモロジーの有限性・消滅からエタール性を延長。
- `GenericBijective`：局所化後の核・余核の消滅から、有限加群の同型を一つの分母へ延長。
- `GenericSeparable`：有限純非分離体拡大の積の普遍同相性と、有限積での p 反転後の全単射性。
- `UniversalHomeomorphism.Reduction`：被約化の自然な射、その普遍同相性、局所化との両立。
- `NilDiagonal` の判定には Spec 全射性を使わない方向も追加した。一般点への局所化を合成した
  射を扱うため、体値点の一意性から対角イデアルが nil であることを導く。
- 途中保存：`ceed5ea8a`、`09de10bfa`、`0cc048d38`、`f257f9c48`。
  この節の追加分も未検証であり、完成・ビルド成功とは報告しない。
- 共有鍵が空いていた時点にも `ps` で main の監査を確認したため、ビルドは開始していない。
  B4 の単体ビルドが動いている間も待機を継続。全ビルド・verify・監査の実行はしていない。
- `spread_out_generic` と `exists_finiteEtaleStratification` の接続は未完了。main への取り込みはなし。

### B-3 継続：単体ビルド 05・06 と一般点の有限モデル（11-04）

- 共有鍵の待機後、`EtaleStratification.Stratification` の単体ビルド 05（18.0 秒）と 06（10.8 秒）を実行。各回とも実行直前の `ps -axo command=` 確認と `with_build_lock --wait 0` を使用。
- 06 で `GenericPoints`、`GenericVanishing` に続き、`FiniteFieldProduct`、`NoetherianInduction`、`GenericNil`、`GenericEtale`、`ReducedEtale`、`GenericBijective` と追加後の `UniversalHomeomorphism.Basic` が通った。`NilDiagonal` と `Reduction` に残った型の不一致は修正し、07 を待機中。
- `generic_structure` と体ごとの分離部分の補題を `GenericStructure` に整理し、`GenericFactorization` に有限エタール部分代数の構成を記述した。これらの検証は依存先の修正後に進める。
- 待機中に `GenericLocalization`（被約一般ファイバーの局所化）、`GenericSpread`（逆像モデルのエタール性の延長）、`GenericKernel`（nil な核の延長）を記述。これら 3 本はまだビルドしていない。
- 元の主張に残る `sorry` は `spread_out_generic` と `exists_finiteEtaleStratification` の 2 件。一般点からの延長と、商環・底変換を通した有限層別の組み立てが未完了。B-3 の完了報告ではない。
- 作業範囲の変更のみを `codex/bs-w10-b` に保存。main への取り込み、全ビルド、verify、監査は実施していない。

### B-3 継続：verify 待機中の延長証明の接続（11-04）

- 07 の単体ビルドはまだ開始していない。`ps` で B4 の `verify.sh` と別プロジェクトのビルドを確認し、共有鍵の取得前で待機を継続。
- `GenericRadicial` で、局所化後の体値点の一意性 → 対角核の nil 性 → 主開集合上の普遍同相、という接続を記述した。部分代数への制限が radicial 性を保つとは仮定していない。
- `GenericPrimeVanishing`・`GenericPrimeSpreading` で、有限余核の p 冪 torsion の分母払いを p 反転後の同型に接続した。
- `ReducedModel`・`ReducedSpread` で、一般点の部分代数の逆像に有限モデルを取り、三つの分母の積を選ぶ証明を記述した。これを両環の被約化に適用する `spread_out_generic` の本文も記述。
- 明示的な `sorry` は `exists_finiteEtaleStratification` の 1 件になったが、上記の接続は未検証。ビルド成功を意味しない。商環上の帰納、p の二場合への細分、noetherian 近似からの底変換が引き続き必要。
- main への取り込み・全ビルド・verify・監査は行っていない。

### B-3 継続：最終定理の証明草稿まで接続（11-04、未検証）

- `PrincipalOpen`・`FactorizationLocalization`・`StratumLocalization` を追加し、主開集合への制限を接続。Noetherian 帰納では各段で p 可逆な部分を先に選び、そこが空なら p = 0 の部分を選ぶことで二場合への細分を記述した。
- `FactorizationBaseChange` で、有限エタール分解を底変換後の被約化へ移す証明を記述。p 反転後の全射性は p 冪倍の像への所属をテンソル積と商に移し、単射性は被約な有限エタール中間代数と普遍同相の nil な核から導く。
- `StratumLift`・`ReducedTensorProduct`・`StratumBaseChange`・`StratumEquiv` で、層の普遍性、被約テンソル積との同型、代数同型による移送を記述。これらを用いて `exists_finiteEtaleStratification` の本文まで接続した。
- **ソース上の `sorry` と新規 `axiom` は 0 件。ただし B-3 完了ではない。** 単体ビルド 07 は他作業の verify・ビルドが続いているため未開始であり、上記の後半は未検証。今後、型検査のエラーを解消し、指定された単体ビルドの成功を確認する必要がある。
- 現在の保存先は引き続き `codex/bs-w10-b` のみ。main への取り込みは行わない。

### B-3 継続：単体ビルド 07（19.7 秒）

- B4 の verify 終了後の空き時間に、実行直前の `ps -axo command=` 確認と `with_build_lock --wait 0` を経て `EtaleStratification.Stratification` を実行した。19.7 秒で失敗。
- `UniversalHomeomorphism.Basic`、`NilDiagonal`、`Reduction` と、`GenericBijective`、`GenericPrimeVanishing` の成功を確認。対角核の nil 性、被約化の射、p 冪 torsion の分母払いが型検査を通った。
- 残ったエラーは `PrincipalOpen`、`GenericKernel`、`GenericModel`、`Factorization`。主に局所化射の展開、部分加群の局所化 instance、依存型を含む書換え、補題の明示引数の指定であり、修正を `6c38326fe` に保存した。先行する API 引数修正は `d20d0f848`。
- 次の単体ビルド 08 は B4 の監査と別プロジェクトのビルドを検出して開始待ち。全体の `sorry` はソース上 0 件だが、後半の型検査は未完了であり、B-3 完了ではない。main への取り込みは行っていない。

### B-3 継続：単体ビルド 08〜17

いずれも `EtaleStratification.Stratification` の単体ビルドで、実行前の `ps -axo command=` 確認と `with_build_lock --wait 0` を使用。競合時は待機した。所要時間は順に 13.5、9.3、14.3、12.1、8.9、24.8、10.2、20.1、26.8、13.2 秒。最終定理までの成功にはまだ至っていない。

この区間で以下の現行証明が通過した。

- 有限モデルの局所化、一般点のエタール性・nil な対角核・p 反転後の全射性の延長。
- 一般点の構造定理、分離部分の有限エタール部分代数の構成、三つの分母を持つ有限モデル。
- 有限エタール分解の主局所化と被約底変換。
- 商環の初層と元の層の同型、二段階の主局所化、被約層からの射の延長。

08〜13 の修正は `f80d744e0`・`4c1d880ee` などに保存した。12 では、同型の定義中に未確定引数が残ったエラーに続いて Lean の内部エラーが出たが、引数を明示した 13 では再発していない。

17 時点の検査停止箇所は `ReducedSpread`、`ReducedTensorProduct`、`StratumEquiv`。修正を保存し、18 を待機中。底変換した層の比較と最終定理も引き続き検証が必要であり、ソース上の `sorry` 0 をもって B-3 完了とはしない。main・全ビルド・verify・監査には触れていない。

## 停止点 B-3：Lemma 10.12 の証明完了（2026-11-05）

### 結果

`exists_finiteEtaleStratification` まで単体ビルドに成功した。B-3 の残り 4 件（`exists_noetherianApproximation`、`generic_structure`、`spread_out_generic`、`exists_finiteEtaleStratification`）をすべて証明した。B-2 を含む新規 36 ファイル（`UniversalHomeomorphism/` 6 本、`EtaleStratification/` 30 本）に `sorry`・`axiom`・`admit` は 0 件。最終ビルドに `sorry` の警告はない。

承認された主張を保ち、表示の係数による Noetherian 近似、一般点での分離部分、主開集合への延長、イデアルの Noetherian 帰納、p 可逆／p = 0 の細分、元の基底への被約底変換を接続した。「核が nil」は各元が冪零という意味のままで、イデアルの冪零性に置き換えていない。有限生成部分代数への制限が radicial 性を保つという仮定も使っていない。原典から主張を変更した点はない。

### 最終の検証

対象はいずれも `SerrePositivity.CommutativeAlgebra.EtaleStratification.Stratification`。各回とも実行直前の `ps -axo command=` と共有鍵の空きを確認し、`scripts/refactor/with_build_lock.sh --wait 0 -- lake build <module>` を使用した。

| 回 | 実測 | 結果 |
|---|---:|---|
| 18 | 16.1 秒 | 被約テンソル積・代数同型による層の移送が成功。後続 2 本で失敗。 |
| 19 | 20.4 秒 | 底変換の射と局所化の型指定を修正。 |
| 20 | 20.1 秒 | 全補助モジュールが成功し、Stratification 本体の接続で失敗。 |
| 21 | 13.5 秒 | Noetherian 近似の内部証明に残るエラーを確認。 |
| 22 | 9.5 秒 | 像への制限写像の値を展開する等式 1 箇所が残った。 |
| 23 | **14.5 秒** | **成功。最終定理まで型検査を通過。** |

23 のログは `/private/tmp/bsw10-b3-23.log`。末尾は `Build completed successfully (2955 jobs).`。これは指定した 1 モジュールの依存関係を含む Lake の表示で、全ビルドではない。`Basic`・`PowerClosure` を含め、新規両ディレクトリのモジュールはこの依存関係内にある。B-2 の個別ビルド成功は前節に記録済み。

残る警告は長い行、未使用の simp 引数・tactic、`letI` を `let` にできる箇所などの linter 警告のみ。`git diff --check` も通過した。全ビルド・verify・監査・監査ファイル再生成は行っていない。

### 保存と引き渡し

- 証明の最終コミット：**`57556801e`**（`codex/bs-w10-b`）。途中保存もすべて同ブランチ。
- この報告は別の報告コミットに保存する。ステージ対象は作業ファイルを個別指定し、`git add -A` は使っていない。
- **main には取り込んでいない。** CA の監査再生成、論文の層の B4 との衝突確認、main への取り込みは調整役に委ねる。
- B-3 の残作業はなく、この報告・保存で停止する。ビルドも待機処理も終了しており、共有鍵を保持していない。

## main 取り込み準備：マージと監査登録（2026-11-05）

- 調整役の指示に従い、`codex/bs-w10-b` に main `9f59541d3` をマージした。マージコミットは `37da02200`。`-X theirs` で main 側を優先し、手動で解決する衝突は発生しなかった。main 自体には取り込んでいない。
- `scripts/make_area_audits.py` を実行。変更は `scripts/audit/shared.lean` のみで、対象は 641 → 677 モジュール。新規 CA 36 モジュールの import と登録を追加し、監査本体・許可する公理は変更していない。監査登録のコミットは `ba8e73804`。
- 新規モジュールは `UniversalHomeomorphism/` 6 本と `EtaleStratification/` 30 本。両ディレクトリ外のソースに直接 importer はなく、内部の直接 importer はこの 36 本に含まれる。
- `drafts/A8/Stratification.lean` の削除は既に本ブランチの履歴に含まれる。
- 検証対象を上記 36 本の単体ビルドと shared 監査の単独実行に限定した。各実行直前に `ps -axo command=` を確認し、`with_build_lock --wait 0` を使い、各単体ビルド後に鍵を解放する。main のビルド成果物の同期は完了したが、この記録時点では F-1 等との競合により、マージ後の単体ビルドと監査実行は未開始。成功報告ではない。

### 検証の途中経過と競合判定の確認

新規 CA 36 本のうち、辞書順の `Factorization` から `GenericPoints` まで 12 本の単体ビルドに成功した。F-1 の verify と競合し、続きは共有鍵の解放待ち。

これまでは別プロジェクトのビルドも待っていたが、2026-11-05 のユーザー確認で、`ps` の競合判定を **SerrePositivity の worktree 間に限定**することが承認された。以後は `ps -axo command=` と PID ごとの作業ディレクトリを確認し、別プロジェクトを除外する。SerrePositivity のビルド・監査・verify と共有鍵の使用中は従来どおり待機する。成功済み 12 本と成果物同期を再実行せず、残り 24 本と shared 監査から再開する待機処理へ切り替えた。

## 取り込み準備完了（2026-11-05）

F-1 の verify が終了して共有鍵が解放された後、残りの単体ビルドと shared 監査を完了した。

- main `9f59541d3` の取り込み：`37da02200`。main 側優先でマージし、未解決・手動解決の衝突なし。
- shared 監査の再生成・登録：`ba8e73804`。641 → 677 モジュール、新規 CA 36 本の import と登録だけを追加。監査ロジック・許可ファイル・許可公理は変更なし。
- **新規 36 モジュールすべての単体 `lake build` が成功**。内訳は `UniversalHomeomorphism/` 6 本、`EtaleStratification/` 30 本。直接 importer は両ディレクトリ内に収まり、これら 36 本の検査に含まれる。外部の直接 importer は 0 本。
- ビルドの実行時間の合計は **159.8 秒**（各 3.9〜5.4 秒、鍵の待機時間を除く）。`Basic`・`PowerClosure`・`Stratification` も個別に成功。
- **shared 監査の単独実行が成功**（112.4 秒、終了コード 0）。実行コマンドは `scripts/refactor/with_build_lock.sh --wait 0 -- lake env lean scripts/audit/shared.lean`。

監査出力：

```text
17600 declarations in 677 modules checked; 27 depend on sorryAx through the allowed quotations
```

許可済み引用経由の依存は上記のとおりで、監査にエラーはない。新規 CA ディレクトリの `sorry` 0 を維持し、検収済みの証明ソースには今回の取り込み準備による変更を加えていない。

各実行直前に `ps -axo command=` を確認し、`with_build_lock --wait 0` を使用した。途中からはユーザー確認に従い、PID の作業ディレクトリも調べて SerrePositivity の worktree 内に競合判定を限定した。各単体ビルド後に鍵を解放し、他作業のビルド・監査・verify 中は待機した。全ビルド・verify は実行していない。

ログは `/private/tmp/bsw10-main-integration.log`、個別結果・所要時間は `/private/tmp/bsw10-main-integration-results.json`。検証キューは終了済み。`git diff --check` も通過した。`drafts/A8/Stratification.lean` の削除はブランチ差分に含まれる。

**main には取り込んでいない。** 調整役が `codex/bs-w10-b` を取り込める状態で停止する。最終のこの報告だけをパス指定でステージしてコミットする。S4 の追加依頼で書いた篩・切断比較の草稿は別ブランチ `codex/bs-s4-sieve-comparison`（`51c1162c3`、未ビルド）に分離し、この取り込みには含めていない。

検証中に main は `55b419a24` まで進んだ（F-1 と G2 の先行分、S4 草稿の追加）。今回の検証基準は取り込んだ `9f59541d3`。その後の main 更新には、新規 CA 両ディレクトリ、`scripts/audit/shared.lean`、`scripts/make_area_audits.py`、本報告の変更がないことを確認した。S4 草稿の更新は別ブランチで追従する。
