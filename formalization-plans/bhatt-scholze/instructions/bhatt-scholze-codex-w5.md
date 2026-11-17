# Codex 作業指示書 BS-W5：Delta/Basic と Delta/Free 直下を数学的な話題ごとにまとめる（40 本 → 9 本）

作成：2026-10-25（BS 作業チャット）、同日改訂（話題ごとの統合に変更、Codex への送付前）。宛先：Codex。
BS-W4 と転送スタブの削除（`201b022cc`）の後に行う。
ユーザーの決定（10-25）：関連する内容のファイルはまとめ、ファイル数をできるだけ減らす。まとめ方は「数学的な内容で関連するもの」。
まず Delta/Basic と Delta/Free 直下（`Free/Finite/` は含めない）。対応は勉強ノート第 2 章 §2.1（`exposition/ja/bs/02-delta.html`）。

## 0. 前提と全体の方針

- 前提は BS-W1 の §0 と同じ（所有範囲、他レーンの並行作業、root ビルドの禁止、`git add -A`・`git commit -a` の禁止）。
- **宣言名・名前空間・型・証明は変えない**（例外は §2 の一行だけ）。変わるのはモジュールの境界と import 行。
- 所有範囲外から Delta/Basic・Delta/Free を import しているファイルはない（2026-10-25 に確認）。転送スタブは置かない。
- 統合後の import に循環がないことは確認済み（§2 の import 削除を含めて）。
- 新しい sorry・axiom を加えない。

## 1. 作業 A：統合（スクリプト）

計画は [bhatt-scholze-codex-w5-merges.json](../../../evidence/bhatt-scholze/bhatt-scholze-codex-w5-merges.json)、スクリプトは
[bhatt-scholze-merge-modules.py](../../../evidence/bhatt-scholze/bhatt-scholze-merge-modules.py)（多対一の統合用。docstring に動作を書いてある）。

| 統合後 | 話題 | 元（この順に連結） | 行数 |
| --- | --- | --- | --- |
| `Delta/Basic/DeltaRing` | δ 環の定義と基本操作 | DeltaRing、WittTwoMap、WittTwoUnits、DeltaIdentities、DeltaSectionNaturality、DeltaFrobenius、DeltaTransport、DeltaSubring | 610 |
| `Delta/Basic/DeltaQuotient` | イデアルと商 | DeltaIdeal、DeltaQuotient、DeltaClosureGeneration | 299 |
| `Delta/Basic/DeltaColimit` | 極限と余極限 | DeltaDirectLimit（改名） | 122 |
| `Delta/Basic/DeltaWitt` | Witt 環との関係 | DeltaWittGhost の 7 本（Step、Coefficients、LowCoefficients、CoefficientTwo、RingHom、Naturality、Frobenius） | 462 |
| `Delta/Free/RelativeFreeDelta` | 多項式環上の δ 構造と相対自由 δ 環 | PolynomialDelta、PolynomialRankOneDelta、RelativeFreeDelta、RelativeFreeUniversal、RelativeFreePresentation、RelativeFreeVariableSplit | 519 |
| `Delta/Free/FreeDeltaRing` | 整数係数の自由 δ 環と「φ は δ 射」 | FreeDeltaRing、FreeDeltaUniversal、FreeDeltaPresentation、RelativeFreeIntegerComparison、Basic/DeltaFrobeniusNaturality | 289 |
| `Delta/Free/FreeDeltaFrobeniusFlat` | 自由 δ 環の Frobenius の平坦性 | FreeDeltaModP、PrimePolynomialFrobeniusFlat、FreeDeltaFrobeniusModPFlat、FreeDeltaFrobeniusCompletelyFlat、FreeDeltaFrobeniusCoordinateResidueFlat、FreeDeltaFrobeniusCoordinateRegular | 593 |
| `Delta/Free/PolynomialExpand` | 多項式の expand 写像の自由性（可換環論） | PolynomialExponentDivMod、PolynomialExpandDecomposition、PolynomialExpandFree | 232 |
| `Delta/Extension/DeltaAdicEstimate` | δ とイデアル冪の評価 | Free/RelativeDeltaEstimate、Extension/DeltaAdicEstimate | 201 |

各元ファイルは統合先で `/-! ## 見出し（旧 パス） … -/` と `section 元ファイル名 … end 元ファイル名` に包まれる
（variable・set_option・open・local notation・local instance が後ろの部分に漏れない）。`private` 宣言・インスタンス名の衝突はない（確認済み）。

```bash
set -o pipefail
git status --short SerrePositivity/BhattScholze SerrePositivity/CLMST   # 空であること
DECLS() { git grep -hoE '^(private )?(noncomputable )?(theorem|lemma|def|abbrev|structure|instance|class) [^ ]+' \
  -- 'SerrePositivity/BhattScholze/Delta/Basic/*.lean' 'SerrePositivity/BhattScholze/Delta/Free/*.lean' \
  SerrePositivity/BhattScholze/Delta/Extension/DeltaAdicEstimate.lean | sort; }
DECLS > /tmp/bs_w5_decls_before.txt
python3 evidence/bhatt-scholze/bhatt-scholze-merge-modules.py evidence/bhatt-scholze/bhatt-scholze-codex-w5-merges.json
# 期待値（2026-10-25 15dd2d86f 以降の main で確認）："removed_files": 36, "owned_files_rewritten": 38, "foreign_importers": []
python3 evidence/bhatt-scholze/bhatt-scholze-merge-modules.py evidence/bhatt-scholze/bhatt-scholze-codex-w5-merges.json --apply
git add SerrePositivity/BhattScholze/Delta/Basic/DeltaColimit.lean SerrePositivity/BhattScholze/Delta/Basic/DeltaWitt.lean \
  SerrePositivity/BhattScholze/Delta/Free/FreeDeltaFrobeniusFlat.lean SerrePositivity/BhattScholze/Delta/Free/PolynomialExpand.lean
```

件数が違う場合は `--apply` せずに報告する。

## 2. 作業 B：層の逆転の解消（手作業、一行と import 一本）

統合後の `Delta/Free/FreeDeltaRing.lean` の `section DeltaFrobeniusNaturality` にある `frobeniusLift_delta` の証明で、

```lean
  have h := congrArg f (F.isDeltaHom_frobeniusLift
    (freeDeltaRing_p_mul_injective p Unit) t)
```

を、`Delta/Perfect` の補題を使わない次の形に替える（`isDeltaHom_frobeniusLift` の中身そのもの）：

```lean
  have h := congrArg f (isDeltaHom_of_map_frobeniusLift (D := F) (E := F) F.frobeniusLift
    (freeDeltaRing_p_mul_injective p Unit) (fun _ ↦ rfl) t)
```

そのうえで同じファイルの `public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDeltaFrobenius` を削除する。
これで `Delta/Free` から `Delta/Perfect` への依存がなくなる。

この削除で、旧 `DeltaFrobeniusNaturality` を経由して `PerfectDeltaFrobenius` を間接的に受け取っていたファイル
（`Delta/Perfect/DeltaPerfection`、`Andre/RootedExtension/DeltaAlgebra/DeltaAlgebraFrobeniusStages` など）が
ビルドに失敗した場合に限り、そのファイルに `public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDeltaFrobenius` を
一行足してよい。足したファイルは報告する。上の一行の置き換えが elaboration で通らない場合は、その行だけ直してよい（直し方を報告する）。

## 3. 禁止事項

- §2 以外の証明・宣言・名前空間・variable の変更。統合後のファイル内での並べ替え・重複の整理（W6 以降で扱う）。
- 上の表以外のファイルの統合（`Free/Finite/` を含む）。所有範囲外のファイルの変更。

## 4. 受入条件

BS-W1 §5「作業 3 の後」と同じコマンド一式（BS・CLMST の全モジュールのビルド、全 BS・CLMST 監査、`audit_f5`・`audit_f7`、
`scripts/audit_andre_*.lean`、構造監査、CommutativeAlgebra の 4 モジュール）を実行し、すべてエラーなし・終了 0。
ログの全体を `grep -nE "^error|error:|sorryAx"` で確かめてから報告する（宣言名に含まれる `error` は除いてよい）。加えて：

```bash
ls SerrePositivity/BhattScholze/Delta/Basic/   # DeltaColimit DeltaQuotient DeltaRing DeltaWitt の 4 本だけ
ls SerrePositivity/BhattScholze/Delta/Free/    # Finite/ と FreeDeltaFrobeniusFlat FreeDeltaRing PolynomialExpand RelativeFreeDelta の 4 本だけ
DECLS > /tmp/bs_w5_decls_after.txt   # §1 で定義した関数
diff /tmp/bs_w5_decls_before.txt /tmp/bs_w5_decls_after.txt && echo "宣言名は同一"
grep -rn "Delta.Perfect" SerrePositivity/BhattScholze/Delta/Free/FreeDeltaRing.lean   # 出力なし
lake env lean scripts/audit/bhatt_scholze.lean 2>&1 | tail -1   # 「… modules checked; 10 depend on sorryAx through the allowed quotations」
```

## 5. コミット

一つのコミットにする（統合・import の書き換え・§2 の修正）。

```bash
set -o pipefail
git commit --only SerrePositivity/BhattScholze SerrePositivity/CLMST SerrePositivity/Inputs/Perfectoidization.lean \
  scripts/audit_bhatt_scholze*.lean scripts/audit_clmst*.lean scripts/audit_andre_*.lean \
  scripts/audit/bhatt_scholze.lean scripts/audit/clmst.lean -m "$(cat <<'EOF'
refactor(bs): merge Delta/Basic and Delta/Free into nine modules by topic

Basic: DeltaRing (definition and basic operations), DeltaQuotient (ideals and quotients),
DeltaColimit (colimits) and DeltaWitt (the map to Witt vectors). Free: RelativeFreeDelta
(polynomial δ-structures and relative free δ-rings), FreeDeltaRing (the integral free δ-ring and
"φ is a δ-map", no longer importing Delta/Perfect), FreeDeltaFrobeniusFlat and PolynomialExpand.
RelativeDeltaEstimate joins Extension/DeltaAdicEstimate. Declarations, names and proofs are
unchanged except one line that inlines a one-line lemma. Plan: formalization-plans/bhatt-scholze-codex-w5-merges.json.

Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>
EOF
)"
```

## 6. 報告してほしいこと

コミットハッシュ、dry-run の出力、§2 で足した import（あれば）と一行の直し方（変えた場合）、ビルドのジョブ数・所要時間・grep の結果、
§4 の追加確認の出力、想定と違ったこと。失敗したときは直さずにエラーをそのまま報告する（§2 で許したものを除く）。
