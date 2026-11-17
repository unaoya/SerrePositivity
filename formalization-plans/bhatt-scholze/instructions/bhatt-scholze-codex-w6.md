# Codex 作業指示書 BS-W6：Free/Finite・Perfect・Extension・Distinguished を数学的な話題ごとにまとめる（57 本 → 11 本）

作成：2026-10-25（BS 作業チャット）。宛先：Codex。**BS-W5 のコミットの後に行う。**
ユーザーの決定（10-25）：関連する内容のファイルは数学的な話題でまとめ、ファイル数をできるだけ減らす。§2.4（完全 δ 環）の内容で
Delta/Perfect の外にある 3 本（André・Prism の下）も Delta/Perfect へ集める。対応は勉強ノート第 2 章（`exposition/ja/bs/02-delta.html`）。

## 0. 前提と全体の方針

- 前提は BS-W1 の §0 と同じ（所有範囲、他レーンの並行作業、root ビルドの禁止、`git add -A`・`git commit -a` の禁止）。
- **宣言名・名前空間・型・証明は一切変えない**。変わるのはモジュールの境界と import 行だけ。
- 所有範囲外の import 元は `scripts/audit_f5.lean`（`Delta.Perfect.DistinguishedPowerTorsion`）だけ。旧名の位置に転送スタブを置く（スクリプトが書く）。
- 統合後の import に循環がないこと、各統合先の中の連結順が依存に沿っていること、`private` 宣言・インスタンス名の衝突がないことは確認済み。
- 新しい sorry・axiom を加えない。

## 1. 作業：統合（スクリプト）

計画は [bhatt-scholze-codex-w6-merges.json](../../../evidence/bhatt-scholze/bhatt-scholze-codex-w6-merges.json)、スクリプトは
[bhatt-scholze-merge-modules.py](../../../evidence/bhatt-scholze/bhatt-scholze-merge-modules.py)（W5 と同じもの。`stubs` の機能を追加済み）。

| 統合後 | 話題 | 元（この順に連結） | 行数 |
| --- | --- | --- | --- |
| `Delta/Perfect/PerfectDelta` | 完全 δ 環の構造（Lemma 2.28・2.32・2.33、Cor 2.31、Ex 2.6） | DeltaTorsion、DeltaRankOne、PerfectDeltaModP、PerfectDeltaFrobenius、WittDelta、PerfectDeltaWittRecovery、WittDistinguished | 563 |
| `Delta/Perfect/DeltaPerfection` | 完全化と、完全 δ 環が余極限・完備化で閉じること（Rem 2.27） | DeltaPerfection、DeltaPerfectionUniversal、**Andre/Transfinite/PerfectDeltaColimit**、**Prism/Perfection/PerfectDeltaPCompletion**、**Prism/Perfection/PerfectDeltaPDCompletion** | 418 |
| `Delta/Perfect/DistinguishedRegular` | distinguished 元の正則性と商の p 冪ねじれ（Lemma 2.34） | DistinguishedRegular、DistinguishedTorsion、DistinguishedPowerTorsion（**スタブを残す**）、DistinguishedQuotientComplete | 349 |
| `Delta/Extension/DeltaLocalization` | 局所化（Lemma 2.15、Rem 2.16） | DeltaLocalization、DeltaLocalizationSaturation | 214 |
| `Delta/Extension/DeltaAdicCompletion` | δ とイデアル冪、古典的 I 進完備化（Lemma 2.17） | DeltaAdicEstimate、DeltaAdicQuotient、DeltaAdicExtension、DeltaAdicCompletion、DeltaAdicLift | 590 |
| `Delta/Extension/DeltaPDCompletion` | 導来 (p,d) 完備化への延長（Lemma 2.18） | WittTwoModuleSequence、WittTwoModuleComplete、DeltaFrobeniusComplete、WittTwoPDComplete、PDCompletionInterface、DeltaPDCompletion、DeltaPDCompletionUniversal | 609 |
| `Delta/Distinguished/Distinguished` | distinguished 元（Ex 2.20(1)、Lemma 2.23〜2.25） | DeltaPrime、Distinguished | 243 |
| `Delta/Free/RelativeFreeFiniteDelta` | 相対自由 δ 環の有限段での δ の計算 | Finite の VariableSplit、DeltaStep、TopVariableSplit、DeltaStepIdentities、DeltaAdicEstimate、DeltaIterate | 587 |
| `Delta/Free/RelativeFreeFiniteResidue` | p を消す環射の下での δ の計算（一般の δ 環と有限段） | Finite の DeltaResidueArithmetic、DeltaAdditionCarryProduct、DeltaResidue、DeltaSubtraction、DeltaPerturbation、DeltaSquareCongruence、DeltaLinearization | 719 |
| `Delta/Free/RelativeFreeFiniteTopVariable` | 最高段の変数についての解析 | Finite の DeltaTopDegree、DeltaTopCoefficient、DeltaTopDerivative | 480 |
| `Delta/Free/RelativeFreeWitt` | Witt 座標（Rem 2.13・2.14 の相対版） | Finite の FrobeniusTopLinear、WittGhostRecurrence、WittGhostSupport、WittGhostTriangular、WittCoordinateChange、WittInverseSupport、FiniteWittCoordinateChange、WittCoefficientNaturality、DeltaWittJetComparison | 849 |

（Finite の各ファイル名は `RelativeFreeFinite…`・`RelativeFree…` の接頭辞を省いた。正確な名前は JSON を見ること。）
`Delta/Free/Finite/` は空になる。

```bash
set -o pipefail
git log --oneline -1 -- formalization-plans/bhatt-scholze/instructions/bhatt-scholze-codex-w5.md   # W5 の後であること
git status --short SerrePositivity/BhattScholze SerrePositivity/CLMST   # 空であること
DECLS() { git grep -hoE '^(private )?(noncomputable )?(theorem|lemma|def|abbrev|structure|instance|class) [^ ]+' \
  -- 'SerrePositivity/BhattScholze/Delta/*.lean' SerrePositivity/BhattScholze/Andre/Transfinite/PerfectDeltaColimit.lean \
  SerrePositivity/BhattScholze/Prism/Perfection/PerfectDeltaPCompletion.lean \
  SerrePositivity/BhattScholze/Prism/Perfection/PerfectDeltaPDCompletion.lean 2>/dev/null | sort; }
DECLS > /tmp/bs_w6_decls_before.txt
python3 evidence/bhatt-scholze/bhatt-scholze-merge-modules.py evidence/bhatt-scholze/bhatt-scholze-codex-w6-merges.json
# 期待値（W5 適用後の作業ツリーで確認）："removed_files": 51, "owned_files_rewritten": 76 前後,
#   "foreign_importers": ["scripts/audit_f5.lean"], "foreign_imports_without_stub": []
python3 evidence/bhatt-scholze/bhatt-scholze-merge-modules.py evidence/bhatt-scholze/bhatt-scholze-codex-w6-merges.json --apply
git add SerrePositivity/BhattScholze/Delta/Perfect/PerfectDelta.lean SerrePositivity/BhattScholze/Delta/Perfect/DistinguishedRegular.lean \
  SerrePositivity/BhattScholze/Delta/Perfect/DistinguishedPowerTorsion.lean \
  SerrePositivity/BhattScholze/Delta/Extension/DeltaPDCompletion.lean SerrePositivity/BhattScholze/Delta/Extension/DeltaAdicCompletion.lean \
  SerrePositivity/BhattScholze/Delta/Extension/DeltaLocalization.lean \
  SerrePositivity/BhattScholze/Delta/Free/RelativeFreeFiniteDelta.lean SerrePositivity/BhattScholze/Delta/Free/RelativeFreeFiniteResidue.lean \
  SerrePositivity/BhattScholze/Delta/Free/RelativeFreeFiniteTopVariable.lean SerrePositivity/BhattScholze/Delta/Free/RelativeFreeWitt.lean
```

`removed_files` が 51 でない、`foreign_imports_without_stub` が空でない、などの違いがあれば `--apply` せずに報告する。
`owned_files_rewritten` は W5 のコミット内容によって数本ずれてよい（数を報告する）。

## 2. 禁止事項

- 宣言・証明・名前空間・variable の変更（どの一行も）。統合後のファイル内での並べ替え・重複の整理。
- 上の表以外のファイルの統合。所有範囲外のファイルの変更（`scripts/audit_f5.lean` を含む。スタブで受ける）。
- 転送スタブ `Delta/Perfect/DistinguishedPowerTorsion` の削除。

統合でビルドが失敗した場合（統合先で名前や記法が衝突した、など）は、直さずにエラーをそのまま報告する。

## 3. 受入条件

BS-W1 §5「作業 3 の後」と同じコマンド一式（BS・CLMST の全モジュールのビルド、全 BS・CLMST 監査、`audit_f5`・`audit_f7`、
`scripts/audit_andre_*.lean`、構造監査、CommutativeAlgebra の 4 モジュール）を実行し、すべてエラーなし・終了 0。
ログの全体を `grep -nE "^error|error:|sorryAx"` で確かめてから報告する（宣言名に含まれる `error` は除いてよい）。加えて：

```bash
ls SerrePositivity/BhattScholze/Delta/Perfect/        # DeltaPerfection DistinguishedPowerTorsion(スタブ) DistinguishedRegular PerfectDelta
ls SerrePositivity/BhattScholze/Delta/Extension/      # DeltaAdicCompletion DeltaLocalization DeltaPDCompletion
ls SerrePositivity/BhattScholze/Delta/Distinguished/  # Distinguished
ls SerrePositivity/BhattScholze/Delta/Free/           # 8 本、Finite/ はない
DECLS > /tmp/bs_w6_decls_after.txt   # §1 で定義した関数
diff /tmp/bs_w6_decls_before.txt /tmp/bs_w6_decls_after.txt && echo "宣言名は同一"
lake env lean scripts/audit_f5.lean 2>&1 | tail -2    # スタブ経由で通ること
lake env lean scripts/audit/bhatt_scholze.lean 2>&1 | tail -1
```

## 4. コミット

一つのコミットにする。

```bash
set -o pipefail
git commit --only SerrePositivity/BhattScholze SerrePositivity/CLMST SerrePositivity/Inputs/Perfectoidization.lean \
  scripts/audit_bhatt_scholze*.lean scripts/audit_clmst*.lean scripts/audit_andre_*.lean \
  scripts/audit/bhatt_scholze.lean scripts/audit/clmst.lean -m "$(cat <<'EOF'
refactor(bs): merge Free/Finite, Perfect, Extension and Distinguished by topic

Perfect (structure, perfection and closure under colimits and completions, Lemma 2.34) now also
holds the perfect-δ-ring facts that lived under Andre/Transfinite and Prism/Perfection;
Extension (localization, adic completion, (p,d)-completion); Distinguished (one module);
Free/Finite becomes four Free modules (finite stages, residues, top variable, Witt
coordinates). 57 modules become 11; Delta/Perfect/DistinguishedPowerTorsion stays as a
forwarding stub for scripts/audit_f5.lean. Declarations, names and proofs are unchanged.
Plan: formalization-plans/bhatt-scholze-codex-w6-merges.json.

Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>
EOF
)"
```

## 5. 報告してほしいこと

コミットハッシュ、dry-run の出力、ビルドのジョブ数・所要時間・grep の結果、§3 の追加確認の出力、想定と違ったこと。
失敗したときは直さずにエラーをそのまま報告する。
