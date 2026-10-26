# Codex 作業指示書 BS-W9：Delta/DividedPower と Delta/Division を数学的な話題ごとにまとめる（133 本 → 11 本）

作成：2026-10-26（BS 作業チャット）。宛先：Codex。**BS-W8（`19655cbd1`）と、`MonicRelationRegularSequence` の移動に伴う import の修正（`ebf510bcc`）の後に行う。**
ユーザーの決定（10-26）：`Delta/` のうちまだ一本ずつ残っている `DividedPower`（§2.5、74 本）と `Division`（d で割る δ 包、59 本）を、
W5〜W8 と同じく数学的な内容でまとめる。`DividedPower` はノート §2.5 の五つのまとまり（Lemma 2.35・2.36 の係数、Lemma 2.36、
生の A{a/p} と完備化、Lemma 2.38 の r = 1、一変数の分冪多項式代数）に沿う。

## 0. 前提と全体の方針

- 前提は BS-W1 の §0 と同じ（所有範囲、他レーンの並行作業、root ビルドの禁止、`git add -A`・`git commit -a` の禁止）。
- **宣言名・名前空間・型・証明は一切変えない**。変わるのはモジュールの境界と import 行だけ。
- スクリプトは W8 で直したもの（`e13b67fd9` 以降）。所有範囲外の import 元はない（使っているのは André と Semiperfectoid だけ）ので、スタブは作らない。
- 統合後の import に循環がないこと、`private` 宣言の名前の重なりがないことは確認済み。
- BS 作業チャットが使い捨て worktree で適用し、§3 の受入確認を全部通すことを確認する（結果は §5 の下に書く）。

## 1. 作業：統合（スクリプト）

計画は [bhatt-scholze-codex-w9-merges.json](bhatt-scholze-codex-w9-merges.json)（話題の説明は各統合先の docstring）、スクリプトは
[bhatt-scholze-merge-modules.py](bhatt-scholze-merge-modules.py)。

| 統合後 | 本数 | 元（この順に連結） |
| --- | --- | --- |
| `Delta/DividedPower/Factorial` | 7 | DeltaDividedPowerCoefficients, DeltaDividedPowerExpansion, DeltaDividedPowerStep, DeltaFactorialDivision, DeltaDividedPowerIdeal, DeltaDividedPowers, DeltaDividedPowerCoefficientImage |
| `Delta/DividedPower/PDivision` | 18 | DeltaPDivisionFirstRelationRegular, DeltaPDivisionLocalization, DeltaPDivisionFactorial, DeltaPDivisionRawMinimal, DeltaPDivisionFactorialSubring, DeltaPDivisionFactorialDelta, DeltaPDivisionFactorialStable, DeltaPDivisionFactorialStructure, DeltaPDivisionFactorialIdeal, DeltaPDivisionWittResidueSolution, DeltaPDivisionWittResidueEvaluation, DeltaPDivisionFactorialMap, DeltaPDivisionFactorialFunctorial, DeltaPDivisionFactorialDPMorphism, DeltaPDivisionFactorialDeltaMap, DeltaPDivisionFactorialPDTarget, DeltaPDivisionFactorialPDLift, DeltaPDivisionFactorialPDUniversal |
| `Delta/DividedPower/PrincipalDP` | 19 | PrincipalDPPresentation, PrincipalDPRegular, PrincipalDPToFactorial, PrincipalDPFactorialKernel, PrincipalDPFactorialEquiv, PrincipalDPRelativeModPKoszul, PrincipalDPBaseChangeRelations, PrincipalDPBaseChangeUniversal, PrincipalDPRelativeDerivedModP, PrincipalDPRelativeCompletionModP, PrincipalDPEvaluationTensor, PrincipalDPQuotientFlat, RegularPrincipalDPUniversal, PrincipalDPModP, RegularPrincipalDPModP, PrincipalDPBaseChange, PrincipalDPCompletionModP, RegularPrincipalDPBaseChange, RegularPrincipalDPModPFlat |
| `Delta/DividedPower/RankOneDP` | 25 | RankOneDPBaseChangeMap, RankOneDPTensorRelations, RankOneDPBaseChangeUniversal, RankOneDPBasis, RankOneDPAnyBasis, RankOneDPPrimeBasis, RankOneDPPrimeBlocks, RankOneDPPrimeBlockBasis, RankOneDPTruncatedAction, RankOneDPTruncatedFree, RankOneDPPolynomialAction, RankOneDPEnvelopeBaseChange, RankOneDPTruncationQuotient, RankOneDPEnvelopeFree, RankOneDPQuotientToEnvelope, RankOneDPEnvelopeCoefficientFlat, RankOneDPEvaluatedEnvelope, RankOneDPBaseChange, RankOneDPTruncationDerived, RankOneDPDerivedFactorization, RankOneDPDerivedKoszul, RankOneDPTruncatedTensorFlat, RankOneDPDerivedRelativeFlat, RankOneDPEvaluatedDerivedFlat, RankOneDPCharacteristicCompletion |
| `Delta/Division/Basic` | 7 | DeltaAdjoinDivision, DeltaTorsionReduction, DeltaDivisionUniversal, DeltaPTorsionReduction, DeltaDivisionClassicalCompletion, DeltaDivisionPDCompletion, DeltaDivisionQuotient |
| `Delta/DividedPower/PDivisionCompletion` | 5 | DeltaPDivisionFrobeniusShift, DeltaPDivisionDerivedUnit, DeltaPDivisionFrobeniusShiftTorsion, DeltaPDivisionFrobeniusShiftDerived, DeltaPDivisionUnit |
| `Delta/Division/Family` | 7 | DeltaAdjoinDivisionSum, DeltaAdjoinDivisionReindex, DeltaAdjoinDivisionEmpty, DeltaAdjoinDivisionReindexFunctorial, DeltaAdjoinDivisionFiniteSystem, DeltaAdjoinDivisionFiniteColimit, DeltaAdjoinDivisionFiniteColimitEquiv |
| `Delta/Division/Relations` | 7 | Relations/DeltaDivisionIteratedRelations, Relations/DeltaDivisionFiniteRelationPolynomial, Relations/DeltaDivisionFiniteLeadingLinear, Relations/DeltaDivisionFiniteTopDerivative, Relations/DeltaDivisionFiniteTopCoefficient, Relations/DeltaDivisionFiniteGeneratorResidue, Relations/DeltaDivisionFiniteGeneratorConstant |
| `Delta/Division/Residue` | 10 | Relations/DeltaDivisionFiniteResidueRelation, Relations/DeltaDivisionResidueRelation, Relations/DeltaDivisionSecondResidueRelation, Relations/DeltaDivisionSecondFiniteResidueRelation, Relations/DeltaDivisionSecondFinitePresentation, Relations/DeltaDivisionFirstResiduePresentation, Relations/DeltaDivisionFirstResiduePowerPresentation, Relations/DeltaDivisionFirstOrderNormalForm, Relations/DeltaDivisionSecondMonicPresentation, Relations/DeltaDivisionSecondPowerPresentation |
| `Delta/Division/Source` | 14 | Relations/DeltaDivisionFiniteEvaluationRelations, Relations/DeltaDivisionEvaluationSource, Relations/DeltaDivisionSourceAlgebras, Relations/DeltaDivisionSourceTensor, Relations/DeltaDivisionUnitDenominator, Relations/DeltaAdjoinDivisionFamilyRegular, Relations/DeltaDivisionEvaluationFamilyStep, Relations/RelativeFreeSubsetSplit, Relations/DeltaDivisionSourceCoefficientTor, Relations/DeltaDivisionSourceCoefficientReduction, Relations/DeltaDivisionSourceCoefficientMaps, Relations/DeltaDivisionSourceCoefficientQuotients, Relations/DeltaDivisionSourceCoefficientRightFactor, Relations/DeltaDivisionSourceTensorDelta |
| `Delta/Division/Witt` | 14 | Relations/DeltaDivisionWittJetRelations, Relations/WittDivisionTriangular, Relations/DeltaDivisionWittMonicRelations, Relations/WittDivisionPolynomialRemainder, Relations/DeltaDivisionWittPolynomialRelations, Relations/DeltaDivisionWittRelationElement, Relations/DeltaDivisionWittRelationIdeal, Relations/DeltaDivisionWittFiniteRelationIdeal, Relations/DeltaDivisionWittNormalizedRelation, Relations/DeltaDivisionWittNormalizedIdeal, Relations/DeltaDivisionWittNormalizedQuotient, Relations/DeltaDivisionFiniteNormalizedPresentation, Relations/DeltaDivisionFiniteNormalizedStep, Relations/DeltaDivisionWittJetRegularity |

```bash
set -o pipefail
git log --oneline -1 ebf510bcc   # MonicCandidate の import 修正があること（BS-W8 の後）
git status --short SerrePositivity/BhattScholze SerrePositivity/BhattScholze.lean SerrePositivity/CLMST scripts/audit_bhatt* scripts/audit_clmst* scripts/audit_andre_* scripts/audit/   # 空であること
DECLS() { git grep -hoE '^(private )?(noncomputable )?(theorem|lemma|def|abbrev|structure|instance|class) [^ ]+' \
  -- 'SerrePositivity/BhattScholze/Delta/*.lean' | sort; }
DECLS > /tmp/bs_w9_decls_before.txt
python3 formalization-plans/bhatt-scholze-merge-modules.py formalization-plans/bhatt-scholze-codex-w9-merges.json
# 期待値："removed_files": 133, "owned_files_rewritten": 27, "foreign_importers": [], "foreign_imports_without_stub": []、新しいモジュール 11 本（589〜1918 行）
python3 formalization-plans/bhatt-scholze-merge-modules.py formalization-plans/bhatt-scholze-codex-w9-merges.json --apply
find SerrePositivity/BhattScholze -type d -empty -print -delete
python3 formalization-plans/bhatt-scholze-dedupe-audit-modules.py scripts/audit_andre_*.lean SerrePositivity/BhattScholze/Andre/PowerRootEnvelope/Audit/*.lean
# 期待値：すべて unchanged（W9 では監査の対象モジュール配列に重なりは生じない）
```

件数が違う場合は `--apply` せずに報告する。

## 2. 禁止事項

宣言・証明の変更、上の表にないファイルの統合・移動・削除、所有範囲外のファイルの変更、転送スタブの作成。
失敗した場合は、直さずにエラーをそのまま報告する。

## 3. 受入条件

BS-W1 §5「作業 3 の後」と同じコマンド一式（BS・CLMST の全モジュールのビルド、全 BS・CLMST 監査、`audit_f5`・`audit_f7`、
`scripts/audit_andre_*.lean`、構造監査、CommutativeAlgebra の 4 モジュール）に加え、次を実行し、すべてエラーなし・終了 0。
ログの全体を `grep -nE "^error|error:|sorryAx"` で確かめてから報告する（sorryAx の表示は作業前と同じであること）。
構造監査の未解決の import が BS・CLMST の外（他レーンの作業中のファイル）だけから出る場合は、その一覧を報告に書いて通ったものとする。

```bash
lake build SerrePositivity.BhattScholze SerrePositivity.EInfinity.Perfectoidization.Comparison 2>&1 | tail -2
for d in Delta/DividedPower Delta/Division; do echo "$d $(ls SerrePositivity/BhattScholze/$d/*.lean | wc -l)"; done   # 5 と 6
ls -d SerrePositivity/BhattScholze/Delta/Division/Relations 2>&1 | head -1   # 存在しないこと
DECLS > /tmp/bs_w9_decls_after.txt
diff /tmp/bs_w9_decls_before.txt /tmp/bs_w9_decls_after.txt && echo "宣言名は同一"
```

## 4. コミット

一つのコミットにする。

```bash
set -o pipefail
git commit --only SerrePositivity/BhattScholze SerrePositivity/BhattScholze.lean SerrePositivity/CLMST \
  scripts/audit_bhatt_scholze*.lean scripts/audit_clmst*.lean scripts/audit_andre_*.lean scripts/audit/bhatt_scholze.lean scripts/audit/clmst.lean \
  -m "$(cat <<'MSG'
refactor(bs): merge Delta/DividedPower and Delta/Division by topic

DividedPower follows the five groups of §2.5 (factorial denominators, Lemma 2.36, the raw
A{a/p} and its completion, Lemma 2.38 for r = 1, the rank-one divided power algebra);
Division is split into the raw envelope, families, the iterated relations, their residues,
the evaluation source and the Witt normalization. 133 modules become 11. Declarations,
names and proofs are unchanged. Plan: formalization-plans/bhatt-scholze-codex-w9-merges.json.

Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>
MSG
)"
```

## 5. 報告してほしいこと

コミットハッシュ、dry-run の出力、ビルドのジョブ数・所要時間・grep の結果、§3 の追加確認の出力、想定と違ったこと。
失敗したときは直さずにエラーをそのまま報告する。

## BS 作業チャットの事前試験

使い捨て worktree（`f7d3f64a4` に `ebf510bcc` と同じ import の修正を当てた状態。`.lake` は APFS のクローン複製で、消える 133 本の
olean などの古いビルド成果物 798 ファイルは先に消した）で §1 を適用し、§3 を全部実行した（10-26）：

- BS・CLMST の全モジュールのビルド：成功（5649 ジョブ、約 10 分）。集約・EInfinity・CommutativeAlgebra の 4 本：成功（11776 ジョブ）。
- `scripts/audit_bhatt_scholze*.lean`（7 本）、`audit_clmst*.lean`（2 本）、`audit_andre_*.lean`（2 本）、`scripts/audit/{bhatt_scholze,clmst}.lean`、
  `audit_f5`・`audit_f7`：すべて終了 0、エラー 0。構造監査：終了 0。
- 重複除去スクリプト：6 本すべて unchanged。宣言の前後比較（`Delta/` の 1309 宣言）：同一。
