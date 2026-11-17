# Codex 作業指示書 BS-W7：Prism・Semiperfectoid・Perfectoidization・Almost・Interface を数学的な話題ごとにまとめる（181 本 → 34 本）

作成：2026-10-25（BS 作業チャット）、同日改訂（Codex の適用前の指摘：統合先と同じ名前の `Almost.PerfectoidAlmost` が
スタブ一覧に入っていたのを外し、スクリプトにこれを禁じる検査を足した）。宛先：Codex。**BS-W6（`ba0da6a23`）の後に行う。**
ユーザーの決定（10-25）：ファイルは数学的な内容でまとめる。André の下にある §3・§4 の一般論（有界 prism、Lemma 4.8、Lemma 3.9）を
Prism へ移す。Prism の中の §7（Cor 7.3 の構成）を Semiperfectoid へ、完全 δ 環のテンソル積を Delta/Perfect へ移す。
Semiperfectoid・Perfectoidization・Almost・PerfectoidizationInterface も話題ごとにまとめる。André 本体と Semiperfectoid/RootEnvelope は W8。
対応は勉強ノート第 3 章（`exposition/ja/bs/03-prism.html` の BR33）と第 7・8・10 章。

## 0. 前提と全体の方針

- 前提は BS-W1 の §0 と同じ（所有範囲、他レーンの並行作業、root ビルドの禁止、`git add -A`・`git commit -a` の禁止）。
- **宣言名・名前空間・型・証明は一切変えない**。変わるのはモジュールの境界と import 行だけ。
- スクリプトは W6 の失敗を受けて直してある（`22ebf1610` 以降）：本文中のどこにある `universe` も冒頭へ集める。各部分は元の冒頭の
  section 行（`@[expose] public noncomputable section`・`@[expose] public section`・`public section`）に元ファイル名を付けた名前付き section で
  包むので、公開・expose・noncomputable の効果は元のファイルと同じ。import だけの元ファイルは見出しだけになる。
  この形で統合ファイル 3 本（`Almost/PerfectoidAlmost`、`Semiperfectoid/Surjectivity`、`PerfectoidizationInterface/IntegralExistence`）を
  試験コンパイルし、エラーなしを確認した。
- BS・CLMST だけが使う `CommutativeAlgebra` の 4 本（`AbsolutelyIntegrallyClosedPerfectoidQuotient`、`PerfectoidIdeal`、
  `PerfectoidIdealCompatibleRoots`、`PerfectoidIdealCover`）はスクリプトが import 行を書き換える。
- 所有範囲外の import 元は root の `SerrePositivity.lean` と `scripts/audit_f7.lean`。root が旧名で import する 27 本のうち
  `Almost.PerfectoidAlmost` は統合先と同じ名前なのでスタブは要らない。残る **27 本**（root の 26 本と `audit_f7` の 1 本）は旧名の位置に転送スタブを置く
  （スクリプトが書く）。EInfinity は `PerfectoidizationInterface.Interface` を import しているが、統合先が同じ名前なので影響しない。
- 統合後の import に循環がないこと、各統合先の中の連結順が依存に沿っていること、`private` 宣言・インスタンス名の衝突がないことは確認済み。
- 新しい sorry・axiom を加えない。

## 1. 作業：統合（スクリプト）

計画は [bhatt-scholze-codex-w7-merges.json](../../../evidence/bhatt-scholze/bhatt-scholze-codex-w7-merges.json)（話題の説明は各統合先の docstring）、スクリプトは
[bhatt-scholze-merge-modules.py](../../../evidence/bhatt-scholze/bhatt-scholze-merge-modules.py)。

| 統合後 | 本数 | 元（この順に連結） |
| --- | --- | --- |
| `Prism/Basic/OrientedPrism` | 5 | Prism/Basic/OrientedDeltaPair, Prism/Basic/OrientedPrism, Prism/Basic/PerfectOrientedPrism, Prism/Basic/OrientedPrismHom, Prism/Basic/CrystallineOrientedPrism |
| `Prism/Basic/Rigidity` | 5 | Prism/Basic/OrientedPrismRegularRigidity, Prism/Basic/OrientedPrismHomRigidity, Prism/Basic/OrientedPrismIdealTensor, Prism/Basic/OrientedPrismIsoCriterion, Andre/Remark715/BoundedPrismHomRigidity |
| `Prism/Bounded/Completeness` | 4 | Andre/Remark715/RegularPowerQuotientTorsion, Andre/Remark715/BoundedPrismAdicComplete, Andre/Remark715/BoundedPrismPrimeComplete, Andre/Remark715/PerfectPrismPairAdicComplete |
| `Prism/Bounded/Tilt` | 4 | Andre/Remark715/CommonAdicCompatibleRoots, Andre/Remark715/PerfectPrismCompatibleRootsLift, Andre/Remark715/BoundedPrismCompatibleRootsLift, Andre/Remark715/BoundedPrismTiltQuotient |
| `Prism/PerfectPrismHomLift` | 7 | Andre/Remark715/PerfectSourceAdicRigidity, Andre/Remark715/PerfectPrismBoundedTargetRigidity, Andre/Remark715/PerfectSourceDeltaHom, Prism/Perfectoid/WittQuotientHomFaithful, Prism/Perfectoid/WittQuotientHomLift, Prism/Perfectoid/PerfectPrismHomLift, Andre/Remark715/PerfectPrismBoundedTargetLift |
| `Prism/Perfection/PCompletedPerfection` | 6 | Prism/Perfection/PCompletedDeltaPerfection, Prism/Perfection/PCompletedDeltaRegularity, Prism/Perfection/PCompletedDeltaFunctor, Prism/Perfection/PCompletedDeltaRecovery, Prism/Perfection/PCompletedDistinguishedPrism, Prism/Perfection/PCompletedPrismUniversal |
| `Prism/Perfection/PrismPerfection` | 7 | Prism/Perfection/PerfectDeltaPDPrism, Prism/Perfection/PerfectDeltaPDPrismUniversal, Prism/Perfection/PerfectDeltaPDQuotientEquiv, Andre/RootedExtension/DeltaPerfectionPDCompletionUniversal, Andre/RootedExtension/DeltaPDCompletionPerfectionUniversal, Andre/RootedExtension/DeltaPerfectionPDCompletionComparison, Andre/RootedExtension/DeltaPDCompletionPerfectionComparison |
| `Prism/Perfectoid/WittQuotientTilt` | 8 | Prism/Perfectoid/PerfectDeltaQuotientFrobenius, Prism/Perfectoid/WittDistinguishedQuotient, Prism/Perfectoid/WittQuotientModP, Prism/Perfectoid/WittQuotientFrobeniusKernel, Prism/Perfectoid/WittQuotientTiltMap, Prism/Perfectoid/WittQuotientTiltKernel, Prism/Perfectoid/WittQuotientTiltKernelRegular, Prism/Perfectoid/WittQuotientTiltSurjective |
| `Prism/Perfectoid/WittQuotientPerfectoid` | 6 | Prism/Perfectoid/WittQuotientFontaineComparison, Prism/Perfectoid/WittRegularQuotientPerfectoid, Prism/Perfectoid/WittRegularQuotientFontaineKernel, Prism/Perfectoid/WittQuotientFontaineIso, Prism/Perfectoid/WittQuotientTiltEquiv, Prism/Perfectoid/WittCompleteQuotientPerfectoid |
| `Prism/Perfectoid/PerfectPrismPerfectoid` | 8 | Prism/Perfectoid/FontaineNaturality, Prism/Perfectoid/FontaineKernelNaturality, Prism/Perfectoid/PerfectoidDistinguishedKernel, Prism/Perfectoid/PerfectoidRingEquiv, Prism/Perfectoid/PerfectPrismWittPresentation, Prism/Perfectoid/PerfectPrismQuotientPerfectoid, Prism/Perfectoid/PerfectoidTrialPrism, Prism/Perfectoid/WittDistinguishedQuotientPerfectoid |
| `Prism/Residue/PrismaticResidue` | 8 | Prism/Residue/PrismaticCoefficientQuotientComposition, Prism/Residue/PrismaticCoefficientCompletionReduction, Prism/Residue/PrismaticPowerResidueNilpotent, Prism/Residue/PrismaticPowerResidueDerived, Prism/Residue/PrismaticPowerResidueCanonical, Prism/Residue/PrismaticPowerDerivedFlat, Prism/Residue/PrismaticGeneratorPowerModP, Prism/Residue/PrismaticGeneratorPowerModPFaithful |
| `Prism/Residue/PerfectDeltaResidue` | 3 | Prism/Residue/PerfectDeltaPrismaticResidue, Prism/Residue/PerfectDeltaFrobeniusModels, Prism/Residue/PerfectDeltaFrobeniusQuotientSquare |
| `Delta/Perfect/PerfectDeltaTensor` | 5 | Prism/Tensor/PerfectDeltaCompletedTensorDiscrete, Prism/Tensor/PerfectDeltaTensorRegular, Prism/Tensor/PerfectDeltaTensorStructure, Prism/Tensor/PerfectDeltaTensorPCompletion, Prism/Tensor/PerfectDeltaCompletedTensorH0 |
| `Prism/Tensor/PerfectPrismTensor` | 7 | Prism/Tensor/PerfectDeltaIteratedTensorH0, Prism/Tensor/PerfectDeltaIteratedTensorDiscrete, Prism/Tensor/PerfectDeltaCartierTensorComparison, Prism/Tensor/PerfectDeltaCartierTensorAlgebra, Prism/Tensor/PerfectDeltaCartierTensorAlgEquiv, Prism/Tensor/PerfectDeltaPresentedTensorRing, Prism/Tensor/PerfectDeltaResidueTensorTransport |
| `Prism/Tensor/PerfectPrismResidueTensor` | 3 | Prism/Tensor/PerfectPrismResidueFactor, Prism/Tensor/PerfectPrismCartierTensorComparison, Prism/Tensor/PerfectPrismResidueTensorTransport |
| `Semiperfectoid/PerfectPrismDivision` | 5 | Prism/Perfection/PCompletedDeltaDivision, Prism/Perfection/PCompletedDeltaDivisionComparison, Prism/Perfection/PCompletedDeltaDivisionQuotient, Prism/Perfection/PCompletedDeltaDivisionPresentation, Prism/Perfection/PCompletedDeltaDivisionPowerTorsion |
| `Semiperfectoid/PerfectPrismDivisionComparison` | 6 | Prism/Perfection/PCompletedDeltaDivisionRecovery, Prism/Perfection/PCompletedDeltaDivisionRepeat, Prism/Perfection/PCompletedDeltaDivisionSequential, Prism/Perfection/PCompletedDeltaDivisionSequentialEquiv, Prism/Perfection/PCompletedDeltaDivisionTorsion, Prism/Perfection/PCompletedDeltaDivisionTorsionQuotient |
| `Semiperfectoid/CharacteristicP` | 2 | Prism/Perfectoid/CharacteristicPPerfectoid, Prism/Perfectoid/CharacteristicPQuotient |
| `Semiperfectoid/Perfectoidization` | 5 | Prism/Perfection/PerfectDeltaDivisionPrism, Prism/Perfection/PerfectDeltaDivisionQuotient, Prism/Perfectoid/PerfectPrismQuotientPerfectoidization, Semiperfectoid/SemiperfectoidPerfectoidization, Semiperfectoid/QuotientPerfectoidization |
| `Semiperfectoid/Surjectivity` | 12 | Semiperfectoid/TensorResidueBaseChangeComparison, Semiperfectoid/PerfectoidizationSurjectivityDescent, Semiperfectoid/TensorBaseChangeKernel, Semiperfectoid/RootedExtension/RootedIdealSurjectivity, Semiperfectoid/RootedExtension/RootedKernelSurjectivity, Semiperfectoid/RootedExtension/RootedTensorBaseChangeSurjectivity, Semiperfectoid/RootedExtension/RootedPerfectoidSurjectivityDescent, Semiperfectoid/AndreSurjectivity, Semiperfectoid/SemiperfectoidSurjectivity, Semiperfectoid/TorsionFreeQuotientSurjectivity, Semiperfectoid/PerfectoidizationSurjectivity, Semiperfectoid/PerfectoidizationSurjectiveMap |
| `Semiperfectoid/CompatibleRoot` | 11 | Semiperfectoid/RootedExtension/CompatibleRoot/CompatibleRootIdeal, Semiperfectoid/RootedExtension/CompatibleRoot/CompatibleRootIdealFlat, Semiperfectoid/RootedExtension/CompatibleRoot/CompatibleRootIdealTensor, Semiperfectoid/RootedExtension/CompatibleRoot/CompatibleRootQuotientTor, Semiperfectoid/RootedExtension/CompatibleRoot/CompatibleRootPerfectQuotient, Semiperfectoid/RootedExtension/CompatibleRoot/CompatibleRootTilt, Semiperfectoid/RootedExtension/CompatibleRoot/CompatibleRootFamilyIdeal, Semiperfectoid/RootedExtension/CompatibleRoot/CompatibleRootQuotient, Semiperfectoid/RootedExtension/CompatibleRoot/CompatibleRootPerfectoidUniversal, Semiperfectoid/RootedExtension/CompatibleRoot/CompatibleRootCompletionSurjective, Semiperfectoid/RootedExtension/CompatibleRoot/CompatibleRootFamilyQuotient |
| `Semiperfectoid/CompatibleRootPerfectoid` | 6 | Prism/Perfection/PerfectDeltaPDQuotientComparison, Semiperfectoid/RootedExtension/CompatibleRoot/CompatibleRootSingletonComparison, Semiperfectoid/RootedExtension/CompatibleRoot/CompatibleRootPDComparison, Semiperfectoid/RootedExtension/CompatibleRoot/CompatibleRootFamilyPDComparison, Semiperfectoid/RootedExtension/CompatibleRoot/CompatibleRootFamilyCompletionPerfectoid, Semiperfectoid/RootedExtension/CompatibleRoot/CompatibleRootCompletionPerfectoid |
| `Perfectoidization/WittPushout` | 5 | Perfectoidization/PerfectCoefficientTensor, Perfectoidization/WittPresentation/WittCoefficientPushout, Perfectoidization/WittPresentation/PerfectoidWittBasePresentation, Perfectoidization/WittPresentation/PerfectoidWittPushout, Perfectoidization/WittPresentation/PerfectoidWittPushoutModP |
| `Perfectoidization/TensorCompatibility` | 3 | Perfectoidization/PerfectoidizationTensorCompatibility, Perfectoidization/PerfectoidizationCompletedTensorCompatibility, Perfectoidization/Prop813PerfectoidBaseChange |
| `Perfectoidization/Excision` | 3 | Perfectoidization/PerfectoidizationExcisionDiagram, Perfectoidization/PerfectoidizationExcision, Perfectoidization/PerfectoidizationExcisionResults |
| `Almost/Lemma103` | 3 | Almost/Lemma103KernelTensor, Almost/Lemma103PerfectoidTensor, Almost/PerfectoidIdealLemma103 |
| `Almost/PerfectoidAlmost` | 4 | Almost/PerfectoidIdealConormalCompletion, Almost/PerfectoidIdealIdempotent, Almost/PerfectoidAlmostExtension, Almost/PerfectoidAlmost |
| `Almost/SupportedQuotient` | 3 | Almost/PerfectoidizationSupportedQuotientKernel, Almost/PerfectoidizationSupportedQuotientLinear, Almost/PerfectoidizationImageComparison |
| `PerfectoidizationInterface/Interface` | 6 | PerfectoidizationInterface/Setup, PerfectoidizationInterface/Derived, PerfectoidizationInterface/Completion, PerfectoidizationInterface/LimitData, PerfectoidizationInterface/ExcisionDiagram, PerfectoidizationInterface/Interface |
| `PerfectoidizationInterface/IntegralExistence` | 5 | PerfectoidizationInterface/InitialLimit, PerfectoidizationInterface/InitialBridge, PerfectoidizationInterface/IntegralExistence, PerfectoidizationInterface/IntegralPerfectoidization, PerfectoidizationInterface/FiniteIntegralExistence |
| `PerfectoidizationInterface/Excision` | 3 | PerfectoidizationInterface/ExcisionBridge, PerfectoidizationInterface/Excision, PerfectoidizationInterface/ArcExcision |
| `Perfectoidization/TensorPerfectoidization` | 4 | Perfectoidization/WittPresentation/WittPresentedPerfectoidTensor, Perfectoidization/WittPresentation/WittPresentedPerfectoidTensorModP, Perfectoidization/PerfectoidTensorPerfectoidization, Perfectoidization/PerfectoidizationBaseChange |
| `Perfectoidization/CompletedTensor` | 6 | Perfectoidization/WittPresentation/FontaineCompletedTensorDiscrete, Perfectoidization/PerfectoidCompletedTensorDiscrete, Perfectoidization/PerfectoidCompletedQuotientMul, Perfectoidization/CompletedTensorPerfectoidization, Perfectoidization/CompletedTensorPerfectoidUniversal, Perfectoidization/PerfectoidFiniteProduct |
| `Perfectoidization/CompletedBaseChange` | 3 | Perfectoidization/PerfectoidCompletedBaseChangeDiscrete, Perfectoidization/CompletedBaseChangeCoefficientComparison, Perfectoidization/PerfectoidizationCompletedBaseChange |

```bash
set -o pipefail
git log --oneline -1 --grep="merge Free/Finite"   # ba0da6a23 があること
git status --short SerrePositivity/BhattScholze SerrePositivity/CLMST SerrePositivity/CommutativeAlgebra   # 空であること
DECLS() { git grep -hoE '^(private )?(noncomputable )?(theorem|lemma|def|abbrev|structure|instance|class) [^ ]+' \
  -- 'SerrePositivity/BhattScholze/Prism/*.lean' 'SerrePositivity/BhattScholze/Semiperfectoid/*.lean' \
  'SerrePositivity/BhattScholze/Perfectoidization/*.lean' 'SerrePositivity/BhattScholze/Almost/*.lean' \
  'SerrePositivity/BhattScholze/PerfectoidizationInterface/*.lean' 'SerrePositivity/BhattScholze/Delta/Perfect/*.lean' \
  'SerrePositivity/BhattScholze/Andre/Remark715/*.lean' 'SerrePositivity/BhattScholze/Andre/RootedExtension/*.lean' | sort; }
DECLS > /tmp/bs_w7_decls_before.txt
python3 evidence/bhatt-scholze/bhatt-scholze-merge-modules.py evidence/bhatt-scholze/bhatt-scholze-codex-w7-merges.json
# 期待値（ba0da6a23 で確認、3 分ほどかかる）："removed_files": 176, "owned_files_rewritten": 90,
#   "foreign_importers": ["SerrePositivity.lean", "scripts/audit_f7.lean"], "foreign_imports_without_stub": []
python3 evidence/bhatt-scholze/bhatt-scholze-merge-modules.py evidence/bhatt-scholze/bhatt-scholze-codex-w7-merges.json --apply
git add SerrePositivity/BhattScholze   # 新しい統合ファイル 29 本と転送スタブ 27 本を含む（BhattScholze の中だけ）
```

件数が違う、`foreign_imports_without_stub` が空でない、などの場合は `--apply` せずに報告する。

## 2. 禁止事項

- 宣言・証明・名前空間・variable の変更（どの一行も）。統合後のファイル内での並べ替え・重複の整理。
- 上の表以外のファイルの統合（André 本体・`Andre/Remark715` の残り・`Semiperfectoid/RootEnvelope` は W8）。
- 所有範囲外のファイルの変更（`SerrePositivity.lean`、`scripts/audit_f5.lean`・`audit_f7.lean`、EInfinity を含む）。転送スタブの削除。

ビルドが失敗した場合は、直さずにエラーをそのまま報告する。

## 3. 受入条件

BS-W1 §5「作業 3 の後」と同じコマンド一式（BS・CLMST の全モジュールのビルド、全 BS・CLMST 監査、`audit_f5`・`audit_f7`、
`scripts/audit_andre_*.lean`、構造監査、CommutativeAlgebra の 4 モジュール）に加え、`lake build SerrePositivity.EInfinity.Perfectoidization.Comparison`
を実行し、すべてエラーなし・終了 0。ログの全体を `grep -nE "^error|error:|sorryAx"` で確かめてから報告する。加えて：

```bash
for d in Prism Prism/Basic Prism/Bounded Prism/Perfection Prism/Perfectoid Prism/Residue Prism/Tensor Semiperfectoid \
  Perfectoidization Perfectoidization/WittPresentation Almost PerfectoidizationInterface Delta/Perfect; do
  echo "$d $(ls SerrePositivity/BhattScholze/$d/*.lean | wc -l)"; done
# 期待値（スタブを含む）：Prism 1、Basic 2、Bounded 2、Perfection 2、Perfectoid 4（うちスタブ 1）、Residue 2、Tensor 17（スタブ 15）、
#   Semiperfectoid 7、Perfectoidization 13（スタブ 6）、WittPresentation 1（スタブ）、Almost 5（スタブ 2）、Interface 4（スタブ 1）、Delta/Perfect 5
DECLS > /tmp/bs_w7_decls_after.txt   # §1 で定義した関数
diff /tmp/bs_w7_decls_before.txt /tmp/bs_w7_decls_after.txt && echo "宣言名は同一"
lake env lean scripts/audit/bhatt_scholze.lean 2>&1 | tail -1
```

## 4. コミット

一つのコミットにする。

```bash
set -o pipefail
git commit --only SerrePositivity/BhattScholze SerrePositivity/CLMST SerrePositivity/Inputs/Perfectoidization.lean \
  SerrePositivity/CommutativeAlgebra/AbsolutelyIntegrallyClosedPerfectoidQuotient.lean SerrePositivity/CommutativeAlgebra/PerfectoidIdeal.lean \
  SerrePositivity/CommutativeAlgebra/PerfectoidIdealCompatibleRoots.lean SerrePositivity/CommutativeAlgebra/PerfectoidIdealCover.lean \
  scripts/audit_bhatt_scholze*.lean scripts/audit_clmst*.lean scripts/audit_andre_*.lean \
  scripts/audit/bhatt_scholze.lean scripts/audit/clmst.lean -m "$(cat <<'EOF'
refactor(bs): merge Prism, Semiperfectoid, Perfectoidization, Almost and the interface by topic

Prism now holds the general §3/§4 material that lived under Andre (bounded prisms, Lemma 4.8,
Lemma 3.9) and is organized by topic; the Cor 7.3 constructions move to Semiperfectoid and the
tensor products of perfect δ-rings to Delta/Perfect. Semiperfectoid, Perfectoidization, Almost
and PerfectoidizationInterface are merged by topic. 181 modules become 34; 27 old names that
the root aggregator and scripts/audit_f7.lean import stay as forwarding stubs. Declarations,
names and proofs are unchanged. Plan: formalization-plans/bhatt-scholze-codex-w7-merges.json.

Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>
EOF
)"
```

## 5. 報告してほしいこと

コミットハッシュ、dry-run の出力、ビルドのジョブ数・所要時間・grep の結果、§3 の追加確認の出力、想定と違ったこと。
失敗したときは直さずにエラーをそのまま報告する。
