# CompletedTensor の分割仕様（W9-III-08 の実施、2a 後）

作成：2026-11-03（BS 作業チャット）。宛先：2a の担当（調整役）または 2a 後の BS-W10 の Codex。
目的：E3（`BhattScholze.Inputs.exists_perfectoidizationInterfaceE3`）を消す組み立て（a9-design §7）の前提として、
`SerrePositivity/BhattScholze/Perfectoidization/CompletedTensor.lean` から E3 への依存を外す。**数学的な変更はなく、モジュールの分割と一つの定理の証明の差し替え**。
基準：main `1ed122760` の本体（DG-W3 後も同ファイルは不変）。

## 0. 2a 後の現状（2026-11-04、main 590c4eff7 の取り込み後に再確認。§1 は 2a 前の記録）

- `CompletedTensor.lean` は同じ場所（`BhattScholze/Perfectoidization/`）・同じ 610 行・同じ 6 節。E3 依存は最後の節だけで、`Derived.IntegralExistence` の import（12 行）も残る。
  `IsIntegralPerfectoid`・`IsPerfectoidization` は 2a で `CommutativeAlgebra/Perfectoid/Defs.lean` に移った（旧 `CommutativeAlgebra/IntegralPerfectoid` は削除）。
- **CompletedTensor を直接 import するもの**（7 本）：ルート `BhattScholze.lean`、`Almost/Lemma103`、`PerfectoidIdeal/CompletedQuotient`、
  `Perfectoidization/{CompletedBaseChange, CompletedTensorComparison, ExcisionTor, TensorCompatibility}`。
- **有限直積の節を使うもの**（3 本）：`isIntegralPerfectoid_finPi` は `Perfectoidization/ExcisionTor`・`Perfectoidization/FiniteComparisonExcision`・
  `CLMST/PerfectoidizationIsogeny/ConstantRank`、`finiteProduct_perfectoidization_exists_algEquiv` は `ExcisionTor` だけ。§1 の CLMST 5 本は 2a の統合で消え、CLMST は 1 本になった。
- 置き場所の推奨：芯は `BhattScholze/Perfectoidization/CompletedTensor.lean` に残し（名前を変えない。importer の付け替えが不要になる）、
  有限直積の節を新モジュール `BhattScholze/Perfectoid/FiniteProduct.lean` に切り出して直接証明に差し替える（drafts/A6/PerfectoidFiniteProduct の置き場所の予定どおり）。
  これで付け替えが要るのは有限直積を使う 3 本だけ（CLMST は import 行 1 行）。

## 1. 現状（確認済み、2a 前）

- `CompletedTensor.lean`（610 行、6 節）。E3 に依存するのは最後の節 `PerfectoidFiniteProduct`（554〜610 行）だけ：
  - `isIntegralPerfectoid_finPi`（567 行）：`Inputs.exists_perfectoidization_of_integral R (Fin r → R) p hR` を使う。
  - `finiteProduct_perfectoidization_exists_algEquiv`（594 行）：上の定理と `isPerfectoidization_id.exists_equiv` から。
- import 行 `public import SerrePositivity.BhattScholze.Perfectoidization.Derived.IntegralExistence`（12 行）はこの節のためだけ。
  **他の 10 本の import は Inputs に到達しない**（import 行を再帰的に辿って確認：PerfectPrismTensor、WittPushout、PerfectPrismPerfectoid、MappedPrincipalQuotient、
  CompletedTensorZero、PerfectoidDerivedComplete、CompletedSurjectiveAlgebraMul、CompletedQuotientTensorExtension、TensorPerfectoidization、PerfectoidizationIdentity）。
- 前半 5 節（Fontaine 表示による完備テンソルの芯）：`FontaineCompletedTensorDiscrete`（`fontaine_completedTensor_pure_and_h0`・`_pure`）、
  `PerfectoidCompletedTensorDiscrete`（`integralPerfectoid_completedTensor_pure_and_h0`・`_pure`・`integralPerfectoid_completedTensorH0_isIntegralPerfectoid`）、
  `PerfectoidCompletedQuotientMul`（`integralPerfectoid_completedSurjectiveAlgebraMul_isIso` ほか 4）、`CompletedTensorPerfectoidization`（`completedTensorPerfectoidizationMap` ほか 6）、
  `CompletedTensorPerfectoidUniversal`（`existsUnique_completedTensorPerfectoidLift` ほか 5）。これらは E3 を使わない。
- 利用側（import 行の付け替えが要る）：
  - BS：`Perfectoidization/CompletedBaseChange.lean`、`Perfectoidization/TensorCompatibility.lean`、`Almost/Lemma103.lean`、ルート `SerrePositivity/BhattScholze.lean`。いずれも前半の芯だけを使う。
  - CLMST：`PerfectoidIdealCompletedMul.lean`、`Prop247TensorUnit.lean`（芯）、`PerfectoidFiniteProductTor.lean`（`isIntegralPerfectoid_finPi`・`finiteProduct_perfectoidization_exists_algEquiv`）、
    `KLAicTorFromExcision.lean`・`Prop247ConstantRankExcision.lean`（`isIntegralPerfectoid_finPi`）。

## 2. 分割

1. **芯**：前半 5 節を E3 非依存のモジュールへ。名前は 2a の Perfectoidization* の統合先に合わせる（仮称 `Perfectoidization/CompletedTensorCore`、または統合後の
   `Perfectoid/CompletedTensor`）。import から `Derived.IntegralExistence` を外す。宣言名・証明は不変。
2. **有限直積**：`isIntegralPerfectoid_finPi` を**E3 を使わない直接証明**に差し替える（§3）。`finiteProduct_perfectoidization_exists_algEquiv` は証明不変（`finPi` と
   `isPerfectoidization_id` から）。置き場所は芯の末尾でも別モジュール `Perfectoid/FiniteProduct` でもよい。**E3 を使う旧証明は削除**（E3 後に隔離する案 (b) は採らない。
   W9-III-08 の決定 (a)、design-status §5）。
3. **利用側**：上の 9 本の import 行を付け替える（機械的。`scripts/move_module.py` の対応表に載せれば drafts の import コメントも追従する）。
4. **受入条件**：(i) 分割後、drafts/ の起点（A6/ArcSite・A6/ArcSheafProperty・A8/AlmostConnectivity）と本体の import 行を再帰的に辿って
   `Inputs/PerfectoidizationInterface` に到達しない（下の python 片）。(ii) 変更したモジュールと直接の importer（BS・CLMST の数十本）の小さな `lake build` が通る
   （coordination.md §2 の 4a：下流ビルド・verify が走っていない時間帯）。(iii) 監査（`scripts/audit/bhatt_scholze.lean`・`clmst.lean`）は分割で宣言が変わらないので再生成だけ。

```python
# 到達性の確認（Lean を動かさない）。root で実行。
import re, pathlib
root = pathlib.Path('.')
def imports(mod):
    p = root / (mod.replace('.', '/') + '.lean')
    return re.findall(r'^(?:public )?import (\S+)', p.read_text(), re.M) if p.exists() else []
target = 'SerrePositivity.BhattScholze.Inputs.PerfectoidizationInterface'
def reaches(start, seen=None):
    seen = seen or set(); stack = [start]
    while stack:
        m = stack.pop()
        for i in imports(m):
            if i == target: return True
            if i.startswith('SerrePositivity') and i not in seen: seen.add(i); stack.append(i)
    return False
starts = set()
for f in pathlib.Path('formalization-plans/bhatt-scholze/drafts').rglob('*.lean'):
    starts |= set(re.findall(r'^public import (SerrePositivity\S+)', f.read_text(), re.M))
print([s for s in sorted(starts) if reaches(s)])   # 期待：[]
```

## 3. 有限直積の直接証明（G-A6-12）

主張：R が perfectoid（`IsIntegralPerfectoid R p`）なら `Fin r → R` も perfectoid（r = 0 を含む）。
- r = 0：零環。`IsIntegralPerfectoid` は `Subsingleton S ∨ …` なので左の選択肢。
- r ≥ 1：環同型 `(Fin (r+1) → R) ≃+* R × (Fin r → R)` と `isIntegralPerfectoid_of_ringEquiv`（`Prism/Perfectoid/PerfectPrismPerfectoid.lean:166`）で
  **二つの perfectoid 環の直積 R × S が perfectoid** に帰着し、r の帰納。
- R × S（R・S とも非零。どちらかが零環なら他方と同型）：
  - p は単元でない（成分ごと）。p 進完備：`IsAdicComplete (span {p}) (R × S)` は成分ごと（Mathlib に `Pi`／`Prod` 版が見当たらないので、`IsHausdorff`・`IsPrecomplete` を
    成分ごとに示す小補題を書く）。
  - ϖ = (ϖ_R, ϖ_S)、単元 a = (a_R, a_S) で p = a ϖ^p。
  - mod p の Frobenius の全射性：(R × S)/p ≅ R/p × S/p（`Ideal.quotientInfEquivQuotientProd` 系か直接）で成分ごと。
  - **Fontaine 核の単項性**：PreTilt(R × S) ≅ PreTilt R × PreTilt S（perfection = Frobenius に沿う逆極限は有限積と可換）、
    W(A × B) ≅ W(A) × W(B)（`WittVector.map` の射影の対と、係数ごとの単射・全射。Mathlib に直積の同型はないので係数で書く）。
    この同型の下で θ_{R×S} = θ_R × θ_S（`fontaineTheta` の定義は ghost 成分と Teichmüller で成分ごと）、よって
    ker θ_{R×S} = ker θ_R × ker θ_S = (ξ_R, ξ_S) の生成する単項イデアル（直積環では I × J = ((x, y)) if I = (x)、J = (y)）。
  - 注意：`isIntegralPerfectoid_of_compatible_p_roots`（`CommutativeAlgebra/Perfectoid/Fontaine.lean:1133`）は p 正則（p 非零因子）を仮定するので、
    一般の perfectoid R（p ねじれあり得る）には使えない。p ねじれなしの場合の近道としてのみ可。
- 必要な新しい小補題（Mathlib に見当たらない）：`IsAdicComplete` の直積、`PreTilt`／`Perfection` の直積、`WittVector` の直積の環同型と θ との両立。いずれも係数・成分ごとの
  計算で、E3・BS の結果は不要。

## 4. 時期と担当

- BhattScholze/ の Lean は 2a の取り込みまで凍結（11-02 の取り決め）。2a は Perfectoidization* 12 本を Perfectoid/ へ統合するので、**この分割は 2a に含めるのが最も安い**
  （同じファイル群を一度だけ動かす）。含められない場合は 2a 直後の最初の BS-W10 作業 A（`bhatt-scholze-codex-w10.md`）。
- 完了の報告は design-status §3.1 の依頼行に記録し、a9-design §7 の受入条件を満たしたことを到達性の出力（空リスト）で示す。
