# BS の転送スタブ 32 本を消すための import の書き換え（進捗確認チャットへの依頼）

作成：2026-10-25（BS 作業チャット、BS-W4 `05bbd64d6` の後）。

BS のモジュールを原典の節ごとに移した（BS-W1〜W4）際、所有範囲外のファイルが旧名で import しているモジュールには
旧名の位置に転送スタブ（新しい場所を `public import` するだけのファイル）を置いた。残りは 32 本で、旧名を import しているのは
root の `SerrePositivity.lean`（30 行）と `scripts/audit_f5.lean`・`scripts/audit_f7.lean`（各 1 行）だけである。
この 32 行を新しい名前に替えれば、BS 側でスタブ 32 本を削除できる。

## 書き換え（旧名 → 新しい名前）

`SerrePositivity.BhattScholze.` を `BS.` と略す。書き換えは import 行のモジュール名だけで、`public import` などの修飾子は保つ。

| 旧名 | 新しい名前 | import 元 |
| --- | --- | --- |
| `BS.Andre.MonicRootedExtension` | `BS.Andre.Variants.MonicRootedExtension` | `SerrePositivity.lean` |
| `BS.Andre.Unoriented` | `BS.Andre.Remark715.Unoriented` | `SerrePositivity.lean` |
| `BS.CompletedBaseChangeCoefficientComparison` | `BS.Perfectoidization.CompletedBaseChangeCoefficientComparison` | `SerrePositivity.lean` |
| `BS.CompletedTensorPerfectoidization` | `BS.Perfectoidization.CompletedTensorPerfectoidization` | `SerrePositivity.lean` |
| `BS.FontaineCompletedTensorDiscrete` | `BS.Perfectoidization.WittPresentation.FontaineCompletedTensorDiscrete` | `SerrePositivity.lean` |
| `BS.Inputs.AndreFlatness` | `BS.Andre.AndreFlatness` | `SerrePositivity.lean` |
| `BS.PerfectDeltaCartierTensorAlgEquiv` | `BS.Prism.Tensor.PerfectDeltaCartierTensorAlgEquiv` | `SerrePositivity.lean` |
| `BS.PerfectDeltaCartierTensorAlgebra` | `BS.Prism.Tensor.PerfectDeltaCartierTensorAlgebra` | `SerrePositivity.lean` |
| `BS.PerfectDeltaCartierTensorComparison` | `BS.Prism.Tensor.PerfectDeltaCartierTensorComparison` | `SerrePositivity.lean` |
| `BS.PerfectDeltaCompletedTensorDiscrete` | `BS.Prism.Tensor.PerfectDeltaCompletedTensorDiscrete` | `SerrePositivity.lean` |
| `BS.PerfectDeltaCompletedTensorH0` | `BS.Prism.Tensor.PerfectDeltaCompletedTensorH0` | `SerrePositivity.lean` |
| `BS.PerfectDeltaIteratedTensorDiscrete` | `BS.Prism.Tensor.PerfectDeltaIteratedTensorDiscrete` | `SerrePositivity.lean` |
| `BS.PerfectDeltaIteratedTensorH0` | `BS.Prism.Tensor.PerfectDeltaIteratedTensorH0` | `SerrePositivity.lean` |
| `BS.PerfectDeltaPresentedTensorRing` | `BS.Prism.Tensor.PerfectDeltaPresentedTensorRing` | `SerrePositivity.lean` |
| `BS.PerfectDeltaResidueTensorTransport` | `BS.Prism.Tensor.PerfectDeltaResidueTensorTransport` | `SerrePositivity.lean` |
| `BS.PerfectDeltaTensorPCompletion` | `BS.Prism.Tensor.PerfectDeltaTensorPCompletion` | `SerrePositivity.lean` |
| `BS.PerfectDeltaTensorRegular` | `BS.Prism.Tensor.PerfectDeltaTensorRegular` | `SerrePositivity.lean` |
| `BS.PerfectDeltaTensorStructure` | `BS.Prism.Tensor.PerfectDeltaTensorStructure` | `SerrePositivity.lean` |
| `BS.PerfectPrismCartierTensorComparison` | `BS.Prism.Tensor.PerfectPrismCartierTensorComparison` | `SerrePositivity.lean` |
| `BS.PerfectPrismResidueFactor` | `BS.Prism.Tensor.PerfectPrismResidueFactor` | `SerrePositivity.lean` |
| `BS.PerfectPrismResidueTensorTransport` | `BS.Prism.Tensor.PerfectPrismResidueTensorTransport` | `SerrePositivity.lean` |
| `BS.PerfectoidAlmost` | `BS.Almost.PerfectoidAlmost` | `SerrePositivity.lean` |
| `BS.PerfectoidCompletedBaseChangeDiscrete` | `BS.Perfectoidization.PerfectoidCompletedBaseChangeDiscrete` | `SerrePositivity.lean` |
| `BS.PerfectoidCompletedQuotientMul` | `BS.Perfectoidization.PerfectoidCompletedQuotientMul` | `SerrePositivity.lean` |
| `BS.PerfectoidCompletedTensorDiscrete` | `BS.Perfectoidization.PerfectoidCompletedTensorDiscrete` | `SerrePositivity.lean` |
| `BS.PerfectoidizationCompletedBaseChange` | `BS.Perfectoidization.PerfectoidizationCompletedBaseChange` | `SerrePositivity.lean` |
| `BS.PerfectoidizationExcisionResults` | `BS.Perfectoidization.PerfectoidizationExcisionResults` | `SerrePositivity.lean` |
| `BS.PerfectoidizationSupportedQuotientKernel` | `BS.Almost.PerfectoidizationSupportedQuotientKernel` | `SerrePositivity.lean` |
| `BS.PerfectoidizationSupportedQuotientLinear` | `BS.Almost.PerfectoidizationSupportedQuotientLinear` | `SerrePositivity.lean` |
| `BS.Perfectoidization` | `BS.PerfectoidizationInterface.FiniteIntegralExistence` | `SerrePositivity.lean` |
| `BS.DistinguishedPowerTorsion` | `BS.Delta.Perfect.DistinguishedPowerTorsion` | `scripts/audit_f5.lean` |
| `BS.WittQuotientFontaineIso` | `BS.Prism.Perfectoid.WittQuotientFontaineIso` | `scripts/audit_f7.lean` |

## 一括で書き換える場合

```bash
python3 - <<'PY'
import re, pathlib
B = "SerrePositivity.BhattScholze."
stubs = [p for p in pathlib.Path("SerrePositivity/BhattScholze").glob("**/*.lean")
         if "互換用の転送モジュール" in p.read_text()]
mp = {}
for p in stubs:
    old = str(p.with_suffix("")).replace("/", ".")
    mp[old] = re.search(r"public import (\S+)", p.read_text()).group(1)
for f in ["SerrePositivity.lean", "scripts/audit_f5.lean", "scripts/audit_f7.lean"]:
    s = pathlib.Path(f).read_text()
    t = re.sub(r"^((?:public )?import )(\S+)$", lambda m: m.group(1) + mp.get(m.group(2), m.group(2)), s, flags=re.M)
    pathlib.Path(f).write_text(t)
    print(f, sum(1 for a, b in zip(s.splitlines(), t.splitlines()) if a != b))
PY
# 期待値：SerrePositivity.lean 30、scripts/audit_f5.lean 1、scripts/audit_f7.lean 1
```

書き換えは import 先のモジュールを同じものに保つ（スタブは新しい場所を再公開するだけ）ので、ビルド結果は変わらない。
書き換えのコミット後に BS 作業チャットへ知らせてもらえれば、BS 側でスタブ 32 本を削除する。
