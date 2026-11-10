# BS-W15 K1 の検証中の証明

BS 著者版 Lemma 2.38 と Corollary 2.39 の有限 Koszul 正則列の実装候補。指定 worktree の本体と同じ相対パスで保存した。まだ対象ビルドと監査は未完了。

`PrincipalReduction`、`RegularSequencePD`、`FreeDPModPBlocks` は対象ビルドと監査を通過し、本体へ移した。次は `PrimeLocalFlat`、`RegularSequencePDFactorial` と `RegularSequencePDKoszul` を単体で検証する。続いて `RegularSequencePDPrimeRegular`、`RegularSequencePDTor`、`FrobeniusDivisionRegularSequence`、`RegularSequencePDUniversalTor` を閉じる。

高次 Tor はまず係数多項式環 `A[X_i]` 上で計算する。`PrimeLocalFlat` と `RegularSequencePDUniversalTor` は、`ℤ_(p) → A` の平坦性と自由分冪代数の底変換から原典の `ℤ_(p)[X_i]` 上の Tor へ戻す候補。完備模型の候補は `PDCompletionH0` の環同型であり、⑤b の標準脚との可換性も確認する。

鍵付き検証時は、依存を含めて候補を隔離したモジュールパスに置く。宣言が閉じてから指定 worktree の本体へ移し、小さい対象ビルドと `AuditK1.lean` を実行する。
