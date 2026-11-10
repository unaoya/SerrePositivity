# BS-W15 K1 の検証中の証明

BS 著者版 Lemma 2.38 と Corollary 2.39 の有限 Koszul 正則列の実装候補。指定 worktree の本体と同じ相対パスで保存した。まだ対象ビルドと監査は未完了。

最初に `RegularSequencePD`、`FreeDPModPBlocks`、`PrincipalReduction` を検証する。前回の検証は、順に商の係数代数構造・二重像、基底の座標計算、ホモロジー写像の `IsIso` に型エラーがあり、候補ではそれぞれ修正を試みている。続いて `RegularSequencePDFactorial` と `RegularSequencePDKoszul`、`RegularSequencePDPrimeRegular`、`RegularSequencePDTor` と `FrobeniusDivisionRegularSequence` の順に閉じる。切断イデアルの展開は、`TruncatedPolynomialBasis` 側で定義の公開方法をそろえる必要がある。

高次 Tor の候補は係数多項式環 `A[X_i]` 上の計算。原典の `ℤ_(p)[X_i]` 上の Tor との比較は、`ℤ_(p) → A` の平坦性と自由分冪代数の底変換を用いる追加段階。完備模型の候補は `PDCompletionH0` の環同型であり、⑤b の標準脚との可換性も確認する。

鍵付き検証時は、依存を含めて候補を隔離したモジュールパスに置く。宣言が閉じてから指定 worktree の本体へ移し、小さい対象ビルドと `AuditK1.lean` を実行する。
