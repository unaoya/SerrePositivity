# E∞-dg 代数

## 規約

namespace は `SerrePositivity.EInfinity`。
`A : Type u`、`[CommRing A]`、`Complex A = CochainComplex (ModuleCat.{u} A) ℤ`。
複体は非有界、微分は +1、ホモトピーは −1。
射影モデル構造は `letI := projectiveModelCategory A` として局所的に選ぶ。
対称列は既存の `SerrePositivity.SymmetricSequence (Complex A)` を使う。
その共変な置換作用から、逆元で通常の右作用を得る。
テンソル積と交換には既存の Koszul 符号付きモノイダル構造を使う。
オペラッドと代数は arity 0 の演算を含む。

## E2a-3 の設計変更案（未採用）

目標は任意の可換環 A 上の完全な転送モデル構造であり、
弱同値と fibration は忘却関手 U で作る。自由関手を F、複体の生成類を I・J とする。
`Transfer.Right.rightTransfer` に渡す acyclicity は次の包含である。

```text
transfiniteCompositions ((coproducts (J.strictMap F)).pushouts)
  ≤ (quasiIso (ModuleCat A) (.up ℤ)).inverseImage U
```

原指示の Berger–Moerdijk §5 の filtration 議論では、命題 5.4 の入力の代数は
cellular である。Berger–Fresse 3.1.7 も Σ-projective なオペラッドに対する
cofibrant な始域の結論を述べている。これらから任意の始域に対する上記の包含を
そのまま得ることはできない。始域の cofibrancy を追加した結果で置き換えない。

提案する証明経路は次のとおり。

1. E2a-2 に Alexander–Whitney 対角 `E → E ⊗ E` と、標準区間の正規化鎖の
   E-coalgebra 構造を追加する。
2. これらから全 E 代数の functorial path object を構成する。これは
   Berger–Moerdijk 命題 4.1(a)・§4.6.3、Berger–Fresse 3.1.2–3.1.6 の経路である。
3. fibration に対して左持ち上げ性を持つ任意の代数射について、零複体上の終対象への
   持ち上げから retraction を得る。さらに path object の両端への fibration に
   持ち上げ、底の複体射がホモトピー同値であることを証明する。
4. したがって `fibrations.llp ≤ weakEquivalences` を得る。自由・忘却随伴の
   lifting 対応から生成 J-cell 射にこれを適用し、上記の acyclicity を得る。
5. 自由像の I・J の小対象性と有限極限・余極限は別途証明し、
   `Transfer.Right.rightTransfer` で Mathlib の `ModelCategory` を構成する。

この案は未採用であり、`AlgebraModel.lean` の実装はまだ開始していない。

原典：
[Berger–Moerdijk 2003](https://arxiv.org/pdf/math/0206094)、
[Berger–Fresse 2004](https://arxiv.org/pdf/math/0109158)。
