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

## E2a-3 の採用方針（2026-10-19）

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

採用する証明経路は次の四工程とし、各工程で検証してコミットする。

1. **Hopf 構造**：各 `E(n) = N_*(EΣ_n)` に Alexander–Whitney 対角を構成する。
   一般の単体集合について shuffle 写像が AW 余代数の射であることを証明し、
   単体的合成写像に対する AW の自然性から `E → E ⊗ E` のオペラッド射性を得る。
   余結合性、augmentation `E → Com` による余単位、Σ_n 同変性も証明する。
2. **区間の界面**：E-coalgebra H、鎖ホモトピー同値である余単位 `H → 𝟙`、
   E-coalgebra 射であり次数ごとに分裂単射である二点 `𝟙 ⊕ 𝟙 → H` を
   一つの structure にまとめる。この界面から全 E 代数の functorial path object
   `A → Hom(H, A) → A × A` を構成する。
   fibration に対して左持ち上げ性を持つ代数射について、終対象への持ち上げから
   retraction を得て、path object の両端への fibration に持ち上げることで、
   底の複体射がホモトピー同値であることを証明する。
   これにより `fibrations.llp ≤ weakEquivalences` を得る。
   自由・忘却随伴の lifting 対応から J-cell 射の acyclicity を導く。
   自由像の I・J の小対象性と有限極限・余極限も証明し、
   `Transfer.Right.rightTransfer` の適用を H の具体的構成に依存せず閉じる。
3. **区間の構成**：`H = N_*(Δ¹)` を用いる。Berger–Fresse §1.3 の
   table reduction `TR : E → χ` のオペラッド射性を一般に証明し、
   χ の区間切断作用（McClure–Smith）を Δ¹ に適用する。
   区間切断作用の計算は Δ¹ に特殊化してよく、必要な次数は `E(n)_r, r ≤ n`。
   一般の単体集合への一般化は費用が変わらない場合に限る。
   着手前にファイル数と主要補題の見積もりを計画に一段落で記す。
4. **転送の完成**：構成した区間を工程 2 の界面に代入して E2a-3 を完成し、E2a-4 へ進む。

この経路は Berger–Moerdijk 命題 4.1・§4.6.3、Berger–Fresse §3.1 に基づく。
始域の cofibrancy は追加せず、任意の可換環上の完全なモデル構造を構成する。
Hinich 4.1.1 はこの工程の原典に用いない。正標数では E は Σ-split でないためである。

工程 1 の現在地：一般の小さい単体集合の AW 鎖写像 `AlexanderWhitney.diagonal` を
負の整数コチェイン模型へ移した `cochainDiagonal` を構成済み。次数成分との接続は
`cochainDiagonal_projection_generator`。テンソルの標準比較は自然で、結合子・左右単位子を保つ。
実際の E(n) 上の `BarrattEccles.complexDiagonal` は余結合的で Σ_n 同変、既存の
augmentation を左右余単位に持つ。次は一般の shuffle の AW 余代数射性と
標準比較の braiding 適合性。Hopf オペラッド射と転送モデル構造は未完成。

原典：
[Berger–Moerdijk 2003](https://arxiv.org/pdf/math/0206094)、
[Berger–Fresse 2004](https://arxiv.org/pdf/math/0109158)。
