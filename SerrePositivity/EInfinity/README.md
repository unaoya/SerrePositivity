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

工程 1 は完了。一般の正規化 AW 鎖対角と shuffle の余代数射性を整数模型へ移し、
`BarrattEccles.partialComposition_diagonal_tensorμ` で既存 BE 部分合成との両立を検証した。
`Operad.hadamard` は arity ごとのテンソルオペラッドであり、単位・内外等変性・
入れ子と独立な代入の結合則を含む。`BarrattEccles.unit_diagonal` と自然性を合わせ、
`hopfDiagonal : E → E ⊗ E` を実際のオペラッド射として構成済み。
`BarrattEccles.hopf` はこの対角、既存の `augmentation : E → Com`、
余結合性と左右余単位則を束ねる。余可換性は要求しない。
工程 2 の抽象界面は `Operad.CoalgebraInterval`。余演算を保つ二端点・収縮と、
底の複体の境界 cofibration・収縮の擬同型を持つ。区間は augmentation を保存する
オペラッド射で制限でき、制限射の Hopf 対角保存は不要。
`convolutionAction` は内部 Hom 上の各 arity の演算 chain map、
`CoalgebraInterval.prepathComplex` は底の複体の定数射・両端点評価と三角形を供給する。
定数・評価の自然性も検証済み。`convolutionAction_unit` が単位則、
`convolutionAction_equivariance` が全置換についての等変性を与える。
`convolutionAction_post` は P 代数射による後合成の演算保存を与える。
反復評価は二ブロックの連結・分割と両立する。
`convolutionAction_insertion_zero_evaluation` は標準の先頭代入と余代入の評価を比較する。
`Algebra.ofFirstComposition` は等変性と先頭の部分合成則から全代数公理を構成する。
`convolutionAction_comp` で全位置の部分合成則を証明し、`convolutionAlgebra` を構成済み。
余代数射の前合成も全演算を保存する。`convolutionFunctor` は固定した余代数からの
代数の自己関手、`convolutionPreNat` は余代数射による自然な前合成を与える。
`unitCoalgebra ε` は任意の augmentation からの単位余代数。
`convolutionUnitNatIso` は Hom(単位,B) ≅ B を自然な代数同型にする。
`CoalgebraInterval.prepathAlgebra` は自然な代数射である定数射・両端点評価を持ち、
底の射は既存の `constant`・`evaluation` と厳密に一致する。
`evaluationPair_projectiveFibration` は底の二端点評価の対の射影 fibration 性を与える。
射影 cofibration の各次数での分裂を持ち上げ性から導き、任意の値域への Hom の
境界制限の全次数全射性を証明した。値域の cofibrancy は不要。
`constant_quasiIso` と `evaluation_quasiIso` により、定数射と両端点評価は底で擬同型。
単位の cofibrancy と端点の trivial cofibration から鎖ホモトピー逆を構成し、
符号付き前合成によって内部 Hom へ移した。区間のホモトピー同値性を追加仮定にしていない。
`Algebra.ofJointlyMonicActions` は共同単射な射の後で代数公理を判定する。
`Algebra.binaryProductIsLimit` と `Algebra.terminalAlgebraIsTerminal` により二項積と終対象を構成。
`Algebra.binaryProductIso` は選んだ積と底の直和上の代数の比較同型。
弱同値・fibration の構造は忘却の逆像として局所的に選び、モデル構造は仮定しない。
`CoalgebraInterval.pathAlgebra` は全代数の good path object。
`fibrations_llp_quasiIso` は終対象と二端点評価への持ち上げから retraction と逆合成の path を取り、
底の擬同型性を示す。`freeGeneratingTrivialCofibrations_cell_acyclicity` は自由・忘却随伴と
左持ち上げ類の閉性を使い、任意の始域に対する相対 J-cell 射の acyclicity を与える。
`Algebra.forget_createsLimit` は任意の底の極限錐を頂点ごと持ち上げる。
代数の圏は全ての小極限を持ち、忘却は底に存在する形の極限を作り、保存する。
`tensorPower_preservesSiftedColimits_of_tensor` は一般のモノイダル圏で両変数の保存から
有限テンソル冪の sifted 余極限保存を導く。複体の閉モノイダル構造へ適用済み。
Schur 関手と自由・忘却の合成の sifted・filtered 余極限保存も検証済み。
工程 2 は完了。`Algebra.forget_createsColimit` はテンソル冪で保存される底の余極限を作る。
sifted・filtered 余極限の創出・保存と忘却のモナド性を証明済み。
reflexive coequalizer の形の sifted 性を検証し、図式圏へのモナド性の拡張と随伴持ち上げで
代数の全小余極限を構成した。一般の余極限を忘却が保つとは仮定しない。
自由代数による有限表示性の保存から、自由像の I・J が ℵ₀ の小対象論法を許すことを証明。
`Operad.intervalModelCategory` は任意の Hopf オペラッドと余代数区間からの完全な転送モデル構造。
弱同値と fibration は忘却の逆像であり、自由像で生成され、忘却関手は右 Quillen。
モデル構造は局所的に選び、始域の cofibrancy は要求しない。
工程 3 は TR の正規化への降下まで構成済み。`Surjection.BasisWord` は隣接値が異なる全射語、
`degreeModule` はその自由加群であり、退化・非全射な語は零へ送る。
区切り位置の個数が次数に等しいこと、削除符号と線形な削除写像の置換同変性を証明。
次数零は置換と同値で、BE の右作用の規約には逆置換の語が対応する。
原典の七文字の例の符号・五項の削除式と、arity 0 の空語を監査で照合済み。
`TableReduction.onSequence` は任意の次数・arity の置換列について行長の有限和を構成する。
行抽出の長さと単射な文字変更との両立、有限和の置換同変性を証明済み。
`degreeMap` は実際の BE 複体の自由基底から各次数の線形写像へ延長する。
次数零は逆置換の語、arity 0 の次数零は空語・正次数は零になる。
原典の table の例について、非退化出力の二項と各項の重複度 1 を監査で確認済み。
同じ隣接行の境界重複から、退化な置換列の各項と有限和の消滅を証明済み。
`onSequence_eq_zero_of_degenerate` は実際の BE 退化単体の消滅を与える。
`normalizedMap_generator` は退化単体も含む全ての正規化生成元の像を table の和と同定する。
`degreeMap_action` は実際の BE 各次数の線形写像の置換同変性。
`canonicalRow` は確定した最終出現と残りの最初の出現を連結し、全値を一度ずつ含む。
`canonicalPermutation` はその行を BE の頂点置換に変換する。
`rowStart` は区切りから得る d+1 個の開始位置で、狭義単調かつ正の arity では終端より前。
`canonicalVertices` と `canonicalSimplex` は指定した全射語の逆像候補を構成する。
復元行は最終出現だけの区間では不変で、区切りでは一文字を非自明に後方へ移す。
開始位置と次の区切りの間には別の区切りがないことを証明し、実際の隣接頂点へ適用済み。
`canonicalSimplex_mem_nonDegenerate` は候補単体の非退化性、
`canonicalNondegenerateSimplex` は正規化 BE 基底の実際の添字を与える。
具体例の復元行と唯一の非退化出力は監査済み。一般の TR の値の同定は未証明。
TR の全射性・微分保存・部分合成保存は未完成。
χ の平方零とオペラッド公理は、TR の全射性と保存則から導く原典の順に進む。
具体的な Δ¹ の余代数構造とその代入、E2a-4・5、E2b・G1′ は未完成。

原典：
[Berger–Moerdijk 2003](https://arxiv.org/pdf/math/0206094)、
[Berger–Fresse 2004](https://arxiv.org/pdf/math/0109158)。
