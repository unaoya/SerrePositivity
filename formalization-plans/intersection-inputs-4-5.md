# 外部引用4〜5：古典的交点重複度の証明経路

作成：2026-10-13。更新：2026-10-15。状態：引用5は Adams の経路で証明・監査完了。
従来の1〜5の計画から4・5の内容を分離した。以下の候補比較は当初の調査として保持する。
環の存在構成1〜3は [専用計画](local-algebra-1-3.md)、6は [Frobeniusの計画](frobenius-homology.md)。
全体は [overview](overview.md)を参照する。

## 1. 対象と引用境界

4は `Inputs.serrePositivity_of_field`、5は `Inputs.intersectionVanishing`。
所在は [SerrePositivity](../SerrePositivity/Inputs/SerrePositivity.lean) と
[IntersectionTheory](../SerrePositivity/Inputs/IntersectionTheory.lean)。
4の一般版は直接の `sorry` が残るが、主定理が使う剰余標数零の正値性は証明済み。
5は [Adams の計画](intersection-vanishing-adams.md) の S1–S11 により全剰余標数で証明済み。
公開型を保持し、公開消滅と利用先に `sorryAx` がないことを専用・共通監査で確認した。

## 2. 4番：Serre の等標数正値性

主定理が使う剰余標数零の場合は [対角線論法の計画](serre-equal-characteristic.md) で証明済み（2026-10-14）。
以下は当初の調査として残す。

### 主張と現在の再利用範囲

体を含む正則局所環 `R` と非零有限生成加群 `M,N` について、
`M ⊗_R N` が有限長で、`dim M + dim N = dim R` なら

\[
\chi^R(M,N)=\sum_i(-1)^i\ell_R\operatorname{Tor}_i^R(M,N)>0.
\]

現在の引用の利用先では、剰余標数零から体の作用を構成する部分を別に証明している。
[CharacteristicZeroReduction](../SerrePositivity/Paper/Section5/CharacteristicZeroReduction.lean) の
接続を、古典定理そのものの証明と区別する。

正則局所環上の有限自由分解、Tor の有限長性と加法性、Koszul、環自身に対する重複度公式などは再利用候補である。
ただし、現在の Koszul 重複度公式を任意の有限生成加群に対する公式として使用してはいけない。

### 対角線への帰着による候補

標準的な方向は、完備化と係数体による表示を経て、`R = k[[x_1,…,x_d]]` とし、
二つの変数組を持つ環上で対角線の元

\[
\delta_i=x_i\otimes1-1\otimes x_i
\]

を使うことである。Tor の Euler 数を、この列の Koszul Euler 数へ移す。
対角線への帰着は Serre の古典的議論であり、
[Skalit の論文](https://arxiv.org/html/1409.3616)にも、その利用とスペクトル系列が記されている。

整備すべき核心は、完備テンソル積の具体的構成、Noether 性・次元、
対角線の商と有限長性、Tor と Koszul の比較である。
通常のテンソル積と完備テンソル積を同一視しない。

最後の重複度への接続には二案がある。

- **一般加群版を作る。** 完備テンソル積の上の `M` と `N` から作る有限加群について、
  次元・非零性・パラメータ条件を確認し、加群版の Koszul 重複度公式と正値性を使う。
- **素因子へ分解する。** 加法性と prime filtration で `R/P,R/Q` へ移し、
  `D=(R/P)\widehat\otimes_k(R/Q)` の環自身に対する公式を使う。
  最大次元の成分で正値性を、次元和が小さい成分で等標数の消滅を示す必要がある。

後者でも「長さ `d` の列に対し、環の次元が `d` 未満なら Koszul Euler 数が零」という接続が必要になる。
これを5番の一般消滅を引用して済ませれば、4番のその証明は5番に依存する。
4番を独立に証明したい場合は、この等標数の消滅を対角線と重複度の議論から導く。

### 段階別計画

1. 現行引用の一般性を保つ、完備化・係数体・冪級数表示への還元を整理する。
2. 完備テンソル積と対角線の具体的な環・加群・写像を作る。
3. 有限長性、支持の次元、対角線 Koszul と Tor の対応を証明する。
4. 一般加群版と prime filtration 版の不足を比較し、重複度に接続する。
5. 等標数正値性を導き、任意の体を含む正則局所環の現行宣言へ戻す。

4番はホモロジー代数と可換環論の両方を使うが、
5番の局所 Chern character や6番の tight closure を先に全面実装する計画にはしない。

## 3. 5番：Roberts–Gillet–Soulé の交点重複度消滅

2026-10-15：巡回 Adams 二乗と三乗で証明・監査完了。以下の候補は履歴として残す。

### 主張

任意の正則局所環 `R` と有限生成加群 `M,N` に対し、テンソル積が有限長で

\[
\dim M+\dim N<\dim R
\]

なら `χ^R(M,N)=0`。証明済みの公開型は体を含む場合に限定されず、混標数も含む。
論文では低次元の項を除くために用いる。
定理3.1・補題4.6の二つの降下入力とは別の外部定理である。

### 候補A：局所 Chern character と Riemann–Roch

[Roberts の一次解説](https://www.numdam.org/article/PSMIR_1985___4_25_0.pdf)
は、局所 Chern character と重複度の関係、および消滅への適用を説明している。

有限自由分解 `F,G` を取り、局所 Riemann–Roch と積の公式を用いて Euler 数を表す。
支持の余次元に応じた Chern character の低次数成分の消滅と、
正則環の Riemann–Roch 類の性質を用い、次元和が小さいと寄与が消えることを導く。

形式化する対象と成果物：Chow 群、支持つき局所 Chern character、積・次数の規則、
局所 Riemann–Roch、正則環での特殊化、必要な余次元の消滅定理。
特に、支持が小さいことから低次数成分が消える部分も数学的な定理であり、定義だけから省略しない。

Ma の Dutta 重複度の公式にも近い言語だが、その交代和の計算から6番の個々の高次ホモロジー消滅が
自動的に得られるわけではない。6番の計画とはこの点を区別する。

### 候補B：支持つきK理論と Adams 操作

Gillet–Soulé の方法では、支持つきK理論の Adams 操作と、支持の余次元に対応する重みを使う。
有限長支持での Euler 数の重み、テンソル積に対する積性を合わせて、次元条件から消滅を導く方向である。

形式化する対象と成果物：支持つきK₀、テンソル積、Adams 操作、
必要な重みの分解または filtration、支持の余次元の制約、有限長支持の Euler 数との両立。
これらの一般結果から具体的な消滅を証明する部分を分離する。

[Brown–Miller–Thompson–Walker, *Cyclic Adams Operations*](https://arxiv.org/abs/1601.05072)
は、循環的 Adams 操作から Serre の消滅を導く経路も提示する。
この版を採用する場合は、操作に使う素数の可逆性、根の追加、係数拡大からの帰着など、
原文の仮定を確認する。全ての正則局所環に直接適用できると仮定しない。

### 経路選択とK理論計画との関係

5番の経路は未確定である。次の調査をしてから選ぶ。

1. 原典の定理の仮定・結論と、一般正則局所環への還元を固定する。
2. Chern／Riemann–Roch と Adams の各経路で、構成すべき具体的対象と引用する一般定理を比較する。
3. [K理論の計画](k-theory.md)と共有できる API を確認する。
4. 必要な一般定理から `intersectionVanishing` を導き、依存を監査する。

K理論降下の計画にはスペクトル・dg 理論の整備が含まれるが、それだけで Adams 操作の証明が完成するわけではない。
逆に、5番に必要な支持つきK₀と操作から始める計画が、非連結K理論全体を必ず先に作ることを意味するわけでもない。
基礎の重複を避けつつ、数学的に必要な追加理論を明示する。

## 4. 区切りと検証

- 4：現行引用の一般性を保つ還元、完備テンソル積、対角線、Tor/Koszul比較、重複度への接続。
- 5：原典の仮定と全還元の確認、Chern／Adamsの基盤比較、経路選択、具体的消滅への接続。
- 1〜3の限定版が完成しても、4〜5の必要な仮定がすべて供給されたとは扱わない。
- 一般結果の引用には正確な型と出典を記し、既存引用の別名への移動で完了とはしない。
- 実装時は対象モジュール・全体ビルド・下流公理監査を行う。文書だけの変更ではリンクを確認する。

新しい一般論は `CommutativeAlgebra/`・`HomologicalAlgebra/`・K理論の一般層、
論文の適用は `Paper/` に置く。期間は初回API調査と具体的な証明単位から評価する。

## 5. 参照と未確認範囲

- Serre, [Local Algebra](https://doi.org/10.1007/978-3-662-04203-8), Chapter V, Theorem 1。証明全体の逐条照合は未実施。
- Skalit, [Intersection Multiplicity of Serre in the Unramified Case](https://arxiv.org/html/1409.3616)。対角線の経路の参考。
- Roberts, [Intersection Multiplicities in Commutative Algebra](https://www.numdam.org/article/PSMIR_1985___4_25_0.pdf)。局所Chern characterの一次解説。
- Gillet–Soulé, Intersection theory using Adams operations。原論文の版・番号・全依存を追加調査する。
- Brown–Miller–Thompson–Walker, [Cyclic Adams Operations](https://arxiv.org/abs/1601.05072)。一般ステートメントへの全還元は未確認。

今回の分離は既存の計画を保存するためで、新たな原典調査や4〜5の方針変更の報告ではない。
