# Frobenius 高次ホモロジー消滅の調査と形式化計画

作成日：2026-10-13。状態：調査・設計段階。新しい Lean 実装はこの文書の作成には含まない。

## 1. 対象と現在の方針

これまで外部引用一覧の「6番」と呼んでいた、Roberts の Frobenius 高次ホモロジーの
正規化長さ消滅を対象とする。既存の引用を下から証明していくための計画であり、
論文全体や tight closure 理論全体を一度に形式化する計画ではない。

最初の実装目標は、現在の等標数構成が必要とする、完備 Noether 局所整域上の
パラメータ Koszul 複体の消滅とする。そのために使う一般結果は、論文専用の仮定束ではなく、
具体的な環・加群・複体について独立した定理として整備する。

会話では tight closure 経路を優先して比較検討する案を出した。
その後、Roberts の双対化複体による一様零化も一次資料で確認できたため、
現段階で tight closure 経路に確定せず、両者の必要な基礎理論を比較する。
初期段階では、長さ評価から消滅への接続と、低次元係数への比較を共通の成果物にする。

原証明の未確認箇所を、既に証明・調査済みの結果として扱わない。
深い外部結果を引用することは許容されているが、新しい引用を実装するときは、
正確な仮定・結論・文献番号を明示し、証明した接続部分と区別する。

## 2. 現在の実装と、6番の役割

現在の引用は
[Inputs/RobertsFrobenius.lean](../SerrePositivity/Inputs/RobertsFrobenius.lean) の
`SerrePositivity.Inputs.frobenius_homology_length_tendsto_zero`。

その仮定は次のとおり。

- `D` は完備 Noether 局所環、標数は素数 `p`。
- `ringKrullDim D = d`。
- `K` は有限自由項を持ち、cochain 次数 `[-d, 0]` の外で零。
- 全てのホモロジーが有限長。

結論は、homological 次数 `i > 0`、すなわち cochain 次数 `-i` に対して

\[
\frac{\ell_D H_i(F^nK)}{p^{nd}}\longrightarrow 0.
\]

ここで `F^n` は `iterateFrobenius` に沿った基底変更である。
現在この一般定理の証明は名前付きの `sorry` である。

引用から等標数構成までの次の部分は、既に実装されている。

| モジュール | 役割 |
| --- | --- |
| [FrobeniusKoszulLimit](../SerrePositivity/CommutativeAlgebra/FrobeniusKoszulLimit.lean) | Koszul 複体の適用条件、Frobenius 基底変更とパラメータの冪の同定、数値の変換 |
| [PerfectKoszulLength](../SerrePositivity/Paper/Section2/PerfectKoszulLength.lean) | 有限段の Koszul ホモロジーの正規化長さの同定 |
| [PerfectKoszulLimit](../SerrePositivity/Paper/Section2/PerfectKoszulLimit.lean) | ホモロジーと有向極限の比較、消滅極限から perfection 上の長さ零への移送 |
| [KoszulMultiplicityLimit](../SerrePositivity/CommutativeAlgebra/KoszulMultiplicityLimit.lean) | 高次の消滅、Koszul Euler 公式、冪の重複度公式から商の極限を同定 |
| [LengthAlgebraConstruction](../SerrePositivity/Paper/Section2/LengthAlgebraConstruction.lean) | 二つの長さの性質をまとめ、具体的な等標数の長さ代数を構成 |

特に `perfectClosure_length_properties_of_higher_tendsto` は、パラメータ系 `z` に対する

\[
\frac{\ell_D H_i(K(z_1^{p^n},\ldots,z_d^{p^n};D))}{p^{nd}}
\longrightarrow 0\qquad(i>0)
\]

から次の二性質を導く、証明済みの接続である。

1. perfection 上の正次数 Koszul ホモロジーの正規化長さが零。
2. perfection のパラメータ商の正規化長さが Hilbert–Samuel 重複度に一致。

従って6番は、抽象 Euler・比較理論を具体的な等標数の環で実現する重要な入力である。
新しい証明でも、この接続を再利用する。

実際の適用先は、完備局所整域、完全な剰余体、および正則局所環からの有限な正規化を持つ。
一方、現在の引用のステートメント自体は整域・完全剰余体を仮定しない。
適用先だけの証明ができた時点と、一般引用全体を証明できた時点は区別する。

## 3. 一次資料で確認できた結果

### 3.1. Ma の記述

[Ma, *Lech's conjecture in dimension three*, v3](https://arxiv.org/html/1609.00095v3)
§2.3、定理2.4は、現在の引用に対応する消滅を述べる。
直前には、Roberts (1989) の結果と、tight closure による
Hochster–Huneke (1993)、定理6.2の強化版を区別して記している。
Ma 自身がこの箇所で tight closure による証明を与えているわけではない。

### 3.2. Hochster–Huneke の強い成長評価

[Bhatt–Hochster–Ma, *Lim Cohen–Macaulay sequences of modules*, 最終稿](https://sites.lsa.umich.edu/hochster/wp-content/uploads/sites/1337/2026/02/limCM-Crelle-final.pdf)
定理5.2（印刷頁20）は、[HH93, Theorem 6.2] を再掲している。

標数 `p > 0` の Noether 局所環 `R` 上で、長さ `s` の有限自由複体 `G` の全ホモロジーが有限長、
`M` は有限生成、`d = dim M` とする。ある `C > 0` が存在し、全ての自然数 `t, n` に対して

\[
\ell_R H_{s-t}(M\otimes_R F^nG)
\le C p^{n\min(d,t)}.
\]

このステートメントには、完備・整域・被約・等次元・F-finite・完全剰余体の追加仮定はない。
負の homological 次数は零として読む。`M = R`、`s = d`、`t = d-i` とすると

\[
\ell_R H_i(F^nG)\le Cp^{n(d-i)}\qquad(1\le i\le d).
\]

これを `p^(nd)` で割れば、現在必要な消滅が従う。`i > d` は振幅の外で零。
この成長評価は確認済みだが、HH93 原本 §6 の証明全文と、その全依存関係は未確認である。

### 3.3. Phantom acyclicity と test element

[Hochster の2004年講義](https://www.math.utah.edu/vigre/minicourses/algebra/hochster.pdf)
定理15は、標数 `p > 0` の Noether 整域上で、自由複体のランク条件と小行列式イデアルの
高さ条件から、サイクルが境界の tight closure に入るという判定を述べる。
この資料で確認したものは整域版であり、非被約の環へそのまま適用してはいけない。

[Hochster–Huneke の一次プレプリント](https://sites.lsa.umich.edu/hochster/wp-content/uploads/sites/1337/2024/09/tcz.pdf)
§1.4.11–12は、excellent local ring に completely stable weak test element を保証し、
被約の場合の test element を区別する。通常の test element と weak test element の
Frobenius 冪に関する量化条件を混同しない。

### 3.4. Roberts の一様零化

[Roberts, *Two applications of dualizing complexes over local rings* (1976)](https://www.numdam.org/article/ASENS_1976_4_9_1_103_0.pdf)
命題1・定理1（頁104）は、双対化複体のホモロジーの零化イデアルの積 `b_j` について、
`dim(R/b_j) ≤ j` と、有限長ホモロジーを持つ有限自由複体の対応する次数の一様零化を示す。
証明には二つのスペクトル系列と Matlis 双対が使われる。

この結果を次数を反転して読むと、完備局所整域の長さ `d` の複体について、
高次ホモロジーを一様に消す非零元を得る入口になる。
Frobenius 後にも適用するには、その複体の有限長ホモロジーを確認する必要がある。

これは1976年論文で確認した代数的な入口であり、Roberts (1989) の原証明全体を確認したという意味ではない。
1989年原本の該当箇所と、必要な成長評価の正確な版・仮定は追加確認が必要である。

## 4. 5番との関係

5番は交点重複度の消滅、6番は個々の高次ホモロジーの正規化長さの消滅である。

局所 Chern character と局所 Riemann–Roch は、Euler 数という交代和を計算する。
Ma の式 (2.3.2) の Dutta 重複度の公式と、定理2.4の個別ホモロジー消滅は別の主張である。
交代和の極限だけから各正次数の消滅を導くことはできない。

6番のために、5番の Chow 群・局所 Riemann–Roch、または Adams 操作による K 理論を
全て先に整備する計画にはしない。共有できる基盤は、有限自由複体、支持、長さ、
完全列、係数変更などである。双対化複体や tight closure は、それぞれ別の追加基盤になる。
定理3.1・補題4.6の計画は [K理論の計画](k-theory.md) で扱う。

## 5. 比較する二つの証明経路

### A. Tight closure 経路

検討する流れは、tight closure の具体的定義、phantom acyclicity、Frobenius 反復との両立、
test element などによる一様な制御、長さ評価、正規化消滅である。
この並びは証明設計の候補であり、HH93 原証明の依存関係を確定したものではない。

Koszul 版では、パラメータに関する colon-capturing から進むか、一般の小行列式による
phantom acyclicity criterion を使うかも比較する。必要な結論に対して、どちらの整備が小さいかを確認する。

必要になる可能性がある成果物：

- Frobenius による部分加群の変換と tight closure の定義、表示に依存しないこと。
- phantom homology と stably phantom homology の定義。
- Koszul 複体での phantom acyclicity と、その反復版。
- 適用する環での test element の存在と、必要な一様制御への接続。
- その制御から長さ評価を導く定理。

正標数の可換環論・ホモロジー代数として進められるが、これらの深い定理の証明は大きな作業になり得る。
tight closure の局所化問題や F-regularity の全理論など、今回の依存に入らない一般論は初期対象にしない。

### B. 双対化複体と低次元係数の成長評価

完備局所整域 `D` に対して、一様な非零元 `c` が

\[
cH_i(F^nK)=0\qquad(i>0,\ n\ge0)
\]

を満たすとする。有限自由項上では `c` 倍は単射なので、複体の短完全列

\[
0\longrightarrow F^nK\xrightarrow{c}F^nK
\longrightarrow F^nK\otimes_D D/cD\longrightarrow0
\]

の長完全列から

\[
H_{i+1}(F^nK\otimes_D D/cD)\twoheadrightarrow H_i(F^nK)
\]

を得る。従って、低次元の有限係数加群に対する評価

\[
\ell_D H_j(F^nK\otimes_D M)\le C p^{n\dim M}
\]

を `M = D/cD` に適用できれば、`dim(D/cD) ≤ d-1` から正規化消滅を得る。
商が零の場合は別途自明な場合として処理する。

この流れは確認した一様零化からの再構成案である。
成長評価の正確な仮定・出典は実装前に固定する。HH93 の強い定理をその評価として使うと、
6番を下から証明したことにはならないため、依存が循環しない成長評価を確保する。

追加基盤は、双対化複体、Matlis 双対、二重複体とスペクトル系列、一様零化の構成である。
既存 API の不足を調べる前に、この経路が tight closure より軽いとは判断しない。

## 6. 段階別の形式化計画

| 段階 | 作業と成果物 | 完了条件 |
| --- | --- | --- |
| M0 | 文献の版・番号・仮定を固定し、両経路の依存表と Mathlib／既存コードの API 調査を作る | 長さ評価の出典と、引用する補助定理を特定。A/B の実装順を決定 |
| M1 | 次数別の成長評価から正規化消滅を導く一般補題を証明 | 振幅外、有限長、実数への変換、分母の正値性、極限を処理 |
| M2 | 非零元による複体の短完全列、ホモロジーの全射、長さ不等式を証明 | 具体的な複体と加群から比較を構成。一様零化と成長評価は定理の明示的な前提として扱う |
| M3 | 選択した経路の具体的基盤を定義し、文献補助定理を正確に定式化 | 対象・演算を定義し、未証明入力を台帳に列挙。6番全体の別名引用で完了とはしない |
| M4 | パラメータ Koszul 複体について、必要な制御と長さ評価から消滅を証明 | 適用先の仮定を確認し、`perfectClosure_length_properties_of_higher_tendsto` へ接続 |
| M5 | 一般の有限自由複体、および一般引用の環の仮定へ拡張 | 一般化を必要とする場合、非整域・非被約・非等次元の還元も含めて元のステートメントを証明 |
| M6 | 旧引用の利用箇所、解説、依存監査を更新 | 全体ビルドと引用依存の監査が通り、達成した範囲を文書に反映 |

M1・M2は両経路の比較を保ちながら実装できる。
M3以降は M0 の調査結果に従って進める。両経路を同時に全面実装することは初期目標にしない。

HH93 の強い評価を先に名前付きで引用し、M1 の接続を実装する案もある。
これは引用の精密化として有用だが、未証明依存を解消した成果とは数えない。
この文書の作成だけでは、その新しい引用をコードに追加しない。

新しい一般補題は `CommutativeAlgebra/` と `HomologicalAlgebra/` に置き、
`Paper/Section2/` は具体的適用を担う。共通の `CategoryTheory/` に Frobenius・環・塔の依存を持ち込まない。
モジュール名の確定は、既存 API と依存方向を調べてから行う。

## 7. 数学と Lean の確認事項

- **Frobenius の二種類。** 基底変更 `F^n` と係数制限 `F_*^n` を区別する。
  後者の有限生成性には F-finite の条件が関わり、剰余体の次数も長さに現れる。
- **Frobenius 後の有限長。** 非正則環で Frobenius の平坦性を仮定しない。
  閉点の外での有限自由完全複体の分裂と基底変更、支持の議論などから正しく確認する。
- **次数。** homological `i` は cochain `-i`。双対化のために次数を反転するときは振幅と零化次数を証明する。
- **長さ。** `ENat.toNat` や `ENNReal.toReal` に変換する前に有限性を確保する。
- **成長定数。** `C` は Frobenius の反復回数 `n` に依存しないことが必要。
  次数ごとの定数で足りる場合と、全次数共通の定数を要求する場合を区別する。
- **Test element。** 通常版・weak 版・stable 版の条件と適用範囲を明示する。
- **整域から一般環へ。** 完備整域での成果を、任意の完備 Noether 局所環の定理と同一視しない。
- **基礎定理の利用。** 一様零化や成長評価の証明に、目標の6番を間接的に使っていないか依存を確認する。

## 8. 引用境界と完了の意味

初期の区切りは、必要な補助結果を明示した上で、Koszul 版の消滅をそれらから導き、
現在の等標数構成へ接続することである。
この時点でも補助結果に `sorry` が残るなら、その依存は残っていると報告する。

一般引用全体の完了は、`frobenius_homology_length_tendsto_zero` の全仮定の下で証明を与えること。
適用先のみ完成した場合は、適用先の依存から旧引用を外せるかを調べ、一般引用自体の状態は別に記録する。
外部補助定理まで標準公理だけで証明したことは、さらに別の達成段階である。

実装後は、対象モジュールと全体のビルドに加え、
[公理監査](../scripts/audit_axioms.lean)で主定理までの未証明依存を確認する。
直接の `sorry` の数だけでなく、到達する引用定理の名前・意味・仮定を確認する。
文書だけの変更では、リンク・数式・現状のコードとの整合性を検証し、Lean の全体ビルドは不要。

## 9. 次の調査と未確定事項

1. HH93 定理6.2の原証明を入手し、tight closure の必要な補題と還元を確認する。
2. 低次元係数の Frobenius 成長評価の正確な定理・仮定を、Dutta／Seibert 等の一次資料から固定する。
3. Roberts (1989) の証明と、1976年の一様零化を使う再構成の関係を確認する。
4. Mathlib と本リポジトリの tight closure、双対化、スペクトル系列、長さ評価の実装を調査する。
5. Koszul 版に必要な範囲で A/B の不足を比較し、M3 の採用経路を決める。

現段階では工数や完成時期を確定しない。どちらの証明経路も、一般可換環論の定義だけで
短く終わると判断する根拠はない。一方、適用先が Koszul 複体に限られることは、
一般引用全体より先に実質的な成果を出すための有用な範囲設定である。

## 10. 参考文献

- Ma, [*Lech's conjecture in dimension three*, v3](https://arxiv.org/html/1609.00095v3), §2.3、定理2.4。
- Hochster–Huneke, *Phantom Homology*, Memoirs AMS 103, no.490 (1993), 定理6.2。
  原本の証明全文は未確認。ステートメントは次の著者を含む一次資料で確認。
- Bhatt–Hochster–Ma,
  [*Lim Cohen–Macaulay sequences of modules*, 最終稿](https://sites.lsa.umich.edu/hochster/wp-content/uploads/sites/1337/2026/02/limCM-Crelle-final.pdf), 定理5.2–5.4。
- Hochster, [2004年の講義](https://www.math.utah.edu/vigre/minicourses/algebra/hochster.pdf), 定理15。
- Hochster–Huneke,
  [*Tight closure in equal characteristic, big Cohen–Macaulay algebras, and solid closure*](https://sites.lsa.umich.edu/hochster/wp-content/uploads/sites/1337/2024/09/tcz.pdf), §1.4.11–12。
- Roberts,
  [*Two applications of dualizing complexes over local rings*](https://www.numdam.org/article/ASENS_1976_4_9_1_103_0.pdf), Ann. Sci. ENS 9 (1976), 103–106、命題1・定理1。
- Roberts, *Intersection theorems*, MSRI Publications 15 (1989), 417–436。
  [出版 DOI](https://doi.org/10.1007/978-1-4612-3660-3_23)。原本の該当証明は未確認。
- Hochster, [*Intersection Theorems*, 2006年の講演](https://sites.lsa.umich.edu/hochster/wp-content/uploads/sites/1337/2024/10/swb2.pdf), 頁9–11。
  Dutta 重複度等の証明の説明であり、それだけで6番の原証明全体を確認したとはしない。
- Seibert, *Complexes with homology of finite length and Frobenius functors*, J. Algebra 125 (1989), 278–287。
  [出版 DOI](https://doi.org/10.1016/0021-8693(89)90164-6)。必要な成長評価の適用仮定は追加調査する。
