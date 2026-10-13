# 外部引用1〜3：剰余体拡大と有限正規化の詳細計画

作成・更新：2026-10-13。状態：P1・R3・R4の完備Noether局所実現と、A4の一般Noether判定まで実装済み。
現在の到達点と検証結果は§12。引用1と引用3を既存の公開型を保って実構成へ置換した。
次は引用2の任意剰余体の係数体とCohen–Gabberの分離的選択。
引用2は微分を軸にしたGabberの原証明を採用する。
詳細な証明順と受入条件は [微分経路の計画](cohen-gabber-differentials.md) を正本とする。
未実装のステートメント案は計画として扱い、引用1・3は解消済み。引用2の一般形は未解消。

共通の完備化の平坦性・係数制限の比較・分担は、[完備化の統合計画](adic-completion-integration.md)を正本とする。
この計画ではA4のNoether判定と剰余体拡大への固有の適用を担当する。共通平坦性はCLMST側の一般完全性からの流れで進める。

対象は会話の外部引用番号1〜3。論文の節番号ではない。
4〜5は [交点重複度の計画](intersection-inputs-4-5.md)、6は [Frobeniusの計画](frobenius-homology.md)で扱う。
この計画はそれらの実装順や、進行中のCLMST・K理論の実装を変更しない。

## 1. 最終目標と二種類の区切り

| 番号 | 現行入口 | 全体の完了条件 |
| --- | --- | --- |
| 1 | `Inputs.exists_complete_flat_local_extension` | 任意のNoether局所環Bと任意の剰余体拡大Kに、同じ宇宙の完備Noether平坦局所拡大B′を構成。極大イデアルの拡張と、剰余体同型のBの剰余体上の両立まで証明 |
| 2 | `Inputs.cohen_gabber_normalization` | 完備Noether局所整域D、標数p、任意の剰余体について、標準座標付きの正則冪級数基底と有限単射を構成。分数体拡大の分離性まで証明 |
| 3（解消済み） | `Inputs.cohen_normalization_mixedCharacteristic` | Witt係数、パラメータ、標準冪級数基底、同じ評価の有限性と単射性を実構成。既存の公開型に接続済み |

所在は [ResidueFieldExtension](../SerrePositivity/Inputs/ResidueFieldExtension.lean)、
[CohenNormalization](../SerrePositivity/Inputs/CohenNormalization.lean)。
現在、直接 `sorry` が残るのは2だけで、1・3は型を保った実構成の適用になっている。
この作業では新しい引用をコードへ追加しない。

**限定版の区切り**も設ける：1の単生成／有限生成体拡大版、2の完全剰余体版、
または係数環・パラメータを既に与えた条件付き有限正規化。
これらが完成しても、現行の一般引用の解消とは呼ばない。
補助定理を引用する区切りでは、その依存を明示し、`sorry`の移動を解消とは数えない。

## 2. 依存関係：共通するのは道具であり、存在構成は別

```text
A：adic・冪級数・有限性・標準基底の一般API
  ├─ R：単生成拡大 → 一般の剰余体拡大 → 完備Noether平坦版（1）
  ├─ C：係数体のsection → 有限正規化 → 分離的選択（2）
  └─ W：Witt係数の埋め込み → pと残りのパラメータ → 有限正規化（3）

Wは標数pの冪零核の持ち上げ、D/(p)の完備性、既存のθ写像を使う。
Rの一般拡大を経由する一般Cohen環の構成は採用していない。
Cの非完全剰余体の場合は、指定p-basisの持ち上げと係数体の変更が必要になる。
```

1→2→3という一本道にしない。共通APIの後、各構成に必要な入力を独立に確定する。
1の完成を待たずに、係数環が与えられた2・3の有限正規化を進められる。
ただし一般係数環の存在証明で1を使う場合は、依存図にその矢印を追加する。

## 3. 確認済みAPIと不足を区別する

調査対象は `lake-manifest.json` の固定Mathlibと現在の作業ツリー。
以下は計画作成時にソースで宣言と仮定を読んだ結果。実装後の型照合・ビルド・公理監査は§12に記録する。

| 部分 | 確認した材料 | 次に行うこと |
| --- | --- | --- |
| adicと位相的完備性 | Mathlib `AdicCompletion/Topology`：`IsAdic.isAdicComplete_iff`、`isPrecomplete_iff`、`isHausdorff_iff` | 既存結果を使用。新しい同値定理を作り直さない |
| 冪級数評価 | Mathlib `MvPowerSeries/Evaluation`：`eval₂Hom`、`eval₂_unique`、`eval₂_C`、`eval₂_X` | 有限列がI内にあるときの `HasEval` と、C・X上の計算を使いやすい入口へ整理 |
| 実際の使用例 | [AdicCompletionNoetherian](../SerrePositivity/CommutativeAlgebra/AdicCompletionNoetherian.lean)は `WithIdeal`、離散係数、`HasEval`、評価、商からの全射を既に使用 | まずこの証明を再利用。新しい入口は複数の利用先が必要な部分だけ抽出 |
| 完備な有限自由加群・全射 | [AdicCompleteness](../SerrePositivity/CommutativeAlgebra/AdicCompleteness.lean)：`isPrecomplete_pi`、`isPrecomplete_of_surjective`、`isAdicComplete_finite` | 有限生成判定の証明に前完備性を使用。結論の有限性を先に仮定しない |
| 商での全射から全射 | Mathlib `AdicCompletion/Functoriality`：`surjective_of_mkQ_comp_surjective`。仮定は始域の前完備性と終域の分離性 | 有限個の商生成元を持ち上げて適用する |
| 完備化の局所性・剰余体 | Mathlib `AdicCompletion/LocalRing`：有限生成極大イデアル版の局所性・完備性・剰余体写像の全単射 | 中間環のNoether性がなくても、FG版を確認して使用 |
| Witt環 | Mathlib `WittVector/DiscreteValuationRing`：`isDiscreteValuationRing`。`Complete`：`quotientPEquiv`、`isAdicCompleteIdealSpanP` | 完全剰余体から `PerfectRing k p` を供給し、(p)と極大イデアルを同定。W(k)→Dの存在とは分ける |
| 多変数冪級数のNoether性 | Mathlib `MvPowerSeries/Equiv`：有限変数の `isNoetherianRing` | 局所性・次元・正則性・混標数の(p,X)完備性は別に確認 |
| モニック多項式の商 | Mathlib `AdjoinRoot`：`powerBasisAux'`、モニック性からの整性等 | 1の代数的単生成拡大の有限自由性・平坦性に適用 |
| Weierstrass | Mathlib `PowerSeries/WeierstrassPreparation`に定理と分解の計算式がある | 再利用候補として保持。採用した微分経路の必須工程には置かない |

**Noether性の注意。** 既存の `isNoetherianRing_of_adicComplete_of_surjective_quotient` は
Noether環RからSへの写像と、R→S/Jの全射を要求する。
1ではB→Kは通常全射ではなく、K→中間環のsectionも与えられていない。
この補題をそのまま使うことも、2・3の係数環の存在を先に仮定することもできない。
A4の「商だけがNoether」の判定を別に扱う。

## 4. 共通APIの数学的ステートメント案

名前は候補。正確なLeanの引数・宇宙はP0で決める。前提と結論をfieldsに詰めた設定束は作らない。

### A1：有限変数のadic評価

可換環R、S、有限添字σ、環写像f : R→S、イデアルJ、列x : σ→Sを与え、
SがJ進完備、各x_i∈Jなら、具体的な評価写像

`ev : MvPowerSeries σ R →+* S`

を構成し、`ev(C r)=f(r)`、`ev(X_i)=x_i`を証明する。
係数環に離散位相を入れる方法は既存証明を使う。
一意性は明示した冪級数位相・連続性のもとで述べ、任意の環写像の一意性とはしない。
`(X_i)`の像は`(x_i)`である。
混標数ではさらに `(p,X_i)` の像を `(p,x_i)` と計算する。

### A2：完備性からの有限生成判定

可換環A、I⊂A、A加群Mについて、

- AはI進前完備、
- MはI進分離、
- M/IMはA/I上有限生成、

なら `Module.Finite A M`。
商生成元を有限個持ち上げ、A^n→Mを作り、`surjective_of_mkQ_comp_surjective`を適用する。
Mの有限生成性・Noether性・完備性を前提へ追加しない。
完備環版はこの弱い版の適用とする。
[Stacks 031D](https://stacks.math.columbia.edu/tag/031D)は完備環版を述べる。

### A3：冪級数基底からの条件付き有限正規化

既に係数写像とパラメータ列を与えた段階で、A1の評価を使う。

- 等標数：A=k[[X_1,…,X_h]]、I=(X_i)、D/(x_i)がk上有限。
- 混標数：A=W(k)[[X_2,…,X_h]]、I=(p,X_i)、D/(p,x_i)がk上有限。

AのI進完備性とDのID進分離性を確認し、A2からDのA上有限性を得る。
ここではD上の列がm_D準素なら、既存のイデアル冪比較から必要な分離性を得る。
有限性を得た後で、次元を使って単射性を証明する。

単射性の共通補題案：Aは有限次元のNoether局所整域、Dは非零の有限A代数で整域、
`dim D=dim A`ならA→Dは単射。
核が非零ならA/kerの次元が下がり、有限整拡大による次元一致と矛盾する。
適用前にAの次元・整域性を証明する。単射を使ってから有限性を導く循環を避ける。

### A4：商のNoether性からのNoether判定

`I.FG`、SがI進完備、S/IがNoetherならSはNoether。
さらに任意のSについて `I.FG` とS/IのNoether性から、I進完備化がNoetherであることを導く。
[Stacks 05GH](https://stacks.math.columbia.edu/tag/05GH)の仮定に合わせる。

随伴次数環を `(S/I)[T_1,…,T_r]` の商としてNoetherにし、各イデアルの初期形式の
有限生成元を持ち上げる。次数ごとの誤差を完備性で消す。
既存 `AssociatedGraded`・`ReesPresentation`の構成は任意の可換環を扱うが、
一部の有限生成定理はSのNoether性を要求する。
その定理をこの証明へ適用してSのNoether性を仮定してしまわないよう、使用箇所を点検する。
係数sectionを要求しないこの一般補題が、1の一般拡大の完備化に必要である。

2026-10-13に以下を実装した。

- `isNoetherianRing_gradedReesRing_of_fg`は、Mathlibの
  `isNoetherianRing_reesAlgebra_quotient`を適用する。I.FGとR/IのNoether性だけでよく、
  RのNoether性・完備性・係数sectionは要求しない。局所環の極大イデアル版も供給する。
- `reesCoefficientIdeal R I J`はJの元を全係数に持つRees多項式の実際のイデアル。
  `exists_finite_reesCoefficientIdeal_lifts`はその随伴次数環での像の生成元を、
  有限個のRees多項式z_iへ持ち上げる。全係数がJに入ることと、像を生成することを証明する。
- `submodule_le_range_of_shifted_adic_approximation`は、x∈N∩I^nMに対し
  p∈I^(n-c)Pとx-f(p)∈I^(n+1)Mを毎次数で供給できるならN⊆range fと結論する。
  完備な始域で係数の極限を取り、分離した終域で等式を得る。
  `fg_of_shifted_adic_approximation`は有限な係数加群PについてN.FGを導く。
  Nの閉性・前完備性・有限性やRのNoether性を仮定しない。

この近似条件も全てのJについて実際に供給し、A4を完成した。
`exists_shifted_approximation_of_rees_lifts`は有限個のz_iの次数の上界cを取り、
各z_iの0次からc次までの係数を有限な生成元候補に採用する。
Rees係数はI^(n-d)に入り、d≤cからI^(n-c)への所属を確認する。
Mathlibの`mem_map_algebraMap_reesAlgebra_iff`で商の誤差をI^(n+1)へ移し、
`fg_of_shifted_adic_approximation`を各Jへ適用する。

`isNoetherianRing_of_adicComplete_of_noetherian_quotient`は、I.FG、I進完備性、
R/IのNoether性だけからRのNoether性を結論する。係数section・RのNoether性は不要。
`isNoetherianRing_of_complete_local_of_fg`が局所版、
`isNoetherianRing_adicCompletion_of_noetherian_quotient`が非Noether環の完備化版。
既存の係数環からの全射による判定とNoether環の完備化も、この一般判定の適用へ整理した。


### A5：標準冪級数基底の性質

別々の定理として、k[[X]]とW(k)[[X]]の局所性、剰余体、極大イデアル、
指定イデアルについての完備性、次元、正則性を供給する。

- 体係数：極大イデアルは(X)、次元は変数の個数。
- Witt係数：極大イデアルは(p,X)、次元は変数の個数+1。
- Witt係数の(p,X)進完備性は完成。係数のp進完備性とMathlibのX進完備性を、
  `AdicCompletenessSup`の和の完備性へ実際に接続した。
- 正則性を先に仮定して、生成元数＝次元からその正則性を結論してしまわない。

必要な性質は [Stacks 0323 Remark 10.160.9](https://stacks.math.columbia.edu/tag/0323)に対応する。
有限変数でのNoether性と局所性はMathlibのインスタンスを再利用する。
`PowerSeriesLocalStructure`で定数係数の核・極大イデアル・極大イデアル進完備性を供給済み。
`PowerSeriesRegular`で次元公式と正則局所性も供給済み。
一変数のXによる商から次元を求め、生成数の上界から正則性を導き、有限変数へ帰納する。
一般の次元公式には係数環の正則性・整域性・完備性を要求しない。

## 5. R：1の剰余体拡大

### R1：代数的単生成拡大

R1/R2の完備化前の構成は任意の局所環B上で述べる。Noether性を使うのは
単生成のNoether版を完備化する段階であり、一般拡大の後続段の前提へ追加しない。

k=ResidueField B、K=k(α)、αのモニック既約最小多項式をfとする。
fの係数をBへ持ち上げてモニックFを作り、S=AdjoinRoot Fとする。

証明するもの：

1. Fの次数とモニック性、Sの具体的なB基底、有限自由性・平坦性。
2. S/m_BS ≃ k[T]/(f) ≃ K。係数写像とαの対応も確認。
3. 有限整拡大と閉ファイバーが体であることからSは局所環、極大イデアルはm_BS。
4. BがNoetherなのでSもNoether。Sを完備化し、既存のNoether環の完備化の平坦性を適用。
5. 完備化の剰余体同型を合成し、元のk上の可換性を保持。

fの分離性は要求しない。純非分離拡大も1の対象である。

2026-10-13に上の代数的単生成版を実装した。公開APIは§12参照。
生成条件は `IsIntegral k α` と `Algebra.adjoin k {α} = ⊤`。
代数的な一元による体生成ではk[α]=k(α)なので、この条件で対象範囲を表す。
一般の有限拡大が単生成であるとは仮定せず、分離的な原始元定理も使わない。

### R2：超越的単生成拡大

S=B[T]をm_B B[T]で局所化する。商はk[T]で、m_B B[T]は素イデアル。

証明するもの：局所性、平坦性、極大イデアルの拡張、剰余体とk(T)の同型、
αへの写像、Noether性。完備化はR1と同じNoether局所環用の補題を再利用する。
「閉ファイバーk[T]」と「局所化後の剰余体k(T)」を取り違えない。

2026-10-13に実装した。指定体Kの生成条件は
`Transcendental k α` と `IntermediateField.adjoin k {α} = ⊤`。
`residuePolynomialEval`の核Pで局所化し、超越性からP=m_B B[T]を証明する。
局所化の普遍性でKへの写像を構成し、k(α)の各元を多項式の比で表すMathlibの
`IntermediateField.mem_adjoin_simple_iff`から全射性を確認する。
商と有理関数体の同型を独自に一般化せず、指定体Kへ直接接続する。
全射の核が局所化の極大イデアルなので、商の第一同型定理で剰余体同型を得る。
係数とTの像も同じ写像で確認する。完備版はR1と共通の§12のAPIを適用する。

### R3：任意の体拡大

[Stacks 03C3](https://stacks.math.columbia.edu/tag/03C3)のようにKの元を整列し、
後続段ではR1/R2の**完備化前**の単生成構成、極限段では有向極限を使う。
各段で剰余体同型とKへの包含を両立させる。段ごとに完備化する別の図式は初期案に採用しない。

必要な保存定理：局所環・局所写像の極限、mの拡張、剰余体の極限、平坦加群の有向極限。
任意の環全体を対象にしたZornの補題ではなく、Kを用いたサイズの管理された添字を選ぶ。
環はType uに収める。整列・部分図式・colimitの宇宙上昇をP0で点検する。
中間環SはNoetherとは限らないが、極大イデアルn=m_BSは有限生成で、S/n≃Kである。
有限生成体拡大版は有限個のR1/R2の合成として先に完成できるが、一般K版とは別の区切り。

2026-10-13に有限生成体拡大版を実装した（§12）。Mathlibの
`IntermediateField.induction_on_adjoin_fg`で中間体を帰納し、後続段では
前段の剰余体同型eから係数写像を作る。`adjoin_eq_top_of_scalar_equiv`で
単生成条件を移送し、R1/R2の共通入口を適用する。基底段はB自身。
極大イデアル等式は`Ideal.map_map`、平坦性は`Module.Flat.trans`で合成する。
有限生成版では基底BがNoetherなので有限段の環もNoether。
最後だけ共通APIで完備化する。一般拡大の極限環のNoether性は、この帰納法からは得られない。

2026-10-13に極限段の保存APIも実装した（§12）。Mathlibの`DirectLimit`を用い、
平坦性は有限個の代表元と後続段での零関係から方程式判定で証明する。
局所性の保存には遷移写像の局所性は不要だが、各段から極限への写像の局所性には必要。
極大イデアルの拡張は各段の等式と`Ideal.map_map`から確認する。
指定体Kへの段写像が両立し、その像の合併がKを覆う場合、極限からKへの全射を作り、
剰余体同型と元の剰余体上の両立性を証明する。
基底がNoetherなら極限の極大イデアルは有限生成だが、極限環のNoether性は結論しない。
添字・各段がType uなら極限もType u。ただし、一般Kに対する整列・図式そのものの
構成はこの極限段のAPIだけからは得られない。

その後、体側の添字と後続段を実装した。`exists_residueGeneratorOrder`でK自身に整列を入れ、
`residueGeneratorBefore`／`residueGeneratorAfter`で開／閉初期部分の生成する中間体を定義する。
一元追加・単調性・初期部分の合併・最初の基底体・K全体の被覆を証明した。
添字と初期部分はKと同じ宇宙に収まる。順序体を仮定するのではなく、生成元のラベルに順序を入れる。
`exists_residueField_successor`はNoether性なしで旧段から新段への局所平坦写像を実際に構成し、
基底からの合成と剰余体写像の両立を証明する。有限生成版もこのAPIへ移行した。
`residueFieldStageMap`が段からKへの代数写像を構成し、核・像・段間の両立を計算する。
`AlgebraSystemWithTop`は新しい終段への両立する写像から具体的な延長図式を構成し、
自己・合成の法則を証明する。直極限から次の環への写像による接続も供給する。
これらを全ての整列段にわたって貼り合わせる依存再帰も実装した。以下の図式の保持と実貼り合わせを使う。

初期部分を扱う接続も実装した。`initialSegmentWithTopEquiv`が
`WithTop {j // j < i}`と`{j // j ≤ i}`を具体的に同定する。
`algebraInitialSegmentMap`は新終段の追加を閉初期部分へ移し、旧段の環・遷移・Kへの写像を保持する。
源・終域の型が添字によって異なる比較はHEqで述べ、実際の型の同一視も確認した。
二回の図式の制限が合成した一回の制限と一致することも証明した。
`algebraSystemGlueMap`は共有した段の環S_jと、制限が一致する初期部分の遷移p_iから、
全体の遷移を終域の初期部分p_kで定義する。局所の自己・合成則から全体の法則を導く。
`exists_flat_local_extension_of_initialSegments`がこの貼り合わせを極限段へ適用する。
段の環S_jそのものと、全段の制限一致は、`exists_coherent_residueFieldHistories`と構造を保つ貼り合わせで供給する。

開初期部分の直極限からの一段延長も接続した。
`algHomToIntermediateField`はKへの代数写像を値の入る中間体へ実際に制限する。
各段の像がAfter jならBefore iへの値の包含を証明し、非空で有向な中間体の合併という
Mathlibの定理からBefore i全体への被覆を供給する。K全体への被覆は要求しない。
`residueFieldBeforeLimitEquiv`は直極限の剰余体をBefore iへ同定し、段写像・係数写像と両立する。
`exists_residueField_successor_of_beforeLimit`はこの同型と保存定理を使って後続段を構成し、
剰余体を体側の等式に沿ってAfter iへ移す。
`exists_closed_extension_of_beforeLimit`が旧段から新終段への実際の写像を作り、
閉初期部分の図式の法則・局所性・平坦性・極大イデアル・全段のKへの像を確認する。
最小元では`residueFieldMinEquiv`でBの剰余体をBefore iへ同定し、Bを初期環としてiを加える。
`exists_closed_extension_of_min`は空添字の条件も証明し、非空側と同じ閉延長の法則を供給する。
`exists_residueField_closed_extension`は開初期部分の空・非空を分岐し、共通の入口を供給する。
添字の非空性・Noether性・整列性はこの一段延長の仮定ではない。

`ResidueFieldClosedStepData`には新終段の局所B代数と旧段からの写像・Kへの写像を格納する。
平坦性・極大イデアル・像・核・図式の法則は別の`IsResidueFieldClosedExtension`述語に置き、
両方の実構成から証明する。`residueFieldClosedStep`はその検証済み候補を選び、
`residueFieldClosedStep_spec`が法則を保証する。未証明の存在を仮定する入口ではない。

通常の局所B代数の図式を`LocalAlgebraDiagram`に格納し、`IsResidueFieldDiagram`で法則を検証する。
`residueFieldExtendDiagram`は証明済みの一段延長を適用し、検証済みの閉図式を供給する。
`residueFieldDiagramOfStep_restrict`と`residueFieldExtendDiagram_restrict`は、旧添字へ制限すると
環の台・環構造・代数構造・遷移・Kへの写像を含めて元の図式に等しいことを証明する。

`exists_coherent_wellFounded_history`はMathlibの`WellFounded.fix`を使う再帰の制御補題。
良い先行履歴を保つ延長の実構成を入力として受け、その法則と全段の制限一致を帰納法で証明する。
無効な先行履歴には既定値を置いて関数を全域化するが、完成した族の各段では良い分岐が選ばれる。
`exists_coherent_residueFieldHistories_of_open_gluing`はこの補題と実際の一段延長を接続する。
この制御APIの`glueOpen`は型上の明示的な仮定だが、`ResidueFieldHistoryGlue`で実構成を供給した。
`LocalAlgebraPoint`には台・環構造・局所性・B代数構造・指定終域への写像を格納する。
`castMap`はこの段全体の等式に沿って代数写像を移す。台の型だけを同一視する入口ではない。
`localAlgebraLowerGlue`は対角段と終域の履歴から図式を構成し、
`localAlgebraLowerGlue_restrict`が任意の先行履歴への制限を図式全体の等式で証明する。
この共通構成は下方に閉じた添字集合を対象にし、開初期部分と全添字集合の両方で使う。
前者には`residueFieldOpenGlue_spec`、後者には`residueFieldDiagramGlueAll_spec`を適用する。
局所性・平坦性・極大イデアル・像・自己／合成則は各先行履歴から実際に導く。

`exists_coherent_residueFieldHistories`は貼り合わせを仮定せず、整列したK上の両立履歴を構成する。
`exists_residueField_generatorDiagram`はそこから全体図式を抽出し、
`exists_flat_local_extension_of_residueField`がその直極限を取る。
この最終定理に必要なのは局所可換環B、指定体K、`Algebra (ResidueField B) K`のみ。
BからKへの代数構造と係数の塔、生成元の整列は証明内で供給し、仮定にしない。
Noether性・体拡大の有限生成性・有限性・分離性・完全性は不要で、CはB・Kと同じType u。
各x∈KはAfter xに入り、段の像の等式から全体への被覆を得る。
結論は平坦局所B代数C、m_B C=m_C、剰余体C≃Kと基底剰余体上の両立性。
Cの完備性・Noether性は結論に含まない。外部引用1の完備Noether版への接続にはR4が必要。

### R4：中間環から完備Noether平坦版へ

2026-10-13に前半を実装した。`exists_complete_local_extension_with_flat_quotients`は
B→Sの平坦局所拡大、m_B S=m_S、m_Bの有限生成性、指定剰余体の同型と両立性から、
完備局所B代数Cを構成する。m_B C=m_C、m_Cの有限生成性、指定剰余体との両立、
全てのn∈ℕについてC/m_B^n CのB/m_B^n上の平坦性を証明する。
SのNoether性は要求しない。基底BのNoether性を使ってm_Bの有限生成性を供給し、
R3を適用する最終入口は`exists_complete_local_extension_of_residueField_with_flat_quotients`。
A4を適用してCのNoether性も結論に加えた。B上の平坦性も共通の代数版を適用して証明済み。

`adicCompletion_ker_eval_eq_map`はMathlibの`pow_smul_top_eq_ker_eval`から評価の核を計算する。
`adicCompletionPowQuotientEquiv`と`adicCompletionBasePowQuotientEquiv`は冪商の同型を供給する。
後者はB/m_B^n上の代数同型であり、単なる環同型ではない。
商への基底変換はMathlibの`quotIdealMapEquivQuotTensor`を使い、
`adicCompletionBasePowQuotient_flat`で全冪商の平坦性を導く。これらに局所性・Noether性は不要。
n=0の零商も同じ型と証明で扱う。
`adicCompletionTargetResidueEquiv`とその自然性は有限生成な極大イデアルだけで構成し、
既存のNoether中間環の完備化もこの共通APIを適用するよう整理した。

残る工程は、独立に進めるA4のNoether判定と、共通の完備化の平坦性の適用。
共通工程の型・証明手順・受入条件は[統合計画§2〜§5](adic-completion-integration.md#2-統合する中心定理)に集約する。

- 可換環論側：Sの有限生成な極大イデアルに沿う完備化Cについて、A4からNoether性を導く。
  随伴次数・初期形式・近似持上げの残る接続を進め、共通平坦性の完成を待たない。
- CLMST側：Noether基底B上の任意の平坦加群の完備化の平坦性を証明し、
  拡張イデアルに沿う代数の完備化への係数制限の比較と代数版を供給する。
  中間環Sや完備化CのNoether性を平坦性証明の仮定にしない。
- 可換環論側：R3で構成したSに代数版を適用し、m_B S=m_Sを使って完備化のイデアルを合わせる。
  具体的な`C := AdicCompletion (maximalIdeal S) S`を固定して、同じCにNoether性・平坦性を接続する。
  既存の完備局所実現の存在定理はCがその完備化であるという同定を公開していないため、
  その結論のCだけを取り出して新しい一般平坦性定理を適用したとは扱わない。

全冪商の同型と平坦性は証明済みの成果として保持する。
旧案のStacks 0523による「Noether局所拡大の全冪商からの平坦性判定」は、代替経路の記録に留め、
今回の必須工程から外す。共通の完備化の平坦性と並行して独立に実装しない。
非Noether環Sの完備化写像が一般に平坦だという主張で代用しない。
採用経路は原典を組み合わせたもので、EGA 0.6.8.3.1の原証明の逐条形式化ではない。

### R5：利用先へ戻す

現行の `exists_complete_flat_local_extension` と同じ型に接続。
`Section2.lemma_2_1`、長さ・Samuel関数・次元・正則性・Torの保存は既存証明を再利用する。
基底Bの完備性、体拡大の有限性／分離性／完全性を追加しない。

## 6. W：3のWitt係数による正規化

### W0：既存Witt APIと係数写像の経路

完全体kについてDVR性、`W(k)/(p)≃k`、p進完備性は既存結果を使用する。
W(k)→Dと、D→kとの合成が定数係数写像になることは、
`WittCoefficientConstruction.lean`の `exists_wittVector_residue_lift`で証明済み。
採用した経路は次の通り。

1. `PerfectNilpotentLifting.lean`で、完全環からの写像を冪零核の全射に沿って一意に持ち上げる。
   核を消すFrobenius冪を全射に沿って降ろし、源の逆Frobeniusを合成する。
2. 各正の冪商への持ち上げの一意性から、商写像との両立を証明する。
   `IsAdicComplete.StrictMono.liftRingHom`の正の次数の逆極限で、完備環への実際の写像を得る。
   共通定理は任意の完全環を源にでき、局所性・Noether性・有限生成性を要求しない。
3. D/(p)をD上の有限加群として扱い、既存の有限加群の完備性から、
   D/(p)→kの核に沿う完備性を供給する。この適用でDのNoether性を使う。
   2を適用し、指定された剰余写像のsection k→D/(p)を構成する。
4. Mathlib `Perfection.lift`でk→PreTilt D pへ持ち上げ、
   `WittVector.map`と `WittVector.fontaineTheta`を合成する。
   θの剰余公式とsectionの等式から、D→kとの両立を計算する。

θはDのp進完備性を要求するが、perfectoid性を要求しない。
対象のp進完備性はW1の一般定理を再利用した。
Dの標数零・整域性は、この存在の構成には不要。

採用前の比較案（現在の残作業ではない）：

- **直接持ち上げ案（最初の調査対象）**：n≥1についてW(k)/p^n→D/m_D^nを両立して構成し、逆極限から環写像を得る。
  始域をW(k)に戻した両立射を使い、n=0の零商も補って `liftRingHom` に渡す。
  `Z/p^n → W(k)/p^n`の形式的滑らかさ等、必要な持ち上げ定理の正確な範囲を確定する。
  Mathlibの `IsAdicComplete.liftRingHom` は両立する射の極限に再利用できる。
- **Cohen環案**：係数Cohen環の存在・埋め込みを証明し、完全剰余体でW(k)と同定する。
  一般Cohen環の存在にRの結果を使うなら、その依存を明示する。

Witt環がDVRであることだけで、任意のDへのこの埋め込みは得られない。
一般Cohen環の存在全体を新たに実装する案は採用していない。

2026-10-13のローカルAPI確認：`IsAdicComplete.liftRingHom`は既に両立する
冪商への環写像を引数に取り、その存在を供給しない。
`Algebra.FormallySmooth.of_perfectField`（Mathlib `Smooth/Field.lean`）は
`Algebra.EssFiniteType K L`を要求するので、任意の完全剰余体にそのまま適用する経路にはならない。
`WittVector.teichmuller`は乗法的な写像であり、係数環の環写像として代用しない。
これらを代用品にせず、上記の冪零核の持ち上げとθの既存構成を使った。

### W1：係数の埋め込みと非零性

W0の実構成と下の検証を `exists_wittVector_coefficient_embedding`で合成した。
標数零の完備Noether局所環と完全剰余体について、局所的な係数埋め込みと
指定剰余写像との両立を証明済み。以下の共通定理を再利用する。

- `WittCoefficientEmbedding.lean`の `SerrePositivity.wittVector_ringHom_injective` は、
  任意のφについて、φ(p)=p_DとDの標数零からp_Dの全冪の非零性を供給し、
  DVRの単元×一様化元の冪への分解から単射性を証明した。
  終域Dの整域性・局所性・Noether性・完備性はこの証明では不要。
  共通入口 `ringHom_injective_of_dvr_uniformizer_powers` は、
  任意のDVRから任意の環への写像に同じ証明を適用する。
- `wittVector_map_maximalIdeal`はφによる源の極大イデアルの像が(p_D)であることを計算する。
  `wittVector_ringHom_isLocalHom`は、Dが局所環で剰余標数pならφが局所準同型であることを証明する。
  指定剰余写像との両立はW0の実構成で別に証明する。
- `isAdicComplete_span_residue_characteristic`は完備Noether局所環Dのp進完備性を供給する。
  Dの整域性・標数零・剰余体の完全性は不要。
  `AdicCompletenessClosedQuotient.lean`の共通定理はI≤Jについて、J進完備性と
  各I冪商のJ進分離性からI進完備性を導く。
  Noether性と有限生成性は、有限加群への適用で冪商の分離性を供給するために使う。

W0・W1・W2は完成。Witt冪級数環の(p,X)進完備性と極大イデアルの計算も完成。
W3の基底の次元・正則性と標準座標も完成。
評価の有限性・単射性と既存の公開型への接続も完成し、引用3を解消した。

### W2：pを含むパラメータ

完成。`PrescribedParameter.lean`で、Noether局所環の極大イデアル内の
指定非零因子xを先頭に置くパラメータ系を構成した。

- `ringKrullDim_quotient_eq_of_nonZeroDivisor`は、dim R=r+1ならdim R/(x)=rを証明する。
  Mathlibの非零因子による次元降下の等式を適用し、有限次元を自然数化せず等式からrを得る。
- `exists_parameters_completing_nonZeroDivisor`は、商R/(x)で既存の
  `PrimaryParameterExistence.exists_parameters_in_primary`を適用し、r個の元をRへ持ち上げる。
  商写像の局所性から持ち上げが極大イデアルに入ることを確認する。
  生成イデアルの像と核の包含を計算し、根基のcomapから
  √((x)+(y))=m_Rを導く。根基の等式を未証明入力にしていない。
- `exists_systemOfParameters_with_first_nonZeroDivisor`はこの列の先頭にxを置き、
  次元と根基の等式から `IsSystemOfParameters` を供給する。
  一般定理には整域性・正則性・Cohen–Macaulay性・完備性を要求しない。
- `radical_span_eq_maximalIdeal_of_nonZeroDivisor_of_dim_one`はr=0の空列の境界。

`MixedCharacteristicParameters.lean`の `exists_mixedCharacteristic_systemOfParameters`は
dim D=h>0に対し、pを先頭とするFin hの列とパラメータ系の条件を供給する。
整域性と標数零はp≠0から非零因子性を供給する箇所に使い、
剰余標数pはp∈m_Dを証明する箇所に使う。
`ringKrullDim_quotient_span_residue_characteristic`で商の次元も別に公開した。
完全剰余体・完備性・Witt係数写像はW2の仮定ではない。

### W3：標準基底から有限単射

A=W(k)[[X_2,…,X_h]]を**実際の環**として選び、A1でφとパラメータを評価する。
A5、A2、A3を使って正則性・完備性・有限性・単射性を供給する。
`t_0=p`、`t_i=X_i`、Aの極大イデアル生成を計算し、現行の引用へ接続する。
h=1では変数が空で、A=W(k)への同型と同じ計算になる。
`MvPowerSeries`の空変数版と係数環を定義的に同一視せず、同型を使う。

W3/A5の完備性・極大イデアルの部分は完成：

- `AdicCompletenessSup.lean`の `SerrePositivity.isAdicComplete_sup_of_complete_quotients`は、
  I進完備性と全I冪商のJ進完備性から、商でのJ進極限を両立させ、
  代表元のI進極限を取り、I+J進完備性を実構成する。
  一般定理にNoether性・局所性・有限生成性は不要。
  Noether局所環の適用では有限加群の前完備性とKrull分離性から全冪商の完備性を供給する。
- `PowerSeriesCoefficientCompleteness.lean`では、有限生成IについてMathlibの
  `mem_map_C_iff_of_fg`を再利用し、I冪の合同を全係数の合同へ移して極限を取る。
  この係数方向の完備性には変数の有限性・環のNoether性を要求しない。
- `PowerSeriesMixedCompleteness.lean`では有限変数、Noether局所係数環について、
  係数イデアルの完備性と変数イデアルの完備性を和の定理へ適用する。
  `isAdicComplete_wittPowerSeries_p_sup_variables`がWitt係数の(p,X)進完備性。
- `PowerSeriesLocalStructure.lean`では、Mathlibの変数進完備化との同型と評価の核を使い、
  全変数が定数係数の核を生成することを証明する。
  分裂する定数係数写像のcomapから極大イデアルの生成を計算し、
  `wittPowerSeries_maximalIdeal_eq`と `isAdicComplete_powerSeries_maximalIdeal`へ接続する。

次元・正則性と具体的な標準座標も完成：

- `PowerSeriesRegular.lean`では、一変数の定数係数の核を(X)と計算し、
  Xによる商を係数環へ明示的に同定する。Xの非零因子性と極大イデアルへの所属を供給して、
  Mathlibの次元降下の等式を適用する。dim R[[X]]=dim R+1。
- Mathlibの極大イデアルの生成数の上界を使い、係数環が正則局所環なら
  冪級数環の生成数がその次元以下であることから正則性を証明する。
  冪級数環の正則性を先に仮定していない。
- `finSuccEquiv`による帰納と `renameEquiv`による添字の移送で、
  任意の有限変数の次元公式と正則局所性を供給する。
  空変数は `isEmptyEquiv` を使用する。Witt係数には既存のDVRの次元1と正則性を再利用する。
- `WittNormalizationBase.lean`では、引用3と同じ変数集合
  `{i : Fin h // (i : ℕ) ≠ 0}`について標準列 `wittPowerSeriesParameter`を定義する。
  零座標のpと各非零座標のXを計算し、列の像、極大イデアル生成、次元hを証明する。
  `wittNormalizationBase_one_equiv`でh=1の基底をW(k)へ同定する。

評価・有限性・単射性と引用3の型への接続も完成：

- `FiniteNormalizationTools.lean`の `finite_quotient_of_common_residue_primary`を使う。
  Dの準素商がArtin局所環であることと指定剰余体への全射性を実際に確認し、
  既存の共通剰余体による長さの一致から係数環上の有限性を導く。
  係数環のNoether性・局所性は不要。
- `ringHom_injective_of_finite_of_equal_dimension`は有限写像の核による商を係数環とし、
  整性による次元上界と、非零核元による次元降下を合わせる。
  始域は有限Krull次元の整域。終域の整域性・局所性、始域のNoether性・正則性は不要。
- `exists_finite_wittPowerSeries_map_of_parameters`はJ=(z)を評価先の完備イデアルにする。
  J進完備性は完備Noether局所環の小さいイデアルへの完備性の移行から供給する。
  同じ評価Fについて、F(t_i)=z_i、m_Aの像がJであること、閉ファイバーの有限性、
  既存adic有限生成判定によるFの有限性、剰余写像への全射性を証明する。
- `exists_cohen_normalization_mixedCharacteristic`はW0・W2の実構成をこれへ適用し、
  dim A=dim D=hから同じFの単射性を供給する。
  Aは引用3と同じWitt冪級数環を選び、Fから代数構造を作る。
  `Inputs.cohen_normalization_mixedCharacteristic`は公開型を保持した適用へ置換済み。

混標数の分数体分離性は標数零から利用側で証明済み。
正規化の構成の前提として分離性を追加しない。

## 7. C：2の係数体・Cohen–Gabber

### C0：係数体の存在を別定理にする

`κ : k→D`で `residue D ∘ κ=id_k`を構成する。
完全剰余体での先行成果と、現行引用が要求する任意の剰余体を区別する。
任意剰余体の経路には指定したp-basisの持ち上げが現れ、Cohen–Gabberで係数体を変更する際にも使う。
通常の微分・分離性・完備化のAPIの調査結果と、p-basis／連続微分の不足は
[微分経路の台帳](cohen-gabber-differentials.md#3-確認済みapiと確認していない接続)に集約する。
存在するものとしてsectionを全定理の入力に渡しただけでは2の完了としない。

### C1：分離性を要求しない有限正規化

Dのh個のパラメータを選ぶ。κを係数写像としたA=k[[X_1,…,X_h]]からの評価を作り、
A5・A2・A3により有限単射・正則性・完備性・剰余体を証明する。
これは通常の有限正規化という独立した成果物であり、Cohen–Gabber全体の完成ではない。
h=0の入力ではDが体となり、空変数の基底と剰余体同型で扱う。

### C2：分離的選択の原証明を実装単位へ分割

採用経路はGabberの微分による原証明の整域版。
訂正版Exposé IVの係数体変更を正本とし、p-basis、連続微分、
体の微分の階数安定、独立な微分を持つ持ち上げ、パラメータ `τ_i^p*(1+f_i)`、
同じ評価の有限性・分離性の順に接続する。
具体的な型案・原典の訂正・G0〜G6の受入条件は [微分経路の計画](cohen-gabber-differentials.md) を参照。
最初の範囲は整域版であり、複数成分での同時選択は最終目標に必要になるまで追加しない。

過去に候補とした [Kurano–Shimomoto v2](https://arxiv.org/html/1510.03573v2)の
超曲面・Weierstrass・偏微分による座標変更の経路は比較資料として保持する。
両経路の完全な証明を並行実装しない。完全剰余体でもパラメータの選択は必要。
例えば完全体k上でもk[[t^p]]⊂k[[t]]は有限な純非分離拡大なので、
任意のパラメータによる有限正規化の分離性を完全性だけから推論しない。

### C3：実際の分数体写像と利用先

構成した単射A→Dから分数体の環写像を作り、`Algebra`と`IsScalarTower`を供給。
C2の分離性をこの写像について述べ、現行の引用と同じ型へ接続する。
新たな独立した分数体作用を選んで、構成した環写像との両立を省略しない。
[GenericEtale](../SerrePositivity/CommutativeAlgebra/GenericEtale.lean)は分離性から有限エタール局所化を
得る下流の証明なので再利用する。それは分離的正規化の選択を証明する代用品ではない。

## 8. 実装の順序と受入条件

| 区切り | 具体的な成果物 | 終了時に確認すること |
| --- | --- | --- |
| P0 | 下の最初の作業指示とAPI台帳、統合計画の完備化の平坦性、W0の採用経路、C2の依存表 | 存在するAPI、未確認の接続、新しい証明課題を混ぜない |
| P1 | adic評価の必要部分とA2の有限生成判定 | 対象環のNoether性・係数section・Mの有限性を不当に追加しない |
| P2 | A5の標準冪級数基底、条件付き有限正規化 | 等標数／混標数の完備イデアルと座標、h=0／h=1を確認 |
| R1/R2 | 代数的・超越的単生成拡大とそのNoether完備版 | 不分離代数拡大も含める。剰余体上の写像を確認 |
| R3/R4 | 一般拡大、A4、共通の完備化の平坦性の適用、完備Noether版 | 一般K・非完備Bのまま1に到達。宇宙・商の代数構造も確認 |
| W1/W2/W3 | 係数写像、パラメータ、条件付き有限正規化への適用 | 完全剰余体の混標数版として3に到達 |
| C0/C1 | 係数体と通常有限正規化 | 係数体を仮定する条件付き版と、存在を証明した版を区別 |
| C2/C3 | 分離的選択と分数体の両立 | 任意剰余体の整域版として2に到達 |

A4はA1の評価だけから出る定理ではなく、随伴次数環と持ち上げの別の成果物。
R1/R2はA4を待たずに進められる。WとCは共通基盤を使うが、同時に係数体／係数環の
存在全体へ着手することを初期条件にしない。
各引用の解消は、その入口と下流の公理監査で個別に判定する。

## 9. 初期の作業単位と指示（実施済みの記録）

最初に採用した単位は「前完備な環上の有限生成判定」と「既存評価APIの再利用表」。
この単位は実施済み。現在の次の作業は§12に記録する。

- 入力：A、I、A加群M。AのI進前完備性、MのI進分離性、M/IMの有限生成性。
- 出力：Mの有限生成性と、持ち上げた商生成元からの明示的な全射A^n→M。
- 証明：商生成元の選択 → 線形写像 → `isPrecomplete_pi` →
  `surjective_of_mkQ_comp_surjective` → `Module.Finite.of_surjective`。
- 仮配置：`CommutativeAlgebra/AdicFiniteGeneration.lean`。既存ファイルとの依存をP0で確認。
- 対照例：I=0、M=0、商生成元が空、有限自由加群。I=⊤なら分離性からM=0。
- 併せて：`AdicCompletionNoetherian`内の評価構成のどの行を、2・3でも再利用するかを記録。
  評価やadic完備性の同値そのものの独自再実装は行わない。

計画作成時点ではLeanファイルを追加しなかった。その後、実装の指示を受けて§12の共通APIと単生成代数の基盤を追加した。
実装時も、新しい引用・恒久的公理・結論を仮定する入力束・`native_decide`は導入しない。
既存の `Inputs` の三つの公開型は、証明の置換時まで保持する。

## 10. 実装前に確定する調査と検証

- R4：A4のNoether判定と、共通の代数版の完備化の平坦性の適用まで完成。
- W0：冪零核の持ち上げとθの経路を採用し、指定剰余写像と両立するWitt係数埋め込みまで完成。
- C0/C2：微分経路のG0で、指定p-basisの持ち上げ、連続微分のモデル、係数体変更、分離性のAPIを確定する。
- A5：冪級数の局所性・次元・正則性・(p,X)完備性は実装済み。微分基底の計算は新計画のG3へ置く。

新規定理の検証は、対象モジュールのビルド、`#print axioms`、明示的な仮定の確認、
接続時の全体ビルド・下流監査。文書だけの変更ではローカルリンク・参照名・差分を確認する。
ソース検索だけで、未発見APIが存在しないと断定しない。
外部引用の総数は他作業で変わり得るので、この計画の固定値にせず現在の監査を参照する。

## 11. 一次資料と調査範囲

- [Stacks 03C3](https://stacks.math.columbia.edu/tag/03C3)：単生成と一般体拡大の構成。本文を確認。
- EGA I, 2nd ed., 0.6.8.3・0.6.8.3.1：現行1の出典。原証明の全逐条照合は未実施。
- [Stacks 05GH](https://stacks.math.columbia.edu/tag/05GH)：FG理想とNoether商によるNoether完備化。
- [Stacks 0523](https://stacks.math.columbia.edu/tag/0523)：旧案の全冪商からの平坦性判定。統合後は代替経路の記録とし、今回の必須工程では実装しない。
- [Stacks 0315](https://stacks.math.columbia.edu/tag/0315)、[031D](https://stacks.math.columbia.edu/tag/031D)：商からの全射と有限生成判定。
- [Stacks 0323](https://stacks.math.columbia.edu/tag/0323)：係数環、正規化、標準基底。Cohen環の持ち上げを含む。
- [Kurano–Shimomoto v2](https://arxiv.org/html/1510.03573v2)：Cohen–Gabberの定理1.1、係数体の定理2.2、§3の構成を確認。全補題のLean依存表は今後作成。

原典が上の数学的主張を証明していることと、対応するLean APIの完成は別に記録する。

## 12. 実装の到達点（2026-10-13）

P1・有限生成版・R3・R4前半に加え、A4の一般Noether判定と具体的な完備化への適用まで実装した。
新しい引用・恒久的公理・入力束は追加しない。既存の三つの存在引用そのものは、この段階で置換していない。

| 成果物 | 実装と確認する範囲 |
| --- | --- |
| 商生成元の持ち上げ | [AdicFiniteGeneration](../SerrePositivity/CommutativeAlgebra/AdicFiniteGeneration.lean)：`surjective_linearCombination_of_quotient`、`exists_surjective_pi_of_finite_quotient`。有限自由加群からの全射を構成 |
| 最弱の有限生成判定 | `finite_of_quotient_of_isPrecomplete`。基底環の前完備性・加群の分離性・商の有限性だけを使う。Noether性、局所性、Mの完備性、Iの有限生成性は不要 |
| 零商の境界 | `subsingleton_of_subsingleton_quotient_of_isHausdorff`。零個の生成元を使い、基底環の前完備性も不要 |
| 代数と閉ファイバー | `finite_algebra_of_finite_quotient_map`。イデアル像と商の係数制限を線形同型で明示して有限生成判定を適用 |
| 冪級数評価 | [AdicPowerSeries](../SerrePositivity/CommutativeAlgebra/AdicPowerSeries.lean)：`adicPowerSeriesEval`、係数・変数、変数イデアルと追加係数のイデアル像を計算 |
| 有限な評価 | `adicPowerSeriesEval_finite`は明示した始域イデアルの前完備性と閉ファイバーの有限性から評価の有限性を導く。`adicPowerSeriesEval_finite_of_span`版では(X)の完備性をMathlibから供給 |
| 既存証明への適用 | [AdicCompletionNoetherian](../SerrePositivity/CommutativeAlgebra/AdicCompletionNoetherian.lean)の評価・全射の補助証明を新しいAPIの適用へ移行。公開名・仮定を保持 |
| 単生成代数の基盤 | [ResidueFieldExtensionConstruction](../SerrePositivity/CommutativeAlgebra/ResidueFieldExtensionConstruction.lean)：整拡大の閉ファイバーが体の場合の局所性・極大イデアル、モニック商の有限平坦性、剰余体上の多項式商との代数同型、既約還元からの局所性 |
| 指定体への接続 | [ResidueFieldAlgebraicExtension](../SerrePositivity/CommutativeAlgebra/ResidueFieldAlgebraicExtension.lean)：`exists_monic_residue_lift`、`liftedMinpolyClosedFibreEquiv`と根の計算。係数写像と生成元の対応を保持 |
| 代数的単生成局所拡大 | `exists_finite_free_local_extension_of_powerBasis`、`exists_finite_free_local_extension_of_integral_generator`。実際の環は持ち上げた最小多項式の商。局所写像・有限自由性・平坦性・極大イデアル等式・指定体との剰余体同型を供給。Noether性・分離性は不要 |
| 単生成の完備版 | `exists_complete_flat_local_extension_of_integral_generator`。基底がNoetherなら構成した有限自由局所拡大を完備化し、Noether性・完備性・平坦性・極大イデアル等式を確認。剰余体写像の両立と指定生成元への対応も保持 |
| 完備化の共通API | [ResidueFieldCompletion](../SerrePositivity/CommutativeAlgebra/ResidueFieldCompletion.lean)：`exists_complete_flat_local_extension_with_residue`。構成済みの平坦Noether局所拡大Sを完備化し、極大イデアル・指定剰余体・指定元を保持。基底BのNoether性は不要。R1/R2両方に適用 |
| 超越的単生成局所拡大 | [ResidueFieldTranscendentalExtension](../SerrePositivity/CommutativeAlgebra/ResidueFieldTranscendentalExtension.lean)：`residuePolynomialEval_ker`、`exists_flat_local_extension_of_transcendental_generator`。実際の環は評価の核による局所化。局所写像・平坦性・極大イデアル等式・指定体との剰余体同型・生成元の対応を供給。Noether基底なら局所化もNoether |
| 超越的単生成の完備版 | `exists_complete_flat_local_extension_of_transcendental_generator`。局所化のNoether性を確認して共通の完備化APIを適用 |
| 単生成の共通入口と係数移送 | [ResidueFieldSimpleExtension](../SerrePositivity/CommutativeAlgebra/ResidueFieldSimpleExtension.lean)：`exists_flat_local_extension_of_simple_generator`。代数性で分岐してR1/R2を適用。`adjoin_eq_top_of_scalar_equiv`で剰余体同型に沿って生成条件を移送 |
| 有限生成体拡大 | [ResidueFieldFiniteExtension](../SerrePositivity/CommutativeAlgebra/ResidueFieldFiniteExtension.lean)：`exists_noetherian_flat_local_extension_of_fg_intermediateField`、`exists_noetherian_flat_local_extension_of_fg`。共通の後続段APIを有限合成し、平坦性・Noether性・極大イデアル等式・指定体との剰余体同型を確認 |
| 有限生成の完備版 | `exists_complete_flat_local_extension_of_fg`、`exists_complete_flat_local_extension_of_finset`、`exists_complete_flat_local_extension_of_essFiniteType`。最後に一度だけ完備化。Mathlibの`Algebra.EssFiniteType`からも適用可能。空生成集合を許す |
| 一般の加群の極限 | [DirectLimitFlat](../SerrePositivity/CommutativeAlgebra/DirectLimitFlat.lean)：`directLimit_exists_representatives`、`directLimit_flat`。有限個の元の共通代表と方程式判定による平坦性。局所性・Noether性・遷移写像の単射性は不要 |
| 局所環の極限 | [DirectLimitLocalRing](../SerrePositivity/CommutativeAlgebra/DirectLimitLocalRing.lean)：`directLimit_isUnit_iff`、`directLimit_isLocalRing`、`directLimit_isLocalHom`。単元は後続段で検出できる。局所性と標準写像の局所性の仮定を分離 |
| 剰余体拡大の極限 | [ResidueFieldDirectLimit](../SerrePositivity/CommutativeAlgebra/ResidueFieldDirectLimit.lean)：`directLimit_maximalIdeal_map`、`directLimit_maximalIdeal_fg`、`directLimitResidueEquiv`と段写像・係数写像の計算。`exists_flat_local_extension_of_directed_system`が各保存定理を適用してType uの平坦局所拡大を構成。実際の図式・両立性・指定体を覆う条件は適用側で確認する |
| 後続段 | [ResidueFieldSuccessor](../SerrePositivity/CommutativeAlgebra/ResidueFieldSuccessor.lean)：`exists_residueField_successor`。旧段から一元を加え、局所性・平坦性・基底からの合成・二つの極大イデアル等式・剰余体の両立を供給。旧段のNoether性は不要 |
| 段から指定体への写像 | [ResidueFieldStageMap](../SerrePositivity/CommutativeAlgebra/ResidueFieldStageMap.lean)：`residueFieldStageMap`の核は段の極大イデアル、像は指定中間体。`residueFieldStageMap_comp_of_residue_tower`で後続段の剰余体等式を環写像の両立へ接続 |
| 体側の整列添字 | [ResidueFieldGeneratorIndex](../SerrePositivity/CommutativeAlgebra/ResidueFieldGeneratorIndex.lean)：K自身の整列、開／閉初期部分の中間体、一元追加・合併・被覆。添字の宇宙を上げない |
| 図式への終段追加 | [AlgebraSystemWithTop](../SerrePositivity/CommutativeAlgebra/AlgebraSystemWithTop.lean)：具体的な段・遷移写像の定義と自己・合成則。局所性・平坦性を段ごとに保持し、指定終域への写像の両立を供給。`algebraSystemWithTop_of_directLimit`で前段の極限からの写像へ適用 |
| 初期部分の添字 | [InitialSegmentWithTop](../SerrePositivity/CommutativeAlgebra/InitialSegmentWithTop.lean)：`initialSegmentWithTopEquiv`。開初期部分への終点追加と閉初期部分の順序同型。最小元での空初期部分にも同じ同型を適用 |
| 添字変更と制限 | [AlgebraSystemReindex](../SerrePositivity/CommutativeAlgebra/AlgebraSystemReindex.lean)：単調写像に沿う制限、恒等・合成、局所性・指定終域への両立の保存。型が添字で変わる写像の比較も供給 |
| 初期部分の延長 | [AlgebraInitialSegment](../SerrePositivity/CommutativeAlgebra/AlgebraInitialSegment.lean)：閉初期部分の段・遷移を構成し、旧段と写像の保持を証明。直極限からの写像で延長する入口に、有向図式の法則・局所性・Kへの両立を接続 |
| 一致する初期部分の貼り合わせ | [AlgebraSystemGlue](../SerrePositivity/CommutativeAlgebra/AlgebraSystemGlue.lean)：共有した環S_jと制限が一致する局所図式p_iから全体の遷移を構成。任意の初期部分への制限、自己・合成則、局所性、終域への両立を証明 |
| 貼り合わせから極限へ | [ResidueFieldInitialSegments](../SerrePositivity/CommutativeAlgebra/ResidueFieldInitialSegments.lean)：`exists_flat_local_extension_of_initialSegments`。全体の遷移・有向図式の法則を貼り合わせで供給して極限の保存APIを適用。環S_jと局所図式の制限一致は適用側で構成する |
| 中間体への終域制限と被覆 | [IntermediateFieldUnionMap](../SerrePositivity/CommutativeAlgebra/IntermediateFieldUnionMap.lean)：`algHomToIntermediateField`と両立性。各段の像と有向な中間体の合併から制限先全体の被覆を証明。局所性・Noether性・平坦性は不要 |
| Before iへの剰余体同定 | [ResidueFieldBeforeLimit](../SerrePositivity/CommutativeAlgebra/ResidueFieldBeforeLimit.lean)：`beforeLimitStageMap_cover`、`residueFieldBeforeLimitEquiv`と段・係数の計算。`exists_residueField_successor_of_beforeLimit`は極限の局所性・平坦性・極大イデアルを保存定理から供給して、一元追加とAfter iへの同定まで実際に構成 |
| 非空の開初期部分から閉初期部分へ | [ResidueFieldBeforeExtension](../SerrePositivity/CommutativeAlgebra/ResidueFieldBeforeExtension.lean)：`exists_closed_extension_of_beforeLimit`。直極限から新終段への写像を旧段へ合成し、閉初期部分の図式、局所な遷移、全段の平坦性・極大イデアル等式・Kへの像を確認。Noether性は要求しない |
| 閉延長の共通仕様 | [ResidueFieldClosedExtension](../SerrePositivity/CommutativeAlgebra/ResidueFieldClosedExtension.lean)：`IsResidueFieldClosedExtension`は具体的な対象・写像の性質。`isResidueFieldClosedExtension_of_cocone`が既存APIから閉図式の法則を導く |
| 最小元の初期段 | [ResidueFieldMinExtension](../SerrePositivity/CommutativeAlgebra/ResidueFieldMinExtension.lean)：`residueFieldMinEquiv`と`exists_closed_extension_of_min`。Bから生成元を加え、空添字の条件を証明する |
| 空・非空の統合と選択 | [ResidueFieldClosedStep](../SerrePositivity/CommutativeAlgebra/ResidueFieldClosedStep.lean)：`exists_residueField_closed_extension`と`residueFieldClosedStep`・`residueFieldClosedStep_spec`。検証済みの新終段と写像を同じ関数で選ぶ。全段の履歴一致は別途必要 |
| 図式のデータと制限 | [LocalAlgebraDiagram](../SerrePositivity/CommutativeAlgebra/LocalAlgebraDiagram.lean)：環・構造・遷移・指定終域を格納。`reindex`の恒等・合成は図式全体の等式。平坦性・像は格納しない |
| 図式としての実延長 | [ResidueFieldDiagramExtension](../SerrePositivity/CommutativeAlgebra/ResidueFieldDiagramExtension.lean)：`residueFieldExtendDiagram`・`_spec`・`_restrict`。通常の図式を延長し、法則と旧図式全体の保持を証明 |
| 履歴の整礎再帰 | [WellFoundedHistory](../SerrePositivity/CategoryTheory/WellFoundedHistory.lean)：型の異なる履歴の再帰。環や剰余体に依存しない。延長の実構成は呼出側で証明 |
| 再帰と実延長の接続 | [ResidueFieldHistory](../SerrePositivity/CommutativeAlgebra/ResidueFieldHistory.lean)：`exists_coherent_residueFieldHistories_of_open_gluing`。開図式への貼り合わせを明示的に仮定する条件付き制御入口。その仮定は次の実貼り合わせで供給 |
| 構造を含む段と移送 | [LocalAlgebraPoint](../SerrePositivity/CommutativeAlgebra/LocalAlgebraPoint.lean)：`point`・`castMap`・`ext_point`。環・代数の構造と指定終域を含む等式から写像と図式全体の一致を得る |
| 共通の実貼り合わせ | [LocalAlgebraDiagramLowerGlue](../SerrePositivity/CommutativeAlgebra/LocalAlgebraDiagramLowerGlue.lean)：`localAlgebraLowerGlue`・`_restrict`、`localAlgebraGlueAll`・`_restrict`。開初期部分と全添字集合で同じ構成を使用。剰余体・Noether性・平坦性に依存しない |
| 貼り合わせの法則の保存 | [ResidueFieldDiagramGlue](../SerrePositivity/CommutativeAlgebra/ResidueFieldDiagramGlue.lean)：`residueFieldDiagramLowerGlue_spec`・`residueFieldDiagramGlueAll_spec`。局所性・平坦性・極大イデアル・指定中間体の像と図式の法則を各履歴から供給 |
| 全段の両立履歴の実構成 | [ResidueFieldHistoryGlue](../SerrePositivity/CommutativeAlgebra/ResidueFieldHistoryGlue.lean)：`residueFieldOpenGlue`・`_spec`・`_restrict`で制御APIの仮定を解消。`exists_coherent_residueFieldHistories`は整列性以外の図式の存在・貼り合わせを仮定しない |
| 任意剰余体の完備化前の実現 | [ResidueFieldGeneralExtension](../SerrePositivity/CommutativeAlgebra/ResidueFieldGeneralExtension.lean)：`exists_residueField_generatorDiagram`と`exists_flat_local_extension_of_residueField`。一般Kへの実図式と被覆を供給し、直極限の保存APIを適用。Noether性・完備性は結論しない |
| 完備化の冪商 | [AdicCompletionQuotient](../SerrePositivity/CommutativeAlgebra/AdicCompletionQuotient.lean)：評価の核と`adicCompletionPowQuotientEquiv`。有限生成イデアルで全てのnを扱う。Noether性は不要 |
| 基底冪商上の同型 | [AdicCompletionBaseQuotient](../SerrePositivity/CommutativeAlgebra/AdicCompletionBaseQuotient.lean)：`adicCompletionBasePowQuotientEquiv`。Mathlibの標準的な商代数構造でB/I^n上の同型を構成 |
| 冪商の平坦性 | [AdicCompletionFlatQuotient](../SerrePositivity/CommutativeAlgebra/AdicCompletionFlatQuotient.lean)：`flat_quotient_of_flat_algebra`と`adicCompletionBasePowQuotient_flat`。基底変換と同型で導く。C全体の平坦性は結論しない |
| 有限生成版の剰余体の保存 | [AdicCompletionResidue](../SerrePositivity/CommutativeAlgebra/AdicCompletionResidue.lean)：`adicCompletionTargetResidueEquiv`・`_apply`・`_base_map`。SのNoether性なしで指定体へ移送。既存のNoether版もこのAPIへ移行 |
| 一般拡大の完備局所実現 | [ResidueFieldGeneralCompletion](../SerrePositivity/CommutativeAlgebra/ResidueFieldGeneralCompletion.lean)：完備局所C、有限生成なm_C、m_B C=m_C、指定剰余体の同型、全冪商の平坦性を供給。CのNoether性は証明済み。B上の平坦性も共通の代数版を適用して証明済み |
| 随伴次数環のNoether性 | [GradedReesNoetherian](../SerrePositivity/CommutativeAlgebra/GradedReesNoetherian.lean)：商のNoether性とI.FGからMathlibのRees商の定理を適用。元の環のNoether性・完備性は不要 |
| 有限な初期形式の持ち上げ | [ReesIdealLifts](../SerrePositivity/CommutativeAlgebra/ReesIdealLifts.lean)：`reesCoefficientIdeal`・`exists_finite_reesCoefficientIdeal_lifts`。Jの係数を持つ有限なRees多項式で初期形式の像を生成 |
| 次数を制御した近似の極限 | [AdicApproximationLifting](../SerrePositivity/CommutativeAlgebra/AdicApproximationLifting.lean)：一様な次数のずれcを許す近似からrangeへの所属と有限生成性を導く。全Jへの近似は`ReesCoefficientApproximation`で供給済み |
| 次数付き近似の実構成 | [ReesCoefficientApproximation](../SerrePositivity/CommutativeAlgebra/ReesCoefficientApproximation.lean)：有限なRees生成元の係数と次数の上界から、全Jの近似を供給。完備性・Noether性は仮定しない |
| A4の一般Noether判定 | [AdicNoetherianCriterion](../SerrePositivity/CommutativeAlgebra/AdicNoetherianCriterion.lean)：`isNoetherianRing_of_adicComplete_of_noetherian_quotient`・局所版・完備化版。元の環のNoether性や係数sectionを要求しない |
| 引用1の解消と利用先 | [ResidueFieldGeneralCompletion](../SerrePositivity/CommutativeAlgebra/ResidueFieldGeneralCompletion.lean)：具体的なCの公開仕様と完備Noether平坦版。`Inputs.exists_complete_flat_local_extension`と`Section2.lemma_2_1`のsorry依存を解消 |
| 完全環からの一意な持ち上げ | [PerfectNilpotentLifting](../SerrePositivity/CommutativeAlgebra/PerfectNilpotentLifting.lean)：冪零核・完備な核を越える環写像を実構成。冪商での一意性から両立性を供給。局所性・Noether性・有限性は不要 |
| Witt係数埋め込み | [WittCoefficientConstruction](../SerrePositivity/CommutativeAlgebra/WittCoefficientConstruction.lean)：`exists_wittVector_residue_lift`・`exists_wittVector_coefficient_embedding`。指定剰余写像との両立と、標数零での局所的な単射性まで証明 |
| 指定非零因子を含むパラメータ | [PrescribedParameter](../SerrePositivity/CommutativeAlgebra/PrescribedParameter.lean)：商の次元、商での選択、持ち上げ、根基の等式。整域性・完備性・正則性は不要 |
| pを先頭に置くパラメータ | [MixedCharacteristicParameters](../SerrePositivity/CommutativeAlgebra/MixedCharacteristicParameters.lean)：`exists_mixedCharacteristic_systemOfParameters`。指定非零因子の一般定理を実現し、完全剰余体・係数埋め込み・完備性を要求しない |
| 和に沿う完備性 | [AdicCompletenessSup](../SerrePositivity/CommutativeAlgebra/AdicCompletenessSup.lean)：I進完備性と各I冪商のJ進完備性からI+J進完備性。Noether局所版では有限加群の完備性を実際に供給 |
| 係数方向の冪級数完備性 | [PowerSeriesCoefficientCompleteness](../SerrePositivity/CommutativeAlgebra/PowerSeriesCoefficientCompleteness.lean)：有限生成イデアルへの係数ごとの合同と極限。変数の有限性は不要 |
| 混合イデアルの冪級数完備性 | [PowerSeriesMixedCompleteness](../SerrePositivity/CommutativeAlgebra/PowerSeriesMixedCompleteness.lean)：係数と全変数の和について完備。Witt係数の(p,X)版も証明 |
| 冪級数の局所構造 | [PowerSeriesLocalStructure](../SerrePositivity/CommutativeAlgebra/PowerSeriesLocalStructure.lean)：定数係数の核、係数極大イデアルと全変数による生成、極大イデアル進完備性 |
| 冪級数の次元と正則性 | [PowerSeriesRegular](../SerrePositivity/CommutativeAlgebra/PowerSeriesRegular.lean)：Xによる商の同型、dim R[[X]]=dim R+1、生成数による正則性、有限変数への帰納と添字の移送 |
| 引用3の具体的な基底と座標 | [WittNormalizationBase](../SerrePositivity/CommutativeAlgebra/WittNormalizationBase.lean)：零以外のFin hを変数とする基底の次元h、pと全変数の標準列、極大イデアル生成、h=1の明示的同型 |
| 閉ファイバーと単射性 | [FiniteNormalizationTools](../SerrePositivity/CommutativeAlgebra/FiniteNormalizationTools.lean)：共通剰余体と準素商から係数環上の有限性。有限写像の次元一致から単射性 |
| 混標数Cohen正規化の実構成 | [WittNormalizationConstruction](../SerrePositivity/CommutativeAlgebra/WittNormalizationConstruction.lean)：同じ評価写像に有限性・単射性・指定剰余写像への全射性を供給。引用3の既存型へ接続 |







混標数の(p,X)進完備性と極大イデアルの計算は完成。
基底の次元・正則性と標準座標は完成。
混標数の有限正規化の評価・有限性・単射性も完成。Cohen–Gabberの分離的選択は未完。
W2のpを含むパラメータは完成。
明示したHについての前完備性を受け取る共通有限性定理と、その実現条件を供給する証明を区別する。
R3は完成。R4は完備Noether局所実現・基底冪商上の同型・全冪商の平坦性まで実装済み。
CのNoether性は証明済み。B上の平坦性も共通の代数版を適用して証明済み。
Wの係数埋め込みは完成。Cohen–Gabberの分離的選択は未完。
任意の体拡大を扱う外部引用1の完備Noether平坦版も完成し、既存のInputs入口は引用非依存になった。

R4・R5は完成。`adicCompletion_local_residue_properties`で具体的なCの性質を供給し、
`exists_complete_flat_local_extension_of_noetherian_base`で同じCに共通の平坦性を適用する。
`exists_complete_flat_local_extension_of_residueField`はR3とこれを合成し、
基底の完備性や体拡大の有限性・分離性・完全性を要求せず、既存引用1と同じ型を証明する。
`Inputs.exists_complete_flat_local_extension`はその適用へ置換し、補題2.1の保存則も標準公理だけで証明した。

Noether性と平坦性を別々に存在する環へ適用したのではなく、Sの極大イデアル進完備化Cを固定して合成する。
共通の代数版の平坦性はCLMST側の実装を再利用し、ここで重複実装していない。
主定理には外部引用9件と保留K理論2件が残る。次の固有作業は引用2の係数体と分離的正規化。

検証は `lake build` と `lake env lean scripts/audit_local_algebra.lean`。
この監査は共通APIと既存Noether性の適用、R1/R2・有限生成体拡大・R3の極限段を直接importし、他作業の入力と区別する。
以下は引用1の解消時点の検証記録。その後の引用3の解消と最新監査は本節末尾を参照。
検証結果：

- 対象モジュールのビルド：具体的なCの公開仕様、同じCへの共通平坦性の適用、引用1の既存型の証明、補題2.1への接続、全て成功。新規・変更モジュールの警告・エラーなし。
- 全体 `lake build`：3964ジョブで成功。
- `audit_local_algebra.lean`：引用1の実構成を含む221宣言すべて `propext`・`Classical.choice`・`Quot.sound` のみ。`assert_no_sorry`も成功。冪商の同型と平坦性に局所性・Noether性が不要なこと、一般完備化の中間環SにNoether性を要求しないこと、全冪商の平坦性がC全体の平坦性とは別の結論であることを公開型で確認。
- `audit_axioms.lean`：引用1の入口と補題2.1の`assert_no_sorry`も成功。主定理に残るsorriesは外部引用10件と保留K理論2件で、引用1は含まれない。主定理の`sorryAx`依存そのものは残る。
- 文書検査：13個のMarkdownと293個の解説参照、失敗0。
- `git diff --check`：成功。

この区切りのコミット対象は、環の存在構成の計画整理・共通adic API・剰余体拡大・R4前半・A4の上記準備とその監査。
別作業の未コミットファイルは含めない。

### W1の検証補題（2026-10-13）

`AdicCompletenessClosedQuotient.lean`と `WittCoefficientEmbedding.lean`に上記7定理を実装した。
引用2・3の入口はまだ変更しておらず、外部引用の残数は10件、保留K理論は2件のまま。
この区切りの時点ではφの構成が未完だった。その後のW0の実装は次の記録を参照。

- 共通APIの対象ビルドは成功。新規2モジュールの警告・エラーなし。
- `audit_local_algebra.lean`の228宣言の `assert_no_sorry` が成功。
  追加7定理の公理は `propext`・`Classical.choice`・`Quot.sound` のみ。
  一般完備性の定理ではNoether性・有限生成性を要求しないこと、
  Witt写像の単射性では対象の整域性を要求しないことを公開型でも確認した。
- 全体 `lake build` は3974ジョブで成功。
- 文書検査は13個のMarkdownと293個の解説参照、失敗0。
- 主定理の公理監査は成功。外部引用10件・保留K理論2件が残ることを再確認した。
- `git diff --check` は成功。この追加分は未コミット。

### W0・W1の実構成（2026-10-13）

`PerfectNilpotentLifting.lean`の4定理で、冪零核を越える一意な持ち上げと、
その冪商での両立性からの完備環への持ち上げを証明した。
`WittCoefficientConstruction.lean`の2定理はこれとMathlibのθ写像を使って、
指定剰余写像と両立するWitt係数写像を実構成し、標数零の下で局所的な単射性まで供給する。
この段階ではDの整域性、次元、パラメータ、有限正規化を仮定しない。

- 対象ビルドは成功。新規2モジュールの警告・エラーなし。
- `audit_local_algebra.lean`の234宣言の `assert_no_sorry` が成功。
  追加6定理は `propext`・`Classical.choice`・`Quot.sound` のみに依存する。
- 引用3の入口は未置換で、W2・W3のパラメータ・標準冪級数基底・有限正規化が残る。
  引用2では任意剰余体の係数体とCohen–Gabberの分離的選択が残る。
- 全体 `lake build` は3983ジョブで成功。
  初回は並行作業によるKoszulモジュールの更新中に`.olean`未検出で失敗したが、
  現在の依存関係で再実行して成功した。
- 主定理の公理監査は成功。外部引用10件・保留K理論2件の依存は変わらない。
- 文書検査は13個のMarkdownと293個の解説参照、失敗0。
- `git diff --check` は成功。この追加分は未コミット。

### W2の指定パラメータ（2026-10-13）

`PrescribedParameter.lean`の4定理と `MixedCharacteristicParameters.lean`の2定理で、
指定非零因子による正確な次元降下、商でのパラメータ選択と持ち上げ、
根基の等式、pを先頭とするFin hのパラメータ系を証明した。
次元1では残りがFin 0の空列となることも一般定理として確認した。
商のNoether性・非自明性・局所性を実際に供給し、既存の選択定理を適用している。

- 対象ビルドは2441ジョブで成功。新規2モジュールの警告・エラーなし。
- `audit_local_algebra.lean`の240宣言の `assert_no_sorry` が成功。
  追加6定理の公理は `propext`・`Classical.choice`・`Quot.sound` のみ。
- W2は完成。引用3の入口はまだ未置換で、W3の標準冪級数基底の性質、
  有限性、単射性、引用の型への接続が残る。
- 全体 `lake build` は、並行作業中の `HomologicalAlgebra/KoszulCoordinateControl.lean`
  の108・117行の未解決ゴールで失敗。再実行でも同じ箇所で停止した。
  当該ファイルには変更を加えていない。
- 主定理の公理監査と文書の解説宣言参照の検査も、同モジュールの`.olean`不足で実行未完了。
  前回の全体成功・引用依存監査と、今回の対象ビルド・直接importによる公理監査を区別する。
- Markdown13文書のローカルリンク検査は失敗0。`git diff --check`は成功。
  この追加分は未コミット。

### W3/A5の完備性と極大イデアル（2026-10-13）

`AdicCompletenessSup`、`PowerSeriesCoefficientCompleteness`、
`PowerSeriesMixedCompleteness`、`PowerSeriesLocalStructure`に計13定理を実装した。
Witt係数の(p,X)進完備性、全変数による定数係数の核の生成、
係数極大イデアルと全変数による極大イデアルの生成を証明した。
Noether性と局所性はMathlibの既存インスタンスを使う。
基底の次元・正則性と有限正規化は未完なので、引用3の入口は置換していない。

- 対象ビルドは2365ジョブで成功。新規4モジュールの警告・エラーなし。
- 全体 `lake build` は3994ジョブで成功。前回停止したKoszul側も現在の作業ツリーで成功。
- `audit_local_algebra.lean`の253宣言の `assert_no_sorry` が成功。
  追加13定理は `propext`・`Classical.choice`・`Quot.sound` のみに依存する。
  係数方向の完備性に変数の有限性を要求しないことと、和の一般定理にNoether性を要求しないことを公開型でも確認。
- 主定理の公理監査は成功。外部引用10件・保留K理論2件は残る。
- 文書検査は13個のMarkdownと293個の解説参照、失敗0。`git diff --check`は成功。
- この追加分は未コミット。次は基底の次元・正則性を供給し、既存adic評価と有限生成判定へ接続する。

### W3/A5の次元・正則性と標準座標（2026-10-13）

`PowerSeriesRegular.lean`と `WittNormalizationBase.lean`に計21宣言を実装した。
一変数の商の同型と次元、正則性、有限変数への帰納・添字の移送、
引用3と同じ変数集合についての標準座標・極大イデアル生成・次元hを証明した。
一般の次元公式は係数環のNoether性・局所性だけを使い、正則性・整域性・完備性を要求しない。
正則性の定理は係数環の正則性を仮定し、冪級数環の正則性を生成数から証明する。
h=1の基底は明示的な同型 `wittNormalizationBase_one_equiv`でW(k)へ戻す。

Witt基底の整域性も、Mathlibの `MvPowerSeries.NoZeroDivisors`を公開importし、
既存の零因子なしのインスタンスを `NoZeroDivisors.to_isDomain` で束ねて供給する。
`isDomain_mvPowerSeries`は変数の有限性を要求しない。
次はW0の係数写像とW2のパラメータに既存のadic評価を適用し、
同じ評価写像について有限性・単射性・剰余写像の全射性を供給する。
引用3の入口の証明はまだ置換していない。

- 新規2モジュールのビルドは成功。警告・エラーなし。
- 全体 `lake build` は4000ジョブで成功。
- `audit_local_algebra.lean`の274宣言の `assert_no_sorry` が成功。
  追加21宣言は標準公理のみ。引用3の実際の基底の整域性・Noether性も `#synth` で確認した。
- 主定理の公理監査は成功。外部引用10件・保留K理論2件が残る。
- 文書検査は13個のMarkdownと293個の解説参照、失敗0。`git diff --check`は成功。
- この追加分は未コミット。

### 引用3の解消：同じ評価の有限性・単射性（2026-10-13）

`FiniteNormalizationTools.lean`と `WittNormalizationConstruction.lean`に計4定理を実装した。
W0の実際の係数写像とW2のパラメータをJ=(z)進の冪級数評価へ接続し、
F(t_i)=z_iとm_Aの像がJであることを計算した。
共通剰余体の長さの一致からW(k)上の閉ファイバーの有限性を導き、
基底の極大イデアル進完備性と既存の有限生成判定から同じFの有限性を証明した。
有限写像の次元一致の一般定理を同じFへ適用して単射性を供給し、
`Inputs.cohen_normalization_mixedCharacteristic`を公開型を保持した証明へ置換した。

この接続は、新たな未証明入力・有限性を仮定する構造体・恒久的公理を導入していない。
主定理に残る入力は外部引用9件と保留K理論2件。引用1・3は含まれない。
引用1〜3の範囲で残るのは、引用2の任意剰余体の係数体と分離的正規化の選択。

- 新規2モジュールと引用3の入口のビルドは成功。新規モジュールの警告・エラーなし。
- 全体 `lake build` は4002ジョブで成功。
- `audit_local_algebra.lean`の278宣言の `assert_no_sorry` が成功。
  追加4定理は `propext`・`Classical.choice`・`Quot.sound` のみに依存する。
- 主定理の公理監査は成功。引用3の旧入口の `assert_no_sorry`も成功。
  主定理のsorriesは外部引用9件と保留K理論2件で、引用3は含まれない。
- 文書検査は13個のMarkdownと295個の解説参照、失敗0。
- 解説TeXの引用表・件数・混標数の適用説明を更新し、PDFを再生成した。
  冒頭、補題2.2の説明、付録の引用表と構成説明の表示を確認した。
- `git diff --check`は成功。この追加分は未コミット。
