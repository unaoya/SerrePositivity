# 外部引用1〜3：剰余体拡大と有限正規化の詳細計画

作成・更新：2026-10-13。状態：P1・R3・R4前半と、A4の随伴次数のNoether性／有限な初期形式の持ち上げ／近似の極限まで実装済み。
現在の到達点と検証結果は§12。次は有限なRees生成元から次数を制御した近似を供給し、A4のNoether判定を完成する。
未実装のステートメント案は計画として扱い、存在引用1〜3の一般形は未解消。

対象は会話の外部引用番号1〜3。論文の節番号ではない。
4〜5は [交点重複度の計画](intersection-inputs-4-5.md)、6は [Frobeniusの計画](frobenius-homology.md)で扱う。
この計画はそれらの実装順や、進行中のCLMST・K理論の実装を変更しない。

## 1. 最終目標と二種類の区切り

| 番号 | 現行入口 | 全体の完了条件 |
| --- | --- | --- |
| 1 | `Inputs.exists_complete_flat_local_extension` | 任意のNoether局所環Bと任意の剰余体拡大Kに、同じ宇宙の完備Noether平坦局所拡大B′を構成。極大イデアルの拡張と、剰余体同型のBの剰余体上の両立まで証明 |
| 2 | `Inputs.cohen_gabber_normalization` | 完備Noether局所整域D、標数p、任意の剰余体について、標準座標付きの正則冪級数基底と有限単射を構成。分数体拡大の分離性まで証明 |
| 3 | `Inputs.cohen_normalization_mixedCharacteristic` | 標数零・剰余標数p・完全剰余体の完備Noether局所整域Dに、W(k)を係数とする標準冪級数基底と有限単射を構成。pと残りの変数による極大イデアル生成まで証明 |

所在は [ResidueFieldExtension](../SerrePositivity/Inputs/ResidueFieldExtension.lean)、
[CohenNormalization](../SerrePositivity/Inputs/CohenNormalization.lean)。
現在の三つの入口には直接 `sorry` がある。この作業では新しい引用をコードへ追加しない。

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

Rの一般拡大・完備化は、一般Cohen環の構成を採用する場合にWとも共有する。
Witt環から直接持ち上げる場合の依存は、W0で別に確定する。
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
| Weierstrass | Mathlib `PowerSeries/WeierstrassPreparation`に定理と分解の計算式がある | 2の原証明で使う係数環・変数変更に適用できる仮定を確認 |

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

この近似条件は、有限個の初期形式が各次数を生成することから供給すべき入力であり、
現時点で全てのJについて供給したわけではない。A4そのものは未証明。
次は、有限個のz_iの係数を元のJの有限生成元候補に採用し、次数の上界cを取る。
Mathlibの`mem_map_algebraMap_reesAlgebra_iff`により、商での生成の誤差が
I^(n+1)へ入ることを読み取る。Rees係数の冪への所属から係数側のI^(n-c)を確認し、
上の持ち上げを各Jへ適用して全イデアルの有限生成性を証明する。


### A5：標準冪級数基底の性質

別々の定理として、k[[X]]とW(k)[[X]]の局所性、剰余体、極大イデアル、
指定イデアルについての完備性、次元、正則性を供給する。

- 体係数：極大イデアルは(X)、次元は変数の個数。
- Witt係数：極大イデアルは(p,X)、次元は変数の個数+1。
- Witt係数のX進完備性だけで(p,X)進完備性を供給したとはしない。
- 正則性を先に仮定して、生成元数＝次元からその正則性を結論してしまわない。

必要な性質は [Stacks 0323 Remark 10.160.9](https://stacks.math.columbia.edu/tag/0323)に対応する。
Mathlibの局所性・次元・regular local APIの正確な不足はP0で確認する。

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
この段階ではCのNoether性とB上の平坦性はまだ結論していない。

`adicCompletion_ker_eval_eq_map`はMathlibの`pow_smul_top_eq_ker_eval`から評価の核を計算する。
`adicCompletionPowQuotientEquiv`と`adicCompletionBasePowQuotientEquiv`は冪商の同型を供給する。
後者はB/m_B^n上の代数同型であり、単なる環同型ではない。
商への基底変換はMathlibの`quotIdealMapEquivQuotTensor`を使い、
`adicCompletionBasePowQuotient_flat`で全冪商の平坦性を導く。これらに局所性・Noether性は不要。
n=0の零商も同じ型と証明で扱う。
`adicCompletionTargetResidueEquiv`とその自然性は有限生成な極大イデアルだけで構成し、
既存のNoether中間環の完備化もこの共通APIを適用するよう整理した。

以下は残る二つの判定までを含む証明経路。

Sのn進完備化をB′とする。nは有限生成なので、MathlibのFG版からB′の完備性・局所性・
極大イデアル・剰余体を確認する。A4からB′のNoether性を得る。

平坦性は、S→B′が非Noether環の完備化だから平坦だ、としてはいけない。
各r≥1について `B′/m_B^r B′ ≃ S/m_B^r S`を**B/m_B^r上で**構成し、
SのB上の平坦性から右辺の平坦性を得る。
その後 [Stacks 0523](https://stacks.math.columbia.edu/tag/0523)の判定に、
基底B、Noether局所環B′、B′上の有限加群M=B′を適用し、B→B′の平坦性を導く。
この判定はArtin–Reesを用いる。固定Mathlibの対応APIと不足補題はR0で確認する。

商同型とその上の平坦性は実装済み。Noether判定と平坦性判定は未証明。
今回の固定MathlibのNoetherian／Flat／AdicCompletionを調べた範囲では、
この形の二つの判定を直接適用できる入口はまだ確認できていない。
原典を組み合わせた証明経路であり、EGA 0.6.8.3.1の原証明の逐条形式化ではない。

### R5：利用先へ戻す

現行の `exists_complete_flat_local_extension` と同じ型に接続。
`Section2.lemma_2_1`、長さ・Samuel関数・次元・正則性・Torの保存は既存証明を再利用する。
基底Bの完備性、体拡大の有限性／分離性／完全性を追加しない。

## 6. W：3のWitt係数による正規化

### W0：既存Witt APIと係数写像の経路

完全体kについてDVR性、`W(k)/(p)≃k`、p進完備性は既存結果を使用する。
残る核心はW(k)→Dで、D→kとの合成が定数係数写像になること。
二案をP0で比較する。

- **直接持ち上げ案（最初の調査対象）**：n≥1についてW(k)/p^n→D/m_D^nを両立して構成し、逆極限から環写像を得る。
  始域をW(k)に戻した両立射を使い、n=0の零商も補って `liftRingHom` に渡す。
  `Z/p^n → W(k)/p^n`の形式的滑らかさ等、必要な持ち上げ定理の正確な範囲を確定する。
  Mathlibの `IsAdicComplete.liftRingHom` は両立する射の極限に再利用できる。
- **Cohen環案**：係数Cohen環の存在・埋め込みを証明し、完全剰余体でW(k)と同定する。
  一般Cohen環の存在にRの結果を使うなら、その依存を明示する。

Witt環がDVRであることだけで、任意のDへのこの埋め込みは得られない。
両案を同時に全面実装しない。必要な持ち上げ／同定のAPIを調べて採用案を決める。

### W1：係数の埋め込みと非零性

φ : W(k)→Dを構成し、定数係数写像との剰余体上の可換性を証明する。
φ(p)=p_D、Dが標数零なのでp_D≠0。
W(k)の非零元がpの冪×単元であることからφの単射性を導く。
この過程でDの整域性・標数零を使う場所を明示する。

### W2：pを含むパラメータ

dim D=h>0。D/pDの次元h−1を証明し、そこからh−1個のパラメータを選ぶ。
pが非零因子で極大イデアルに入ること、商の次元、持ち上げ後の根基がm_Dになることを確認する。
パラメータの存在・次元に必要な一般論は既存 `PrimaryParameterExistence`・Mathlibと照合する。

### W3：標準基底から有限単射

A=W(k)[[X_2,…,X_h]]を**実際の環**として選び、A1でφとパラメータを評価する。
A5、A2、A3を使って正則性・完備性・有限性・単射性を供給する。
`t_0=p`、`t_i=X_i`、Aの極大イデアル生成を計算し、現行の引用へ接続する。
h=1では変数が空で、A=W(k)への同型と同じ計算になる。
`MvPowerSeries`の空変数版と係数環を定義的に同一視せず、同型を使う。

混標数の分数体分離性は標数零から利用側で証明済み。
正規化の構成の前提として分離性を追加しない。

## 7. C：2の係数体・Cohen–Gabber

### C0：係数体の存在を別定理にする

`κ : k→D`で `residue D ∘ κ=id_k`を構成する。
完全剰余体での先行成果と、現行引用が要求する任意の剰余体を区別する。
任意剰余体の経路には指定したp-basisの持ち上げが現れ、Cohen–Gabberで係数体を変更する際にも使う。
`k`の形式的滑らかさ、持ち上げ、p-basisの正確なMathlib APIは未調査。
存在するものとしてsectionを全定理の入力に渡しただけでは2の完了としない。

### C1：分離性を要求しない有限正規化

Dのh個のパラメータを選ぶ。κを係数写像としたA=k[[X_1,…,X_h]]からの評価を作り、
A5・A2・A3により有限単射・正則性・完備性・剰余体を証明する。
これは通常の有限正規化という独立した成果物であり、Cohen–Gabber全体の完成ではない。
h=0の入力ではDが体となり、空変数の基底と剰余体同型で扱う。

### C2：分離的選択の原証明を実装単位へ分割

採用候補は [Kurano–Shimomoto v2](https://arxiv.org/html/1510.03573v2)の整域版。
原証明の主張を現行の整域に特殊化してから、次を依存表にする。

1. 冪級数のWeierstrass分解、有限性、超曲面表示。
2. 有限個の素イデアルを避けるパラメータ・座標変更と、パラメータ条件の保存。
3. 偏微分が非零になる座標変更と、有限分数体拡大の分離性判定。
4. 非完全剰余体では、p-basisの指定持ち上げと係数体の変更。
5. 超曲面の場合から生成元の余剰個数への帰納と、分数体の塔における分離性の合成。

これらはすべて必要性と正確な仮定を原典と照合する。非整域の場合の最小成分への還元は、
現行の整域版に不要なら初期対象に含めない。
完全剰余体版では4を簡略化できる可能性があるが、座標の選択は依然必要。
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
| P0 | 下の最初の作業指示とAPI台帳、R4の平坦性判定、W0の採用経路、C2の依存表 | 存在するAPI、未確認の接続、新しい証明課題を混ぜない |
| P1 | adic評価の必要部分とA2の有限生成判定 | 対象環のNoether性・係数section・Mの有限性を不当に追加しない |
| P2 | A5の標準冪級数基底、条件付き有限正規化 | 等標数／混標数の完備イデアルと座標、h=0／h=1を確認 |
| R1/R2 | 代数的・超越的単生成拡大とそのNoether完備版 | 不分離代数拡大も含める。剰余体上の写像を確認 |
| R3/R4 | 一般拡大、A4、全冪の平坦性判定、完備Noether版 | 一般K・非完備Bのまま1に到達。宇宙・商の代数構造も確認 |
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

- R4：FG理想の完備化の全冪商同型は実装済み。残る調査は0523の平坦性判定のMathlib接続と、商からのNoether判定の証明。
- W0：W(k)/p^nの持ち上げか、Cohen環の存在・同定か。実際の補題と依存で決める。
- C0/C2：指定p-basisの持ち上げ、係数体変更、Weierstrass・偏微分・分離性のAPI。
- A5：Noether性は既存。局所性・次元・正則性・(p,X)完備性の正確な不足を調べる。

新規定理の検証は、対象モジュールのビルド、`#print axioms`、明示的な仮定の確認、
接続時の全体ビルド・下流監査。文書だけの変更ではローカルリンク・参照名・差分を確認する。
ソース検索だけで、未発見APIが存在しないと断定しない。
外部引用の総数は他作業で変わり得るので、この計画の固定値にせず現在の監査を参照する。

## 11. 一次資料と調査範囲

- [Stacks 03C3](https://stacks.math.columbia.edu/tag/03C3)：単生成と一般体拡大の構成。本文を確認。
- EGA I, 2nd ed., 0.6.8.3・0.6.8.3.1：現行1の出典。原証明の全逐条照合は未実施。
- [Stacks 05GH](https://stacks.math.columbia.edu/tag/05GH)：FG理想とNoether商によるNoether完備化。
- [Stacks 0523](https://stacks.math.columbia.edu/tag/0523)：Noetherな基底・終域、有限終域加群、全冪の平坦性による判定。
- [Stacks 0315](https://stacks.math.columbia.edu/tag/0315)、[031D](https://stacks.math.columbia.edu/tag/031D)：商からの全射と有限生成判定。
- [Stacks 0323](https://stacks.math.columbia.edu/tag/0323)：係数環、正規化、標準基底。Cohen環の持ち上げを含む。
- [Kurano–Shimomoto v2](https://arxiv.org/html/1510.03573v2)：Cohen–Gabberの定理1.1、係数体の定理2.2、§3の構成を確認。全補題のLean依存表は今後作成。

原典が上の数学的主張を証明していることと、対応するLean APIの完成は別に記録する。

## 12. 実装の到達点（2026-10-13）

P1・有限生成版・R3・R4前半に加え、A4の随伴次数・有限な初期形式・近似の極限まで実装した。
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
| 一般拡大の完備局所実現 | [ResidueFieldGeneralCompletion](../SerrePositivity/CommutativeAlgebra/ResidueFieldGeneralCompletion.lean)：完備局所C、有限生成なm_C、m_B C=m_C、指定剰余体の同型、全冪商の平坦性を供給。CのNoether性・B上の平坦性は未証明 |
| 随伴次数環のNoether性 | [GradedReesNoetherian](../SerrePositivity/CommutativeAlgebra/GradedReesNoetherian.lean)：商のNoether性とI.FGからMathlibのRees商の定理を適用。元の環のNoether性・完備性は不要 |
| 有限な初期形式の持ち上げ | [ReesIdealLifts](../SerrePositivity/CommutativeAlgebra/ReesIdealLifts.lean)：`reesCoefficientIdeal`・`exists_finite_reesCoefficientIdeal_lifts`。Jの係数を持つ有限なRees多項式で初期形式の像を生成 |
| 次数を制御した近似の極限 | [AdicApproximationLifting](../SerrePositivity/CommutativeAlgebra/AdicApproximationLifting.lean)：一様な次数のずれcを許す近似からrangeへの所属と有限生成性を導く。全Jへの近似の供給は未完 |





混標数の(p,X)進完備性、係数環の埋め込み、正規化の単射性・分離的選択は未完。
明示したHについての前完備性を受け取る共通有限性定理と、その実現条件を供給する証明を区別する。
R3は完成。R4は完備局所実現・基底冪商上の同型・全冪商の平坦性まで実装済み。
CのNoether性・B上の平坦性は未証明。Wの係数埋め込み・Cohen–Gabberの選択は未着手。
この完成は、任意の体拡大を扱う外部引用1の完備Noether版の完成を意味しない。

R4の前半は実装済み。次は、以下の二つの判定を証明する。

1. 有限生成な極大イデアルmを持つm進完備局所環CのNoether性。
   局所版の共通ステートメントは`[IsLocalRing C] [IsAdicComplete (maximalIdeal C) C]`
   と`(maximalIdeal C).FG`から`IsNoetherianRing C`を導く形。剰余体は既に体なのでNoether。
   現在の`isNoetherianRing_of_adicComplete_of_surjective_quotient`は、Noetherな係数環から
   C/mへの全射を要求する。一般拡大KではB→Kは全射とは限らず、K→Cの係数sectionも
   まだ供給していないため、その定理の直接適用でA4を済ませてはいけない。
   随伴次数環のNoether性、Jの初期形式の有限な持ち上げ、次数を制御した近似からの
   有限生成への移行は実装済み。残るのはRees生成元の次数の上界から、各Jでその近似を供給する接続。
2. Noether局所基底BとNoether局所拡大Cについて、全冪商の平坦性からB→Cの平坦性。
   全冪商の平坦性は実構成から供給済み。判定に必要な有限性・分離性・局所性の条件を
   確定し、MathlibのArtin–Rees・平坦性の判定APIとの接続を調べる。
3. この二つを適用して完備Noether平坦版を得た後、外部引用1の既存型に戻し、利用先を再監査する。

非Noether環Sの完備化写像が一般に平坦だという主張で代用しない。
新しい完備局所実現の定理の結論にはCのNoether性・B上の平坦性をまだ含めていない。

検証は `lake build` と `lake env lean scripts/audit_local_algebra.lean`。
この監査は共通APIと既存Noether性の適用、R1/R2・有限生成体拡大・R3の極限段を直接importし、他作業の入力と区別する。
検証結果：

- 対象モジュールのビルド：随伴次数のNoether性、Jの初期形式の有限な持ち上げ、ずれを許す近似の極限と有限生成への移行、全て成功。新規・変更モジュールの警告・エラーなし。
- 全体 `lake build`：3957ジョブで成功。
- `audit_local_algebra.lean`：A4の上記準備を含む211宣言すべて `propext`・`Classical.choice`・`Quot.sound` のみ。`assert_no_sorry`も成功。冪商の同型と平坦性に局所性・Noether性が不要なこと、一般完備化の中間環SにNoether性を要求しないこと、全冪商の平坦性がC全体の平坦性とは別の結論であることを公開型で確認。
- `audit_axioms.lean`：既存の監査を再実行して成功。主定理には既存入力に由来する `sorryAx` が残る。
- 文書検査：13個のMarkdownと293個の解説参照、失敗0。
- `git diff --check`：成功。

この区切りのコミット対象は、環の存在構成の計画整理・共通adic API・剰余体拡大・R4前半・A4の上記準備とその監査。
別作業の未コミットファイルは含めない。
