# 形式化計画

2026-10-07 作成、2026-10-12 更新。対象は Theorem 1.1（`notes/MEMO.md`）。
環境は Lean `v4.35.0-rc4`、Mathlib `e6bbacd0`（2026-10-07）。

このファイルには、現在の方針・規約・設計判断と、帰着（M1）の到達点を残す。
実装済みの作業の実施記録、旧ファイル構成、旧マイルストーンの作業項目（旧 §0、§2、§3、§7、§10、§13〜§17 など）は
2026-10-10 に削除した。経緯は git の履歴にある。外部から節番号で参照されているので、節番号は振り直していない。
各トラックの詳細は次のノートにある。

- §2：[section-2.md](section-2.md)（主張と文献の照合）、[section-2-plan.md](section-2-plan.md)（計画と実施記録）
- §3：[lemma-3-4.md](lemma-3-4.md)、[lemma-3-5.md](lemma-3-5.md)
- §4：[section-4.md](section-4.md)、[section-4-plan.md](section-4-plan.md)、[section-4-devissage.md](section-4-devissage.md)
- §5：[step-4-overview.md](step-4-overview.md)（§5.2–5.5 の見取り図）、[lemma-5-2.md](lemma-5-2.md)、
  [lemma-5-3.md](lemma-5-3.md)、[lemma-5-4.md](lemma-5-4.md)
- Mathlib との対応：[mathlib-review-2026-10-10.md](mathlib-review-2026-10-10.md)

## 現在の優先順位（2026-10-12 更新）

ユーザーの最新の指示により、次の順序で未証明箇所を整理する。

1. **補題2.1・2.2の引用と証明の境界。** 剰余体拡大、Cohen–Gabber、Cohen の
   正規化を出典と主張の明確な引用に分ける。長さ・Tor・正則性の保存、
   有限拡大へのパラメータの移送、標数による分岐と分離性の確認は証明する。
2. **今回必要な標準可換環論。** 定義に戻り、Hilbert–Samuel 理論・重複度公式・
   正則パラメータと非混合性のうち本論文で使う範囲を順に証明する。
   別プロジェクトの完成は待たず、一般論全体への拡張は目的としない。
3. **定理3.1・補題4.6の K 理論は後回し。** 既存の入力を保持し、今回の作業で
   dg 表示・係数付き K 群の降下に着手しない。

**今回の到達点。** 作業1は完了した。補題2.1・2.2の公開ステートメントを維持し、
それぞれの本体を証明へ置き換えた。引用は `Inputs/ResidueFieldExtension.lean` と
`Inputs/CohenNormalization.lean` の三つの定理に分け、出典と範囲を明記した。
特に Cohen の引用は「係数環だけの存在」ではなく、文献で証明された有限正規化の形である。
冪級数環の正則性・完備性・Witt 環との同定は引用側に含む。
詳細は [補題2.1・2.2の引用境界](section-2.md) を参照。

作業2では、Samuel 関数の指数についての単調性・イデアルについての反単調性と、
`P_(I^v)(X) = P_I(vX)` を定義から証明した。イデアル自体の冪の公式
`e(I^v,M) = v^(dim M)e(I,M)` は多項式性から導き、次元定理を使わない。
重複度の正値性は、多項式性・次元定理からの証明へ置き換えた。
Koszul Euler 数の係数制限も証明し、未証明なのは同じ環上の Koszul 重複度公式であると明示した。

今回対象にした標準可換環論の六つの主張はすべて証明済み。外部の深い引用と、後回しにした K 理論の未証明箇所は引き続き別に保持する。

| 順序 | 主張 | 必要な範囲での証明 |
| --- | --- | --- |
| 1（完了） | `exists_isSamuelPoly`：Samuel 関数の多項式性 | Hilbert–Serre の数値版を証明し、随伴次数加群へ適用して有理型級数と次数 `≤ s` の Samuel 多項式を構成した。直接の `sorry` を除去済み |
| 2（完了） | `natDegree_poly_eq_dim`：次数と環の次元の一致 | 次元個のパラメータ系から上界、Artin–Rees と素イデアル鎖への帰納法から下界を証明した。元の名前・仮定・結論を維持し、直接の `sorry` を除去済み |
| 3（完了） | `isWeaklyRegular_of_span_eq_maximalIdeal`：正則局所環の正則パラメータ | Samuel 次元定理で随伴次数環の多項式表示の単射性を得て、Krull 共通部分と商への帰納法から正則列を証明した。既存の `sorry` を除去済み |
| 4（完了） | `ringKrullDim_quotient_add_length_of_mem_associatedPrimes`：正則列で割った環の非混合性 | 随伴素イデアルへの深さ上界、商の深さ下界、正則列商の次元公式を接続して証明した。既存の `sorry` を除去済み |
| 5（完了） | `multiplicity_eq_chiOrd_koszul`：Koszul 重複度公式 | Rees Koszul ホモロジーの高次消滅、実際の adic tail の完全性、有限長商の Euler–Poincaré 公式、Samuel 多項式の高階差分を接続して証明した |
| 6（完了） | `multiplicity_parameter_pow`：パラメータ各成分の冪 | 鳩ノ巣評価による理想の冪包含と Samuel 多項式の最高次係数の比較から独立に証明した。イデアル自体の冪の公式とは区別する |

標準可換環論の六つの主張を証明し、直接の `sorry` は15箇所になった。
内訳は外部引用13、後回しの K 理論2。今回対象にした標準可換環論には残らない。
引用からの接続が証明済みでも、引用先と後回しの K 理論への依存は残る。

以前の検証（引用境界と標準可換環論への着手）：全体の `lake build` は3707ジョブで成功。新規・変更20宣言と主定理・核心定理の
計22宣言を公理監査し、11宣言は標準公理のみ、11宣言は明示した未証明入力に由来する
`sorryAx` に依存する。その他の公理はなく、`git diff --check` も通過した。

### 標準可換環論の最後の二つ：証明完了

`MultiplicityFormulas.lean` の二つの公開名・仮定・結論を維持して、既存の `sorry` を
証明へ置き換えた。新しい未証明入力・公理・入力を束ねる構造体は追加していない。

**パラメータ成分ごとの冪。** `ParameterPowerMultiplicity.lean` で
`I=(z_i)`、`J=(z_i^v)` の間の `J^n≤I^(vn)` と
`I^(vn+h(v−1))≤J^n` を単項式の指数の鳩ノ巣評価で証明する。
Samuel 関数を両側から抑え、最高次係数を比較して `e(J)=v^h e(I)` を得る。
Koszul 重複度公式には依存しない。

**Koszul 重複度公式。** 今回必要な係数加群 `M=R` を、次の証明済みの接続で扱う。

- `KoszulReesFinite.lean`：Rees 加群の多項式作用・有限生成性。変数の冪で消える
  有限多項式加群は係数環上有限生成なので、変数列の Koszul ホモロジーも係数環上有限生成。
- `GradedKoszulHomology.lean`・`ReesModuleGrading.lean`・`GradedKoszul.lean`・
  `GradedKoszulVanishing.lean`・`GradedReesKoszulVanishing.lean`：各項とホモロジーの
  次数分解を構成。有限生成性から高次数のホモロジー消滅を得て、同次サイクルの
  原始元を一つ低い係数次数で選び、全 cochain 次数に共通する境界を供給する。
- `GradedKoszulEvaluation.lean`・`ReesKoszulEvaluation.lean`：`t=1` の評価による複体射を構成。
  各項の係数次数 `k` の像が `I^k` 倍に一致し、その次数成分上で評価が単射であることを証明。
- `ModuleSubcomplex.lean`・`AdicFilteredComplex.lean`・`GradedAdicExactness.lean`・
  `ReesKoszulAcyclic.lean`：実際の Koszul 複体の `F_n K^q=I^max(n+q,0)K^q` を構成。
  次数付きのサイクル・境界の持ち上げから十分先の尾部の完全性を得る。
  尾部・元の複体・商の短完全列から、商への射影が quasi-isomorphism であることを示す。
- `FiniteLengthComplexEuler.lean`・`AdicModuleProduct.lean`・`AdicTermEuler.lean`・
  `AdicEulerComparison.lean`：有限長商の Euler–Poincaré 公式と、錐の項の直積表示を使い、
  項の交代和を `E(n)−E(n−1)` の再帰へ移す。
- `PolynomialFiniteDifference.lean`・`KoszulAdicEuler.lean`・`KoszulMultiplicityProof.lean`：
  `h` 階後退差分が `h! × coeff_h` になること、Samuel 次数＝次元を用い、
  実際の Koszul Euler 数を重複度へ同定する。空列・次数零も処理する。

最終の公開公式では、次数付き評価・消滅・尾部の完全性を新しい仮定にはしていない。
同じ環上の公式、係数制限、正則基底上の階数公式、パラメータの冪の Euler 公式まで
証明済みの一般論に接続した。外部の深い引用と K 理論の保留範囲は別に残る。

検証：全体の `lake build` は3790ジョブで成功。新規165宣言と既存14宣言の計179宣言を
公理監査し、175宣言は標準公理のみ。今回対象にした六つの標準定理、係数制限による
重複度公式、正則基底上の階数公式、Koszul の冪の Euler 公式、条件付き正規化長さの極限に
`sorryAx` の依存はない。`firstComparison`・定理2.5・主定理・核心定理の4宣言には
意図して保持した外部引用または K 理論からの依存が残る。その他の公理はなく、
新しい `sorry` は追加せず総数は15。`git diff --check` も通過。

### 正則列商の非混合性：証明完了

`Inputs/Unmixedness.lean` の公開名・仮定・結論を維持して、既存の `sorry` を
`RegularSequenceUnmixedness.dimension_eq` の適用へ置き換えた。一般の Cohen–Macaulay
理論や正則局所環の局所化の定理を新しい入力にはしていない。

- `AssociatedPrimeQuotient.lean`：Krull 共通部分から、正則元 `x` に対して
  `a=x^n b` かつ `b∉xM` となる代表元を選ぶ。正則性で零化イデアルを保存し、
  商の非零元の零化イデアルを含む随伴素イデアルを選んで `p<q` を導く。
- `AssociatedPrimeDepth.lean`：正則列の長さへの帰納法と素商の次元低下を接続し、
  各随伴素イデアルについて `depth M≤dim(R/p)` を証明する。
- `RegularQuotientDepth.lean`：正則元の短完全列の深さ補題から
  `depth M≤depth(M/rsM)+|rs|` を導く。正則局所環の最小正則生成列を使い、
  `dim R≤depth(R/(rs))+|rs|` を得る。
- `AssociatedPrimeDimension.lean` と `RegularSequenceUnmixedness.lean`：
  随伴素イデアルからの単射 `R/p→R/(rs)` により反対側の次元上界を得る。
  商に随伴素イデアルがあれば零商を排除でき、弱正則列を正則列へ変換できる。
  Mathlib の正則列商の次元公式と上下界を組み合わせて等式にする。

この結果を使う素イデアル回避による正則パラメータの選択と、本文の有限拡大への
パラメータの移送も、非混合性の未証明入力への依存がなくなる。

検証：全体の `lake build` は3770ジョブで成功。新規18宣言と既存7宣言の計25宣言を
公理監査し、22宣言は標準公理のみ。非混合性・正則パラメータの選択・有限拡大への
パラメータの移送に `sorryAx` の依存はない。`firstComparison`・主定理・核心定理の
3宣言には既存入力からの依存が残る。その他の公理はなく、直接の `sorry` は17箇所。
`git diff --check` も通過した。

### 正則パラメータの正則性：証明完了

正則局所環の極大イデアルを次元と同数の元で生成する列が弱正則列になることを、
新しい未証明入力なしで証明した。`Inputs/RegularParameters.lean` の既存の公開名・型を保ち、
`isWeaklyRegular_of_span_eq_maximalIdeal` を `RegularParametersProof.lean` の適用へ置き換えた。

- `GradedReesSelf.lean` と `GradedPresentationMap.lean` で、自己随伴次数加群と
  随伴次数環を同定し、多項式表示の全射性・次数適合と係数制限による長さの一致を証明。
- `MonomialCounting.lean` と `PolynomialHilbertSeries.lean` で単項式を多重集合として数え、
  自由多項式環の各次数の長さと Hilbert 級数 `(1-X)^(-s)` を計算。
- `GradedShiftMap.lean`・`GradedCumulativeGrowth.lean`・`GradedSurjection.lean`・
  `HomogeneousRelationGrowth.lean` で、任意の同次次数の単射による商の級数と
  累積成長の次数低下を証明。線形写像の核はイデアルとは限らないので、
  関係式の全ての倍数が消えることを明示し、実際の環準同型に適用する。
- `SamuelCumulative.lean` で累積長さを Samuel 関数と同定。`RegularGradedPresentation.lean` は
  表示の非零同次関係があれば次数が生成元数より下がることを示し、次数＝次元と矛盾させる。
- `GradedRegularLift.lean` と `RegularFromGradedPresentation.lean` で、変数の正則性を
  各次数の単射性へ移し、Krull の共通部分定理から元の環上の正則性を導く。
- `RegularLocalQuotient.lean` と `RegularParametersProof.lean` で、先頭で割った商の
  次元・正則局所性・残りの生成元を確認し、環を一般化した列の長さへの帰納法を行う。
  長さ零は空列として処理する。

旧入力から導いていた正則局所環の整域性・正規性・有界有限自由分解・
Koszul Euler 数＝階数も、正則パラメータの未証明入力への依存がなくなる。
コード内の依存関係の説明も証明済みの状態へ更新した。

検証：全体の `lake build` は3745ジョブで成功。新規82宣言と既存8宣言の計90宣言を
公理監査し、88宣言は標準公理のみ。正則パラメータ・整域性・正規性・有限自由分解・
Koszul Euler 数＝階数に `sorryAx` の依存はない。主定理・核心定理の2宣言には既存入力からの
依存が残る。その他の公理はなく、直接の `sorry` は18箇所、`git diff --check` も通過。

### Samuel 多項式の次数＝Krull 次元：証明完了

三つのサブエージェントで補助層を並行実装し、`HilbertSamuelDimension.lean` で統合した。
一般の加群の支持次元との一致まで拡張せず、今回必要な環自身の場合を証明した。

- `PolynomialGrowth.lean`：十分大きい自然数での評価の比較から次数を比較する。
  後退差分 `P(X)-P(X-c)` の次数が下がることも証明した。
- `SamuelGrowthComparison.lean`：理想の冪包含から添字を線形変更した長さの比較を得て、
  極大イデアルを根基にもつ理想間の次数一致を証明した。次元定理は使わない。
- `PrimaryParameterExistence.lean`：Mathlib の高さ定理を用い、準素イデアル内に
  次元個の元で生成される準素イデアルを選ぶ。生成数による次数上限へ接続した。
- `ArtinReesGrowth.lean`・`SamuelRegularGrowth.lean`：有限加群の正則元 `x` について、
  `σ_(M/xM)(n)+σ_M(n-c)≤σ_M(n)` を Artin–Rees から導いた。
  非零有限加群の正の最高次係数と後退差分を使い、商の次数の厳密な減少を得る。
- `SamuelModuleProperties.lean`：Nakayama から非零有限加群の Samuel 関数の正値性を証明。
  線形同型による Samuel 関数・多項式の移送も用意した。
- `SamuelSurjection.lean`・`PrimeQuotientRegular.lean`：全射での長さの比較、
  `(R/p)/x(R/p)→R/q` の全射、および `x∉p` の素商上の正則性を証明。
- `HilbertSamuelDimension.lean`：`p<q` ごとの次数減少を素イデアル鎖の長さへ移し、
  鎖の長さの上限として定義された Krull 次元を抑える。上下界から一致を得た。

`natDegree_poly_eq_dim` は補助層へ移した同名の証明を `HilbertSamuel.lean` から公開する。
`multiplicity_pos` と平坦局所拡大の次元保存も、この未証明入力への依存がなくなる。
新しい `sorry`・公理・結論を仮定する入力は追加していない。

今回の検証：全体の `lake build` は3730ジョブで成功。新規・移動46宣言と既存7宣言の
計53宣言を公理監査し、51宣言は標準公理のみ。次数定理・重複度の正値性・平坦局所拡大の
次元保存に `sorryAx` の依存はない。主定理と核心定理の2宣言には既存入力からの依存が残る。
その他の公理はなく、直接の `sorry` は19箇所、`git diff --check` も通過した。

### Samuel 多項式の存在と次数上限：証明完了

次の部分を新しい未証明入力なしで実装した。

- `HilbertSamuelBasic.lean`：既存の定義・有限長性・基本性質を切り出した。
  構成のファイルから多項式性の定理を参照しない依存関係にし、後の接続で循環 import を作らない。
  公開宣言の名前と型は保持する。
- `AssociatedGraded.lean`：`I^nM / I^(n+1)M` を部分加群の商として構成し、
  `I` による消滅、準素イデアルの場合の有限長性、次数一の乗法を証明した。
  その商を `M/I^(n+1)M → M/I^nM` の核と同定して、Samuel 関数の増分と部分和の公式を得た。
- `ReesModule.lean`：Mathlib の安定フィルトレーションから Rees 加群を構成し、
  有限生成性を証明した。随伴次数加群の直和表示と Rees 加群の商表示の線形同型も構成した。
- `ReesPresentation.lean`：`I=(z_1,…,z_s)` から `X_i ↦ z_i t` の全射を構成し、
  随伴次数加群が `(R/I)[X_1,…,X_s]` 上有限生成になることと、変数が次数を一つ上げることを証明した。
- `HilbertSeries.lean`：Hilbert 級数 `H(X)` と Samuel 関数の級数 `S(X)` を定義し、
  `(1-X)S(X)=XH(X)` を証明した。`H(X)=Q(X)/(1-X)^s` が得られれば、
  `Polynomial.hilbertPoly (X*Q) (s+1)` が次数 `≤ s` の Samuel 多項式となる。
  冪零イデアルの場合の定数多項式も証明した。

`HilbertSerre.lean` で、有限生成の非負次数多項式加群の長さの級数が
`Q(X)/(1-X)^s` となることを証明した。次数一の作用の核と余核が同次であることを確認し、
各次数の四項完全列から `(1-X)H_M=H_coker-XH_ker` を導く。
核・余核では選んだ変数が零作用なので、残りの変数上での有限生成性を供給し、
変数の個数に関する帰納法を適用する。零変数では有限生成性から高次成分の消滅を得る。
補助層は `HilbertSerreFinite.lean`・`GradedSubquotient.lean`・`GradedLinearMap.lean`・
`GradedHilbertSeries.lean` に分けた。

`HilbertSamuelPolynomial.lean` でこれを実際の I 進随伴次数加群に適用し、
有理型表示を構成した。長さを元の環 R 上で測るので、係数環 R の多項式環上の
有限生成性とその次数一の作用も確認した。
`exists_isSamuelPoly` はこの構成と `exists_isSamuelPoly_of_hilbertSeries` の適用で証明済み。
元の仮定と結論を保ち、新しい `sorry`・公理・結論を仮定する入力を追加していない。
`multiplicity_pow` も `sorryAx` への依存がなくなった。

続く次数と環の Krull 次元の一致も証明済み。次の小節に実装をまとめる。
参考は [Stacks Proposition 10.58.7](https://stacks.math.columbia.edu/tag/00K1) と
[Proposition 10.59.5 の接続](https://stacks.math.columbia.edu/tag/00K4)。
今回証明したのは、必要な長さ値の主張である。

今回の検証（Hilbert–Serre と Samuel 多項式の存在）：全体の `lake build` は3721ジョブで成功。
新規47宣言、存在定理・冪の公式・正値性・平坦局所拡大の次元比較・主定理・核心定理の
計53宣言を公理監査し、49宣言は標準公理のみだった。
`exists_isSamuelPoly` と `multiplicity_pow` に `sorryAx` への依存はない。
残り4宣言は次元定理または既存の引用入力に由来する `sorryAx` に依存し、その他の公理はない。
新しい `sorry` は追加せず、総数は20。`git diff --check` も通過した。

以前の検証（随伴次数加群と母関数の準備）：

検証：全体の `lake build` は3715ジョブで成功。新規65宣言と移設した基本宣言14個の
計79宣言を公理監査し、すべて標準公理のみで、`sorryAx` やその他の公理への依存はない。
今回の追加・移設には `sorry` はなく、直接の `sorry` の総数は21のまま。
今回の変更について `git diff --check` も通過した。

以下はこの方針に至る前の接続作業の到達点である。

抽象化と不要コード整理が完了した後、ユーザーの「1、2、3を順番に」という指示により、
次の順序で論文全体への接続を進めた。

1. **核心定理の仮定から正規化基底・ガロア拡大・群作用を構成する：完了。**
   `Paper/Section5/GaloisNormalization.lean` と `Core.lean` で構成し、
   `core_statement` の直接の `sorry` を除去した。既存の Lemma 2.2、正則パラメータ、
   長さ代数、比較の引用入力への依存は残る。
   完備基底上の有限整域の局所性、正規基底上のガロア正規化、有限自由分解による
   トレースの降下を証明した。正則局所環の整閉性も、既存の正則パラメータの入力から導いた。
2. **一般の主定理から核心定理・Serre の定理への帰着（Lemma 5.1）：完了。**
   零次元の境界の `χ = 1`、両変数の素イデアル商へのデヴィサージュ、
   極大イデアルを保つ平坦局所拡大での長さ・環と加群の次元・Tor・χの保存を証明した。
   Lemma 2.1 と完備化への適用を合わせて `Section5.positivity_of_residueCharP` を得た。
   これは正の剰余標数・任意の有限生成加群の正値性で、環の完備性も
   剰余体の代数閉性も要求しない。完備化環の Noether 性は、有限変数の
   形式冪級数環からの全射を構成して証明した。
   ユーザーの指示により Serre の等標数正値性を `Inputs.serrePositivity_of_field` として引用した。
   剰余標数零では、非零整数の単元性から `ℚ` 代数構造を構成し、この引用へ接続する。
   `main_statement` 自身の `sorry` は除去した。引用定理への依存は残る。
3. **§2の長さ代数の具体的構成：外部引用を前提とする接続は完了。**
   正則基底の正規性を供給して共通分母を構成し、誤差評価用の `h-1` 個の元を
   準素イデアル内で選ぶところを証明した。これらを既存の核・像の長さ評価に適用し、
   正規化した Frobenius 商の長さが perfection の商の正規化長さへ収束することを
   `PerfectQuotientLimit.lean` で導く。塔作用の一意性により、任意の両立する作用での
   `towerLengthOn` にも接続した。
   続いて `PerfectKoszulLength.lean` で、近似環の各次数の Koszul ホモロジーの長さを
   `ℓ_D H^i(z^(p^n); D) / p^(nh)` と同定し、全段・全次数に共通する消去冪を選んだ。
   `KoszulMultiplicityLimit.lean` は高次の正規化長さが零へ収束するという前提から、
   商の極限を Hilbert–Samuel 重複度と同定する。perfection の商への接続も証明した。
   `DirectedHomology.lean`・`KoszulDirectedUnion.lean`・`PerfectKoszulLimit.lean` で、
   Koszul ホモロジーと有向極限の同型を構成し、高次の消滅極限を perfection 全体の
   正規化長さの消滅へ移した。ホモロジーの遷移写像に単射性は仮定しない。
   `FrobeniusKoszulLimit.lean` は Roberts 型の一般定理の適用条件（有限自由性・
   振幅と次元の一致・有限長ホモロジー）を確認し、Frobenius 基底変更を冪の Koszul
   複体と同定して、実数値の極限を `ℝ≥0∞` 値へ変換する。
   `perfectClosure_length_properties_of_roberts` により、この一般定理から等標数の
   二つの長さの性質まで導出した。ユーザーの追加の承認により、Roberts の定理を
   `Inputs.frobenius_homology_length_tendsto_zero` として名前付きの `sorry` で引用し、
   `perfectClosure_length_properties` と `lengthAlgebra_equalCharacteristic` へ適用した。
   旧 `perfectClosure_length_properties_pending` は証明済みの接続へ置き換えた。
   等標数の構成は、Roberts と既存の正則パラメータ・正規化長さ・重複度の引用入力に
   依存する形で完成した。定理2.5の等標数分岐にも接続済み。
   混標数では `CompletedTower` を実際の `p` 進完備化として定義し、
   `MixedPerfectoid` を `CompletedTower ⊗[A] D` の perfectoid 化として構成した。
   perfectoid 性は Fontaine 写像を用いた定義、perfectoid 化は普遍性で指定する。
   有限・有限表示性と `A`・`D`・塔の作用の両立を確認した。
   `Inputs/Perfectoidization.lean`・`PerfectoidTower.lean`・`CLMST.lean` の五つの引用から、
   一様な冪ねじれと係数制限による長さの一致を証明して二性質を導出した。
   旧 `lengthAlgebra_mixedCharacteristic_pending` は `lengthAlgebra_mixedCharacteristic` に
   置き換え、定理2.5に接続済み。冪と階数の公式には既存の共通の証明を使う。

ユーザーは Serre・Roberts に加え、混標数で必要な外部論文の結果も、出典を明示した
名前付きの `sorry` として引用することを許可した（2026-10-11）。今回の追加は
Bhatt–Scholze の存在・普遍性、CLMST の標準塔の perfectoid 性と三つの長さ関連の結果。
外部引用以外の接続には新しい `sorry`・公理・結論を仮定する入力束を追加しない。
`main_statement` の導出の完成と、
引用入力も含めた論文全体の形式化の完成は区別する。

今回の検証（混標数の構成と定理2.5への接続）：全体の `lake build` は3699ジョブで成功。
新規・変更32宣言と主定理・核心定理の計34宣言を公理監査し、7宣言は標準公理のみ、
27宣言は明示した引用入力に由来する `sorryAx` に依存する。その他の公理はない。
直接の `sorry` は17箇所から21箇所になった（外部引用を五つ追加し、混標数の未完了箇所を一つ除去）。
定理2.5の主張は維持し、混標数の構成に残っていた直接の `sorry` は除去した。
`git diff --check` も通過した。

前回の検証（`f1875a0`、有向極限・Roberts の引用・等標数の構成への接続）：全体の `lake build` は
3568ジョブで成功。新規・変更47宣言と主定理・核心定理の計49宣言を公理監査し、
39宣言は標準公理のみ、10宣言は Roberts または既存の引用入力に由来する `sorryAx` に依存する。
その他の公理はない。Roberts の引用を一つ追加し、等標数構成の一つを除去したため、
直接の `sorry` は17箇所のまま。定理2.5の主張と混標数の pending 定理は変更していない。
`git diff --check` も通過した。

前回の検証（`79c8fed`、§2 の Koszul 長さ・重複度への接続）：全体の `lake build` は3560ジョブで成功。
新規・変更25宣言と `main_statement`・`core_statement` の計27宣言を公理監査し、
16宣言は標準公理のみ、11宣言は既存の未証明入力に由来する `sorryAx` に依存する。
その他の公理はない。新しい `sorry` は追加せず、直接の `sorry` は17箇所を維持した。
`git diff --check` も通過した。

前回の検証（`80eb7fc`）：全体の `lake build` は3554ジョブで成功。新規・変更12宣言と
`core_statement` の計13宣言を公理監査し、6宣言は標準公理のみ、
7宣言は明示した引用入力に由来する `sorryAx` に依存する。その他の公理はない。
Serre の引用に一つ `sorry` を追加し、`main_statement` から一つ除去したため、
直接の `sorry` は17箇所のまま。`git diff --check` も通過した。

前回の検証（`4cc9880`）：全体の `lake build` は3549ジョブで成功。新規・変更43宣言の公理監査では、
27宣言が標準公理のみ、16宣言に既存の未証明箇所に由来する `sorryAx` が現れる
（後者には `main_statement` 自身の残る分岐も含む）。その他の公理はない。
直接の `sorry` は18箇所から17箇所に減少し、`git diff --check` も通過した。

### 完了した抽象化の範囲

直前の段階では対象を **付録の抽象化の枠組みと、その二つの実現** に限定した。
以下はその完了範囲の記録であり、上の新しい作業順序を制限しない。

共通理論・二つの実現・主要な既存証明の移行と文章整理に加え、
**概念的な λ-平坦性・λ-CM 性から Koszul 条件を供給する接続**を実装した。
`LengthAlgebra/Flat.lean`・`CohenMacaulay.lean` が有限性・消滅・Euler 数を導き、
`LengthAlgebra/FlatRealization.lean`・`Paper/Section4/FlatRealization.lean` が
二つの実現の共役和比較・消滅・極小 Euler 下界へ適用する。以下は完了範囲を記録する。

1. **共通の抽象論を仕上げる。** 長さ付きアーベル圏、ホモロジー的 Euler 評価、
   反復錐による消滅・第零次の同型・下界、群作用付きの対称比較を共通の定理として整理する。
   共通層は論文固有の環・塔・有限近似の存在構成に依存させない。
2. **perfect 複体版とランク無視版の実現を完成させる。** 実際の圏・関手・群作用を指定し、
   抽象定理の仮定を確認する。有限長さの商と大きな商の有限部分との圏同値、および
   ホモロジー・長さ・Euler・K₀ 評価の対応は実装した。perfect 複体の幾何学的支持と
   スカラーの冪の零作用との同値も、任意の可換環上で証明した。
   長完全列の Euler 加法性も共通化し、旧有限版の錐の加法性とランク版の
   K₀ 評価を共通構成へ移した。二つの実現の入力境界は
   [section-4-plan.md](section-4-plan.md) 冒頭の対応表に記録する。
3. **既存証明を共通定理の適用へ移す。** Euler の加法性、基底公式、共役和比較、
   消滅・下界について新旧の評価・K₀・係数変更の対応を確認し、重複した証明を整理する。
   旧 `chiOrdHom`・`chiLamHom_of_finite` と共通 Euler 評価の引き戻しとの一致は証明した。
   有限射影 K₀ の実際の群作用も構成し、比較写像の係数変更との可換性・同変性、
   局所環上での旧降下入力の移送を証明した。
   必要な具体的計算と論文の主張に対応する公開定理を保持し、移行後に不要な旧入口を整理した。
   本文 §4・§5 と付録 A・B も
   この証明経路に更新し、条件付きの証明と引用入力を区別した（2026-10-11）。
4. **§5への適用範囲。** 有限近似・支持・Koszul 条件などの明示的なデータから、
   共通定理によって比較・消滅・下界を得る部分を扱う。結論そのものを入力には移さない。
   そのデータを元の素イデアル商からすべて構成することは、抽象化段階の完了条件には含めなかった。
5. **論文全体への接続。** 抽象化段階で保存していた `core_of_normalization_bases` を
   上の作業1で使い、作業2で一般の主定理への帰着も完成した。現在は作業3を進める。

新しい抽象論・実現・移行のための `sorry` は追加しない。既存の名前付き未証明定理への依存は
個別に明示する。特に不変 K₀ 類の降下は比較の独立した入力であり、具体的な
`supportedRankK0_descent` に含まれる dg 表示と定理3.1への接続が証明済みになったとはしない。
その証明の完成や、外部入力全般の解消を、今回の作業へ自動的に追加しない。

### 移行後の不要コード整理（2026-10-11）

移行完了分を `1576952` にコミットした後、旧比較層と置換済みの補助証明を削除した。
定理4.7は共通の対称比較の系へ移した。旧 K₀・数値評価・圏の実現に必要な API と、
以前からの未証明入力は保持する。削除対象・置換先・保持理由は
[整理記録](cleanup-candidates-2026-10-11.md) にまとめた。

### 完了判定

今回の完了は、共通の主張と二つの実現の仮定確認がそろい、対象とする既存の比較・消滅・下界が
その適用で証明され、新旧の対応と未証明入力の境界が記録されていることとする。
最後の接続では、剰余体による λ-平坦性・テンソル積の有限ランク判定と、一乗の
Koszul 条件との同値を証明した。正則列の冪と商の長さ `v^e` は短完全列から証明し、
既存の未証明な重複度公式を使わない。λ-CM 性から有限基底上の λ-平坦性・有限ランクも得た。
基底の正則列または Koszul 分解を明示するこれらの接続には新しい未証明入力はない。
全体ビルドは3484ジョブで成功し、新規・変更35宣言の公理監査はいずれも標準公理のみであった。
これで今回の抽象化の完了条件を満たし、一区切りとする。

ユーザーの指示（2026-10-11）により、反復錐を二項係数個の直和へ並べ替える同型と、
有限版から複体列へ送る `ι` の独立した入口は残作業・完了条件から削除した。
これらを追加実装する予定は置かず、現在の再帰的分裂と評価公式を使う。
論文の核心定理・主定理が完成していることは要求しない。

`lake build` と定理ごとの `#print axioms` を確認する。名前付きの `sorry` 定理を利用すれば、
利用先にも `sorryAx` が現れる。ただし `#print axioms` は未証明定理の名前別一覧ではないので、
証明内の引用箇所とドキュメントも併せて確認する。
通常の数学的仮定（短完全性や台の条件など）を引数にすることは維持する。
定理の仮定をまとめる専用の `structure`・`class` は禁止する。必要な仮定を個別の引数で書き、
大きな連言の別名へ置き換える方法も使わない。存在定理の結論は存在量化と明示的な連言で書く。

## 1. 設計方針

### 1.1 未証明の引用は名前付きの `sorry` 定理にする

未証明の一般論を Prop 値の入力クラスで引き回さない。各数学的主張を明示的な定理として述べ、
証明を `sorry` とし、利用先ではその定理を直接適用する。これにより `sorryAx` への依存を
Lean の公理監査で確認できる。証明が完成したらその定理の本体を置き換える。
外部のコードは現時点でコピーせず、Mathlib の関連 PR の取り込みを待つ。

### 1.1a 設定用の構造体を作らない（2026-10-10）

`Setup34`、`IsRegularNormalizationBase`、`LengthAlgebraProps`、`LengthAlgebraData` は削除した。
補題3.4・系2.6・定理2.5の前提を個別に述べ、利用しない仮定を証明済みの主張から除いた。
定理2.5の存在結論は `C`、環構造、代数構造、正規化長さを直接存在量化し、四つの性質を列挙する。
過去の実施記録に現れるこれらの構造体名は旧版の記録であり、再導入しない。

### 1.2 層の細分化

`MEMO.md` の 3 層のうち、層 3 を二つに分ける。

| 層 | 中身 | 扱い |
| --- | --- | --- |
| 1 | §5 の議論、Lemma 2.4、Lemma 3.4/3.5 の形式的部分、最終の算術 | sorry なしで証明する |
| 2 | 論文の新しい一般定理：Theorem 3.1、Lemma 3.5（Theorem 3.1 の帰結の形）、§4（Prop. 4.3、Prop. 4.5、Theorem 4.7） | 名前付きの引用定理として置き、人手の検証を最優先する |
| 3a | 標準事実で Mathlib にないもの：Tor の長完全列と平坦基底変更、正則局所環の大域次元・整域性・CM 性、Koszul 複体の基本性質、環の取り替えスペクトル系列、極小自由分解 | 名前付きの `sorry` 定理として置き、順に証明して置き換える。Mathlib への寄与候補 |
| 3b | 文献の深い定理：Serre、Roberts–Gillet–Soulé、Cohen–Gabber、Cohen の構造定理、Monsky、Roberts の Frobenius ホモロジー定理、CLMST、Bhatt–Scholze、Faltings/Gabber–Ramero、Stacks 03QH/0BRI/0BRJ | 名前付きの `sorry` 定理として置く。証明はしない |

引用定理の docstring には論文の番号（例：`(2.4)`、`Lemma 5.5 の証明第 1 段落`）か文献を必ず書く。論文の主張より強い形で置かざるを得ないときは、その旨を docstring に明記する。

### 1.3 Tor の規約：Mathlib の `CategoryTheory.Tor` を使い、第 2 変数を分解する

- `Tor (ModuleCat.{u} R) i` は `X ⊗ -` の左導来関手（第 2 変数で導来）。証明は第 2 変数の分解で計算する。Lemma 5.1 の加法性は各変数で別々に示し、Lemma 5.2 の `Tor_i^R(C_D, E')` は E' の自由分解で計算する（論文もその順）。
- 任意の射影分解から計算できることは `ProjectiveResolution.isoLeftDerivedObj`、`i > 0` で第 2 変数が射影的なら 0 になることは `isZero_Tor_succ_of_projective`、`Tor_0 ≅ ⊗` は `Functor.leftDerivedZeroIsoSelf`（Mathlib）。
- 長完全列は `HomologicalAlgebra/TorLES.lean` で証明済み。両変数を交換した線形同値は `HomologicalAlgebra/TorSymmetry.lean` にあるが、高次の自然性は主張していないので、計算は引き続き第 2 変数の分解による（`HomologicalAlgebra/Tor.lean` の docstring）。
- 宇宙は `u` 一つに固定する。`ModuleCat.{u} R` の制約で、環も加群も `Type u` にそろえる。

### 1.4 χ の定義は `finsum` と `ENat.toNat`

`Module.length` は `ℕ∞` 値なので、`χ = ∑ᶠ i, (-1)^i * (length Tor_i).toNat` と定義する。無限長は 0 に、無限個の非零項は和 0 になる（Mathlib の `eulerChar` と同じ junk value の方針）。正則局所環上では `Tor_i = 0 (i > d)` で有限和になる（`chi_eq_sum_range`）。Tor の各項が有限長であることは `isFiniteLength_torModule`（`CommutativeAlgebra/TorFiniteLength.lean`）で証明済み。

### 1.5 Hilbert–Samuel 重複度は束に入れない

Theorem 2.5 の (2.5) は §5 では `0 < λ(U) < ∞`（(5.5)）としてしか使われない。(2.6) は基底パラメータについて `λ(C_D/(t^v)) = v^h rank_A D` の形で使う。したがって束には (2.5) を「任意のパラメータ系 z と v ≥ 1 で `0 < λ(C_D/(z^v)C_D) < ∞`」に弱めて入れ、Hilbert–Samuel 重複度の定義を避ける。弱めた形なので忠実性の問題はない。

**改訂（2026-10-10）**：この方針は取り下げた。§2 は具体的な対象の話なので、Hilbert–Samuel 重複度は
Samuel 多項式の最高次係数として定義し（`CommutativeAlgebra/HilbertSamuel.lean`）、(2.5) は論文どおり
`λ(C_D/(z^v)C_D) = v^h e((z), D)` と書く。重複度の定理（多項式性、次元定理、正値性）は可換環論の
一般論として別トラックで証明する。詳細は `notes/section-2-plan.md` §5。

## 4. 命題の依存グラフと層の割り当て

当初（2026-10-07）の割り当て。層 3a の多くはその後証明済みで、各補題の現状は対応するファイルの docstring にある。

```
Theorem 1.1
├── Lemma 5.1 帰着 ........................................ 層 1
│   ├── Serre（等標数の正値性） ...................................................... 層 3b
│   ├── 完備化 + Lemma 2.1：χ・次元・有限長・正則性を保つ平坦局所拡大 .................. 層 3b
│   ├── Roberts–Gillet–Soulé 消滅 (5.1) ........................................... 層 3b
│   ├── χ の各変数での加法性、Tor_i = 0 (i > d)、Tor_i の有限長、χ(k,R) = χ(R,k) = 1 .. 層 3a
│   ├── 正則局所環は整域 .............................................................. 層 3a（Mathlib になし）
│   └── 素フィルトレーション、台と supportDim の単調性 .............................. Mathlib にあり
└── 核：D = R/P, E = R/Q
    ├── 設定
    │   ├── Lemma 2.2 正則な正規化基底 A_D ⊂ D ..................................... 層 3b
    │   ├── Galois 閉包 D'、G_D、剰余体 k、幾何ファイバーの推移性 ....................... 層 3b + 層 1
    │   ├── 塔 Λ と λ_∞（Lemma 2.3）.................................................. 層 3b
    │   ├── Lemma 2.4 零長さの極限 .................................................... 層 1（抽象構造から証明）
    │   └── Theorem 2.5：(C_D, λ_D) と (2.4)(2.5 弱)(2.6)、Cor 2.6 .................. 層 3b
    ├── Lemma 5.2 (5.3)：|G_D| a_D a_E χ(D,E) = Σ_σ c_σ ............................ 層 1
    │   ├── Lemma 3.5 (3.11) 通常ノルム比較 .......................................... 層 2
    │   ├── Tor_i^R(C_D,E') = H_i((F ⊗_R D') ⊗_{D'} C_D)、台の有限性、ひねりの不変性 .... 層 3a
    │   └── χ(D',E') = a_D χ(D,E)：D^{a_D} → D' の余核と (5.1)、加法性 ................ 層 1
    ├── 各 σ：(5.18) |G_E| c_σ = Σ_γ b_{σ,γ}
    │   ├── x の選択 (5.4)：素イデアル回避（Mathlib `Ideal.subset_union_prime`）、R は CM .. 層 3a
    │   ├── Lemma 5.3 τ_i(L)：有限、i > l で 0 ....................................... 層 1（証明は層 3a：環の取り替えスペクトル系列、Koszul 分裂）
    │   ├── Lemma 5.4 有限近似 M_n, s_n：(5.9)(5.10)(5.11) ............................ 層 1（極限の取り出し）+ 層 3a/3b（段への降下、平坦性）
    │   ├── Lemma 5.5 台と通常評価 = c_σ ............................................. 層 1（§4 の評価 + 極小分解 (5.13) + (1+t)^l の約分）
    │   └── Theorem 4.7 漸近ノルム比較 ................................................ 層 2
    ├── Lemma 5.6 b_{σ,γ} ≥ ν_σ η_E > 0 ............................................ 層 1（多項式の議論、0 次の全射、(5.11)(5.16)）
    └── 最終の算術：|G_D| a_D a_E χ(D,E) = (1/|G_E|) Σ_σ Σ_γ b_{σ,γ} > 0 ............. 層 1
```

層 1 の各補題の中で、層 3a に回した部分は次のとおり。

| 補題 | 層 1 で証明する部分 | 層 3a に預ける部分 |
| --- | --- | --- |
| 5.2 | 加法性と (5.1) から χ(D',E') = a_D χ(D,E)、ノルム比較の適用 | Tor と複体のホモロジーの同一視、Tor の台が閉点に乗ること、σ でひねっても通常の χ が変わらないこと |
| 5.3 | 結論の組み合わせ | 環の取り替えスペクトル系列による長さの一致、`K(x;R) ⊗^L L ≃ ⊕ L[j]` の分裂、`i > l` の評価 |
| 5.4 | ε と n の対角線論法、(5.11) の下からの評価 | λ の sup 性質からの有限生成近似、有限表示の段 j への降下、`Tor^B(P_ε, L) = Λ ⊗ Tor^B(P_j, L)`、(5.12) の評価 |
| 5.5 | `(1+t)^l` の約分と (5.10) からの `b_i = τ_i(E')`、`b_i` の交代和が c_σ | 切り詰めの誤差が rank o(s_n) であること、`m_B^a` の零ホモトピーから台が出ること、Koszul 分裂 |
| 5.6 | `b_i ≥ 0` かつ `(1+t)^l Σ b_i t^i` の l 次より上が 0 なら `b_i = 0 (i > 0)`、超極限の単調性、(5.17) | Koszul 先取りのスペクトル系列で総次数 > l の λ が 0、0 次ホモロジーから `(C_E/m C_E)^{β_0}` への全射、(5.16) |

## 5. §5 を書くためのインターフェース

2026-10-10 改訂。§5 は具体的な対象と個別の仮定を受け取り、証明済みの定理または名前付きの引用定理を直接使う。旧案の設定構造体・入力クラスを再導入しない。§4 では圏と評価を構成し、有限性・非負性・(4.2)・ノルム比較を個別の定理として供給する。

| 対象または定理 | 論文 | 中身 | §5 で使う性質 | 扱い |
| --- | --- | --- | --- | --- |
| `NormalizedLength C J` | Lemma 2.3、§3.4 冒頭 | 冪ねじれ加群の非負加法長さ | 加法性・同型不変性・単調性 | 数学的対象として実装済み。(2.3) の上限の性質は §2 の別の仕事 |
| 具体的な塔とその長さ | (2.1)、Lemma 2.3 | A_n、Λ、λ_∞ | 有限段での正規化、平坦性、降下、上限の性質 | `section-2-plan.md` に従って構成する |
| 長さ代数の存在定理 | Theorem 2.5、Cor 2.6 | C_D と作用・長さを存在量化 | パラメータに関する消滅・評価・正値性 | `Section2.theorem_2_5`。塔の作用との両立を含む |
| 環・群作用・階数 | §5.1 | A_D、D'、G_D、`Module.finrank` | 有限性、剰余体、幾何ファイバーの推移性 | 個別の対象と仮定で述べる |
| `lemma_3_5` | Lemma 3.5 | 通常のノルム比較 | (3.11)、χ_C の有限性 | 証明済みの部分と名前付き引用への依存を区別する |
| §4 の具体的な評価と各定理 | Prop. 4.3、Theorem 4.7 | b_i^ord、b_i^C、χ_ord、χ_C | 有限性、非負性、(4.2)、ひねり、共役和の一致 | §4 の作業で構成・証明する。専用の仮定の束は作らない |

補足：

- 幾何ファイバーの推移性は `∀ Ω [Field Ω] [IsAlgClosed Ω] [Algebra A Ω], ∀ x y : PrimeSpectrum (T ⊗[A] Ω), ∃ g, g • x = y` と書ける。
- `γ` によるひねり `g^*P` は `ModuleCat.restrictScalars` を複体に写したもの。
- (4.2) の右辺の超極限は Mathlib の超フィルターによる極限を使う。有界列での存在、有限和との交換、通常の極限との一致を §4 用の API として整備する（`Asymptotic/` で §4 の作業として整備中）。
- 「台の十分条件」は rank-small 誤差と支持条件から示す Lemma 5.5 側の接続補題として分ける。先行実装で入力に置く場合も出典を別に明示し、評価の存在だけで証明済みとはしない。

## 6. 帰着の計画と残作業

### M1：Lemma 5.1

2026-10-11 時点で下記1–4の接続は実装済み。1の Serre の定理自体はユーザーの指示で引用に置く。

- `IntersectionMultiplicity/Devissage.lean`：一般の正則局所環上で両変数を素イデアル商へ帰着する。
- `Paper/Section5/PrimeReduction.lean`：零次元の境界を計算する。
- `CommutativeAlgebra/SupportDimension.lean`：短完全列での次元の最大値、有限長テンソル積から根基条件を得る。
- `CommutativeAlgebra/FlatLocalDimension.lean`：平坦局所拡大で環・加群の次元を保存する。
  次元比較は既存の Hilbert–Samuel 多項式の存在と環の次元定理に依存する。
- `HomologicalAlgebra/TorBaseChange.lean`、`IntersectionMultiplicity/BaseChange.lean`：
  射影分解と係数拡大から Tor の同型を作り、長さと χ の保存を導く。ここに新しい引用入力はない。
- `Paper/Section5/ResidueFieldReduction.lean`：Lemma 2.1 で剰余体を代数閉体へ移し、
  完備・正剰余標数の場合を証明する。Lemma 2.1 の結論に含まれる Tor 長さの保存は使わず、上の一般論を使う。
- `CommutativeAlgebra/AdicCompletionNoetherian.lean`：Noether 環のイデアル進完備化の Noether 性を証明する。
  有限変数の形式冪級数環からの評価写像を、剰余環上の全射性と完備性により全射にする。
  完備化環への適用を含めて未証明入力はない。
- `Paper/Section5/CompletionReduction.lean`：完備化で長さ・次元・正則性・χを保存し、
  `positivity_of_residueCharP` を得る。これを `main_statement` の正の剰余標数の分岐に適用する。
- `Inputs/SerrePositivity.lean`：Serre, *Local Algebra*, Chapter V, Theorem 1 の
  等標数正値性を `serrePositivity_of_field` として引用する（ユーザーが許可した `sorry`）。
- `CommutativeAlgebra/ResidueCharacteristicZero.lean`：剰余体が標数零なら非零整数は単元。
  整数環の分数体の普遍性で `ℚ → R` を構成する。この一般論は標準公理のみ。
- `Paper/Section5/CharacteristicZeroReduction.lean`：構成した `ℚ` 代数構造で Serre の引用定理を適用する。
  `main_statement` の剰余標数零の分岐はこの定理を使い、自身の `sorry` を持たない。

この帰着の作業は完了し、次の作業は §2 の具体的構成である。
Serre の結果自体の証明は今回の範囲に含めない。

元の証明構造（2026-10-07 の計画。以下の「要追加」「層3a」は当時の分類）：

1. 剰余標数 0 なら Serre で終わる。以後 `CharP (ResidueField R) p`。
2. 完備化と Lemma 2.1 の平坦局所拡大（名前付き引用）で `R₁` に移る。`chi` と仮定が保たれるので `R₁` で示せばよい。
3. 主張を強めて帰納法にかける：`Claim(M)`：「有限生成 `N` で `length (M ⊗ N) ≠ ⊤` かつ `supportDim M + supportDim N ≤ d` なら `chi M N ≥ 0`、さらに `= d` なら `> 0`」。
   - `M` について `IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime`（Mathlib。零加群、`R ⧸ p`、短完全列の 3 ケース）。
   - 短完全列 `0 → M' → M → M'' → 0` では、`Module.support_of_exact`（Mathlib）で `Supp M = Supp M' ∪ Supp M''` を得て、`supportDim M = max`（要追加）、`M' ⊗ N`、`M'' ⊗ N` の有限長（台の包含と「有限生成で台 ⊆ {m} なら有限長」。要追加）、χ の第 1 変数での加法性（層 3a）。
   - `M = R ⧸ p` のときは `N` について同じ帰納法。第 2 変数の加法性（層 3a）。
   - 両方素イデアル商のとき：次元の和が `< d` なら RGS で 0、`= d` で両方正次元なら核の主張、`= d` で片方が 0 次元なら `p = m` かつもう一方が `0`（正則局所環は整域：層 3a。`ringKrullDim_quotient_succ_le_of_nonZeroDivisor` で `dim R/q < d`）で `χ(k, R) = χ(R, k) = 1`（層 3a）。
4. `P + Q` が `m` 準素であることは「`R/P ⊗ R/Q = R/(P+Q)` が有限長」から出す（Mathlib の `support_of_supportDim_eq_zero` の逆向き。要追加）。

Mathlib に足すべき小補題：`supportDim` と短完全列、`supportDim M = 0 ↔ 有限長`（有限生成・Noether 局所）、`R/(P+Q)` の有限長と `(P ⊔ Q).radical = m` の同値。

§4（旧 M5）の計画は [section-4-plan.md](section-4-plan.md) を正本とする。

## 8. リスクと未決事項

| 項目 | 内容 | 対処 |
| --- | --- | --- |
| Tor の API | 自然性つきの対称性・基底変更は Mathlib にない | §1.3 のとおり第 2 変数の分解で計算する。`Tor.lean` に閉じ込め、定義の差し替えに備える |
| `WithBot ℕ∞` の算術 | 次元の和や比較が煩雑 | Noether 局所環では `FiniteRingKrullDim` のインスタンスがあるので、必要箇所で `ℕ` に落とす補題を用意する |
| Koszul 複体の添字 | 複体のテンソル積の対称性・結合性は `up ℤ` にしかない | ℤ 添字で定義する。鎖複体との読み替え補題を一つ用意する |
| 引用の忠実性 | 論文より強い主張を引用定理に置いてしまう危険 | docstring に出典を必ず書く。Lemma 5.5 の台の条件のように移した部分は一覧を `Inputs/Descent.lean` の冒頭に書く |
| Mathlib の更新 | master 追従で破壊的変更が入る | manifest で固定。更新は PR 単位 |
| 公理の監査 | CI での `#print axioms` の照合はまだない | 必要になったら照合の step を足す |

決定済み（2026-10-07）：Koszul 複体は当面プロジェクト内に閉じる（Mathlib 寄与は考えない）。blueprint は今は入れない（§4 の木と docstring で代用する）。

## 9. ファイルの書き方

- Mathlib はモジュールシステム前提なので、各ファイルは `module` で始め、import は `public import` にする。
  定義を含むファイルは docstring の直後に `@[expose] public section`、定理だけのファイルは `public section` を置く。
- Mathlib の著作権ヘッダ linter は `lakefile.toml` で止めた（`weak.linter.style.header = false`）。
  LICENSE を決めてヘッダを付けるなら戻せる。

## 11. Lemma 3.4 の設計

数学的な整理は `notes/lemma-3-4.md` にある。証明で実際に使う仮定は「`z` が `m_A` を生成する正則列」
「`C` が `A` 代数」「`λ` の加法性と非負性」「(3.9) の `v = 1`」だけで、完備性、剰余標数、`T` が整域であること、
`T` の有限性は使わない。そこで最小の仮定の一般論（`normalizedLength_tor_of_isWeaklyRegular`）を先に証明し、
Lemma 3.4 と Cor 2.6 の 1・2 をそこから出した。

### 11.1 Koszul 複体の定義（決定）

`koszulComplex x`（`x : Fin n → R`）は `n` に関する再帰で、`K(∅) = R`（0 次に集中した cochain 複体）、
`K(x₀,…,xₙ) = Cone(xₙ • 𝟙 : K(x₀,…,xₙ₋₁) → K(x₀,…,xₙ₋₁))`。最後の元を外側の錐にとるので、
Mathlib の正則列 `RingTheory.Sequence.IsRegular M [x₀, …, xₙ]`（`xᵢ` は `M/(x₀,…,xᵢ₋₁)M` 上で正則）
と帰納法の向きが合う。写像錐は Mathlib の `CochainComplex.mappingCone`（ℤ 添字の cochain 複体）。
`H_i(x; M)` は cochain の `-i` 次のホモロジー。

### 11.2 証明の構造（論文）

`V = k` のとき：`z` の Koszul 複体は `k` の `A` 上の自由分解なので `Tor_i^A(k, C) = H_i(z; C)` で、
(3.9) の `v = 1` から主張が出る。一般の有限長 `V` は組成列の帰納法：`0 → V' → V → k → 0` の
Tor 長完全列で、正次数の項は非負性と加法性から `λ = 0`、0 次では連結射の像が `λ = 0` なので
`λ(C ⊗ V) = λ(C ⊗ V') + r`。

### 11.3 必要な部品と Mathlib の状況

| # | 部品 | Mathlib | 扱い |
| --- | --- | --- | --- |
| A1 | 正則局所環の正則パラメータ系は正則列：`Ideal.span (range z) = m` かつ `dim A = e` なら `IsRegular A (List.ofFn z) A` | なし | 層 3a。`Inputs/RegularLocalRing.lean` に `sorry` の定理として置く |
| A2 | 正則列の Koszul 複体は `H^{-i} = 0 (i > 0)`、`H^0 ≅ A/(x)` | 写像錐の三角 `mappingCone.triangleh`、`homologyFunctor` が homological、`homologySequence_exact₁/₂/₃` あり | 証明する。`n` の帰納法。錐の長完全列で `H^{-1}(Cone) = ker(xₙ : H^0 K → H^0 K) = 0`（正則性）、`H^0(Cone) = coker = A/(x)` |
| A3 | Koszul 複体を `ProjectiveResolution (A ⧸ m)` に仕立てる。ℤ 添字 cochain → ℕ 添字 chain の読み替え | `ComplexShape.Embedding.embeddingUpIntLE : Embedding (down ℕ) (up ℤ)`、`restriction`、`ProjectiveResolution` | 証明する。各項は有限自由の直和なので射影的 |
| A4 | 基底変更 `C ⊗_A K(z; A) ≅ K(ι z; C)`：写像錐と `single` が加法的関手と両立 | `homotopyCofiber.mapHomologicalComplexObjIso`、`single` の両立 | 証明する。`n` の帰納法 |
| A5 | `TorAlg (algebraMap A C) i (A ⧸ m) ≅ H_i(ι z; C)` | `ProjectiveResolution.isoLeftDerivedObj` | A3、A4 から |
| A6 | `C ⊗_A (A ⧸ m) ≅ C / mC` | `TensorProduct.quotTensorEquivQuotSMul` | ほぼそのまま |
| B1 | 有限長加群の組成列帰納法。単純加群は `k` | `IsFiniteLength.of_simple_quotient`、`isSimpleModule_iff_isCoatom`、`IsLocalRing.isMaximal_iff` | ほぼそのまま |
| B2 | Tor の長完全列（導来する変数について）：`0 → V' → V → V'' → 0` から `… → Tor_i V' → Tor_i V → Tor_i V'' → Tor_{i-1} V' → …` | なし。馬蹄補題がない。複体の短完全列のホモロジー長完全列（`HomologicalComplex.HomologySequence`）はある | 層 3a で最大の部品。まず `sorry` の補題として置き、Lemma 3.4 を完成させてから、馬蹄補題（`P'ₙ ⊕ P''ₙ` に微分を作る）で証明する |
| B3 | `Tor_i^A(V, C)` は `Ann_A V` で消える。有限長加群は `m` の冪で消える | `leftDerived` の線形性はない | 証明する。`leftDerived_map_eq` で `a • 𝟙` の持ち上げを `a • 𝟙 P` にとり、`extendScalars` が `a • f ↦ φ a • f` であることと `homologyMap` の線形性 |
| B4 | `NormalizedLength` の補題：部分加群・商で単調、完全列 `M₁ → M₂ → M₃` で `len M₂ ≤ len M₁ + len M₃`、両端が `0` なら中央も `0` | 構造の公理から | 証明する。短い |
| C | 組み立て | | B1 の帰納法の中で A5・A6（基底）と B2〜B4（帰納段） |

表の「Mathlib」「扱い」の欄は 2026-10-07 時点のもの。いまはすべて証明済みで、A1 だけが名前付きの `sorry`
（`isWeaklyRegular_of_span_eq_maximalIdeal`）として残る。B2 は馬蹄補題ではなく写像錐で証明した
（`HomologicalAlgebra/TorLES.lean`）。

### 11.5 実装上の注意

- ホモトピー圏の `homologyFunctor` は複体の `homology` と定義上は一致しない（`rfl` が通らない）。
  `HomotopyCategory.homologyFunctorFactors` の同型で短複体ごと移す（`exact_transport`）。
- `single₀` の 0 次の項は `Z` と定義上しか一致しないので、`rw` が「motive が型正しくない」で
  失敗しやすい。`exact Category.assoc _ _ _` のように項で与える。
- 並行して走らせた Bash コマンドは作業ディレクトリを共有するので、`cd` を含むコマンドを
  並行実行すると相対パスが壊れる。ビルドは一度に一つ、読み取りは絶対パスで。
- ビルド出力を `tail` で切ると先頭の「Unknown constant」を見落とす。`head` で先頭から見る。

## 12. Lemma 3.5 の設計

`notes/lemma-3-5.md` の三分割に従い、3.5a（有限性）、3.5b（基底変更での一致）、3.5c（共役和）に分けて
形式化した（`Paper/Lemma3_5.lean`、`Paper/Lemma3_5/`）。

### 12.1 台の条件と `K₀`

- 台の条件は論文 §3.1 の判定法 `IsSupported z P := ∃ v, ∀ j, z_j^v • 𝟙 P` が零ホモトピック、で定義する。
  生成元 `z`（`A` の正則パラメータ系の像）で指定するので、基底変更とひねりで保たれる。
  「ホモロジーが `J` の冪で消える」という定義は基底変更と相性が悪かった。
- `G` の `K₀(T)` への作用は `g • x := (g⁻¹)^* x`（ひねりは反変なので逆元で左作用にする）。
- Theorem 3.1 の帰結（`theorem_3_1_K0`）と `conjSum_eq` の全射性の仮定は、(3.2) の整数版
  「`G` 不変な `y` に `n > 0` と `x` があって `n • y = f x`」で書く。`⊗ ℚ` を扱わずに済む。

### 12.5 Lemma 3.5b の証明計画（2026-10-08）

**論文の議論と変更点**：論文は超 Tor スペクトル系列で `χ(Q ⊗ T)` を `H_j(Q)` の Tor に分解し、
λ 側は Lemma 3.4、通常側は `T` の有限自由 `A` 分解（交代ランク `= r`）で計算する。
Mathlib には超 Tor スペクトル系列も「正則局所環の大域次元は有限」もないので、次の方針に変える。

**方針**：`K₀^{m_A}(A)` は Koszul 複体の類 `[K(z)]` で生成される（台つき完全 `A` 複体 `Q` に
整数 `n` があって `[Q] = n · [K(z)]`）。`Q ↦ χ_T(Q ⊗ T)`、`Q ↦ χ_C(Q ⊗ T)`、`Q ↦ r · χ_A(Q)` は
どれも `K₀^{m_A}(A)` 上の準同型（3.5a を `T` と `A` に適用）なので、`K(z)` での値が `r` で
一致すれば足りる。λ 側では Lemma 3.4 を使わない（`V = k` の場合が `hkz`、`hq` そのもの）。

**主張の分割**：二つの等式は独立に示せるので分けた（`Paper/Lemma3_5.lean`）。

| 主張 | 内容 | 使う仮定 |
| --- | --- | --- |
| `lemma_3_5b_ord` | `χ_T(Q ⊗_A T) = r · χ_A(Q)` | `A` 正則、`hz'`、`hdim`、`T` 有限・局所、`hres` |
| `lemma_3_5b_lam` | `χ_C(Q ⊗_A T) = r · χ_A(Q)` | `A` 正則、`hz'`、`hdim`、`T` 有限、`hkz`、`hq`、`hfin` |
| `lemma_3_5b` | 二つを並べたもの（証明済み） | 両方 |

共通部分は「生成」（下の段階 1〜5）と `χ_A(K(z)) = 1` だけ。

**生成の証明（デヴィサージュ）**：`Q` の項が 0 でない最高次数を `t` とし、ホモロジーの長さの
総和と幅について帰納法。

- `H^t(Q) ≠ 0`：`H^t(Q) ↠ k` を選び、`Q → k[-t]` を Koszul 分解 `K(z)[-t] → k[-t]` に沿って
  持ち上げる（`Q` は有界な射影的複体なので K 射影的、Mathlib の `isKProjective_of_projective`、
  `DerivedCategory.Qh_map_bijective`）。写像錐の長完全列から錐のホモロジーの長さの総和は 1 減る。
  `[Q] = ±[K(z)] - [錐]`。
- `H^t(Q) = 0`：最上段の微分は分裂全射。切り詰め（`truncLE`）で一段短くする。核は有限射影的なので
  局所環上自由。切り詰めは K 射影的な複体の間の擬同型なのでホモトピー同値（`quasiIso_iff`）。
- ホモロジーが 0：非輪状で K 射影的なので可縮、`[Q] = 0`。

**段階**

| 段階 | 内容 | 使う側 |
| --- | --- | --- |
| 1 | 三角形 `X → Y → Z → X[1]` で `a` が `g` と `h` を消すなら `a² • 𝟙_Z ∼ 0`。錐と `K(z)` の台 | 共通 |
| 2 | `K(z)` は台つき完全複体。`K₀` の零複体・シフトの補題 | 共通 |
| 3 | K 射影性による持ち上げと、錐のホモロジーの長さの計算 | 共通 |
| 4 | 最上段の切り詰め（分裂、射影的なら自由、ホモトピー同値） | 共通 |
| 5 | 生成：`∀ Q, ∃ n : ℤ, K0.mk Q = n • K0.mk K(z)` | 共通 |
| 6a | `χ_A(K(z)) = 1`（A1 に依存） | 共通 |
| 6b | `χ_C(K(z) ⊗ T) = r`（`baseChangeKoszulIso`、`hkz`、`hq`、`H_0 ≅ C/(z)`） | λ 側 |
| 7a | Koszul Euler 標数 `χ(z; T) = rank_A T`（`A` 正則）。層 3a の入力として `sorry` で置く | 通常側 |
| 7b | 剰余体が同じ局所環 `T` 上の有限長加群で `length_T = length_A` | 通常側 |
| 8 | `lemma_3_5b_ord`、`lemma_3_5b_lam` の組み立て | 各側 |

7a の証明は別トラック（正則 ⇒ 有限大域次元、`K(z) ⊗ L` の二重複体、交代ランク = 生成ランク）。

### 12.7 通常の長さは正規化長さの特別な場合（旧 §14.1、2026-10-09）

`OrdinaryEuler.lean` と `NormalizedEuler.lean` にあった、ホモトピー不変性と写像錐での加法性の
証明（`chiOrd_cone` と `lambdaEuler_cone` など約 130 行）が `Module.length` と `lam.len` の違いを除いて
同一だった。`NormalizedLength.ordinary T : NormalizedLength T ⊥`（`ℕ∞` を `ℝ≥0∞` に埋め込んだ
`Module.length`）を定義し、`IsPowTorsion ⊥ M` がどの `M` でも成り立つこと（`IsPowTorsion.bot`）を使って、
通常の長さ側の定理を `lambdaEuler` 側の系として導く（`chiOrd_eq_lambdaEuler_ordinary`）。
依存の向きは `NormalizedEuler ← OrdinaryEuler` に反転した。


## 18. 説明コメント（docstring）の書き直し（2026-10-10）

当時の全 46 ファイルのモジュール docstring と宣言 docstring を次の方針で書き直した。
以後に追加するファイルもこの規約に従う。

### 18.1 モジュール docstring

見出しつきで 10〜30 行。

- **概要**：このファイルが何を定義・証明するか、論文のどこに当たるか。
- **背景 / 定義 / 方針 / 証明**：なぜこの形で定義するか、証明の筋道（使う Mathlib の定理、このプロジェクトの
  どの補題に帰着するか）。
- **規約と注意**：添字の向き（cochain の `-i` 次が `H_i`）、junk value（無限長は `0`、`finsum` の規約）、
  ひねりの反変性（`g • [P] = [twist g⁻¹ P]`）、`Tor` は第 2 変数を分解する、など。
- **使われ方**：どのファイル・どの補題から使われるか。残る `sorry` への依存があれば明記する。

### 18.2 宣言 docstring

- 最初の文で主張を日本語で述べる（記号は補助。`λ`、`χ_T`、`K₀^{m}(A)` などは初出で説明する）。
- 仮定の意味（なぜ要るか、何に使うか）を書く。
- 自明でない証明には 1〜3 文で筋道を書く（長完全列のどこを見るか、帰納法の構造、など）。
- 関連する補題・論文の式番号・使われる場所を書く。
- 定義と構造体は「なぜこの形か」を書き、構造体の場には 1〜2 文ずつ付ける。
- 目安：補題 2〜5 文、定義・構造体 3〜8 文。

### 18.3 注意

docstring の変更だけなので定理名・証明は変わらず、`#print axioms` の結果も変わらない。
各ディレクトリの書き換え後に `lake build` で確認した。

## 19. §2 トラック（2026-10-10）

計画・実施記録・残りの引用の一覧は `notes/section-2-plan.md` にある。塔 `Λ`、正規化長さ `λ_∞`、
Hilbert–Samuel 重複度（Samuel 多項式の最高次係数）を具体的に定義し、Theorem 2.5（`Section2.theorem_2_5`）は
塔の作用との両立を含み、`λ_D` は `λ_∞` の係数制限（`towerLengthOn`）として定義する。旧
`Inputs.exists_lengthAlgebra` と極限の式による `hilbertSamuelMultiplicity` は削除した。
