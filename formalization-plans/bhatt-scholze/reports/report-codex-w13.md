# BS-W13 停止点 0

`math/bs-impl` に指示書の入った `main`（`650386066`）を取り込んで照合した。その後、`main` を `5933bde0c` まで取り込んだ。後者までの差分は HTT の調査文書。以下は紙と宣言の照合および型案。Lean の実装、型検査、ビルド、監査は段 1 以降に行う。

BS 著者版 Prop 10.4、Lemma 10.5、Remark 10.7、Thm 10.9、Thm 10.11、Lemma 10.12 を照合した。Thm 10.9 の almost 連結性の証明と Thm 10.11 の組み立てでは Cor 8.12 と導来の perfectoid 化が必要になる。層別、有限代数の近似、比較環と付値環への延長は独立した入力にできる。 [BS 著者版 §10.2、pp. 79–83](https://people.mpim-bonn.mpg.de/scholze/prisms.pdf#page=79)

## C1 と C1′

`drafts/A8/AlmostConnectivity.lean` の記法で、$B=(R/J)_{\mathrm{perfd}}$、$K=\ker(R\to B)$。商から $B$ への写像の全射性には、既存の `surjective_perfectoidization_of_quotient`（`Semiperfectoid/QuotientPerfectoidization.lean`）が使える。この宣言は $J$ の完備性を要求しない。C1 の公開型は draft の完備性仮定を含めて維持する。

- **Prop 10.4。** `Perfectoidization/CompletedTensor.lean` の `integralPerfectoid_completedQuotientMul_isIso` と `Almost/Lemma103.lean` の `integralPerfectoid_completedIdealTensorQuotient_isZero` を $R/K\simeq B$ に移す。$D_{p\text{-comp}}(B)\to D_{p\text{-comp}}(R)$ は完備底変換の右随伴で、乗法同型が余単位の同型性を与える。制限は極限と完備余極限を保つ。後者にはスカラー制限と導来完備化の比較が要る。$K$ で殺される各 $H^i(M)$ は $B$ 加群なので、切り捨てと有界 Postnikov 塔で有限区間を像に入れ、下側の切り捨ての逆極限と上側の切り捨ての完備余極限で $M$ を復元する。これで $K\widehat\otimes^L_R M=0$。逆は $K\widehat\otimes^L_R M\to M\to B\widehat\otimes^L_R M$ から出る。全次数の復元と、完備圏での随伴・保存性が実装の主な規模を決める。
- **Lemma 10.5 と G-A8-1。** コホモロジー次数の $D^{\leq 0}$ を連結とする。$\tau^{>0}M$ に Prop 10.4 を使い、完備テンソルの連結性保存と長完全列を合わせる。almost 連結性の完備 filtered 余極限での閉性は $K\widehat\otimes^L_R-$ の完備余極限保存に帰着する。draft の任意の filtered 準圏に対する型については、完備テンソルの保存性とコホモロジーの計算を準圏の余極限で確認する。
- **根基。** perfectoid 環は被約なので、$R/J$ からの perfectoid 環への写像は $R/\sqrt J$ を一意に通る。指定した古典的な商の perfectoid 化の普遍性で $K(J)=K(\sqrt J)$。
- **生成元ごとの判定。** $J=(f_1,\dots,f_r)$ なら $K(f_i)\subset K(J)$ から一方向。逆向きには、既に perfectoid な $B_i=(R/(f_i))_{\mathrm{perfd}}$ 同士の完備導来テンソルを使える。`integralPerfectoid_completedTensor_pure_and_h0` はこれが離散であることを、`completedTensorPerfectoidizationMap_isPerfectoidization` はその実際の $H^0$ と単位の普遍性を与える。帰納して得る完備積は、perfectoid 環への $R$-写像のうち全 $f_i$ を殺すものを表すので $B$ と単位付きで同型。各 $B_i$ による完備テンソルの単位が $M$ 上で同型なら、合成も同型になる。空の族は単位環 $R$。離散性を使うのは、既に perfectoid な係数環をテンソルする段。
- **完備忠実平坦な底変換。** $R'$ も perfectoid とする。`completedTensorBaseChangeMap_isPerfectoidization` と $(R/J)\otimes_R R'\simeq R'/JR'$ から、$B\widehat\otimes_R^L R'$ は $B'=(R'/JR')_{\mathrm{perfd}}$ の零次対象と単位付きで比較できる。係数三角形を完備底変換し、$R'\to B'$ の全射性からファイバーを零次の $K(JR')$ と同定する。これが draft の `completeBaseChangeH0` の指定射の像になる。完備テンソルの結合性で $K\widehat\otimes_R^L M$ の零性の反映に帰着し、導来 mod $p$、mod $p$ での忠実平坦性、導来 Nakayama を使う。係数の比較は draft の完備底変換の像として記述する。

C1′ の二つの往復は紙の上では既存の古典的完備テンソルで置き換えられる。Lean では、`CompletedTensor.lean` の有界上側模型が draft の `DVertex` での完備テンソルと単位・結合性を保って比較できるかを段 1 で確認する。実装候補は `BhattScholze/Almost/AlmostConnectivity.lean` と `BhattScholze/Almost/AlmostBaseChange.lean`。証明で $D(R)$ の既存 API を使い、公開型との比較には `derivedInfinityHomotopyEquivalence` を使う。型の変更が必要ならそこで報告する。

## C2　Lemma 10.12 と普遍同相

BS-W10 B-3 で実装済み。主宣言は `CommutativeAlgebra/EtaleStratification/Stratification.lean` の `exists_finiteEtaleStratification`。有限かつ有限表示の $R\to S$ と、$p$ 以外の素数が $R$ で可逆という仮定（`StrataBase p` からの代数構造で供給可能）から次を得る。

```lean
∃ (n : ℕ) (g : Fin n → R), Ideal.span (Set.range g) = ⊤ ∧
  ∀ i : Fin n,
    let I := earlierIdeal g i
    let Rᵢ := StratumRing I (g i)
    HasEtaleFactorization p (stratumMap (algebraMap R S) I (g i)) ∧
      ((p : Rᵢ) = 0 ∨ IsUnit (p : Rᵢ))
```

$I=(g_j\mid j<i)$。層は $I$ とその延長の根基で割ってから $g_i$ を反転する。`HasEtaleFactorization` は有限エタールの第一射、普遍同相の第二射、第二射の $p$ 反転後の全単射、および合成の等式を保持する。原典の層の条件と一致する。実装では有限の係数と関係式を noetherian な基底に降ろし、一般点で分解し、開上に広げて閉補集合に帰納する。 [BS 著者版 Lemma 10.12、pp. 82–83](https://people.mpim-bonn.mpg.de/scholze/prisms.pdf#page=82)

- **G-A8-4・5。** `CommutativeAlgebra/UniversalHomeomorphism/Basic.lean` の `IsUniversalHomeomorphism`、`isUniversalHomeomorphism_iff_charP`、`isUniversalHomeomorphism_bijective_of_perfect_reduced` を再利用する。標数 $p$ の判定は核が nil で、各元のある $p$ 冪が像に入ること。完全な始域から被約な終域への場合は全単射から環同型を取れる。
- **G-A8-7。** `EtaleStratification/StratumBaseChange.lean` の `hasEtaleFactorization_stratum_baseChange` と `StratumQuotient.lean` の商の場合を再利用する。前者は底変換後に各層を再び被約化する比較と、$p$ 反転後の全単射を含む。層別全体については、$g_i$ を写して単位イデアル生成と $p=0$ または可逆を移せばよい。

C2 の主張と層ごとの補題は追加 0 行。層別全体の底変換を C4 が一つの宣言として必要とする場合のみ、`EtaleStratification/` に小さな包装を検討する。全体の述語 `IsEtaleStratification` は `drafts/A8/IntegralDiscreteness.lean` に既にある。

## C3　型案と置き場所

以下の `Under (CommRingCat.of R)` は drafts の古典的な `A_R R`。特に G-A8-9・11 は添字を `Type u` に取り、対象の代数構造を `Under` の構造射から取る。いずれも CAlg_R の模型を展開せず、環、加群、$D(R)$ の宣言として置く。

| 部品 | 型案と証明の入口 | 配置候補と新規行数 |
| --- | --- | --- |
| G-A8-6 | `IsIntegralPerfectoid R p`、`[Module.Finite R T] [Algebra.Etale R T]` から `IsIntegralPerfectoid T p`。W11 の `isIntegralPerfectoid_of_finiteEtale` がこの型。 | 既存 `BhattScholze/Perfectoidization/Derived/FiniteEtalePerfectoid.lean`、0 行 |
| G-A8-8 | 任意の小さい filtered $F\colon I\to\mathrm{CommRingCat}$ と余極限錐 $c$ について、各段が perfectoid なら `IsIntegralPerfectoid (completionRing p c.pt) p`、$p^n x=0\Rightarrow px=0$、$L\Lambda_p(c.pt[0])$ の零次以外のコホモロジーの消滅。ねじれを殺す等式はある後段に移る。perfectoid 性は `Andre/Transfinite/Limit.lean` の有向系の証明を利用する。任意の filtered 添字との比較を調べ、必要なら基準段からの undercategory 上で distinguished 生成元を揃える部分を一般化する。 | 新規 `BhattScholze/Perfectoidization/Derived/PerfectoidFilteredColimit.lean`、350–750 行 |
| G-A8-9 | `[Algebra R S]` と `Algebra.IsIntegral R S` から、$S$ に向かう有限表示有限 $R$-代数の小さい filtered 図式 $F\colon I\to\mathrm{Under}(R)$ と `IsColimit`。有限個の元のモニック式と有限個の関係式で段を作り、関係式を増やして平行射を等化する。有限個の変数・関係のデータで小さい添字を作る。 | 新規 `CommutativeAlgebra/IntegralApproximation/Basic.lean`、250–450 行 |
| G-A8-11 | 整 $R$-代数 $T$ と $T[1/g]\simeq B$、$B$ は $R[1/g]$ 上有限表示。G-A8-9 と同じ形の余極限に、すべての段で標準の $A_i[1/g]\to B$ が全単射という条件を加える。draft には $T$ が整閉包、$B$ が有限エタールの場合を渡す。まず局所化が $B$ になる固定モデルを作り、各追加生成元 $y$ にモニック関係と $g^N y=a$ を課す。二対象は固定モデル上で押し出し、平行射は生成元の像の差を課して等化する。 | 新規 `CommutativeAlgebra/IntegralApproximation/FixedLocalization.lean`、250–450 行 |
| G-A8-3′ | $S[1/g]\simeq (R[1/g])^r$ から、draft の `trivialCoverComparison` と同じく $S$ と $R^r$ の像の join $S'$ を取る。`[Module.Finite R S]` から `Module.Finite R S'`、二つの射の整性と $g$ を反転したときの同型。さらに $R$ が被約かつ導来 $p$ 完備なら `IsModuleComplete R (p : R) (ModuleCat.of R S')`。座標冪等元と $S$ の生成元の積が $S'$ を生成する。有限個の分母を払い、$R/\operatorname{ann}(g)$ の有限積への線形写像の像として完備性を出す。$R/\operatorname{ann}(g)\cong\operatorname{im}(g\cdot-)$ の完備性には `isModuleComplete_ker` と `isModuleComplete_coker` を使う。 | 新規 `BhattScholze/Almost/FiniteEtaleComparison.lean`、220–400 行 |
| G-A8-3″ | 整な環準同型 $f:S\to T$ と $S[1/g]\simeq T[1/f(g)]$ から、$g$ の像が非零の任意の付値整域 $V$ への $k:S\to V$ に対し `∃! l : T →+* V, l.comp f = k`。商体へ一意に延ばし、整閉性で $V$ に戻す。階数 1・$p$ 完備の場合が `ArcOutside` の主イデアル版。一般補題に階数・完備性の仮定は要らない。 | 新規 `CommutativeAlgebra/ValuativeExtension/Localization.lean`、130–250 行 |
| G-A8-10 | $B=S_{\mathrm{red}}[1/g]$、$T\subset B$ を $R$ の整閉包、$\widehat T=\texttt{completionRing}\ p\ T$ とする。整な $S/R$ について $S\to T$ は整で、$S\to T$ と $S\to\widehat T$ は `ArcOutside`。後者は完備化の普遍性による。さらに $R$ が perfectoid、$B$ が $R[1/g]$ 上有限エタールなら $T$ の $p$ 冪ねじれは $p$ で消える。$\widehat T$ は完備で、通常の `AdicCompletion` と単位付きで同型、$L\Lambda_p(T[0])$ は離散。 | 新規 `BhattScholze/Perfectoidization/Derived/IntegralClosureCompletion.lean`、200–400 行 |

G-A8-8 の離散性は有界 $p$ ねじれから得る。G-A8-10 のねじれ評価は、BS Lemma 2.34(2) の $p$ によるねじれの零化を局所化、平坦な $R[1/g]\to B$、部分環 $T\subset B$ の順で移す。一般補題の `ArcOutside` への接続には `Derived/Interface.lean` の既存述語を使う。 [BS 著者版 Lemma 2.34、Thm 10.9、Thm 10.11](https://people.mpim-bonn.mpg.de/scholze/prisms.pdf)

### G-A8-10 の整性の範囲

W13 §0 の表の文言には $S\to\widehat T$ の整性も含まれるように読める。設計 §3.3・§4 と `drafts/A8/IntegralDiscreteness.lean` の型では整性は $S\to T$ に付き、$S\to\widehat T$ に必要なのは `ArcOutside` と完備性。次の反例があるので表は draft に揃える案とする。

$V$ を $\mathbb Q_p(p^{1/p^\infty})$ の完備化の整数環とし、$R\subset\prod_{n\ge1}V$ を $p$ 進収束列の環とする。$R$ は $p$ 正則かつ $p$ 進完備。$\varpi=p^{1/p}$ とすると、$R/\varpi$ と $R/p$ はそれぞれ $V/\varpi$、$V/p$ の最終的に定値の列の環であり、相対 Frobenius は座標ごとの同型。よって $R$ は perfectoid。 [BMS18 Lemma 3.10(ii)](https://arxiv.org/pdf/1602.03148#page=22)

$S=R$、$g=(p^n)_n$、$B=R[1/g]$ とする。$R$ は被約、$g$ は非零因子で、$B$ は $R[1/g]$ 上有限エタール。任意の $b\in\prod_n V$ について $gb$ は零に収束するので、$B\subset\prod_n\operatorname{Frac}(V)$ は $\prod_n V$ を含む。$T$ を $B$ における $R$ の整閉包とすると、座標ごとの整閉性から $T\subset\prod_n V$。

有限値の列 $b_k=(n\bmod p^k)_n$ は定数係数のモニック式を満たすので $T$ に属する。\$(b_{k+1}-b_k)/p^k$ も有限値の列で $T$ に属する。これらは $\widehat T$ の元を与え、完備な $\prod_n V$ への標準延長で $b=(n)_n$ に写る。仮に $b$ が $R$ 上整なら、そのモニック式の係数列を極限に送って得るモニック多項式は、各正整数 $m$ について $n=m+p^\ell$ の部分列から $m$ を根に持つ。標数 0 では矛盾する。したがって $\widehat T$ のこの元も $S$ 上整でない。

## 規模と段 4 の境界

- 段 1 は C1 が 500–1,100 行、C1′ が 150–400 行程度。完備圏の切り捨て・復元と完備テンソルの模型比較で幅がある。
- 段 2 は既存宣言の利用が中心。全体の包装が要る場合で 40–140 行程度。
- 段 3 は上表の合計で約 1,400–2,700 行。G-A8-9・11 の小さい添字と G-A8-8 の一般の filtered 図式が規模を左右する。
- 段 4 は `drafts/A8/AlmostPurityConnectivity.lean` と `drafts/A8/IntegralDiscreteness.lean` で古典的な入力の接続を確認する。80–200 行程度を見込む。Cor 8.12、A7、完備 filtered 余極限の perfd による保存を使う組み立てと E3 の `integral` は drafts に置く。

⑤b と ⑥ の作業差分を照合し、この報告と上の配置候補に重複は見つからなかった。本体、入口、監査にこの段で登録するモジュールはない。停止点 0 で承認を待つ。

## 段 1 の中断記録

停止点 0 の承認を含む `main` `e0d04cb21` を `math/bs-impl` に取り込んだ（`a1b817442`）。⑤b・⑥ の作業差分に予定ファイルの重複は見つからなかった。

### 比較の試行

- draft の `moduleHeartVertex` の底は `moduleFreeCochainResolution`。この解像度は正次数が零で、各項は自由、標準の増大射は擬同型。したがって `BoundedAboveDerivedModel` に同じ解像度を指定し、`boundedAboveDerivedTensorModelIso` を適用する候補を作った。両側の完備化は同じ `derivedComplexCompletionFunctor`。導来同値の余単位を合成して、draft の `completedModuleTensor` の離散な二入力での値へ比較する。
- 射の比較には `boundedAboveDerivedTensorModelIso_naturality` と `moduleFreeCochainAugmentationNat` を使う候補を作った。次に、環の標準因子写像をこの比較に通して、単位との両立を確認する。比較候補は `/tmp/bsw13-tensor-probe.lean` にある。
- 根基不変性と、perfectoid 化の核が加群を零化するときの完備テンソル消滅の候補を `/tmp/bsw13-kernel-probe.lean` に置いた。後者は一般商の Lemma 10.3 と `completedTensor_isZero_of_algebraModule` を組み合わせる。

### 検証の状態

共有ビルド鍵を取得できず、いずれの試行も型検査開始前に終了コード 75 で待ち時間切れになった。確認中に Kerodon の確認レーンと K の地図レーンが鍵を使用しており、最後の待機終了時は Kerodon の確認レーンが使用中だった。比較の成否は未判定。段 1 は未検収で、次は鍵を取得して二つの比較候補を確認する。現時点のコミット対象はこの報告だけで、本体への登録対象はない。

## 段 1 の再開と検証済みの部分

共有鍵の運用追記 `b61779518` を取り込んだ（`d699ce648`）。再開後の対象ビルド・型検査・監査は `zsh scripts/refactor/with_build_lock.sh --wait 1800 -- …` を経由した。

- `Almost/CompletedModuleTensor.lean` の `completedTensorAlgebraVertexIso` で、完備テンソルの代数模型と draft の `DVertex` の離散入力を、同じ自由解像度で比較した。二つの加群の射に関する自然性と、左右の標準因子写像が解像度の単位写像から得られる等式も証明した。`completedModuleTensor_isLE` は、半自由代表自体に有界性を仮定せず、入力のコホモロジーの上界から完備テンソルの上界を得る。
- `Almost/AlmostConnectivity.lean` で、任意のイデアル商の perfectoid 化の核、almost 零性と almost 連結性、根基不変性を定めた。核が離散加群を零化すれば完備テンソルが零になる方向は一般の perfectoid 商に対する Lemma 10.3 から得た。
- `Almost/AlmostTensor.lean` の `isAlmostZero_of_completedTensor_isZero` は Prop 10.4 の逆向き。任意の半自由代表が K-flat であることから核と商の解像度を外し、係数の短完全列を完備導来圏の三角形に移して、商環の作用を各次数に渡した。
- `Almost/AlmostGenerators.lean` の `isAlmostZero_iff_forall_gen` は draft と同じ型。導来完備なコホモロジー加群の零化イデアルによる商も導来完備であることを漸化式と余核で確認し、その商へ二つの perfectoid 商の完備テンソルから写した。この証明で使う普遍性は、通常のテンソルの零次の導来完備化への標準写像のもの。

対象ビルドは成功。上の四モジュールを対象とする段階 II 監査と同じ方式の検査は 66 宣言、標準三公理のみ。この四モジュールが入口と監査の登録候補。既存宣言の変更はなく、四モジュールの import 閉包に E3 の入力はない。

段 1 の残りは Prop 10.4 の順向き、Lemma 10.5 と G-A8-1、C1′ の底変換による反映。非有界の順向きに向け、上への切り捨ての列が元の複体を余極限として与えることまで試験用ファイルで確認した。段 1 の検収前の記録として、証明済みの部分を保存する。

### C1 の複体版と連結性

`Almost/AlmostTensorForward.lean` の `isAlmostZero_iff_completedTensor_isZero` で、Prop 10.4 の複体版を draft と同じ型で証明した。各切り捨てで、隣接段の錐を一つのコホモロジー加群と比較した。固定次数では十分低い上界から有限回進めれば消滅を示せる。非有界の場合は各冪の Koszul 簡約で逐次余極限を取り、導来完備化の消滅に戻した。

同モジュールの `isAlmostConnective_iff_completedTensor_connective` と `connective_iff_almost` で G-A8-1 の系と Lemma 10.5 を証明した。前者の順向きは正次数への切り捨てに上の消滅を適用し、逆向きは係数三角形の長完全列から商のコホモロジーへの単射を取る。後者は同じ係数三角形で連結性を移す。

登録候補に `SerrePositivity.BhattScholze.Almost.AlmostTensorForward` を追加する。五モジュールの対象ビルド成功。段階 II と同じ方式の対象監査は 186 宣言、標準三公理のみ。C1′ の完備忠実平坦な底変換での反映と、任意の filtered 準圏の余極限での almost 連結性は引き続き drafts にある。

### C1′ の底変換の残り

`completeBaseChangeH0` を既存の有界上側の底変換と同じ自由解像度で比較し、基底環の零次単位同型 `completeBaseChangeUnitIso` を得た。古典的な商の完備底変換を零次の `(R′/JR′)_perfd` と比較する `quotientBaseChangeDerivedIso` も得た。両者は `/tmp/bsw13-basechange-coefficients.lean` で型検査・公理検査済み（標準三公理）。

残る `perfectoidIdeal_baseChange` は、完備底変換した短完全列の零次の長完全列で核を同定する。指定射の像まで含めた候補は `/tmp/bsw13-basechange-probe.lean` にある。候補全体の検査は約 5 分で打ち切って共有鍵を解放したため、型検査済みなのは上記の二つの比較まで。正規化した射 `R′ → (R′/JR′)_perfd` の全射性が得られれば、標準商写像と同じ核を持つ。任意の完備複体での反映には、さらに完備底変換とテンソルの比較、および完備忠実平坦な底変換での零性の反映を接続する必要がある。

Prop 10.4 と Lemma 10.5 の係数三角形は共通化した。最新の対象監査も 186 宣言、標準三公理のみ。C2 の既存宣言は再利用できる。この段の登録候補は上記の五モジュール。C1′ の底変換による反映は drafts に残し、ここまでを段 1 の報告とする。

## 停止点 3（C3）

停止点 1 の登録までの `main`（`287fb6e70`）を `math/bs-impl` に取り込んだ。Lemma 10.12、普遍同相、有限エタール代数の perfectoid 性は既存の宣言を用いる。層別の条件はそのまま接続できるので、段 2 の包装は省いた。

| 部品 | 本体で確かめた型と証明 |
| --- | --- |
| G-A8-3′ | `Almost/FiniteEtaleComparison`。分裂後の局所化で二つの像が生成する比較環を、各成分で元の代数の像を取った直積として記述した。有限性、二つの射の整性と局所化での全単射、比較環の導来 p 完備性を証明した。完備性には有限個の分母を払う操作と、完備加群からの全射と完備加群への単射による漸化式の判定を使った。 |
| G-A8-3″・10 | `Derived/IntegralClosureCompletion`。既存の付値環への一意延長を `ArcOutside` に接続した。被約化の主局所化内の整閉包への比較は整で、整閉包とその完備化の両方への比較が `ArcOutside` を満たす。有限エタール層の平坦性で p 冪ねじれの境界を移し、導来完備化の離散性と通常完備化への単位付き同型を得た。 |
| G-A8-8 | `Derived/PerfectoidFilteredColimit`。小さい filtered 圏を Mathlib の共終な有向半順序で置き換え、一段以降で最小元を取った。元とその等式の段への降下で指定余極限を環の有向余極限と比較し、完備化の perfectoid 性、p 冪ねじれの境界、導来完備化の離散性を証明した。 |
| G-A8-9・11 | `Derived/IntegralApproximation` と `Derived/IntegralClosureApproximation`。有限個の変数と関係に各変数のモニック関係を加えた小さい有向図式を作った。G-A8-11 では局所化先の生成元と核の関係の分母を払い、指定局所化が全単射になる段を共終に取った。整閉包への特殊化では、有限エタール層の各元が基底の局所化上整であることから、分母を払って整閉包に入れた。 |

登録候補は次の五モジュール。

- `SerrePositivity.BhattScholze.Almost.FiniteEtaleComparison`
- `SerrePositivity.BhattScholze.Perfectoidization.Derived.IntegralClosureCompletion`
- `SerrePositivity.BhattScholze.Perfectoidization.Derived.PerfectoidFilteredColimit`
- `SerrePositivity.BhattScholze.Perfectoidization.Derived.IntegralApproximation`
- `SerrePositivity.BhattScholze.Perfectoidization.Derived.IntegralClosureApproximation`

共有鍵付きの対象ビルドに成功。新規モジュールを対象とした段階 II と同方式の監査は 171 宣言、標準三公理のみ。本体の既存宣言の変更と新規の `sorry` は 0。⑤b・⑥ とファイルの重複はなく、入口と共通の監査は調整役の登録に委ねる。

## 停止点 4（C4）

`drafts/A8/W13AssemblyInputs.lean` に収めた型照合を、同じ内容の試験用ファイルで共有鍵付きで検査した。分裂比較環への二つの付値環条件と完備性、整閉包の完備化への Corollary 8.12 の環論的前提、Lemma 10.12 の層別、Lemma 10.5 の帰納段を照合した。指定した局所化での全単射は、主局所化の一意性で局所化した基底上の同型になり、有限エタール性を各近似へ戻せる。

Theorem 10.9 の almost 連結性と Theorem 10.11 の組み立ては、A6・A7 の perfd を使うため引き続き `drafts/A8/AlmostPurityConnectivity.lean` と `drafts/A8/IntegralDiscreteness.lean` に置く。特に、Corollary 8.12 から almost 同型への移行、完備 filtered 余極限と perfd の比較、任意の filtered 準圏の完備余極限での almost 連結性の保存、A4 の完備入力と E3 の `integral` の接続が残る。G-A8-8 は離散な perfectoid 環の図式に使う。各有限表示有限近似で Theorem 10.9 が供給するのは almost 連結性。

C1′ の完備忠実平坦な底変換による反映も drafts に残す。段 1 で検査した単位と商の比較の次に、核と指定射の像の照合、および任意の完備複体への反映が要る。

段 4 は drafts の型照合のみ。登録候補は停止点 3 の五モジュール。
