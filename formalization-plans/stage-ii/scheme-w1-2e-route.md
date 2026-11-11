# 段 2e の作業メモ（11-10）

## 標準開の比較

- Noether 環 A 上で、P = A[X₀,…,Xᵣ] の標準次数付け、S = P/J（J は斉次イデアル）、有限生成次数付き S 加群 M を入力にする。ブローアップでは S は中心の Rees 環、M = S。Proj の標準開の被覆性は Mathlib の `Proj.affineOpenCoverOfIrrelevantLESpan` に渡せる。
- 非空の添字集合 T に対して D₊(∏ᵢ∈T xᵢ) 上の項を `(M[1/∏ᵢ∈T xᵢ])₀` とする。構造層の項と制限は `Proj.basicOpenIsoAway` と `Proj.awayMap_awayToSection` で比較する。加群では分母で次数をずらした斉次分数の表示を作り、普通の加群局所化の完全性を次数零に取る。M を P 加群として局所化した場合も、局所化の普遍性で同じ複体になる。
- 計算には狭義増加列で添字付けした有界複体を使う。全タプルの Čech 複体との比較には、昇順整列の符号と反復添字での零を使う。構造層の導来切断と比較する場合は、別に準連接層のアフィン消滅と Čech 比較が要る。2g の共通複体を全タプルのアフィン Čech で組む場合は、共通細分による比較と、射に対する整合性を確認する。有限交叉の環同型だけではこの整合性は出ない。 [Stacks 01FM](https://stacks.math.columbia.edu/tag/01FM)・[Stacks 01X8](https://stacks.math.columbia.edu/tag/01X8)
- ブローアップの有限ファイバー冪には各因子の標準開の積を使える。Segre 座標の標準開はこの積と一致する。全タプルの複体なら、Čech の面・退化の座標削除・反復が被覆の添字にも作用する。例外部分と閉厚化には同じ被覆を制限する。この特殊な図式を先に比較すれば、任意の射に対する比較の実装と切り分けられる。 [Stacks 01WD](https://stacks.math.columbia.edu/tag/01WD)
- P の捻りでは Laurent 単項式ごとに成分を分ける。指数の負の台 N を持つ単項式は T ⊇ N の項に現れる。空でも全体でもない N では、N の外の固定頂点を挿入・削除する符号付き写像で縮約する。N が空なら次数零、全体なら最上次数に寄与する。捻りを固定すると残る単項式は有限個。一般の M は有限斉次自由加群の全射とその有限生成の核を使い、被覆の長さからコホモロジー次数を下げて有限性を得る。 [Stacks 01XS](https://stacks.math.columbia.edu/tag/01XS)

有限個の捻りの自由加群へ移すときは、各成分への射影と包含の合成の和が恒等写像になることを使う。これらを標準開の局所化図式、Čech 複体、コホモロジーへ送る。元のコホモロジーから各捻りのコホモロジーの有限積への写像が単射となるので、Noether 性から有限生成になる。必要な可換性は、局所化の写像が和と合成を保つこと。

## Rees 環上の有限性と形式関数

- I ⊆ A に対して B = ⊕ₙ Iⁿ。Mathlib は `reesAlgebra I` の有限型性と Noether 性を持つ。M' = ⊕ₙ IⁿM は B[X₀,…,Xᵣ] 加群で、M の有限斉次生成元を Rees 次数零に置いて生成する。Proj 次数は変数 Xᵢ の次数から来る。IⁿM は M 内の積の像であり、Iⁿ ⊗ M からの写像の単射性を仮定する必要はない。
- チャートごとに Proj 次数零局所化と Rees 次数分解を交換する。分母は Xᵢ の積なので Rees 次数を変えない。Čech 各項が有限積なので、Rees 直和と交換できる。切断の制限も Rees 次数を保つため、Hᵠ(M') = ⊕ₙ Hᵠ(IⁿM) が B 加群として従う。B 上で射影有限性を一度適用する。 [Stacks 02O7](https://stacks.math.columbia.edu/tag/02O7)
- 有限斉次生成元の次数の上界 c を取る。Hᵠ(IⁿM) → Hᵠ(M) の像は Iⁿ⁻ᶜHᵠ(M) に入る。長完全列で、これは Hᵠ(M) → Hᵠ(M/IⁿM) の核となる。
- Kₘ = ker(Hᵠ⁺¹(IᵐM) → Hᵠ⁺¹(M)) の直和は B 部分加群なので有限斉次生成。m ≥ n + c なら、その生成元（次数 d ≤ c）に掛かる係数は Iᵐ⁻ᵈ ⊆ Iⁿ にある。したがって Hᵠ⁺¹(IᵐM) → Hᵠ⁺¹(IⁿM) の Kₘ 上の制限は、生成元ごとに Hᵠ⁺¹(M) を経由して零となる。連結写像の自然性から Hᵠ(M/IᵐM) の Hᵠ(M/IⁿM) 内の像が Hᵠ(M) からの像に一致する。
- この二式から逆極限の形式関数も得られる。BST13 Lemma 3.9 と 2f への先行出力は二式そのものにする。正次数では、中心外で零となる有限コホモロジーを I の冪が消し、Frobenius の十分高い反復が厚化を経由する。 [Stacks 02O7](https://stacks.math.columbia.edu/tag/02O7)・[BST13 Lemma 3.9](https://arxiv.org/pdf/1307.3763v3#page=12)

最初に標準開の交叉・制限を確認し、次に局所化加群の次数零部分を定義する。規模は当面 2d 報告の約 8,000–25,000 行を維持する。見積もりの幅は主に、全タプルの Čech 複体への比較と、2g での共通複体への接続に残る。

## 先行して切り出す Čech 比較補題

有限全順序集合 J に対し、添字集合 T ⊆ J ごとの加群と T ⊆ T' に対する制限写像が作る図式を入力とする。全タプル版と狭義増加タプル版の間に、次の比較を一つの補題として出す。

- 狭義増加版から全タプル版への比較 c は、重複のあるタプルを零にし、他のタプルを整列の符号で評価する。これはコチェイン写像で、係数の写像と添字の任意の写像に対して自然。狭義増加版の添字写像も、像の添字を整列し、重複のある場合は零とする。逆向きは増加タプルへの成分射影 π で、πc は恒等。自然性を必要とする 2g には c を渡す。
- ホモトピーの証明は自由整数鎖の側で行う。全タプルを生成元とし、境界は添字を一つずつ削除する交代和。整列して符号を付け、重複を零とする鎖写像 p と、増加タプルを含める鎖写像 i を作る。p の鎖写像性は隣接交換と、隣接する同じ添字を削除する二項の相殺で示す。
- 各タプル t の添字集合を T とする。T 内の全タプルの増大鎖複体は、一つの頂点 v ∈ T を先頭に付ける作用 sᵥ で縮約される。H を次数で帰納し、各 t に対して z = (id − ip)(t) − H(∂t)、H(t) = sᵥ(z) と置く。z は帰納法でサイクルなので ∂H(t) = z。H(t) の全項の添字は T に入る。増大次数で H = 0 と始めれば、この議論は次数零にも適用できる。
- 係数付きコチェインへ戻す際、H(t) に現れるタプルの添字集合は T に含まれるため、その成分を T に制限できる。制限の合成則で鎖側の恒等式がそのままコチェイン側に移る。これで c がホモトピー同値となり、係数を取り替えても使える。ホモトピーの選択には添字写像に対する自然性を要求しない。

比較の結論は Stacks 01FM と同じ。証明ではタプルごとに縮約を使い、整列の途中の置換に対する符号計算を、整列写像の鎖写像性に集約する。全タプル版の定義は Mathlib の `cechComplexFunctor` と比較する。 [Stacks 01FG](https://stacks.math.columbia.edu/tag/01FG)・[Stacks 01FM](https://stacks.math.columbia.edu/tag/01FM)

## 標準開と Laurent 単項式の実装順（11-11）

- `ProjStandardOpen` は、非空有限交叉の切断の図式を、次数零局所化の図式と自然同型にする。有限集合の包含が余面の制限を与える。加群側では `ProjectiveCechGradedLocalization` の斉次分数による写像・全射性・完全性を使う。
- 全タプル版から狭義増加版への成分射影は余境界と可換。逆向きの整列写像については、一点を削除した置換の符号の式を使う。単射なタプルではこの式で削除の順を交換する。重複のあるタプルでは、重複する二つの位置を交換する置換を使い、その二つを削除する項を相殺する。他の面は重複のため零となる。その後、整数鎖のホモトピーを有限交叉の制限写像付きコチェインに移す。
- 負の指数の台が全体より小さいとき、全タプルのコチェインでは台の外の頂点を先頭に付けて縮約する。台が空のときは増大項が通常の次数零の寄与を与える。台が全体のときは狭義増加版に移して最高次数だけに寄与する。標準開ごとに Laurent 単項式表示を作り、この縮約を有限個のタプル上で単項式ごとの直和に適用する。 [Stacks 01XS](https://stacks.math.columbia.edu/tag/01XS)

- Laurent 図式での有限性は、台が空または全体の指数だけを含む部分加群と、余境界の核の交わりからコホモロジーへの全射で示す。射影空間の捻りに移すには、各チャートの局所化同型が次数と制限を保つことを示す。有限生成次数付き加群への接続には、斉次生成元から自由表示を作り、核の次数分解と標準開の項ごとの完全性を確認する。

## 11-11 の対象検証の結果

- `projectiveModuleAwayRestriction_comp` は、分母の整除で得る局所化加群の制限の合成則。普遍性で証明した。
- `orderedCechComplex_shortExact` は、有限交叉の係数図式の短完全列から狭義増加 Čech 複体の短完全列を作る。
- `fullCechOrderedHomotopyEquiv` は、全タプル版と狭義増加版の Čech 複体のホモトピー同値。有限交叉に対する任意の加群図式で使える。
- `fullCechOrderedHomologyIso` は、同じ比較が各次数で与えるコホモロジー同型。
- `projectiveCechFinite_of_shortExact_presentations` は、コホモロジーの有限性が既知の複体による短完全表示からの降下帰納。表示の核も同じ対象の族に属することを仮定する。
- `exists_finset_homogeneous_span_top` は、有限生成次数付き加群の有限個の斉次生成元の存在。
- `projectiveGradedKernelDecomposition` は、次数を保つ加群写像の核の次数分解。

これらのモジュールを個別の対象ビルドで確認した。上の宣言のうち、制限の合成、短完全列、ホモトピー同値とコホモロジー同型、有限性の降下帰納、斉次生成元、核の次数分解を `#print axioms` で確認し、依存公理はいずれも `propext`・`Classical.choice`・`Quot.sound` のみだった。コミットは `f6015b9e1` と `faf8a15d1`。

Laurent 単項式 Čech の有限性は `projectiveLaurentCechHomology_finite` でコホモロジーの型まで接続した（`cc2fbc94a`）。`projectiveLaurentGradedLocalizationLinearEquiv` は分数の指定次数と Laurent 単項式の次数成分を同一視し、`projectiveLaurentLocalizationLinearEquiv_restriction_mk` は分母を広げる式とチャートの制限を比較する。これらを含む 2e の import 閉包のうち AlgebraicGeometry の 401 宣言を再帰的に監査し、標準三公理のみを確認した。

`projectivePolynomialTwistChartIso` は、標準開の斉次局所化の図式と Laurent 単項式の図式の自然同型。この比較を使った `projectivePolynomialTwistFullCechHomology_finite` と `projectivePolynomialTwistOrderedCechHomology_finite` を対象ビルドで確認した（`ad562e32b`・`ba15286ee`）。この時点の新しい AlgebraicGeometry の import 閉包は 465 宣言で、依存公理は標準三公理のみだった。

`projectiveOrderedCech_shortExact` は、次数を保つ短完全列から標準開の狭義増加 Čech 複体の短完全列を作る。`projectiveGradedModuleChartMap_comp`・`projectiveGradedModuleChartMap_sum` は、加群の写像の合成・有限和を標準開の図式へ移す。対象ビルドと 472 宣言の監査を通した（`85e5a1626`、標準三公理のみ）。

`projectiveGradedChartShiftIso` は整数次数のずらしを標準開の図式の自然同型にし、`projectiveShiftedPolynomialOrderedCechHomology_finite` はその Čech コホモロジーの有限性を与える。対象ビルドと 479 宣言の監査を通した（`e49220b97`、標準三公理のみ）。

`projectiveFreeOrderedCechHomology_finite` は有限個の捻りの自由加群の有限性。`projectiveGradedOrderedCechHomology_finite` と `projectiveGradedFullCechHomology_finite` は、有限斉次生成元による表示とその核に長完全列を適用し、任意の有限生成次数付き多項式加群の各 Čech コホモロジーの有限性を示す（`eaa44977f`）。加群の台の型は多項式環と同じ宇宙にそろえた。

`projectiveNatGradingIntDecomposition` と `projectiveNatGradingIntSMul` は、自然数次数の加群を負の次数で零にして整数次数へ延ばす。`projectiveNatGradedOrderedCechHomology_finite` と `projectiveNatGradedFullCechHomology_finite` で、この入力への有限性も確認した。

`projectiveHomogeneousAwayLinearEquiv` は、自然数次数の次数零斉次局所化を、環の自己加群を局所化した中の斉次分数の部分加群と比較する。`projectiveHomogeneousAwayToModule_restriction` は、この比較と標準開の制限の可換性。`projectiveScalarLocalizationLinearEquiv` と `projectiveScalarGradedAwayLinearEquiv` は、多項式環などの係数環で局所化する操作を、代数内の分母の像で局所化する操作と比較し、分子の各部分加群に制限する。

`fullCechNonemptyComplexIso` は、非空有限交叉の係数の自然同型から通常の全タプル Čech 複体の同型を作る。自然数次数の有限性、係数環の変更、非空交叉での比較は `45926c8e9`。`projectiveHomogeneousChartFullCechHomology_finite` は、これらをつないだ次数零斉次局所化の図式の有限性（`e908549f5`）。`projectiveScalarModuleAwayLinearEquiv_restriction` と `projectiveHomogeneousChartDiagram_map` は、この図式の制限を斉次局所化の環の制限と比較する（`66710c2af`）。ここまでの新しいモジュールとその import 閉包の AlgebraicGeometry の 619 宣言を監査し、標準三公理のみを確認した。

### Proj の切断への最後の比較

自然数次数の加群を、負の成分が零である整数次数の加群へ延ばす。多項式加群としての局所化は、商代数中の分母の像による環局所化と、局所化の普遍性で比較する。次数零の斉次局所化から通常の局所化への単射と、分子を斉次成分へ戻す表示で、この比較を次数零へ制限する。分母に追加因子を掛ける制限写像との可換性も確認する。

次数 q ≥ 0 の Čech 項は長さ q+1 のタプルを使い、その台は非空になる。したがって、Proj の切断との比較に使う有限交叉の自然同型は、非空の交叉で与えればよい。`SerrePositivity/AlgebraicGeometry/ProjectiveCechNonemptyComparison.lean` で、この入力から通常の全タプル複体の同型を作った。非空交叉の項と制限の比較を、コチェイン写像にまとめる補題として使える。この補題は対象ビルドと監査を通した。

`ProjectiveProjStandardSections` を対象ビルドで確認した。

- `projectiveProjStandardOpen_eq_intersection` は、分母の像の標準開を変数の像の標準開の有限交叉と同一視する。
- `projectiveProjStandardSectionIso` は、各非空有限交叉の係数環と、その上の構造層の切断の環同型。
- `projectiveProjStandardSectionIso_naturality` は、有限性を計算した係数図式の制限と、構造層の切断の制限の可換性。
- `projectiveProjStandardAffineOpenCover` は、変数の像による irrelevant ideal の生成条件を明示した標準アフィン開被覆。

これで、有限生成次数付き加群の Čech 有限性と、構造層の標準開の各項・余境界の比較を接続した。新しい 32 モジュールを `SerrePositivity/AlgebraicGeometry.lean` に登録し、同モジュールの対象ビルドを通した。2e の 627 宣言の import 閉包の監査と、既存の `scripts/audit_kst_scheme_lemmas.lean` による AlgebraicGeometry 全体の 5,044 宣言の監査は、いずれも標準三公理のみだった。

全タプル版と狭義増加版の比較は、係数の自然変換に対する自然性まで確認した。添字の任意の写像に対する整列写像の自然性は、2g で使う比較に合わせて扱う。層コホモロジーの導来関手による定義との比較は未実装。Čech モデルから BS17 へ渡す方法は、下の二案について調整役が決める。Rees 加群の有限性・評価・安定化と形式関数は、引き続き 2e で作る。

Rees 側の通常の Artin–Rees の入力には、Mathlib の `Ideal.Filtration.submodule`、`Ideal.Filtration.submodule_fg_iff_stable`、`Ideal.exists_pow_inf_eq_pow_smul` を使う。次は、基底の Rees 環上の多項式環から、拡大イデアルの Rees 環への写像と、Rees 加群の Proj 次数分解を作る。次数ごとの局所化と有限積の交換を先に示し、その後でコホモロジーとの直和の交換をつなぐ。

## Rees 側の接続（11-11）

Rees 加群の二つの次数と射影 Čech 有限性への適用まで、対象ビルドと監査を通した。次数ごとのコホモロジーの直和との比較以後は、引き続き実装する。

基底環を R、有限変数の多項式環を P = R[X₀,…,Xᵣ]、基底の中心を I、P への拡大を J とする。B = R[It] とおくと、B[X₀,…,Xᵣ] → P[Jt] は、係数を既存の `reesMap` で写し、各 Xᵢ を Rees 次数零の Xᵢ へ送る全射となる。J が I の像で生成されるので、P[Jt] の次数一の生成元もその像に入る。有限 P 加群 M の J 進 Rees 加群は P[Jt] 上有限であり、この全射による制限で B[X₀,…,Xᵣ] 上有限になる。B 上有限であるとは主張しない。

M の Proj 次数への射影は R 線形である。拡大イデアルによる JⁿM を R に制限すると IⁿM になるため、この射影は各 JⁿM を保つ。これを Rees 係数ごとに作用させ、B 線形の射影を作る。係数は有限個なので、その Proj 次数の有限台の合併を取り、Rees 加群の Proj 次数による分解を得る。各 Xᵢ がこの次数を一つ上げることから標準次数の多項式作用を作り、既存の射影 Čech 有限性を B 上で適用する。

その後、Rees 次数の直和と局所化を局所化の普遍性で交換し、Čech 項の有限積との交換を座標ごとに証明する。任意直和の完全性は Mathlib の ModuleCat の AB4 と `ShortComplex.mapHomologyIso` を使い、次数ごとの Čech コホモロジーの直和との比較へ進む。係数環を変える局所化には `IsLocalizedModule.restrictScalars_powers` を使う。比較はまず R 線形で作り、各斉次 Rees 単項式の作用との可換性を確認して B 線形の比較へ渡す。この最後の比較と Rees の斉次生成元の次数の評価を接続して初めて、形式関数に要る核の評価と像の安定化が得られる。現時点の `formalFunctions_range_eq_of_kernel_killed` などの図式追跡は、その入力を仮定する補題であり、形式関数の完成ではない。

### コホモロジーと直和の交換で残す式

各次数の複体 Cₙ の三項を `Discrete ℕ ⥤ ModuleCat R` の短複体 S としてまとめる。`ModuleCat` の AB4 により `colim` は完全なので、`S.mapHomologyIso colim` が使える。各項の余極限を `DirectSum.toModule` の普遍性で外部直和と比較し、評価関手についての `S.mapHomologyIso` と `Discrete.natIso` で、各次数のコホモロジーの直和へ移す。この手順でコホモロジーの完全性を作り直さない。

比較同型には、直和の成分包含 `lof n` と、複体への包含が誘導するコホモロジー写像の対応の式を付ける。Rees 単項式 a tⁱ は次数 n を n+i へ動かすので、同じ次数の係数写像に対する自然性だけでは足りない。複体の上で「a tⁱ の作用と第 n 成分の包含」の合成を「第 n+i 成分の包含と a の作用」に分解し、上記の対応とコホモロジーの関手性を使う。単項式の有限和へ延ばして、比較の B 線形性を示す。

### 二つの評価から完備化へ

C⁽q⁾ₙ = Hᵠ_Čech(IⁿM) とする。これらの直和が B 上有限であることを得た後、次の順に進める。

1. Hᵠ_Čech(M) 内の Fₙ = im(C⁽q⁾ₙ → C⁽q⁾₀) は I のフィルトレーションになる。有限な Rees コホモロジーからその Rees 加群への全射を作り、Mathlib の `Ideal.Filtration.submodule_fg_iff_stable` を使う。F₀ = Hᵠ_Čech(M) と安定性から、ある c に対し Fₙ ⊆ Iⁿ⁻ᶜHᵠ_Čech(M)（n ≥ c）となる。長完全列で Fₙ が厚化への写像の核であることを合わせる。
2. Kₙ = ker(C⁽q+1⁾ₙ → C⁽q+1⁾₀) の直和も、B が Noether なので有限になる。有限斉次生成元の次数を c 以下に取る。l ≥ n+c の生成元の係数は Iⁿ に属するので、C⁽q+1⁾ₖ → C⁽q+1⁾ₙ の対応する写像は、元の加群 M を経由する乗法写像へ分解する。生成元は M へのコホモロジー写像の核にいるため、Kₗ → Kₙ は零となる。長完全列の図式追跡を使い、厚化の Hᵠ の l 段から n 段への像が、Hᵠ_Čech(M) からの像と一致することを示す。
3. 二つの一様な次数の評価を使って、Hᵠ_Čech(M)/IⁿHᵠ_Čech(M) の塔と Hᵠ_Čech(M/IⁿM) の塔の極限を比較する。前者の極限は I 進完備化。核・余核が十分先の遷移で零になることを明示して極限の同型を作り、一般の導来極限の理論を重複して作らない。必要な逆極限の完全性には既存の `SerrePositivity.Cech.InverseTower` と ModuleTower の材料を照合する。

以上は Čech 版の証明手順であり、下の案 (a) の層コホモロジーとの比較や、案 (b) の降下への直接接続を代替したことにはならない。

## 11-11 Rees 部分の対象検証と監査

実装コミット：`239144d56`（16 モジュールと直接 importer、1,506 行）。2e の途中成果であり、停止点 2e ではない。

名前空間は `SerrePositivity.AlgebraicGeometry`。以下の 16 モジュールは個別の `lake env lean` と対象 `lake build` を通した。直接 importer `SerrePositivity.AlgebraicGeometry` の対象ビルドも成功。新しいモジュールの import 閉包の 835 宣言と、AlgebraicGeometry 全体の 5,218 宣言の監査は、いずれも標準三公理のみ。共有鍵は `--wait 3600` で待ち、各取得を 30 分以内に収めた。

| モジュール | 主な宣言と主張 |
|---|---|
| `ReesFiltrationModule` | `reesFiltrationDirectSumLinearEquiv`：一般のフィルトレーションの Rees 加群を次数成分の外部直和と比較。`reesFiltration_finite`：安定な場合の有限生成性。 |
| `ReesFiltrationMaps` | `reesFiltrationMap`：各段を保つ写像を Rees 線形写像へ移し、係数・単項式・合成・直和との両立性を示す。 |
| `ReesFiltrationExact` | `reesFiltrationMap_surjective`・`reesFiltrationMap_exact`：各次数の持ち上げと完全性を Rees 加群へ移す。 |
| `ReesFiltrationAdic` | `reesAdicMap_surjective`：I 進 Rees 加群の全射。`reesKernelInclusion_exact`・`reesKernelFiltration_stable`：核との交叉と安定性。 |
| `ReesFiltrationGrade` | `isInternal_reesFiltrationGrade`・`reesFiltrationGradeSMul`：Rees 次数の内部直和と斉次作用。 |
| `ReesExtendedFiltration` | `reesExtendedAdic_restrictScalars`・`reesExtendedAdic_decompose_mem`：拡大イデアルの冪を係数制限で比較し、Proj 次数への射影が各段を保つ。 |
| `ReesExtendedModule` | `reesExtendedMap`：基底環上の線形写像を係数ごとに持ち上げ、基底 Rees 環上で線形な写像を作る。 |
| `ReesProjectiveGrading` | `mem_reesProjectiveGrade_iff`・`isInternal_reesProjectiveGrade`：元の Proj 次数を、基底 Rees 環上の内部直和として持ち上げる。 |
| `ReesPolynomialBaseChange` | `reesPolynomialBaseChange_surjective`・`reesAdicPolynomialModule_finite`：B[X] から拡大中心の Rees 環への全射と、B[X] 上の Rees 加群の有限性。二つの多項式作用の scalar tower も示す。 |
| `ReesProjectiveFiniteness` | `reesProjectiveFullCechHomology_finite`：二つの次数を持つ Rees 加群の Proj 標準開 Čech コホモロジーは、B 上有限生成。 |
| `ProjectiveGradingFromVariables` | `projectiveGradedSMul_of_variables`：各標準変数が次数を一つ上げる条件から、標準次数の多項式作用を作る。 |
| `ProjectiveLocalizedDirectSum` | `projectiveLocalizedDirectSumLinearEquiv`・`projectiveLocalizationToDirectSum_naturality`：局所化と任意直和の交換、および係数写像に対する自然性。 |
| `ProjectiveDirectSumFinitePi` | `projectiveDirectSumFinitePiLinearEquiv`：任意直和と有限積の交換。係数写像に対する自然性も示す。 |
| `ProjectiveModuleScalarLocalization` | `projectiveModuleScalarLocalizationLinearEquiv`・`projectiveModuleScalarLocalizationLinearEquiv_mk`：任意の加群の局所化の係数環変更と、一般の分数の公式。 |
| `ProjectiveDirectSumCech` | `projectiveCechDirectSumComplexIso`：係数の直和の Čech 複体と、各 Čech 複体の項ごとの直和の同型。 |
| `ProjectiveFormalFunctionsBounds` | `formalFunctions_range_eq_of_kernel_killed`・`formalFunctions_eventually_injective_of_kernel_bound`：核の評価を入力にした、像の安定化の図式追跡と十分厚い商への単射性。 |

`reesProjectiveFullCechHomology_finite` の複体は、B[X] 加群としての Rees 加群から作る Proj 標準開の Čech 複体。次数ごとの Hᵠ_Čech(IⁿM) の直和との比較は、次に証明する接続である。核の評価、像の安定化、逆極限による形式関数の完成も残っている。`ProjectiveFormalFunctionsFiltration` は、この先の安定性からの評価の下書きとして作業木に置き、未検証のためコミットしていない。

## 原典の Hⁱ と Čech 版の接続（11-11、停止点報告へ引き継ぐ）

| 原典の箇所 | 定式化と、このレーンとの関係 |
|---|---|
| BS17 Lemma 2.6、Theorem 2.9 の十分性 | 前者は固有全射の幾何学的な細分と次元帰納。後者は空間値前層の降下判定。コホモロジーを使う特殊化は Lemma 4.6(i) で、fppf の RΓ の完全三角として述べる。 |
| BST13 Lemma 3.9、pp. 12–14 | Nisnevich の RΓ の完全三角。証明の正次数部分で Hⁱ_Nis(Y,O_Y/Iⁿ) の核の評価と像の安定化を使い、Frobenius 極限へ移る。 |
| Stacks 02O7、Lemma 30.20.4 と Theorem 30.20.5 | 準連接・連接層の Hⁱ と、その長完全列・完備化・逆極限で述べる。現在の版の Lemma 30.20.4(1),(3) が BST13 の引用する二式に対応する。 |

最初の行は [BS17 pp. 5–7, 16](https://arxiv.org/pdf/1507.06490#page=5)、二行目は [BST13 pp. 12–14](https://arxiv.org/pdf/1307.3763#page=12)、三行目は [Stacks 02O7](https://stacks.math.columbia.edu/tag/02O7) を照合した。原典の Hⁱ と本体の Čech 複体のコホモロジーを同定する部分は、調整役が次の二案から選ぶ。

**案 (a)**。分離的なスキーム上の準連接層について、アフィン上の導来コホモロジーの消滅と、アフィン有限交叉を持つ被覆の Čech 比較を作る。準同型と短完全列に自然な比較にして、Iⁿ、商、Frobenius の図式を移す。さらに BST13 の Nisnevich、BS17 Lemma 4.6(i) の fppf に渡す際の位相の比較を確認する。Zariski の比較の原典は [Stacks 30.2.2, 30.2.6](https://stacks.math.columbia.edu/tag/01X8)、fppf などの比較は [Stacks 35.9.3](https://stacks.math.columbia.edu/tag/0GN8)。Nisnevich の段も、準連接層のアフィン消滅と被覆の比較で接続する。

**案 (b)**。本体の主張を「射影標準開の Čech 版の形式関数・核の評価・像の安定化」と明記し、2g の最終出力 `SerrePositivity.Cech.AugmentedRingCechExact` まで直接証明する。共通アフィン細分との比較、底変換、閉厚化、Frobenius、filtered colimit との整合性を証明し、ブローアップと fppf の細分から得る二重 Čech の完全性へ渡す。この接続を実装して初めて BS17 の使用に足りると判定する。原典の導来 RΓ の主張の形式化範囲は、調整役の決定に合わせて記す。

両案で共通して使う Rees 加群・局所化・Čech 複体の代数的な補題を先に進める。現時点の宣言は `CechHomology` として明記した型を持ち、両案の選択は保留している。

宇宙の条件について、BS17 で使う有限変数多項式商・有限生成加群は多項式環と同じ宇宙に実現できる。一般の大きい型の有限生成加群も、有限変数多項式環の `Algebra.FiniteType.small` と加群の `Module.Finite.small`、`Shrink.linearEquiv` で移せるため、数学的な使い方は制限されない。添字と加群の宇宙がそれぞれ異なる場合にも、加群が基底環の宇宙で small になることを監査時の Lean の例で確認した。大きい型をそのまま渡す入口には、この同値に沿う次数分解・局所化・Čech 図式の移送を接続する作業が残る。

## 2g の被覆模型に渡す材料

### 有限型 Fₚ の段と貼り合わせ

1. 任意のアフィン v 被覆 `Spec B → Spec A` では、まず B を有限表示 A 代数の filtered colimit として表示する。有限変数集合と、それらの多項式環で成り立つ有限個の関係を添字にする。各有限表示因子は元の v 被覆で細分される。有限表示因子については、A の有限生成 Fₚ 部分代数を包含で並べ、方程式の係数を含む段を取る。等式や細分のデータも同じ系で降ろす。材料は `Algebra.FinitePresentation.iff_quotient_mvPolynomial'`、`Algebra.adjoin`、`Subalgebra.fg_iff_finiteType`、`Algebra.FinitePresentation.of_finiteType`、`Algebra.FiniteType.isNoetherianRing`。この場合の filtered 系をまとめる補題は要実装。 [BS17 Lemma 2.12](https://arxiv.org/pdf/1507.06490#page=9)
2. 一般の有限表示スキームの模型では、有限アフィン被覆、重なりの準コンパクト開、貼り合わせの射と三重交叉の等式を順に降ろす。`AffineTransitionLimit` の `exists_preimage_eq`、`exists_map_preimage_eq_map_preimage`、`Scheme.OpenCover.exists_of_isCofiltered_of_finite`、`Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`、`Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType` と `nonempty_isColimit_Γ_mapCocone` を使う。組み立てには `Scheme.GlueData.glued` と `Scheme.OpenCover.glueMorphisms` が使える。これらの足場を有限表示スキームの存在・射の降下・等式の降下にまとめる。 [Stacks 01ZM](https://stacks.math.columbia.edu/tag/01ZM)

### 固有性と全射性を同じ段にそろえる

| 材料 | 使う箇所 |
|---|---|
| 2d の `exists_preimage_eq_bot_of_isLimit` | 準コンパクト開の極限への逆像が空なら有限段で空になる。 |
| 2d の `exists_surjective_pullback_snd_of_isLimit` | Noether な段で固有性を得た直後に適用する。極限で全射ならある後の段で全射となり、固有性は基底変換で保たれる。 |
| 2d の `exists_proper_fppf_blowup_refinement_of_proper_surjective` | 固有全射を同じ段で得た後、被約基底へ引き戻し、BS17 Lemma 2.6 の帰納へ渡す。 |
| `Scheme.Pullback.range_snd`、`Scheme.Hom.isConstructible_image`、`Scheme.Hom.isConstructible_preimage` | fppf 側など固有性のない射にも全射性の降下を使う。非像を構成可能な集合として扱い、基底変換後の非像をその逆像と同定する。 |
| `WithConstructibleTopology`、`compactSpace_withConstructibleTopology`、`AlgebraicGeometry.exists_mem_of_isClosed_of_nonempty` | 前二者は構成可能な非像の逆系を扱う材料。最後の補題は Zariski 閉集合向け。アフィン段では、構成可能集合を有限個の V(J) ∩ D(g) に分け、各部分を商環の局所化の Spec として `Scheme.nonempty_of_isLimit` を適用することもできる。 |
| `isProper_eq`、`IsProper.of_comp`、`UniversallyClosed.of_comp_surjective`、`IsClosedImmersion.iff_isProper_and_mono`、`Proj.toSpecZero` の固有性 | 固有性の有限段版を作る材料。分離性は対角の閉埋め込みを降ろす。一般の 081F の経路では、初期の分離した模型の Chow 細分を取り、極限での射影空間への閉埋め込みを有限段へ降ろし、全射な細分から普遍閉性を戻す。Chow 細分と閉埋め込みの有限段への降下は別途必要。 |

作業順は、模型と可換図式、固有性、全射性、他の条件との共通段の順。fppf 因子の有限表示模型については、平坦性と全射性をそれぞれ降ろし、有向性で共通段を取る。固有性・平坦性・全射性はいずれもその後の基底変換で維持される。一般の固有射を近似する 0A0P のうち、ここでは有限表示の細分データから始めるので、有限表示の固有射を作る別の近似は要らない。 [Stacks 081F](https://stacks.math.columbia.edu/tag/081F)・[Stacks 0A0P](https://stacks.math.columbia.edu/tag/0A0P)・[Stacks 07RR](https://stacks.math.columbia.edu/tag/07RR)

### BS17 に要る射影的な細分を先に作る場合

2a 報告 §4 の構成では、初期のアフィン模型を一般平坦性で層化し、各被約層で 2d の `exists_dense_open_flat_restrict_specMap_of_finiteType` と `exists_affine_flatPure_center_of_finiteType` を使う候補がある。後者は有限型アフィン代数で使える一方、既存の `flat_strictTransformπ_specMap_of_chartPureTransform` は固有射を仮定する。この構成のアフィン v 被覆へ適用するには、その仮定を外したチャート比較、または純変換から直接平坦な閉部分を作る補題が残る。固有全射の 2d 定理を任意の v 被覆の初期模型に直接適用することはできない。

引き戻し後に稠密開の閉包を取り直し、付値環で元の v 被覆を使って平坦な部分の像を確保する。そこで得られる射影的な細分を斉次方程式で降ろせれば、固有性は `Proj.toSpecZero` と閉埋め込みから従う。その場合も全射性の有限段版には同じ 2d の宣言を使う。有限表示の閉部分への近似と、平坦な細分の模型化はこの経路でも必要。 [2a 報告 §4](scheme-w1-2a-report.md#4-段-2g--v-被覆の細分近似)・[Stacks 0ETQ](https://stacks.math.columbia.edu/tag/0ETQ)

## 対象ビルドの順番

1. 検証は `math/scheme` で共有の `scripts/refactor/with_build_lock.sh --wait 3600` を通す。11-11 の整理券方式では昼夜の順位はスクリプトが判定する。同じ worktree の待機は一つにまとめる。取得後に他の `lake build` がないことを確かめ、一回の検証は 30 分以内に収める。
2. `ProjStandardOpen` の有限交叉、環同型、制限写像の自然性を先に単体で検証する。11-11 の対象ビルドで確認済み。
3. `CechTupleContraction` の境界・先頭追加・ホモトピー方程式と、`ProjectiveCechComplex` の余境界・成分射影は対象ビルドで確認済み。`ProjectiveCechComparison` で整列写像の余境界との可換性と、全タプル版へのホモトピー同値を組む。
4. `ProjectiveCechFiniteness` の指数有限性・降下帰納と、`ProjectiveCechGradedLocalization` の斉次分数表示・完全性は対象ビルドで確認済み。次に `ProjectiveCechGradedRestriction` の制限、`ProjectiveLaurentChart` の Laurent 単項式表示・縮約・有限性を確認する。
5. `ProjectiveCechFunctor` の項ごとの完全性、`ProjectiveGradedPresentation` の斉次生成と核の次数分解、`ProjectiveCechDevissage` の長完全列による有限性の順に確認する。
6. 検証済みの下書きから `SerrePositivity/AlgebraicGeometry/` のモジュールに移し、各モジュールと直接の importer を確認する。コミットは検証が通った範囲に限る。
