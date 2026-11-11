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

全タプル版と狭義増加版の比較は、係数の自然変換に対する自然性まで確認した。添字の任意の写像に対する整列写像の自然性は、2g で使う比較に合わせて扱う。層コホモロジーの導来関手による定義との比較は未実装。Čech モデルから BS17 へ渡す方法は、scheme-w1.md §9 で案 (b) に決まった。Rees 加群の有限性・評価・安定化と形式関数は、引き続き 2e で作る。

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

`reesProjectiveFullCechHomology_finite` の複体は、B[X] 加群としての Rees 加群から作る Proj 標準開の Čech 複体。次数ごとの Hᵠ_Čech(IⁿM) の直和との比較は、次に証明する接続である。核の評価、像の安定化、逆極限による形式関数の完成も残っている。`ProjectiveFormalFunctionsFiltration` の条件付きの像の評価は、その後の案 (b) 決定後の検証で通した（下記）。実際の Čech コホモロジーの核との同定は残っている。

## 案 (b) 決定後の直和比較（11-11）

実装 `e29f8cc3d`、4 モジュールと直接 importer、357 行。対象ビルドと `SerrePositivity.AlgebraicGeometry` のビルドが成功し、AG 全体の監査は 5,285 宣言・標準三公理のみ。

- `projectiveDirectSumShortComplexHomologyIso`：ModuleCat の AB4 と `ShortComplex.mapHomologyIso` により、短複体の直和のコホモロジーを各コホモロジーの直和と比較する。
- `projectiveDirectSumColimitIso_naturality`：外部直和と離散余極限の比較は、各成分の写像に自然。
- `projectiveCechDirectSumHomologyIso`：上の比較を、既存の Čech 複体の項ごとの直和同型へ接続する。係数の直和の Čech コホモロジーと、各コホモロジーの直和の同型。
- `reesAdicProjectiveSubmodule_isHomogeneous`・`reesAdicProjectivePieceDecomposition`：各 IⁿM に元の Proj 次数を制限し、次数分解を得る。
- `reesAdicProjectivePolynomialModule_scalarTower`・`reesAdicProjectivePieceGradedSMul`・`reesAdicProjectivePolynomialModule_finite`：この制限と、多項式環の作用・次数・有限生成性の両立。
- `cechFormalFunctions_filtration_bound_of_finiteReesImage`：有限な Rees 加群から像のフィルトレーションの Rees 加群への全射を入力として、一様な I 進評価を得る。実際のコホモロジーの核の評価へ渡す全射の構成は残る。

次は直和の各成分の包含とコホモロジー同型の対応の式。Rees の局所化・Proj 次数を各 IⁿM のチャートと比較し、次数を動かす作用に対する B 線形性を示す。これらの接続、実際の核の評価、像の安定化、逆極限による形式関数は未完了。停止点 2e ではない。

§9 の条件に合わせ、既存の有限性の docstring に原典 Stacks 30.19.2/30.20.1、形式関数の図式補題に 30.20.4(1),(3) を明記した。いずれも Čech 版とし、Stacks 30.2.6 の層コホモロジーとの比較は形式化しない旨を記した。既存の 9 ファイルの変更はコメントのみで、コメントを除く宣言テキストが一致することを確認した。

## 原典の Hⁱ と Čech 版の接続（11-11、停止点報告へ引き継ぐ）

| 原典の箇所 | 定式化と、このレーンとの関係 |
|---|---|
| BS17 Lemma 2.6、Theorem 2.9 の十分性 | 前者は固有全射の幾何学的な細分と次元帰納。後者は空間値前層の降下判定。コホモロジーを使う特殊化は Lemma 4.6(i) で、fppf の RΓ の完全三角として述べる。 |
| BST13 Lemma 3.9、pp. 12–14 | Nisnevich の RΓ の完全三角。証明の正次数部分で Hⁱ_Nis(Y,O_Y/Iⁿ) の核の評価と像の安定化を使い、Frobenius 極限へ移る。 |
| Stacks 02O7、Lemma 30.20.4 と Theorem 30.20.5 | 準連接・連接層の Hⁱ と、その長完全列・完備化・逆極限で述べる。現在の版の Lemma 30.20.4(1),(3) が BST13 の引用する二式に対応する。 |

最初の行は [BS17 pp. 5–7, 16](https://arxiv.org/pdf/1507.06490#page=5)、二行目は [BST13 pp. 12–14](https://arxiv.org/pdf/1307.3763#page=12)、三行目は [Stacks 02O7](https://stacks.math.columbia.edu/tag/02O7) を照合した。以下は比較した二案の記録。11-11 の調整役の決定（scheme-w1.md §9）により案 (b) を採用し、案 (a) は実装しない。

**案 (a)、不採用**。分離的なスキーム上の準連接層について、アフィン上の導来コホモロジーの消滅と、アフィン有限交叉を持つ被覆の Čech 比較を作る。準同型と短完全列に自然な比較にして、Iⁿ、商、Frobenius の図式を移す。さらに BST13 の Nisnevich、BS17 Lemma 4.6(i) の fppf に渡す際の位相の比較を確認する。Zariski の比較の原典は [Stacks 30.2.2, 30.2.6](https://stacks.math.columbia.edu/tag/01X8)、fppf などの比較は [Stacks 35.9.3](https://stacks.math.columbia.edu/tag/0GN8)。Nisnevich の段も、準連接層のアフィン消滅と被覆の比較で接続する。

**案 (b)、採用**。本体の主張を「射影標準開の Čech 版の形式関数・核の評価・像の安定化」と明記し、2g の最終出力 `SerrePositivity.Cech.AugmentedRingCechExact` まで直接証明する。共通アフィン細分との比較、底変換、閉厚化、Frobenius、filtered colimit との整合性を証明し、ブローアップと fppf の細分から得る二重 Čech の完全性へ渡す。この接続を実装して初めて BS17 の使用に足りると判定する。原典の導来 RΓ との比較を作らず、上記の最終出力への接続を証明する。

案 (b) として、Rees 加群・局所化・Čech 複体から最終出力まで直接接続する。途中の主張は名前と docstring で Čech 版と明記する。原典の Hⁱ の番号と、Stacks 30.2.6 の比較は形式化しないことを記す。`AugmentedRingCechExact` と利用側の型は変更しない。

2g への受け渡し条件は、共通アフィン細分との比較、底変換、閉厚化、Frobenius、filtered colimit との整合性を、射に自然な形で実装すること。この五つの整合性を、単に各対象上の同型があるという主張で代用しない。

五つの整合性は次の範囲を区別して実装する。

| 整合性 | 必要な形と実装上の境界 |
|---|---|
| 共通アフィン細分 | 全タプルの Čech 複体の細分写像と合成を作る。既存の固定被覆での係数自然性だけでは、被覆の変更の比較を完了したことにはならない。 |
| 底変換 | 項・制限写像の形成を比較する。コホモロジーとの交換では平坦性など必要な仮定を明示し、一般の非平坦な底変換で Hⁱ が交換するとは述べない。平坦な底変換の増大 Čech 完全性には既存の `SerrePositivity.Cech` の API を使う。 |
| 閉厚化 | 分子の Iⁿ 倍、商の局所化、短完全列と連結写像の自然性を示す。閉厚化を平坦な底変換として処理しない。 |
| Frobenius | 分母の p 乗と同じ標準開を比較し、Iⁿ → Iᵖⁿ と Proj 次数 d → pd を追う。次数零の構造層の複体へ渡し、Fₚ 線形（基底環上では半線形）の写像とする。一般の Frobenius の平坦性は仮定しない。 |
| filtered colimit | 有限な各 Čech 項と局所化の比較、filtered 余極限の完全性を使う。最終出力の増大 Čech 完全性には既存の `isCechExact_colimit` を使い、同じ判定法を再実装しない。 |

直和のコホモロジー同型の包含の公式には、評価関手から `colim` への自然変換（各図式の `colimit.ι`）と Mathlib の `NatTrans.app_homology` が使える。これは Rees 単項式が次数を動かす作用との比較をつなぐための式になる。

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

### 完備化への写像を作る具体的な手順（案 (b)）

最後の極限比較では、`Mathlib/RingTheory/AdicCompletion/Basic` の `AdicCompletion.eval` と `AdicCompletion.transitionMap_comp_eval` を使う。一般の導来極限の完全性を新しく作る必要はない。H を固定の Čech コホモロジー、Qₙ を厚化の Čech コホモロジー、uₙ : H → Qₙ とする。IⁿH ⊆ ker uₙ により H/IⁿH → Qₙ ができ、互換な族を評価ごとに写す線形写像を作る。

一様な定数 c で ker uₙ₊꜀ ⊆ IⁿH を得たとき、この極限写像は単射になる。実際、像が零の元の第 n+c 成分の代表は ker uₙ₊꜀ に入り、その第 n 成分が零になる。代表への依存は、Iⁿ⁺ᶜH ⊆ IⁿH で消える。

全射性には像の安定化を使う。互換な族 bₙ ∈ Qₙ は十分先の bₗ の像なので、各 n で im uₙ に入る。uₙ(hₙ)=bₙ となる hₙ を選ぶ。第 n 成分を hₙ₊꜀ mod IⁿH として定めると、互換性は hₘ₊꜀−hₙ₊꜀ ∈ ker uₙ₊꜀ ⊆ IⁿH（m ≥ n）から従う。これは選択した代表によらず、元の族 bₙ を写像の像に持つ。線形性を逆写像の選択から証明せず、先に作った線形写像の全単射性から `LinearEquiv.ofBijective` を適用する。

この段も Čech 版の形式関数であり、原典 Stacks Theorem 30.20.5 の導来関手の Hⁱ との比較は含めない。共通細分等の五つの整合性については、各段の uₙ と厚化の遷移に対する可換性を先に示す。完備化の比較の自然性は、極限の各評価への合成が一致することから得る。現時点ではこの極限比較の実装と、上記二評価を実際の Čech コホモロジーで満たす証明は未完了。

## 包含・次数移動と局所化の対象検証（11-11）

実装 `3ba4d621e`。5 モジュールと直接 importer、461 行。各モジュールと `SerrePositivity.AlgebraicGeometry` の対象ビルドは成功。公式監査 `scripts/audit_kst_scheme_lemmas.lean` は **5,353 宣言・標準三公理のみ**。共有鍵 `--wait 3600` の待機は一つにまとめ、取得後の検証は一回の 30 分以内で行った。

| 宣言 | 主張 |
|---|---|
| `projectiveColimitInclusion` | 離散図式の一つの成分の評価から、余極限への自然変換。 |
| `projectiveDirectSumShortComplexInclusion` | 各短複体から、項ごとの直和の短複体への包含。 |
| `projectiveShortComplexColimitInclusion_eq` | 余極限への包含と、外部直和への包含が比較同型で一致する。 |
| `projectiveDirectSumShortComplexHomologyIso_inclusion` | Čech 版の直和コホモロジー比較は、各成分の包含を保つ。 |
| `projectiveDirectSumShortComplexHomologyIso_naturality_component` | 成分 n を別の成分 m へ送る短複体の写像にも、比較は自然。Rees 単項式の n→n+i に使える。 |
| `projectiveCechDirectSumComplexInclusion`・`projectiveCechDirectSumInclusion` | 各 Čech 複体から、項ごとの直和と係数の直和の Čech 複体への包含。 |
| `projectiveCechDirectSumHomologyIso_inclusion` | Čech 複体の包含が誘導するコホモロジー写像は、比較の下で直和の包含となる。 |
| `projectiveLocalizationToDirectSum_component` | 直和と局所化の比較は各成分への射影と可換。 |
| `projectiveLocalizedDirectSumLinearEquiv_mk_component` | 任意の分母の分数の第 n 成分は、分子の第 n 成分を同じ分母で割ったもの。 |
| `projectiveLocalizedModuleCongr`・`projectiveLocalizedModuleCongr_mk` | 加群の線形同値を局所化へ移し、一般の分数での値を計算する。 |
| `reesAdicDirectSumPolynomialLinearEquiv` | 各 IⁿM の直和と全 Rees 加群の、元の多項式環上の線形同値。 |
| `reesAdicTotalBaseModule`・`reesAdicTotalBaseModule_scalarTower` | 全 Rees 加群の基底環の作用を多項式環経由で選び、基底 Rees 環の作用との両立性を示す。 |
| `reesAdicDirectSumLinearEquiv`・`reesAdicDirectSumLinearEquiv_coeff` | 基底環上の同値と、直和の第 n 成分を Rees の第 n 係数に送る式。 |
| `reesAdicDirectSumProjectivePiece`・`reesAdicDirectSumLinearEquiv_mem_iff` | 直和上の Proj 次数を成分ごとに指定し、比較がその次数を保つことを示す。 |
| `reesAdicLocalizedDirectSumLinearEquiv` | 元の多項式環の任意の元の冪で局所化した Rees 加群を、各 IⁿM の同じ局所化の直和と比較する。 |
| `reesAdicLocalizedDirectSumLinearEquiv_mk_component` | この局所化同値は分母を保ち、分子を Rees 次数成分に分ける。 |

これはまだ停止点 2e ではない。今回の局所化同値は元の多項式環 P 上の周囲の加群の比較である。次に、基底環上に係数を制限して Proj 次数零に制限し、既存の P→B[X] の局所化の係数変更とつなぐ。局所化の比較は、各成分の射影に対する式と斉次分数表示で次数を保つ。逆方向は有限台の直和を各成分の包含に分け、各斉次分数を全 Rees 加群の同じ次数の分数に持ち上げる。

その後、標準開の制限と可換な比較を Čech 複体へ移す。次数を移す作用の自然性を使ってコホモロジー同型の B 線形性を得てから、核の評価と像の安定化に適用する。実際の Čech コホモロジーでの二評価、完備化の同型、および §9 の五つの整合性は残っている。条件付きフィルトレーションの評価を、これらの完成とは扱わない。

## 斉次局所化の直和比較と標準開の制限（11-11、続き）

`d5e67da87`（2 モジュールと直接 importer、166 行）と `3518217df`（8 モジュールと直接 importer、510 行）を保存した。前者の AG 監査は 5,377 宣言、後者は **5,436 宣言、いずれも標準三公理のみ**。各対象と直接 importer のビルドは成功した。main `7a3a0f965` を merge `da96e3024` で取り込み、17:10 追加の鍵の規則も取り込んだ。以後は一回のビルド・監査ごとに鍵を返し、編集や検討中に鍵を保持しない。以前の修正待ちを含むローカル検証用スクリプトは無効化した。

| 宣言 | 主張 |
|---|---|
| `projectiveDirectSumSubmodule` | 各成分が指定部分加群に属する、周囲の直和の部分加群。 |
| `mem_projectiveDirectSumSubmodule` | その所属を各成分で判定する。 |
| `projectiveDirectSumSubmodule_range` | 各成分の部分加群の包含の直和の像が、この部分加群となる。 |
| `projectiveDirectSumSubmoduleLinearEquiv` | 部分加群の外部直和と、周囲の直和の部分加群の線形同値。 |
| `projectiveDirectSumSubmoduleLinearEquiv_val` | 比較の周囲への値は、各成分の包含の直和。 |
| `projectiveGradedLocalizedDirectSum_map` | 局所化と直和の同値は、分子の指定部分の斉次局所化を対応させる。 |
| `projectiveGradedLocalizedDirectSumLinearEquiv` | 各成分で指定した分子の斉次局所化の直和と、周囲の直和の同じ斉次局所化の同値。 |
| `projectiveGradedLocalizedDirectSumLinearEquiv_val` | 斉次成分の比較は、周囲の局所化の比較を制限したもの。 |
| `projectiveGradedAwayCongr` | 分子の指定部分を対応させる線形同値を、斉次局所化へ移す。 |
| `projectiveGradedAwayCongr_val` | この移送は、周囲の局所化の誘導写像と同じ値を持つ。 |
| `projectiveGradedLocalizedDirectSumTransport` | 周囲の加群が直和と同値であり分子も対応するなら、その斉次局所化を各成分の斉次局所化の直和へ移せる。 |
| `reesAdicDirectSumPolynomialLinearEquiv_projective_mem` | Rees 加群の分子の Proj 次数を、各 IⁿM の同じ次数で判定する。 |
| `reesAdicGradedLocalizedDirectSumLinearEquiv` | 分母 f の第 k 冪に Proj 次数 ν k の分子を許す Rees 局所化は、各 IⁿM の同じ斉次局所化の直和と R 線形に同値。 |
| `projectiveLocalizedDirectSumLinearEquiv_restriction` | 周囲の局所化の直和比較は、分母を広げる制限写像と可換。 |
| `projectiveGradedLocalizedDirectSumLinearEquiv_component_val` | 斉次成分の比較の各成分は、周囲の局所化の同じ成分。 |
| `projectiveDirectSumSubmodule_restriction_mem` | 分母を広げる因子の冪が各分子を保つなら、その直和の分子も保つ。 |
| `projectiveGradedLocalizedDirectSumLinearEquiv_restriction` | 斉次局所化の直和比較は、標準開の制限に自然。 |
| `projectiveModuleScalarGradedAwayLinearEquiv` | 任意の加群の P 上の斉次局所化と、P→Q で分母を写した Q 上の斉次局所化を R 線形に比較する。 |
| `projectiveModuleScalarGradedAwayLinearEquiv_val` | この斉次成分の比較は、周囲の加群局所化の係数変更と同じ値。 |
| `reesPolynomialCoefficientAlgebra_scalarTower` | P→B[X] の係数変更は、基底環 R からの代数構造と両立する。 |
| `reesPolynomialBaseChange_base_scalarTower` | B[X] 上の制限した加群作用は、P を経由する R 作用と両立する。 |
| `projectiveGradedLocalizedDirectSumTransport_val` | 斉次成分の移送は、周囲の加群同値を局所化し、直和と局所化を交換したものに一致する。 |
| `projectiveGradedLocalizedDirectSumTransport_component_val` | 移送の第 n 成分を、周囲の局所化の第 n 成分で計算する。 |
| `projectiveGradedLocalizedDirectSumTransport_fraction` | 分子に逆の加群同値を適用し、同じ分母で各成分を割る、一般の斉次分数の式。 |
| `projectiveLaurentDenominator_mem_natGrade` | 標準開の分母は、反転する変数の個数の自然数次数に斉次。 |
| `projectiveNatGradedChartZero_mul_denominator` | 分母を掛けると、次数零の分子の第 k 段は第 k+1 段へ移る。 |
| `projectiveNatGradedChartZero_submodule_eq` | 自然数次数を整数次数に延ばした標準開の次数零の分子は、元の G(k·card T) の分子と一致する。 |
| `projectiveNatGradedChartZeroLinearEquiv` | 既存の標準開係数図式の次数零の対象を、G(k·card T) の斉次局所化と比較する。 |

この結果で、以前は周囲の加群だけだった Rees 局所化の比較を、指定 Proj 次数の分子へ制限した。`ν k = k·card T` と分母を変数の積に取るための、既存の自然数次数の標準開との照合もできる。一般の斉次局所化の直和比較については、標準開の制限との自然性を証明した。

まだ停止点 2e ではない。Rees 加群の P 上と B[X] 上の比較を実際の標準開係数図式へまとめ、コホモロジーの直和比較と Rees 単項式の作用をつないで B 線形性を示す接続が残る。その後、実際の Čech コホモロジーへの核の評価・像の安定化の適用と、完備化の同型へ進む。今回の局所化の係数環の変更はテンソル積による底変換の定理ではなく、§9 の五整合性の底変換を完了したことにはならない。共通アフィン細分・閉厚化・Frobenius・filtered colimit についても、引き続き §9 の条件を満たす必要がある。

### Čech コホモロジーと係数制限

`511aea3da`（新モジュールと直接 importer、60 行）で次を保存した。main 取り込み後の対象モジュールと直接 importer のビルドは成功し、別の鍵で実行した公式 AG 監査は **5,447 宣言・標準三公理のみ**だった。

- `projectiveCechRestrictScalarsComplexIso`：B 加群の係数図式の Čech 複体を R に係数制限したものと、係数図式を R に制限してから作った Čech 複体との同型。各タプルの成分の恒等同型と交代和の式で比較する。
- `projectiveCechRestrictScalarsHomologyIso`：上の複体の同型と Mathlib の係数制限の完全性・`ShortComplex.mapHomologyIso` により、Čech コホモロジーと係数制限の交換を得る。原典 Stacks 30.20.1 の Hⁱ に対応する Rees–Čech 比較の途中の入力であり、層コホモロジーの導来関手との比較は含めない。

この係数制限もテンソル積による底変換ではない。係数図式の自然変換に対するコホモロジー同型の可換式と、Rees のチャートの図式・作用への適用を次に接続する。最終出力の `AugmentedRingCechExact` の型や、その利用側の型は変更していない。

## 実際の Rees 加群の P 上の Čech 直和比較（11-11）

`1a174f6af`（6 モジュールと直接 importer、537 行）を保存。対象モジュールと直接 importer のビルドは成功し、別の鍵による公式 AG 監査は **5,498 宣言・標準三公理のみ**。監査待ちも一つにまとめた。

| 宣言 | 主張 |
|---|---|
| `projectiveCechRestrictScalarsComplexIso_naturality` | Čech 複体と係数制限の比較は、係数図式の自然変換に自然。 |
| `projectiveCechRestrictScalarsHomologyIso_naturality` | Čech コホモロジーの係数制限の比較も、係数図式の自然変換に自然。 |
| `projectiveLocalizedModuleMap_restriction` | 局所化した加群写像は、分母を広げる制限と可換。 |
| `projectiveLocalizedModuleCongr_restriction` | 加群同値の局所化も、同じ制限に自然。 |
| `projectiveGradedAwayMap_restriction` | 分子を保つ加群写像の斉次局所化は、標準開の制限に自然。 |
| `projectiveGradedAwayCongr_restriction` | 分子を対応させる加群同値の斉次局所化も、標準開の制限に自然。 |
| `projectiveGradedTransport_restriction_mem` | 各直和成分の分子が追加因子で移るなら、同値で対応する全体の加群の分子も移る。 |
| `projectiveGradedLocalizedDirectSumTransport_restriction` | 加群同値を経由した斉次局所化の直和比較全体が、標準開の制限と可換。 |
| `projectiveGradedModuleChartDirectSumIso` | 次数を対応させる直和の加群同値は、各標準開の比較を係数図式の同型にまとめる。 |
| `projectiveGradedModuleChartDirectSumCechHomologyIso` | 上の図式の同型と直和・Čech 比較により、各次数の Čech コホモロジーの直和との同型を得る。 |
| `projectiveNatGradingInt_directSum_mem_iff` | 自然数次数の直和の分子の対応は、負の次数を零に延ばしても成り立つ。 |
| `projectiveNatGradedSMul_of_directSumLinearEquiv` | 各成分の多項式の次数付き作用を、分子の次数を保つ同値で全体の加群へ移す。 |
| `projectiveNatGradedModuleChartDirectSumIso` | 自然数次数の版の、標準開の係数図式の直和との同型。 |
| `projectiveNatGradedModuleChartDirectSumCechHomologyIso` | 自然数次数の版の、Čech コホモロジーの直和との同型。 |
| `reesAdicProjectiveBaseGrade` | Rees 加群の Proj 次数の部分加群を R に係数制限したもの。 |
| `reesAdicProjectiveBaseGradedSMul` | 元の多項式環 P の作用は、この R 上の Proj 次数と両立する。 |
| `reesAdicProjectiveBaseChartDirectSumIso` | Rees 加群の P 上の標準開係数図式は、各 IⁿM の同じ図式の直和と同型。 |
| `reesAdicProjectiveBaseCechHomologyDirectSumIso` | Rees 加群の P 上の Čech コホモロジーを、各 IⁿM の同じ Čech コホモロジーの直和と R 線形に比較する。 |

これで、Rees 加群と各 IⁿM の比較を実際の標準開の係数図式と Čech コホモロジーに接続した。ただし、有限性を既に確認した B[X] 上の Čech 複体との比較、Rees 作用と直和の次数の移動との一致はまだ別の接続である。R 線形の比較だけを B 線形の比較とは呼ばない。

### Rees 作用の接続で使う既存の線形性

Mathlib の `Algebra/Homology/ShortComplex/Linear` に `ShortComplex.homologyMap_smul` と `homologyFunctor_linear` がある。複体の三項を取る関手へ戻すことで、Čech 版のコホモロジー写像のスカラー倍を追える。一般の複体の `homologyMap_smul` は `Algebra/Homology/Linear` では TODO なので、それがあるとは仮定せず、短複体の API を使う。

次の接続は、(1) P→B[X] で分母の変数の積を同定し、係数制限と可換な標準開の比較を得る、(2) その比較の係数写像に対する自然性と、Čech コホモロジーの係数制限の自然性を合成する、(3) 各次数からの包含と Rees 単項式の作用を追い、直和上の作用が n→n+i を保つことを示す、の順。この作用の確認後に、有限 Rees 加群の斉次生成元を用いる核の評価・像の安定化へ進む。

## 多項式の係数変更とスカラー作用の入力（11-11）

`fd2d691f1`（4 モジュールと直接 importer、374 行）を保存した。対象モジュールと直接 importer のビルドは成功し、別の鍵による公式 AG 監査は **5,544 宣言・標準三公理のみ**。

| 宣言 | 主張 |
|---|---|
| `projectiveModuleScalarLocalizationLinearEquiv_mk_pow` | 局所化の係数環変更は、分母の第 k 冪を像の第 k 冪へ写す。 |
| `projectiveModuleScalarLocalizationLinearEquiv_restriction` | 局所化する環の変更は、分母を広げる制限と可換。 |
| `projectiveModuleScalarGradedRestriction_mem` | 分子を追加因子で移す条件は、係数環へ写した因子でも成り立つ。 |
| `projectiveModuleScalarGradedAwayLinearEquiv_restriction` | 斉次局所化の係数環変更も、標準開の制限に自然。 |
| `projectiveModuleScalarGradedAwayLinearEquivOfEq` | 分母の像を指定した分母と同定して、斉次局所化を比較する。 |
| `projectiveModuleScalarGradedAwayLinearEquivOfEq_fraction` | 分母の同定を含む比較でも、分子と分母の冪の分数表示を保つ。 |
| `projectiveModuleScalarGradedAwayLinearEquivOfEq_restriction` | 標準分母との同定を含む比較も、標準開の制限に自然。 |
| `projectiveModuleScalarRestrictionLinearEquiv` | 互換な R 作用と B から係数制限した R 作用を、恒等写像で同一視する。 |
| `projectiveGradedFraction_restrictScalars` | 斉次分数の線形写像は係数制限と交換する。 |
| `projectiveGradedAway_restrictScalars` | 斉次局所化の部分加群は係数制限と交換する。 |
| `projectiveGradedAwayScalarRestrictionLinearEquiv` | 斉次局所化の係数制限を、R 加群としての線形同値にまとめる。 |
| `projectiveGradedAwayScalarRestrictionLinearEquiv_val` | この比較は、周囲の局所化の元を変えない。 |
| `projectivePolynomialCoefficientDenominator` | R[X]→B[X] の係数変更は、標準開の変数の積を同じ変数の積へ写す。 |
| `projectiveGradedPolynomialCoefficientChangeLinearEquiv` | 局所化する環の変更と B→R の係数制限を、各標準開で合成する。 |
| `projectiveGradedPolynomialCoefficientChangeChartIso` | 上の各標準開の比較は、制限と可換な係数図式の同型になる。 |
| `projectiveGradedPolynomialCoefficientChangeCechHomologyIso` | R[X] 上の Čech コホモロジーと、B[X] 上の Čech コホモロジーを R に係数制限したものを比較する。 |
| `projectiveCechComplexMap_smul` | 係数の自然変換のスカラー倍は、Čech 複体の写像のスカラー倍に移る。 |
| `projectiveCechHomologyMap_smul` | Čech コホモロジー写像も、係数写像のスカラー倍を保つ。 |
| `projectiveCechHomologyMap_smul_id` | 恒等係数写像のスカラー倍は、Čech コホモロジー上の元のスカラー作用を誘導する。 |

### 次の Rees への特殊化と次数移動

係数変更の一般補題は整数次数の B 部分加群 H を入力する。Rees では、H に自然数次数の `reesProjectiveGrade` を負の次数で零に延ばしたものを入れる。R への係数制限と負の次数への延長を交換する等式を、次数が非負かどうかに分けて示せば、`reesAdicProjectiveBaseCechHomologyDirectSumIso` の R 側の次数分解と同じ型になる。

P→B[X] の代数構造は、既存の `reesPolynomialCoefficientAlgebra` と今回の多項式の係数写像の代数構造が同じ定義である。加群の作用の両立性には `reesPolynomialBaseChange_source_scalarTower`・`reesPolynomialBaseChange_base_scalarTower`・`reesPolynomialBaseChange_module_scalarTower` を使う。この特殊化で、有限性を確認済みの B[X] 上の Čech コホモロジーを R に制限したものと、各 IⁿM の Čech コホモロジーの直和との R 線形な比較を合成できる。

その後、比較によって B の作用を直和へ移す。作用を移しただけでは、直和の Rees 次数に対する次数付き作用を証明したことにはならない。斉次 Rees 単項式 a·tⁱ の作用を第 n 成分の包含と合成し、第 n+i 成分への写像と一致させる。元の加群の上の入力は `reesFiltration_monomial_smul_single` と `reesMap` の単項式の公式、コホモロジーへの入力は各成分の包含の比較と、今回の `projectiveCechHomologyMap_smul_id` である。

係数変更の比較の、次数を保つ加群写像に対する自然性も合わせて接続する。これは各チャートで斉次分数を代表に取り、両辺が同じ分子の写像を持つ分数になることから示せる。こうして得た実際の次数付き B 作用と有限生成性を、像・核の Rees 加群の構成へ渡す。現時点では、この特殊化と作用の次数移動、実際の核の評価・像の安定化・完備化の同型は未完了である。

## Rees の係数環比較・移送した作用の有限性と次数間の写像（11-11）

`de30e97f1`（新規 8 モジュールと直接 importer、683 行）に保存。対象と直接 importer のビルドは成功し、別の共有鍵による公式 AG 監査は **5,663 宣言・標準三公理のみ**。このコミットは、19:15 の依頼に対する途中取り込み点 **`d63382a9b`＋報告文書 `a0c59bc4e` より後**の継続成果であり、今回選定した取り込み範囲には含めない。取り込み範囲と追加登録 78 モジュールは `scheme-w1-2e-interim-report.md` に固定してある。

有限性を確認済みの B[X] 上の Čech コホモロジーを、各 IⁿM の Čech コホモロジーの直和と R 線形に比較し、その比較で B 作用と有限性を移す。ここで B=Rees(I)、P=R[X]。また、実際の係数 a∈Iⁱ が Rees 次数 j を i+j に移す写像を、元の加群・標準開の図式・Čech コホモロジーに用意した。

| 宣言 | 主張 |
|---|---|
| `projectiveNatGradingInt_restrictScalars` | 負の次数への零延長は係数制限と交換する。 |
| `projectiveNatPolynomialCoefficientChangeChartIso` | 自然数次数の標準開の図式について、R[X] と B[X] の係数変更を R への係数制限と比較する。 |
| `projectiveNatPolynomialCoefficientChangeCechHomologyIso` | この比較を Čech コホモロジーの R 線形な同型へ移す。 |
| `reesAdicProjectiveCoefficientChartIso` | 上の標準開の比較を実際の Rees 加群へ特殊化する。 |
| `reesAdicProjectiveCoefficientCechHomologyIso` | 実際の Rees 加群の P と B[X] での Čech コホモロジーを R 上で比較する。 |
| `reesAdicProjectiveCechHomologyDirectSumIso` | B[X] 上の Rees の Čech コホモロジーを R に係数制限したものと、各 IⁿM の同じ Čech コホモロジーの直和を同定する。 |
| `projectiveScalarRestrictionTransportModule` | 係数制限した加群との R 線形同値で B 作用を移す。 |
| `projectiveScalarRestrictionTransport_scalarTower` | 移した作用は既存の R 作用と両立する。 |
| `projectiveScalarRestrictionTransportLinearEquiv` | 移した作用を用いて元の比較を B 線形同値にする。 |
| `projectiveScalarRestrictionTransportLinearEquiv_apply` | 線形同値の元への値は変わらない。 |
| `projectiveScalarRestrictionTransport_finite` | B 上の有限性も同じ比較で移る。 |
| `projectiveScalarRestrictionTransportModuleOfIso` | ModuleCat の同型から終域へ B 作用を移す。 |
| `projectiveScalarRestrictionTransportOfIso_scalarTower` | 同型による移送も R 作用と両立する。 |
| `projectiveScalarRestrictionTransportLinearEquivOfIso` | 同型による移送の B 線形同値。 |
| `projectiveScalarRestrictionTransportOfIso_finite` | 同型による移送での B 上の有限性。 |
| `reesAdicProjectiveCechObject` | B[X] 上の Rees 加群の標準開 Čech コホモロジーを B 加群の対象としてまとめる。 |
| `reesAdicCechDirectSumTransportedModule` | Rees の Čech 比較で直和に B 作用を移す。 |
| `reesAdicCechDirectSumTransportedScalarTower` | この直和の B 作用は、既存の R 作用と両立する。 |
| `reesAdicCechDirectSumTransportedLinearEquiv` | 移した作用について、直和と Rees の Čech コホモロジーは B 線形に同値。 |
| `reesAdicProjectiveCechObject_finite` | Noether な R と有限な P 加群 M に対し、Rees の Čech コホモロジーは B 上有限。 |
| `reesAdicCechDirectSumTransportedFinite` | 同じ仮定で、移した B 作用について直和が B 上有限。 |
| `reesAdicProjectiveDegreeShift_mem` | a∈Iⁱ の作用は IʲM を Iⁱ⁺ʲM に送る。 |
| `reesAdicProjectiveDegreeShift` | この作用を P 線形写像にする。 |
| `reesAdicProjectiveDegreeShift_val` | もとの加群での値は a によるスカラー倍。 |
| `reesAdicProjectiveDegreeShift_preservesPiece` | この写像は Proj 次数を保つ。 |
| `reesMap_monomial` | Rees 代数の係数環の写像は、任意の次数の斉次単項式を保つ。 |
| `reesExtendedModule_monomial_smul_single` | 基底 Rees 環の a·tⁱ が拡大 Rees 加群の第 j 単項式を第 i+j 単項式へ送る公式。 |
| `projectiveNatGradingInt_map_mem` | 自然数次数を保つ写像は、零で延ばした整数次数も保つ。 |
| `projectiveNatGradedModuleChartMap` | 自然数の Proj 次数を保つ P 線形写像を、標準開の図式間の写像にする。 |
| `projectiveNatGradedModuleCechHomologyMap` | 同じ写像を Čech コホモロジーの写像にする。 |
| `reesAdicProjectiveDegreeShiftChartMap` | a∈Iⁱ による IʲM→Iⁱ⁺ʲM の写像を標準開の図式に渡す。 |
| `reesAdicProjectiveDegreeShiftCechHomologyMap` | 同じ写像を Čech コホモロジーに渡す。 |

### できた比較と、まだ必要な照合

上の有限性は「比較によって移した B 作用について」の有限性である。この作用が直和の Rees 次数を保つこと、すなわち a·tⁱ が第 j 成分から第 i+j 成分への上記の Čech 写像を与えることは、まだ別の証明義務である。直和の各成分の包含との比較、係数環変更の比較の加群写像への自然性、および今回の単項式の公式を合成して示す。これが通るまでは、次数付き Rees 加群の有限性が完成したとは呼ばない。

その後、像のフィルトレーションへの実際の B 線形全射を作り、既存の条件付き `cechFormalFunctions_filtration_bound_of_finiteReesImage` に渡す。核の直和を次数付き B 部分加群とし、有限斉次生成元の次数の上界から遷移の零化を得て、長完全列へ接続する。像の安定化と一様な核の評価の後、互換な剰余類の持ち上げから完備化の同型を構成する。

残りの主要な群は、(1) 実際の Rees 次数作用との照合、(2) 実際の像・核の評価と像の安定化、(3) 完備化の同型、(4) §9 の共通アフィン細分・底変換・閉厚化・Frobenius・filtered colimit の自然性。**停止点 2e ではない**。最終出力と利用側の `AugmentedRingCechExact` の型は変更していない。宇宙についても、既存の `Module.Finite.small` と `Shrink.linearEquiv` による入口の方針を保つ。

## 係数比較の射への自然性と直和の包含公式（11-11）

`7a5b7573e`（新規 7 モジュールと直接 importer、608 行）に保存。対象モジュールと直接 importer のビルドは成功し、別の共有鍵による公式 AG 監査は **5,701 宣言・標準三公理のみ**。数学の宣言と主張の 18 件を以下に記す。今回も一回のビルド・一回の監査ごとに鍵を返し、待ちは一つにまとめた。

登録モジュール：`ProjectiveScalarGradedMapNaturality`、`ProjectivePolynomialCoefficientMapNaturality`、`ProjectiveCoefficientGradingCongr`、`ProjectiveGradedTransportInclusion`、`ProjectiveCechDiagramInclusion`、`ProjectiveGradedChartDirectSumInclusion`、`ProjectiveNatChartDirectSumInclusion`（いずれも `SerrePositivity.AlgebraicGeometry` の下）。

### 宣言と主張

| 宣言 | 主張 |
|---|---|
| `projectiveModuleScalarGradedAwayLinearEquivOfEq_map` | 分母の同定を含む局所化の係数環比較は、分子を保つ加群写像に自然。 |
| `projectiveGradedAwayScalarRestrictionLinearEquiv_map` | 斉次局所化の係数制限の比較も、同じ写像に自然。 |
| `projectiveGradedPolynomialCoefficientChangeLinearEquiv_map` | 各 Proj 標準開の係数環比較は、次数を保つ B[X] 線形写像と可換。 |
| `projectiveGradedPolynomialCoefficientChangeChartIso_naturality` | この可換式を標準開の係数図式間の自然変換の等式にまとめる。 |
| `projectiveGradedPolynomialCoefficientChangeCechHomologyIso_naturality` | 多項式係数環比較の Čech コホモロジーの同型も、次数を保つ写像に自然。 |
| `projectiveGradedTransportInclusion_mem` | 直和の加群同値と各成分の包含の合成は、分子の指定部分を保つ。 |
| `projectiveGradedLocalizedDirectSumTransport_inclusion` | 斉次局所化の直和比較は、局所化した各成分の包含を直和の lof に送る。 |
| `projectiveCechDirectSumDiagramInclusion` | 各係数図式から、その直和の図式への包含。 |
| `projectiveCechDirectSumDiagramInclusion_complex` | 図式の包含が誘導する Čech 写像は、既存の項ごとの直和からの包含と一致。 |
| `projectiveCechDirectSumDiagramInclusion_homology` | この図式の包含を Čech コホモロジーの直和比較に渡すと lof になる。 |
| `projectiveGradedModuleChartInclusion_mem` | 直和同値と成分の包含の合成は、整数の Proj 次数を保つ。 |
| `projectiveGradedModuleChartInclusion` | 上の合成が誘導する標準開の係数図式の包含。 |
| `projectiveGradedModuleChartDirectSumIso_inclusion` | 標準開の直和比較は、元の包含を係数図式の直和の包含に送る。 |
| `projectiveGradedModuleChartDirectSumCechHomologyIso_inclusion` | 同じ包含を Čech コホモロジーの直和比較に渡すと lof になる。 |
| `projectivePolynomialCoefficientChartIsoOfGradeEq` | 基底環上の次数を等しい族で書いた、係数比較の同型。 |
| `projectivePolynomialCoefficientChartIsoOfGradeEq_naturality` | 次数の族とその作用の証明を一緒に移すと、係数比較の射への自然性も保たれる。 |
| `projectiveNatGradedModuleChartInclusion` | 自然数の Proj 次数で、直和同値と各成分の包含を標準開へ渡す。 |
| `projectiveNatGradedModuleChartDirectSumCechHomologyIso_inclusion` | 自然数次数の Čech 直和比較も、各成分の包含を lof に送る。 |

### Rees への適用時の次数の選び方

自然数次数の係数比較の全体を、零延長と係数制限の関数の等式で移送する形は、カーネルの型検査で展開が大きくなる。この移送の自然性を試した 2 ファイルは未検証の下書きに戻し、本体にもコミットにも含めない。追加した計算量上限も本体には残していない。これは数学的な不足ではない。

Rees への特殊化では、先に B 上で Proj 次数を整数へ延ばし、その整数次数の部分加群を R へ制限して R 側の次数とする。各 IⁿM 側では元の R 上の次数を整数へ延ばす。Rees の直和同値がこれらの整数次数を対応させることは、次数が非負かどうかに分けた所属の命題として示せる。この命題と検証済みの整数次数の chart/Čech 比較を使えば、図式全体を等式で移送する操作を避けて、射への自然性と直和の包含公式をそのまま適用できる。

B 側の標準開図式は、既存の B 上の自然数次数の図式が使う整数次数への延長と同じ定義である。従って既存の Rees の Čech 有限性を使える。直和側も各 IⁿM の同じ Čech コホモロジーの直和であり、最終出力や利用側の型の変更は要らない。既存の比較の宣言と本文は変えず、この次数を選んだ自然な比較を追加して接続する。

### Rees の作用への残る適用

今回の API は、Rees の作用を追うための二つの入力（係数環比較の射への自然性、直和比較の包含との両立性）をそろえる。局所化の比較は分数の分子の写像で証明し、コホモロジーへの移送には既存の係数制限の自然性と直和比較を使う。新しく二重 Čech の議論を作っていない。

次はこれらを、実際の Rees 加群と各 IⁿM の比較へ特殊化する。その際、標準開での基底係数 b の作用が b 倍の恒等係数写像に一致することを確認し、既存の `projectiveCechHomologyMap_smul_id` に渡す。今回の包含の公式と `reesExtendedModule_monomial_smul_single`・`reesAdicProjectiveDegreeShiftCechHomologyMap` を合成すると、移した作用が第 j 成分を第 i+j 成分へ送る式に帰着する。この特殊化と作用の一致はまだ未完であり、今回の一般 API だけを Rees の次数付き作用の完成とは呼ばない。

その後の主要な群は、実際の像・核の評価と像の安定化、完備化の同型、§9 の五つの整合性。最終出力の `AugmentedRingCechExact` の型は変更せず、停止点 2e ではない。19:15 の依頼で選定した途中取り込み点 `a0c59bc4e` は変更しない。

### main の取り込みと検証入力の同一性

`61da67328` で main `375deaa6e` を `math/scheme` へ取り込んだ。検証済み AG のローカル import 閉包・Lean/Lake の設定・監査スクリプトの計 **613 ファイル**の SHA-256 を取り込み前後で比較し、不一致 **0**。従って上の対象ビルドと 5,701 宣言の監査は取り込み後にも対応する。入力に変更がないため、同じビルド・監査は繰り返していない。共有鍵の夜二枠の改定も取り込み済み。

## Rees 次数付き Čech 直和の作用と有限性（11-11）

`3704bfef8`（新規 7 モジュールと直接 importer、1,209 行）に保存。対象モジュールと直接 importer `SerrePositivity.AlgebraicGeometry` のビルドは成功し、別の共有鍵による公式監査は **5,900 宣言・標準三公理のみ**。一回のビルド・一回の監査ごとに鍵を返した。

登録モジュールは `ProjectiveGradedChartScalarAction`、`ProjectiveScalarRestrictionTransportComponent`、`ReesIntegerCechComparison`、`ReesIntegerCechInclusion`、`ReesIntegerCechAction`、`ReesIntegerCechComponentAction`、`ReesIntegerCechGradedAction`（すべて `SerrePositivity.AlgebraicGeometry` の下）。既存の宣言の型・本文は変更していない。

### 今回通った主張

P=R[Xᵢ]、B=Rees(I) とする。Proj 次数 d と Čech 次数 q を固定した外部直和

`E = ⨁ n, H_Cech^q(IⁿM; d)`

に、整数次数の自然な比較を用いて B 作用を入れた。この作用について次の式を証明した。

`(a·tⁱ) • lof_j(x) = lof_(i+j)(H_Cech^q(a : IʲM → Iⁱ⁺ʲM; d)(x))`（a∈Iⁱ）。

その結果、`range (lof_n)` による Rees 次数と `reesGrade I` の作用が両立することを `SetLike.GradedSMul` として示した。R が Noether、M が P 上有限なら、**この次数付き性を確認した同じ作用について E は B 上有限生成**。R からのスカラー塔も既存の R 作用と一致する。

以後、像・核の構成には `reesAdicCechIntegerDirectSumTransportedModule`、`reesAdicCechIntegerDirectSumGradedSMul`、`reesAdicCechIntegerDirectSumFinite` を使う。以前の `reesAdicCechDirectSumTransportedModule` は別の比較で移した作用としてそのまま残し、新旧の作用の同一性を仮定していない。

B 側では整数へ延ばした同じ部分加群を使い、R 側もその係数制限を次数として選んだ。直和との対応は所属の命題で示すので、図式全体を次数の関数の等式で移送する必要はなかった。今回の本体には計算量上限の追加はない。変数に有限な線形順序を選ぶだけで、BS17 の有限個の射影座標での利用を制限しない。宇宙も従来どおりで、大きい加群の入口は `Module.Finite.small`・`Shrink.linearEquiv` で移せる。

### 宣言と主張（ローカルな型クラス設定を除く35件）

| 宣言 | 主張 |
|---|---|
| `projectiveBaseScalarLinearMap` | 基底係数の作用を、係数環上線形な自己写像にする。 |
| `projectiveGradedAwayMap_baseScalar` | 斉次局所化でこの写像は既存の基底スカラー作用と一致。 |
| `projectiveGradedModuleChartMap_baseScalar` | 標準開の係数図式では、恒等自然変換のスカラー倍となる。 |
| `projectiveGradedModuleCechHomologyMap_baseScalar` | その Čech コホモロジー写像も、既存のスカラー作用に一致。 |
| `projectiveScalarRestrictionTransportOfIso_component_smul` | 同型で移した作用を、成分の写像の可換式から計算する一般補題。成分側には B 作用を要しない。 |
| `reesAdicProjectiveIntegerBaseGrade` | B 上で整数へ延ばしてから R に係数制限した Rees の Proj 次数。 |
| `reesAdicProjectiveIntegerBaseGrade_mem_iff` | 直和同値は、この整数次数と各 IⁿM の整数次数を対応させる。 |
| `reesAdicProjectiveIntegerBaseChartDirectSumIso` | 同じ整数次数の標準開の図式を、各 IⁿM の図式の直和と比較する。 |
| `reesAdicProjectiveIntegerBaseCechHomologyDirectSumIso` | 同じ R 上の Čech コホモロジーを、各 IⁿM のコホモロジーの直和と比較する。 |
| `reesAdicProjectiveIntegerCechHomologyDirectSumIso` | B 上の Čech コホモロジーを R へ制限したものから、上の直和への同型。 |
| `reesAdicProjectiveIntegerCoefficientInclusion` | 各 IⁿM から Rees 加群への P 線形な包含。 |
| `reesAdicProjectiveIntegerCoefficientInclusion_apply` | この包含は Rees 加群の第 n 単項式を作る。 |
| `reesAdicProjectiveIntegerChartInclusion` | その包含を標準開の係数図式へ渡す。 |
| `reesAdicProjectiveIntegerBaseChartDirectSumIso_inclusion` | 標準開の直和比較で、各次数の包含は係数図式の直和への包含になる。 |
| `reesAdicProjectiveIntegerBaseCechHomologyDirectSumIso_inclusion` | 同じ包含は、Čech コホモロジーの直和比較で lof に移る。 |
| `reesAdicProjectiveIntegerCoefficientInclusion_monomial` | 単項式の作用と各次数の包含・次数移動が作る P 線形な可換式。 |
| `reesAdicProjectiveIntegerCoefficientChartIso` | 整数の Proj 次数を固定した、R と B 上の標準開の係数比較。 |
| `reesAdicProjectiveIntegerBaseScalarChartMap` | b∈B の実際の作用が誘導する R 上の標準開図式の自己写像。 |
| `reesAdicProjectiveIntegerCoefficientChartIso_scalar` | 標準開の係数比較は、この作用を B 上のスカラー倍と対応させる。 |
| `reesAdicProjectiveIntegerCoefficientCechHomologyIso` | R と B 上の整数次数の Rees の Čech コホモロジーの比較。 |
| `reesAdicProjectiveIntegerCoefficientCechHomologyIso_scalar` | この Čech 比較も、実際の Rees スカラー作用と可換。 |
| `reesAdicProjectiveIntegerChartInclusion_monomial` | 単項式と各次数の包含の可換式を、標準開の図式へ渡す。 |
| `reesAdicProjectiveIntegerCechObject` | B 上の整数次数の Rees の Čech コホモロジーの対象。 |
| `reesAdicProjectiveIntegerCechComponentMap` | 各 IⁿM の Čech コホモロジーを、Rees の B 上の計算を R に制限した対象へ送る。 |
| `reesAdicProjectiveIntegerCechComponentMap_directSum` | この写像は、直和比較で第 n 成分の lof に移る。 |
| `reesAdicProjectiveIntegerCechComponentMap_monomial` | 単項式の作用は、この成分写像を次数 i+j の写像と対応させる。 |
| `ReesIntegerCechDirectSum` | 各 IⁿM の同じ Proj・Čech 次数のコホモロジーの外部直和。 |
| `reesAdicCechIntegerDirectSumTransportedModule` | 整数次数の比較によって、上の直和に B 作用を入れる。作用先の直和の型を明示。 |
| `reesAdicCechIntegerDirectSumTransportedScalarTower` | その B 作用は直和の既存の R 作用と両立する。 |
| `reesAdicCechIntegerDirectSumTransportedLinearEquiv` | この作用に関する、直和と B 上の Rees Čech コホモロジーとの B 線形同値。 |
| `reesAdicCechIntegerDirectSum_monomial_smul_lof` | a·tⁱ の作用は、lof_j(x) を実際の次数移動の Čech 写像の lof_(i+j) に送る。 |
| `reesAdicCechIntegerDirectSumPiece` | 外部直和の第 n 成分を、lof_n の像という R 部分加群で表す。 |
| `reesAdicCechIntegerDirectSumGradedSMul` | 上の作用は reesGrade I と外部直和の Rees 次数に関して次数付き。 |
| `reesAdicProjectiveIntegerCechObject_finite` | R が Noether、M が P 上有限なら、B 上の整数次数の Rees Čech コホモロジーは B 上有限。 |
| `reesAdicCechIntegerDirectSumFinite` | 同じ仮定で、次数付き性を確認した B 作用について外部直和が B 上有限。 |

### 次の像・核と完備化への接続

H=H_Cech^q(M;d)、αₙ:H_Cech^q(IⁿM;d)→H を包含から作り、Fₙ=range(αₙ) とする。Iⁿ⁺¹M→IⁿM の写像による減少性と、今回の係数作用の可換式による I·Fₙ⊆Fₙ₊₁ を示して I フィルトレーションにする。各 αₙ を像へ制限した全射を直和に取り、既存の `reesFiltrationDirectSumLinearEquiv` と合成すると E→Rees(F) の R 線形全射ができる。単項式での B 線形性は、今回の作用公式と `reesFiltration_monomial_smul_single` から示し、有限和へ延ばす。この実際の入力を `cechFormalFunctions_filtration_bound_of_finiteReesImage` に渡す。H の R 上の有限性は既存の射影 Čech 有限性を使う。

核では Kₙ=ker(αₙ) の成分ごとの直和を E の B 部分加群にする。今回の単項式の公式が閉性を与える。B の Noether 性と E の有限性で核も有限となり、有限生成元の各直和成分を集めて有限な斉次生成元に取り替える。その次数の上界を c とすると、l≥n+c で K_l→K_n が零になる：次数 j≤c の生成元への係数は I^(l-j) に入り、Iⁿ にも入るため、遷移は H_Cech^q(IʲM)→H_Cech^q(M) を経由して零となる。この零化と Čech 複体の短完全列の長完全列を合わせ、実際の核の評価と像の安定化を得る。

完備化では、一様な核の評価と像の安定化を使って互換な剰余類を持ち上げ、既存の I 進完備化との同型を作る。条件付きのフィルトレーション評価だけを形式関数の完成とは呼ばない。これらの構成と、§9 の共通アフィン細分・底変換・閉厚化・Frobenius・filtered colimit の自然性が残る。**停止点 2e ではない**。最終出力・利用側の `AugmentedRingCechExact` と、選定済みの途中取り込み点 `a0c59bc4e` は変更しない。


## 実際の Čech 像の Rees 加群と I 進評価（11-11）

`2f6cf60a4`（新規 7 モジュールと直接 importer、753 行）に保存。対象と直接 importer `SerrePositivity.AlgebraicGeometry` のビルドは **4,233 jobs 成功**、別の共有鍵による公式監査は **6,005 宣言・標準三公理のみ**。ビルド・監査ごとに共有鍵を取り、終了時に返した。既存宣言の型・本文は変更していない。

登録モジュールは `ReesAdicProjectiveTransition`、`ProjectiveNatGradedChartMapLaws`、`ReesAdicProjectiveCechTransition`、`ReesCechImageFiltration`、`ReesDirectSumLinearMap`、`ReesCechImageAssembly`、`ReesCechImageBounds`（すべて `SerrePositivity.AlgebraicGeometry` の下）。

### 通った主張と残る同定

αₙ:H_Cech^q(IⁿM;d)→H_Cech^q(M;d) を実際の包含から作った。Fₙ=range αₙ は減少する I フィルトレーションで、IⁿH⊆Fₙ を満たす。前節の **次数付き性を確認した同じ B 作用** の外部直和 E から Rees(F) への全射を構成し、単項式と各成分の式から B 線形性を示した。Noether 基底・多項式環上有限生成という既存の仮定の下で、Rees(F) は B 上有限生成となる。既存の条件付き評価へこの実際の全射を渡し、ある c について n≥c なら Fₙ⊆I^(n−c)H を得た。従って実際の Čech 像と I 進フィルトレーションは互いに共終である。

これは閉厚化への写像の核との同定まで済ませたという主張ではない。0→IⁿM→M→M/IⁿM→0 の Čech 長完全列による同定と、ker αₙ の遷移の一様零化・像の安定化が次に残る。零化に必要な「係数 a∈Iⁿ の次数移動の後の遷移は αⱼ を経由する」という因子分解は、係数加群と Čech コホモロジーの両方で今回証明した。完備化の同型と §9 の五つの自然性も引き続き残る。**停止点 2e ではない**。

最終出力・利用側の `AugmentedRingCechExact` と、選定済みの途中取り込み点 `a0c59bc4e` は変更しない。射影座標に有限な線形順序を選ぶことと加群の宇宙の扱いも前節のとおりで、BS17 の使い方を制限しない。

### 宣言と主張（ローカルな型クラス設定を除く48件）

| 宣言 | 主張 |
|---|---|
| `reesAdicProjectiveToModule` | 各 IⁿM から元の加群への包含。 |
| `reesAdicProjectiveSubmodule_antitone` | I 進部分加群は、指数が大きいほど小さい。 |
| `reesAdicProjectiveTransition` | IⁱM から IʲM への遷移（j≤i）。 |
| `reesAdicProjectiveTransition_val` | 遷移の元の加群での値は変わらない。 |
| `reesAdicProjectiveToModule_transition` | 遷移と元の加群への包含は可換。 |
| `reesAdicProjectiveTransition_comp` | 遷移の合成は遷移に一致。 |
| `reesAdicProjectiveToModule_degreeShift` | 次数移動後に元の加群へ含めると、基底係数のスカラー写像になる。 |
| `reesAdicProjectiveCoefficientLift` | Iⁿ の係数の作用は、元の加群から IⁿM への写像を与える。 |
| `reesAdicProjectiveToModule_coefficientLift` | 係数の持ち上げと包含の合成は、元の加群のスカラー作用。 |
| `reesAdicProjectiveTransition_degreeShift_factor` | 係数が Iⁿ に入れば、次数移動からの遷移は元の加群を経由する。 |
| `reesAdicProjectiveToModule_preservesPiece` | 元の加群への包含は Proj 次数を保つ。 |
| `reesAdicProjectiveTransition_preservesPiece` | 遷移は Proj 次数を保つ。 |
| `reesAdicProjectiveCoefficientLift_preservesPiece` | 係数の持ち上げは Proj 次数を保つ。 |
| `projectiveNatGradedModuleChartMap_id` | 自然数次数の標準開への写像は恒等写像を保つ。 |
| `projectiveNatGradedModuleChartMap_comp` | 自然数次数の標準開への写像は合成を保つ。 |
| `projectiveNatGradedModuleCechHomologyMap_comp` | 自然数次数の Čech コホモロジーへの写像も合成を保つ。 |
| `projectiveNatGradedModuleChartMap_baseScalar` | 自然数次数の標準開の図式では、基底係数の写像は恒等自然変換のスカラー倍。 |
| `projectiveNatGradedModuleCechHomologyMap_baseScalar` | 自然数次数の Čech コホモロジーで、基底係数の写像は既存のスカラー作用。 |
| `reesAdicProjectiveCechTarget` | 元の加群の、固定した Proj・Čech 次数のコホモロジーの対象。 |
| `reesAdicProjectiveCechToModule` | 各 IⁿM の Čech コホモロジーから、元の加群の同じコホモロジーへの写像。 |
| `reesAdicProjectiveCechTransition` | IⁱM→IʲM の遷移が誘導する Čech コホモロジーの写像。 |
| `reesAdicProjectiveCechCoefficientLift` | Iⁿ の係数の持ち上げが誘導する、Čech コホモロジーの写像。 |
| `reesAdicProjectiveCechToModule_transition` | Čech 遷移と元のコホモロジーへの包含は可換。 |
| `reesAdicProjectiveCechTransition_comp` | Čech 遷移の合成は、指数の合成に一致。 |
| `reesAdicProjectiveCechToModule_degreeShift` | Čech の次数移動を元のコホモロジーへ送ると、基底係数の作用になる。 |
| `reesAdicProjectiveCechToModule_coefficientLift` | 係数の持ち上げと包含は、元の Čech コホモロジーのスカラー作用を与える。 |
| `reesAdicProjectiveCechTransition_degreeShift_factor` | 十分 I 進的な係数による Čech 次数移動の遷移は、元のコホモロジーを経由。 |
| `reesAdicProjectiveCechStage` | IⁿM の、固定した Proj・Čech 次数のコホモロジーの対象。 |
| `reesAdicProjectiveCechImage` | 各 IⁿM の Čech コホモロジーからの包含の像。 |
| `reesAdicProjectiveCechImage_antitone` | Čech コホモロジーの像は、I 進指数について減少する。 |
| `reesAdicProjectiveCechImage_pow_smul_le` | Iⁱ と第 j 段の Čech 像の積は、第 i+j 段の像に入る。 |
| `reesAdicProjectiveCechImage_contains_pow` | 通常の Iⁿ 倍は、第 n 段からの Čech 像に入る。 |
| `reesAdicProjectiveCechImageFiltration` | 各 IⁿM の Čech 像からなる、元のコホモロジーの実際の I フィルトレーション。 |
| `reesAdicProjectiveCechImageStageMap` | 各段の Čech コホモロジーを、その像へ制限した線形写像。 |
| `reesAdicProjectiveCechImageStageMap_surjective` | 像へ制限した各段の Čech 写像は全射。 |
| `reesDirectSumLinearMap_smul_of_monomial_lof` | 単項式と各直和成分で作用と可換なら、すべての Rees 元の作用と可換。 |
| `reesDirectSumLinearMapOfMonomialLof` | 単項式と各成分での可換性から、同じ値の Rees 線形写像を作る。 |
| `reesDirectSumLinearMapOfMonomialLof_apply` | Rees 線形にした写像の元への値は変わらない。 |
| `reesDirectSumLinearMapOfMonomialLof_surjective` | Rees 線形にする前の写像が全射なら、そのまま全射。 |
| `reesAdicProjectiveCechImageAssembleR` | 各段の Čech 像への写像を、像の Rees 加群への R 線形写像に組む。 |
| `reesAdicProjectiveCechImageAssembleR_lof` | 一つの Čech 成分は、その像を係数とする Rees 単項式に写る。 |
| `reesAdicProjectiveCechImageAssembleR_surjective` | 各段の像への全射を組んだ R 線形写像は全射。 |
| `reesAdicProjectiveCechImageAssembleR_monomial_lof` | Čech 像への直和写像は、単項式と各成分で Rees 作用と可換。 |
| `reesAdicProjectiveCechImageAssemble` | 各段の Čech 像への写像を組んだ Rees 線形写像。 |
| `reesAdicProjectiveCechImageAssemble_surjective` | Čech コホモロジーの直和から、像の Rees 加群への Rees 線形写像は全射。 |
| `reesAdicProjectiveCechImageRees_finite` | 各 IⁿM からの Čech 像の Rees 加群は有限生成。 |
| `reesAdicProjectiveCechImage_bound` | Čech 版の実際の像の一様な I 進評価。 |
| `reesAdicProjectiveCechImage_cofinal` | Čech 像のフィルトレーションと I 進フィルトレーションは互いに共終。 |

## 実際の Čech 核の有限斉次生成元と遷移の一様零化（11-11）

`46ddda943`（新規 4 モジュールと直接 importer、409 行）に保存。対象と直接 importer `SerrePositivity.AlgebraicGeometry` のビルドは **4,237 jobs 成功**、別の共有鍵による公式監査は **6,040 宣言・標準三公理のみ**。一回のビルド・一回の監査ごとに鍵を返した。新規ファイルに `sorry`・`admit`・追加公理はなく、計算量の上限も追加していない。既存宣言の型・本文は変更していない。

登録モジュールは `LinearMapZeroOnSpan`、`ReesCechKernel`、`ReesCechKernelTransition`、`ReesCechKernelVanishing`（すべて `SerrePositivity.AlgebraicGeometry` の下）。

### 通った主張

前節の実際の Rees 全射 u:E→Rees(F) の核 K を取り、K への所属が「各直和成分 xₙ に対して αₙ(xₙ)=0」と同値であることを示した。従ってこれは実際の ker αₙ の直和であり、B 部分加群である。K は一つの直和成分に入れた核の元で生成され、Noether 基底・M の多項式環上の有限性の下で、有限個の斉次生成元を選べる。その Rees 次数には共通の上界 c がある。

次数 j≤c の生成元の単項式 a·tⁱ 倍の第 l 成分を見ると、i+j=l の場合だけ寄与する。l≥n+c なら i≥n なので、前節の因子分解により IˡM→IⁿM の Čech 写像は αⱼ を経由し、生成元が核にあることから零となる。任意の Rees 係数は単項式の有限和に分け、さらに生成部分加群へ加法的に延ばした。**遷移そのものを B 線形とは仮定していない**。これにより、実際の写像について次を得た。

`∃ c, ∀ n l≥n+c, ∀ x∈ker α_l, H_Cech^q(IˡM→IⁿM;d)(x)=0`。

有限生成元を選ぶ段と、与えられた次数上界から零化する段を別の補題に分けた結果、既定の計算量内で通った。これは Stacks 30.20.4(3) の Hⁱ の像の安定化に渡す **Čech 版の核の零化** である。

### main の取り込みと残り

`b4ea18add` で main `6b91dab00` を `math/scheme` に取り込んだ。検証済み AG のローカル import 閉包・Lean/Lake 設定・監査スクリプトの **631 ファイル**の SHA-256 を比較し、不一致 **0**。従って上の対象ビルドと 6,040 宣言の監査は取り込み後にも対応し、入力が同じビルド・監査は繰り返していない。

残りの主要な群は三つ：閉厚化の短完全列と Čech 長完全列の自然性によって実際の核の評価・像の安定化へ渡すこと、完備化の同型、§9 の五つの整合性。全タプル Čech 複体の短完全性の未検証下書きを `scheme-drafts/ProjectiveFullCechExact.lean` に用意しているが、本体への登録・コミットには含めていない。**停止点 2e ではない**。最終出力と利用側の `AugmentedRingCechExact`、選定済みの途中取り込み点 `a0c59bc4e` は変更しない。

### 宣言と主張（ローカルな型クラス設定を除く17件）

| 宣言 | 主張 |
|---|---|
| `linearMap_zero_on_span_of_smul_generators` | 生成元のすべての B 倍で零なら、R 線形写像はその B 生成部分加群で零。 |
| `reesAdicProjectiveCechKernel` | Čech 像への Rees 全射の核。各段の包含の核をまとめる。 |
| `reesAdicProjectiveCechKernel_mem_iff` | Rees 核への所属は、各成分が実際の Čech 包含で零になることと同値。 |
| `reesAdicProjectiveCechKernel_lof_mem_iff` | 一つの斉次成分の Rees 核への所属は、その Čech 包含での零化と同値。 |
| `reesAdicProjectiveCechKernelHomogeneous` | 各段の実際の Čech 核の元を、一つの直和成分に入れた集合。 |
| `reesAdicProjectiveCechKernel_span_homogeneous` | 実際の Čech 核の Rees 加群は、その斉次な核の元で生成される。 |
| `reesAdicProjectiveCechKernel_finite` | Čech 核の Rees 加群は有限生成。 |
| `reesAdicProjectiveCechKernel_finite_homogeneous_generators` | 実際の Čech 核には有限個の斉次生成元を選べる。 |
| `reesAdicProjectiveCechTransition_mem_kernel` | 各段の Čech 包含の核は、I 進遷移で保たれる。 |
| `reesAdicProjectiveCechTransition_degreeShift_zero` | 十分 I 進的な係数による次数移動は、Čech 核の元の遷移を零にする。 |
| `reesAdicProjectiveCechKernel_bounded_homogeneous_generators` | 実際の Čech 核は、次数に一様な上界のある有限個の斉次元で生成される。 |
| `reesAdicProjectiveCechTransitionComponent` | 直和の第 l 成分を取り、そこから第 n 段へ遷移する R 線形写像。 |
| `reesAdicProjectiveCechTransitionComponent_monomial_kernel_zero` | 十分高い次数の成分の遷移は、低次数の斉次核の元の単項式倍で零。 |
| `reesAdicProjectiveCechTransitionComponent_smul_kernel_zero` | 同じ成分の遷移は、低次数の斉次核の元の任意の Rees 倍で零。 |
| `reesAdicProjectiveCechTransitionComponent_zero_of_span` | 低次数の斉次核で生成した Rees 部分加群では、十分先の成分の遷移は零。 |
| `reesAdicProjectiveCechKernel_transition_zero_of_bounded_generators` | 次数が c 以下の斉次核で生成されれば、c だけ遅らせた核の遷移は零。 |
| `reesAdicProjectiveCechKernel_transition_eventually_zero` | 実際の Čech 包含の核の遷移は、一様に遅らせれば零になる。 |

## 実際の閉厚化の Čech 長完全列と核の評価（11-11）

`bf864a77e`（新規 6 モジュールと直接 importer、501 行）に保存。対象と直接 importer `SerrePositivity.AlgebraicGeometry` のビルドは **4,243 jobs 成功**、別の共有鍵による公式監査は **6,103 宣言・標準三公理のみ**。

登録モジュールは `ProjectiveFullCechExact`、`ProjectiveFullGradedCechExact`、`ProjectiveNatCechExact`、`ReesAdicProjectiveQuotient`、`ReesAdicProjectiveClosedCech`、`ReesClosedCechHomology`。全タプル Čech の短完全性の下書きを本体へ移し、整数次数・自然数次数の斉次短完全列に適用した。商の次数分解は既存の `HilbertSerre.isInternal_quotientGrade` を再利用した。

Qₙ=M/IⁿM を実際の商加群として作り、0→IⁿM→M→Qₙ→0 の標準開の全タプル Čech 複体の短完全列を得た。Mathlib の長完全列を使い、包含・射影・連結写像の三か所の完全性を示した。その結果、射影 πₙ:H_Cech^q(M;d)→H_Cech^q(Qₙ;d) の核が、前節の実際の像 Fₙ と等しいことが分かった。従って **実際の閉厚化への Čech 写像の核** について、ある c とすべての n≥c で ker πₙ⊆I^(n−c)H_Cech^q(M;d) を得た。これは Stacks 30.20.4(1) の Hⁱ の核の評価に対応する Čech 版であり、像を核と同定する仮定は残っていない。

### 宣言と主張（ローカルな型クラス設定を除く27件）

| 宣言 | 主張 |
|---|---|
| `fullCechComplexFunctor_preservesZeroMorphisms` | 全タプル Čech 関手は零射を保つ。 |
| `fullCechComplex_shortExact` | 各交叉の係数列が短完全なら、全タプル Čech 複体の列も短完全。 |
| `projectiveFullCech_shortExact` | 斉次な短完全列は標準開の Čech 複体でも短完全となる。 |
| `projectiveNatFullCech_shortExact` | 自然数次数を保つ短完全列は、全タプル標準開 Čech 複体でも短完全。 |
| `reesAdicProjectiveQuotient` | I 進閉厚化の実際の商加群 M/IⁿM。 |
| `reesAdicProjectiveQuotientPolynomialModule` | 同じ商加群の、多項式環上の加群構造。 |
| `reesAdicProjectiveQuotientPolynomialModule_scalarTower` | 商における基底作用と多項式作用の両立性。 |
| `reesAdicProjectiveQuotientProjection` | 閉厚化の商への、多項式環上線形な射影。 |
| `reesAdicProjectiveQuotientProjection_surjective` | 閉厚化の商への射影は全射。 |
| `reesAdicProjectiveToModule_quotientProjection_exact` | IⁿM の包含と、閉厚化の商への射影は完全。 |
| `reesAdicProjectiveQuotientPiece` | I 進閉厚化の商の Proj 次数成分。 |
| `reesAdicProjectiveQuotientPieceDecomposition` | I 進閉厚化の商は、元の Proj 次数の分解を受け継ぐ。 |
| `reesAdicProjectiveQuotientProjection_preservesPiece` | 商への射影は Proj 次数を保つ。 |
| `reesAdicProjectiveQuotientPieceGradedSMul` | 閉厚化の商の次数と、多項式の次数の作用は両立する。 |
| `reesAdicProjectiveCechInclusionChartMap` | IⁿM の包含から得られる、標準開の係数図式の写像。 |
| `reesAdicProjectiveClosedCechProjectionChartMap` | 実際の閉厚化の商への射影が誘導する、標準開の係数図式の写像。 |
| `reesAdicProjectiveClosedCech_shortExact` | 実際の I 進閉厚化の列は、標準開の全タプル Čech 複体でも短完全。 |
| `reesAdicProjectiveClosedCechShortComplex` | 実際の I 進閉厚化の全タプル Čech 複体からなる短複体。 |
| `reesAdicProjectiveClosedCechShortComplex_shortExact` | 実際の閉厚化から作った Čech の短複体は短完全。 |
| `reesAdicProjectiveClosedCechHomology` | 実際の閉厚化 M/IⁿM の全タプル Čech コホモロジーの対象。 |
| `reesAdicProjectiveClosedCechProjection` | 実際の閉厚化への射影が誘導する Čech コホモロジーの写像。 |
| `reesAdicProjectiveClosedCechConnecting` | 実際の閉厚化の Čech 長完全列の連結写像。 |
| `reesAdicProjectiveClosedCech_exact_middle` | 元の加群の Čech コホモロジーにおける、閉厚化の長完全列の完全性。 |
| `reesAdicProjectiveClosedCech_exact_projection_connecting` | 閉厚化の Čech コホモロジーにおける、長完全列の完全性。 |
| `reesAdicProjectiveClosedCech_exact_connecting_inclusion` | 次の次数の Čech コホモロジーにおける、長完全列の完全性。 |
| `reesAdicProjectiveClosedCechProjection_ker_eq_image` | 実際の閉厚化への Čech 写像の核は、IⁿM の Čech 包含の像に等しい。 |
| `reesAdicProjectiveClosedCechProjection_kernel_bound` | 実際の閉厚化への Čech 写像の核の一様な I 進評価。 |

## 閉厚化の Čech 遷移の自然性と実際の像の安定化（11-11）

`87f64753d`（新規 3 モジュールと直接 importer、268 行）に保存。対象と直接 importer `SerrePositivity.AlgebraicGeometry` のビルドは **4,251 jobs 成功**、別の共有鍵による公式監査は **6,133 宣言・標準三公理のみ**。

登録モジュールは `ReesAdicProjectiveQuotientTransition`、`ReesClosedCechTransition`、`ReesClosedCechStabilization`。実際の商 Qᵢ→Qⱼ（j≤i）を作り、IⁱM→IʲM、M の恒等写像、Qᵢ→Qⱼ から、先ほどの Čech 短完全列の間の射を構成した。係数写像の合成則から両方の四角形を示し、連結写像の自然性は Mathlib の `HomologySequence.δ_naturality` を使った。

次の Čech 次数 q+1 での ker α_l→ker α_n の一様零化を、既存の `formalFunctions_range_eq_of_kernel_killed` の **実際の入力** に渡した。その結果、ある c が存在して l≥n+c なら、H_Cech^q(Q_l;d)→H_Cech^q(Q_n;d) の像は H_Cech^q(M;d)→H_Cech^q(Q_n;d) の像と等しい。従ってこの逆系は像が安定する。これは Stacks 30.20.4(3) の Hⁱ の主張の Čech 版であり、条件付きの図式追跡だけではなく、上に構成した実際の商・写像・長完全列について証明済み。

### 宣言と主張（ローカルな型クラス設定を除く11件）

| 宣言 | 主張 |
|---|---|
| `reesAdicProjectiveQuotientTransition` | 閉厚化の実際の商加群の間の、多項式環上線形な I 進遷移。 |
| `reesAdicProjectiveQuotientTransition_projection` | 商への射影は、閉厚化の I 進遷移と可換。 |
| `reesAdicProjectiveQuotientTransition_preservesPiece` | 閉厚化の商の遷移は、Proj 次数を保つ。 |
| `reesAdicProjectiveCechTransitionChartMap` | IⁱM→IʲM の写像が誘導する、標準開の係数図式の遷移。 |
| `reesAdicProjectiveClosedCechTransitionChartMap` | 閉厚化の商の間の写像が誘導する、標準開の係数図式の遷移。 |
| `reesAdicProjectiveClosedCechShortComplexMap` | 閉厚化の Čech 短完全列の間の、I 進遷移による射。 |
| `reesAdicProjectiveClosedCechTransition` | 実際の閉厚化の Čech コホモロジーの間の I 進遷移。 |
| `reesAdicProjectiveClosedCechTransition_projection` | 閉厚化への Čech 射影は、I 進遷移と可換。 |
| `reesAdicProjectiveClosedCechTransition_connecting` | 閉厚化の Čech 連結写像は、I 進遷移と可換。 |
| `reesAdicProjectiveClosedCechTransition_range_eq_of_kernel_killed` | 次の次数の Čech 核が遷移で零になれば、実際の閉厚化の像は元の像に一致。 |
| `reesAdicProjectiveClosedCechTransition_range_stabilizes` | 実際の閉厚化の Čech コホモロジーの像は、一様に遅らせれば安定する。 |

### 完備化への次の接続と残り

H=H_Cech^q(M;d)、Fₙ=ker πₙ とすると、H/Fₙ は range πₙ と自然に同型である。互換な Qₙ の Čech コホモロジーの族は、各 n で十分先の項から来るので、今回の像の安定化により range πₙ に入る。このため、その互換族を H/Fₙ の互換族と同一視できる。一方 IⁿH⊆Fₙ と F_(n+c)⊆IⁿH の共終性から、H/Fₙ の互換族と Mathlib の `AdicCompletion I H` を比較する。Mathlib の `AdicCompletion.submodule`・`incl`・`eval` は既に互換剰余類の族を与えるので、別の完備化を定義しない。商遷移の恒等・合成則と、この同型の評価写像による特徴付けを次に作る。

残りの主要な群は **完備化の同型と、§9 の五つの整合性の二群**。核の一様評価と像の安定化は、実際の閉厚化について今回までに証明した。一般の固有射のコホモロジー有限性や、導来関手の Hⁱ との比較へは広げない。加群の宇宙と有限な座標の順序は前節の扱いを保ち、BS17 での利用を制限しない。

両コミットの追加に `sorry`・`admit`・追加公理・計算量上限の追加はなく、既存宣言の型・本文は変更していない。全ビルド・全監査は共有の鍵 `--wait 3600` を一回の実行ごとに取り、終了時に返した。ルート全体のビルドは行っていない。**停止点 2e ではない**。最終出力と利用側の `AugmentedRingCechExact`、選定済みの途中取り込み点 `a0c59bc4e` は変更しない。

## 途中取り込み点の更新と、実際の Čech 形式関数の完備化同型（11-11）

調整役の 22:15 の連絡により、**途中取り込み点は `9e78e7dc0` に更新され、main `f654cdc11` に取り込まれた**。上の各節の `a0c59bc4e` は、更新前に選定した点の歴史的な記録である。今回 `math/scheme` も main `f654cdc11` まで fast-forward し、検証済み AG の閉包・Lean/Lake 設定・監査スクリプトの **640 ファイルの SHA-256 の不一致 0** を確認した。調整役のルート全体の検証結果を、こちらの検証としては数えていない。

### 完備化の同型

`b65e5c6bc`（新規 6 モジュールと直接 importer、425 行）に保存。対象と直接 importer `SerrePositivity.AlgebraicGeometry` のビルドは **4,257 jobs 成功**、別の共有鍵による公式監査は **6,198 宣言・標準三公理のみ**。登録モジュールは `LinearCompatibleFamilies`、`LinearRangeDescent`、`AdicProjectionFactor`、`AdicProjectionInverseComponents`、`AdicProjectionCompletionInverse`、`ReesClosedCechCompletion`。

実際の Čech 射影 πₙ:H→Qₙ（ここで H=H_Cech^q(M;d)、Qₙ=H_Cech^q(M/IⁿM;d)）を使い、次の線形同型を構成した。

`reesAdicProjectiveClosedCechCompletionLinearEquiv : AdicCompletion I H ≃ₗ[R] {x : ∀ n, Qₙ // ∀ i j (h:j≤i), tᵢⱼ(xᵢ)=xⱼ}`。

これは Stacks 30.20.5 の Hⁱ の形式関数の **Čech 版**。導来関手の Hⁱ との比較は形式化していない。基底の Noether 性、M の多項式環上の有限生成性、有限な座標と次数分解という、これまでと同じ仮定を使う。大きい型の入口は従来の `Module.Finite.small`・`Shrink.linearEquiv` の方針を保ち、BS17 での利用を制限しない。

順写像は πₙ を H/IⁿH 上へ降ろし、Mathlib の完備化を第 n 成分で評価する。逆写像は、ker π_(n+c)⊆IⁿH によって range π_(n+c)→H/IⁿH を作り、互換族の n+c 成分へ適用する。各成分が射影の像に入ることは、証明済みの像の安定化から得た。代表によらない降下には核による商と像の標準同型を使い、逆写像の互換性と両方の合成の恒等性は、同じ代表を遷移で移して示した。

同型の順写像は、核の評価で選ぶ c によらない **標準写像そのもの** として等しい。加群の元 m を完備化に送って第 n 成分で評価すると、πₙ(m) になる。この評価式も証明済み。新しい完備化を定義せず、Mathlib の `AdicCompletion` をそのまま使っている。

### 宣言と主張（30件）

| 宣言 | 主張 |
|---|---|
| `compatibleLinearFamilies` | 線形な遷移写像に関する互換族の部分加群。 |
| `compatibleLinearFamiliesEval` | 互換族を第 n 成分で評価する線形写像。 |
| `linearRangeDescent` | ker f⊆ker g なら、g を f の像から降ろせる。 |
| `linearRangeDescent_rangeRestrict` | 像から降ろした写像を元の代表で計算する。 |
| `adicProjectionQuotientMap` | IⁿH を殺す射影を、通常の I 進剰余類上へ降ろす。 |
| `adicProjectionQuotientMap_mk` | I 進剰余類上の射影は、代表上で元の射影と一致。 |
| `adicProjectionQuotientMap_transition` | 射影の互換性は、I 進剰余類からの写像にも降りる。 |
| `adicProjectionCompletionMap` | I 進完備化から、射影先の互換族への標準線形写像。 |
| `adicProjectionCompletionMap_of_apply` | 標準写像を加群の元に評価すると、元の射影の族になる。 |
| `adicProjectionImageToQuotient` | 十分先の射影の像から、元の加群の Iⁿ による商への線形写像。 |
| `adicProjectionImageToQuotient_rangeRestrict` | 像から I 進剰余類への写像は、元の代表をそのまま剰余類に送る。 |
| `compatibleLinearFamiliesEvalToRange` | 互換族を、その成分が属する射影の像へ評価する線形写像。 |
| `adicProjectionCompatibleComponent` | 射影先の互換族を、第 n 番目の I 進剰余類へ戻す線形写像。 |
| `adicProjectionCompatibleComponent_eq_mk` | 互換族の十分先の成分を代表で書けば、戻した成分は同じ代表の剰余類。 |
| `adicProjectionCompatibleComponent_transition` | 戻した各 I 進剰余類は、通常の I 進遷移について互換。 |
| `compatibleLinearFamilies_mem_range_of_stable` | 遷移の像が十分先で射影の像に入れば、互換族の各成分も射影の像に入る。 |
| `adicProjectionCompletionInverse` | 射影先の互換族から、元の加群の I 進完備化への線形写像。 |
| `adicProjectionCompletionInverse_left_inverse` | 互換族から戻す写像は、完備化からの標準写像の左逆。 |
| `adicProjectionCompletionInverse_right_inverse` | 互換族から戻す写像は、完備化からの標準写像の右逆。 |
| `adicProjectionCompletionLinearEquiv` | 核の一様評価と像への所属から得られる、I 進完備化と互換族の線形同型。 |
| `adicProjectionCompletionLinearEquiv_apply` | 完備化同型の順写像は、標準写像そのもの。 |
| `reesAdicProjectiveClosedCechCompatibleFamilies` | 実際の閉厚化の Čech コホモロジーの互換族の加群。 |
| `reesAdicProjectiveClosedCechProjection_pow_le_ker` | Iⁿ 倍は、実際の閉厚化への Čech 写像の核に入る。 |
| `reesAdicProjectiveClosedCechProjection_linear_compat` | 閉厚化への Čech 射影の互換性を、線形写像の合成として述べる。 |
| `reesAdicProjectiveClosedCechCompletionMap` | 元の Čech コホモロジーの完備化から、実際の閉厚化の互換族への標準写像。 |
| `reesAdicProjectiveClosedCechProjection_shifted_kernel_bound` | 核の評価を、n+c 段の核が Iⁿ 倍に入るという形にする。 |
| `reesAdicProjectiveClosedCechCompatibleFamilies_mem_range` | 閉厚化の Čech 互換族の各成分は、元のコホモロジーからの像に入る。 |
| `reesAdicProjectiveClosedCechCompletionLinearEquiv` | 実際の射影 Čech コホモロジーの形式関数の線形同型。 |
| `reesAdicProjectiveClosedCechCompletionLinearEquiv_toLinearMap` | 形式関数の Čech 同型の順写像は、標準写像そのもの。 |
| `reesAdicProjectiveClosedCechCompletionLinearEquiv_of_apply` | 形式関数の Čech 同型を加群の元で評価すると、元の閉厚化への射影になる。 |

### §9 への接続

残りは、共通アフィン細分・底変換・閉厚化・Frobenius・filtered colimit の五つについて、必要な比較を実際の図式へ接続し、完備化の同型と射に自然な形で合わせること。基底環とイデアルを固定した可換な係数写像に対する標準写像の自然性と、閉厚化の遷移の恒等・合成則を、次の新規ファイルで検証中である。一般の係数写像の可換式だけを、五つの比較の完成とは数えない。

flat な底変換ではコホモロジーの交換を使う。閉厚化には flat 性を仮定せず複体の自然な写像を扱う。Frobenius には半線形性と I 進指数の p 倍を明示する。filtered colimit では有限交叉の各次数の Čech 計算とコホモロジーの比較を扱い、完備化と任意の filtered colimit の交換同型を仮定することはしない。

全ビルド・監査は共有鍵 `--wait 3600` を一回ごとに取り、終了時に返した。23 時以降の二枠と、KL-W1 が停止点 3 の報告まで鍵の外で作業する改定も main から取り込み済み。新規の追加に `sorry`・`admit`・追加公理・計算量上限の追加はなく、既存の宣言の型・本文は変えていない。**停止点 2e ではない**。最終出力と利用側の `AugmentedRingCechExact` は保つ。

## 完備化比較の自然性と、実際の Čech 逆系（11-11）

`93427500d`（新規 4 モジュールと直接 importer、229 行）に保存。対象と直接 importer `SerrePositivity.AlgebraicGeometry` のビルドは **4,261 jobs 成功**、別の共有鍵による公式監査は **6,225 宣言・標準三公理のみ**。

登録モジュールは `LinearCompatibleFamiliesMap`、`AdicProjectionNaturality`、`ReesQuotientTransitionLaws`、`ReesClosedCechInverseSystem`。基底環とイデアルを固定した可換な係数写像について、完備化から互換族への標準写像の自然性を示した。完備化側は Mathlib の `AdicCompletion.map` を使う。すでに構成した Čech 形式関数の同型の順写像は標準写像と等しいため、この自然性を同型の順方向にも適用できる。

実際の商 M/IⁿM の遷移の恒等・合成則を代表上で示し、標準開の図式、Čech 複体、コホモロジーへ送った。その結果 `reesAdicProjectiveClosedCechInverseSystem : ℕᵒᵖ ⥤ ModuleCat R` を構成した。形式関数の同型では、この逆系の逆極限を各遷移に互換な族の型として扱う。

### 宣言と主張（ローカルな型クラス設定を除く11件）

| 宣言 | 主張 |
|---|---|
| `compatibleLinearFamiliesMap` | 遷移と可換な成分写像が誘導する、互換族の間の線形写像。 |
| `compatibleLinearFamiliesMap_apply` | 互換族の写像を成分で評価する。 |
| `adicProjectionQuotientMap_naturality` | 射影の可換性は、I 進剰余類上へ降ろした射影にも成り立つ。 |
| `adicProjectionCompletionMap_naturality_apply` | 完備化から互換族への標準写像は、成分写像と可換。 |
| `reesAdicProjectiveQuotientTransition_self` | 閉厚化の同じ段の間の遷移は恒等写像。 |
| `reesAdicProjectiveQuotientTransition_comp` | 閉厚化の二つの遷移の合成は、直接の遷移に等しい。 |
| `reesAdicProjectiveClosedCechTransitionChartMap_self` | 閉厚化の標準開の図式における、同じ段の遷移は恒等写像。 |
| `reesAdicProjectiveClosedCechTransitionChartMap_comp` | 閉厚化の標準開の図式における、遷移の合成則。 |
| `reesAdicProjectiveClosedCechTransition_self` | 閉厚化の Čech コホモロジーの同じ段の間の遷移は恒等写像。 |
| `reesAdicProjectiveClosedCechTransition_comp` | 閉厚化の Čech コホモロジーの遷移の合成則。 |
| `reesAdicProjectiveClosedCechInverseSystem` | 実際の閉厚化の Čech コホモロジーの逆系。 |

## 半線形な自然性と Frobenius の I 進指数の制御（11-11）

`730982aa7`（新規 4 モジュールと直接 importer、231 行）に保存。対象と直接 importer `SerrePositivity.AlgebraicGeometry` のビルドは **4,265 jobs 成功**、別の共有鍵による公式監査は **6,261 宣言・標準三公理のみ**。

登録モジュールは `SemilinearCompatibleFamiliesMap`、`AdicSemilinearMap`、`AdicProjectionSemilinearNaturality`、`FrobeniusAdicControl`。

係数環の準同型 σ:R→S、I⊆R、J⊆S、半線形写像 f:H→K について、I.map σ⊆J から f(IⁿH)⊆JⁿK を示し、Mathlib の完備化の間の **σ 半線形** 写像を構成した。flat 性は仮定しない。射影 πₙ・ρₙ と半線形成分写像 gₙ の四角形が可換なら、各剰余類、互換族、完備化からの標準写像の四角形も可換になる。これは §9 の具体的な Čech 比較に使う共通補題であり、具体的な比較の存在自体は入力として残る。

Frobenius には指数標数 p を使う。I.map(Frob)⊆Iᵖ を証明し、Frobenius 半線形な f に対して **f(IⁿH)⊆I^(p*n)K** を得た。Frob による完備化の写像も半線形写像として構成した。この部分は実際の基底環の Frobenius とイデアルの評価であり、構造層の標準開の Čech 図式の Frobenius との照合が次に残る。

### 宣言と主張（16件）

| 宣言 | 主張 |
|---|---|
| `compatibleSemilinearFamiliesMap` | 遷移と可換な半線形成分写像が誘導する、互換族の半線形写像。 |
| `compatibleSemilinearFamiliesMap_apply` | 半線形な互換族の写像を、各成分で評価する。 |
| `adicSemilinear_smul_top_le_comap` | イデアルの像の包含から、半線形写像は各イデアル冪の作用を保つ。 |
| `adicSemilinearQuotientMap` | 各イデアル冪による剰余類の間の半線形写像。 |
| `adicSemilinearQuotientMap_mk` | 剰余類の半線形写像は、元の代表をそのまま送る。 |
| `adicSemilinearQuotientMap_transition` | 剰余類の半線形写像は、通常の I 進・J 進遷移と可換。 |
| `adicSemilinearCompletionMap` | イデアル冪を保つ半線形写像が誘導する、Mathlib の完備化の間の半線形写像。 |
| `adicSemilinearCompletionMap_apply` | 半線形な完備化写像の成分は、剰余類の半線形写像で計算できる。 |
| `adicSemilinearCompletionMap_of_apply` | 半線形な完備化写像は、元の加群の写像と両立する。 |
| `adicProjectionQuotientMap_semilinear_naturality` | 半線形な射影の可換式は、各イデアル冪による剰余類にも降りる。 |
| `adicProjectionCompletionMap_semilinear_naturality_apply` | 完備化から互換族への標準写像は、係数環を変える半線形写像と可換。 |
| `frobeniusIdeal_map_le_pow` | Frobenius による I の像は、通常のイデアル冪 Iᵖ に含まれる。 |
| `frobeniusIdeal_map_le_self` | Frobenius による I の像は、I 自身にも含まれる。 |
| `frobeniusSemilinear_ideal_power_control` | Frobenius 半線形写像は、Iⁿ 倍を I^(p*n) 倍に送る。 |
| `frobeniusSemilinearCompletionMap` | Frobenius 半線形写像が誘導する、I 進完備化の間の Frobenius 半線形写像。 |
| `frobeniusScalarSemilinearMap` | 基底環の実際の Frobenius を、Frobenius 半線形な加群写像として見る。 |

### §9 の比較を具体化する次の順序

以下はまだ実装の残る部分であり、今回の一般的な可換式だけで完了とは数えない。

1. **共通アフィン細分**：二つの有限アフィン被覆の交叉の二重 Čech 図式を作る。各アフィン交叉上の被覆の増大 Čech の完全性を用意し、既存の `SerrePositivity.Cech.doubleCech_acyclic_iff` などを再利用して比較する。有界版と全タプル版の既存の比較だけでは、任意の共通アフィン細分の比較までは含まない。
2. **底変換**：有限な各次数の Čech 項について、テンソル積と有限積を交換する複体の比較を作る。flat な係数拡大では、その完全性によりコホモロジーの比較を同型にする。標準開の局所化・Proj 次数の比較へ接続し、今回の半線形な自然性に渡す。既存の `ProjectiveCechRestrictScalars` は係数制限の比較であり、ここで必要なテンソル積の比較とは別の入口として再利用する。
3. **閉厚化**：加群写像 M→M/JM と、(M/JM)/Iⁿ(M/JM) を M/(IⁿM+JM) と比較する商の可換図式を使う。次数付き加群写像に対する Čech の自然性から、実際の商で作った短完全列と完備化比較へ渡す。非 flat な底変換として、複体上の写像と長完全列を使う。
4. **Frobenius**：構造層に使う次数付き環の Frobenius は、Proj 次数 d→p*d と局所化の分母の p 乗を伴う。標準開の faces と可換な半線形 Čech 写像を作り、今回の I 進指数 n→p*n の評価へ接続する。Iᵖ に関する完備化と I に関する完備化の共終な比較も、必要な評価式とともに扱う。
5. **filtered colimit**：有限被覆の各 Čech 次数の有限積、局所化、次数零の成分との交換を示し、filtered colimit の完全性を使ってコホモロジーの比較へ渡す。完備化と任意の filtered colimit の交換同型は入力にしない。2g の Noether 近似で必要な有限段の図式と、今回の可換式の整合性を使う。

次の具体的な係数写像の入口としては、`reesExtendedAdic_map_mem` が基底環上線形な写像による IⁿM の保存を既に与える。次数を保つ多項式加群写像に対し、IⁿM と M/IⁿM の写像を作り、`fullCechComplexFunctor.mapShortComplex` で短完全列の間の射へ送る。これで閉厚化の比較と、他の比較を射に自然な形で渡す API を共通に使える。

全ビルド・全監査は共有の鍵 `--wait 3600` を一回の実行ごとに取り、終了時に返した。新規追加に `sorry`・`admit`・追加公理・計算量上限の追加はなく、既存宣言の型・本文は変更していない。数学の未コミット分はない。**停止点 2e ではない**。最終出力と利用側の `SerrePositivity.Cech.AugmentedRingCechExact` の型は保つ。

## §9：実際の加群写像と閉厚化の比較（11-11 夜）

### 実際の次数付き加群写像の自然性

`318ca02b2`（新規 3 モジュールと直接 importer、329 行）に保存。対象と直接 importer `SerrePositivity.AlgebraicGeometry` のビルドは **4,268 jobs 成功**、別の共有鍵による公式監査は **6,310 宣言・標準三公理のみ**。

登録モジュールは `ReesAdicProjectiveModuleMap`、`ReesClosedCechModuleMap`、`ReesClosedCechModuleNaturality`（すべて `SerrePositivity.AlgebraicGeometry` の下）。

次数を保つ多項式加群写像 f:M→N から、IⁿM→IⁿN と M/IⁿM→N/IⁿN を構成した。拡大イデアルの冪の保存は既存の `reesExtendedAdic_map_mem` を使う。実際の商の写像は射影・I 進遷移と可換であり、その Proj 次数の保存も示した。標準開の図式の写像を Čech コホモロジーへ送り、閉厚化の逆系の間の自然変換と、互換族の線形写像を構成した。先に証明した一般的な可換式にこれらの実際の写像を渡し、標準写像と Čech 形式関数の同型の両方について、f との自然性を得た。

宣言と主張（ローカルな型クラス設定を除く 17 件）：

| 宣言 | 主張 |
|---|---|
| `reesAdicProjectiveSubmoduleMap` | 多項式加群の写像を、実際の IⁿM の間の写像に制限する。 |
| `reesAdicProjectiveQuotientMap` | 多項式加群の写像を、実際の I 進閉厚化の商の間へ降ろす。 |
| `reesAdicProjectiveSubmoduleMap_inclusion` | IⁿM の包含と加群写像の四角形は可換。 |
| `reesAdicProjectiveQuotientMap_projection` | 閉厚化への射影と加群写像の四角形は可換。 |
| `reesAdicProjectiveQuotientMap_transition` | 加群写像からの商写像は、閉厚化の遷移と可換。 |
| `reesAdicProjectiveSubmoduleMap_preservesPiece` | IⁿM の間の写像は、元の写像が保つ Proj 次数を保つ。 |
| `reesAdicProjectiveQuotientMap_preservesPiece` | 閉厚化の商写像は、元の写像が保つ Proj 次数を保つ。 |
| `reesAdicProjectiveClosedCechModuleChartMap` | 加群写像から得られる、実際の閉厚化の標準開図式の写像。 |
| `reesAdicProjectiveClosedCechModuleMap` | 加群写像が誘導する、実際の閉厚化の Čech コホモロジーの写像。 |
| `reesAdicProjectiveClosedCechModuleChartMap_projection` | 標準開の図式の商写像は、閉厚化への射影と可換。 |
| `reesAdicProjectiveClosedCechModuleChartMap_transition` | 標準開の図式の商写像は、I 進遷移と可換。 |
| `reesAdicProjectiveClosedCechModuleMap_projection` | 実際の閉厚化の Čech 写像は、元の Čech コホモロジーからの射影と可換。 |
| `reesAdicProjectiveClosedCechModuleMap_transition` | 実際の閉厚化の Čech 写像は、I 進遷移と可換。 |
| `reesAdicProjectiveClosedCechModuleNatTrans` | 実際の次数付き加群写像が誘導する、閉厚化の Čech 逆系の間の自然変換。 |
| `reesAdicProjectiveClosedCechModuleFamiliesMap` | 実際の次数付き加群写像が誘導する、閉厚化の Čech 互換族の間の線形写像。 |
| `reesAdicProjectiveClosedCechCompletionMap_module_naturality` | 完備化からの標準 Čech 写像は、実際の次数付き加群写像と可換。 |
| `reesAdicProjectiveClosedCechCompletionLinearEquiv_module_naturality` | Čech 形式関数の同型は、実際の次数付き加群写像に自然。 |

### M→M/JM と二重閉厚化の係数比較

`ae7273e40`（新規 2 モジュールと直接 importer、161 行）に保存。対象と直接 importer `SerrePositivity.AlgebraicGeometry` のビルドは **4,270 jobs 成功**、別の共有鍵による公式監査は **6,337 宣言・標準三公理のみ**。

登録モジュールは `ReesClosedThickeningNaturality`、`ReesIteratedClosedQuotient`（すべて `SerrePositivity.AlgebraicGeometry` の下）。

上の自然性を、実際の射影 M→M/JM に適用した。商の次数分解と多項式環上の有限性も実際の商から供給し、flat 性を仮定せず、M と M/JM の Čech 形式関数の同型の可換式を示した。さらに全射 M→M/JM による IⁿM の像が Iⁿ(M/JM) に等しいことから、第三同型定理を使って (M/JM)/Iⁿ(M/JM)≃M/(JM+IⁿM) を多項式環上線形に構成した。この同型は元の代表 m を単一の剰余類へ送る。

宣言と主張（ローカルな型クラス設定を除く 8 件）：

| 宣言 | 主張 |
|---|---|
| `reesClosedThickeningCechHomologyMap` | M→M/JM が誘導する、元の標準開 Čech コホモロジーの写像。 |
| `reesClosedThickeningCechFamiliesMap` | M→M/JM が誘導する、I 進閉厚化の Čech 互換族の間の写像。 |
| `reesClosedThickeningCechCompletionMap_naturality` | 実際の M/JM への閉厚化は、完備化からの標準 Čech 写像と可換。 |
| `reesClosedThickeningCechCompletionLinearEquiv_naturality` | Čech 形式関数の同型は、実際の M/JM への閉厚化と可換。 |
| `reesAdicProjectivePolynomialSubmodule` | 多項式環上で見た、基底イデアルの拡大冪による部分加群。 |
| `reesIteratedClosedQuotient_submodule_image` | 全射 M→M/JM による IⁿM の像は、Iⁿ(M/JM) に等しい。 |
| `reesIteratedClosedQuotientLinearEquiv` | (M/JM)/Iⁿ(M/JM) と M/(JM+IⁿM) の、多項式環上線形な同型。 |
| `reesIteratedClosedQuotientLinearEquiv_mk_mk` | 二重閉厚化の同型は、元の加群の代表をそのまま単一の剰余類に送る。 |

### 二重閉厚化の Proj 次数と Čech コホモロジーの比較

`4a8c20976`（新規 2 モジュールと直接 importer、188 行）に保存。対象と直接 importer `SerrePositivity.AlgebraicGeometry` のビルドは **4,272 jobs 成功**、別の共有鍵による公式監査は **6,364 宣言・標準三公理のみ**。

登録モジュールは `ProjectiveNatGradedEquiv`、`ReesIteratedClosedGrading`（すべて `SerrePositivity.AlgebraicGeometry` の下）。

上の係数同型と逆写像の両方が、元の Proj 次数を保つことを示した。単一の商の次数成分は G_d の像で与える。両方向で次数を保つ多項式線形同型を、標準開の図式と Čech コホモロジーの同型へ送る一般補題を使い、実際の二重閉厚化と M/(JM+IⁿM) の各 Čech コホモロジーを比較した。Noether 性はこの比較自体には要らない。

宣言と主張（ローカルな型クラス設定を除く 8 件）：

| 宣言 | 主張 |
|---|---|
| `projectiveNatGradedModuleChartIso` | 両方向で Proj 次数を保つ同型が誘導する、標準開の図式の同型。 |
| `projectiveNatGradedModuleCechHomologyIso` | 次数付き加群の同型が誘導する、標準開 Čech コホモロジーの同型。 |
| `projectiveNatGradedModuleCechHomologyIso_hom` | Čech の同型の順写像は、元の線形同型からの Čech 写像そのもの。 |
| `reesIteratedClosedSumPiece` | 単一の商 M/(JM+IⁿM) における、元の Proj 次数成分の像。 |
| `reesIteratedClosedQuotientLinearEquiv_preservesPiece` | 二重閉厚化から単一の商への同型は、元の Proj 次数を保つ。 |
| `reesIteratedClosedQuotientLinearEquiv_symm_preservesPiece` | 単一の商から二重閉厚化への逆写像も、元の Proj 次数を保つ。 |
| `reesIteratedClosedSumPieceGradedSMul` | 単一の商の Proj 次数と、多項式の次数の作用は両立する。 |
| `reesIteratedClosedCechHomologyIso` | 二重閉厚化と M/(JM+IⁿM) の標準開 Čech コホモロジーの比較同型。 |

### 閉厚化の互換族と形式関数への接続

`6231c8e5c`（新規 4 モジュールと直接 importer、375 行）に保存。対象と直接 importer `SerrePositivity.AlgebraicGeometry` のビルドは **4,276 jobs 成功**、別の共有鍵による公式監査は **6,427 宣言・標準三公理のみ**。

登録モジュールは `LinearCompatibleFamiliesEquiv`、`ReesIteratedClosedTransition`、`ReesIteratedClosedCechTransition`、`ReesClosedThickeningFormalFunctions`（すべて `SerrePositivity.AlgebraicGeometry` の下）。

M/(JM+IⁱM)→M/(JM+IʲM) の実際の商写像を作り、係数同型が遷移と可換であることを代表上で示した。標準開の合成則と Čech 関手を使って、各段の Čech 比較同型も I 進遷移と可換と分かった。互換な成分同型を互換族の線形同型へまとめ、M/JM の形式関数と合成した。その結果、AdicCompletion I H_Cech^q(M/JM;d) と、各 H_Cech^q(M/(JM+IⁿM);d) の互換族の間に線形同型を得た。元の M の完備化からの射影についても可換式を示した。

宣言と主張（ローカルな型クラス設定を除く 17 件）：

| 宣言 | 主張 |
|---|---|
| `compatibleLinearFamiliesEquiv_inverse_commute` | 互換な成分同型の逆写像も、逆向きに遷移と可換。 |
| `compatibleLinearFamiliesEquiv` | 成分ごとの互換な線形同型が誘導する、互換族の線形同型。 |
| `compatibleLinearFamiliesEquiv_apply` | 互換族の同型の成分は、もとの成分同型で計算できる。 |
| `reesIteratedClosedSumTransition` | 一重の商 M/(JM+IⁱM) から M/(JM+IʲM) への遷移。 |
| `reesIteratedClosedQuotientLinearEquiv_transition` | 二重閉厚化から一重の商への同型は、実際の遷移と可換。 |
| `reesIteratedClosedSumTransition_preservesPiece` | 一重の商の遷移は、元の Proj 次数を保つ。 |
| `reesIteratedClosedSumChartTransition` | 一重の商の遷移が誘導する、標準開の係数図式の写像。 |
| `reesIteratedClosedSumCechHomology` | 一重の商 M/(JM+IⁿM) の Čech コホモロジーの対象。 |
| `reesIteratedClosedSumCechTransition` | 一重の商の遷移が誘導する、Čech コホモロジーの写像。 |
| `reesIteratedClosedChartIso` | 二重閉厚化と一重の商の、標準開の係数図式の比較同型。 |
| `reesIteratedClosedChartIso_transition` | 二重閉厚化の標準開での比較は、実際の遷移と可換。 |
| `reesIteratedClosedCechHomologyIso_transition` | 二重閉厚化の Čech 比較は、実際の I 進遷移と可換。 |
| `reesIteratedClosedSumCechFamilies` | 一重の商 M/(JM+IⁿM) の Čech コホモロジーの互換族。 |
| `reesIteratedClosedCechFamiliesEquiv` | 二重閉厚化と一重の商の Čech 比較を、互換族の線形同型へまとめる。 |
| `reesClosedThickeningSumCechFamiliesMap` | 元の M の閉厚化の互換族を、一重の商の Čech 互換族へ送る。 |
| `reesClosedThickeningSumCechFormalFunctions` | M/JM の Čech コホモロジーの完備化を、M/(JM+IⁿM) の互換族と比較する同型。 |
| `reesClosedThickeningSumCechFormalFunctions_naturality` | 一重の商で表した閉厚化の Čech 形式関数も、元の M からの射影と可換。 |

### 比較先の実際の次数分解と有限性

`567c970e8`（新規 1 モジュールと直接 importer、74 行）に保存。対象と直接 importer `SerrePositivity.AlgebraicGeometry` のビルドは **4,277 jobs 成功**、別の共有鍵による公式監査は **6,434 宣言・標準三公理のみ**。

登録モジュールは `ReesIteratedClosedSumDecomposition`（すべて `SerrePositivity.AlgebraicGeometry` の下）。

JM+IⁿM が G の成分射影で保たれることを、和の代表と射影の加法性から示した。既存の `HilbertSerre.isInternal_quotientGrade` を使い、上で定義した単一の商の次数成分が実際の直和分解を与えることを確認した。基底が Noether、M が多項式環上有限という従来の仮定の下で、単一の商の Čech コホモロジーも基底環上有限と示した。

宣言と主張（ローカルな型クラス設定を除く 3 件）：

| 宣言 | 主張 |
|---|---|
| `reesIteratedClosedSum_isHomogeneous` | 分母 JM+IⁿM は、元の Proj 次数について斉次。 |
| `reesIteratedClosedSumPieceDecomposition` | 一重の商の Proj 次数成分は、商加群の直和分解を与える。 |
| `reesIteratedClosedSumCechHomology_finite` | 一重の商 M/(JM+IⁿM) の標準開 Čech コホモロジーは有限生成。 |

### 今回の到達点と残り

閉厚化については、基底環 R 上の次数付き多項式加群の表示を使い、実際の M→M/JM、二重商と一重商の比較、各 Čech コホモロジー、I 進遷移、互換族、形式関数の同型までを可換にした。原典 Stacks 30.20.5 の Hⁱ の形式関数に対応する **Čech 版**であり、導来関手の Hⁱ との比較は形式化していない。比較先の次数分解と Stacks 30.19.2 に対応する Čech 有限性も供給済み。

この束は R 上の加群としての表示である。R/J 上の係数で述べた標準開図式と、その係数を R へ制限した図式との照合は、次のテンソル積による係数モデルと併せて接続する。非 flat な閉厚化で、コホモロジーとテンソル積の交換を仮定していない。

残る主要な四群は、共通アフィン細分、flat な底変換の比較、実際の Čech Frobenius と p 倍の指数の照合、filtered colimit の比較。底変換では、まず次数零の局所化とテンソル積の複体の比較を作り、flat な場合だけコホモロジーの交換を使う。この係数モデルで上の R/J の照合も扱う。共通細分・二重 Čech には既存の `SerrePositivity.Cech` の API を再利用する。

全新規モジュールに `sorry`・`admit`・追加公理・計算量上限の追加はなく、既存の宣言の型・本文は変更していない。全ビルド・監査は共有鍵 `--wait 3600` を一回ごとに取り、終了時に返した。ルート全体のビルドは行っていない。宇宙の扱いは従来どおりで、BS17 の入口に必要な大きい加群の移送は `Module.Finite.small`・`Shrink.linearEquiv` の方針を保つ。

`3345ac42a` で main `d9e596898` を `math/scheme` に取り込んだ。検証済み AG のローカル import 閉包・Lean/Lake 設定・公式監査スクリプトの **666 ファイルの SHA-256** を前後で比べ、不一致 **0**。従って上のビルドと最新 **6,434 宣言・標準三公理のみ**の監査は、取り込み後にも対応する。入力が同じ検証は繰り返していない。

検証済みの本体はすべて枝にコミット済み。**停止点 2e ではない**。最終出力と利用側の `SerrePositivity.Cech.AugmentedRingCechExact` の型は変更しない。

## 閉厚化の商環上の係数表示（11-12）

`6dfb5e2bf` に新規 5 モジュールと直接 importer を保存（410 行）。対象と直接 importer `SerrePositivity.AlgebraicGeometry` のビルドは **4,282 jobs 成功**。終了後に共有鍵を取り直して行った公式監査は **6,483 宣言・標準三公理のみ**。

登録モジュール（すべて `SerrePositivity.AlgebraicGeometry` の下）：

- `ReesClosedCoefficientModule`
- `ReesClosedCoefficientTower`
- `ProjectiveHomogeneousCoefficientLift`
- `ReesClosedCoefficientGrading`
- `ReesClosedCoefficientCech`

前の束は閉厚化 M/JM を R 加群として扱っていた。今回は型と元の R 作用を保ったまま、実際に R/J と (R/J)[X] の加群構造を与えた。J とその拡大イデアルが商加群を消すことを示し、Mathlib の `MvPolynomial.quotientEquivQuotientMvPolynomial` で多項式作用を移した。次数成分の台は元の商次数成分のままであり、R への係数制限で元の成分に戻る。

全射な係数変更に沿って斉次多項式を同じ次数で持ち上げられることを、任意の持ち上げの斉次成分を取って示した。これで商係数の多項式作用が Proj 次数を保つことを証明し、既存の係数変更の比較を実際の閉厚化へ適用した。標準開の図式の同型は標準開間の制限射に自然で、全タプル Čech コホモロジーの比較同型を誘導する。Noether な R と多項式環上有限な M という従来の仮定から、商環上で表示した Čech コホモロジーの R/J 上の有限性も得た。

宣言と主張（ローカルな型クラス設定を除く 18 件）：

| 宣言 | 主張 |
|---|---|
| `reesClosedCoefficient_torsion` | J は実際の閉厚化 M/JM を消す。 |
| `reesClosedCoefficientModule` | 同じ閉厚化に R/J 加群構造を与える。 |
| `reesClosedCoefficient_mk_smul` | 商環の代表による作用は元の R 作用に一致する。 |
| `reesClosedCoefficient_scalarTower` | R/J から R への係数制限は元の加群構造を回復する。 |
| `reesClosedPolynomialCoefficient_torsion` | 拡大イデアル J[X] は元の多項式加群の閉厚化を消す。 |
| `reesClosedPolynomialCoefficientModule` | 同じ閉厚化に (R/J)[X] 加群構造を与える。 |
| `reesClosedPolynomialCoefficient_map_smul` | 多項式の係数を商へ写してからの作用は、元の作用と一致する。 |
| `reesClosedPolynomialCoefficient_scalarTower` | R[X] と (R/J)[X] の作用は係数変更と両立する。 |
| `reesClosedPolynomialCoefficient_base_scalarTower` | R と (R/J)[X] の作用は両立する。 |
| `reesClosedPolynomialCoefficient_quotient_scalarTower` | R/J と (R/J)[X] の作用は両立する。 |
| `projectiveHomogeneousComponent_map` | 多項式の次数成分を取る操作は、任意の係数変更と交換する。 |
| `projectiveHomogeneousCoefficientLift` | 全射な係数変更に沿って、斉次多項式を同じ次数で持ち上げられる。 |
| `reesClosedCoefficientPiece` | 閉厚化の Proj 次数成分を R/J 上の部分加群として表す。 |
| `reesClosedCoefficientPiece_restrictScalars` | その係数制限は元の R 上の商次数成分と一致する。 |
| `reesClosedCoefficientPieceGradedSMul` | 商係数の斉次多項式作用は、実際の閉厚化の Proj 次数を保つ。 |
| `reesClosedCoefficientChartIso` | 元の R 上の標準開図式を、R/J 上の図式の係数制限と比較する同型。 |
| `reesClosedCoefficientCechHomologyIso` | 実際の閉厚化の Čech コホモロジーを、商環上の同じ計算の係数制限と比較する同型。 |
| `reesClosedCoefficientCechHomology_finite` | 商環上で表示した閉厚化の Čech コホモロジーは R/J 上有限生成。 |

これは Stacks 30.19.2 の有限性と Stacks 30.20.5 の形式関数に使う **Čech 版**の係数比較である。分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、この比較は形式化していない。非平坦な閉厚化でコホモロジーとテンソル積が交換するという主張は使っていない。今回の商環上の表示自体にはテンソル積モデルを必要とせず、商多項式環から直接構成できた。

**停止点 2e ではない。** この同型を加群の射に関する自然性と I 進遷移に接続し、既存の二重閉厚化・互換族・形式関数の可換式へ渡す作業は残る。標準開間の制限射に関する自然性だけを、§9 の射に自然な整合性の完成とは数えない。主要な残りは引き続き、共通アフィン細分、flat な底変換、実際の Čech Frobenius と p 倍の指数、filtered colimit の比較である。一般の固有射のコホモロジーの有限性・導来関手の Hⁱ との比較は範囲に加えていない。最終出力と利用側の `SerrePositivity.Cech.AugmentedRingCechExact` の型は変更していない。

全ビルドと監査は `with_build_lock.sh --wait 3600` を経由し、一回ごとに鍵を返した。既存の宣言の型・本文は変えず、新規宣言に `sorry`・`admit`・追加公理・計算量上限の追加はない。宇宙の条件は従来どおりで、大きい型の入口は承認済みの `Module.Finite.small`・`Shrink.linearEquiv` による移送の方針を保つ。

`fa676e429` で main `2fc3dc7ce` を取り込んだ。今回の検証済み AG のローカル import 閉包・設定・監査スクリプト **671 ファイル**の SHA-256 を前後で比較し、不一致 **0**。main 側の変更は他レーンの指示文書のみであり、上のビルドと監査は取り込み後にも対応する。

## 商係数比較の自然性と I 進遷移への接続（11-12）

`03e7b92c2` に新規 9 モジュールと直接 importer を保存（1,185 行）。対象と直接 importer `SerrePositivity.AlgebraicGeometry` のビルドは **4,291 jobs 成功**。別の共有鍵で行った公式監査は **6,704 宣言・標準三公理のみ**。

登録モジュール（すべて `SerrePositivity.AlgebraicGeometry` の下）：

- `ProjectiveCoefficientChartTransport`
- `ProjectiveNatCoefficientNaturality`
- `ReesClosedCoefficientAdicFormalFunctions`
- `ReesClosedCoefficientModuleMap`
- `ReesClosedCoefficientNaturality`
- `ReesCoefficientAdicCech`
- `ReesCoefficientAdicCechTransition`
- `ReesCoefficientAdicQuotient`
- `SurjectiveCoefficientQuotient`

実際の次数付き加群写像 M→N を M/JM→N/JN へ降ろし、その写像が (R/J)[X] 上線形であることと、元の R[X] へ制限すると以前の商写像に戻ることを示した。この実際の写像について、商係数の標準開比較と Čech コホモロジーの比較が可換となる。

次数族の等式を比較同型の型へ直接輸送すると核の計算が重くなるため、今回は次数成分上の恒等加群写像を標準開へ送る `projectiveCoefficientChartIsoOfRestrictEq` を使い、射に自然な比較 `projectiveNatCoefficientChartIso`・`projectiveNatCoefficientCechIso` を追加した。既存の `projectiveNatPolynomialCoefficientChangeChartIso`・`reesClosedCoefficientCechHomologyIso` の型・本文は変更していない。この束の自然性と I 進系には新しい比較を一貫して使う。計算量上限は増やしていない。

さらに基底の全射 R→B を固定し、実際の R 上の商 M/IⁿM の型を保ったまま B と B[X] の作用を与えた。部分加群は (I B)ⁿ の拡大作用そのものに一致する。I 進遷移を B[X] 上線形に扱い、その R[X] への係数制限が以前の実際の遷移に一致することを代表上で示した。各段の標準開比較と Čech 比較はこの遷移と可換であり、互換族の線形同型へまとめられる。

これを B=R/J、係数加群 M/JM に特殊化した `reesClosedCoefficientAdicCechIso_transition` は、既存の `reesAdicProjectiveClosedCechTransition` そのものと可換である。既存の互換族と、R/J 上で計算した各 (M/JM)/(I B)ⁿ(M/JM) の Čech コホモロジーの互換族との間に線形同型を作った。Noether な R と R[X] 上有限な M の下で、既存の形式関数と合成し、

AdicCompletion I H_Cech^q(M/JM;d) ≃ₗ[R] {R/J 上の各 I 進閉厚化の Čech コホモロジーの互換族}

を得た。この商係数表示の形式関数も、元の M→M/JM からの射影と可換である。左辺の完備化は I に関する R 加群の完備化として述べており、B 上の完備化との交換や非平坦なコホモロジーとテンソル積の交換を仮定していない。

宣言と主張（ローカルな型クラス設定を除く 55 件）：

| 宣言 | 主張 |
|---|---|
| `projectiveCoefficientChartIsoOfRestrictEq` | 指定した次数族との同定を、恒等の加群写像による標準開の同型にする。 |
| `projectiveCoefficientChartIsoOfRestrictEq_naturality` | 次数族の同定を含む比較も、次数を保つ加群の射に自然。 |
| `projectiveNatCoefficientChartIso` | 自然数次数の係数比較を、次数成分の恒等写像を介して構成する。 |
| `projectiveNatCoefficientChartIso_naturality` | 自然数次数の係数比較は、次数を保つ加群の射に自然。 |
| `projectiveNatCoefficientCechIso` | 自然な標準開比較が誘導する Čech コホモロジーの係数比較。 |
| `projectiveNatCoefficientCechIso_naturality` | 自然数次数の Čech 係数比較は、次数を保つ加群写像に自然。 |
| `reesClosedCoefficientAdicCechIso` | M/JM の実際の I 進閉厚化の、商係数 Čech 計算との比較。 |
| `reesClosedCoefficientAdicCechIso_transition` | 閉厚化の商係数比較は、以前の実際の I 進 Čech 遷移と可換。 |
| `reesClosedCoefficientAdicCechFamiliesEquiv` | 閉厚化の実際の互換族を、R/J 上の Čech 計算の互換族へ送る同型。 |
| `reesClosedCoefficientAdicCechFamiliesMap` | 元の M の閉厚化の互換族から、商係数で表示した M/JM の互換族への写像。 |
| `reesClosedCoefficientAdicCechFormalFunctions` | M/JM の Čech 形式関数を、R/J 上の各閉厚化の計算を用いて表す同型。 |
| `reesClosedCoefficientAdicCechFormalFunctions_naturality` | 商係数で表した Čech 形式関数も、元の M からの閉厚化射影と可換。 |
| `reesClosedCoefficientModuleMap` | 実際の閉厚化の商写像を、商係数多項式環上の写像として表す。 |
| `reesClosedCoefficientModuleMap_restrictScalars` | 元の多項式環への係数制限で、既存の実際の商写像を回復する。 |
| `reesClosedCoefficientModuleMap_preservesPiece` | 商係数の閉厚化の射も、実際の商次数成分を保つ。 |
| `reesClosedCoefficientNaturalChartIso` | 実際の閉厚化の標準開の、射に自然な商係数比較。 |
| `reesClosedCoefficientNaturalCechIso` | 実際の閉厚化の Čech コホモロジーの、射に自然な商係数比較。 |
| `reesClosedCoefficientModuleChartMap` | 次数付き加群の射が誘導する、商係数の閉厚化の標準開の射。 |
| `reesClosedCoefficientNaturalChartIso_naturality` | 商係数の標準開比較は、実際の閉厚化の加群写像と可換。 |
| `reesClosedCoefficientModuleCechMap` | 元の次数付き加群の射から得られる、商係数の閉厚化の Čech 写像。 |
| `reesClosedCoefficientNaturalCechIso_naturality` | 商係数の Čech 比較は、実際の閉厚化の加群写像と可換。 |
| `reesCoefficientAdicProjection` | 変更後の基底環上で見た、実際の I 進商への射影。 |
| `reesCoefficientAdicPiece` | I 進商の Proj 次数成分を、変更後の係数環上の部分加群として表す。 |
| `reesCoefficientAdicPiece_restrictScalars` | I 進商の次数成分は、係数制限で元の R 上の商次数成分に戻る。 |
| `reesCoefficientAdicPieceGradedSMul` | 変更後の多項式係数の作用は、I 進商の次数を保つ。 |
| `reesCoefficientAdicTransition_preservesPiece` | 実際の I 進遷移は、変更後の係数環で表した次数成分も保つ。 |
| `reesCoefficientAdicChartIso` | I 進商の標準開図式の、変更後の係数環への比較同型。 |
| `reesCoefficientAdicChartTransition` | 変更後の係数環上での、実際の I 進遷移の標準開写像。 |
| `reesCoefficientAdicChartIso_transition` | I 進商の係数比較は、実際の I 進遷移と可換。 |
| `reesCoefficientAdicOriginalCechHomology` | 元の R 上で計算する、実際の I 進商の Čech コホモロジー。 |
| `reesCoefficientAdicOriginalCechTransition` | 元の R 上で計算する、実際の I 進遷移の Čech 写像。 |
| `reesCoefficientAdicRestrictedCechHomology` | 変更後の係数環上で計算した Čech コホモロジーの係数制限。 |
| `reesCoefficientAdicCechIso` | I 進商の Čech コホモロジーの係数比較。 |
| `reesCoefficientAdicRestrictedCechTransition` | 変更後の係数環上の I 進遷移が誘導する Čech 写像の係数制限。 |
| `reesCoefficientAdicCechIso_transition` | I 進商の Čech 係数比較は、実際の I 進遷移と可換。 |
| `reesCoefficientAdicRestrictedCechFamilies` | 変更後の係数環で計算した I 進 Čech コホモロジーの互換族。 |
| `reesCoefficientAdicCechFamiliesEquiv` | 元の R 上の互換族と、変更後の係数環上の計算の互換族との同型。 |
| `reesCoefficientAdicPolynomial_surjective` | 全射な基底係数変更は、多項式環の係数変更も全射にする。 |
| `reesCoefficientAdicSubmodule` | 実際の IⁿM を、変更後の多項式環上の部分加群として表す。 |
| `reesCoefficientAdicSubmodule_eq` | 変更後の係数環で表した IⁿM は、I の拡大冪の作用そのものである。 |
| `reesCoefficientAdicSubmodule_eq_mappedIdeal` | 同じ部分加群は、変更後の基底のイデアル I B の冪による作用でもある。 |
| `reesCoefficientAdicQuotientPolynomialModule` | 同じ I 進商の、変更後の多項式環上の加群構造。 |
| `reesCoefficientAdicQuotientModule` | 同じ I 進商の、変更後の基底環上の加群構造。 |
| `reesCoefficientAdicQuotient_base_scalarTower` | 元の基底と変更後の基底の作用の塔。 |
| `reesCoefficientAdicQuotient_base_polynomial_scalarTower` | 元の基底と変更後の多項式環の作用の塔。 |
| `reesCoefficientAdicQuotient_polynomial_scalarTower` | 変更後の基底と変更後の多項式環の作用の塔。 |
| `reesCoefficientAdicQuotient_coefficient_scalarTower` | 二つの多項式環の作用の塔。 |
| `reesCoefficientAdicQuotientTransition` | 変更後の多項式環上で見た、実際の I 進遷移。 |
| `reesCoefficientAdicQuotientTransition_restrictScalars` | I 進遷移の係数制限は、以前の実際の遷移そのものである。 |
| `surjectiveCoefficientSubmodule` | 全射な係数変更では、小さい環の部分加群は大きい環でも閉じている。 |
| `surjectiveCoefficientSubmodule_restrictScalars` | 係数変更後の部分加群の制限は元の部分加群に一致する。 |
| `surjectiveCoefficientQuotientModule` | 元の商の型を保った、変更後の係数環上の加群構造。 |
| `surjectiveCoefficientQuotient_scalarTower` | 変更後の係数作用は、元の商の作用と両立する。 |
| `surjectiveCoefficientQuotientProjection` | 商への射影は変更後の係数環上でも線形。 |
| `surjectiveCoefficientQuotientProjection_apply` | 係数変更後の射影も、代表を同じ剰余類へ送る。 |

コホモロジーと形式関数の主張は、引き続き Stacks 30.20.5 の原典の Hⁱ に対応する **Čech 版**である。分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、この比較は形式化していない。

**停止点 2e ではない。** 今回は、商係数による比較を実際の加群の射に自然にし、実際の I 進遷移・互換族・形式関数・元の M からの射影まで接続した。I 進系全体の比較を任意の M→N に対する自然変換として一つにまとめる API はまだ作っていない（各段の一般自然性は上の `projectiveNatCoefficientCechIso_naturality` で供給）。次の主要な作業群は引き続き、共通アフィン細分、flat なテンソル底変換、実際の Čech Frobenius と p 倍の指数、filtered colimit の比較である。一般の固有射の有限性・Stein 分解・導来関手の Hⁱ との比較は範囲に加えていない。

全ビルド・監査は共有鍵 `with_build_lock.sh --wait 3600` を経由し、一回ごとに鍵を返した。待ちは同じ worktree から一つだけ。ルート全体のビルドは行わず、取り込みは調整役に任せる。既存の宣言の型・本文、最終出力と利用側の `SerrePositivity.Cech.AugmentedRingCechExact` の型は変更していない。新規宣言に `sorry`・`admit`・追加公理・計算量上限の追加はない。宇宙の条件と `Module.Finite.small`・`Shrink.linearEquiv` による移送の方針も保つ。

`da2713482` で main `e3dc5ba4b` を取り込んだ。検証済み AG のローカル import 閉包・設定・公式監査スクリプト **680 ファイル**の SHA-256 を前後で比較し、不一致 **0**。main 側の変更は文書のみで、上の 4,291 jobs のビルドと 6,704 宣言の監査は取り込み後にも対応する。
