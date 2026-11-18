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

## I 進系全体の加群写像に対する自然性（11-12）

`6e414c886` に新規 5 モジュールと直接 importer を保存（979 行）。対象と直接 importer `SerrePositivity.AlgebraicGeometry` のビルドは **4,296 jobs 成功**。終了後に共有鍵を取り直して行った公式監査は **6,876 宣言・標準三公理のみ**。

登録モジュール（すべて `SerrePositivity.AlgebraicGeometry` の下）：

- `ReesClosedCoefficientAdicModuleNaturality`
- `ReesCoefficientAdicFamiliesNaturality`
- `ReesCoefficientAdicFormalFunctionsNaturality`
- `ReesCoefficientAdicModuleCech`
- `ReesCoefficientAdicModuleMap`

前回残した、I 進系全体の比較を任意の次数付き加群写像に自然にする可換式をまとめた。全射な係数変更 R→B を固定し、B[X] 上線形な次数付き加群写像 f:M→N を、同じ型の実際の I 進商 M/IⁿM→N/IⁿN へ降ろした。この商写像は B[X] 上線形で、R[X] へ係数制限すると既存の実際の商写像に戻る。射影・I 進遷移と可換で、Proj 次数を保つ。

この実際の商写像を標準開と Čech コホモロジーへ送り、元の R 上と変更後の B 上の両方で全遷移との可換性を示した。各段の係数比較が f と可換であることを使い、I 進 Čech 互換族の比較の順写像・逆写像が共に f に自然と分かった。R 線形写像の合成としての可換式も供給した。

元の R 上の互換族写像は、既存の `reesAdicProjectiveClosedCechModuleFamiliesMap` そのものであることを成分で照合した。この照合と既存の形式関数の自然性を合成して、B 上で各段を計算した互換族への標準完備化写像が f と可換であることを示した。標準写像の自然性には Noether 性と有限生成性を使わない。Noether な R と R[X] 上有限な M,N の下では、形式関数の線形同型についても同じ自然性が成り立ち、その順写像は標準完備化写像と一致する。

最後に B=R/J、係数加群 M/JM,N/JN とし、元の任意の R[X] 上の次数付き写像 M→N が誘導する実際の商写像に特殊化した。既存の `reesClosedCoefficientAdicCechFamiliesEquiv` と `reesClosedCoefficientAdicCechFormalFunctions` の型・本文を保ったまま、各 I 進段・互換族・形式関数の比較がその写像と可換であることを証明した。互換族の特殊化は成分の可換式に分け、次数族や互換族全体の等式による重い輸送を避けて検証した。

宣言と主張（ローカルな型クラス設定を除く 31 件）：

| 宣言 | 主張 |
|---|---|
| `reesClosedCoefficientAdicModuleFamiliesMap` | 実際の M/JM→N/JN が誘導する、商係数の I 進 Čech 互換族の写像。 |
| `reesClosedCoefficientAdicModuleCechMap` | 実際の M/JM→N/JN が各 I 進段で誘導する、商係数の Čech 写像。 |
| `reesClosedCoefficientAdicCechIso_module_naturality` | 実際の閉厚化の各 I 進段の係数比較は、任意の元の次数付き加群写像に自然。 |
| `reesClosedCoefficientAdicCechFamiliesEquiv_module_naturality` | 実際の閉厚化の I 進互換族の係数比較は、任意の元の次数付き加群写像に自然。 |
| `reesClosedCoefficientAdicCechFormalFunctions_module_naturality` | M/JM の商係数表示の Čech 形式関数は、任意の元の次数付き加群写像に自然。 |
| `reesCoefficientAdicOriginalCechFamiliesMap` | 元の R 上の I 進 Čech 互換族の、実際の加群写像が誘導する写像。 |
| `reesCoefficientAdicRestrictedCechFamiliesMap` | B 上で計算した I 進 Čech 互換族の、実際の加群写像が誘導する写像。 |
| `reesCoefficientAdicCechFamiliesEquiv_module_naturality` | I 進 Čech 互換族の係数比較は、実際の加群写像に自然。 |
| `reesCoefficientAdicCechFamiliesEquiv_module_naturality_linear` | 互換族の係数比較の自然性を、R 線形写像の可換な合成として述べる。 |
| `reesCoefficientAdicCechFamiliesEquiv_symm_module_naturality` | 互換族の係数比較の逆写像も、実際の加群写像に自然。 |
| `reesCoefficientAdicCompletionMap` | 完備化から実際の I 進 Čech 互換族への標準写像を、B 上の表示へ送る。 |
| `reesCoefficientAdicOriginalCechFamiliesMap_eq_native` | 元の R 上の実際の互換族写像は、既存の I 進 Čech 写像に一致する。 |
| `reesCoefficientAdicCompletionMap_module_naturality` | 商係数表示の完備化からの標準 Čech 写像は、任意の次数付き加群写像に自然。 |
| `reesCoefficientAdicFormalFunctions` | Čech 形式関数を、B 上で計算した実際の I 進閉厚化の互換族で表す同型。 |
| `reesCoefficientAdicFormalFunctions_toLinearMap` | 商係数表示の形式関数の順写像は、既存の標準 Čech 写像そのものである。 |
| `reesCoefficientAdicFormalFunctions_module_naturality` | 商係数表示の Čech 形式関数は、任意の次数付き加群写像に自然。 |
| `reesCoefficientAdicModuleChartMap` | 実際の加群写像から得られる、B 上の I 進商の標準開の写像。 |
| `reesCoefficientAdicOriginalModuleChartMap` | 元の R 上で計算する、実際の加群写像の I 進商の標準開の写像。 |
| `reesCoefficientAdicModuleChartMap_transition` | B 上の I 進標準開写像は、実際の I 進遷移と可換。 |
| `reesCoefficientAdicOriginalModuleChartMap_transition` | R 上の I 進標準開写像も、実際の I 進遷移と可換。 |
| `reesCoefficientAdicChartIso_module_naturality` | 各 I 進段の標準開係数比較は、実際の加群写像に自然。 |
| `reesCoefficientAdicOriginalCechModuleMap` | 元の R 上での、実際の加群写像からの I 進 Čech コホモロジーの写像。 |
| `reesCoefficientAdicRestrictedCechModuleMap` | B 上の実際の加群写像からの I 進 Čech 写像の係数制限。 |
| `reesCoefficientAdicOriginalCechModuleMap_transition` | R 上の実際の I 進 Čech 写像は遷移と可換。 |
| `reesCoefficientAdicRestrictedCechModuleMap_transition` | B 上の実際の I 進 Čech 写像の係数制限も遷移と可換。 |
| `reesCoefficientAdicCechIso_module_naturality` | I 進 Čech コホモロジーの係数比較は、実際の加群写像に自然。 |
| `reesCoefficientAdicQuotientModuleMap` | 変更後の多項式環上で見た、実際の加群写像の I 進商への降下。 |
| `reesCoefficientAdicQuotientModuleMap_restrictScalars` | 商係数の I 進商の写像の係数制限は、元の実際の商写像である。 |
| `reesCoefficientAdicQuotientModuleMap_projection` | 商係数の I 進商の写像は、商への実際の射影と可換。 |
| `reesCoefficientAdicQuotientModuleMap_transition` | 商係数の I 進商の写像は、実際の I 進遷移と可換。 |
| `reesCoefficientAdicQuotientModuleMap_preservesPiece` | 商係数の I 進商の写像は、元の射が保つ Proj 次数を保つ。 |

コホモロジーと形式関数の主張は、原典 Stacks 30.20.5 の Hⁱ に対応する **Čech 版**。分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、この比較は形式化していない。完備化は引き続き元の R 上の I 進完備化であり、非平坦なコホモロジーとテンソル積の交換は使っていない。

**停止点 2e ではない。** 閉厚化の商係数表示については、元の任意の次数付き加群写像、実際の I 進遷移、互換族、標準完備化写像、形式関数まで自然な可換式を供給した。次の主要な作業群は、共通アフィン細分、flat なテンソル底変換、実際の Čech Frobenius と p 倍の指数、filtered colimit の比較。今回の線形な写像の自然性を、これら四群の具体的な比較の完成とは数えない。一般の固有射の有限性・Stein 分解・導来関手の Hⁱ との比較は作っていない。

全ビルド・監査は共有鍵 `with_build_lock.sh --wait 3600` を経由し、待ちは同じ worktree から一つだけ、鍵は一回ごとに返した。ルート全体のビルドは行わず、取り込みは調整役に任せる。既存の宣言の型・本文、最終出力と利用側の `SerrePositivity.Cech.AugmentedRingCechExact` の型は変更していない。新規宣言に `sorry`・`admit`・追加公理・計算量上限の追加はない。宇宙の条件と `Module.Finite.small`・`Shrink.linearEquiv` による移送の方針も保つ。

## Čech の実際のテンソル底変換と局所化への接続（11-12）

`1bc0f3ee1` に新規 5 モジュールと直接 importer を保存（452 行）。対象と直接 importer `SerrePositivity.AlgebraicGeometry` のビルドは **4,315 jobs 成功**。別の共有鍵で行った公式監査は **6,927 宣言・標準三公理のみ**。

登録モジュール（すべて `SerrePositivity.AlgebraicGeometry` の下）：

- `ProjectiveCechFlatBaseChange`
- `ProjectiveCechTensorBaseChange`
- `ProjectiveCechTensorNaturality`
- `ProjectiveNatGradedTensorBaseChange`
- `ProjectiveRightTensorLocalization`

有限な被覆の係数図式 D と任意の環準同型 φ:R→B に対し、実際の `ModuleCat.extendScalars φ` と全タプル Čech 複体の比較を作った。各項は有限なタプル集合上の積なので、`TensorProduct.piRight` でテンソル積と有限積を交換できる。純テンソル上で交代和の微分と可換と示し、複体の同型へまとめた。これは平坦性を仮定せず成立し、係数図式の任意の自然変換に自然である。複体の比較は関手の自然同型としても供給した。

φ が flat な場合だけ、Mathlib の `ModuleCat.preservesFiniteLimits_extendScalars_of_flat` と左随伴による有限余極限の保存を使い、

B ⊗_R H_Cech^q(D) ≅ H_Cech^q(D ⋙ extendScalars φ)

を構成した。このコホモロジーの同型も係数図式の射に自然である。元の R 上の Čech コホモロジーが有限なら、右辺は B 上有限と分かった。原典の Hⁱ の flat 底変換の番号は [Stacks 30.5.2(2), 02KH](https://stacks.math.columbia.edu/tag/02KH) で確認した。

これを、次数付き多項式加群の実際の標準開図式へ適用した。`projectiveNatGradedTensorChartDiagram` は、各標準開の係数を実際に B とテンソル積した図式である。元の R が Noether、加群が R[X] 上有限という従来の仮定と flat な φ から、この図式の Čech コホモロジーが B 上有限と示した。**B の Noether 性は仮定しない。** 比較同型は、元の次数を保つ多項式加群の射に自然である。

標準開の分数表示への接続では、R→P、P 加群 M、R 加群 N と任意の乗法的集合 S⊂P に対して、

S⁻¹(M ⊗_R N) ≃ₗ[P] (S⁻¹M) ⊗_R N

を Mathlib の局所化の普遍性から作った。純テンソルの分数は (m⊗n)/s ↦ (m/s)⊗n で計算できる。P 線形な M の写像と可換で、S が f の冪の場合は標準開を狭める制限にも自然である。この周囲の局所化の比較にも平坦性は要らない。

宣言と主張（ローカルな型クラス設定を除く 20 件）：

| 宣言 | 主張 |
|---|---|
| `projectiveCechFlatBaseChangeIso` | flat なテンソル底変換は、有限被覆の Čech コホモロジーと交換する。 |
| `projectiveCechFlatBaseChangeIso_naturality` | flat な Čech 底変換の比較は、係数図式の任意の射に自然。 |
| `projectiveCechFlatBaseChange_finite` | flat 底変換後の Čech コホモロジーは、元のコホモロジーの有限生成性を保つ。 |
| `projectiveCechTensorCochainsIso` | 実際のテンソル底変換は、加群の射の加法を保つ。 -/ |
| `projectiveCechTensorCochainsIso_tmul` | 各項のテンソル比較は、純テンソルをタプルごとに評価する。 |
| `projectiveCechTensorCochainsIso_differential` | テンソル積と有限積の比較は、Čech の交代和の余境界と可換。 |
| `projectiveCechTensorComplexIso` | 有限被覆の全タプル Čech 複体は、実際のテンソル底変換と交換する。 |
| `projectiveCechTensorCochainsIso_naturality` | Čech 各項のテンソル比較は、任意の係数図式の射に自然。 |
| `projectiveCechTensorComplexIso_naturality` | Čech 複体のテンソル比較は、係数図式の自然変換と可換。 |
| `projectiveCechTensorComplexNatIso` | Čech 複体とテンソル底変換の比較を、係数図式の圏上の自然同型にする。 |
| `projectiveNatGradedTensorChartDiagram` | 各標準開の係数を実際に B とテンソル積した図式。 |
| `projectiveNatGradedTensorCechIso` | 標準開 Čech コホモロジーのテンソル積と、テンソル係数の Čech 計算との同型。 |
| `projectiveNatGradedTensorCechIso_naturality` | テンソル係数の標準開 Čech 比較は、次数を保つ加群写像に自然。 |
| `projectiveNatGradedTensorCechHomology_finite` | flat なテンソル係数の標準開 Čech コホモロジーは B 上有限生成。 |
| `projectiveLocalizedModule_mk_add` | 同じ分母を持つ局所化の分数は、分子について加法的である。 |
| `projectiveRightTensorLocalizationEquiv` | 加群の実際の局所化と右テンソル積を交換する、P 線形な同型。 |
| `projectiveRightTensorLocalizationEquiv_mk_one` | 局所化と右テンソル積の比較は、分母一の純テンソルを保つ。 |
| `projectiveRightTensorLocalizationEquiv_mk` | 局所化と右テンソル積の比較は、純テンソルの分母を保つ。 |
| `projectiveRightTensorLocalizationEquiv_naturality` | 局所化と右テンソル積の比較は、P 線形な加群写像に自然。 |
| `projectiveRightTensorLocalizationEquiv_restriction` | 局所化と右テンソル積の比較は、標準開を狭める制限にも自然。 |

**今回の範囲と次の接続。** 上の Čech 比較の右辺は D の各係数をテンソル積した図式である。標準開への特殊化でも、まだ「B 上へ基底変更した次数付き加群の、次数零の局所化による標準開図式」との同型は含まない。その接続には、基底変更した多項式加群の B[X] 作用と次数成分、斉次局所化の指定次数部分とテンソル積の照合、そこでの B 線形性と制限射の可換性をまとめる必要がある。周囲の局所化の比較だけで、§9 の底変換の整合性の完成とは呼ばない。元の R[X] を B 代数と仮定する形にはしない。

従って **停止点 2e ではない**。次はこの次数零の接続を進め、既存の閉厚化・I 進系の自然性と合わせる。共通アフィン細分、実際の Čech Frobenius と p 倍の指数、filtered colimit の比較も残っている。導来関手の層コホモロジーとの比較、非平坦なコホモロジーとテンソル積の交換、一般の固有射の有限性・Stein 分解は作っていない。コホモロジーの主張の docstring は原典の Hⁱ の番号と **Čech 版**であることを示し、分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、この比較は形式化しないと明記した。

全ビルド・監査は共有鍵 `with_build_lock.sh --wait 3600` を経由し、同じ worktree の待ちは一つだけ、鍵は一回ごとに返した。ルート全体のビルドは行っていない。既存の宣言の型・本文、最終出力と利用側の `SerrePositivity.Cech.AugmentedRingCechExact` の型は変更していない。新規宣言に `sorry`・`admit`・追加公理・計算量上限の追加はない。宇宙の条件と `Module.Finite.small`・`Shrink.linearEquiv` による移送の方針も保つ。


## 2026-11-12：基底変更後の多項式作用と次数成分（2e 途中）

実装コミット：`bad8a3243`。対象ビルドと直接の importer `SerrePositivity.AlgebraicGeometry` は成功（4,320 jobs）。監査は **7,000 宣言、標準三公理 `propext`・`Classical.choice`・`Quot.sound` のみ**。生成宣言を含む監査対象は前回 6,927 から 73 増えた。5 モジュールと入口の import 追加、計 429 行。既存宣言の型と本文は変更していない。

前の比較の右辺は、元の標準開の係数をテンソル積した図式だった。今回、その接続先になる実際の B[X] 加群 M⊗_R B と次数成分、標準開図式を構成した。

まず交換同型から M⊗_R B の右係数 B の作用を入れ、元の R[X] の作用との可換性を示した。この二つの作用を B⊗_R R[X] の作用にまとめ、多項式環のテンソル比較で B[X] の作用へ移した。係数変更された元の多項式の作用、定数多項式の作用、純テンソル上の単項式の作用をそれぞれ計算し、元の R と R[X]、右係数 B に対するスカラー塔を示した。元の R[X] を B 代数と仮定しない。R[X] 線形な射も実際の B[X] 線形な射へ送れる。

次数 j の成分を (G j)⊗_R B→M⊗_R B の像として定めた。単項式ごとの計算と加法から B[X] の次数付き作用を示し、元の次数を保つ射がこの次数成分も保つことを証明した。ここまでは平坦性を仮定しない。flat な場合は元の次数成分からのテンソル写像が単射なので、(G j)⊗_R B と新しい次数成分の B 線形同型を得た。この次数成分を使った実際の標準開図式と、次数付き加群の射が誘導する図式の射も構成した。

登録したモジュール（すべて `SerrePositivity.AlgebraicGeometry` の下）：

- `TensorCoefficientRightModule`
- `TensorCoefficientAlgebraModule`
- `ProjectiveTensorPolynomialModule`
- `ProjectiveTensorGrading`
- `ProjectiveTensorGradedChart`

宣言と主張（ローカルな型クラス設定を除く 32 件）：

| 宣言 | 主張 |
|---|---|
| `tensorRightCoefficientModule` | 右係数のテンソル積に、交換同型から B 加群構造を入れる。 |
| `tensorRightCoefficient_smul_tmul` | 係数 B の作用は、純テンソルの右因子への乗法で計算できる。 |
| `tensorRightCoefficient_scalarTower` | 右係数の B 作用は、元の R 作用と両立する。 |
| `tensorRightCoefficientComm` | テンソル積の交換同型は、右係数の B 加群構造について B 線形。 |
| `tensorRightCoefficientComm_tmul` | B 線形な交換同型の、純テンソル上の計算式。 |
| `tensorRightCoefficientMap` | 元の R 線形写像を、右係数テンソル積の B 線形写像として扱う。 |
| `tensorRightCoefficient_smulCommClass` | 左因子の P 作用と右係数 B の作用は可換。 |
| `tensorRightCoefficientAlgebraModule` | 二つの可換な作用をまとめた、B⊗_R P 上の加群構造。 |
| `tensorRightCoefficientAlgebra_tmul_smul` | テンソル代数の純テンソルの作用は、元の二つの作用の合成。 |
| `tensorRightCoefficientAlgebra_tmul_tmul` | 二重の純テンソル上の作用は、元の P 作用と B の乗法で計算できる。 |
| `tensorRightCoefficientAlgebra_coefficient_scalarTower` | テンソル代数の作用は、右係数 B の作用を拡張する。 |
| `tensorRightCoefficientAlgebra_scalarTower` | テンソル代数の作用は、元の基底 R の作用と両立する。 |
| `tensorRightCoefficientAlgebraMap` | P 線形な写像は、係数変更後のテンソル代数上でも線形。 |
| `projectiveTensorPolynomialModule` | 基底変更後の実際の多項式加群構造。 |
| `projectiveTensorPolynomial_map_smul` | 係数変更した多項式の作用は、元の多項式の作用と一致する。 |
| `projectiveTensorPolynomial_C_smul` | 定数多項式の作用は、右係数 B の作用に一致する。 |
| `projectiveTensorPolynomial_monomial_tmul` | 単項式の作用は、元の単項式の作用と右係数の乗法で計算できる。 |
| `projectiveTensorPolynomial_coefficient_scalarTower` | B[X] の作用は、右係数 B の作用を拡張する。 |
| `projectiveTensorPolynomial_base_scalarTower` | B[X] の作用は、元の基底 R の作用と両立する。 |
| `projectiveTensorPolynomial_polynomial_scalarTower` | 基底変更後の多項式作用は、元の R[X] の作用と両立する。 |
| `projectiveTensorPolynomialMap` | 元の多項式加群の射を、基底変更後の B[X] 線形な射へ送る。 |
| `projectiveTensorPolynomialMap_tmul` | 基底変更後の多項式加群の射は、純テンソルの元の因子だけに作用する。 |
| `projectiveTensorPiece` | 基底変更した次数成分は、元の次数成分のテンソル積の像。 |
| `projectiveTensorPiece_tmul_mem` | 元の次数成分の純テンソルは、基底変更後の同じ次数成分に入る。 |
| `projectiveTensorPiece_monomial_smul_mem` | 単項式の作用は、テンソル像で定めた次数を加える。 |
| `projectiveTensorPiece_gradedSMul` | 基底変更後の B[X] の斉次作用は、テンソル像の次数を保つ。 |
| `projectiveTensorPiece_map_mem` | 次数を保つ元の加群写像は、テンソル像の次数成分も保つ。 |
| `projectiveTensorGradedModuleChartDiagram` | 基底変更後の B[X] 加群の、指定次数の実際の標準開図式。 |
| `projectiveTensorPiece_injective` | flat な基底変更では、元の次数成分のテンソル積は全体のテンソル積に単射。 |
| `projectiveTensorPieceEquiv` | flat な基底変更後の次数成分は、元の次数成分のテンソル積と同型。 |
| `projectiveTensorPieceEquiv_tmul` | 次数成分の比較は、純テンソルの元を同じ元へ送る。 |
| `projectiveTensorGradedModuleChartMap` | 次数付き加群の射から、基底変更後の実際の標準開図式の射を得る。 |

**残り。** 今回は、テンソル係数の旧標準開図式と、B[X] 加群の指定次数の斉次局所化からなる新標準開図式との同型までは作っていない。次は、周囲の局所化とテンソル積の既存の比較を指定次数部分へ制限し、B 線形性、標準開の制限射、次数を保つ加群写像との自然性をまとめる。この同型を既存の flat な Čech 比較と合成して、底変換の接続を完了する。共通アフィン細分、実際の Čech Frobenius と p 倍の指数、filtered colimit の比較も残る。従って **停止点 2e ではない**。最終出力 `SerrePositivity.Cech.AugmentedRingCechExact` と利用側の型は変更していない。大きい宇宙の入口は引き続き `Module.Finite.small` と `Shrink.linearEquiv` で移送する。

全ビルドと監査は共有鍵 `scripts/refactor/with_build_lock.sh --wait 3600` を経由した。同じ worktree の待ちは一つにし、一回の対象ビルド／監査ごとに鍵を返した。ルート全体のビルドは行っていない。入力の保存確認では、前回確認済みの 690 ファイルのうち変更は入口の import 追加だけで、新規 5 ファイルを含む 695 ファイルを記録した。新規宣言に `sorry`・`admit`・追加公理・計算量上限の追加はなく、`git diff --check` も通った。


## 2026-11-12 09:40：指定次数のテンソル比較の途中と、ビルドの一時停止

調整役から、KL-W1 verify のメモリと swap の都合により、終了連絡までビルド・監査を控える指示を受けた。共有鍵の待ちを取り消し、当レーンの実行が終了したことを確認した。終了連絡を受けるまでは再開しない。

`bad8a3243` の続きとして、指定次数の局所化とテンソル積の接続を書いている。任意の分子族 V に対し、V の各成分のテンソル像を分子に持つ局所化への写像を作り、分数写像の像の上限を使って全射性を示した。flat な場合には、元の指定次数部分の包含をテンソルした写像の単射性から同型を得る。この一般比較には、分子族が分母倍で次の成分に移るという仮定は不要である。

次に、局所化する元の環 P と、B 係数の作用を共に持つ変更先 Q を使い、局所化環の既存の変更比較と合成した。分子族が分母倍で次へ移る場合は、一つの斉次分数の表示を使って B 線形性を証明できる。元の P に B 代数構造を仮定する必要はない。この二本のモジュールはそれぞれ対象と直接 importer のビルドを通しているが、**今回の束の監査はまだ実行しておらず、数学は未コミット**である。

R[X]→B[X] の標準開への適用では、負次数の零延長と次数成分のテンソル像が交換することを示し、各標準開の指定次数部分の B 線形同型を作った。純テンソルの分数の分母の冪を保つ公式から、標準開を狭める制限との可換性も書いた。図式全体の同型は、Mathlib の `extendScalars φ` と同じ `φ.toAlgebra` を入口で選ぶ。比較写像の深い展開による `whnf` timeout を避けるため、成分の同型と純テンソル公式を分割した最新編集は、停止指示のため未検証である。計算量上限は増やしていない。

停止中の紙の作業として、次数を保つ加群写像 M→N に対する自然性の下書きを用意した。元の標準開の元を m/fⁿ と表せば、両経路とも f(m)⊗b を分子、変更後の fⁿ を分母に持つので、成分の四角形は一致する。これを実際の標準開図式の自然性へまとめ、既存の flat な Čech 比較と合成する。続いて閉厚化・I 進系に関する前の自然性へ渡す。

再開後は、最新の図式比較を小さなビルドで確認し、加群写像への自然性と Čech 比較の合成を実装する。対象と直接 importer が通った後、別の共有鍵で監査し、検証済みの数学だけをコミットする。**停止点 2e ではない。** 共通アフィン細分、実際の Čech Frobenius と指数 n→p*n、filtered colimit との比較も残る。最終出力と利用側の `SerrePositivity.Cech.AugmentedRingCechExact` は変更していない。


### 停止中の証明メモ：図式の自然性から Čech 比較へ

次数を保つ R[X] 線形写像 f:M→N に対し、元の標準開の図式の射を η、変更後の実際の B[X] 加群の図式の射を η_B、各図式の比較を e_M・e_N と書く。標準開 T の元 u=m/sⁿ の純テンソルについて、

`e_N(b ⊗ η_T(u)) = (η_B)_T(e_M(b ⊗ u))`

は、両辺の分子が f(m)⊗b、分母が変更先の sⁿ であることから従う。元の加群の射が整数への零延長後の次数も保つことには、既存の `projectiveNatGradingInt_map_mem` を使う。テンソル帰納と自然変換の成分ごとの外延性で、`(η ⋙ extendScalars) ≫ e_N = e_M ≫ η_B` にまとめる。成分の同型・純テンソル公式を別の補題にして、自然変換の証明の中で比較写像全体を展開しない。

その図式の自然同型を `fullCechComplexFunctor.mapIso` へ送り、さらに `HomologicalComplex.homologyFunctor.mapIso` へ送る。既存の `projectiveNatGradedTensorCechIso` と合成すれば、比較先は各係数をテンソル積しただけの図式から、基底変更後の B[X] 加群の実際の標準開の Čech H へ移る。合成の自然性は、既存の flat な Čech 比較の自然性と上の図式の四角形を関手で写して得る。既存の射影有限性とこの同型を使えば、B 自身に Noether 性を仮定せず、変更後の Čech H の B 上の有限生成性も得られる。この合成と有限性の Lean 下書きは `scheme-drafts/` に置き、未検証として本体の入口へは登録していない。

### 停止中の証明メモ：残る三群の実装境界

**filtered colimit。** 各 Čech 次数では被覆の添字集合を有限かつ固定し、有限積だけを余極限と交換する。Mathlib の `ModuleCat/AB.lean` は加群圏の AB5 を供給し、filtered な余極限関手の有限極限の保存を使える。コホモロジーの比較は、各複体の短複体を関手圏上に作り、余極限関手に対する `ShortComplex.mapHomologyIso` と次数ごとの余極限の比較を合成する。B1 の `Cech/Filtered.lean` に同じ短複体の作り方がある。最終出力の環の増大 Čech 完全性は既存の `isCechExact_colimit` を使い、作り直さない。

Noether 近似では基底環 R_j も動くので、固定した R 上の加群の余極限だけを示して完了としない。有限型 F_p モデルなら、まず全ての加群と写像を共通の F_p[X] 上に係数制限して局所化を比較し、各段の R_j[X] の実際の標準開との既存の係数変更比較へ渡す。一般の環なら共通の基底を ℤ とする。有限個の被覆の生成元を一つの有限段へ降ろし、そこから先の添字集合を固定する。次数零成分と余極限の交換では、無限積や無限個の核との交換を仮定しない。次数分解の射影による有限な核・像の計算、または分子族の分数表示と二つの filtered 添字の共通上界を使う。完備化と任意の filtered colimit の交換は使わない。

**Frobenius。** 正標数の次数付き環 A の実際の Frobenius は、次数 d の元を次数 p*d の元へ写す。斉次分数 m/sⁿ は mᵖ/s^(p*n) へ写り、標準開の同じ台を保つ。一般の R[X] 線形写像の API に直接渡すことはできないので、分子の写像を Frobenius 半線形として扱い、分母も p 乗へ送る局所化の写像を作る。各標準開でこの分数式を示せば、制限射との可換性は追加因子の p 乗の式に帰着する。加法群の射は整数係数の交代和と可換なので、全タプル Čech 複体の射へ渡せる。IⁿA→I^(p*n)A と A/IⁿA→A/I^(p*n)A を実際の Frobenius から作り、既存の `frobeniusSemilinear_ideal_power_control` の評価と、I 進系の遷移の自然性へつなぐ。指数の共終性には p>0 を明示し、BS17 の有限型 F_p モデルでは素数 p の仮定を使う。

**共通アフィン細分。** 二つの有限アフィン被覆 U・V に対し、二つの全タプルの組で交叉上の切断を取る二重図式を作る。分離性で交叉がアフィンであることを使い、各アフィン交叉上の増大 Čech 列の完全性を供給する。B1 の `doubleCech_acyclic_iff` は零番の行・列の増大完全性を比較する API なので、これだけを任意の正次数のコホモロジーの同型と読み替えない。形式関数の各 Hⁱ の被覆比較には、有限対角線の全複体への二つの edge map が quasi-isomorphism であること、または refinement map の cone の acyclicity を示す橋が要る。B1 の二重複体の有限対角線の消去を再利用できる形で橋を作り、係数の射に自然な比較として供給する。最終的な増大 Čech の完全性の判定では B1 の既存 API をそのまま使う。Mathlib の `Sites/SheafCohomology/Cech.lean` にある Čech 複体の定義だけを、共通細分の quasi-isomorphism の証拠とは数えない。

以上は、ビルド停止中に整理した証明方針と未検証の下書きである。検証済みの数学の完成報告ではなく、停止点 2e の検収には含めない。


### Frobenius の下書きで確認した、空の標準開の扱い

Mathlib の `LocalizedModule` は、係数加群 A が P 代数である環の場合に環構造を持ち、`LocalizedModule.mk_pow` が `(m/s)^p = m^p/s^p` を供給する。このため、構造層の Frobenius は任意の加群の半線形局所化を先に作らず、実際の局所化環の冪写像から構成できる。

ただし、標準開は空の場合があり、局所化環に `Nontrivial` を仮定してはいけない。元の環の `ExpChar A p` を局所化へそのまま推論させることもできない。Mathlib の `ExpChar` は標数零か素標数を表し、零環にはこの形の構造がないためである。必要なのは「p の像が零なら、p 乗は環準同型」という、零環も許す主張である。素数 p に対する既存の `add_pow_prime_eq` と `(p:A)=0` から冪の環準同型を作り、局所化では `LocalizedModule.numeratorRingHom` で p が零であることを移せばよい。通常の指数標数がある環では、この写像は既存の `frobenius A p` と同じ冪写像になる。

この入口と分数の指数 n→p*n の公式の未検証下書きを `scheme-drafts/ProjectiveLocalizedFrobenius.lean` に置いた。新しい非自明性や局所化環の標数の仮定を付ける案は採らない。ビルド・監査は引き続き停止中で、この下書きは本体に登録していない。


## 2026-11-12 09:50 の依頼：停止中の下書きと次段の準備

ビルド・監査を行わず、`scheme-drafts/ReesClosedTensorComparison.lean` に M⊗_R(R/J) と既存の閉厚化 M/JM の商係数表示との照合を書いた。Mathlib の `tensorQuotEquivQuotSMul` と `reesExtendedAdic_restrictScalars` を使い、右係数の作用と実際の商への射影を合わせる。平坦性も H とテンソルの交換も仮定しない。未検証のため本体へ未登録・未コミット。

紙の成果は [2f の段取り](scheme-w1-2f-route.md) と [停止点 2e 報告の下書き](scheme-w1-2e-report-draft.md)。前者は主張の型の案、2e の出力、不足する橋、約 3,000–9,000 行の見込みを記した。後者は §9 の五つの比較について、検証済み・下書き・未完を区別し、案 (b) の条件を満たすための検収項目を記した。これらを完成した数学の検収とは扱わない。

2f の次数零では、B_Y/IB_Y→H⁰(E) の核を 2e の核の評価と Frobenius によって nil にし、像の安定化によって各元の十分高い p 冪を像へ入れる証明案を具体化した。既存の普遍同相の p 冪判定と有限射の導手による四角形へ渡し、Stein 分解を使わない予定である。実際の環の H⁰ と Frobenius の厚化の写像の照合は、これから形式化する。

再開の合図の後は、調整役の指定どおり図式比較の対象ビルドから始める。現在の worktree の未検証 Lean はそのまま保存し、検証前にコミットしない。


## 2026-11-12：実際の指定次数の標準開と、テンソル係数図式との同型

数学コミット `1b359a90e`。対象と直接 importer のビルド成功（4,324 jobs）、別実行の監査は **7,086 宣言・標準三公理のみ**。4 モジュールと入口の import 追加、計 531 行。main `27f0ea688` は `0314ebff7` で取り込んだ。検証した 699 入力のハッシュは取り込み前後で全て一致した。

任意の分子族 V に対し、元の斉次局所化と右テンソル積から、分子を V の各成分のテンソル像に置き換えた斉次局所化への写像を作った。分数写像の像の上限を比較して全射性を示し、flat な右テンソル積では元の指定次数部分の包含の単射性から同型を得た。元の局所化環 P を B 代数と仮定せず、共通の変更先 Q で局所化環を変更し、分子族の分母倍の条件から B 線形性を示した。

これを R[X]→B[X] の標準開へ適用した。負次数の零延長と次数成分のテンソル像の交換を示し、各標準開の指定次数部分の B 線形な同型を作った。分数の分母の冪を保つ公式により、標準開を狭める制限との可換性を示した。最後に ModuleCat.extendScalars φ と同じ φ.toAlgebra を入口で選び、実際の B[X] 加群の標準開図式との自然同型を構成した。成分の同型と純テンソル公式を分けることで whnf timeout を解消し、計算量上限は増やしていない。

登録モジュール：

- `ProjectiveGradedTensorLocalization`
- `ProjectiveGradedTensorCoefficientChange`
- `ProjectiveTensorChartComparison`
- `ProjectiveTensorChartDiagram`

宣言と主張（ローカルな型クラス設定を除く 25 件）：

| 宣言 | 主張 |
|---|---|
| `projectiveTensorNumerator` | 分子族の右テンソル像を、元の基底環上の部分加群として扱う。 |
| `projectiveTensorNumerator_fraction_mem` | 純テンソルの斉次分数は、テンソル像の分子族に属する。 |
| `projectiveGradedTensorLocalization_symm_tmul_mem` | 周囲の局所化の比較の逆は、元の指定次数部分の純テンソルを保つ。 |
| `projectiveGradedTensorLocalizationMap` | 右テンソル像の指定次数部分への、元の斉次局所化からの比較写像。 |
| `projectiveGradedTensorLocalizationMap_val` | 斉次局所化の比較写像の周囲での値は、通常の局所化比較の逆である。 |
| `projectiveGradedTensorLocalizationMap_injective` | flat な右テンソル積では、斉次局所化の比較写像は単射。 |
| `projectiveGradedTensorLocalizationMap_fraction` | 純テンソルの比較写像は、元の分数の分母を保つ。 |
| `projectiveGradedTensorLocalizationMap_surjective` | 指定次数の比較写像は全射。分子族のテンソル像の定義だけで成立する。 |
| `projectiveGradedTensorLocalizationEquiv` | flat な右テンソル積は、指定分子族の斉次局所化と交換する。 |
| `projectiveTensorCoefficientNumerator` | 分子族のテンソル像を、変更後の基底環 B 上の部分加群として扱う。 |
| `projectiveTensorCoefficientNumerator_restrict` | B 上の分子のテンソル像を R に制限すると、元の R 上のテンソル像になる。 |
| `projectiveGradedTensorCoefficientEquiv` | 局所化する環を変えた、指定分子族のテンソル比較。まず R 線形に構成する。 |
| `projectiveGradedTensorCoefficientEquiv_fraction` | 係数環の変更を含めた比較も、純テンソル分数の分子と分母の冪を保つ。 |
| `projectiveGradedTensorCoefficientEquiv_smul` | 分子族が分母倍で次へ移るなら、係数変更を含む比較は B の作用と可換。 |
| `projectiveGradedTensorCoefficientLinearEquiv` | flat な基底変更と斉次局所化の比較を、B 線形な同型にする。 |
| `projectiveTensorPiece_int` | 負次数を零に延ばす操作は、次数成分のテンソル像と交換する。 |
| `projectiveTensorChartNumerator_eq` | 分母の冪ごとのテンソル像は、基底変更後の指定次数の分子と一致する。 |
| `projectiveTensorChartRightLinearEquiv` | 基底変更後の各標準開の指定次数部分と、元の標準開の右テンソル積との B 線形同型。 |
| `projectiveTensorChartLinearEquiv` | 基底変更後の各標準開の指定次数部分と、元の標準開の左テンソル積との B 線形同型。 |
| `projectiveTensorChartRightLinearEquiv_fraction` | 右テンソルによる標準開の比較は、指定次数の純テンソル分数を保つ。 |
| `projectiveTensorChartLinearEquiv_fraction` | 左テンソルによる標準開の比較も、指定次数の純テンソル分数を保つ。 |
| `projectiveTensorChartLinearEquiv_restriction` | 各標準開のテンソル比較は、標準開を狭める制限と可換。 |
| `projectiveTensorChartComponentIso` | 環準同型から係数構造を固定した、各標準開の実際のテンソル比較。 |
| `projectiveTensorChartComponentIso_hom_tmul` | 各標準開の環準同型による比較は、左純テンソルの既存の比較と一致する。 |
| `projectiveTensorChartDiagramIso` | 元の標準開図式のテンソル底変換と、基底変更後の実際の標準開図式との自然同型。 |

今回の自然性は標準開の制限についてのもの。任意の次数付き加群の射に関する自然性と、既存の flat な Čech H 比較との合成は次の束で検証する。R/J の非 flat な H とテンソル積の交換は主張していない。共通アフィン細分、実際の Čech Frobenius、filtered colimit の比較も残る。**停止点 2e ではない。**


## 2026-11-12：実際の標準開の flat Čech 比較と加群写像への自然性

対象と直接 importer のビルド成功（4,326 jobs）、別実行の監査は **7,110 宣言・標準三公理のみ**。2 モジュールと入口の import 追加、230 行。前の検証入力 699 の変更は入口の import 追加だけで、新規を含む 701 入力を記録した。ビルド・監査は共有鍵 `--wait 3600` を一回ごとに返して実行した。

標準開図式のテンソル比較を、元の次数を保つ R[X] 線形な加群写像に自然と示した。純テンソルの分数で両経路が同じ分子 f(m)⊗b と同じ分母を持つことを示し、図式全体の四角形へまとめた。これを Čech 複体とコホモロジーへ送り、既存の flat な比較と合成した。

比較先は **基底変更後の B[X] 加群の実際の指定次数の標準開図式の Čech H** であり、旧図式の係数をテンソルしただけの図式からの接続が入った。Noether な元の基底上の有限生成次数付き加群なら、変更先 B の Noether 性を仮定せず、この実際の標準開の Čech H は B 上有限生成と示した。H とテンソル積を交換するところには flat を仮定している。

登録モジュール：`ProjectiveTensorChartNaturality`、`ProjectiveNativeTensorCechBaseChange`。

| 宣言 | 主張 |
|---|---|
| `projectiveTensorChartLinearEquiv_map` | 各標準開の実際のテンソル比較は、次数を保つ加群写像と可換。 |
| `projectiveTensorChartDiagramIso_naturality` | 標準開図式のテンソル比較の自然同型は、次数付き加群の射が誘導する自然変換と可換。 |
| `projectiveNativeTensorCechIso` | flat なテンソル底変換と、変更後の実際の標準開の Čech H との同型。 |
| `projectiveNativeTensorCechIso_naturality` | 実際の標準開の Čech flat 比較は、元の次数を保つ加群写像に自然。 |
| `projectiveNativeTensorCechHomology_finite` | 実際の flat 底変換後の標準開の Čech H は、変更先 B 上有限生成。B の Noether 性は不要。 |

原典 Stacks 30.5.2(2) と 30.19.2 の Hⁱ に対応する **Čech 版**として docstring に明記した。分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、この比較は形式化しない。非 flat な H とテンソル積の交換は主張しない。

次は R/J の実際の閉厚化との追加の係数表示を検証する。実際の Čech Frobenius、共通アフィン細分、filtered colimit の比較が残り、**停止点 2e ではない**。最終出力の `AugmentedRingCechExact` と利用側の型は変更していない。


## 2026-11-12：R/J のテンソル表示と既存の閉厚化との照合

数学コミット `5d5943541`。対象と直接 importer のビルド成功（4,329 jobs）、別実行の監査は **7,172 宣言・標準三公理のみ**。3 モジュールを登録し、15 件の数学宣言を追加した。前の検証入力 701 の変更は入口の import 追加だけで、新規を含む 704 入力を記録した。共有鍵 `--wait 3600` を一回のビルド・監査ごとに返して実行した。

M⊗_R(R/J) と既存の実際の閉厚化 M/JM を、Mathlib のテンソルと商の比較、および拡大イデアルの作用の係数制限から同定した。R/J 線形な同型へ昇格し、元の R[X] の作用と変更先の (R/J)[X] の作用を保つことを示した。元の M からの射影は m↦m⊗1 の式で一致する。

テンソル像の Proj 次数成分が既存の商係数の閉厚化の次数成分へ対応することを両方向で示し、既存の次数付き加群の同型を標準開へ送る関手を使った。これにより、R/J にテンソルした加群の実際の標準開図式と、前に実装した商係数の閉厚化の図式の同型、および Čech H の同型を得た。元の任意の次数を保つ R[X] 線形写像について、加群の射、標準開の図式、Čech H の三段で自然性を示した。変更先の射は以前からの `reesClosedCoefficientModuleMap`、`reesClosedCoefficientModuleChartMap`、`reesClosedCoefficientModuleCechMap` そのもので、別の条件付きの射へ置き換えていない。

R→R/J の平坦性は仮定しない。ここで同定したのは、基底変更後の加群と既存の閉厚化の **実際の二つの表示**であり、H(M)⊗_R(R/J) と H(M/JM) の交換ではない。新しい自然性は、以前の商係数表示と I 進系・形式関数の自然性へ、同じ商写像を通して合成できる。

登録モジュール：

- `ReesClosedTensorComparison`
- `ReesClosedTensorChart`
- `ReesClosedTensorNaturality`

宣言と主張（ローカルな型クラス設定を除く 15 件）：

| 宣言 | 主張 |
|---|---|
| `reesClosedTensor_submodule_eq` | 拡大イデアルで定義した一段目の閉厚化は、実際の JM による商。 |
| `reesClosedTensorEquiv` | 既存の閉厚化と右テンソルの比較。まず元の基底環上で線形に構成する。 |
| `reesClosedTensorEquiv_tmul_mk` | テンソルと閉厚化の比較は、商環の代表を元の係数の作用として計算する。 |
| `reesClosedTensorEquiv_smul` | 商係数の作用についても、テンソルと閉厚化の比較は線形。 |
| `reesClosedTensorCoefficientEquiv` | 既存の R/J 係数の閉厚化との、R/J 線形な同型。 |
| `reesClosedTensorCoefficientEquiv_tmul_one` | 閉厚化の比較は、元の加群からの射影を保つ。 |
| `reesClosedTensorEquiv_polynomial_smul` | 商とテンソルの比較は、元の多項式環の作用を保つ。 |
| `reesClosedTensorPolynomialEquiv` | 既存の閉厚化の多項式係数表示と、テンソルの多項式作用との同型。 |
| `reesClosedTensorPiece_map_eq` | 次数成分のテンソル像は、既存の R/J 係数の商次数成分に一致する。 |
| `reesClosedTensorPiece_mem_iff` | 商とのテンソル比較は、元の次数成分を両方向で対応させる。 |
| `reesClosedTensorChartIso` | R/J にテンソルした加群の標準開図式と、既存の閉厚化の商係数図式との自然同型。 |
| `reesClosedTensorCechIso` | R/J にテンソルした加群の実際の標準開と、閉厚化の商係数表示の Čech 比較。 |
| `reesClosedTensorEquiv_naturality` | テンソルと閉厚化の比較は、元の多項式加群の射と可換。 |
| `reesClosedTensorChartIso_naturality` | R/J による標準開の表示の同型は、次数を保つ加群写像に自然。 |
| `reesClosedTensorCechIso_naturality` | R/J の実際の閉厚化の Čech 比較は、次数を保つ加群写像に自然。 |

実際の Čech Frobenius、共通アフィン細分、filtered colimit の比較が残り、**停止点 2e ではない**。コホモロジーの docstring は原典 Stacks 30.20.4–30.20.5 の Hⁱ の比較に使う Čech 版と明記した。分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、この比較は形式化しない。最終出力と利用側の `AugmentedRingCechExact` の型は変更していない。


## 2026-11-12：局所化と指定次数の Frobenius、半線形 Čech 写像の入口

数学コミット `69ace8712`。対象と直接 importer のビルド成功（4,332 jobs）、別実行の監査は **7,204 宣言・標準三公理のみ**。3 モジュールを登録し、15 件の数学宣言を追加した。前の検証入力 704 の変更は入口の import 追加だけで、新規を含む 707 入力を記録した。共有鍵 `--wait 3600` を各ビルド・監査ごとに返して実行した。

空の標準開も含め、p の像が零である環の p 乗写像を環準同型として構成した。局所化にもこの条件を移し、実際の局所化環の Frobenius を作った。局所化が非自明であることや、局所化環の ExpChar は仮定しない。分数 m/fⁿ を mᵖ/f^(p*n) へ送る式、標準開の制限との可換性、元の基底環の Frobenius に関する半線形性を示した。

分子族 V の元の p 乗が W の p 倍の指数の部分に入る場合、この実際の Frobenius を指定次数の斉次局所化へ制限した。自然数次数を整数へ零延長しても、p 乗が Proj 次数を p 倍することを示した。一般の係数制限への自然変換から、既存の Čech 係数制限比較を再利用してコホモロジーの半線形写像を作る入口も供給した。

登録モジュール：

- `ProjectiveLocalizedFrobenius`
- `ProjectiveCechSemilinearMap`
- `ProjectiveGradedFrobenius`

宣言と主張（ローカルな型クラス設定を除く 15 件）：

| 宣言 | 主張 |
|---|---|
| `projectivePrimePowerRingHom` | p の像が零であれば、零環も含め p 乗は環準同型である。 |
| `projectivePrimePowerRingHom_eq_frobenius` | 通常の指数標数の Frobenius と、p が零であることから作った冪写像は一致する。 |
| `projectiveLocalized_primeCast_eq_zero` | 元の係数環で p が零なら、局所化でも p は零。空の標準開の場合も含む。 |
| `projectiveLocalizedFrobenius` | 実際の局所化環の Frobenius。局所化が零環でも定義できる。 |
| `projectiveLocalizedFrobenius_mk` | 局所化の Frobenius は、分子と分母を共に p 乗へ送る。 |
| `projectiveFrobeniusDenominator_pow` | 分母 fⁿ の p 乗は、同じ f の n*p 冪。 |
| `projectiveLocalizedFrobenius_fraction` | 標準開の Frobenius は、元の分母の指数を p 倍にする。 |
| `projectiveModuleAwayRestriction_pow` | 局所化の制限は、係数環の作用による分子の冪の計算と可換。 |
| `projectiveLocalizedFrobenius_restriction` | 実際の局所化の Frobenius は、標準開を狭める制限と可換。 |
| `projectiveLocalizedFrobeniusSemilinear` | 実際の局所化の Frobenius は、元の基底環の Frobenius について半線形。 |
| `projectiveCechSemilinearHomologyMap` | 係数制限として与えた図式の写像は、Čech コホモロジーの半線形写像を誘導する。 |
| `projectiveGradedAwayFrobenius` | Frobenius は、分子の p 乗が対応する指定部分へ入る場合に斉次局所化へ降りる。 |
| `projectiveGradedAwayFrobenius_val` | 斉次局所化の Frobenius は、周囲の実際の局所化の Frobenius の制限。 |
| `projectiveNatGradingInt_pow_mem` | 自然数次数を整数へ零延長した後も、p 乗は Proj 次数を p 倍する。 |
| `projectiveNatGradingInt_chart_pow_mem` | 指定分母の n 冪の分子の p 乗は、p 倍の捻りと p*n 冪の分母に対応する。 |

標準開図式全体の Frobenius とその Čech 写像を具体化する `ProjectiveCechFrobenius.lean` は、通常の係数作用と Frobenius による制限作用の型合わせが未解決なので、入口から外して未コミットの下書きとして残した。係数の代数の射への自然性も下書きで、まだ完成と数えない。既存の n→p*n の I 進評価と実際の厚化の写像への接続、共通アフィン細分、filtered colimit の比較が残る。**停止点 2e ではない。**


## 2026-11-12：実際の Čech Frobenius、I 進商と環の閉厚化との照合

数学コミット **`72c7ff525`**。新規 7 モジュール（590 行）と入口の import 7 行、32 件の数学宣言（公開の次数付き構造の instance 二件を含み、local instance は除く）。対象と直接 importer `SerrePositivity.AlgebraicGeometry` のビルドは **4,339 jobs で成功**。別実行の標準監査は **7,276 宣言・標準三公理のみ**。共有鍵 `--wait 3600` は各ビルド・監査の間だけ持ち、待ちは一つにまとめた。既存の数学宣言の本文・型・名前、および計算量上限は変更していない。sorry・admit・新しい公理も追加していない。

標準開の実際の p 乗写像を、係数を Frobenius で制限した図式への自然変換にし、その Čech H の半線形写像を構成した。未検証だった型合わせは、`ModuleCat.ofHom` の対象を明示し、半線形の `map_smulₛₗ` を使うことで解決した。一般の半線形な係数の可換四角形を H へ送る補題を一つにまとめ、次数を保つ代数の射について、局所化・標準開図式・Čech H の三段の自然性を示した。

この **実際の** Čech Frobenius に既存のイデアル冪の制御を適用し、H 自身の I 進商で n→p*n の写像と遷移との可換性、I 進完備化の半線形写像と元の H からの写像の可換性を示した。遷移の証明を Čech H の内部で展開すると kernel timeout が出たため、一般の半線形加群の補題へ分離して適用した。上限は増やしていない。**H/IⁿH を、閉厚化の H と同一視してはいない。**

さらに、実際の環の商 A/J に元の次数成分の像を入れ、単位・積・多項式作用を保つことを示した。局所化が零環になる場合と、環の商自体が零になる場合も含めた。この実際の商写像と Čech Frobenius の可換性を検証した。Rees の実際の商加群 A/IⁿA と環の商 A/(IⁿA) の R 線形・R[X] 線形な比較を作り、同じ代表元と次数成分を保つことから、標準開図式と Čech H の同型へ送った。

登録モジュール：`FrobeniusAdicQuotient`、`ProjectiveCechFrobenius`、`ProjectiveCechSemilinearNaturality`、`ProjectiveFrobeniusNaturality`、`ProjectiveCechFrobeniusAdic`、`ProjectiveRingQuotientGrading`、`ReesClosedRingComparison`。

| 宣言 | 主張 |
|---|---|
| `frobeniusSemilinearShiftedQuotientMap` | 任意の Frobenius 半線形写像は、指数 n を p*n へ送る I 進商の写像を誘導する。 |
| `frobeniusSemilinearShiftedQuotientMap_mk` | その商写像は、代表元に元の半線形写像を適用する。 |
| `frobeniusSemilinearShiftedQuotientMap_transition` | 指数を p 倍する商写像は、I 進商の遷移と可換。 |
| `frobeniusSemilinearCompletionMap_of` | Frobenius 半線形な完備化写像は、元の加群からの写像を保つ。 |
| `projectiveNatGradedChartFrobenius` | 実際の標準開の指定次数の p 乗写像。捻り d を p*d へ送る。 |
| `projectiveNatGradedChartFrobenius_val` | 指定次数の写像は、周囲の局所化環の Frobenius の制限。 |
| `projectiveNatGradedChartFrobeniusNatTrans` | 各標準開の Frobenius は、係数を Frobenius で制限した標準開図式への自然変換。 |
| `projectiveNatGradedCechFrobenius` | 実際の標準開図式の Čech H の Frobenius 半線形写像。 |
| `projectiveCechSemilinearHomologyMap_naturality` | 半線形な係数図式の可換四角形は、同じ Čech H の可換四角形を与える。 |
| `projectiveLocalizedFrobenius_map` | 実際の局所化の Frobenius は、代数の射による局所化の写像と可換。 |
| `projectiveNatGradedChartFrobeniusNatTrans_naturality` | 標準開図式の Frobenius は、次数を保つ代数の射に自然。 |
| `projectiveNatGradedCechFrobenius_naturality` | 実際の Čech H の Frobenius は、次数を保つ代数の射に自然。 |
| `projectiveNatGradedCechFrobenius_ideal_power_control` | 実際の Čech Frobenius は、H の Iⁿ 倍を I^(p*n) 倍へ送る。 |
| `projectiveNatGradedCechFrobeniusAdicQuotientMap` | 実際の Čech Frobenius が H 自身の I 進商へ誘導する、指数 n→p*n の写像。 |
| `projectiveNatGradedCechFrobeniusAdicQuotientMap_mk` | この I 進商の写像は、同じ H の代表元に Frobenius を適用する。 |
| `projectiveNatGradedCechFrobeniusAdicQuotientMap_transition` | 実際の Čech Frobenius の I 進商の写像は、遷移と可換。 |
| `projectiveNatGradedCechFrobeniusAdicCompletionMap` | 実際の Čech Frobenius の I 進完備化の半線形写像。 |
| `projectiveNatGradedCechFrobeniusAdicCompletionMap_of` | 実際の Čech Frobenius の完備化は、元の H からの写像を保つ。 |
| `projectiveRingQuotientGrade` | 実際の商環の次数成分を、元の次数成分の商写像による像として定義する。 |
| `projectiveRingQuotientGradeGradedMonoid` | 商環の次数成分は、単位と積を保つ。 |
| `projectiveRingQuotientGradeGradedSMul` | 商環の次数成分は、元の多項式環の次数付き作用を保つ。 |
| `projectiveRingQuotientProjection_preservesPiece` | 実際の商写像は、元の次数成分を商の同じ次数成分へ送る。 |
| `projectiveRingQuotient_primeCast_eq_zero` | p の像が零であることは、零環を許す商環でも成り立つ。 |
| `projectiveRingQuotientCechFrobenius_naturality` | 実際の環の商への射影と、標準開の Čech Frobenius は可換。 |
| `reesClosedRing_submodule_eq` | Rees の閉厚化の部分加群は、A の拡大イデアルの係数制限。 |
| `reesClosedRingLinearEquiv` | Rees の商加群表示と、実際の環の閉厚化との R 線形同型。 |
| `reesClosedRingLinearEquiv_mk` | 環の商との比較は、同じ代表元を持つ剰余類を対応させる。 |
| `reesClosedRingPolynomialEquiv` | 環の商との比較を、多項式環上の線形同型へ昇格する。 |
| `reesClosedRingPolynomialEquiv_mk` | 多項式線形な比較も、同じ代表元を送る。 |
| `reesClosedRingPolynomialEquiv_mem_iff` | 比較は、商の Proj 次数成分を両方向で対応させる。 |
| `reesClosedRingChartIso` | Rees の閉厚化と実際の環の閉厚化の標準開図式の同型。 |
| `reesClosedRingCechIso` | Rees の閉厚化と実際の環の商の Čech H の同型。 |

原典の Hⁱ に対応する主張の docstring は「Čech 版」と明記し、Stacks 30.2.6 の比較は形式化しないと記した。最終出力と利用側の `AugmentedRingCechExact` の型は変更していない。

残り：`reesClosedRingChartIso`・`reesClosedRingCechIso` と、以前の閉厚化への射影・厚化間の遷移との可換性を、同じ実際の商写像で明示する。その後、閉厚化の Frobenius を互換族と形式関数の同型へ接続する。H 自身の I 進商の n→p*n の写像ができたことだけでは、閉厚化の H の間の指数を移す写像までできたとはしない。共通アフィン細分、filtered colimit の実際の比較も未完。**停止点 2e ではない。**

証拠：作業木の `scheme-drafts/` に、`frobenius-root-importer-build-3.log`、`rees-closed-ring-build.log`、`frobenius-closed-ring-audit.log`、`verified-frobenius-closed-ring.json` を保存した。


## 2026-11-12：実際の閉厚化の Frobenius と形式関数の可換性

数学コミット `8e896e65c`。3 モジュール（399 行）・21 件の数学宣言。対象と直接 importer のビルド成功（**4,342 jobs**）。別実行の標準監査は **7,343 宣言・標準三公理のみ**。新規を含め、既存の数学宣言は変更していない。上限の追加・sorry・admit・新しい公理はない。鍵は `--wait 3600`、一回ごとに返却した。

`72c7ff525` の環の商との比較を、既存の Rees の閉厚化への射影と厚化間の遷移に自然にした。多項式線形写像の代表元の計算、標準開図式、Čech H の順に可換性を示した。実際の環の閉厚化の Frobenius を、この構成済みの同型で既存の Rees の Čech H へ戻し、以前からの射影と I 進遷移に可換であることを証明した。

これを実際の閉厚化の互換族へ送り、既存の `adicProjectionCompletionMap_semilinear_naturality_apply` を使って、完備化から互換族への canonical な比較が Frobenius と可換と示した。射影の場合の形式関数の同型の順写像はその比較そのものなので、同型自体の Frobenius の可換性を得た。Noether 性と多項式環上の有限生成性は、形式関数の同型の箇所にだけ仮定する。導来関手の Hⁱ との比較や、H/IⁿH と閉厚化の H の同一視は行わない。

登録：`ReesClosedRingNaturality`、`ReesClosedCechFrobenius`、`ReesClosedCechFrobeniusCompletion`。

| 宣言 | 主張 |
|---|---|
| `reesClosedRingPolynomialEquiv_projection` | Rees と環の商の比較は、既存の射影を実際の環の射影へ送る。 |
| `reesClosedRingTransition` | 実際の環の閉厚化の間の、指数を下げる商射。 |
| `reesClosedRingTransition_mk` | 環の閉厚化の遷移は、同じ代表元を送る。 |
| `reesClosedRingPolynomialEquiv_transition` | Rees と環の商の比較は、以前の厚化間の遷移と可換。 |
| `reesClosedRingTransition_preservesPiece` | 環の閉厚化の遷移は、商の Proj 次数を保つ。 |
| `reesClosedRingProjectionChartMap` | 環の閉厚化への射影が誘導する標準開図式の射。 |
| `reesClosedRingTransitionChartMap` | 環の閉厚化の遷移が誘導する標準開図式の射。 |
| `reesClosedRingChartIso_projection` | 標準開の具体的な比較は、既存の閉厚化への射影と可換。 |
| `reesClosedRingChartIso_transition` | 標準開の比較は、以前の厚化間の遷移と可換。 |
| `reesClosedRingCechIso_projection` | 環の商の Čech H の比較は、以前からの閉厚化への射影と可換。 |
| `reesClosedRingCechIso_transition` | 環の商の Čech H の比較は、既存の I 進遷移と可換。 |
| `reesAdicProjectiveClosedCechFrobenius` | 実際の商環の Frobenius を、構成済みの同型で Rees 表示の閉厚化の Čech H へ戻す。 |
| `reesAdicProjectiveClosedCechFrobenius_compare` | Rees 表示へ戻した Frobenius は、環の商の表示の Frobenius そのもの。 |
| `reesAdicProjectiveClosedCechFrobenius_projection` | 実際の閉厚化の Čech Frobenius は、以前からの閉厚化への射影と可換。 |
| `reesAdicProjectiveClosedCechFrobenius_transition` | 実際の閉厚化の Čech Frobenius は、既存の I 進遷移と可換。 |
| `reesAdicProjectiveClosedCechFrobenius_linear_transition` | 遷移の可換性を、互換族への写像に使う半線形写像の合成の等式で述べる。 |
| `reesAdicProjectiveClosedCechFamiliesFrobenius` | 実際の閉厚化の Čech 互換族に誘導した Frobenius 半線形写像。 |
| `reesAdicProjectiveClosedCechFamiliesFrobenius_apply` | 互換族の Frobenius は、各厚化の実際の Čech Frobenius を適用する。 |
| `reesAdicProjectiveClosedCechFrobenius_linear_projection` | 射影の可換性を、半線形写像の合成の等式で述べる。 |
| `reesAdicProjectiveClosedCechCompletionMap_frobenius` | 完備化から実際の閉厚化の互換族への canonical な写像は、Frobenius と可換。 |
| `reesAdicProjectiveClosedCechCompletionLinearEquiv_frobenius` | 射影版の形式関数の同型は、実際の Čech Frobenius と可換。 |

上の原典の Hⁱ に関する主張は、名前と docstring で Čech 版と明記し、Stacks 30.2.6 の導来関手との比較は形式化しないとした。最終出力と利用側の `AugmentedRingCechExact` は変更していない。

§9 の残りは、共通アフィン細分、filtered colimit の実際の比較、およびそれらと既存の比較の可換性。閉厚化の n→p*n を移す写像の追加構成は、同じ n の閉厚化の Frobenius と区別して扱う（2f の冪による因子分解に必要）。**停止点 2e ではない。2f は未着手のまま。**

証拠は作業木の `scheme-drafts/rees-closed-frobenius-completion-importer-build.log` と `rees-closed-frobenius-completion-audit.log` に保存した。


## 2026-11-12：filtered colimit の Čech H の自然な比較と、実際の局所化・次数成分

数学コミット `df7c1d105`。8 モジュール（754 行）と入口 import 8 行、43 件の数学宣言（公開の instance を含み、local instance は除く）。対象と直接 importer のビルドは **4,352 jobs で成功**、別実行の標準監査は **7,466 宣言・標準三公理のみ**。共有鍵 `--wait 3600` を各実行の間だけ持ち、待ちは一つにまとめた。既存の数学宣言の型・本文・名前と計算量上限は変更していない。

固定した有限被覆の各 Čech 項について、各タプル成分の代表元と等式を一つの有限段へ送ることで、canonical な filtered colimit の比較が全単射であると示した。ここから全タプル Čech 複体が filtered colimit を保つことを導いた。各次数の H との交換は、関手圏の短複体と加群圏の AB5 を使って別に構成した。正次数の H の同型を、B1 の増大完全性の同値だけから導いてはいない。複体と H の比較はともに係数図式の射に自然と示した。最終的な環の増大 Čech 完全性の `isCechExact_colimit` は B1 のものを使い、作り直していない。

実際の加群の局所化を、局所化環とのテンソル積と自然同型で比較し、小さい colimit を保つことを示した。この比較は同じ分子・分母の分数を保ち、図式の射に自然である。局所化が零になる場合も含む。さらに、filtered 図式の遷移で保たれる部分加群の colimit を、各段の像の有向上限と線形同定した。基底環 R と作用の環 P を分けて係数制限し、余極限の分子族の次数成分を構成した。一つの有限段の同じ次数の代表元を持つこと、各段の射が次数を保つこと、分母倍の条件が保たれることを示した。

原典 [Stacks 30.6.1 / 07TB](https://stacks.math.columbia.edu/tag/07TB) は準コンパクト・準分離な射に対する層の filtered colimit と高次順像を扱う。今回の H の比較は、その計算に使う **Čech 版**であり、導来関手との比較は作らない。該当する docstring に原典の番号と Stacks 30.2.6 の比較を形式化しないことを明記した。

登録モジュール：`ProjectiveCechFilteredCochains`、`ProjectiveFilteredHomology`、`ProjectiveCechFilteredComplex`、`ProjectiveFilteredHomologyNaturality`、`ProjectiveCechFilteredNaturality`、`ProjectiveLocalizedColimit`、`ProjectiveFilteredSubmodule`、`ProjectiveGradedColimit`。

| 宣言 | 主張 |
|---|---|
| `projectiveCechCochainsFunctor` | 全タプル Čech の固定した長さの項を、係数図式の関手にする。 |
| `projectiveCoefficientColimit_exists_rep` | 係数図式の余極限の各交叉の元は、一つの有限段の代表元を持つ。 |
| `projectiveCoefficientColimit_eq_iff` | 同じ段の係数の余極限での等式は、ある有限段での等式と同値。 |
| `projectiveCechColimitCochainsMap_ι` | canonical な余極限比較は、各有限段のタプル成分をそのまま送る。 |
| `projectiveCechColimitCochainsMap_surjective` | 有限被覆の Čech 各項の filtered colimit 比較は全射。 |
| `projectiveCechColimitCochainsMap_injective` | 有限被覆の Čech 各項の filtered colimit 比較は単射。 |
| `projectiveCechCochainsFunctorPreservesFilteredColimits` | 有限被覆の全タプル Čech の各項は filtered colimit を保つ。 |
| `projectiveFilteredShortComplexDiagram` | 短複体の図式を、関手圏の一つの短複体にまとめる。 |
| `projectiveFilteredShortComplexHomologyDiagramIso` | 関手圏の短複体の H を、各有限段の H の図式と同定する。 |
| `projectiveFilteredShortComplexHomologyIso` | 短複体の filtered colimit の H は、各段の H の colimit。 |
| `projectiveFilteredComplexShortComplexIso` | 複体の colimit の短複体を、各項の colimit の短複体と比較する。 |
| `projectiveFilteredComplexHomologyIso` | 複体の filtered colimit と各次数の H を比較する。 |
| `projectiveFullCechFunctorPreservesFilteredColimits` | 有限被覆の全タプル Čech 複体は filtered colimit を保つ。 |
| `projectiveCechFilteredComplexIso` | 有限被覆の Čech 複体と係数図式の filtered colimit の canonical な比較。 |
| `projectiveCechFilteredHomologyIso` | 有限被覆の Čech H は、係数図式の filtered colimit と交換する。 |
| `projectiveFilteredShortComplexHomologyDiagramIso_naturality` | 関手圏と各段の短複体の H の比較は、図式の射に自然。 |
| `projectiveFilteredShortComplexHomologyIso_naturality` | 短複体の filtered colimit の H の比較は、図式の射に自然。 |
| `projectiveFilteredComplexShortComplexIso_naturality` | 複体の短複体と各項の colimit の比較は、図式の射に自然。 |
| `projectiveFilteredComplexShortComplexIso_inv_naturality` | 短複体の比較の逆向きも、図式の射に自然。 |
| `projectiveFilteredComplexHomologyIso_naturality` | 複体の filtered colimit と各次数の H の比較は、図式の射に自然。 |
| `projectiveCechFilteredComplexIso_naturality` | Čech 複体と filtered colimit の比較は、係数図式の射に自然。 |
| `projectiveCechFilteredHomologyIso_naturality` | Čech H の filtered colimit 比較は、係数図式の射に自然。 |
| `projectiveLocalizedModuleFunctor` | 実際の分数の局所化を、元の環上の加群の関手にする。 |
| `projectiveLocalizedModuleTensorNatIso` | 実際の局所化と、局所化環とのテンソル積を自然に比較する。 |
| `projectiveLocalizedModuleFunctorPreservesColimits` | 固定した共通の環での実際の局所化は、小さい colimit を保つ。 |
| `projectiveLocalizedColimitIso` | 実際の局所化と colimit の canonical な比較。 |
| `projectiveLocalizedColimitIso_fraction` | 局所化の比較は、有限段の分数の同じ分子・分母を保つ。 |
| `projectiveLocalizedColimitIso_naturality` | 実際の局所化と colimit の比較は、加群図式の射に自然。 |
| `projectiveFilteredSubmodule` | 余極限内の指定部分を、各段の部分加群の像の上限と定義する。 |
| `projectiveFilteredSubmodule_directed` | 遷移で保たれる部分加群の像は、有向族をなす。 |
| `mem_projectiveFilteredSubmodule_iff` | 余極限の指定部分の元は、一つの段の指定部分の代表元を持つ。 |
| `projectiveFilteredSubmoduleDiagram` | 各段の指定部分加群自身を、加群の filtered 図式とする。 |
| `projectiveFilteredSubmoduleInclusion` | 各段の指定部分の包含を、図式の包含とする。 |
| `projectiveFilteredSubmoduleInclusionMono` | 指定部分加群の図式の包含は mono。 |
| `projectiveFilteredSubmoduleColimit_injective` | 部分加群の filtered colimit からの包含は単射。 |
| `projectiveFilteredSubmoduleColimit_range` | 部分加群の colimit の像は、有限段の像の有向上限そのもの。 |
| `projectiveFilteredSubmoduleColimitEquiv` | 部分加群の colimit を、余極限内の具体的な指定部分と線形同定する。 |
| `projectiveFilteredSubmoduleColimitEquiv_val` | 指定部分の比較は、余極限内の同じ元を送る。 |
| `projectiveGradedColimitGrade` | P 上の加群図式の余極限に、共通基底 R 上の分子族の像から次数成分を作る。 |
| `projectiveGradedColimitBaseInclusion` | 各有限段からの P 線形な射を、共通基底 R 上の線形射として扱う。 |
| `mem_projectiveGradedColimitGrade_iff` | 余極限の次数成分の元は、一段の同じ次数の元で表される。 |
| `projectiveGradedColimitInclusion_preservesPiece` | 各段からの canonical な射は、同じ Proj 次数の成分を保つ。 |
| `projectiveGradedColimitGrade_step` | 有限段の分母倍の条件は、余極限の次数成分でも保たれる。 |

**残り。** 固定係数の任意の係数図式の Čech H の比較はできたが、これだけで動く基底の実際の標準開との比較が完了したとはしない。次は、構成した余極限の次数成分を分子族とする `projectiveGradedAway` と、各段の斉次局所化の colimit を比較する。全射性は分子の有限段への持ち上げ、単射性は分母倍での零化と有限段の等式判定による。その同型を実際の標準開の制限と加群の射に自然にし、Čech H の比較と合成する。負の次数の零延長、動く基底の実際の係数変更図式、既存の閉厚化・Frobenius との整合性もそこで確認する。

共通アフィン細分も未完。完備化と filtered colimit の交換、無限積との交換は主張していない。最終出力と利用側の `AugmentedRingCechExact` の型は変更していない。**停止点 2e ではない。**

証拠は作業木の `scheme-drafts/cech-filtered-importer-build.log`、`projective-graded-colimit-build-2.log`、`cech-filtered-audit.log` に保存した。次の斉次局所化の接続手順は `scheme-drafts/graded-away-colimit-route.md` にも記録した。


## 2026-11-12 夜：新しい上限規則に基づく途中の規模報告

規則は main `f5baa8763` の `coordination.md` §2 と `scheme-w1.md` の夜の追記で確認した。2e の段 0 の見込みは 2d 停止点報告 §3 の **8,000–25,000 行**。停止基準は上端の 2 倍の **50,000 行**。見込みの半分の報告点は、上端の半分 **12,500 行**として早めに報告する。

検証済みの計測点は `0e0f9fc07`（数学 `df7c1d105`）。2d 停止点の報告 `df035c08e` から増えた `AlgebraicGeometry/` の新規 Lean は **205 本・22,140 行**。既存の数学ファイルの差分はなく、入口 `AlgebraicGeometry.lean` の登録追加 **206 行**を含めると **22,346 行**。空行・コメントを含むソース行数で数え、文書・`scheme-drafts/`・ビルド成果物は含めない。main の取り込みで増えた他レーンの `CommutativeAlgebra/` 33 本・3,616 行は 2e の実測に混ぜない。半分の報告点は既に越えているので、この時点で報告して作業を継続する。

| 残る作業 | 現時点の追加行数の見込み |
|---|---:|
| 斉次局所化の colimit、実際の標準開・動く基底への接続 | 約 2,000–5,000 |
| 共通アフィン細分と、各 H の比較・自然性 | 約 5,000–11,000 |
| 五つの比較同士の整合性と停止点報告の仕上げ | 約 1,000–3,000 |
| 合計 | **約 8,000–19,000** |

従って合計は現時点で約 **30,000–42,000 行**の見込みであり、新しい停止基準を超える見込みにはまだ至っていない。主な不確かさは、共通アフィン細分の正次数の H の比較（アフィン交叉上の完全性と二重複体の edge map / cone）の接続である。検証済みの前段の API だけでその比較が済んだとは数えない。残りの見込みが変わり、50,000 行を超えそうになった場合は、その時点の検証済みをコミットして報告し、止める。

計測は `git diff --name-only --diff-filter=A df035c08e 0e0f9fc07 -- SerrePositivity/AlgebraicGeometry` の Lean ファイルの各 `git show` の行数を合計した。パス・行数・ハッシュは作業木の `scheme-drafts/size-2e-1112.json` に保存した。最後の検証は対象と直接 importer 4,352 jobs、監査 7,466 宣言・標準三公理のみ。**停止点 2e ではない。**


## 追記：一括移動の凍結に向けた途中の取り込み（11-12 午後）

調整役の連絡により、一括レーンの凍結の一晩は停止点 2e を待たずに行う（早くて翌日の夜。具体的な日程はまだ未指定）。指定された日の夕方までに検証済みを枝へコミットして報告し、途中の取り込み点として main に渡す。その夜はコミットを控え、翌朝に改名表で追従する。未検証の Lean は作業木に残し、途中の取り込みの対象に混ぜない。2e の停止点の基準と残りの数学は変更しない。


### 共通細分のアフィン側：局所化による完全性の実装候補（紙の調査、未検証）

[Stacks 30.2.1](https://stacks.math.columbia.edu/tag/01X8) の標準被覆の議論を、導来関手の H との比較を経ずに使う。有限標準被覆を与える元の集合 s が単位イデアルを生成するとき、各 f∈s で局所化すれば一つの被覆元が単元になる。そこでその頂点をタプルの先頭へ挿入し、制限写像の逆を使って増大 Čech 複体を縮約する。Mathlib の `exact_of_localized_span`（`RingTheory/LocalProperties/Exactness.lean`）は各局所化での完全性から元の加群の完全性を戻す入口であり、同ファイルの `injective_of_localized_span` が増大項を扱う。有限積と局所化の比較は各次数で有限個のタプルについて行う。無限積と局所化の交換は使わない。

まず任意の係数図式 D で、固定頂点 v の挿入 T→T∪{v} による制限がすべて同型なら、全タプルの先頭挿入が縮約を与えるという加群の補題を切り出す。その後に実際の局所化図式へ特殊化する。単項式の縮約 `projectiveMonomialContraction_identity` の符号計算を参照できるが、一般の係数図式では制限写像とその逆の可換性を追加で示す必要がある。既存の単項式の補題がそのまま任意の係数図式に適用できるとはしない。

これは交叉上の完全性の入口であって、二つの被覆の各正次数の H の比較を閉じるものではない。共通細分の二重図式、全複体への比較の quasi-isomorphism、係数の射への自然性は別に構成する。B1 の増大完全性の同値をこの H の同型と置き換えない。ここに記したものは紙の調査で、検証済みの宣言数には含めない。


既存の `CechTupleContraction.lean` の `cechTupleBoundary_prepend` は整数タプル鎖の先頭追加の恒等式を既に供給している。したがって符号相殺をもう一度証明する必要はない。`ProjectiveCechComparison.lean` の `fullCechTranspose_comp` は台を広げない写像用なので、そのまま先頭追加に適用せず、T の代わりに T∪{v} 上で評価する転置を追加する。通常の境界との二つの合成則を示せば、既存の鎖の恒等式を係数付きの先頭挿入の恒等式へ移せる。`scheme-drafts/ProjectiveCechInsertTranspose.lean` と `ProjectiveCechSplitVertex.lean` はこの準備の下書きであり、本体・入口・検証済みの数には未登録。


## 斉次局所化から実際の標準開の filtered 比較へ（11-12、650650c96）

数学コミット **`650650c96`**。新規 8 モジュール、数学宣言 **30 件**、本体 **738 行**と入口 8 行、計 **746 行**。対象と直接 importer `SerrePositivity.AlgebraicGeometry` は **4,360 jobs で成功**。別実行の標準監査は **7,579 宣言・標準三公理のみ**。いずれも共有の `with_build_lock.sh --wait 3600` を通し、監査の鍵はビルド終了後に取り直した。未検証の下書きは含めていない。

登録したモジュール：

- `ProjectiveGradedAwayColimit`
- `ProjectiveGradedAwayColimitValues`
- `ProjectiveGradedColimitGrading`
- `ProjectiveGradedColimitNaturality`
- `ProjectiveNatChartColimit`
- `ProjectiveNatChartColimitComponent`
- `ProjectiveNatChartColimitIso`
- `ProjectiveNatChartColimitNaturality`

| 宣言 | 主張 |
|---|---|
| `projectiveGradedAwayColimitDiagram` | 各有限段の指定次数の斉次局所化を filtered 図式にする。 |
| `projectiveGradedAwayColimitCocone` | 有限段から、余極限の分子族の斉次局所化への余錐。 |
| `projectiveGradedAwayColimitMap` | 斉次局所化の colimit から余極限の斉次局所化への比較射。 |
| `projectiveGradedAwayColimitMap_ι` | 比較射は各有限段の実際の局所化写像を保つ。 |
| `projectiveGradedAwayColimitMap_surjective` | 分子の有限段の代表元により比較射は全射。 |
| `projectiveGradedAwayColimitMap_injective` | 分母倍での零化を有限段へ降ろして比較射の単射性を示す。 |
| `projectiveGradedAwayColimitEquiv` | 斉次局所化と filtered colimit の比較の線形同型。 |
| `projectiveGradedAwayColimitEquiv_ι` | 同型は各有限段からの局所化の写像を保つ。 |
| `projectiveGradedAwayColimitEquiv_ι_value` | 同型を周囲の局所化の写像の値で計算する。 |
| `projectiveGradedColimitGrade_bot` | 各有限段の零部分から作った余極限の次数成分は零。 |
| `projectiveGradedColimitGrade_int` | 余極限の次数成分と整数への零延長が交換する。 |
| `projectiveGradedColimitGradeGradedSMul` | 有限段の次数付き作用を余極限の次数成分へ移す。 |
| `projectiveGradedColimitMap_preservesPiece` | 次数を保つ図式の射の colimit は、余極限でも同じ次数を保つ。 |
| `projectiveNatChartColimitDiagram` | 実際の射影標準開の係数図式を各有限段について並べる。 |
| `projectiveNatChartColimitCocone` | 有限段から余極限の次数付き加群の標準開への余錐。 |
| `projectiveNatChartColimitMap` | 標準開の制限写像を含む図式全体の canonical な余極限比較。 |
| `projectiveNatChartColimitNumerator` | 標準開の分子族の余極限と、余極限の次数成分から作る分子族の一致。 |
| `projectiveNatChartColimitNumerator_map` | 有限段の次数を保つ射は、各標準開の分子族も保つ。 |
| `projectiveNatChartColimitNumerator_step` | 標準開の分子族は、その分母倍で次の項へ移る。 |
| `projectiveNatChartColimitComponentDiagramIso` | 各有限交叉の成分図式と固定した分母の斉次局所化の図式を同定する。 |
| `projectiveNatChartColimitComponentEquiv` | 標準開の各有限交叉で余極限比較を線形同型にする。 |
| `projectiveNatChartColimitComponentDiagramIso_ι` | 成分図式の同定は各有限段からの射を保つ。 |
| `projectiveNatChartColimitComponentEquiv_ι_val` | 成分同型と実際の余錐の写像は同じ局所化分数を与える。 |
| `projectiveNatChartColimitMap_app_isIso` | canonical な標準開比較射は各有限交叉で同型。 |
| `projectiveNatChartColimitIso` | 標準開間の制限写像を含め、図式全体の比較を同型にする。 |
| `projectiveNatCechFilteredHomologyIso` | 実際の標準開の Čech H と有限段の Čech H の filtered colimit との同型。 |
| `projectiveNatChartColimitDiagramMap` | 次数を保つ図式の射を、有限段の標準開の図式の射へ移す。 |
| `projectiveNatChartColimitTargetMap` | 図式の射の colimit から、余極限の実際の標準開の射を作る。 |
| `projectiveNatChartColimitMap_naturality` | canonical な標準開の比較射は、次数を保つ図式の射に自然。 |
| `projectiveNatCechFilteredHomologyIso_naturality` | 実際の標準開の Čech H の余極限比較は、次数を保つ図式の射に自然。 |


分母倍での零化を有限段へ降ろすため、分母の非零因子性や基底環の非自明性は仮定しない。負の次数の零延長、空の有限集合の標準開、指定次数の分子族も同じ比較で扱う。成分図式の一致を kernel に大きく展開させる箇所は、明示的な自然同型とその有限段の公式に切り出した。計算量上限は増やしていない。既存の数学宣言の本文・型は変更せず、新しい 8 ファイルと入口登録だけを追加した。`sorry`・`admit`・新しい公理はない。

Čech H の二つの新しい入口は、原典 Stacks 30.6.1 の Hⁱ に対応する **Čech 版**と docstring に明記し、分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、この比較は形式化しないと記した。最終出力と利用側の `SerrePositivity.Cech.AugmentedRingCechExact` の型は変更していない。

**停止点 2e ではない。** 今回の入力は共通の R と多項式環 R[X] 上の filtered な次数付き加群の図式で、出力は余極限の実際の次数成分から作る標準開の図式である。係数環 B_j が動く各段の B_j[X] 上の標準開と、共通係数へ制限したこの図式との照合はまだ別に閉じる必要がある。`projectiveNatCoefficientChartIso` などの既存の係数変更比較、および Frobenius・閉厚化・底変換との可換性を、同じ有限段の写像で接続する。共通アフィン細分の各 H の比較と自然性も未完。今回の標準開の比較だけで、被覆によらないことまで示したとはしない。完備化や無限積と filtered colimit の交換も主張しない。

段 2e の実測は基点 `df035c08e` から新規 **213 本・22,878 行**、入口登録を含め **23,092 行**。他レーンの追加・文書・下書きを含めない。前回の半分の報告点を越えた実測報告は継続して有効で、新しい停止基準 50,000 行には達していない。残りの主な幅は引き続き共通アフィン細分にある。


### 共通アフィン細分：mapping cone と B1 による接続案（再開後の紙の作業）

正次数の H の比較の橋として、一般の全複体の edge map の理論を先に作る代わりに、refinement map の cone に B1 の `exact_zero_row_iff_zero_col_of_commute` を適用する案を使う。以下は紙の筋で、Lean で検証済みの結論ではない。

有限アフィン被覆 V が U を細分し、添字写像 ρ により V_j⊂U_{ρ(j)} とする。非増大の Čech 複体の射 r:C(U)→C(V) に対し、負の一項を自然数の第零項へ移した cone を E⁰=C⁰(U)、E^{p+1}=Cᵖ(V)⊕C^{p+1}(U) と置く。微分は第零項で a↦(r(a),−d(a))、以後 (b,a)↦(d(b)+r(a),−d(a))。この cone の完全性と r の各 H の同型性を、サイクル・境界の前像で結ぶ補題を切り出す。導来関手の層コホモロジーとの比較は使わない。

V のタプルとの交叉で上の cone を作れば、縦方向を V の増大 Čech にした二重図式になる。正の縦次数では、交叉全体が V のそのタプルの先頭の開に入り、また U_{ρ(j)} にも入る。両方の横の増大 Čech が固定頂点の先頭挿入で縮約する。共通の増大項の射が恒等なので、そこから非増大の射の cone の完全性を加群の計算で得る。縦の各列は、U のアフィン交叉を V で被覆した増大 Čech、またはその有限直和。従ってその完全性を供給すれば、B1 によって縦次数零の cone の完全性が従う。この段で初めて各 H の同型を結論する。単なる増大完全性の同値を各 H の同型と読み替えない。

アフィンの任意の有限アフィン被覆の完全性は、先に標準被覆の場合を局所化と先頭挿入で証明し、有限標準細分 W を選んで B1 の完全性の比較を使う。V|W の各交叉では、W が入る V の開が一つあるので縮約する。他方向では、アフィン V の交叉へ U の大域関数の標準被覆を制限した形なので、標準被覆の完全性を使う。この順なら、任意のアフィン被覆の完全性を共通細分の H の同型から循環的に導かない。

細分の添字写像によるコチェインの射、合成との整合性、係数の射への自然性、二つの添字写像が与える射のホモトピーも別に供給する。被覆によらない比較を閉じるまで、存在する一つの細分についての同型だけを停止点の条件としない。


## 固定頂点の縮約・アフィン標準被覆の単元の場合・refinement cone（eac527fbd）

数学コミット **`eac527fbd`**。新規 **7 モジュール・40 宣言**、本体 **711 行**と入口 7 行、計 **718 行**。対象と直接 importer は **4,367 jobs で成功**。別実行の標準監査は **7,650 宣言・標準三公理のみ**。共有の `with_build_lock.sh --wait 3600` でビルドと監査を一回ずつ別に実行した。未検証の `CechHomologyCycleCriterion.lean` はこのコミットと監査数には含めない。

- `ProjectiveCechSplitVertex`・`ProjectiveCechSplitExact`：固定頂点を挿入する制限がすべて同型である係数図式では、増大項の写像が単射で、各正長のサイクルは境界。符号計算は既存の `cechTupleBoundary_prepend` を、台を一頂点まで広げる転置で移して再利用した。
- `AffineModuleCechDiagram`・`AffineModuleCechMap`・`AffineModuleCechUnit`：実際の局所化加群の各有限交叉と制限を図式にし、係数の射の恒等・合成を保つ。被覆元の一つが単元なら、上の縮約から増大 Čech の完全性を得る。単位イデアルを生成する一般の場合の完全性とは区別する。
- `CechRefinementCone`・`CechRefinementConeExactness`：非負次数の射の cone を負一の項から自然数で添字付けし、同じ増大項を保つ二つの完全な列の射では、その cone の第零項の核が零で各正次数のサイクルが境界になる。これは二重図式の正次数の行に用いる加群の計算である。

| モジュール | 宣言 | 主張 |
|---|---|---|
| `ProjectiveCechSplitVertex` | `cechInsertVertexFunctor` | 有限集合に固定した頂点を挿入する関手。 |
| `ProjectiveCechSplitVertex` | `fullCechInsertVertexMap` | 係数図式の制限による、頂点挿入の自然変換。 |
| `ProjectiveCechSplitVertex` | `fullCechInsertVertexIso` | 各交叉で頂点挿入の制限が可逆なら、係数図式の自然同型になる。 |
| `ProjectiveCechSplitVertex` | `fullCechPrependVertex` | タプルの先頭への挿入による、挿入後の係数での評価。 |
| `ProjectiveCechSplitVertex` | `fullCechPrependVertex_naturality` | 先頭挿入の評価は、係数図式の射に自然。 |
| `ProjectiveCechSplitVertex` | `fullCechSplitVertexContraction` | 挿入の制限の逆で係数を戻した、縮約の候補。 |
| `ProjectiveCechSplitVertex` | `fullCechInsertTranspose` | 頂点挿入まで台を広げる鎖写像の転置。 |
| `ProjectiveCechSplitVertex` | `fullCechInsertTranspose_comp_preserving_left` | 挿入まで広げる写像の前に、台を保つ写像を合成する場合の転置。 |
| `ProjectiveCechSplitVertex` | `fullCechInsertTranspose_comp_preserving_right` | 台を保つ写像の前に、挿入まで広げる写像を合成する場合の転置。 |
| `ProjectiveCechSplitVertex` | `fullCechInsertTranspose_add` | 挿入を許す転置は鎖写像の和を保つ。 |
| `ProjectiveCechSplitVertex` | `fullCechInsertTranspose_id` | 恒等写像の挿入を許す転置は、挿入による係数の制限。 |
| `ProjectiveCechSplitVertex` | `cechTuplePrepend_support_insert` | 先頭追加の像の台は、元の台にその頂点を追加した集合に収まる。 |
| `ProjectiveCechSplitVertex` | `fullCechInsertTranspose_prepend` | 先頭追加を転置したものは、係数図式への先頭挿入の評価。 |
| `ProjectiveCechSplitVertex` | `fullCechPrependVertex_identity` | 係数図式付きの先頭挿入と余境界の反交換式。同型性の仮定は不要。 |
| `ProjectiveCechSplitVertex` | `fullCechSplitVertexContraction_identity` | 挿入の制限が同型なら、係数図式の全タプル Čech コチェインは縮約する。 |
| `ProjectiveCechSplitExact` | `cechTupleBoundary_prepend_zero` | 長さ零のタプルでは、先頭を追加して境界を取ると元に戻る。 |
| `ProjectiveCechSplitExact` | `fullCechPrependVertex_zero_differential` | 長さ零の先頭挿入と余境界の合成は、頂点挿入による係数の制限。 |
| `ProjectiveCechSplitExact` | `fullCechAugmentedDifferential_squared` | 全タプルの余境界の二乗は、長さ零の増大項からも零となる。 |
| `ProjectiveCechSplitExact` | `fullCechSplitVertexContraction_zero_identity` | 増大項での縮約も、余境界との合成が恒等になる。 |
| `ProjectiveCechSplitExact` | `fullCechSplitVertexDifferential_zero_injective` | 固定頂点による縮約があれば、増大項からの余境界は単射。 |
| `ProjectiveCechSplitExact` | `fullCechSplitVertex_cycle_boundary` | 固定頂点による縮約があれば、正の長さの各 Čech サイクルは境界。 |
| `AffineModuleCechDiagram` | `affineModuleAwayRestrictionIso` | 二つの分母が互いに整除するときの局所化加群の同型。 |
| `AffineModuleCechDiagram` | `affineCechDenominator` | 有限交叉を定める被覆元の積。 |
| `AffineModuleCechDiagram` | `affineCechDenominator_dvd` | 添字を増やすと、交叉の分母は元の分母の倍数になる。 |
| `AffineModuleCechDiagram` | `affineModuleCechDiagram` | アフィン標準被覆の各有限交叉での局所化加群の図式。 |
| `AffineModuleCechDiagram` | `affineCechDenominator_insert_dvd` | 単元の被覆元を追加しても、交叉の分母は元の分母を割る。 |
| `AffineModuleCechDiagram` | `affineModuleCechDiagram_map_insert_isIso` | 被覆元が単元なら、それを交叉へ追加する制限は同型。 |
| `CechRefinementCone` | `cechRefinementConeTerm` | 自然数で添字付けした cone の項。 |
| `CechRefinementCone` | `cechRefinementConeDifferential` | 負一から移した cone の微分。 |
| `CechRefinementCone` | `cechRefinementConeDifferential_squared` | この添字付けでも cone の微分の二乗は零。 |
| `CechRefinementCone` | `cechRefinementCone` | 共通アフィン細分の射の完全性を測る、自然数添字の cone。 |
| `CechRefinementConeExactness` | `cechRefinementCone_zero_kernel` | 増大項で恒等を誘導する射の cone は、第零項で核が零。 |
| `CechRefinementConeExactness` | `cechRefinementCone_cycle_boundary` | cone の正次数の各サイクルは境界。増大項を保つ二つの完全な列を用いる。 |
| `AffineModuleCechMap` | `affineModuleCechMap` | 加群写像が誘導する、各有限交叉の局所化加群の図式の射。 |
| `AffineModuleCechMap` | `affineModuleCechMap_id` | 局所化した係数写像は恒等写像を保つ。 |
| `AffineModuleCechMap` | `affineModuleCechMap_comp` | 局所化した係数写像は合成を保つ。 |
| `AffineModuleCechUnit` | `affineModuleCechUnitInsertionIsIso` | 単元の頂点の挿入は、係数図式のすべての成分で同型。 |
| `AffineModuleCechUnit` | `affineModuleCechUnit_zero_injective` | 単元の被覆元があれば、増大項からの写像は単射。 |
| `AffineModuleCechUnit` | `affineModuleCechUnit_cycle_boundary` | 単元の被覆元があれば、増大 Čech の各サイクルは境界。 |
| `AffineModuleCechUnit` | `affineModuleCechUnit_exact` | 単元の被覆元があれば、増大 Čech の連続する二つの余境界は完全。 |


既存の数学宣言の型・本文は変更していない。新しい sorry・admit・公理・計算量上限はない。最終出力と利用側の `SerrePositivity.Cech.AugmentedRingCechExact` の型も変更していない。段 2e の実測は基点 `df035c08e` から **220 本・23,589 行**、入口登録を含め **23,810 行**。50,000 行の停止基準には達していない。

**停止点 2e ではない。** 単位イデアルを生成する一般のアフィン標準被覆は、局所化と有限積の比較を供給してから今回の単元の場合へ渡す必要がある。任意のアフィン被覆の完全性、共通細分の二重図式の実装、cone の完全性から実際の H の同型へ渡す判定と自然性、細分の選択との整合性が残る。動く係数環の標準開と共通係数の図式の照合、および既存の五つの比較同士の可換性も未完。今回の cone の補題の前提を仮定しただけで、一般の共通細分が完成したとはしない。


## アフィン標準 Čech の完全性・細分の自然性と選択の独立性（ecd5061a5）

数学コミット **`ecd5061a5`**。新規 **27 モジュール・141 宣言**、本体 **2,387 行**、入口 **27 登録と区切り空行 1 行**、git 差分 **2,415 行**。対象と直接 importer のビルドは **4,452 jobs で成功**。別実行の公理監査は **7,890 宣言・標準三公理のみ**。どちらも共有の `with_build_lock.sh --wait 3600` を使い、一つの待ちを終えてから次の鍵を取った。検証時とコミット時の全 27 ソースおよび入口のハッシュが一致することを確認した。

- 単位イデアルを生成する一般のアフィン標準被覆の増大 Čech の完全性を、被覆元での局所化、有限積との交換、固定頂点の縮約から示した。Mathlib の準連接層の局所化 API を使い、Spec の実際の標準開上の切断へ渡した。
- 開被覆の有限交叉、細分の実際のコチェイン写像、係数の射への自然性、恒等と合成、二つの添字の選択が同じ Čech H の射を与えることを示した。最後は整数鎖の比較ホモトピーとその台の包含を、切断の制限で評価した。
- アフィン被覆を有限標準開で細分する存在、アフィン対角の下での実際の共通アフィン被覆、非空有限交叉のアフィン性を供給した。有限標準細分の添字は `Fin n` とし、座標環の宇宙から添字の制約が生じない形にした。
- 加法的係数比較に沿う完全性の輸送を追加した。大域の係数環と、アフィン座標の係数環の線形構造を同一視しない。
- cone が完全なら各 H の射が同型となる判定と、二重図式の行の cone に B1 を適用する接続を示した。**これらの完全性の前提をまだ全て実際のアフィン交叉へ供給していない。** `OpenCoverCechResolution` は実際の二重 Čech 構成の入口だが、任意のアフィン被覆の完全性や一般の細分の H の同型が完成したとは数えない。

| モジュール | 宣言 | 主張 |
|---|---|---|
| `AffineLocalizingCech` | `cechAwayFactorUnits` | 局所化先では、分母を割る元の冪も可逆に作用する。 |
| `AffineLocalizingCech` | `cechSpecRestriction` | Spec の大域切断から標準開への制限。 |
| `AffineLocalizingCech` | `cechBasicOpen_le_of_dvd` | 分母の整除に沿う標準開の包含。 |
| `AffineLocalizingCech` | `specStandardCechDiagram` | 標準開の交叉上の切断を、積の標準開で表示する係数図式。 |
| `AffineLocalizingCech` | `specStandardCechSectionIso` | 標準開の切断と大域切断の局所化の同型。 |
| `AffineLocalizingCech` | `specStandardCechSectionIso_naturality` | 標準開の切断と局所化の比較は、交叉を狭める制限に自然。 |
| `AffineLocalizingCech` | `specStandardCechDiagramIso` | 局所化を与える前層の、標準開係数図式との自然同型。 |
| `AffineLocalizingCech` | `specStandardCech_zero_injective` | 局所化を与える前層の標準開被覆では、増大項からの写像は単射。 |
| `AffineLocalizingCech` | `specStandardCech_exact` | 局所化を与える前層の標準開被覆の増大 Čech 完全性。 |
| `AffineLocalizingCech` | `cechBasicOpen_denominator` | 分母の積の標準開は、各分母の標準開の有限交叉。 |
| `AffineLocalizingCech` | `specStandardCechOpenDiagramIso` | 積の標準開による図式と、実際の有限交叉による図式の自然同型。 |
| `AffineLocalizingCech` | `specStandardOpenCech_exact` | Spec の標準開被覆上の実際の切断の増大 Čech の完全性。 |
| `AffineModuleLocalizedCech` | `affineModuleLocalizedCechInsertionIsIso` | 被覆元で局所化すれば、その頂点を交叉へ挿入する制限はすべて同型。 |
| `AffineModuleLocalizedCech` | `affineModuleCech_localized_zero_injective` | 各被覆元で局所化すると、増大項からの写像は単射。 |
| `AffineModuleLocalizedCech` | `affineModuleCech_localized_exact` | 各被覆元で局所化した、連続する Čech の余境界は完全。 |
| `AffineModuleLocalizedCech` | `affineModuleCech_zero_injective` | 単位イデアルを生成する元の標準被覆では、増大項の写像は単射。 |
| `AffineModuleLocalizedCech` | `affineModuleCech_exact` | 標準アフィン被覆の増大 Čech の完全性。 |
| `AffineQuasicoherentStandardCech` | `specQuasicoherent_isLocalizing` | 準連接層の標準開への制限は、その元での局所化。 |
| `AffineQuasicoherentStandardCech` | `specQuasicoherentStandardOpenCech_zero_injective` | 準連接層の標準開被覆の増大項の単射性。 |
| `AffineQuasicoherentStandardCech` | `specQuasicoherentStandardOpenCech_exact` | Spec 上の準連接層の標準開被覆の増大 Čech 完全性。 |
| `CechAdditiveCoefficientComparison` | `fullCechAdditiveCoefficientEquiv` | 各交叉の加法的な比較による Čech 項の加法群の同型。 |
| `CechAdditiveCoefficientComparison` | `fullCechAdditiveCoefficientEquiv_differential` | 係数の制限と可換な加法的比較は、Čech 微分と可換。 |
| `CechAdditiveCoefficientComparison` | `fullCechAdditiveCoefficientEquiv_zero_injective` | 加法的係数比較によって、増大項の単射性を移す。 |
| `CechAdditiveCoefficientComparison` | `fullCechAdditiveCoefficientEquiv_exact` | 加法的係数比較によって、増大 Čech の完全性を移す。 |
| `CechCoefficientExactness` | `fullCechCoefficientEquiv` | 係数の自然同型による、増大項を含む各 Čech 項の同型。 |
| `CechCoefficientExactness` | `fullCechCoefficientEquiv_toLinearMap` | 各項の同型は係数写像で与えられる。 |
| `CechCoefficientExactness` | `fullCechCoefficientEquiv_differential` | 係数の自然同型は微分と可換。 |
| `CechCoefficientExactness` | `fullCechCoefficientEquiv_zero_injective` | 自然同型に沿って増大項の微分の単射性を移す。 |
| `CechCoefficientExactness` | `fullCechCoefficientEquiv_exact` | 自然同型に沿って増大 Čech の完全性を移す。 |
| `CechHomologyCycleCriterion` | `cechCyclesOf` | 元で与えたサイクルを、短複体の抽象的な cycles の元にする。 |
| `CechHomologyCycleCriterion` | `cechCyclesOf_value` | 元で与えたサイクルの値は、元の元に戻る。 |
| `CechHomologyCycleCriterion` | `cechCyclesValue_isCycle` | cycles の元の値は、微分で零になる。 |
| `CechHomologyCycleCriterion` | `cechHomologyCycleValue` | サイクルの H の類を opcycles に写すと、その値の類になる。 |
| `CechHomologyCycleCriterion` | `cechHomologyMapCycleValue` | 短複体の射の H 上の写像は、サイクルの値に元の射を適用する。 |
| `CechHomologyCycleCriterion` | `cechHomologyMap_surjective_of_cycles` | 目標の各サイクルが境界を除いて持ち上がれば、H の射は全射。 |
| `CechHomologyCycleCriterion` | `cechHomologyMap_injective_of_cycles` | 境界への写像を元の境界へ戻せれば、H の射は単射。 |
| `CechHomologyCycleCriterion` | `cechHomologyMap_isIso_of_cycles` | サイクルの持ち上げと境界の反映から、各次数の H の同型性を得る。 |
| `CechLocalizationCochains` | `cechLocalizationFunctorAdditive` | 分数の局所化関手は加法的。 |
| `CechLocalizationCochains` | `cechLocalizationCochainsEquiv` | 各 Čech 次数の局所化と、局所化した係数の Čech の項の比較。 |
| `CechLocalizationCochains` | `cechLocalizationCochainsEquiv_mk` | Čech の各項の局所化比較は、各タプルの分母を保つ。 |
| `CechLocalizationCochains` | `cechLocalizationCochainsEquiv_differential` | 各項の局所化比較は、増大項を含めて Čech の余境界と可換。 |
| `CechLocalizationCochains` | `cechLocalizationComplexIso` | 有限被覆の全タプル Čech 複体と、実際の分数の局所化との同型。 |
| `CechLocalizationCochains` | `cechLocalizationCochainsEquiv_naturality` | 各項の分数の比較は、係数図式の射に自然。 |
| `CechLocalizationCochains` | `cechLocalizedCochainsDifferential` | 元の Čech の余境界を、分数の局所化の間の写像にする。 |
| `CechLocalizationCochains` | `cechLocalizationCochainsEquiv_differential_apply` | 局所化した余境界の比較の、元ごとの式。 |
| `CechLocalizationCochains` | `cechLocalizationCochains_exact_of_exact` | 局所化後の係数図式での完全性は、局所化した二つの余境界の完全性を与える。 |
| `CechLocalizationPi` | `cechLocalizationPiEquiv` | 有限積と局所化の線形同型。 |
| `CechLocalizationPi` | `cechLocalizationPiEquiv_mk` | 有限積との比較は、すべての成分で同じ分母を保つ。 |
| `CechLocalizationPi` | `cechLocalizationPiEquiv_projection` | 有限積との比較の各成分は、射影を局所化した写像である。 |
| `CechLocalizedAwayRestriction` | `cechLocalizedAwayRestriction` | 標準開の制限を、さらに外側の分母で局所化した写像。 |
| `CechLocalizedAwayRestriction` | `cechLocalizedAwayRestriction_surjective` | 追加因子が外側で逆になるなら、局所化した制限は全射。 |
| `CechLocalizedAwayRestriction` | `cechLocalizedAwayRestriction_injective` | 追加因子が外側で逆になるなら、局所化した制限は単射。 |
| `CechLocalizedAwayRestriction` | `cechLocalizedAwayRestriction_isIso` | 追加因子を外側で逆にした標準開の制限は、実際の加群の同型。 |
| `CechProductCoefficients` | `fullCechProductCoefficientDiagram` | 係数図式の成分ごとの直積。 |
| `CechProductCoefficients` | `fullCechProductCochainsEquiv` | 係数の直積と Čech 項の直積の交換。 |
| `CechProductCoefficients` | `fullCechProductDifferential_apply` | 直積の交換は Čech 微分と成分ごとに可換。 |
| `CechProductCoefficients` | `fullCechProduct_zero_injective` | 各係数図式の増大項の微分が単射なら、直積の微分も単射。 |
| `CechProductCoefficients` | `fullCechProduct_exact` | 各係数図式の増大 Čech が完全なら、直積も完全。 |
| `CechRefinementConeDouble` | `cechRefinementConeGrid` | 行の cone を並べた二重図式の項。 |
| `CechRefinementConeDouble` | `cechRefinementConeHorizontal` | 二重図式の水平方向は、各行の cone の微分。 |
| `CechRefinementConeDouble` | `cechRefinementConeVertical` | 二重図式の垂直方向は、二つの列方向の射の直積。 |
| `CechRefinementConeDouble` | `cechRefinementConeVertical_squared` | 列方向の二乗が零なら、cone の列方向の二乗も零。 |
| `CechRefinementConeDouble` | `cechRefinementConeGrid_commute` | 四角の可換性は、cone の二つの微分の可換性を与える。 |
| `CechRefinementConeDouble` | `cechRefinementConeGrid_colExact` | 元の二重図式の列が完全なら、cone の各列も完全。 |
| `CechRefinementConeDouble` | `cechRefinementConeGrid_zero_row_exact` | 正の行の cone と全ての列が完全なら、零番の行の cone も完全。 |
| `CechRefinementConeDouble` | `cechRefinementConeGrid_homologyMap_isIso` | B1 の二重図式の判定から得る、零番の行の Čech H の同型性。 |
| `CechRefinementConeHomology` | `cechRefinementCone_quasiIsoAt` | 自然数添字の cone が完全なら、元の射は各次数で quasi-isomorphism。 |
| `CechRefinementConeHomology` | `cechRefinementCone_homologyMap_isIso` | cone の完全性が与える、元の複体の各次数の H の同型性。 |
| `CechRefinementConeMap` | `cechRefinementConeMapTerm` | cone の各項に可換四角の成分を適用する。 |
| `CechRefinementConeMap` | `cechRefinementConeMapTerm_differential` | 可換四角の成分は cone の微分と可換。 |
| `CechRefinementConeMap` | `cechRefinementConeMap` | 可換四角が誘導する cone の射。 |
| `CechRefinementConeMap` | `cechRefinementConeMapTerm_comp` | cone の項への写像は合成を保つ。 |
| `CechRefinementConeMap` | `cechRefinementConeMapTerm_id` | cone の項への恒等写像。 |
| `CechRefinementConeMap` | `cechRefinementConeMapTerm_zero` | cone の項への零写像。 |
| `CechTupleCarrier` | `cechTupleChainsOn_map` | 生成元の台の条件から、鎖の写像の台の条件を得る。 |
| `CechTupleCarrier` | `cechTupleChainsOn_single_mem` | 台を指定した生成元の所属。 |
| `CechTupleCarrier` | `cechTupleChainsOn_boundary` | 境界は指定した頂点集合を保つ。 |
| `CechTupleCarrier` | `cechTupleChainsOn_prepend` | 集合内の頂点の先頭追加は、その集合を保つ。 |
| `CechTupleCarrier` | `cechTupleChainsOn_reindex` | 再添字付けは、頂点集合の像へ鎖を送る。 |
| `CechTupleCarrier` | `cechTupleComparisonHomotopy_stable_carrier` | 鎖写像で保たれる一つの頂点集合は、比較ホモトピーでも保たれる。 |
| `CechTupleRefinementHomotopy` | `cechRefinementAmbient` | 直和添字の左側を一つ目の写像で右側へ移す。 |
| `CechTupleRefinementHomotopy` | `cechRefinementProjection` | 直和添字を二つ目の写像により元の目標へ戻す。 |
| `CechTupleRefinementHomotopy` | `cechTupleRefinementHomotopy` | 二つの再添字付けをつなぐ整数鎖のホモトピー。 |
| `CechTupleRefinementHomotopy` | `cechTupleRefinementHomotopy_identity` | 再添字付けの比較ホモトピーの方程式。 |
| `CechTupleRefinementSupport` | `cechTupleRefinementHomotopy_carrier` | ホモトピーの値の頂点は、入力タプルの二つの像に含まれる。 |
| `CechTupleRefinementSupport` | `cechTupleRefinementHomotopy_support` | ホモトピーの各出力タプルの台は、二つの像の和集合の中にある。 |
| `CechTupleReindex` | `cechTupleReindex` | 頂点の写像に沿う、タプルの整数鎖の再添字付け。 |
| `CechTupleReindex` | `cechTupleReindex_single` | 再添字付けはタプルの生成元をそのまま写す。 |
| `CechTupleReindex` | `cechTupleReindex_comp` | 再添字付けは合成を保つ。 |
| `CechTupleReindex` | `cechTupleReindex_zero` | 長さ零の再添字付けは、添字の自己写像では恒等。 |
| `CechTupleReindex` | `cechTupleReindex_boundary` | 頂点の再添字付けは増大境界と可換。 |
| `CechZeroCochains` | `cechTupleSupport_empty` | 空タプルの台は空集合。 |
| `CechZeroCochains` | `fullCechZeroCochainsEquiv` | 長さ零の Čech 項と、係数図式の空集合の値の同型。 |
| `CechZeroCochains` | `fullCechZeroCochainsEquiv_naturality` | 空交叉の係数との同定は、係数図式の射に自然。 |
| `CechZeroCochains` | `fullCechZeroCochainsEquiv_exact` | 増大項を空交叉の係数へ置き換えても、増大 Čech の完全性は同じ。 |
| `OpenCoverCech` | `cechOpenIntersection` | 有限個の開集合の交叉。 |
| `OpenCoverCech` | `cechOpenIntersection_antitone` | 添字集合が増えると交叉は小さくなる。 |
| `OpenCoverCech` | `openCoverCechDiagram` | 前層を、有限交叉上の切断の共変な係数図式と見る。 |
| `OpenCoverCech` | `cechOpenIntersection_refinement` | タプルに沿う細分の包含。 |
| `OpenCoverCech` | `openCoverCechRefinementCochains` | 細分による全タプル Čech 項の制限。 |
| `OpenCoverCech` | `openCoverCechRefinementCochains_apply` | 細分による制限の成分表示。 |
| `OpenCoverCech` | `openCoverCechRefinementCochains_differential` | 細分の制限は余境界と可換。 |
| `OpenCoverCech` | `openCoverCechRefinementMap` | 細分による Čech 複体の射。 |
| `OpenCoverCech` | `openCoverCechCoefficientMap` | 係数前層の射が有限交叉の係数図式に誘導する射。 |
| `OpenCoverCech` | `openCoverCechRefinementCochains_naturality` | 細分の制限は係数前層の自然変換に自然。 |
| `OpenCoverCech` | `openCoverCechRefinementCochains_id` | 恒等細分は恒等写像を与える。 |
| `OpenCoverCech` | `openCoverCechRefinementCochains_comp` | 二つの細分を続けた制限は、合成細分の制限。 |
| `OpenCoverCechEvaluation` | `openCoverCechEvaluateAt` | タプルの整数鎖を、指定した開集合上の切断として評価する。 |
| `OpenCoverCechEvaluation` | `openCoverCechEvaluateAt_single` | 一つのタプルの評価は切断の制限。 |
| `OpenCoverCechEvaluation` | `openCoverCechEvaluateAt_restrict` | 台に現れる全タプルの交叉に入る開集合からは、更に制限できる。 |
| `OpenCoverCechEvaluation` | `openCoverCechEvaluateAt_boundary_single` | 境界の生成元の評価は、余境界のその生成元での評価。 |
| `OpenCoverCechEvaluation` | `openCoverCechEvaluateAt_boundary` | 台に現れる交叉が指定開集合を含めば、境界と余境界は評価で対応する。 |
| `OpenCoverCechEvaluation` | `openCoverCechEvaluateAt_naturality` | 指定開集合での評価は、係数前層の射に自然。 |
| `OpenCoverCechRefinementHomotopy` | `cechOpenIntersection_refinement_union` | 細分の交叉は、二つの添字の像を合わせた交叉に含まれる。 |
| `OpenCoverCechRefinementHomotopy` | `openCoverCechRefinementHomotopy_support` | 比較ホモトピーに現れるタプルの交叉は、細分の交叉を含む。 |
| `OpenCoverCechRefinementHomotopy` | `openCoverCechRefinementHomotopyTerm` | 細分の二つの選択を比較する Čech の次数一低い成分。 |
| `OpenCoverCechRefinementHomotopy` | `openCoverCechRefinementHomotopyTerm_zero` | 長さ零での比較成分は零。 |
| `OpenCoverCechRefinementHomotopy` | `openCoverCechRefinementHomotopyTerm_boundary` | 比較鎖の境界への評価は、比較コチェインの余境界に対応する。 |
| `OpenCoverCechRefinementHomotopy` | `openCoverCechRefinementHomotopyTerm_identity` | 二つの細分写像は、制限付きの比較成分によるコチェインホモトピーで結ばれる。 |
| `OpenCoverCechRefinementIndependence` | `openCoverCechRefinementHomotopyComponent` | 細分比較の複体としてのホモトピーの成分。 |
| `OpenCoverCechRefinementIndependence` | `openCoverCechRefinementHomotopyComponent_succ` | 連続する次数での比較ホモトピーの成分。 |
| `OpenCoverCechRefinementIndependence` | `openCoverCechRefinementHomotopy` | 同じ細分の二つの添字の選択は、コチェイン写像としてホモトピック。 |
| `OpenCoverCechRefinementIndependence` | `openCoverCechRefinement_homologyMap_eq` | Čech H 上の細分の射は、細分の添字の選択によらない。 |
| `OpenCoverCechRefinementNaturality` | `openCoverCechRefinementMap_naturality` | 細分の複体の射は係数前層の射に自然。 |
| `OpenCoverCechRefinementNaturality` | `openCoverCechRefinementMap_id` | 恒等細分が誘導する複体の射は恒等。 |
| `OpenCoverCechRefinementNaturality` | `openCoverCechRefinementMap_comp` | 細分の複体の射は細分の合成を保つ。 |
| `OpenCoverCechRefinementNaturality` | `openCoverCechRefinement_homology_naturality` | 各次数の Čech H の細分比較は、係数前層の射に自然。 |
| `OpenCoverCechResolution` | `openCoverIntersectionPresheaf` | 固定した開集合との交叉上の切断を取る前層。 |
| `OpenCoverCechResolution` | `openCoverIntersectionPresheafMap` | 固定する開集合を狭めるときの交叉前層の制限。 |
| `OpenCoverCechResolution` | `openCoverCechResolution` | 開被覆の増大 Čech の一つの項を前層にする。 |
| `OpenCoverCechResolution` | `openCoverCechResolutionDifferential` | 増大 Čech の余境界は開集合について自然。 |
| `OpenCoverCechResolution` | `openCoverCechResolutionDifferential_squared` | 前層としての増大 Čech の微分の二乗は零。 |
| `SchemeCommonAffineCover` | `schemeCommonOpenCover` | 二つの開被覆の交叉による共通細分。 |
| `SchemeCommonAffineCover` | `schemeCommonOpenCover_iSup` | 二つの被覆の交叉も全空間を被覆する。 |
| `SchemeCommonAffineCover` | `schemeCommonOpenCover_le_left` | 共通細分から最初の被覆への包含。 |
| `SchemeCommonAffineCover` | `schemeCommonOpenCover_le_right` | 共通細分から二つ目の被覆への包含。 |
| `SchemeCommonAffineCover` | `schemeCommonOpenCover_isAffineOpen` | アフィン対角のスキームでは、共通細分もアフィン開被覆。 |
| `SchemeCommonAffineCover` | `cechOpenIntersection_isAffineOpen` | アフィン対角のスキームのアフィン開の非空有限交叉はアフィン。 |
| `SchemeFinitePrincipalRefinement` | `schemeFinitePrincipalRefinement` | アフィン開集合の任意の開被覆は、単位イデアルを生成する有限標準開被覆で細分できる。 |
| `SchemeOpenCoverCechIntersections` | `cechOpenIntersection_scheme_preimage` | スキームの逆像は Čech の有限交叉を保つ。 |
| `SchemeOpenCoverCechIntersections` | `cechOpenIntersection_scheme_image_preimage` | 開埋め込みの像による交叉の表示。 |

既存の数学宣言の型・本文は変更していない。新しい sorry・admit・公理・計算量上限はなく、最終出力と利用側の `SerrePositivity.Cech.AugmentedRingCechExact` の型も変更していない。段 2e の実測は前回から本体 2,387 行増え、**247 本・25,976 行**、入口の差分を含め **26,225 行**。50,000 行の停止基準には達していない。

**停止点 2e ではない。** 残りは、準連接層のアフィン座標から元の係数への輸送、実際の二重 Čech の各交叉上での完全性の供給、任意のアフィン被覆の完全性と一般の細分の H の同型への適用、動く係数環の標準開との照合、および五つの比較同士の可換性。これらの下書きは監査数とこのコミットには含めない。共通細分の比較の写像は実際の制限であり、非標準の座標や前像の選択はその同型性を証明するためだけに使う。自然性と選択の独立性の証明を、一般の同型性の証明に置き換えない。


## 11-12：実際のアフィン被覆の完全性と細分の H の同型（85d6de297）

数学コミット `85d6de297`。新規 **14 本・64 宣言・1,147 行**、入口を含む git 差分 **1,163 行**。対象と直接 importer は **4,466 jobs で成功**。別実行の公理監査は **7,995 宣言・標準三公理のみで成功**。停止点 2e ではない。一般のアフィン被覆上の増大 Čech の完全性と、実際の細分写像が誘導する各次数の H の同型まで到達した。共通細分の独立性の同型への接続、Proj のネイティブな構造層との R 線形比較と五つの比較の接続は、次の未検証の束に残る。

| 宣言 | 主張・用途 |
|---|---|
| `openCoverCechCoefficientIso` | 係数前層の自然同型を有限交叉の係数図式へ移す。 |
| `openCoverCechAcyclic_of_iso` | 自然同型な係数前層へ、増大 Čech の完全性を移す。 |
| `openCoverCechAcyclic_of_cycles` | 増大項の核の消滅と、正長の各サイクルの前像から完全性を得る。 |
| `openCoverCechAcyclic_of_double_zero_row` | 二重 Čech の零番の行の完全性から、元の前層の Čech 完全性を得る。 |
| `openCoverIntersectionPresheafTopIso` | 全空間との交叉を取る前層は、元の前層と自然に同型。 |
| `openCoverCechDouble_zero_col_exact` | 元の前層の Čech 完全性から、二重図式の零番の列の完全性を得る。 |
| `openCoverCechAcyclic_of_refinement` | 細分の完全性と各交叉上の完全性から、元の被覆の増大 Čech 完全性を得る。 |
| `openCoverCechZeroEquiv` | 開被覆の空タプルの項と、大域切断の同型。 |
| `openCoverCechZeroEquiv_symm_apply` | 大域切断を空タプルの項へ戻すと、その交叉への制限になる。 |
| `openCoverCechAugmentation` | 大域切断から各被覆開の切断への対角の制限。 |
| `openCoverCechAugmentation_eq` | 対角の制限は、空タプルの項からの Čech 微分と一致。 |
| `openCoverCechAugmentation_squared` | 対角の制限のあとに Čech 微分を適用すると零。 |
| `openCoverCechAugmentation_injective` | 増大 Čech が完全なら、大域切断からの対角の制限は単射。 |
| `openCoverCechAugmentation_exact` | 増大 Čech の完全性は、大域切断からの対角の制限でも完全。 |
| `openCoverCechRefinement_augmentation` | 細分の写像は、共通の大域切断からの増大写像を保つ。 |
| `openCoverCechDoubleTerm` | 二つの被覆の実際の増大 Čech の二重図式の項。 |
| `openCoverCechDoubleHorizontal` | 二重 Čech の水平方向の余境界。 |
| `openCoverCechDoubleVertical` | 二重 Čech の垂直方向の余境界。 |
| `openCoverCechDoubleHorizontal_squared` | 水平方向の微分の二乗は零。 |
| `openCoverCechDoubleVertical_squared` | 垂直方向の微分の二乗は零。 |
| `openCoverCechDouble_commute` | 二つの方向の Čech 微分は可換。 |
| `openCoverCechDouble_rowExact` | 細分の包含から、正次数の行の完全性を得る。 |
| `openCoverCechDouble_colExact` | 各水平交叉上の増大 Čech が完全なら、その直積である列も完全。 |
| `openCoverCechDouble_exact_zero_iff` | 二重 Čech に既存 B1 の零番の行・列の比較を適用する。 |
| `openCoverCechDiagramFunctor` | 前層から有限交叉の係数図式への関手。 |
| `openCoverCechDiagramFunctorAdditive` | 有限交叉への制限は、係数の射の加法を保つ。 |
| `fullCechComplexFunctorAdditive` | 全タプル Čech 複体の係数関手は、射の加法を保つ。 |
| `openCoverCechFunctor` | 前層から被覆の通常の Čech 複体への関手。 |
| `openCoverCechFunctorAdditive` | 前層から Čech 複体への関手は加法的。 |
| `openCoverCechRefinementCone_exact` | 共通増大項を保つ、二つの完全な Čech の細分写像の cone の完全性。 |
| `openCoverCechRefinement_homologyMap_isIso` | 各交叉上の完全性から、細分の実際の Čech H の射は同型。 |
| `openCoverCechResolutionRowIso` | 二重 Čech の一つの行の係数を、交叉上の係数図式の直積として表示する。 |
| `cechOpenIntersection_le_tuple_member` | 正長の交叉は、その中に現れる任意の一つの被覆開に含まれる。 |
| `openCoverCechResolutionRow_zero_injective` | 細分である二重 Čech の正次数の行では、増大項からの微分は単射。 |
| `openCoverCechResolutionRow_exact` | 細分である二重 Čech の正次数の行は、増大 Čech として完全。 |
| `openCoverResolutionZeroIntersection` | 長さ零の被覆交叉を付けても、指定開集合は変わらない。 |
| `openCoverCechResolutionZeroComponentIso` | 増大 Čech 前層の零項と元の前層の、各開集合での同型。 |
| `openCoverCechResolutionZeroIso` | 増大 Čech 前層の零項は、開集合について自然に元の前層と同型。 |
| `cechOpenRestrictedIntersection_eq` | 指定開集合との各交叉の等式を、有限交叉の等式へ移す。 |
| `openCoverCechRestrictedCoverIso` | 指定開集合内で同じ被覆の、有限交叉の係数図式の自然同型。 |
| `openCoverCechAcyclic_of_intersection_eq` | 指定開集合内で同じ被覆へ、増大 Čech の完全性を移す。 |
| `openCoverIntersectionPresheafNestedIso` | 二段階の交叉前層は、交叉した開集合の前層に自然に同型。 |
| `openCoverIntersectionPresheafNestedIsoOfLe` | 小さい開集合での交叉なら、先の大きい開集合の制限は冗長になる。 |
| `cechOpenIntersection_insert` | 頂点の挿入に対応する開集合の交叉。 |
| `openCoverCechSplitIntersection_isIso` | 交叉全体を含む頂点の挿入による、切断の制限は同型。 |
| `openCoverCechSplitIntersection_zero_injective` | 交叉全体を含む頂点がある場合、増大項の微分は単射。 |
| `openCoverCechSplitIntersection_exact` | 交叉全体を含む頂点がある前層の増大 Čech の完全性。 |
| `schemeFiniteCommonOpenCover` | Fin で添字付けした、有限の共通開被覆。 |
| `schemeFiniteCommonCoverLeft` | 有限の共通被覆から第一の被覆への添字。 |
| `schemeFiniteCommonCoverRight` | 有限の共通被覆から第二の被覆への添字。 |
| `schemeFiniteCommonOpenCover_iSup` | 有限共通被覆の全空間の被覆性。 |
| `schemeFiniteCommonOpenCover_le_left` | 有限共通被覆から第一の被覆への包含。 |
| `schemeFiniteCommonOpenCover_le_right` | 有限共通被覆から第二の被覆への包含。 |
| `schemeFiniteCommonOpenCover_isAffineOpen` | アフィン対角の下で、有限共通被覆の各開集合はアフィン。 |
| `schemeModuleCechPresheaf` | 構造層加群の切断を、大域の係数環上の前層として扱う。 |
| `schemeModuleAffineCechCoefficientEquiv` | アフィン開埋め込みの座標の切断と、元のスキームの切断の加法群の同型。 |
| `schemeModuleAffineCechCoefficientEquiv_naturality` | アフィン座標との加法的比較は、交叉を狭める制限に自然。 |
| `schemeModuleStandardOpenCech_exact` | アフィン開集合の標準開被覆上の、準連接層の増大 Čech 完全性。 |
| `schemeModuleStandardOpenCech_zero_injective` | アフィン開集合の標準開被覆における、準連接層の増大項の単射性。 |
| `schemeModuleStandardOpenCech_acyclic` | アフィン標準開被覆の完全性を、増大項の単射性とともにまとめる。 |
| `schemeModuleStandardOpenCech_restrict` | アフィン標準開被覆の完全性は、小さいアフィン開への制限でも成り立つ。 |
| `schemeModuleAffineCoverCech_acyclic` | アフィン開集合をちょうど被覆するアフィン開被覆の増大 Čech 完全性。 |
| `schemeModuleAffineOpenCech_acyclic` | アフィン開と各被覆開との交叉がアフィンで、その開を被覆すれば、増大 Čech は完全。 |
| `schemeModuleCechRefinement_homologyMap_isIso` | 準連接層のアフィン開被覆の細分は、各次数の Čech H の同型を誘導する。 |

段 2e の検証済み実測：**261 本・27,123 行**、入口を含め **27,388 行**。上限 50,000 行内。次の 18 本の未検証の下書きはこの数に含めない。


## 11-12：共通細分の独立性と実際の Proj の Čech への接続（96e18ab78）

数学コミット **`96e18ab78`**。新規 **24 本・65 宣言・1,646 行**、入口を含む差分 **1,671 行**。対象と直接 importer は **4,491 jobs で成功**、別実行の監査は **8,160 宣言・標準三公理のみ**。共通アフィン細分の独立性、係数の射・実際のスキームの引き戻しに対する比較の自然性、実際の Proj の構造層の標準開との R 線形比較、任意の有限アフィン被覆での射影有限性を接続した。

**停止点 2e ではない。** `projectiveProjNativeFilteredHomologyIso` は native な極限の H と、固定した共通係数上の旧 NatChart の各段の H を比較する。各有限段の実際の切断への自然な比較と、動く scalar の grading の carrier の照合はまだ未完である。実際の射影の Čech の引き戻しと旧 NatChart の写像との複体全体の一致、底変換・閉厚化・Frobenius・filtered colimit の五つの比較同士の最終的な可換性も残る。模型の構成は承認どおり 2g に残す。

| 宣言 | 主張・用途 |
|---|---|
| `openCoverCechRefinementH` | 実際の細分写像が誘導する Čech H の射。 |
| `openCoverCechCoefficientH` | 係数前層の射が誘導する Čech H の射。 |
| `openCoverCechComparisonIso` | 共通細分を用いる、二つの被覆の Čech H の比較。 |
| `openCoverCechComparisonIso_naturality` | 共通細分による Čech H の比較は係数前層の射に自然。 |
| `openCoverCechRefinementH_eq` | 細分写像の選択を変えても、誘導される Čech H の射は同じ。 |
| `openCoverCechComparisonIso_choice` | 同じ共通細分への添字の選択によらず、被覆間の Čech H の比較は同じ。 |
| `openCoverCechComparisonIso_refine` | 共通細分をさらに細分しても、Čech H の被覆間の比較は変わらない。 |
| `openCoverCechComparisonIso_trans` | 一つの共通細分で作る三つの Čech H の比較は合成に整合する。 |
| `openCoverCechAcyclic_restrictScalars` | 係数環を制限しても、増大 Čech の完全性は保たれる。 |
| `projectiveHomogeneousChartLinearEquiv_fraction` | 次数零のチャートの線形同型は、分子と分母の冪を保つ。 |
| `projectiveHomogeneousChartLinearEquiv_fraction_reflect` | 斉次分数での表示から、元の多項式加群の局所化での表示を取り戻す。 |
| `projectiveHomogeneousRingChartMap_denominator` | 多項式環上の写像は、標準開の分母の像を保つ。 |
| `projectiveHomogeneousRingChartMap_powers` | 標準開の分母の冪の部分モノイドは、係数環の写像で次の段へ移る。 |
| `projectiveHomogeneousRingChartMap_fraction` | 斉次局所化の写像は、分子に係数の写像を適用し分母の指数を保つ。 |
| `projectiveHomogeneousChartLinearEquiv_map` | 次数零の加群の写像は、実際の斉次局所化の環の写像と一致する。 |
| `projectiveNatChartColimitTargetIso` | 指定された実際の極限の加群の標準開と、各有限段の標準開の filtered colimit の同型。 |
| `projectiveNatCechFilteredHomologyTargetIso` | 指定された実際の極限の係数での Čech H と、有限段の Čech H の余極限との比較。 |
| `projectiveNatGradedChartIso_inverse_mem` | 指定した次数の同型は、逆写像も同じ次数を保つ。 |
| `projectiveNatGradedChartIso` | 次数成分を保つ加群の同型が、標準開の係数図式に与える自然同型。 |
| `projectiveProjCechOpen` | Proj の変数に対応する実際の標準開の族。 |
| `projectiveProjCechOpen_intersection` | 変数の像の積の標準開は、Čech の有限交叉と一致する。 |
| `projectiveProjCechSectionLinearEquiv` | 非空交叉の斉次局所化と、構造層の実際の切断との R 線形同型。 |
| `projectiveProjCechSectionLinearEquiv_naturality` | 非空交叉の R 線形同型は、Čech の制限写像に自然。 |
| `projectiveProjNativeCechComplexIso` | 斉次局所化で計算した Čech 複体と、実際の標準開の構造層の Čech 複体の同型。 |
| `projectiveProjNativeNatCechComplexIso` | 指定次数の代数的な複体から、実際の Proj の標準開への比較。 |
| `projectiveProjNativeStandardCechHomology_finite` | 実際の Proj の構造層の標準開 Čech H の有限性。 |
| `projectiveProjNativeAffineCechHomology_finite` | 実際の Proj の構造層の、任意の有限アフィン被覆での Čech H の有限性。 |
| `projectiveProjNativeCech_preimageOpen` | 実際の Proj の標準開の逆像は、次の係数環での同じ標準開。 |
| `projectiveProjNativeCechMap` | Proj の実際の構造層を引き戻す、標準開の Čech の射。 |
| `projectiveProjNativeFilteredHomologyIso` | 実際の極限の Proj の構造層の Čech H と、各有限段の次数零 Čech H の余極限の比較。 |
| `projectiveProjRingMapSections_apply` | 斉次分数の係数の写像は、実際の Proj の構造層の引き戻しそのもの。 この式は閉厚化や底変換の平坦性を必要としない。 |
| `projectiveProjScalarNaturality_fraction` | 基底環のスカラーの斉次分数は、実際の係数環の写像で保たれる。 |
| `projectiveScalarToGlobalSections_naturality` | Proj の引き戻しは、元の基底環の大域スカラーを保つ。 |
| `projectiveScalarToZero` | 基底環のスカラーは零次成分に属する。 |
| `projectiveScalarToGlobalSections` | 分母 1 のチャートを通る、基底環から Proj の大域切断への写像。 |
| `projectiveScalarToGlobalSections_restrict` | 大域スカラーの標準開への制限は、同じ定数の斉次分数である。 |
| `projectiveHomogeneousAway_scalar_mul` | 元の基底環の加群作用は、零次成分を通る定数の乗法に一致する。 |
| `projectiveProjAwaySectionLinearEquiv` | 正次数の標準開の構造層の環同型は、元の基底環上でも線形。 空交叉の切断は同一視せず、正次数のチャートだけを扱う。 |
| `projectiveProjAwaySectionLinearEquiv_pow` | 標準開の切断への実際の比較は冪写像と可換。零環となる開も含む。 |
| `schemeCechPreimageCoefficientIso` | 逆像被覆の有限交叉と、押し出した前層の係数図式の自然同型。 |
| `schemeCechPreimageComplexIso` | 逆像被覆と押し出した前層の Čech 複体の自然な同型。 |
| `schemeCechPreimageRefinement_naturality` | 逆像被覆の比較は、細分の制限と可換。 |
| `schemeCechPullbackMap` | スキームの射に沿う係数の射から、逆像被覆への Čech の射を作る。 |
| `schemeCechPullbackMap_refinement` | 逆像被覆への Čech の射は、細分の制限と可換。 |
| `schemeCechPullback_homology_refinement` | 逆像被覆への Čech H の射は、細分の H の射と可換。 |
| `schemeCechPullback_comparison_naturality` | 共通細分の Čech H の比較は、実際のスキームの引き戻しに自然。 |
| `schemeModuleCommonAffineCechHomologyIso` | 二つの有限アフィン被覆による、準連接層の Čech H の比較同型。 |
| `schemeModuleCechComparison_commonRefinement_independent` | 実際の準連接係数の二つの共通アフィン細分による Čech H の比較は同じ。 |
| `schemeModuleCommonAffineCechScalarHomologyIso` | 二つの有限アフィン被覆による、準連接層の Čech H の比較同型。 |
| `schemeModuleCechScalarComparison_commonRefinement_independent` | 実際の準連接係数の二つの共通アフィン細分による Čech H の比較は同じ。 |
| `schemeModuleCechScalarRefinement_homologyMap_isIso` | 準連接層のアフィン被覆の細分比較は、任意の基底環の作用に制限しても同型。 |
| `schemeStructureModule` | 構造層を、それ自身の上の階数一の加群として扱う。 |
| `schemeStructureModuleQuasicoherent` | 構造層加群は準連接。 |
| `schemeStructureCechPresheaf` | 構造層の切断を大域切断の環上で扱う、実際の係数前層。 |
| `schemeStructureCechPresheaf_smul` | 構造層の切断の大域スカラー作用は、制限した切断の乗法。 |
| `schemeStructureCechRefinement_homologyMap_isIso` | 構造層のアフィン被覆の細分は、実際の Čech H の同型を誘導する。 |
| `schemeStructurePrimeCast` | 基底の p = 0 は、空の開も含めすべての切断環へ移る。 |
| `schemeStructureCechFrobeniusCoefficient` | 構造層の切断の実際の Frobenius。基底のスカラー作用を p 乗でねじる。 |
| `schemeStructureCechFrobeniusCoefficient_apply` | 構造層の Frobenius の各開上の式は p 乗そのもの。 |
| `schemeStructureCechPullback_scalar` | 構造層の切断の引き戻しは、大域スカラーの引き戻しと整合する。 |
| `schemeStructureCechPullbackCoefficient` | 実際の構造層の引き戻しを、固定した基底環上の前層の射として扱う。 |
| `schemeStructureCechPullbackMap` | スキームの射の、構造層の Čech 複体上の実際の引き戻し。 |
| `schemeCechRefinedPullbackIntersection_le` | 逆像被覆の細分の有限交叉は、元の有限交叉の逆像に含まれる。 |
| `schemeStructureCechRefinedPullbackMap` | 逆像被覆への引き戻しと、さらに細分する写像の合成。 |
| `schemeStructureCechRefinedPullbackMap_apply` | 各タプルでの Čech の引き戻しは、実際の構造層の appLE そのもの。 |

段 2e の検証済み実測：**285 本・28,769 行**、入口を含め **29,059 行**。上限 50,000 行内。未検証の下書きは含めない。


## 11-12 夜：実際の底変換と動く基底の射の比較（d01affd63）

**停止点 2e ではない。** 数学コミット `d01affd63`。26 モジュール・89 宣言、1,928 行（入口登録を含め 1,955 行）。
対象と直接 importer `SerrePositivity.AlgebraicGeometry` は **4,517 jobs 成功**。
別実行の `scripts/audit_kst_scheme_lemmas.lean` は **8,370 宣言、標準三公理のみ**。
どちらも共有鍵 `with_build_lock.sh --wait 3600` を実行中だけ取得した。
既存の宣言は変更せず、新規ファイルと入口の import の追加だけ。sorry・admit・新規公理・計算量上限の追加なし。

到達点：

- 実際の Cartesian なアフィン切断の正方形を元の基底環上のテンソル積と同一視し、左右の入射・純テンソル・制限への自然性を示した。平坦性は不要。
- `schemeStructureCechBaseChangeComplexIso` と `schemeStructureCechNativeTensorComplexIso` は、実際の逆像被覆の通常の Čech 複体を比較する。空交叉の Γ とテンソル積の交換を仮定しない。`schemeStructureCechNativeFlatBaseChangeIso` の H との交換だけに flat を要求する。
- `projectiveProjNativeNatCechComplexIso_naturality` は旧次数零加群の計算と実際の Proj の引き戻しを同じ射として照合する。
- `gradedOriginalProjNativeCechComplexIso`・`gradedOriginalProjCechScalarRestrictionIso`・`gradedOriginalProjNativeCechComplexIso_naturality` は、各段で元の Proj を使ったまま、共通基底上の計算と元の基底のスカラー制限をつなぐ。Mathlib の Proj.map の宇宙の指定に合わせ、射を扱う grading の carrier は環と同じ宇宙に置く。実際の部分加群の次数成分はこの形であり、最終出力の宇宙は変更しない。
- `projectiveHomogeneousChartLinearEquiv_frobenius`・`gradedOriginalProjNativeChart_frobenius` は実際の切断の p 乗と一致する。`schemeStructureCommonAffineCechFrobenius_naturality` は共通アフィン細分の比較と可換で、細分の同型性は準連接性から供給している。

**未完**：各段を実際の元の Proj の Čech H とした filtered 図式全体の比較と、その余極限、I 進の閉厚化・互換族・既存の Rees の形式関数への接続、および比較同士の可換性の最終照合。
`projectiveProjNativeFilteredHomologyIso` の従来の型（極限先の native H と旧有限段の H の余極限）だけを、実際の各段の比較の完成とは数えない。
模型と有限段の存在自体は承認どおり 2g の仕事であり、この束では作っていない。
最終出力 `SerrePositivity.Cech.AugmentedRingCechExact` と利用側の型は変更していない。
今夜は停止点を報告・コミットした後、取り込みを待たず 2f の F0〜F3 へ進む（11-12 夜の指示）。

登録したモジュール：

- `ProjectiveProjRingMapSectionsOfEq`
- `ProjectiveProjNativeCechEvaluation`
- `GradedScalarComponents`
- `GradedOriginalProjSections`
- `SchemeAffinePullbackSections`
- `SchemeScalarMorphism`
- `SchemeAffinePullbackSectionsNaturality`
- `SchemeAffineBaseChangeTensor`
- `SchemeAffineBaseChangeTensorLinear`
- `ModuleCechScalarExtension`
- `SchemeStructureCechBaseChangeCoefficient`
- `ProjectiveProjNativeCechNaturality`
- `SchemeAffineSectionModule`
- `SchemeAffineBaseChangeNativeSections`
- `SchemeStructureCechBaseChangeIso`
- `ProjectiveProjNativeFrobeniusEvaluation`
- `GradedOriginalProjCech`
- `GradedOriginalProjCechScalarRestriction`
- `GradedOriginalProjRingMapSections`
- `GradedOriginalProjScalarNaturality`
- `SchemeStructureCechNativeTensor`
- `GradedOriginalScalarRingMap`
- `SchemeStructureCechComparisonNaturality`
- `GradedOriginalProjCechMaps`
- `GradedOriginalProjCechNaturality`
- `GradedOriginalProjFrobeniusEvaluation`

宣言と主張（一行ずつ。生成宣言は監査に含む）：

| 宣言 | 主張 |
| --- | --- |
| `projectiveProjRingMapSections_of_eq` | 同じ値の指定された分母を使う、標準開の構造層の引き戻しの自然性。 |
| `projectiveProjNativeNatCechComplexIso_apply` | 実際の構造層への複体の比較は、各タプルで非空交叉の切断の同型。 |
| `projectiveProjNativeCech_intersection_le` | 標準開の交叉は、実際の Proj の射での対応する交叉の逆像に含まれる。 |
| `projectiveProjNativeCechMap_apply` | 実際の Proj の Čech の射は、タプルごとに構造層の appLE に等しい。 |
| `gradedScalarComponents` | 元の次数の carrier を、指定した基底環上の部分加群として扱う。 |
| `mem_gradedScalarComponents` | scalar を指定し直しても、各次数の所属の条件は変わらない。 |
| `gradedScalarComponentsGradedRing` | scalar を指定し直した次数成分は、同じ分解を持つ次数付き環になる。 |
| `gradedScalarToOriginal` | scalar を指定した次数付き環から、元の次数付き環への恒等写像。 |
| `gradedOriginalToScalar` | 元の次数付き環から、scalar を指定した次数付き環への恒等写像。 |
| `gradedScalarAwayIso` | 同じ carrier を持つ二つの grading の斉次局所化は、環として自然に同型。 |
| `gradedScalarAwayIso_val` | 二つの grading の比較は、周囲の通常の局所化の値を保つ。 |
| `gradedScalarAwayIso_awayMap` | carrier の比較は、標準開を狭める斉次局所化の制限と可換。 |
| `gradedOriginalAwayModule` | generic な grading の斉次局所化の R 加群構造。通常の局所化への単射で移す。 |
| `gradedScalarAwayLinearEquiv` | 同じ grading の carrier の比較は、指定した基底環上でも線形。 |
| `gradedScalarComponentsGradedSMul` | 係数環を明示した carrier 上にも、同じ次数付き作用がある。 |
| `gradedSubmoduleScalarRestrictionMemClass` | 大きい基底環の部分加群は、共通の小さい基底環の作用でも閉じる。 |
| `gradedOriginalScalarToZero` | 基底環のスカラーは零次成分に属する。 |
| `gradedOriginalScalarToGlobalSections` | 分母 1 のチャートを通る、基底環から Proj の大域切断への写像。 |
| `gradedOriginalScalarToGlobalSections_restrict` | 大域スカラーの標準開への制限は、同じ定数の斉次分数である。 |
| `gradedOriginalAway_scalar_mul` | 元の基底環の加群作用は、零次成分を通る定数の乗法に一致する。 |
| `gradedOriginalProjAwaySectionLinearEquiv` | 正次数の標準開の構造層の環同型は、元の基底環上でも線形。 |
| `gradedOriginalProjAwaySectionLinearEquiv_pow` | 標準開の切断への実際の比較は冪写像と可換。零環となる開も含む。 |
| `gradedOriginalScalarToGlobalSections_comp` | 共通の基底環の大域スカラーは、元の基底環を通る合成と一致する。 |
| `schemeAffinePullbackSectionIso` | アフィン交叉上の実際の切断は、三つの切断環の canonical な pushout と同型。 |
| `schemeAffinePullbackSectionIso_inl` | pushout の左の写像は、実際の構造層の引き戻し。 |
| `schemeAffinePullbackSectionIso_inr` | pushout の右の写像も、実際の構造層の引き戻し。 |
| `schemeAffinePullbackIntersection_isAffineOpen` | 同じ実際の底変換の交叉はアフィン開である。 |
| `schemeScalarMorphism` | 大域スカラーが定める、Spec R への構造射。 |
| `schemeScalarHom` | Spec R への構造射から得られる、大域スカラー。 |
| `schemeScalarMorphism_appTop` | 構造射に移した大域スカラーを、Γ–Spec の三角恒等式で回収する。 |
| `schemeScalarHom_scalarMorphism` | 構造射を経由しても、大域スカラーの環準同型は変わらない。 |
| `schemeScalarHom_naturality` | 実際の構造射の可換な正方形から、切断の引き戻しの scalar の整合性を得る。 |
| `schemeAffinePullbackSectionIso_naturality` | 底変換の canonical なアフィン切断の比較は、開集合を狭める制限に自然。 |
| `schemeAffineSectionAlgebra` | 構造射を指定したアフィン開の切断を、基底環上の代数として束ねる。 |
| `schemeAffineBaseChangeSections_isPushout` | 実際のアフィン切断の正方形を、元の R と A を頂点に持つ pushout に移す。 |
| `schemeAffineBaseChangeTensorIso` | 実際の底変換のアフィン切断と、元の環上のテンソル積の環同型。 |
| `schemeAffineBaseChangeTensorIso_left` | テンソル積の左の写像は、底変換先の構造射が誘導する scalar の写像。 |
| `schemeAffineBaseChangeTensorIso_right` | テンソル積の右の写像は、元の構造層の実際の引き戻し。 |
| `schemeAffineBaseChangeTensorIso_tmul` | 純テンソルの実際の切断への像は、scalar の像と切断の引き戻しの積。 |
| `schemeAffineBaseChangeSectionsLinearEquiv` | 実際のアフィン底変換の切断の比較は、底変換先の環上で線形。 |
| `moduleCechScalarExtension` | スカラーを制限した係数への射の、図式に自然なテンソル積からの延長。 |
| `moduleCechScalarExtension_one_tmul` | 自然なテンソル積からの射は、1 と元の切断の純テンソルを引き戻す。 |
| `schemeStructureCechBaseChangePullbackCoefficient` | 基底環の変わる構造層の引き戻し。スカラー制限の合成を明示する。 |
| `schemeStructureCechBaseChangeDiagramRestriction` | 実際の基底変更から得る、逆像被覆の係数図式への射。 |
| `schemeStructureCechBaseChangeDiagramMap` | 実際の切断の引き戻しをテンソル積から延長した、自然な係数の射。 |
| `projectiveProjNativeCechSection_map` | 標準開上の分数の比較は、交叉の実際の切断への引き戻しに自然。 |
| `projectiveProjNativeNatCechComplexIso_naturality` | 次数零加群の Čech の射は、実際の構造層の Čech の引き戻しと一致する。 |
| `schemeAffineSectionAlgebra_scalar` | 構造射で定める局所のスカラーは、大域スカラーを制限した切断。 |
| `schemeAffineSectionModuleEquiv` | 実際の構造層の係数加群と、構造射で束ねた切断環は同じ加群。 |
| `schemeAffineBaseChangeNativeSectionsEquiv` | アフィン底変換の実際の切断の同型を、元の構造層の係数加群の間で述べる。 |
| `schemeAffineBaseChangeNativeSectionsEquiv_unit` | 実際の切断の同型は、1 と元の切断の純テンソルを構造層の引き戻しへ送る。 |
| `schemeStructureCechBaseChangeSectionIso` | アフィン交叉の切断の同型を、逆像被覆の対応する交叉まで輸送する。 |
| `schemeStructureCechBaseChangeDiagramMap_app` | 自然なテンソル積の射のアフィン交叉での成分は、実際の切断の同型。 |
| `schemeStructureCechBaseChangeDiagramMap_isIso` | 非空アフィン交叉において、実際の係数の底変換の射は同型。 |
| `schemeStructureCechBaseChangeComplexIso` | 実際の底変換の切断の Čech 複体は、係数をテンソル積にした Čech 複体と同型。 |
| `projectiveNatGradedChartZeroFrobenius` | 捻り零の Frobenius は、同じ次数零チャートへの半線形写像。 |
| `projectiveNatGradedChartZeroFrobenius_val` | 捻り零の Frobenius の周囲の局所化への像。 |
| `projectiveHomogeneousChartLinearEquiv_frobenius` | 加群のチャートの Frobenius は、実際の斉次局所化の p 乗に一致する。 |
| `projectiveProjNativeChart_frobenius` | 分数の比較を実際の標準開の切断へ移しても Frobenius は p 乗に一致する。 |
| `gradedOriginalProjCechOpen` | scalar の指定の前の、元の Proj の標準開。 |
| `gradedOriginalProjCechOpen_intersection` | 元の Proj の標準開の交叉は、変数の像の積での標準開。 |
| `gradedOriginalProjCechSectionLinearEquiv` | carrier の正規化前の実際の標準開へ、非空交叉の係数を移す線形同型。 |
| `gradedOriginalProjCechSectionLinearEquiv_naturality` | carrier の正規化前の切断への比較は、標準開を狭める射に自然。 |
| `gradedOriginalProjNativeCechComplexIso` | 共通の係数環上の標準開計算と、元の Proj の Čech 複体の同型。 |
| `gradedOriginalProjCoefficientScalarIso` | 段の基底環での構造層の係数を制限すると、共通の基底環での係数と自然に同型。 |
| `gradedOriginalProjCechScalarRestrictionIso` | 段ごとの基底環の制限と、同じ実際の Proj の Čech 複体の比較。 |
| `gradedOriginalProjRingMapSections_of_eq` | 同じ値の指定された分母を使う、標準開の構造層の引き戻しの自然性。 |
| `gradedOriginalProjRingMapSections_apply` | 元の grading を使う実際の切断への、斉次分数ごとの自然性。 |
| `gradedOriginalProjScalarNaturality_fraction` | 基底環のスカラーの斉次分数は、実際の係数環の写像で保たれる。 |
| `gradedOriginalScalarToGlobalSections_naturality` | Proj の引き戻しは、元の基底環の大域スカラーを保つ。 |
| `schemeStructureCechNativeTensorComplexIso` | 実際のアフィン被覆の逆像の Čech 複体と、元の Čech 複体のテンソル積の同型。 |
| `schemeStructureCechNativeTensorComplexIso_unit_apply` | 複体の比較は、1 と元の cochain の純テンソルを実際の切断の引き戻しへ送る。 |
| `schemeStructureCechNativeFlatBaseChangeIso` | 実際の底変換の構造層の Čech H と、flat なテンソル積の比較。 |
| `gradedOriginalScalarRingMap` | 異なる carrier の次数付き環の射を、共通の基底環の部分加群の次数の射に移す。 |
| `gradedScalarAwayIso_map` | 共通基底への正規化と、実際の斉次局所化の射は可換。 |
| `gradedOriginalScalarRingMap_denominator` | 元の grading の射は、標準開の分母を同じ変数の像の積へ送る。 |
| `gradedOriginalScalarRingMap_powers` | 元の grading の射で標準開の分母の冪を移す包含。 |
| `gradedOriginalChartLinearEquiv_map` | 共通基底の加群でのチャートの射を、元の grading の斉次局所化の射へ戻す。 |
| `schemeStructureCommonAffineCechCoefficient_naturality` | 二つのスカラー作用の間の実際の係数の射に対する、被覆比較の自然性。 |
| `schemeStructureCommonAffineCechFrobenius_naturality` | 実際の構造層の Frobenius は、共通アフィン細分による被覆比較と可換。 |
| `gradedOriginalProjCech_preimageOpen` | 元の grading の Proj の射は、同じ変数の標準開を引き戻す。 |
| `gradedOriginalProjNativeCechMap` | 元の二つの grading の間の、実際の構造層の Čech の引き戻し。 |
| `gradedOriginalProjCech_intersection_le` | 元の grading の標準開の交叉を引き戻す包含。 |
| `gradedOriginalProjNativeCechMap_apply` | 共通基底上での元の Proj の Čech の射は、実際の appLE の引き戻し。 |
| `gradedOriginalProjNativeCechComplexIso_apply` | 共通基底の加群の複体と元の Proj の切断の比較を、タプルごとに計算する。 |
| `gradedOriginalProjNativeCechSection_map` | 標準開上の分数の比較は、交叉の実際の切断への引き戻しに自然。 |
| `gradedOriginalProjNativeCechComplexIso_naturality` | 次数零加群の Čech の射は、実際の構造層の Čech の引き戻しと一致する。 |
| `gradedOriginalChartLinearEquiv_frobenius` | 共通基底のチャートの Frobenius は、元の grading の斉次局所化の p 乗と一致。 |
| `gradedOriginalProjNativeChart_frobenius` | 共通基底での計算を元の Proj の切断へ戻しても、Frobenius は実際の p 乗。 |

段 2e の検証済み実測：**311 本・30,697 行**、入口を含め **31,014 行**。上限 50,000 行内。未検証の下書きを含めない。


## 11-12 夜：各有限段も元の Proj とする filtered 比較（08a716c57）

数学コミット `08a716c57`。3 本・9 宣言・185 行、入口登録を含め 188 行。
対象と直接 importer のビルドは **4,520 jobs 成功**。別実行の監査は **8,409 宣言、標準三公理のみ**。
共有鍵 `--wait 3600` は実行ごとに返却。既存の宣言の変更、sorry・admit・新規公理・計算量上限の追加なし。

`gradedOriginalProjNativeCechDiagram` は各段の元の Proj の実際の構造層を使う。
`gradedOriginalProjNativeCechDiagram_map` は、その遷移が元の grading の Proj の実際の引き戻しであることを示す。
`gradedOriginalProjNativeFilteredHomologyIso` は、極限先と各段の**両方**で元の Proj の実際の Čech H を使う余極限比較。
模型・環の余極限・次数の照合は 2g が供給する入力であり、比較の同型性そのものを仮定していない。
各段の元の基底環での H へは、前の `gradedOriginalProjCechScalarRestrictionIso` と係数制限の完全性で接続する。

**停止点 2e ではない。** I 進の実際の閉厚化・互換族への接続と、五つの比較同士の自然性の最終照合を続ける。

| 宣言 | 主張 |
| --- | --- |
| `cechDiagramTransport` | 各段の同型に沿って、図式の遷移を移す。 |
| `cechDiagramTransportIso` | 各段の同型は、移した遷移も含めた図式全体の自然同型。 |
| `gradedOriginalRingDiagramModule` | 次数付き環の図式を、共通の多項式環上の加群の図式として扱う。 |
| `gradedOriginalRingDiagramMap` | 元の各段の grading の、環の遷移に沿う次数付き環の射。 |
| `gradedOriginalRingChartDiagram` | 共通基底上の次数零チャートの、遷移を含めた係数図式。 |
| `gradedOriginalProjNativeCechDiagram` | 各段で元の Proj の構造層を使う、実際の Čech 複体の図式。 |
| `gradedOriginalProjNativeCechDiagramIso` | 各段だけでなく、図式全体での次数零チャートと元の Proj の自然同型。 |
| `gradedOriginalProjNativeCechDiagram_map` | 移した図式の遷移は、元の Proj の実際の構造層の引き戻しそのもの。 |
| `gradedOriginalProjNativeFilteredHomologyIso` | 各段と極限先の両方で、元の Proj の実際の構造層を使う filtered Čech H の比較。 |

段 2e の検証済み実測：**314 本・30,882 行**、入口を含め **31,202 行**。上限 50,000 行内。


## 11-12 夜：閉厚化の実際の切断の商表示（c95341d13）

数学コミット `c95341d13`。5 本・12 宣言・284 行、登録を含め 289 行。
対象と直接 importer のビルドは **4,525 jobs 成功**。別実行の監査は **8,423 宣言、標準三公理のみ**。
共有鍵 `--wait 3600` は実行中だけ取得して返した。既存の宣言の変更、sorry・admit・新規公理・計算量上限の追加なし。

実際の Cartesian な閉厚化のアフィン切断は、元の切断環の拡大イデアルによる商と同型であり、
商への射影は構造層の実際の引き戻しと一致する。全射性と核の拡大イデアルへの一致も示した。
Rees 側では、IⁿM の各次数の像を Iⁿ 倍と同定し、分子のイデアル倍の局所化と、局所化後の成分のイデアル倍が一致することを示した。
**非 flat な商に flat 底変換の H の比較を使っていない。**

**停止点 2e ではない。** 両側の核が一致することから Rees の商の係数図式を実際の閉厚化の切断へ移し、
I 進遷移・互換族・既存の形式関数の同型をつなぐ部分と、五つの比較の自然性の最終照合が残る。

| 宣言 | 主張 |
| --- | --- |
| `projectiveIdealGradeProjection_mem` | イデアル倍の元を次数 d に射影すると、次数 d の成分のイデアル倍に入る。 |
| `projectiveHomogeneous_mem_ideal_smul_iff` | 斉次元が全体のイデアル倍に入ることと、同じ次数成分のイデアル倍に入ることは同値。 |
| `reesAdicProjectiveSubmodule_eq_ideal_smul` | 拡大イデアルで書いた Rees の部分加群は、元の Iⁿ 倍の部分加群そのもの。 |
| `projectiveGradedFraction_ideal_range` | 指数を固定した分数のイデアル倍の像は、元の像のイデアル倍。 |
| `projectiveGradedAway_ideal_smul` | 分子の各成分のイデアル倍を局所化すると、局所化の指定成分のイデアル倍になる。 |
| `reesAdicProjectivePiece_image_eq_ideal_smul` | Rees の IⁿM の自然数次数 d の像は、元の d 成分の Iⁿ 倍。 |
| `reesAdicProjectiveIntPiece_image_eq_ideal_smul` | 整数への零延長後も、Rees の次数成分の像は同じ Iⁿ 倍。 |
| `projectiveGradedAwayMap_range_ideal` | 分子ごとの像の等式は、斉次局所化の像を元の指定成分のイデアル倍にする。 |
| `schemeAffineClosedBaseChangeSectionIso` | 実際の閉厚化のアフィン切断は、元の切断の拡大イデアルによる商。 |
| `schemeAffineClosedBaseChangeSectionIso_projection` | 元の切断から商へ射影する写像は、実際の閉厚化への引き戻し。 |
| `schemeAffineClosedBaseChangeSections_surjective` | 実際の閉厚化のアフィン切断への引き戻しは全射。 |
| `schemeAffineClosedBaseChangeSections_ker` | 実際の閉厚化へのアフィン切断の射の核は、元の切断での拡大イデアル。 |

段 2e の検証済み実測：**319 本・31,166 行**、入口を含め **31,491 行**。上限 50,000 行内。


## 11-12 夜：Rees の標準開の核と商（c0fb175e4）

数学コミット `c0fb175e4`。3 本・8 宣言・223 行、登録を含め 226 行。
対象と直接 importer のビルドは **4,528 jobs 成功**。別実行の監査は **8,453 宣言、標準三公理のみ**。
共有鍵 `--wait 3600` は実行中だけ取得。既存の宣言の変更、sorry・admit・新規公理・計算量上限の追加なし。

各標準開の指定次数の部分で、Rees の閉厚化の射影の全射性と完全性を取り出した。
IⁿM の包含の像は元の成分の Iⁿ 倍であり、閉厚化への射影の核も同じ Iⁿ 倍。
`reesAdicProjectiveClosedChartQuotientIso` は元の係数の Iⁿ 倍による商から Rees の商の標準開への同型で、元の射影と可換。
非 flat なコホモロジーの底変換は使わず、係数ごとの商の比較を供給する。

**停止点 2e ではない。** 実際の閉厚化の切断との係数の自然同型、I 進遷移と互換族、形式関数への接続と五つの比較の最終照合を続ける。

| 宣言 | 主張 |
| --- | --- |
| `projectiveNatChartMap_surjective` | 次数ごとに全射な加群の射は、各標準開の指定次数部分へも全射。 |
| `projectiveNatChartMap_exact` | 次数を保つ完全列は、各標準開の指定次数部分でも完全。 |
| `reesAdicProjectiveChartInclusion_range_ideal` | IⁿM から元の標準開の次数 d 成分への写像の像は、同じ成分の Iⁿ 倍。 |
| `reesAdicProjectiveClosedChart_exact` | Rees の閉厚化の列は、各標準開の指定次数部分でも完全。 |
| `reesAdicProjectiveClosedChartProjection_surjective` | 閉厚化への射影は、各標準開の指定次数部分へ全射。 |
| `reesAdicProjectiveClosedChartProjection_ker` | 閉厚化への指定次数の標準開の射の核は、元の成分の Iⁿ 倍。 |
| `reesAdicProjectiveClosedChartQuotientIso` | Rees の閉厚化の標準開は、元の標準開の指定次数成分の Iⁿ 倍による商。 |
| `reesAdicProjectiveClosedChartQuotientIso_mk` | 商の同型は、元の標準開の成分を元の Rees の射影で送る。 |

段 2e の検証済み実測：**322 本・31,389 行**、入口を含め **31,717 行**。上限 50,000 行内。


## 11-12 夜：共通の核からの係数比較（688d39921）

数学コミット `688d39921`。3 本・7 宣言・135 行、登録を含め 138 行。
対象と直接 importer のビルドは **4,531 jobs 成功**。別実行の監査は **8,474 宣言、標準三公理のみ**。
共有鍵 `--wait 3600` は実行中だけ取得。既存の宣言の変更、sorry・admit・新規公理・計算量上限の追加なし。

同じ核を持つ二つの全射を、元の加群の射影と可換な形で比較する。
元の次数零加群から Proj の実際の非空交叉の切断への比較を係数ごとの線形同型として取り出し、制限への自然性を示した。
指定した大域スカラーと構造射で束ねた切断代数の比較は、元そのものを変えない。
**停止点 2e ではない。** 実際の閉厚化への係数写像の核を照合し、Čech 複体・I 進遷移・互換族・形式関数へつなぐ部分を続ける。

| 宣言 | 主張 |
| --- | --- |
| `cechQuotientComparison` | 同じ核を持つ二つの全射の、共通の元の加群から定まる比較。 |
| `cechQuotientComparison_projection` | 商の比較は、元の加群からの二つの射影と可換。 |
| `schemeScalarMorphismSectionModuleEquiv` | 指定した大域スカラーと、それが定める構造射で束ねた切断代数の加群の同型。 |
| `schemeScalarMorphismSectionModuleEquiv_apply` | スカラーを指定した切断の比較は、元そのものを変えない。 |
| `projectiveProjNativeNatCechSectionEquiv` | 次数零加群で計算した標準開の非空交叉と、実際の切断の線形同型。 |
| `projectiveProjNativeNatCechSectionEquiv_naturality` | 元の次数零加群から実際の切断への比較は、非空交叉の制限に自然。 |
| `projectiveProjCechOpenIntersection_isAffineOpen` | 標準開の非空交叉は実際の Proj のアフィン開。 |

段 2e の検証済み実測：**325 本・31,524 行**、入口を含め **31,855 行**。上限 50,000 行内。


## 11-12 夜：実際の閉厚化の Čech 複体・H への接続（863487464）

数学コミット `863487464`。3 本・14 宣言・327 行、登録を含め 330 行。
対象と直接 importer のビルドは **4,534 jobs 成功**。別実行の監査は **8,520 宣言、標準三公理のみ**。
共有鍵 `--wait 3600` は実行中だけ取得。既存の宣言の変更、sorry・admit・新規公理・計算量上限の追加なし。

実際の Cartesian な閉厚化への、元の次数零加群からの係数写像について、制限への自然性・全射性と核が J 倍であることを示した。
Rees の射影と同じ核を使って非空交叉ごとの canonical な係数同型を作り、制限に自然であることを示した。
`reesAdicNativeClosedCechComplexIso` と `reesAdicNativeClosedCechHomologyIso` は、Rees の商の計算を**実際の閉厚化の構造層の Čech 複体・H**へ接続する。
`reesAdicNativeClosedPushedComplexIso_projection` により、元の係数からの Rees の射影は、元の Proj の切断を実際に引き戻す Čech の射に一致する。
空交叉の同型も、非 flat な H とテンソル積の交換も仮定していない。

**停止点 2e ではない。** 厚化間の実際の遷移との可換性と、I 進互換族・形式関数への接続、五つの比較の最終照合を続ける。

| 宣言 | 主張 |
| --- | --- |
| `projectiveProjPullbackCechPresheaf` | 元の基底のスカラーを実際に引き戻して、構造層の係数前層を作る。 |
| `projectiveProjClosedPullbackCoefficient` | 非空交叉の次数零加群の係数から、実際に引き戻した切断への線形写像。 |
| `projectiveProjClosedPullbackCoefficient_apply` | 係数の線形写像は、元の Proj の切断の実際の引き戻しそのもの。 |
| `projectiveProjClosedPullbackCoefficient_naturality` | 次数零加群から実際の切断への射は、非空交叉の制限に自然。 |
| `projectiveProjClosedPullbackCoefficient_surjective` | 閉厚化への係数の写像は、実際の切断へ全射。 |
| `projectiveProjClosedPullbackCoefficient_ker` | 閉厚化の実際の切断への係数の写像の核は、元の係数の J 倍。 |
| `reesAdicNativeClosedCoefficientIso` | 実際の閉厚化の切断と Rees の商の、非空交叉での canonical な係数同型。 |
| `reesAdicNativeClosedCoefficientIso_projection_apply` | 係数同型は、元の係数からの射影を実際の引き戻しへ送る。 |
| `reesAdicNativeClosedCoefficientIso_projection` | 非空交叉の同型は、元の係数からの射影と実際の引き戻しを同じ射にする。 |
| `reesAdicNativeClosedCoefficientIso_naturality` | 実際の閉厚化の切断への係数同型は、非空交叉の制限に自然。 |
| `reesAdicNativeClosedPushedComplexIso` | Rees の商の Čech 複体と、実際の切断を押し出した係数の複体との同型。 |
| `reesAdicNativeClosedCechComplexIso` | Rees の商の Čech 複体と、実際の閉厚化の逆像被覆の Čech 複体との同型。 |
| `reesAdicNativeClosedCechHomologyIso` | Rees の商の H と、実際の閉厚化の構造層の Čech H の比較。 |
| `reesAdicNativeClosedPushedComplexIso_projection` | 元の係数からの Rees の射影は、実際の切断を引き戻す Čech の射と一致する。 |

段 2e の検証済み実測：**328 本・31,851 行**、入口を含め **32,185 行**。上限 50,000 行内。


## 11-13 夜：停止点 2e（bf9767cdc）

停止点の正式報告は [scheme-w1-2e-report.md](scheme-w1-2e-report.md)、全モジュールと宣言の一行ずつの一覧は [scheme-w1-2e-declarations.md](scheme-w1-2e-declarations.md)。最後の束は 8 本・37 宣言・703 行（入口込み 711 行）。対象と直接 importer は 4,542 jobs 成功、別実行の監査は 8,615 宣言・標準三公理のみ。累計 336 本・32,554 行（入口込み 32,896 行）。五つの比較、Čech 版の範囲、最終出力の型と宇宙は正式報告に記録した。夜の指示どおり、取り込みを待たず 2f F0〜F3 へ進む。

| 宣言 | 主張 |
| --- | --- |
| `projectiveProjAdicScheme` | Proj の指定した大域スカラーに沿う実際の I 進閉厚化。 |
| `projectiveProjAdicProjection` | Proj の実際の閉厚化からの射。 |
| `projectiveProjAdicCechComplex` | 実際の I 進閉厚化の逆像被覆の構造層の Čech 複体。 |
| `projectiveProjAdicCechComplexIso` | Rees の商の Čech 複体と canonical な実際の閉厚化の Čech 複体の同型。 |
| `projectiveProjAdicCechTransition` | 実際の厚化間のスキームの射が誘導する Čech の遷移。 |
| `projectiveProjAdicCechHomology` | 実際の閉厚化の標準開被覆による Čech コホモロジー。 |
| `projectiveProjAdicCechHomologyTransition` | 実際の厚化間の射が誘導する Čech コホモロジーの遷移。 |
| `projectiveProjAdicCechHomologyProjection` | 元の構造層から実際の閉厚化への Čech コホモロジーの射影。 |
| `projectiveProjSourceCechHomology` | 元の Proj の構造層の標準開 Čech コホモロジー。 |
| `projectiveProjSourceCechHomologyIso` | 元の Proj の標準開被覆の Čech H と、次数零の計算の同型。 |
| `projectiveProjAdicCechHomologyIso` | 実際の閉厚化の Čech H と、Rees の商による計算の同型。 |
| `projectiveProjAdicCechHomologyIso_transition` | 閉厚化の Čech H の比較は I 進遷移と可換。 |
| `projectiveProjAdicCechHomologyIso_projection` | 閉厚化の Čech H の比較は、元の構造層からの射影と可換。 |
| `projectiveProjAdicCechFamilies` | 実際の閉厚化の Čech コホモロジーの互換族。 |
| `projectiveProjAdicCechFamiliesEquiv` | Rees の商の互換族と、実際の閉厚化の Čech 互換族の線形同型。 |
| `projectiveProjAdicCechProjection` | 元の Proj の構造層の Čech 複体から、実際の閉厚化への引き戻し。 |
| `projectiveProjAdicCechProjection_transition` | 実際の閉厚化への射影は、厚化間の実際の Čech 遷移と可換。 |
| `projectiveProjAdicCechComplexIso_projection` | Rees の射影を実際の閉厚化へ移す複体の比較は、元の射影と可換。 |
| `projectiveProjAdicCechComplexIso_transition` | Rees の商と実際の閉厚化の Čech 複体の比較は、I 進遷移に自然。 |
| `projectiveProjCechFormalFunctions` | 実際の Proj と閉厚化の構造層に対する Čech 版の形式関数の同型。 |
| `projectiveProjCechFormalFunctions_of_apply` | Čech 形式関数の同型は、元の切断のコホモロジーを実際の閉厚化へ制限する。 |
| `reesAdicNativeClosedCechComplexIso_projection` | Rees の射影と、実際の閉厚化への構造層の Čech の引き戻しとの一致。 |
| `reesAdicNativeClosedCechComplexIso_projection_refined` | 実際の引き戻しを恒等添字の細分として書いても、Rees の射影と一致する。 |
| `schemeAdicBaseChange` | 実際の Iⁿ による閉厚化。 |
| `schemeAdicBaseChangeProjection` | 閉厚化から元のスキームへの射。 |
| `schemeAdicBaseChangeStructure` | 閉厚化の商環上の構造射。 |
| `schemeAdicBaseChange_isPullback` | 定義した閉厚化は、実際に元の構造射の底変換。 |
| `schemeAdicBaseChangeTransition` | 小さい指数の閉厚化から大きい指数の閉厚化への canonical な射。 |
| `schemeAdicBaseChangeTransition_projection` | 閉厚化の遷移は、元のスキームへの射と可換。 |
| `schemeAdicBaseChangeTransition_structure` | 閉厚化の遷移は、基底の商環の射とも可換。 |
| `schemeAdicBaseChangeTransition_self` | 同じ指数の閉厚化の遷移は恒等射。 |
| `schemeAdicBaseChangeTransition_comp` | 閉厚化の遷移を二度合成すると、直接の遷移になる。 |
| `schemeStructureAffineCechPullback_comparison_naturality` | アフィン射の実際の引き戻しは、共通アフィン細分による Čech H の比較と可換。 |
| `schemeStructureCechPullbackMap_eq_refined` | 同じ逆像被覆への恒等細分を合成しても、実際の引き戻しは変わらない。 |
| `schemeStructureCechRefinedPullbackMap_comp` | 同じ添字で細分した、構造層の実際の引き戻しはスキームの射の合成と可換。 |
| `schemeStructureCechPullbackScalar_comp` | 共通の元のスカラーを合成して引き戻すと、各段で引き戻したスカラーの合成になる。 |
| `schemeStructureCechPreimage_refinement` | 共通の射への可換な三角形は、逆像被覆の細分を与える。 |
