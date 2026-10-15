# dg 理論（M5）の独立実装計画

作成・調査：2026-10-14。更新：2026-10-15。状態：U0〜U9 を実装・検証済み（U10は継続中）。
U0〜U3の記録は§11、U4/U5の実績と後続契約は§12。D0〜D10全体の完了ではない。
この計画だけを受け取る実装担当者向けの仕様である。
ホモトピー論の共有契約は [k-theory.md §123](k-theory.md#123-次段階の設計i抽象モデル圏とその当てはめ2026-10-14)。
以下のD0〜D10、ファイル配置、API案は、既存又は§11で実装済みと明記したもの以外は予定名。

対象は任意の可換環 `A : Type u_A`、小さいA線形dg圏Dとその**非有界**右dg加群。
環のnoetherian性・体・標数零・有限次元性は基本定義に課さない。
M5はSpectraをimportせず進める。M9の自由列・ランク商は当てはめ、M6がスペクトル側との合流点。
完了はdg商のperfect hullを既存Verdier商・Karoubi包絡へ、商への関手、中心作用、係数変更の
自然同型を伴って比較できること。ホモトピー圏の同値だけをM6向けのdgデータの代用にしない。

固定環境は Lean `v4.35.0-rc4`、Mathlib `e6bbacd0e1b7307ff6e17da09cd2455f60804fa6`。
Mathlibへの相対パスはすべて `.lake/packages/mathlib/Mathlib/` からのパス。
リポジトリへのパスは `SerrePositivity/` からのパス。
本調査ではこの固定版のソースを読んだ。将来のMathlib masterにあるという推測は採用しない。

## 1. 現状との差分と再利用入口

「未確認」はHomology・Enriched・ModelCategoryとリポジトリの対応するファイルを検索した範囲で
対応APIを確認できなかった意味。実装単位の冒頭に再探索する。

固定版ソースの主要な入口：
[HomComplex](https://github.com/leanprover-community/mathlib4/blob/e6bbacd0e1b7307ff6e17da09cd2455f60804fa6/Mathlib/Algebra/Homology/HomotopyCategory/HomComplex.lean)、
[Monoidal](https://github.com/leanprover-community/mathlib4/blob/e6bbacd0e1b7307ff6e17da09cd2455f60804fa6/Mathlib/Algebra/Homology/Monoidal.lean)、
[Enriched](https://github.com/leanprover-community/mathlib4/blob/e6bbacd0e1b7307ff6e17da09cd2455f60804fa6/Mathlib/CategoryTheory/Enriched/Basic.lean)、
[DerivedCategory](https://github.com/leanprover-community/mathlib4/blob/e6bbacd0e1b7307ff6e17da09cd2455f60804fa6/Mathlib/Algebra/Homology/DerivedCategory/Basic.lean)、
[Injective model](https://github.com/leanprover-community/mathlib4/blob/e6bbacd0e1b7307ff6e17da09cd2455f60804fa6/Mathlib/Algebra/Homology/ModelCategory/Injective.lean)。

| M5の項目 | 固定版Mathlib・既存コードの根拠 | 新しく定義・証明するもの | 引用してよい比較（定義の代替にしない） |
| --- | --- | --- | --- |
| 複体・次数つきHom・微分 | `Algebra/Homology/HomotopyCategory/HomComplex.lean`：`CochainComplex.HomComplex.Cochain`, `Cochain.comp`, `δ`, `δ_δ`, `δ_comp`, `Cocycle.equivHom`, `Cochain.equivHomotopy`, `CochainComplex.linearHomComplex` | Hom複体の評価・合成をA複体の射に束ね、豊穣構造と閉構造へ接続 | 不要 |
| tensor・符号・閉構造 | `Algebra/Homology/Monoidal.lean`：`HomologicalComplex.tensorObj`, `tensorHom`, `monoidalCategory`。`TotalComplexSymmetry.lean`：`HomologicalComplex₂.totalFlipIso`。既存 `PerfectComplex/Tensor.lean`：`cochainTensor`, `cochainTensorι_d`、`TensorSymmetry.lean`：`cochainTensorSymmetry`, `ιTensorObj_cochainTensorSymmetry`, `cochainTensorSymmetry_hom_comp` | 任意非有界Ch(A)のtensor–linearHomComplex随伴、自然性、signed braiding/hexagonと必要な登録。既存の交換同型だけで全整合性が済んだとしない | 不要 |
| dg圏・閉次数零単位・Leibniz | `CategoryTheory/Enriched/Basic.lean`：`EnrichedCategory`, `eId`, `eComp`、`Ordinary/Basic.lean`：`EnrichedOrdinaryCategory`, `eHomEquiv`。dg専用定義は未確認 | Ch(A)豊穣としての入口、成分API、Z⁰(D)、H⁰(D)、dg algebraの一対象例・複体の例 | 不要 |
| dg関手・準同値 | `EnrichedFunctor.id`, `.comp`, `.forget`、`EnrichedNatTrans`は既存 | 各Hom準同型＋H⁰で本質的全射のpredicate、合成・不変性、restriction/extension | 準同値から導来加群圏への比較はDG-MORの明示した成分 |
| dg加群・Hom複体 | `Enriched/Opposite.lean`, `Enriched/FunctorCategory.lean`。`Enriched/Basic.lean`末尾は豊穣自然変換の**対象**の構成をTODOとしている | `Dᵒᵖ`からCh(A)への豊穣関手、次数つき線形変換のend、representable、Yoneda、free/forget、cone/shift、極限余極限 | 不要。通常の関手圏と同じ型とは扱わない |
| 加群の導来圏 | `HomotopyCategory`, `DerivedCategory`, `DerivedCategory.Q`, `Qh`, `Qh.IsLocalization`の準同型・acyclic.trW版（`DerivedCategory/Basic.lean`） | dg加群版K(D)、acyclic、objectwise quasiIso、局所化D(D)、三角構造、semifree resolutionと計算API | モデル比較は共有G1の証明。新しい一般局所化型は作らない |
| K射影・K単射・モデル | `HomotopyCategory/KProjective.lean`：`CochainComplex.IsKProjective`, `isKProjective_of_projective`、KInjective版。`DerivedCategory/KProjective.lean` / `KInjective.lean`：それぞれのnamespaceの`Qh_map_bijective`, `quasiIso_iff`。`ModelCategory/Injective.lean`のscoped `ModelCategory (CochainComplex.Plus C)` | dg加群のhomotopically projective/semifree、非有界Ch(A)の射影構造、dg加群への転送 | Tabuadaの**dg圏全体**のモデル存在はDG-TAB。dg加群のモデルとは別 |
| 導来tensor・K-flat | 既存 `HomologicalAlgebra/DerivedTensor.lean`：`derivedTensor`, `derivedTensor_homology_eq`は普通の加群二つのℕ鎖複体値。`DerivedTensorRealization.lean`：`realizedDerivedTensor`, `realizedDerivedTensorHomologyIso`はそのD(A)への実現（調査時未追跡の並行作業） | 非有界複体・dg bimoduleのcoend tensor、K-flat、両変数の置換比較、derived tensor、extension of scalars | 特殊な比較・Moritaのみ。既存の普通加群用tensorを一般dg tensorと呼び替えない |
| perfect・コンパクト | 既存 `PerfectComplex/HomotopyCategory.lean`：`strictlyPerfectComplex`, `perfectHomotopyProperty`, `PerfectHomotopy`、`PerfectComplex/K0*.lean`。通常の環の有限射影複体 | representableの有限shift/cone/retract閉包、finite cell、compactの宇宙付き定義、dg enhancement・小さい代表系、環の場合の既存perfectとの比較 | DG-PER：指定Dのperfect＝compact。任意三角圏のcompact生成定理のaxiomを共有層へ置かない |
| 生成元による表示 | 既存 `Asymptotic/FreeSequenceGenerator.lean`：`FreeSequence.exists_retract_generator_multiple`（`∀ n, 0 < s n`） | dg Yoneda、endomorphism dg algebraへのbimodule、perfect制限、生成仮定の具体的検証 | DG-GEN：指定enhancementと生成元に対する表示。H⁰の生成元からenhancementを復元したことにしない |
| Drinfeld商 | 固定版とプロジェクトにdg商の対象は未確認 | εのpath直和、微分、合成、対象を殺す関手、K-flat解像度版、pretriangulated hull | DG-DR：定義済み商とVerdier商の比較、適切なflatness仮定 |
| Morita | 一般の圏同値・局所化・導来随伴はある | bimoduleの導来合成、Morita predicate、identity/comp、perfect保存、準同値との区別 | DG-MOR：具体的bimoduleの比較判定 |
| Verdier/Karoubiへの比較 | `CategoryTheory/VerdierKaroubi.lean`：`karoubiNullEnvelope`, `karoubiVerdierOrderEquivalence`、`VerdierKaroubiLinear.lean`：A線形性。`Asymptotic/PaperRankQuotient.lean`：`PaperRankQuotient`, `paperRankEquivalence`, `paperSequenceComparison` | enhancementからH⁰/hull→既存圏への関手、三角性・A線形性・商への因子化、retractと中心作用・基底変更の比較 | DG-DR/DG-MORを入力にしてこの接続を証明 |

注意：`Injective.lean` はabelian・enough injectivesのCについて**下に有界**な`Plus C`。
非有界dg加群への適用も、monoidal性もそこからは得られない。
K射影/K単射のpredicateと既存計算定理の存在は、全非有界対象の解像度の存在を意味しない。
`DerivedCategory (ModuleCat A)` と `D(D)` を区別する。dg加群圏をそのままabelian圏と見て
`DerivedCategory`を適用すると「dg加群の複体」という別の二重複体問題になる。

## 2. 主モデルと次数・合成の規約

推奨は **(i) `EnrichedCategory (CochainComplex (ModuleCat A) ℤ) D`**。
Mathlibの型を主データとし、利用者には次数つきHom・微分・通常のdg合成の成分APIを提供する。
宇宙はAの`u_A`、Dの対象の`u_obj`、Hom加群の`u_hom`を契約に記録し、
path直和・加群全体・局所化・小さいperfect代表系で必要なmax/successorを別々に明示する。
最初は必要な宇宙をmaxへ持ち上げる方法を許すが、Homのsmallnessが自動で保たれるとはしない。

| 案 | 利点 | 不足・費用 | 採用方法 |
| --- | --- | --- | --- |
| (i) 複体豊穣 | 単位・結合・関手が既存Enriched上に載る。tensor、opposite、共有G6と接続できる。複体の定義を再実装しない | Ch(A)の閉構造、線形Hom、豊穣自然変換のendが追加作業。Enrichedの合成順と通常dg合成の符号比較が必要 | 主モデル。D0で符号比較を先に固定、D1で成分constructor/accessorを整備 |
| (ii) 次数Hom＋微分を直接保持 | path商や符号計算を書きやすく、Homのelement APIが直接得られる | d²・結合・単位・Leibniz、豊穣との比較を二重に維持。Mathlib置換時の負担と別モデル間のtransport | 独立した公開dg圏型にはしない。D1の入力constructorの補助データとして使い、主モデルへの変換を証明 |

`Ch(A) = CochainComplex (ModuleCat A) ℤ`、dの次数は+1。
通常のdg合成は `μ(g,f)=g∘f`、`|g|=q`, `|f|=p` とし、
`d(g∘f)=dg∘f + (-1)^q g∘df`。単位は次数0のcocycle。
Hom複体の微分は `d(f)=d_Y f - (-1)^p f d_X`。
Mathlib `HomComplex.δ_comp` は先にf、次にgの`Cochain.comp`に対してこの規則を表している。

**順序のゲート**：Mathlib `EnrichedCategory.comp` の源はHom(X,Y)⊗Hom(Y,Z)。
通常のμの源はHom(Y,Z)⊗Hom(X,Y)なので、signed braidingを介して
`eComp(f⊗g)=(-1)^(pq) μ(g,f)`とする（普通の次数0射では符号は1）。
無符号の`Cochain.comp`をそのまま前向きtensorのchain mapに束ねるとLeibnizと合わない。
D0/D1でbraiding・合成順・結合則・通常射との一致を証明する。
dg opposite・右加群の作用・bimoduleにもこの比較を一貫して使う。

通常の圏 `Z⁰(D)` のHomは閉次数0の射、`H⁰(D)`はその境界による商。
`ForgetEnrichment`はZ⁰の入口に使えるが、H⁰を返すものとは扱わない。
準同値は各HomのquasiIsoとH⁰の本質的全射。Morita同値は導来加群圏上の条件で別predicate。
M9のεは次数−1、`d ε = id`。次数0からのpath商は非正次数。
原論文のホモロジー次数は `i ↦ -i` で、非負＝connectiveの向きを固定する。
任意dg圏のHomが非正次数であるとは仮定しない。

## 3. 導来圏の作り方と推奨経路

**先行する主経路は局所化、後で射影モデルと比較する。**
dg加群の対象を定義した後、W_Dを各対象xでquasiIsoとなる射として定義し、
`MorphismProperty.Localization` / `HasLocalization`を使用する。
dg加群のホモトピー圏K(D)のacyclic対象のVerdier商との比較を証明する。
これはM5内部の計算・比較の構成法であり、全体のホモトピー論の基底はMathlib ModelCategoryのまま。

| 方法 | 依存・長所 | 追加作業・制限 | 判断 |
| --- | --- | --- | --- |
| W_D局所化＋K(D)/Acyc | 既存の局所化の普遍性、cone/shift、Verdier API。G4/G8も転送の完成も待たず進める | 局所化の定義だけでは計算できない。semifree resolution・Hom計算・三角構造・局所小性と余積を証明する | D4の主経路 |
| 非有界Ch(A)の射影モデル→dg加群転送 | W=quasiIso、Fib=degreewise epi、Cof=llp(trivial Fib)。free_x(S^n→D^n)、free_x(0→D^n)で生成。cofibrant置換でtensorを計算 | G2/G5と具体的smallness/acyclicity。Hom_DがA上cofibrantでない場合も検証する。pointwise cofibrancyだけでdg-cofibrancyとはしない | D4mの後続比較。存在は共有認識定理＋M5の具体的証明 |
| 単射モデル | bounded-belowについては固定版API、unbounded injectiveは別構成が必要 | dg加群・非有界版の存在が不足。tensorは普通Quillen bifunctorにならないので導来tensorの入口に不向き | 初期主経路には採らない。必要な右導来Hom用に後から追加 |

dg加群Hom複体がacyclicを消すことをhomotopically projectiveの定義とし、
semifreeがこの条件を満たすこと、各加群にsemifree準同型があることを証明する。
最初からMathlibの「普通の複体のIsKProjective」と同じinstanceにはしない。
一対象D=Aの比較で、Mathlib `DerivedCategory (ModuleCat A)` とQ/Qhへの自然同型を公開する。
D4mでは同じW_Dの局所化を使うため、モデル由来HoとD(D)の同値を普遍性で得る。
置換の選択独立性とtensor・restriction・extensionとの両立までを受入条件とする。

K-flatはA上のacyclic複体をtensorでacyclicに送る性質と、D上の相対tensor版を区別する。
semifree dg加群が相対的に良いことから**A上**K-flatを得るには、Hom_DのA上K-flat等の条件が必要。
M9で使う「次数ごとflatかつコチェインで上に有界 ⇒ K-flat」はD5の証明対象。
非正次数の複体は上に有界なので適用できる。任意非有界なdegreewise flat複体へ拡張しない。

## 4. 共有一般論との分担と引継ぎ契約

G番号はk-theory.md §123.3と同一。共有の証明は(I)系列が所有し、M5に複製しない。
共有成果を待つD4m以外の定義・局所化・path構成はM5だけで進められる。

| 共有成果 | 所有者・時期 | M5が渡すもの／使うもの | 待つ段階 |
| --- | --- | --- | --- |
| G0 宇宙・scope・台帳 | (I) H0、M5 D0で同じ契約を確認 | Ch(A)、対象族、path集合、加群圏・局所化の宇宙。代替ModelCategory型なし | 全段階の仕様のみ |
| G1 Quillen・導来随伴 | (I) H1/H4 | M5はfree/forget・restriction/extension・tensor随伴と保存条件を渡す。共有側は既存derivability/`Adjunction.derived`へ接続 | D4m・D5のモデル比較。D4の局所化構成は待たない |
| G2 生成・小対象・転送 | (I) H3、G1の初期後 | M5はsphere/disk、free_x、smallnessの加群的証拠、free(J)-cellのquasiIsoを渡す。共有側は一般認識定理・関手的分解 | D4m |
| G3 projective/injective/Reedy図式 | (I)、G2の後 | underlying familyは離散対象族の通常関手圏。dg加群は豊穣関手なので、多対象転送を用いる | 通常図式比較で利用可。D3/D4の必須依存ではない |
| G5 monoidal model・monoid axiom・多対象加群転送 | (I)、G2から。G4と独立 | M5はCh(A)のpushout-product・unit・monoid axiomの具体的検証、tensor/coendと多対象作用を供給。一般closure・転送の論理は(I) | D4m、D5のQuillen比較 |
| G6 豊穣tensor/cotensor・SM7 | (I) H5以降 | 任意Vの表現性・pullback-hom同値は共有。Ch(A)の閉構造・signed braiding・dg HomのendはM5 D0/D3 | 後続の豊穣モデル比較。dg定義自体にSM7を要求しない |
| G4 Bousfield / G7 stable / G8 spectra | (I)後半 | M5は安定スペクトル、有理化、hGを作らない。M6で必要な比較を受け取る | M5・M9のdg部分に依存なし |

予定配置は `DifferentialGraded/Complexes/`, `Category/`, `Functor/`, `Module/`,
`Derived/`, `Tensor/`, `Perfect/`, `Quotient/`, `Morita/`, `Comparison/`。
具体的M9は `Paper/Section4/` 側の新規ファイル、引用は
`Inputs/DifferentialGraded/` に所有者・台帳IDを付ける。
一般の圏論補題は必要なら `CategoryTheory/Enriched/`、モデル一般論は `HomotopicalAlgebra/`。
Monoidalへの追加前に [shared-foundations-arxiv.md](shared-foundations-arxiv.md) を読む。
今回の範囲では括弧規約の統一・移植・共有パッケージ化を行わない。

## 5. 段階・依存関係・受入条件

各段階の終了時に、対象と主要法則、具体例、比較図式を一緒に検証する。
引用のない一般論をsorryで通して次へ進めない。引用は§7の採用ゲートを通した当てはめに限定。

| 段階 | 依存 | 成果物と受入条件 |
| --- | --- | --- |
| D0 複体と規約 | G0契約、固定版のtensor/Hom | Ch(A)、degree convention、unit、linearHomComplex。tensor/Hom随伴・signed compositionのchain map・結合/単位、必要なbraiding整合性。任意CommRing A、非有界複体で型が通る。既存Tensor APIとの比較、環を体に限定しない |
| D1 dg圏 | D0の合成/単位部分 | Enriched主モデル、成分constructor、Z⁰/H⁰、one-object dg algebra、普通A線形圏の次数0化、Ch(A)の豊穣化。閉次数0の単位・Leibniz・結合を証明。Z⁰の普通射と既存chain mapの一致 |
| D2 dg関手・準同値 | D1 | EnrichedFunctor入口、H⁰ functor、quasiEquivalence、identity/comp、opposite。HomのquasiIsoとH⁰本質的全射を独立にテスト。自然変換・符号の規約を維持 |
| D3 dg加群 | D0〜D2 | 右/左加群、bimodule、Homのend、dg Yoneda、representable/free_xと評価の随伴。shift・cone・homotopy、極限余極限。`D=A`と普通A複体の比較。objectwise quasiIsoのMorphismProperty、2-out-of-3/retract。G2へ生成射・cell計算の仕様を引き渡す |
| D4 導来圏（先行） | D3 | K(D)、acyclic.trWとW_D局所化の比較、D(D)、三角構造、semifree解像度、Hom計算、coproduct・局所小性の宇宙。`D=A`の既存DerivedCategoryとの自然同値。局所化の存在だけで完了としない |
| D4m 射影モデル比較 | D3/D4、G1/G2/G5 | 非有界Ch(A)とdg加群のMathlib ModelCategory、objectwise W/Fib、cofibrancyの正確な条件、Ho≃D(D)。D4の解像度とcofibrant置換の比較、導来随伴のunit/counitが一致。G4/G8は不要 |
| D5 tensor・K-flat | D3/D4、D0の閉構造 | coend/balanced tensor、導来tensor、K-flat・semifreeの条件付きflatness、associativity/unit、両変数・係数変更の自然性。上に有界flat⇒K-flat、任意Tへのunderived/derived比較の仮定を明示。モデル比較のみG1/G5/D4m待ち |
| D6 perfect・compact | D4/D5 | finite cellとrepresentableの有限三角閉包・retract、Perf(D)とdg enhancement（homotopically projectiveな代表）、小さい代表系。compactの宇宙を固定、perfect⇒compactと逆向きの証明又はDG-PER適用。通常Aの既存PerfectHomotopyへの比較がshift/cone/retractを保存 |
| D7 生成元表示 | D5/D6 | 指定dg生成元EのEnd(E)、Yoneda/bimodule、Perf制限の同値。生成性・compact性・Hom quasiIsoを証明してDG-GEN/DG-MORを適用。一般の生成集合と一生成元を区別し、無限直和を勝手にcompactとしない |
| D8 dg商 | D1〜D5（対象構成はD1後から先行可） | full dg subcategory B、ε_b、有限pathの直和、d²、単位/結合、contracting homotopy付き関手への厳密普遍性。flatnessのないDはK-flat resolution版を用意。pretriangulated hullとDG-DRの仮定・結論を接続。path式のstrict scalar extension比較を証明 |
| D9 Morita | D5〜D8 | derived bimodule compositionとunit、Morita同値のidentity/comp、準同値⇒Morita、Perf functorの自然性。DG-MOR判定の各仮定を具体的Homで検証。三角圏同値だけからdg Moritaを結論しない |
| D10 Verdier/Karoubi比較 | D6/D8/D9、既存VerdierKaroubi* | `H⁰(Perf_dg(D/B)) ≃ Karoubi(tria(D)/tria(B))`の正確なnull部分を固定（Bの像の三角閉包）。商への関手とYonedaの四角形、shift/三角形、A線形性、retract、中心作用・scalar extensionの自然同型。M9のPaperRankQuotient・支持圏への具体的比較入口まで公開 |

`tria(D)`はDのrepresentableからshift/coneで作るpretriangulated hullのH⁰。
一般のH⁰(D)は三角圏ではないので `H⁰(D)/H⁰(B)` を無条件にVerdier商とは書かない。
D10のKaroubi前後の順序交換には既存`karoubiVerdierOrderEquivalence`を用い、
対象を殺す部分圏がどちらの順序でも対応することを証明する。

依存の主線は `D0 → D1 → D2 → D3 → D4 → D5 → D6 → D7`。
D8のpath定義はD1から先行可能、比較はD4/D5/D6を待つ。
`D8 + D9 + D6 → D10`、`G1/G2/G5 + D3/D4 → D4m` は別の合流点。
全M5を待たず、D1/D3/D5/D8と既存自由列からM9の次数・path・基底変更を先行できる。

## 6. M9の10項目からの逆算

以下の具体的構成はM5の一般ファイルに入れない。環S、列s、群G、支持パラメータを当てはめで固定。

| M9 | 利用するM5成果 | 既存入力・追加する当てはめ／残る不足 |
| --- | --- | --- |
| 1 E_Sの加法的生成性 | D1の次数0化、D3 Yoneda、D7 | `FreeSequence.exists_retract_generator_multiple`を使う。`∀ n, 0 < s n`、ランクの一様比較と有限multipleを明示。retractの既存結果からdg生成仮定への接続が未実装 |
| 2 B_S=∏ M_{s_n}(S) | D1 one-object、D7/D9 | E_Sのendomorphism ringと無限積の環同型を具体的に証明。商前の有限complex/retract圏とPerf(B_S)の同値。B_Sをdg基盤の定義に埋め込まない |
| 3 flatness・無限積tensor | D0/D5への入力 | 無限積のA平坦性には環・Sの仮定を原論文と照合（一般のflat加群の積は自動でflatではない）。有限表示T等の必要な仮定を切り分け、Homの積とtensor比較を別証明。有限`TensorProduct.piRight`では不足 |
| 4 小ランクのidを殺す | D1/D8 | full subcategory Bを小ランク条件で定義。ε_bとpath表示を使用。既存rank nullとの対応はD10の当てはめ |
| 5 非正次数・connective | D0規約、D8 path | 元のHomは次数0、εは−1。path長rの次数−rを証明し、H^i=0 (i>0)。スペクトルのπ_iとの対応はM6/Shipleyを待つ |
| 6 HのK-flatと導来tensor | D5/D8 | path項のflat、直和・有限tensorのflatをM9(3)から証明し、上に有界flat⇒K-flatを適用。これで任意TについてH⊗_A Tの導来比較を得る。TのA平坦性を追加しない |
| 7 T側へのpath係数変更 | D5 scalar extension、D8 | pathの添字と直和/tensorの比較はstrict構成で証明。D_TのHom比較と小ランク部分の対応は別条件。T上のflatnessを再検証しDG-DR適用。TのA平坦性から代用しない |
| 8 perfect hull≃𝒫_S | D6〜D10 | `PaperRankQuotient`, `paperRankEquivalence`, `paperSequenceComparison`, `karoubiVerdierOrderEquivalence`へ接続。pretriangulated hull→有限自由列complexの比較、nullの一致とKaroubi順序比較が不足 |
| 9 中心局所化・支持 | D5/D6/D10＋中心作用API | `CategoryTheory/KaroubiScalarSupport.lean`, `Asymptotic/SupportedRank*.lean`の支持圏へ接続。central localizationのdg bimodule、compact性からパラメータ冪の零作用、商後のretractでの支持対応を証明。一般Tに一様支持代表元を要求しない |
| 10 Gひねり・係数変更 | D2/D5/D10の自然性 | Gのstrict作用、T因子の自己同型、composition/unit、既存changeRing/twistとの自然同型を証明。既存 `rankQuotientChangeRing_fac`, `supportedRankChangeRingFactors`との四角形。hGはM4の別成果 |

M5だけでは埋まらないのは、(3)の具体的可換環論、(8)(9)(10)の既存ランク・支持・群作用との接続、
(5)のスペクトル次数への翻訳。これらを一般dg理論の引用の仮定へ隠さない。
M9のdg表示の大半はD10までのM5＋既存コードで進められるが、本文のK理論の主張はM6が必要。

## 7. 引用候補台帳（型の案・採用ゲート）

今回axiomは追加しない。一般のモデル圏論G1〜G8にも引用を入れない。
下記は当てはめの `Inputs/DifferentialGraded/` に置く候補で、使用時にA、D、B、宇宙、
対象・射のクラス・関手を具体的に固定した名前つき定理へ専門化する。
引用対象の定義・path・Perf・bimoduleをまず作る。一般の存在定理を全Vに量化したaxiomにはしない。

| ID | 調査した版・番号 | 仮定・結論の型案／接続の責任 |
| --- | --- | --- |
| DG-DR | [Drinfeld, DG quotients of DG categories, arXiv math/0210114v7 (2008)](https://arxiv.org/pdf/math/0210114v7)、§3.1、Thm 3.4、§3.5。出版はJ. Algebra 272 (2004), 643–691、出版番号対照は採用前確認 | 小さいA-dg圏D、full B、すべてx,bについてHom_D(x,b)がA上K-flat、又は逆向きHom_D(b,x)がK-flat。定義したpath商に対し `tria(D)/tria(B) ≃ tria(D/B)`。flatnessなしは解像度版。D8の構成とD10のKaroubi接続は自分で証明 |
| DG-PER | [Keller, On differential graded categories, math/0601185v5 (2006)](https://arxiv.org/pdf/math/0601185v5)、§3.5、Cor 3.7 | 固定した小さいD、宇宙内の全余積をもつD(D)。representable生成からPerf(D)＝compact。finite cell/retractの定義、小さいenhancementと具体的既存perfect比較はD6が所有 |
| DG-GEN | 同Keller v5、Thm 3.8（とくに(b)/(c)の条件を採用時照合） | algebraicなA線形三角圏と指定生成集合。一生成元版は既に定義したdg enhancementのEnd(E)を使う。idempotent complete＋thick生成でPerf比較、compact生成の場合のみ導来加群圏全体比較。単なる加法的生成性で後者を得ない |
| DG-MOR | 同Keller v5、Lemma 3.10、Thm 3.11 | 指定D–E bimodule Xについて各X_xがperfect、Homへの準同型、compact生成の三条件を固定し、`(-⊗ᴸ_D X)`の導来圏同値・Perf制限を得る。自然性と中心/scalar extension比較はD5/D9/D10で接続 |
| DG-TAB | [Tabuada, C. R. Math. Acad. Sci. Paris 340 (2005), 15–19](https://www.numdam.org/item/10.1016/j.crma.2004.11.007.pdf)、Thm 2.1 | 小さいA-dg圏全体、W=quasiEquivalence。Fibは各Hom degreewise surjective＋H⁰のisomorphism lifting、Cof=llp(trivial Fib)。生成I,Jを本文に合わせ定義後Mathlib ModelCategoryへ載せる。**Morita Wの構造ではない**、dg加群転送とも別。M5初期の必須依存にしない |
| DG-INFTY | [Lurie, Higher Algebra, 2017-09-18版](https://www.math.ias.edu/~lurie/papers/HA.pdf)、Prop 1.3.1.10/1.3.1.17、§1.3.2、Thm 1.3.4.20 | 比較入力は一つの名前に束ねる案。dg nerveとDold–Kanからのsimplicial nerve比較、指定homotopically projective module enhancementからの安定モデルの提示、exact/Morita図式の翻訳を必要成分として区別。1.3.4.20はsimplicial model仮定、任意Ch(A)が標準SM7を持つとはしない。§1.3.2のstable subcategory条件は採用時に番号を追加照合 |
| DG-SHIP | [Shipley, HZ-algebra spectra are differential graded algebras, math/0209215v4 (2006)](https://arxiv.org/pdf/math/0209215v4)、Thm 1.1、Cor 2.15。出版AJM 129 (2007), 351–379、出版番号対照は採用前確認 | 可換離散環A上の**結合的**非有界dg algebra HとHA-algebraのQuillen同値のzigzag、その加群版。one-object End(E)への具体的特殊化をM6で使用。任意Aの可換dg algebraと厳密可換ring spectrumの比較を主張しない。perfect保存・中心作用・connectiveness・係数変更の適合は別の明示的結論/接続 |

原典の全一般性をLeanで実装することと、その具体的適用の引用を区別する。
DG-INFTYは現状でLeanの∞圏型を新設する指示ではなく、文献から使う主張の翻訳台帳。
未定義∞圏をopaque対象で置き換えず、M6の源のdgモデル・導来関手・exact図式について
Leanで述べられる結論に落とす。その結論が上記番号だけから十分に得られるかは採用前レビューが必要。
ShipleyはM6所有の比較で、M5は入力となるH・Perf_dg(H)を供給する。

採用ゲートは、版/番号/ページ、環・smallness・flatness、cochain/chain変換、
定義済みの対象と射クラス、比較関手、自然性の範囲、使用先とaxiom依存を台帳へ記録し、
引用の仮定を具体的対象で証明すること。番号未照合の成分は定理の採用済み仕様に数えない。

## 8. M6への入力の形

推奨入力は小さいdg enhancement **`Perf_dg(D)`**（予定名）とそのH⁰、
dg functor又はperfectを保存する導来bimodule、Morita W、dg exact sequenceのデータ。
大きいD(D)全体を非連結K理論のsmallな入力にしない。
Perf_dg(D)はhomotopically projective加群の有限cell/retractの代表系から作り、
`H⁰(Perf_dg(D)) ≃ Perf(D)` を提供する。D(D)のretractをstrict dg idempotentへ
自動に持ち上げず、解像度・代表系のHom比較を明示する。

M5がM6へ渡す契約は、(1) smallnessと冪等完備性、(2) shift/coneとexactness、
(3) derived tensorによる係数変更のidentity/comp自然同型、(4) dg商のexact sequenceと
perfect hull/Verdier/Karoubi比較、(5)中心・支持・G作用、(6)H⁰から既存三角K₀への関手。
非連結K理論のπ₀比較そのものはM6が所有し、M5のK₀比較と二重実装しない。

M6が対応する安定圏を入力に選ぶ場合も、元のdg enhancementを保持し、
DG-INFTYで「このモデルが表す安定∞圏」の主張として文献と比較する。
Shipleyは一対象dg algebra（M9のH）について始め、一般dg圏のspectral enrichmentへの
拡張は別の比較契約とする。M5全体の完了条件にShipleyの実装を含めない。

## 9. 見積もりと最初の実装単位

1単位は通常1〜3ファイル、定義・主要法則・具体例・比較・ビルド/監査を含む。
数値はLeanで試作した実績ではなく設計見積もり。共有G群の工数はk-theory.md側だけに数える。

| M5独自の範囲 | 単位数 | 主な不確実性 |
| --- | --- | --- |
| D0〜D2 | 12〜22 | closed構造、符号とbraiding、H⁰の線形商 |
| D3 | 12〜22 | enriched end・Yoneda・free、cone/shift |
| D4（局所化/semifree） | 15〜28 | 任意small Dの解像度、三角公理、局所小性/余積 |
| D4m（具体的検証/比較のみ） | 8〜15 | Ch(A)のsmallness、monoid axiom、多対象cell計算。G2/G5は含まない |
| D5 | 15〜28 | coend、非有界K-flat、導来合成・係数変更 |
| D6〜D7 | 12〜24 | 小さいenhancement、compact/retract、生成元比較 |
| D8 | 18〜35 | path微分・合成・任意環の解像度、hull |
| D9〜D10 | 12〜24 | bimodule整合性、既存商のnull・自然性 |

合計104〜198単位。標準単位0.5〜2人日、重い解像度・宇宙・商比較は2〜4人日以上で、
全体の暫定幅は160〜400人日程度（共有G群・M9固有の可換環論・M6は別）。
初期の3〜5単位で再見積もりする。局所化を先行する案のM9向け最小経路は
D0/D1の必要部分＋D3のrepresentable部分＋D5のbounded-above K-flat＋D8のpath定義で、
25〜45単位程度。これはM5完了・M9完了の見積もりではない。

| 最初の単位 | 予定配置 | 前提・受入条件 |
| --- | --- | --- |
| U0 仕様固定 | `DifferentialGraded/README.md`＋小さい検証入口 | G0の宇宙とcochain規約、主モデル/合成順、引用-free入口、既存APIを一覧化。依存にSpectra・論文固有圏を含めない |
| U1 A線形Hom複体と合成 | `Complexes/HomComplex.lean`, `Complexes/Composition.lean` | `linearHomComplex A`を再利用。通常順の合成chain map、δ_compとの一致、閉次数0単位と結合。degree 0/−1/1で成分例、特性2にも余計な仮定を置かない |
| U2 豊穣dg圏の入口 | `Category/Basic.lean`, `Category/Examples.lean` | U1と既存monoidal。Enriched主モデルと成分constructor往復、Koszul順序比較、one-object A・Ch(A)の例、ForgetEnrichment≃Z⁰。別の公開dg構造体を増やさない |
| U3 H⁰・関手・準同値 | `Category/Homotopy.lean`, `Functor/Basic.lean`, `Functor/QuasiEquivalence.lean` | U2。境界による商、H⁰の合成well-defined、A線形性、dg functorのH⁰ functor、準同値のidentity/comp。通常の圏同値との混同がない |
| U4 tensor–Homと豊穣計算 | `Complexes/Closed.lean`, 必要なら`Complexes/Braiding.lean` | U1。整数全次数のtensor/Hom随伴・自然性、signed braiding整合性。既存cochainTensor/Symmetryと比較、G6へCh(A)の具体的入力を引き渡す |
| U5 representable右加群 | `Module/Basic.lean`, `Module/Yoneda.lean` | U2/U3/U4。dg oppositeの符号、代表加群、Hom複体/変換、Yoneda、D=Aの普通複体例。後続free/forget・resolutionのAPIを確定 |

U1〜U3はG2/G4/G8のいずれの選択でも先に作れる。
U4で閉構造の難度を測定し、U5後にD4主経路とD4m共有ゲートの工程を再確認する。
上記は2026-10-14の設計時の予定。2026-10-15にU0〜U3を実装した（§11）。

## 10. 検証と終了条件

実装担当者は各単位で対象ファイルをビルドし、主要な一般宣言の`#print axioms`を確認する。
一般論の新規sorry・引用axiom依存は不可。当てはめの引用の依存は台帳IDで説明する。
既存のnamespace・宣言名、`Spectra/StageTwo.lean`の引継ぎを壊さない。
ルートimport、可換環論・CLMST・未追跡のDerivedTensorRealization等の並行作業ファイルは変更しない。
比較用の新規入口から既存APIをimportし、必要な変更が発見された場合は先に範囲を記録する。

段階の受入はビルドだけでなく、任意Aの例、一対象の既存D(A)/perfect比較、
商への因子化と係数変更の可換図式、引用条件の具体的検証を含む。
D10終了時にM5完了とし、M9固有の未完項目とM6への契約を別に報告する。
2026-10-14の設計段階の終了条件は二つの計画の記録と照合であった。
2026-10-15の独立実装の終了条件・検証結果は§11に記録する。


## 11. U0〜U3 実装記録と次段階への引継ぎ（2026-10-15）

**U0〜U3を完了。** 独立入口は
[StageOne.lean](../SerrePositivity/DifferentialGraded/StageOne.lean)、
仕様とファイル一覧は [README](../SerrePositivity/DifferentialGraded/README.md)。
namespace は `SerrePositivity.DifferentialGraded`。
Lean `v4.35.0-rc4`、Mathlib HEAD と manifest の SHA
`e6bbacd0e1b7307ff6e17da09cd2455f60804fa6` を再照合した。
共有ルート・既存 PerfectComplex・Spectra・共有一般論・他チャットの作業ファイルは編集していない。

### 11.1 実際に公開した API と受入根拠

| 単位 | 実装と検証 |
| --- | --- |
| U0 | `Complex A` は `CochainComplex (ModuleCat.{u} A) ℤ`。`A : Type u` と Hom 加群の宇宙は同じ u、対象 `D : Type v` は独立。Hom 元・Z⁰/H⁰ Hom は Type u。非有界・任意 CommRing。引用-free独立入口、import閉包、既存APIの再利用をREADMEに記録 |
| U1 | `homComplex` は Mathlib `linearHomComplex A`。`differential_comp` は既存 `δ_comp` と同じ通常順Leibniz。`composition : Hom(Y,Z) ⊗ Hom(X,Y) ⟶ Hom(X,Z)` を直和普遍性 `tensorLift` で構成。`enrichedComposition` は既存 signed symmetry の後に通常順合成。`enrichedComposition_component`/`_apply` が `(-1)^(pq)` を証明。`identity_comp`/`comp_identity`/`enrichedComposition_assoc`、`closedZeroEquiv`、`contractingHomotopy`。0/−1/1 と ZMod 2 の受入例 |
| U2 | `DGCategory` は既存 `EnrichedCategory (Complex A)` の別名。`ofHomObjects` と双次数 constructor `ofComponents`、`ofHomObjects_recover` と `tensorLift_recover`。独立したdg構造体なし。`GradedHom`/`forward`/`compose`、通常順の微分・単位・結合。Ch(A)と一対象Aの具体例。`complexClosedEquivalence` と `complexEnrichedOrdinary` が既存chain map圏と単位・合成を比較 |
| U3 | `HomotopyCategory A D` は `CategoryTheory.Quotient (boundaryRelation A D)`。`boundaryCongruence` で合成well-defined。`toHomotopy_map_eq_iff_boundary` が元のHom複体の−1境界による商であることを証明。Z⁰/H⁰と商関手はA線形。`DGFunctor` は既存 `EnrichedFunctor`。A線形の `onHomotopy`、商への四角形 `onHomotopy_fac`、identity/comp。`HomQuasiIso` と `QuasiEquivalence`、identity/compの証明。`complex_H0_eq_iff` は既存chain homotopyとの一致 |

`ofComponents` はHom複体と閉単位、双次数の**A線形射**、tensor微分との両立を入力する。
単位・結合の入力は構成したchain mapに対するMathlibの豊穣圏法則。
元だけの独立dgモデルや未証明法則をまとめたSetup型は作っていない。

Z⁰ は `ForgetEnrichment` をそのまま使う。`unitCycleEquiv`/`closedHomEquiv` により閉次数零元と同一視する。
H⁰ の関係は単位複体からの射のchain homotopyで定義し、
`unit_homotopy_boundary` により `d : Hom⁻¹ → Hom⁰` の境界との厳密な一致を証明した。
この関係自体がcongruenceなので、商の合成閉包が余分な等式を増やさない。
一般のH⁰の三角構造は未主張。

### 11.2 検証結果

[Acceptance.lean](../SerrePositivity/DifferentialGraded/Checks/Acceptance.lean) は
任意A・整数次数・標数二の型検査、単位・合成の符号、H⁰のA線形関手を検査する。
準同値の二条件には独立の反例を用意した：

- 空dg圏から一対象Aへの関手は HomQuasiIso だが H⁰ 上本質的全射ではない。
- 非零Aの一対象dg圏から零dg圏への関手は H⁰ 上本質的全射だが HomQuasiIso ではない。

[Axioms.lean](../SerrePositivity/DifferentialGraded/Checks/Axioms.lean) の主要41宣言は
すべて `propext`・`Classical.choice`・`Quot.sound` のみ。
新規sorry・引用axiom・外部引用依存なし。
対象17 Leanファイルをこの入口からビルドした。

再実行入口：

```sh
lake build SerrePositivity.DifferentialGraded.Checks.Axioms
lake env lean SerrePositivity/DifferentialGraded/Checks/Axioms.lean
lake build SerrePositivity.Spectra.StageTwo
lake env lean scripts/check_spectra_stage2.lean
python3 scripts/check_documentation.py
```

ローカルimportの推移的閉包を調べ、Spectra・Paper・Inputsのモジュールを含まないことを確認した。
既存tensor・signed symmetryとそれらのPerfectComplex依存を再利用する。
引用台帳は [Inputs/DifferentialGraded/README](../SerrePositivity/Inputs/DifferentialGraded/README.md)。
採用済み0件。§7の候補は依然として未採用。

### 11.3 共有系列への契約と要求

U0〜U3は共有G群を待たず完了し、共有一般論の複製はない。
現段階で不足する共有APIによるブロックはない。
次の依頼は**後続使用時の型契約**であり、存在を仮定したLean axiomではない。

| 共有所有 | 型・仮定・使用箇所 |
| --- | --- |
| G0 | 初期 `u_hom = u_A = u`、`u_obj = v`。より大きいHom/加群/局所化/余積の宇宙を別途指定する契約を維持。U4の閉構造とU5のendでmax/successorを確認し、任意Dがsmallだとはしない |
| G6/H5 | 任意モノイダルVと `EnrichedOrdinaryCategory V C` の表現性。tensor/cotensorのHom同値は `Hom_C(v ⊗ x,y) ≃ Hom_V(v,eHom(x,y))` 及び双対、自然性付き。M5はU4のCh(A)閉構造・U5のHom endを具体的入力として渡す。SM7やpullback-hom/pushout-productの一般同値は共有所有 |
| G1/H4 | Mathlibの通常 `Adjunction` 上のQuillen条件と、同じMorphismPropertyの局所化上の `Adjunction.derived`。使用はD4m/D5。dg加群の随伴と保存条件はM5が具体的に検証して渡す |
| G2/G5 | free/forget右転送。生成I,J、small object仮定、free(J)-cellのobjectwise quasiIsoを入力し、Mathlib ModelCategoryを返す一般API。M5がU5以降にfree_x、球/円盤、cell計算を供給。U0〜U3には依存しない |

### 11.4 U4/U5 と残課題

U4は整数全次数の `tensor–linearHomComplex` 随伴・両変数自然性を構成する。
既存 `cochainTensorSymmetry` の自然性・hexagonを証明し、signed `SymmetricCategory` を登録する。
今回証明した合成の結合・単位だけからbraiding全整合性・閉構造の完成とは数えない。
Ch(A)の `MonoidalPreadditive`/`MonoidalLinear` と双/三次数のext・tensor成分・単位評価は再利用できる。

U5はそのbraidingを使ってMathlib `EnrichedCategory.opposite` に接続し、
`Dᵒᵖ` からCh(A)への右代表加群、Hom end・Yonedaを構成する。
通常の `Dᵒᵖ ⥤ Ch(A)` と同一視しない。通常順μとopposite/右作用の符号の成分比較を維持する。
`DGFunctor.onHomotopy_fac` と `toHomotopy_map_eq_iff_boundary` を後続の比較図式の入口にする。

D4はobjectwise quasiIsoによるMathlib局所化を先行し、D4mの射影モデル比較は共有G1/G2/G5後。
dg加群・semifree解像度・非有界K-flat・導来tensor・dg商・Morita・Perf_dg・既存perfect比較は未実装。
従ってD0〜D10の全受入、M5完了、M6入力、M9当てはめの完了とは報告しない。
U4/U5の実装実績後に§9の長期見積もりを再評価する。

## 12. U4/U5 の実装実績（2026-10-15、受入済み）

以下は検証・コミットの区切り。U4全受入は§12.3、U5全受入は§12.7で確認した。
D3全体やM5全体の完了とは数えない。

### 12.1 U4a：signed braiding

[Complexes/Braiding.lean](../SerrePositivity/DifferentialGraded/Complexes/Braiding.lean) で
既存 `cochainTensorSymmetry` の両変数自然性、forward/reverse hexagon、対合性を用いた
`complexSymmetricCategory` を実装した。`braiding_eq_existing` は既存交換同型との定義上の一致。
すべて任意可換環・非有界複体。三重tensor成分上でKoszul符号の指数の分配を証明する。
[Checks/Braiding.lean](../SerrePositivity/DifferentialGraded/Checks/Braiding.lean) のビルド成功。
主要5宣言は標準公理のみ。ZMod 2、Mathlib enriched oppositeのinstance、両hexagonを検査した。

tensor–Hom随伴・閉構造・豊穣計算、右代表加群・Hom end・Yonedaは引き続き実装する。

### 12.2 U4b：tensor–Hom 随伴と閉構造

[HomFunctor.lean](../SerrePositivity/DifferentialGraded/Complexes/HomFunctor.lean) の
`homFunctor`/`homPostcompose`/`homPrecompose` は既存 `linearHomComplex` の関手性。
[Currying.lean](../SerrePositivity/DifferentialGraded/Complexes/Currying.lean) で
全整数次数の `curryRight`/`uncurryRight`、chain map 性、往復則、三変数自然性を証明した。
直和 tensor と全次数の Hom の族を直接使い、有界性・平坦性・体の仮定なし。
[Closed.lean](../SerrePositivity/DifferentialGraded/Complexes/Closed.lean) の
`tensorRightHomAdjunction`、`complexClosed`、`complexMonoidalClosed` は Mathlib の随伴・閉構造。
右随伴の対象は `linearHomComplex A` と定義上同じ。
`tensorHomEquiv_component` と `evaluation_component` は左 tensor 転置と評価の Koszul 符号を固定する。

[Checks/Closed.lean](../SerrePositivity/DifferentialGraded/Checks/Closed.lean) がビルド成功。
任意A・ZMod 2・既存tensor/Homの一致・転置の往復・随伴の両三角恒等式を検証。
主要14宣言は標準公理のみ。次は既存dg豊穣合成と閉構造由来合成の比較、U5の右加群とYoneda。

### 12.3 U4c：閉構造と主dg豊穣の一致、U4受入

[Complexes/Enrichment.lean](../SerrePositivity/DifferentialGraded/Complexes/Enrichment.lean) の
`closedComposition_eq`、`closedIdentity_eq`、`complexEnrichment_eq_closed` は
閉構造由来のMathlib自己豊穣とU1/U2の主dg豊穣の一致を証明する。
評価の全次数の符号を計算し、豊穣合成の符号と同じことを確認した。
[Checks/Enrichment.lean](../SerrePositivity/DifferentialGraded/Checks/Enrichment.lean) はビルド成功、
主要3宣言は標準公理のみ。

これでU4の随伴・自然性・signed braiding整合性・既存tensor/symmetry比較を満たす。
G6には `complexSymmetricCategory`、`complexMonoidalClosed`、三変数自然性と
`complexEnrichment_eq_closed` を具体的Ch(A)入力として渡せる。
U5全体は継続中であり、右代表加群・Hom end・Yonedaと一対象比較の完了を引き続き要求する。

### 12.4 U5a：opposite・代表加群・Hom end

`Module/Basic.lean` は Mathlib 豊穣 opposite とその Koszul 符号の成分公式、
`Module/Representable.lean` は右代表加群 `representable x` の単位・合成保存を証明する。
右加群の対象は Mathlib `EnrichedFunctor` の型別名であり、新たな対象データは導入しない。
`Module/Hom.lean` の `moduleHom` は全対象の Hom 複体の直積から、
全豊穣 Hom に対する自然性を equalizer で課す end。
`moduleHomEquiv` は任意パラメータ複体 K からの射と Mathlib `GradedNatTrans` の同値。
Mathlib の現行 `EnrichedNatTrans.out` は閉次数零の通常圏の自然性のみなので、
それを全次数自然性の代用には使わない。

Hom end の存在仮定は `[Small.{u} D]`、係数環と加群の宇宙は u、対象宇宙 v は独立。
任意 D に smallness を仮定したことにはせず、この仮定を公開 API に保持する。
上記3ファイルはビルド成功。加群圏の単位・合成、dg Yoneda、一対象比較は継続中。

### 12.5 U5b：全次数 dg Yoneda

`Module/Action.lean` は斉次作用の単位・符号付き結合則を証明する。
全次数自然性と、次数 k の変換 α と次数 p の作用 f に対する
`α(f v) = (-1)^(kp) f(α(v))` の往復を証明した。
`Module/Yoneda.lean` の `dgYonedaEquiv` は任意パラメータ複体 K の豊穣自然変換を M(x) への射に同定し、
`dgYonedaIso` は `moduleHom (representable x) M ≅ M(x)` を chain iso として構成する。
拡張・単位での評価・両往復とパラメータでの自然性を証明し、H⁰ のみには制限していない。
Hom end と同じ `[Small.{u} D]` を明示する。ビルド成功。
加群圏の単位・合成、閉次数零射との比較、一対象環の比較と free/forget の後続契約は継続中。

### 12.6 U5c：主モデルの dg 加群圏

`Module/Composition.lean` は全次数自然性の合成保存、単位の自然性、
Hom end への単位・豊穣合成と成分公式を証明する。
`Module/Category.lean` の `moduleEnrichment` は既存 Mathlib `EnrichedCategory` の instance。
end の成分による ext から両単位則と結合則を証明する。
`ModuleCategory` はその Mathlib `ForgetEnrichment`、
`moduleClosedHomEquiv` は射を単位パラメータの全次数自然変換に同定する。
`moduleEvaluationDG` は end 成分による豊穣評価関手、
`moduleEvaluation` は閉零圏から既存の非有界 chain map 圏への評価関手。
通常の enrichedFunctor 圏の弱い自然性には置き換えていない。
両ファイルはビルド成功。一対象比較・後続契約と総合検証は引き続き行う。

### 12.7 U5d：一対象環 A の比較と U5 受入

`Module/Ring.lean` の `ringModuleObjEquiv` は加群対象と既存 Ch(A) の同値。
単位保存から作用が一意に定まることを証明し、`ringModule_recover` は厳密な対象復元。
`ringModuleHomIso` は任意の一対象加群対の全次数 Hom end と通常の `linearHomComplex` の chain iso。
`ringModuleEquivalence` は閉零加群圏と既存非有界複体圏の同値であり、評価関手の
充満・忠実・本質的全射を証明する。一般可換環のままで、体の仮定はない。

独立入口は `DifferentialGraded/StageTwo.lean`。
`Checks/ModulesAcceptance.lean` は任意 A、独立対象宇宙 v と明示 smallness、
全次数パラメータ Yoneda、次数 1 の変換と次数 −1 の作用、ℤ と ZMod 2 の一対象比較を検証した。
`Checks/Modules.lean` の主要16宣言は標準公理のみ。新規 sorry・引用 axiom はなし。
U4/U5 に追加した監査は38宣言、U0〜U5合計79宣言。

これで U5 の dg opposite 符号、代表加群、全次数 Hom/変換、dg Yoneda、
一対象 A と普通複体の比較、後続契約の条件を満たす。
`moduleEnrichment` と Hom end を G6 の Ch(A) 具体例に供給できる。

### 12.8 次の独立実装と共有系列への型契約

以下は**未実装の後続 API の仕様**。Lean の定理・存在仮定・引用 axiom にはしていない。
`A : Type u`, `[CommRing A]`, `D : Type v`, `[DGCategory A D]`, `[Small.{u} D]` を保つ。
`RightModule A D : Type (max (u+1) v)`、その Hom 複体は依然 `Complex A : Type (u+1)`。
任意の大きい D の end を黙って仮定しない。

| 所有・次の範囲 | 固定する型・仮定・使用箇所 |
| --- | --- |
| M5：free/forget | `freeAt x : Complex A ⥤ ModuleCategory A D`、値は `K ⊗ Hom_D(y,x)`。次数 p の右作用を K の次数 k と交換すると `(-1)^(pk)`。`freeAt x ⊣ moduleEvaluation A D x` を通常 chain map の随伴として証明し、豊穣 Hom の `Hom(freeAt x K,M) ≅ homComplex A K (M(x))` も保持する。現在実装した `representable`/`dgYonedaIso`/`moduleEvaluationDG` を使う |
| M5：underlying family | `ModuleCategory A D ⥤ (Discrete D ⥤ Complex A)`。射は `moduleEvaluation` の全成分。これは忘却先であって、右 dg 加群を通常 Dᵒᵖ の関手圏に置き換えるものではない |
| M5：resolution/導来圏 | `K(D) := HomotopyCategory A (RightModule A D)` は既存境界商の入口。閉零圏の射 f に対し `W_D f := ∀ x, QuasiIso ((moduleEvaluation A D x).map f)` を Mathlib `MorphismProperty` として定義し、2-out-of-3・retractを証明する。先にこの W の局所化を構成し、shift/cone・極限余極限・semifreeの実装を続ける |
| M5 → G2/G5 | `freeAt x` で球/円盤の生成射を移し、対象族・次数・射の宇宙を u/v とともに固定。free(J)-cell が objectwise W_D に入ることと smallness の具体的証拠は M5 側。一般 small object・多対象転送・モデル認識は共有側 |
| M5 → G1 | free/eval・restriction/extensionの実際の随伴と objectwise W/Fib の保存条件を供給後、通常 Mathlib Quillen/derived adjunction API へ接続する。U4/U5ではモデル構造の存在を仮定していない |
| M5 → G6 | `complexSymmetricCategory`, `complexMonoidalClosed`, `complexEnrichment_eq_closed`, `moduleEnrichment`, `moduleHomEquiv` と明示 smallness。任意VのSM7・pullback-hom/pushout-product一般同値は共有側 |

未完成は D3 の free_x・shift/cone・極限余極限・objectwise W、D4 の局所化・解像度、
D4m の射影モデル比較、D5以降の K-flat・導来 tensor・dg 商・Morita・Perf/既存 perfect 比較。
この段階で M5全体、M6入力、M9当てはめの完成は主張しない。
共有 G API の不足による現在のブロックはない。対象ファイル・共有ルート import・既存 PerfectComplex は保持した。

### 12.9 総合検証と保存

2026-10-15、固定 Mathlib HEAD と `lake-manifest.json` の SHA 一致を再確認。
次のビルド対象を同時に指定して成功した：

- `DifferentialGraded.Checks.Axioms`（U0〜U3、41宣言）
- `DifferentialGraded.Checks.Braiding`（5宣言）
- `DifferentialGraded.Checks.Closed`（14宣言）
- `DifferentialGraded.Checks.Enrichment`（3宣言）
- `DifferentialGraded.Checks.Modules`（16宣言、`ModulesAcceptance`/`StageTwo` を含む）
- 既存 `SerrePositivity.Spectra.StageTwo`

上の5つの dg 監査ファイルをそれぞれ `lake env lean` で直接実行した。
79宣言の公理はすべて `propext`・`Classical.choice`・`Quot.sound` のみ。
担当 Lean ファイルの `sorry`/`admit`/新規 `axiom` 検索は0件。
`lake env lean scripts/check_spectra_stage2.lean` も成功。
`python3 scripts/check_documentation.py` は Markdown 21ファイル・exposition参照306件、失敗0件。
担当ファイルの `git diff --check` も成功。
StageTwo のローカル import 閉包は63モジュール（うちdg実装29）で、Spectra・Paper・Inputsへの依存はない。
共有ルート import・既存 PerfectComplex・並行作業ファイルは編集していない。

U4は3区切り、U5は4区切りに分け、担当ファイルのみをコミットした。
後続作業は§12.8の具体的契約から始める。採用済み引用は引き続き0件。

## 13. U6〜U10 の継続実装（2026-10-15、進行中）

ユーザー依頼は「U10まで完成、ステップごとにコミット」。目標を途中の定義だけへ縮小しない。
任意可換環・非有界複体・Mathlib 豊穣主モデル・明示 smallness の契約と編集範囲を維持する。
U4/U5の実装済み対象・法則を再利用し、一般論の sorry・引用 axiom は追加しない。

| 単位 | 成果物と受入条件 |
| --- | --- |
| U6 | free/evaluation 随伴、全次数豊穣 Hom 同型・自然性、underlying family。自由対象 K⊗Hom_D(y,x) の作用の符号 (-1)^(pk) を検証する |
| U7 | 零対象・shift・cone、必要な極限余極限。全次数作用の保持、objectwise 評価式、一対象 A と既存複体構成の比較 |
| U8 | 加群ホモトピーと K(D)、objectwise quasiIso の Mathlib MorphismProperty。境界商との一致、2-out-of-3・retract、評価との整合性 |
| U9 | 指定 quasiIso の局所化 D(D)。対象・射宇宙・普遍性を固定し、閉零圏からの局所化と K(D) からの局所化を比較 |
| U10 | semifree 解像度、Hom 計算、三角構造・余積。一対象 A の既存 DerivedCategory との自然比較。解像度の存在・計算仮定を証明し、局所化の定義だけでは完了としない |

主経路 U6→U7→U8→U9→U10 は共有の射影モデル構造を先行条件としない。
D4m のモデル比較は共有の既存 G1/G2/G5/G6 API を再確認して具体的条件を供給する別の合流点。

### 13.1 U6a：自由加群の対象・全次数作用と underlying family

`Complexes/TensorEnriched.lean` で `tensorLeftHom` を閉構造から chain map として構成した。
`tensorLeftHom_apply` は斉次射の次数 p と左因子の次数 i による符号 (-1)^(pi) を検証する。
閉単位・豊穣合成保存を全整数次数で証明し、`tensorLeftDG` は Mathlib EnrichedFunctor。
`Module/Tensor.lean` の `tensorModule` はこの豊穣関手との合成。
`freeModule x K` の値は K⊗Hom_D(y,x)。単位・合成は豊穣関手から継承し、
`tensorModule_action` は右作用の符号を成分上で固定する。

`Module/Underlying.lean` は `moduleMorphism_ext`、対象の離散族への忘却関手とその忠実性。
通常の Dᵒᵖ の関手圏への置換はしない。
`Checks/FreeTensor.lean` で任意 A・独立対象宇宙・明示 smallness・ZMod 2 の自由対象を検証する。
U6aはU6全体の完了ではない。次は K の射に対する自由加群の関手性、
free/evaluation の通常随伴、全次数豊穣 Hom 同型と自然性を証明する。
U7〜U10 の受入は引き続き未完。

U6a の対象ビルドと `lake env lean .../Checks/FreeTensor.lean` の直接監査は成功。
主要6宣言は `propext`・`Classical.choice`・`Quot.sound` のみ。
担当差分の whitespace 検査と文書検査も成功（21 Markdown、306参照、失敗0）。

### 13.2 U6b：閉零射の成分構成と自由加群の関手性

`Complexes/ClosedMaps.lean` は通常 chain map と閉零豊穣射の cycle 比較、
Hom の前合成・後合成と閉零豊穣合成の一致を証明する。
`Module/ClosedMaps.lean` は Hom chain map の全次数可換式を仮定する成分族から、
Mathlib `GradedNatTrans`、主 Hom end の閉零加群射を構成する。
`moduleMorphismMk_eval` は評価による厳密な成分復元。
この構成は閉零射だけの通常自然性を仮定するものではない。
`tensorLeftHom_naturality` は左因子の chain map と全次数 Hom 作用の可換性。
`Module/Free.lean` は `tensorModuleMap`、`tensorModuleFunctor`、`freeAt x` を構成した。
恒等射・合成保存は underlying 成分の ext と tensor の関手性から証明する。

次の U6c は free/evaluation の随伴と、その単位・余単位・自然性。
U6d は全次数の豊穣 Hom 同型。これらが残るので U6全受入とU7〜U10の完成は未達。

U6b の対象ビルド、既存 `Checks.Modules` の受入・監査、
`lake env lean .../Checks/FreeFunctor.lean` の直接公理監査が成功した。
追加主要6宣言は標準公理のみ。文書検査（21 Markdown・306参照・失敗0）と担当差分検査も成功。

### 13.3 U6c：自由加群と評価の随伴

`Complexes/ClosedMaps.lean` の `mapFromUnit` と `closedMap` の両往復を証明した。
`Module/ClosedMaps.lean` は全豊穣自然性から Hom chain map の可換式を復元し、
その可換式と全次数作用の可換式の両方向を証明する。
`moduleMapFamilyEquiv` は主 Hom end の閉零射と全次数自然な通常 chain map 族の同値。
新たな dg 圏構造体や弱い通常自然変換の圏は導入していない。

`Module/TensorAdjunction.lean` の `tensorFamilyCurry` と `tensorFamilyUncurry` は
閉射族を任意非有界 K パラメータの Mathlib `GradedNatTrans` と同定する。
作用の符号 (-1)^(kp) を転置・逆転置の両方向で検証し、両往復を証明した。
`tensorClosedHomEquiv` は主閉零圏の射についての同値。
`freeHomEquiv` はそれを全次数 dg Yoneda に接続し、
`freeAt x K → M` と `K → M(x)` を同定する。
単位元での斉次評価公式から両変数の自然性を証明し、
`freeEvaluationAdjunction` は実際の Mathlib `Adjunction` として登録した。

`Checks/FreeAdjunction.lean` は任意 A・独立対象宇宙・明示 smallness、ℤ・ZMod 2、
任意 K のパラメータ、随伴の両三角恒等式を検証する。
主要9宣言は標準公理のみ。

この区切りで通常の free/evaluation 随伴は完成。
**U6d の全次数 Hom 複体の chain iso・自然性が残るため U6全体は未完**。
U7〜U10 の受入も引き続き未完。共有 G1/G2/G5 へは、この実際の随伴と
`freeAt`・`moduleUnderlying` を具体的入力として渡せるが、
モデル構造・Quillen保存条件・cell acyclicity・semifree解像度の存在はまだ主張しない。

U6c の対象・受入ビルド、前段 `Checks.FreeFunctor` の検証、直接公理監査が成功。
主要9宣言は `propext`・`Classical.choice`・`Quot.sound` のみ。
担当差分検査と文書検査（21 Markdown・306参照・失敗0）も成功した。

### 13.4 U6d1：自由加群の全次数 Hom 複体の chain iso

`Module/FreeHom.lean` は `freeUnitInsert`、Hom end の全次数自由評価 `freeHomEvaluation`、
通常 `linearHomComplex(K,M(x))` からの自由拡張 `freeHomExtension` を構成する。
`freeExtensionApp_apply` の符号は、次数 s の斉次 Hom が K の次数 k の元に作用した
出力次数 s+k と、代表 Hom の次数 q の積 (-1)^((s+k)q)。
微分との可換性は閉 tensor–Hom 転置から得られる実際の chain map であり、
次数零だけのデータを定義として使わない。
`moduleParamNaturality_of_cochain` と作用の成分公式から全豊穣自然性を証明した。

`freeFamilyEvaluation_extension` と `freeFamilyEvaluation_restore` は評価・拡張の両往復。
復元では任意のパラメータ複体 E と全次数自然な成分族を扱い、自由生成元の単位での値から復元する。
`freeHomIso` は `moduleHom (freeModule x K) M ≅ homComplex A K (M(x))` の chain iso。
任意可換環・非有界複体・明示 `[Small.{u} D]` を維持する。

`Checks/FreeHom.lean` は両往復、負次数 Hom と正次数の K/代表 Hom の成分、ZMod 2 を検証する。
主要6宣言を公理監査する。
**U6d2 の K/M の射に対する同型の自然性と、通常の随伴 Hom 同値との比較が残る**。
そのため U6全受入は引き続き未達。U7〜U10 の受入も未完。

U6d1 の対象ビルド・負正次数/ZMod 2 の受入・前段随伴の検証が成功。
`Checks/FreeHom.lean` の直接公理監査は6宣言すべて標準公理のみ。
担当差分と文書検査も成功（21 Markdown・306参照・失敗0）。

### 13.5 U6d2：全次数 Hom 同型の自然性・閉零比較、U6受入

`Module/HomFunctor.lean` は Mathlib `eHomWhiskerLeft`/`eHomWhiskerRight` による
主 Hom end の前後合成を、各評価対象の通常 `homPostcompose`/`homPrecompose` に同定する。
任意Vの一般論は既存 Mathlib を再利用し、このファイルには Ch(A)・dg 加群の具体的成分だけを置く。
`Complexes/ClosedMaps.lean` は Mathlib の豊穣 Hom whisker と既存線形 Hom の一致を証明する。

`Module/FreeHomNaturality.lean` の `freeHomIso_naturality_target` と
`freeHomIso_naturality_source` は自由 Hom の **chain iso** の M・K の射に対する自然性。
`freeHomIso_closed_zero` はその閉零制限と U6c の通常随伴 Hom 同値の一致を証明する。
全次数の Hom 複体を閉零射だけへ置き換えるものではない。

`tensorModule` の対象・Hom 射を明示した constructor 表記へ展開し、
`tensorModule_eq_comp` で既存 `EnrichedFunctor` の合成と定義上同じデータであることを証明した。
元の作用・単位・合成と公開 API は保持する。

U6の free/evaluation 随伴、全次数 Hom 同型、両変数自然性、閉零比較、underlying family の
受入項目が揃った。独立入口は `DifferentialGraded/StageThree.lean`（U0〜U6）。
U6 の受入検証は `Checks/FreeTensor`, `FreeFunctor`, `FreeAdjunction`, `FreeHom`, `FreeHomNaturality`。
任意可換環・非有界複体、独立対象宇宙と明示 smallness、正負次数、ℤ・ZMod 2 を検証する。
U6d2の主要8宣言、U6全体35宣言の公理監査を行う（U0〜U6合計114宣言）。

次は U7 の零対象・shift・cone・必要な極限余極限と objectwise 評価式。
続いて U8 のホモトピー/準同型、U9 の局所化、U10 の semifree・Hom 計算・三角構造・余積・
一対象 A の既存導来圏比較を完成させる。U10までの目標は保持し、現段階では未達。
共有 G1/G2/G5/G6 の一般論は複製せず、U6の実際の随伴と Hom 同型を具体的入力として渡す。

U6全体の5受入入口と既存 `SerrePositivity.Spectra.StageTwo` の同時ビルドは成功。
10の dg 監査ファイルを `lake env lean` で直接実行し、114宣言すべて標準公理のみと確認した。
担当 Lean ファイルの `sorry`/`admit`/新規 `axiom` は0件。
既存 `scripts/check_spectra_stage2.lean`、文書検査（21 Markdown・306参照・失敗0）、
担当差分の whitespace 検査も成功。共有ルート import・並行作業ファイルは編集していない。

### 13.6 U7a1：零加群と全次数零 Hom

`Complexes/Zero.lean` は `IsZero P` または `IsZero Q` から、任意次数の
`Homogeneous P Q n` が零となることと、`homComplex A P Q` の零対象性を証明する。
既存の複体評価・`IsZero` を再利用し、複体の零対象を再実装しない。
閉零複体と通常複体の比較関手の加法性も、この補助ファイルに登録した。

`Module/Zero.lean` の `zeroModule` は全対象で零複体、全次数の Hom 作用で零となる
既存 `EnrichedFunctor` の具体的対象。`moduleZeroTo`/`moduleToZero` は全次数自然な
chain map 族から構成した射であり、各評価が零射となる。
`moduleZero_isZero` は射の一意性、`moduleHasZeroObject` は通常圏の零対象を供給する。
`module_isZero_iff` は全評価での零対象性との同値、`moduleEvaluationZeroIso` は
選ばれた圏の零対象の評価と零複体の同型。
`moduleHom_isZero_src`/`moduleHom_isZero_tgt` は Hom end 自体の零複体性を証明する。
零加群の対象構成は任意 D、Hom end と閉零圏の結果には `[Small.{u} D]` を明示する。

受入入口は `Checks/Zero.lean`。任意可換環・非有界複体・独立対象宇宙、
次数 −1/+1、ℤ、一対象 A、ZMod 2 を検証する。
U7の直和・shift/cone・必要な極限余極限は残っており、U7全受入とはしない。
U8〜U10も未完で、U10までの目標を保持する。

U7a1の受入入口と既存 `Spectra.StageTwo` の同時ビルド、受入入口の直接実行は成功。
主要17宣言の公理はすべて `propext`・`Classical.choice`・`Quot.sound` のみ。
新規 sorry・admit・axiom は0件。文書検査は21 Markdown・311参照、失敗0件。
担当差分の whitespace 検査も成功。共有ルート・並行作業ファイルは編集していない。

### 13.7 U7a2：全次数作用を保持した有限直和

`Complexes/Biproduct.lean` の `biprodHomMap` は二つの Hom chain map を
既存複体の二項直和上の対角作用へ移す。全斉次成分、単位保存、
Koszul 符号付き豊穣合成保存、両射影・両包含との可換式を証明した。
`homComplex_biprod_ext` は直和への全次数 Hom を射影後の成分で判定する。

`Module/Biproduct.lean` の `biprodModule` は各対象で既存複体の直和を取り、
この対角 Hom を作用とする既存 `EnrichedFunctor`。単位・合成則は全次数で成立する。
`moduleBiprodFst`/`Snd`/`Inl`/`Inr` は全次数自然な chain map 族から構成した閉零射。
`moduleBinaryBiconeIsBilimit` は積・余積両方の普遍性を証明する。
Mathlib の零対象・二項積から有限積を作る一般論を再利用して
`moduleHasFiniteBiproducts` を登録した。共有一般論の複製はない。

`moduleBiprodIso` は具体的 objectwise 構成と選ばれた圏の直和の同型。
`moduleEvaluationBiprodIso` と両射影の可換式は、評価と既存複体の直和の比較。
評価の加法性から Mathlib の有限直和保存を使うので、有限族の評価比較も利用できる。
一対象 A の場合にも同じ評価比較が既存の通常複体の直和へ接続する。
対象の直和構成は任意 D、閉零圏の普遍性には `[Small.{u} D]` を明示する。

受入入口は `Checks/Biproduct.lean`。任意可換環・非有界複体、次数 −1、有限族、
ℤの一対象環と ZMod 2 を検証する。主要31宣言を公理監査する。
これで U7a の零対象・有限直和が揃った。U7の shift/cone・必要な残る極限余極限、
U8〜U10は未完であり、U10までの目標を保持する。

U7a2の受入入口と既存 `Spectra.StageTwo` の同時ビルド、受入入口の直接実行は成功。
主要31宣言の公理はすべて `propext`・`Classical.choice`・`Quot.sound` のみ。
新規 sorry・admit・axiom は0件。既存 `check_spectra_stage2.lean`、文書検査
（21 Markdown・311参照・失敗0）、担当差分の whitespace 検査も成功。
次の U7b では既存 `PerfectComplex/TensorShift.lean` と Mathlib の HomComplexShift を
再利用候補として照合し、全次数の shift 作用と既存複体の shift の比較を構成する。
共有ルート・既存 PerfectComplex・並行作業ファイルは編集していない。

### 13.8 U7b1：整数 shift の全次数 dg 関手と加群評価

固定 Mathlib の `Cochain.shift` は `δ_shift` により Hom 微分を `(-1)^s` 倍する。
`Complexes/Shift.lean` の `shiftHom s P Q` は次数 p の成分を `(-1)^(sp)` 倍し、
真の Hom chain map として構成した。`shiftHom_v` が全斉次成分、
`shiftHom_ofHom` が閉次数0での通常 chain map shift との一致を証明する。
単位と豊穣合成を保存する `shiftDG s` は既存 `EnrichedFunctor` である。
Mathlib の再添字付けと Hom 微分の定理を再利用し、複体 shift を再実装しない。

`Module/Shift.lean` の `shiftModule s M` は各対象で `(M(x))⟦s⟧`、
作用は `M.map ≫ shiftHom`。主 dg 関手との合成と同じデータで、
全次数作用に `(-1)^(sp)` が入ることを証明した。
`shiftedFamily_naturality` は全次数自然な chain map 族の通常 shift の全次数自然性。
`moduleShiftMap`/`moduleShiftFunctor` はこれを主 Hom end の閉零射へ持ち上げ、
`moduleShiftMap_eval` と `moduleShiftEvaluationIso` が評価と Mathlib の shift の一致・自然性を証明する。
対象構成と全次数自然性は任意 D、閉零加群圏の射には `[Small.{u} D]` を明示する。

受入入口は `Checks/Shift.lean`。任意可換環・非有界複体、正負 shift と正負次数、
ℤの一対象環、ZMod 2、閉零 chain map 比較、評価自然同型を検証する。
主要16宣言を公理監査する。整数ごとの関手は完成したが、零 shift と加法 shift の
coherence、`HasShift ℤ` 登録、cone、残る必要な極限余極限は未完。
次の U7b2 はそれらの shift coherence と全次数自然性を証明し、続いて cone を構成する。
U7全受入および U8〜U10は未完で、U10までの目標を保持する。

U7b1の受入入口と既存 `Spectra.StageTwo` の同時ビルド、受入入口の直接実行は成功。
主要16宣言の公理はすべて `propext`・`Classical.choice`・`Quot.sound` のみ。
新規 sorry・admit・axiom は0件。文書検査（21 Markdown・311参照・失敗0）、
担当差分の whitespace 検査も成功。共有ルート・並行作業ファイルは編集していない。

### 13.9 U7b2：shift の整合性と HasShift/CommShift

`Complexes/ShiftCoherence.lean` は Mathlib の `shiftFunctorZero`/`shiftFunctorAdd` の
比較が全次数 Hom に対して自然であることを証明する。
加法比較では `(s+t)p = tp+sp` の符号と既存 `XIsoOfEq` による次数輸送を照合した。

`Module/Isomorphism.lean` の `moduleIsoMk` は全次数自然な複体同型族を主 Hom end の
閉零加群同型へ持ち上げる。逆射の全次数自然性と両逆式も証明済み。
一般圏の同型・shift構造を新しく作らず、Mathlib の同型を再利用する。

`Module/ShiftCoherence.lean` は零・加法比較を加群自然同型に持ち上げ、
忠実な全評価による射の判定を使い、複体の比較から結合・零の整合性を証明する。
`moduleShiftMkCore`/`moduleHasShift` は Mathlib `ShiftMkCore`/`hasShiftMk` に接続する。
登録された関手・零・加法比較と明示構成の一致を公開した。
整数 shift は加法的で、`moduleEvaluationCommShift` は評価比較の零・加法の整合性を供給する。
負 shift は Mathlib の加群圏 `HasShift ℤ` の一般APIから逆関手を得る。
閉零加群圏には `[Small.{u} D]` を明示し、複体の全次数比較には D の仮定を置かない。

受入入口は `Checks/ShiftCoherence.lean`。任意可換環・非有界複体、
零/加法/負 shift、加法性、評価と比較射、一対象 ℤ、ZMod 2 を検証する。
主要28宣言を公理監査する。次は U7b3 の cone とその全次数作用・評価比較。
必要な残る極限余極限、U8〜U10は未完であり、U10までの目標を保持する。

U7b2の受入入口と既存 `Spectra.StageTwo` の同時ビルド、受入入口の直接実行は成功。
主要28宣言の公理は標準公理 `propext`・`Classical.choice`・`Quot.sound` の範囲内。
新規 sorry・admit・axiom は0件。文書検査（21 Markdown・311参照・失敗0）、
担当差分の whitespace 検査も成功。共有ルート・既存 PerfectComplex・並行作業ファイルは編集していない。

### 13.10 U7b3a：cone の全次数作用・微分・標準包含

`Complexes/Cone.lean` の `coneMapCochain` は、閉零射 f/g の cone 上の
全次数対角 cochain を既存 `mappingCone.liftCochain` から構成する。
左成分の +1 shift に次数 p の符号 `(-1)^p` を付け、両射影・全斉次成分を証明した。
加法・Aスカラー/整数単位の符号倍、恒等、通常順の全斉次合成を保存する。
`coneMapCochain_differential` は可換斉次 square の条件から微分との可換性を証明する。
交差項をこの可換式で消去し、Mathlib の `δ_liftCochain`/`δ_comp` を再利用する。

`Complexes/ConeHom.lean` の `coneHomMap` は、共通パラメータ複体 K からの
二つの Hom chain map が閉零射の square と全次数で可換する場合に、
cone の Hom chain map を構成する。Kの有界性や射の準同型性を要求しない。
`coneHomMap_inr` は既存標準包含の全次数自然性を証明する。

`Module/Cone.lean` の `coneModule` は全次数自然な閉零射族のobjectwise cone。
主 `EnrichedFunctor` の単位・合成は全次数で証明した。
`moduleCone f` は主閉零加群圏の実際の射から構成し、`moduleCone_eval` により
各評価が Mathlib の `mappingCone (eval(f))` と定義上同じ複体になる。
`moduleConeInr` は全次数自然な標準包含、評価すると既存の包含となる。
対象・作用は任意 D、主閉零加群圏の射は `[Small.{u} D]` を明示する。

受入入口は `Checks/Cone.lean`。任意可換環・非有界複体、正負次数の符号、
全次数の微分可換性、一対象 ℤ、ZMod 2、objectwise cone と包含を検証する。
主要22宣言を公理監査する。次の U7b3b ではconeからshiftへの射と、
可換squareに対するcone射・関手性を構成する。必要な残る極限余極限、
U8〜U10は未完であり、U10までの目標を保持する。

U7b3aの受入入口と既存 `Spectra.StageTwo` の同時ビルド、受入入口の直接実行は成功。
主要22宣言の公理はすべて `propext`・`Classical.choice`・`Quot.sound` のみ。
新規 sorry・admit・axiom は0件。文書検査（21 Markdown・311参照・失敗0）、
担当差分の whitespace 検査も成功。共有ルート・既存 PerfectComplex・並行作業ファイルは編集していない。

### 13.11 U7b3b：connecting map・cone 関手と triangle 比較

`Complexes/ConeMaps.lean` の `coneHomMap_connecting` は既存の
`mappingCone.triangle f` の第三射の全次数 Hom 自然性を証明する。
この第三射は **minus** の shifted first projection であり、既存
`PerfectComplex/TensorCone.lean` の `coneTriangle_mor₃_f` を再利用して符号を照合した。
`coneMapCochain_ofHom` は U7b3a の次数0対角作用と Mathlib の
`mappingCone.map` が同じ cochain であることを証明する。

`Module/ConeMaps.lean` は全次数自然な `moduleConeConnecting f : Cone(f) ⟶ M⟦1⟧` と
`moduleConeTriangle f` を構成する。各評価の第三射は既存の第三射と一致し、
`moduleConeTriangleEvaluationIso` は評価した標準triangleと既存複体triangleの同型。
この段階で閉零加群圏自体の distinguished triangle 構造を仮定していない。

`Module/ConeFunctor.lean` の `coneFamilyMap_naturality` は全次数自然な可換squareの
objectwise `mappingCone.map` の全次数自然性。これを実際の閉零加群射へ持ち上げ、
`moduleConeMap` の評価・恒等・合成・包含とconnecting mapとの可換性を証明した。
`moduleConeTriangleMap` は標準triangleの射、`moduleConeFunctor` は既存
`Arrow (ModuleCategory A D) ⥤ ModuleCategory A D` の関手。
標準複体cone射の恒等・合成・triangle可換式は Mathlib を再利用した。
対象圏Dの一般データには追加仮定を置かず、Hom end の閉零加群圏には `[Small.{u} D]` を明示する。

受入入口は `Checks/ConeMaps.lean`。任意可換環・非有界複体・全次数Hom、
標準triangle比較、可換square・arrow関手、一対象 ℤ、ZMod 2 を検証する。
主要17宣言を公理監査する。次は U7c の必要な極限余極限とobjectwise評価。
U7全受入、U8〜U10は未完であり、U10までの目標を保持する。

U7b3bの受入入口と既存 `Spectra.StageTwo` の同時ビルド、受入入口の直接実行は成功。
主要17宣言の公理はすべて `propext`・`Classical.choice`・`Quot.sound` のみ。
新規 sorry・admit・axiom は0件。文書検査（21 Markdown・311参照・失敗0）、
担当差分の whitespace 検査も成功。共有ルート・既存 PerfectComplex・並行作業ファイルは編集していない。

### 13.12 U7c1：objectwise 極限と評価による保存

`Module/ActionChain.lean` は主 Hom 射の右転置を `moduleActionChain` として公開し、
全次数自然な閉零射族・実際の加群射がこの tensor の chain map と可換することを証明する。
閉零次数だけの通常関手自然性に置き換えていない。
`Complexes/HomLimits.lean` は指定複体極限への全次数 Hom を射影後に判定する補助API。
これは既存 tensor–Hom 随伴と Mathlib の極限普遍性を使う Ch(A) の具体的結果。

`Module/Limits.lean` は `F : J ⥤ ModuleCategory A D` に対して、各評価図式の既存複体極限を使う。
`moduleLimitActionCone`/`moduleLimitAction`/`moduleLimitHom` により全次数作用を構成し、
射影との可換式、単位・豊穣合成の保存を証明する。
`limitModule`/`moduleLimitObj` はその主 `EnrichedFunctor` と閉零対象。
`moduleLimitπ`、`moduleLimitLift` は全次数自然な加群射で、
`moduleLimitConeIsLimit` は加群圏での極限普遍性を証明する。
`moduleEvaluationLimitIso` と射影の可換式は、選ばれた極限の評価比較。

宇宙は `A : Type u`、`D : Type v`、`J : Type w`、`Category.{w'} J`。
Hom end の閉零加群圏には従来どおり `[Small.{u} D]` を要求する。
一般構成には `∀ x : Dᵒᵖ, HasLimit (F ⋙ moduleEvaluation A D x.unop)` を明示する。
添字対象について `[Small.{u} J]` があれば、既存 ModuleCat/複体極限を使って存在を証明する。
添字射の宇宙 w' は独立で、追加の LocallySmall 仮定を置かない。
`moduleHasLimitsOfShape`、`moduleHasLimitsOfSize.{w',u}` と
`moduleEvaluationPreservesLimitsOfShape`/`OfSize` を登録した。
任意の大きいDや大きい図式の極限存在を暗黙に仮定しない。

受入入口は `Checks/Limits.lean`。任意可換環・非有界複体、独立宇宙、
objectwise射影/lift、真の普遍性と保存、ℤ・ZMod 2 の可算積を検証する。
主要36宣言を公理監査する。次は U7c2 の objectwise 余極限・余積。
U7全受入、U8〜U10は未完であり、U10までの目標を保持する。

U7c1の受入入口と既存 `Spectra.StageTwo` の同時ビルド、受入入口の直接実行は成功。
主要36宣言の公理はすべて `propext`・`Classical.choice`・`Quot.sound` のみ。
新規 sorry・admit・axiom は0件。文書検査（21 Markdown・311参照・失敗0）、
担当差分の whitespace 検査も成功。共有ルート・既存 PerfectComplex・並行作業ファイルは編集していない。

### 13.13 U7c2：objectwise 余極限と評価による保存、U7受入

`Complexes/HomColimits.lean` は指定複体余極限からの全次数 Hom を包含前に判定する。
既存の閉構造による左 tensor の余極限保存を用い、共有の任意Vの一般論を複製しない。
`Module/Colimits.lean` の `moduleColimitActionCocone`/`moduleColimitAction` は
全次数 tensor 作用を、左 tensor が運んだ余極限の普遍性から構成する。
`moduleColimitHom` と包含との可換式、単位・豊穣合成の保存を証明した。

`colimitModule`/`moduleColimitObj` は主 `EnrichedFunctor` と閉零対象。
`moduleColimitι`/`moduleColimitDesc` は全次数自然な射で、
`moduleColimitCoconeIsColimit` は加群圏での真の余極限普遍性。
`moduleEvaluationColimitIso` と包含の可換式は選ばれた余極限の評価比較。
宇宙は U7c1 と同じ u/v/w/w' で、閉零加群圏には `[Small.{u} D]` を要求する。
一般図式には全評価の `HasColimit` を明示し、`[Small.{u} J]` があれば
既存 AddCommGrpCat/ModuleCat/複体余極限から存在を証明する。
添字射宇宙w'は独立で、追加のLocallySmall仮定を置かない。
`moduleHasColimitsOfShape`/`OfSize.{w',u}` と評価の保存を登録した。

受入入口は `Checks/Colimits.lean`。任意可換環・非有界複体、独立宇宙、
objectwise包含/desc、真の普遍性と保存、ℤ・ZMod 2 の可算余積、
既存複体余極限の評価比較、shift/coneとの同時使用を検証する。主要32宣言を公理監査する。

これで U7 の零対象・有限直和・整数shift・cone・必要な極限余極限、全次数作用と
objectwise評価、一対象Aの既存複体構成との比較が揃った。
独立入口は `StageFour.lean`（U0〜U7）。共有ルート import は編集しない。
U8のホモトピー/準同型、U9の局所化、U10のsemifree・Hom計算・三角構造・
導来圏余積・一対象Aの既存DerivedCategory比較は未完で、U10までの目標を保持する。

U7全体の8受入入口（Zero/Biproduct/Shift/ShiftCoherence/Cone/ConeMaps/Limits/Colimits）と
既存 `Spectra.StageTwo` の同時ビルドは成功。8入口を `lake env lean` で直接実行し、
199宣言すべて標準公理の範囲内と確認した。U0〜U7の累計監査対象は313宣言。
担当 Lean の sorry・admit・新規axiomは0件。固定Mathlib HEADとmanifestのSHAは一致し、
Lean v4.35.0-rc4を保持した。既存 `check_spectra_stage2.lean`、文書検査
（21 Markdown・311参照・失敗0）、担当差分の whitespace 検査も成功。
共有ルート・既存 PerfectComplex・並行作業ファイルは編集していない。

共有 G1/G2/G5/G6 へは、既存 free/evaluation 随伴に加え、今回の small 図式の
極限余極限と全次数作用・評価保存を具体的入力として渡せる。
射影モデル構造・Quillen・転送・SM7の一般論は複製せず、現在のU7に共有API不足のブロックはない。
次の U8 は既存境界商の K(D)、objectwise quasiIso の MorphismProperty、
2-out-of-3/retract、ホモトピー・評価・coneによるacyclic性の整合性を証明する。
U9/U10の局所化・解像度・三角構造・導来圏比較は引き続き未完である。

### 13.14 U8a1/b1：全 dg 自然な加群ホモトピー・K(D) と objectwise quasiIso

`Module/Homotopy.lean` は `ModuleHomotopy` を Hom end の次数 −1 の元として定義し、
その微分が閉零射の差となる条件を課す。対象ごとに独立したホモトピーの存在とは区別する。
`moduleHomotopy_nonempty_iff` は既存の境界関係との一致、
`ModuleHomotopyCategory`/`moduleToHomotopy` は既存の A 線形な H⁰ 境界商 K(D) と商関手。
`moduleToHomotopy_map_eq_iff` は加群ホモトピーによる射の同一視の判定。
`moduleHomotopy_evaluation` は各評価への既存 chain homotopy を与え、
`moduleHomotopyEvaluation` は既存の複体ホモトピー圏への関手で、商関手との四角形が可換。

`Module/QuasiIso.lean` は各対象で評価が quasiIso となる閉零射のクラス
`moduleQuasiIso` を Mathlib の MorphismProperty として固定した。
評価による既存 quasiIso の逆像の共通部分との一致、恒等・合成、2-out-of-3、
retract 閉性、同型との両立を証明した。
評価ホモロジー写像は加群ホモトピーで一致し、quasiIso 判定は K(D) の射の代表元によらない。

`Module/HomotopyQuasiIso.lean` は K(D) の評価ホモロジーによる射のクラス
`moduleHomotopyQuasiIso` と `moduleHomotopyHomology` を公開する。
恒等・合成、2-out-of-3、retract 閉性、同型との両立、および
`moduleHomotopyQuasiIso_inverseImage` による閉零圏上の指定クラスとの一致を証明した。
宇宙は A:Type u、D:Type v、Hom の係数宇宙 u、`[Small.{u} D]` を維持し、
任意可換環・非有界複体を扱う。モデル構造・有界性・体の仮定は置かない。

受入入口は `Checks/ModuleHomotopy.lean`。
任意可換環での線形な境界商、評価ホモトピー、quasiIso の2-out-of-3/retract、
閉零/K(D) のクラス一致、ℤ・ZMod 2 の一対象環での既存複体の判定との一致を検証した。
この入口と `StageFour`・既存 `Spectra.StageTwo` の同時ビルドは成功（3169 jobs）。
入口の直接実行も成功し、主要27宣言はすべて propext/Classical.choice/Quot.sound の範囲内。
これまでの累計監査対象は340宣言。一般論の sorry・admit・新規axiomは追加していない。

U8全受入は未完。次は shift が境界を保存すること、K(D) 上のshift、
objectwise acyclic性とcone/quasiIsoの整合性を証明する。
U9の局所化比較、U10のsemifree解像度の存在・Hom計算・三角構造・余積・
一対象Aの既存導来圏比較も未完であり、U10までの目標を保持する。
共有一般論は複製せず、この段階で共有API不足によるブロックはない。

### 13.15 U8a2：全次数加群 shift・境界保存・K(D) の整合的整数 shift

`Module/ShiftHom.lean` はパラメータ付き全次数自然変換の shift を
`shiftModuleParamTrans` として構成し、Hom end の普遍性で `moduleShiftHom` を得る。
`moduleShiftHom_π`/`_π_v` は各対象・次数pの成分を示し、符号 (-1)^(sp) と
再添字付けを維持する。閉単位・豊穣合成の保存から `moduleShiftDG` を構成した。
閉零制限は既存の `moduleShiftFunctor` と一致し、評価した射は既存 chain map shift。

`Module/ShiftHomotopy.lean` はこの真の dg 関手から境界関係の shift 保存を証明した。
Mathlib `HasShift.quotient` を用い、K(D) の整数shiftと zero/add coherence、
商関手の CommShift を得る。評価も CommShift。
`moduleQuasiIso_shift_iff`/`moduleHomotopyQuasiIso_shift_iff` は
閉零圏・K(D)両方での準同型判定のshift不変性を示し、IsCompatibleWithShiftを登録した。
一般の商shiftやCommShift転送を独自に複製していない。

受入入口 `Checks/ShiftHomotopy.lean` のビルド・直接実行は成功。
任意可換環・独立宇宙・非有界加群での全次数構造、次数−1の符号成分、
境界保存、HasShift/CommShift、準同型クラスのshift不変性を検証した。
主要18宣言はすべて標準公理の範囲内。累計監査対象は358宣言。
U8全受入はcone/acyclic判定の受入記録を残して未完。U9/U10も未完で目標を保持する。

### 13.16 U8b2：標準 cone の acyclic 性・準同型判定、U8受入

`Complexes/AcyclicCone.lean` の `complex_quasiIso_iff_acyclic_cone` は、
固定版 Mathlib の `subcategoryAcyclic`、`quasiIso_eq_trW_subcategoryAcyclic` と
既存標準 cone triangle の distinguished 性を再利用して、
任意可換環上の非有界複体について準同型 iff cone が acyclic を証明する。
対象未定義の引用axiomや新たな三角圏公理を導入していない。

`Module/Acyclic.lean` は閉零加群圏の `moduleAcyclic` と K(D) の
`moduleHomotopyAcyclic` を objectwise に定義する。
商関手による acyclic 性の保存・反映、評価ホモロジーの零対象性との一致、
`moduleQuasiIso_iff_acyclic_cone` と
`moduleHomotopyQuasiIso_iff_acyclic_cone` による全 dg 作用を持つ標準加群 cone の判定を公開した。
この段階では K(D) 自体の三角構造や Verdier 商比較を完了と主張しない。それらは U10 に残る。

受入入口 `Checks/Acyclic.lean` は任意可換環・独立宇宙・非有界複体での判定、
閉零/K(D) の比較、恒等射coneのacyclic性、ℤ・ZMod 2 の一対象例を検証する。
ビルド・直接実行は成功し、主要8宣言は標準公理の範囲内。

U8の受入条件との対応は次のとおり。

| 条件 | 証明・検証入口 |
| --- | --- |
| 加群ホモトピーと K(D)、境界商との一致 | Module/Homotopy、Checks/ModuleHomotopy |
| objectwise quasiIso の Mathlib MorphismProperty、2-out-of-3/retract | Module/QuasiIso・HomotopyQuasiIso、Checks/ModuleHomotopy |
| 評価との整合性、ホモトピー不変性、閉零/K(D) の射クラス一致 | moduleHomotopy_evaluation・moduleQuasiIso_iff_of_homotopy・moduleHomotopyQuasiIso_inverseImage |
| 整数 shift と境界・準同型の整合性 | Module/ShiftHom・ShiftHomotopy、Checks/ShiftHomotopy |
| 全作用を持つconeのobjectwise acyclic性による準同型判定 | Module/Acyclic、Checks/Acyclic |

これで U8 を受入済みとする。独立入口は `StageFive.lean`（U0〜U8）。
U8の3受入入口とStageFive・既存Spectra.StageTwoの同時ビルドは成功（3176 jobs）。
3入口の直接実行・公理監査は53宣言すべて標準公理のみ。累計366宣言。
担当Leanのsorry・admit・新規axiomは0件、文書検査は21 Markdown・311参照・失敗0。
固定MathlibのHEADとmanifestのSHAが一致し、依存更新はしていない。
StageFiveのローカルimport閉包は107モジュール（dg69）でSpectra/Paper/Inputs依存なし。
共有ルートimport・既存PerfectComplex・並行作業ファイルは編集していない。

共有系列へは指定射クラスの2-out-of-3/retract、shift不変性、coneによるacyclic判定を
追加の具体的入力として渡せる。一般モデル圏・Quillen・転送・SM7は複製しない。
現在、共有API不足によるブロックはない。
次のU9は指定クラスでの局所化・普遍性と閉零/K(D)の局所化比較。
U10のsemifree解像度の存在・Hom計算・K(D)/D(D)の三角構造・Verdier商比較・
余積/局所小性の宇宙・一対象Aの既存DerivedCategory比較は引き続き未完。
U10までの目標を保持し、局所化の定義だけでは終了しない。

### 13.17 U9a：指定射の局所化・普遍性・導来評価

`Derived/Basic.lean` の `DerivedModuleCategory` は閉零加群圏を
指定 `moduleQuasiIso` で局所化した Mathlib の構成された局所化。
`moduleToDerived` と IsLocalization、指定準同型の像の `moduleDerivedIso` を公開した。
比較対象 `HomotopyDerivedModuleCategory`/`moduleHomotopyToDerived` は
K(D) の `moduleHomotopyQuasiIso` による同じ標準構成。
両者の同値は、この段階ではまだ主張しない。

対象宇宙と標準射宇宙はともに max (u+1) v。
`moduleStandardLocalization` はその宇宙での HasLocalization の具体的データで、
より小さい射宇宙の選択を強制するグローバルinstanceにはしていない。
`moduleDerivedLift`・`_fac`・`_unique` は独立の対象/射宇宙 w/w' に対する
指定射を反転する関手の厳密な延長・因子化・一意性。
`moduleDerivedNatTrans_ext` と `moduleDerivedUniversalEquivalence` は
自然変換を含む関手圏の普遍性。Mathlibの既存局所化一般論を再利用する。

`Derived/Evaluation.lean` の `moduleDerivedHomology` は各対象・整数次数の
ホモロジーを局所化へ延長する。
`moduleToDerived_map_isIso_iff` は元の加群射の像が同型になる条件が
ちょうど指定objectwise quasiIsoであることを証明する。
逆向きは延長された評価ホモロジーで検出し、局所化が射を反転することだけから推測しない。
`moduleDerivedEvaluation` は既存 DerivedCategory (ModuleCat A) への評価。
対象の導来圏を使うAPIでは `[HasDerivedCategory.{w} (ModuleCat.{u} A)]` を明示する。
準同型判定の定理自体にはこの選択を仮定しない。

受入入口 `Checks/Derived.lean` は任意可換環・非有界加群・独立宇宙、
標準射宇宙、IsLocalization/HasLocalization、厳密な普遍性・関手圏同値、
導来評価との四角形、ℤ・ZMod 2 の同型判定を検証する。
この入口・StageFive・既存Spectra.StageTwoの同時ビルドは成功（3176 jobs）。
入口の直接実行と主要22宣言の公理監査も成功し、標準公理のみ。累計388宣言。
一般論のsorry・引用axiomは導入していない。

U9全受入は未完。次は全dg自然な加群ホモトピーに対応するcylinderを構成し、
閉零局所化が境界を同一視することを証明する。
そこから閉零/K(D)の指定局所化比較と比較関手の自然同型を完成させる。
共有の射影モデル構造を先行仮定にはしない。共有API不足のブロックは現在ない。
U10のsemifree解像度の存在・Hom計算・三角構造・Verdier商比較・
余積/局所小性・一対象Aの既存導来圏との自然同値も未完であり、目標を保持する。

### 13.18 U9b1：全 dg 自然な cylinder とホモトピーの延長

`Module/TensorUnit.lean` は閉単位/閉零射の逆転置を既存左unitorに同定し、
全作用を持つ `moduleTensorUnitIso` を構成する。
`moduleParamUncurry` は Hom end へのパラメータchain mapをtensor加群からの射に戻し、
パラメータの前合成・単位パラメータの通常射との一致を証明した。

`Complexes/TensorCylinder.lean` は単位複体の既存標準cylinderを `dgInterval` として再利用する。
`tensorIntervalHomotopyEquiv` はその収縮を任意非有界複体へtensorし、
`tensorIntervalProjection_quasiIso` は左unitorを含む射影の準同型性を証明する。
tensorする射が具体的なホモトピー同値なので、対象複体のflatnessは不要。

`Module/Cylinder.lean` の `modulePrecylinder` は interval と加群のtensorから
全次数作用を持つ Mathlib Precylinder を構成する。
射影のobjectwise準同型性、両端が射影のsectionとなることを証明した。
`moduleCylinderDesc` は単位→Hom endのホモトピーを既存複体cylinderから延長し、
両端との合成が元の加群射となる。
`moduleCylinderLeftHomotopy` はMathlibのLeftHomotopyの具体的証人。
ここでは代替モデル圏や一般cylinder理論を構成していない。

受入入口 `Checks/Cylinder.lean` は任意可換環・独立宇宙・非有界加群、
全作用、tensorのホモトピー同値、射影の準同型性、Hom end内のホモトピーの延長、
ℤ・ZMod 2 の一対象例を検証する。
ビルド・直接実行は成功し、主要18宣言はすべて標準公理の範囲内。累計406宣言。
U9全受入は局所化比較の完成・検証を残して未完。U10の目標も保持する。

### 13.19 U9b2：閉零/K(D)の局所化比較と両方向の自然同型、U9受入

`Derived/HomotopyComparison.lean` の `moduleQuasiIso_equalizes_boundary` は、
quasiIsoを反転する任意の関手が全dg自然な境界関係を同一視することを
前段の具体的cylinderで証明する。対象圏の対象/射宇宙w/w'は独立。
`moduleBoundaryFactorsThroughLocalization` と U8 の射クラスの逆像一致により、
Mathlib `HomRel.FactorsThroughLocalization.strictUniversalPropertyFixedTarget'` を適用し、
`moduleToHomotopy ⋙ moduleHomotopyToDerived` が閉零加群圏の指定quasiIsoを局所化することを得る。
一般の商の局所化理論を複製していない。

`moduleDerivedHomotopyEquivalence` は局所化の一意性による
DerivedModuleCategory ≌ HomotopyDerivedModuleCategory。
`moduleDerivedHomotopyComparisonIso` と `moduleDerivedHomotopyInverseComparisonIso` は
両方向の比較関手と指定局所化関手の自然同型。
`moduleHomotopyToDerivedClosed` は主導来加群圏へのK(D)の局所化関手で、
IsLocalization (moduleHomotopyQuasiIso) を証明した。
`moduleToHomotopyDerivedIso` は閉零→K(D)→D(D)と主局所化の比較自然同型。

受入入口 `Checks/DerivedComparison.lean` は、任意可換環・非有界加群・独立宇宙で
指定局所化の同値、両方向の比較自然同型、K(D)からのIsLocalization、
任意のquasiIso反転関手でのホモトピー同一視を検証する。
ビルド・直接実行と主要9宣言の公理監査は成功し、標準公理のみ。

これで U9 の指定局所化、宇宙・普遍性、閉零/K(D)局所化比較が揃った。
受入条件との対応は次のとおり。

| 条件 | 証明・検証入口 |
| --- | --- |
| 指定Wの局所化D(D)と宇宙 | Derived/Basic、Checks/Derived |
| 関手/自然変換を含む普遍性と元の射の同型判定 | Derived/Basic・Evaluation、Checks/Derived |
| 全dg自然な境界が局所化で同一視されること | Module/Cylinder・Derived/HomotopyComparison、Checks/Cylinder・DerivedComparison |
| 閉零圏/K(D)の指定局所化の同値と比較図式 | Derived/HomotopyComparison、Checks/DerivedComparison |

U9を受入済みとし、独立入口 `StageSix.lean`（U0〜U9）を追加した。
U9の3受入入口とStageSix・既存Spectra.StageTwoの同時ビルドは成功（3183 jobs）。
3入口の直接実行ログを照合し、49宣言すべて標準公理のみ。累計415宣言。
担当Leanのsorry・admit・新規axiomは0件。
StageSixのローカルimport閉包は114モジュール（dg76）でSpectra/Paper/Inputs依存なし。
共有ルートimport・既存PerfectComplex・並行作業ファイルは編集していない。

U10は未完。semifreeの定義だけでは完了とせず、任意加群へのsemifree解像度の存在、
acyclicを消すHomと導来Hom計算・選択独立性、K(D)/D(D)の三角構造・Verdier商比較、
余積/局所小性の宇宙、一対象Aと既存DerivedCategoryの自然同値を証明する。
標準局所化の射宇宙をより小さい宇宙へ下げることは、証拠を得るまで主張しない。
共有の射影モデル比較は別のD4m合流点。共有API不足による現在のブロックはない。
U10までの目標を保持する。

### 13.20 U10d1：一対象Aの既存導来圏との同値・局所化比較・整合的shift

U10の独立に進められる一対象比較を先行した。semifree解像度の存在や一般三角構造の
証明を省略することはなく、U10全受入は引き続き未完。
`Derived/Ring.lean` は `ringModuleQuasiIso_iff` と `ringModuleLocalizer` により、
既存閉零加群圏同値が指定quasiIsoを保ち、反映することを証明する。
Mathlibの誘導localizerと圏同値の局所化一般論を用い、
U9の `moduleDerivedEvaluation` 自体が圏同値となることを証明した。
`ringDerivedEquivalence` は主導来加群圏と既存 DerivedCategory (ModuleCat A) の同値。
`ringDerivedEquivalence_fac` は主局所化、既存閉零加群圏同値、既存複体の局所化の
四角形を結ぶ自然同型。

`Derived/Shift.lean` は任意Dの導来評価の因子化をLocalization.Liftingに登録し、
既存 `Functor.commShiftOfLocalization` により整数shiftのzero/add coherenceを運ぶ。
因子化自然同型のhomもNatTrans.CommShiftを満たす。
一対象比較の通常/導来関手と局所化比較自然同型も整合的なshiftを保存する。
一般の局所化shift理論を複製していない。

対象側の既存導来圏には `[HasDerivedCategory.{w} (ModuleCat.{u} A)]` を明示し、
任意の選択された射宇宙wで比較する。主導来加群圏の標準射宇宙はmax (u+1) vのまま。
任意可換環・非有界複体を扱い、モデル構造・noetherian・体・flatnessを仮定しない。

受入入口 `Checks/DerivedRing.lean` は任意A/独立射宇宙、圏同値、HasShift/CommShift、
自然同型のshift整合性、ℤ・ZMod 2の標準宇宙での比較を検証する。
ビルド・直接実行は成功し、主要15宣言はすべて標準公理の範囲内。累計430宣言。
U10の一般三角構造・余積が未構成なので、それらの保存についてはまだ完了を主張しない。
semifree解像度の存在・Hom計算・選択独立性・Verdier商比較・局所小性も残る。

### 13.21 U10b1：Hom end による homotopically projective 性と代表加群

`Derived/HomotopicallyProjective.lean` は `moduleHomotopicallyProjective` を
閉零加群圏のObjectPropertyとして定義する。
指定objectwise acyclic加群Nに対して全次数Hom end Hom_D(M,N)がacyclicとなる性質。
評価複体のK-projective性で代用せず、Mathlibの複体IsKProjectiveとは別の定義とする。

`representable_homotopicallyProjective` は既存全次数dg Yoneda同型でこの性質を証明する。
対象Dがu-smallという既存Hom endの仮定以外、Hom_DのA上projectivityやflatnessは不要。
主加群圏の真の同型での不変性、IsClosedUnderIsomorphisms、零加群の判定も証明した。

受入入口 `Checks/HomotopicallyProjective.lean` は任意可換環・非有界加群・独立宇宙、
代表/零加群、同型不変性と全次数Homの条件を検証する。
この入口・Checks/DerivedRing・StageSix・既存Spectra.StageTwoの同時ビルドは成功（3185 jobs）。
両新入口の直接実行・主要20宣言の公理監査も成功し、標準公理のみ。累計435宣言。
一般論のsorry・引用axiomは追加していない。

U10全受入は未完。次はsphere/diskとfree_xによるcellの具体化、
shift・余積・semifree filtrationでの上記性質、任意加群へのsemifree解像度の存在と
導来Hom計算を証明する。三角構造・Verdier商比較・余積/局所小性の宇宙、
一対象同値によるそれらの保存も残る。共有の小対象/転送一般論は複製しない。
現時点で共有API不足によるブロックはなく、U10までの目標を保持する。

### 13.22 U10a1：sphere/diskと自由cellの生成元・微分・収縮

`Complexes/Cells.lean` は固定版Mathlibのsingle/doubleを再利用する。
`complexSphere A n` は次数nに集中するA、`complexDisk A n` は次数n→n+1の恒等微分。
`complexSphereHomEquiv` はsphereからの射を次数nのcycleに、
`complexDiskHomEquiv` はdiskからの射を次数nの任意の要素に同定する。
diskの同値の値域自然性、上の生成元の像が下の像の微分であることを証明した。
`complexSphereToDisk A n` の型は sphere (n+1)→disk n。
`complexSphereToDisk_comp` はこの境界への前合成が微分を取る操作となることを示す。
コチェイン次数の規約をホモロジー次数と混同しない。

`Complexes/DiskContractible.lean` は上の次数n+1から下の次数nへ戻す
`complexDiskContractingCochain`（次数−1）を構成し、δh=idを証明する。
`complexDiskContractingHomotopy`・acyclic性と、任意非有界複体へのtensorによる
収縮・acyclic性の保存を証明した。具体的ホモトピーをtensorするのでflatnessは不要。

`Module/Cells.lean` は既存free/evaluation随伴を再利用し、全次数作用を持つ
`freeSphere`/`freeDisk`、`freeCellBoundary`、cycle/斉次生成元を指定するHom同値を公開する。
`freeDiskHomEquiv_naturality` と `freeCellBoundary_comp` は値域自然性と微分の比較。
`freeDisk_acyclic`、`freeDisk_zeroTo_quasiIso` はHom_DのA上flatnessを要求せず、
零加群→自由diskが指定objectwise quasiIsoとなることを証明する。
加群としての全次数作用は保持するが、この段階でfreeDiskのHom end内の収縮や
任意のfree(J)-cellの準同型性まで証明済みとはしない。

受入入口 `Checks/Cells.lean` は任意可換環・全整数次数・独立宇宙、
生成元のHom同値、境界/微分の一致、収縮の次数−1、任意複体とのtensor、
自由diskの準同型性、ℤの負次数とZMod 2の正次数を検証する。
添字族D×ℤがu-smallであることも確認する。
この入口・StageSix・既存Spectra.StageTwoの同時ビルドは成功（3186 jobs）。
直接実行・主要31宣言の公理監査も成功し、標準公理のみ。累計466宣言。
一般論のsorry・新規axiomは追加していない。

共有G2への具体的入力は、Iのfamily `freeCellBoundary A D x n` と
Jのfamily `moduleZeroTo A D (freeDisk A D x n)`、そのHom表現・Jの各射の準同型性。
一般小対象論・転送は複製しない。domainのtransfinite smallnessと
free(J)-cellの準同型性の証拠はまだ残る。独立のsemifree解像度経路を継続する。
次はcellによるliftの具体的判定、shift/余積/filtrationでのhomotopically projective性、
任意加群へのsemifree解像度の存在と導来Hom計算。
三角構造・Verdier商比較・余積/局所小性・一対象同値による保存も未完であり、
U10全受入の目標を保持する。

### 13.23 U10a2：生成cell I/Jの右持ち上げクラスの具体的同定

`Module/CellLifting.lean` の `moduleSurjectiveAt`/`moduleDegreewiseSurjective` は
評価の各次数で全射となる射のクラス。Mathlib ModuleCatのepiとの一致を証明した。
`freeDisk_lifting_iff_surjective` は指定x/nの零→自由diskの右liftと全射性の同値。
具体的射族Jを `freeDiskInclusions` としてMorphismProperty.ofHomsで構成し、
`freeDiskInclusions_rlp_eq` により J.rlp = moduleDegreewiseSurjective を証明する。
このクラスのretract閉性・同型との両立はMathlibのrlp一般論から得る。

sphereのHom同値の値域自然性を追加し、`moduleBoundaryLiftAt` と
`freeCellBoundary_lifting_iff` により境界cellのliftを生成元の方程式に同定する。
条件は、次数n+1のcycle zと次数nのyが f(z)=d(y) を満たすとき、
d(t)=zかつf(t)=yとなる次数nのtが存在すること。
全次数でこの条件が成り立てば、まずd(y)のcycleをliftし、次にyをliftすることで
次数ごとの全射性を証明する。

`Complexes/CellCriterion.lean` は同じ条件を複体射で定義する。
coneのcycleを標準二射影で分解し、coneの微分の符号を使って
`complex_quasiIso_of_boundary_lifting` を証明した。
逆方向の `complex_boundary_lifting_of_surjective_quasiIso` は、coneのacyclic性で境界を選び、
低い次数の全射性で補正して生成元の同時liftを得る。
任意可換環・非有界複体で成立し、体・flatness・projectivityを仮定しない。

Iを `freeCellBoundaries` として構成し、`freeCellBoundaries_rlp_eq` により
I.rlp = moduleDegreewiseSurjective ⊓ moduleQuasiIso を証明した。
局所化で反転されるクラスはU8/U9の指定objectwise quasiIsoのまま。
一般認識定理やモデル構造を新しく定義していない。

受入入口 `Checks/CellLifting.lean` は任意可換環・独立宇宙・非有界加群、
個別disk/boundaryのlift条件、I/Jの右liftクラス、epi判定、retract/同型との両立、
ℤの負次数とZMod 2の正次数を検証する。
この入口・StageSix・既存Spectra.StageTwoの同時ビルドは成功（3188 jobs）。
直接実行・主要25宣言の公理監査も成功し、標準公理のみ。累計491宣言。
一般論のsorry・新規axiomは0件。

共有 `Transfer/EvaluationSmallness.lean` の
`SerrePositivity.ModelGeneration.EvaluationFamily.generators_smallObjectArgument` と
`Transfer/Recognition.lean` を読み直した。
共有APIは利用可能であり、M5に一般小対象論・認識定理を複製しない。
具体的に残る入力は、regular κ:Cardinal.{u} と
`[Fact κ.IsRegular]`/`[OrderBot κ.ord.ToType]` を選んだ上で、
source Ch(A) のsphere/zeroのdomainについて `IsCardinalPresentable _ κ` の証拠、
生成射族の対応と `.HasSmallObjectArgument.{u}`、および J.rlp.llp ≤ moduleQuasiIso のacyclicity。
free/evaluation随伴と評価のu-small余極限保存はU6/U7の既存入力を再利用できる。
今回のI/J.rlpの等式は共有認識定理の具体的lifting入力となる。

U10全受入は未完。次はcellの段階的付加とsemifree filtration、
任意加群へのsemifree解像度の存在、shift/余積/filtrationでのHom計算を証明する。
三角構造・Verdier商比較・余積/局所小性・一対象比較での保存も残る。
導来圏の主経路は局所化で、射影モデル比較はD4mの別合流点として維持する。


### 13.24 U10a3：任意加群への自由disk被覆

`Module/DiskCover.lean` は全対象・整数次数・斉次要素を添字とする自由diskの余積を構成する。
`ModuleDiskCoverIndex` は `[Small.{u} D]` のもとでu-small。
`moduleDiskCoverπ` は各diskの生成元を指定要素へ送り、
`moduleDiskCoverπ_degreewiseSurjective` が全対象・全整数次数の全射性を証明する。
全dg作用と余積はU6/U7の主加群圏APIを再利用する。
この被覆自体の準同型性は主張しない。kernel cycleを後続cellで消すための初期段階である。

受入入口 `Checks/DiskCover.lean` は添字宇宙、全射性、次数ごとのepi、
ℤの負次数とZMod 2の正次数を検証する。
この入口・可算列候補・StageSix・既存Spectra.StageTwoの同時ビルドは成功（3195 jobs）。
直接実行による主要8宣言の公理監査は標準公理のみ。累計499宣言。
U10全受入は未完。次はkernel cell付加、可算列の準同型性と真のsemifree filtrationを証明する。


### 13.25 U10a4：全dg自然なcone延長とkernel cycleのcell付加

`Complexes/ConeDesc.lean` と `Module/ConeDesc.lean` は合成が零となる射のconeからの延長を構成する。
全次数の作用とconeMapの整合性を証明し、成分のchain mapだけで代用しない。
標準包含との合成が元の射となり、coneの左成分に置いたcycleの微分と延長の像を計算する。

`Module/KernelCells.lean` は射fのkernel内の全対象・全次数のcycleをu-smallな添字とする
自由sphereの余積と、その射のconeによる付加を構成する。
`moduleKernelCellStep_fac` は元の値域への射の延長を、
`moduleKernelCellStepπ_degreewiseSurjective` は全射性の保存を証明する。
`moduleKernelCellStep_killsInKernel` は各cycleの像が境界となり、選んだ境界の原像も
延長された射のkernel内にあることを証明する。微分+1・cell生成元の次数nを維持する。

受入入口 `Checks/KernelCells.lean` のビルドと直接実行は成功。
主要28宣言の公理監査は標準公理のみ。累計527宣言。
U10全受入は未完。次は可算列の余極限で全kernel cycleが消えることと、semifree filtrationを証明する。


### 13.26 U10a5：可算cell列と有限段のkernel cycleの消去

`Module/ResolutionSequence.lean` は自由disk被覆を第0段とし、kernel cell付加を反復する
ℕ-indexedな図式をOver M内で構成する。各段の射の整合性と全射性を証明し、
主加群圏の既存余極限から `moduleResolutionCandidateπ` を構成する。
この射は次数ごと全射。標準包含と比較射の合成、隣接段の包含の一致も証明する。
`moduleResolutionCandidate_killsStage` は有限段のkernel内のcycleの像が候補で境界となり、
その原像も候補のkernel内にあることを証明する。

受入入口 `Checks/ResolutionSequence.lean`・前段入口・StageSix・既存Spectra.StageTwoの
同時ビルドは成功（3196 jobs）。直接実行の主要13宣言は標準公理のみ。累計540宣言。
これは解像度の候補であり、準同型性とsemifree性の受入前には解像度とは呼ばない。
次はfiltered余極限のcycleの有限段表示を証明し、全kernel cycleの消去へ接続する。
U10全受入は未完。semifree filtration・Hom計算・三角構造等の残項目を保持する。


### 13.27 U10a6：可算cell候補のobjectwise準同型性

`Complexes/FilteredCycles.lean` は任意可換環上の非有界複体の可算filtered余極限について、
cycleがある有限段のcycleの像であることを証明する。
MathlibのModuleCat忘却関手のfiltered余極限保存と具体圏の表示APIを再利用し、
微分が零となる後続段まで添字を進める。宇宙uの保存証拠から添字宇宙0への縮小を明示する。

`Module/ResolutionQuasiIso.lean` は評価の余極限保存によりこの表示を主加群圏に適用する。
`moduleResolutionCandidate_kernelCycle_boundary` はkernel内の全cycleが、同じkernel内の
原像を持つ境界となることを証明する。
次数ごとの全射性とこの消去を用いて `moduleResolutionCandidate_boundaryLift` を証明し、
U10a2の境界持ち上げ判定から `moduleResolutionCandidateπ_quasiIso` を得る。
これで任意加群Mへの次数ごと全射かつ指定objectwise quasiIsoな可算cell候補が得られた。
モデル構造・flatness・体・noetherian性を仮定しない。

受入入口 `Checks/ResolutionQuasiIso.lean` は一般A/D、I.rlpとの整合性、全整数次数のlift、
ℤとZMod 2の非有界加群で検証する。
この入口・StageSix・既存Spectra.StageTwoの同時ビルドは成功（3201 jobs）。
直接実行の主要5宣言の公理監査は標準公理のみ。累計545宣言。
担当Lean範囲のsorry/admit/新規axiomは0件、文書検査は21 Markdown/311参照で0 failures。

U10全受入は未完。cell候補の真のsemifree filtration（初期diskのsphere段階への分解、
各cone付加の次数付き分裂と自由な商、余極限の網羅性）を次に証明する。
その後、semifreeのHom endがacyclicを消すこと、導来Hom計算と選択独立性、
K(D)/D(D)の三角構造とVerdier商比較、余積・局所小性の宇宙、一対象同値の三角形・余積保存を完成する。
共有の一般小対象論・モデル圏・Quillen・SM7は複製せず、D4mの合流条件は§13.23のまま。
この候補についてsemifree性を未証明のまま主張しない。


### 13.28 U10a7：cone付加の全次数分裂と商の普遍性

`Module/GradedSplit.lean` の `ModuleGradedSplit` は既存主dg加群圏の拡大について、
微分を忘れた次数付き加群でのsection/retractionと全斉次作用との可換性を記録する。
新たなdg圏・dg加群モデルは作らない。包含・射影は主圏のchain mapのまま。
分裂から次数ごとのmono/epi、主加群圏のmono/epi、各評価次数の短完全列、
各評価複体のcokernelを証明する。

`Complexes/ConeGradedSplit.lean` は標準coneの左sectionをconnecting mapの符号に合わせた
-inlとして構成し、右retraction、分裂恒等式、全整数次数の作用との可換性を証明する。
左成分のshiftに入る(-1)^pを明示し、sectionをchain mapとは主張しない。
`Module/ConeGradedSplit.lean` はこれを全dg自然な加群の分裂として構成する。

`Module/GradedSplitCokernel.lean` は各評価のcokernelからの延長が全次数作用と可換することを
射影の次数ごとのepi性から証明し、主dg加群圏の真のcokernel普遍性を与える。
`moduleConeInrCokernel` により N→cone(f) の商がM[1]であることを主圏内で確定した。
評価だけの商の代用ではない。

受入入口 `Checks/ConeGradedSplit.lean` は全次数自然性、主圏のcokernel普遍性、
任意可換環/独立宇宙、ℤの負次数・ZMod 2の正次数での短完全性を検証する。
この入口・前段準同型入口・StageSix・既存Spectra.StageTwoの同時ビルドは成功（3206 jobs）。
直接実行の主要31宣言は標準公理の範囲内。累計576宣言。
U10全受入は未完。次は可算cell列の各商とfiltrationの埋込みを確定し、
初期diskのsphere分解と商の自由性、semifreeのHom計算へ進む。


### 13.29 U10a8：cell列の商・filtrationの包含と網羅性

`Module/ResolutionGradedSteps.lean` は各kernel cell付加について全次数の分裂と真のcokernelを
公開する。商の対象は `moduleKernelCellSource A D f` の+1 shiftである。
`moduleKernelCellStepι_mono` と `moduleResolutionTransition_mono` により付加はmono。
可算列の任意の有限段間の射について、主圏のmonoと全評価次数のmonoを証明した。

`moduleResolutionCandidateι_degreewiseMono` はfiltered余極限の具体的表示と
有限段間のmono性を使い、各有限段の余極限候補への射が全評価次数でmonoであることを証明する。
`moduleResolutionCandidateι_mono` は主dg加群圏のmono性。
`moduleResolutionCandidate_element_rep` は各評価次数の任意の要素が有限段の像に属することを証明する。
従って可算cell列は包含を持つ網羅的filtrationとなる。

受入入口 `Checks/ResolutionGradedSteps.lean` は各商の主圏での普遍性、分裂、
任意の有限段間と余極限への包含、全評価次数のmono、網羅性を検証する。
この入口・StageSix・既存Spectra.StageTwoの同時ビルドは成功（3206 jobs）、警告なし。
直接実行の主要10宣言は標準公理のみ。累計586宣言。
担当Lean範囲のsorry/admit/新規axiomは0件。
全体文書検査 `python3 scripts/check_documentation.py` は、並行K系列のroot importに追加された
`KTheory/Adams/TensorCubeLowMixedSections.lean` のoleanが存在せず、export段階で停止した。
この実行を成功とは記録しない。担当dg入口と既存Spectra.StageTwoの対象ビルドは上記のとおり成功。
共有root/並行K系列は編集せず、この制限を報告する。

U10全受入は未完。semifree性の残る具体的証明は、初期自由disk段を自由sphereの二段に分解し、
後続商 `(∐ freeSphere)[1]` を自由sphereの余積として主dg加群圏で同定すること。
それらの証明を伴ったsemifree filtrationと、任意加群への既存準同型射を結び付ける。
続いてHom endのacyclic性・導来Homと選択独立性、三角構造・Verdier商、余積・局所小性、
一対象比較の三角形/余積保存を完成する。共有一般論の重複はなく、D4m条件は§13.23を維持する。


### 13.30 U10a9：各自由diskの二段sphere filtration

`Complexes/DiskFiltration.lean` は次数n+1のsphere→disk n→sphere nを構成する。
標準double/singleの射を再利用し、合成が零であること、次数0のsection/retraction、
分裂恒等式と各次数のMathlib標準Splitting/ShortExactを証明した。
section/retractionはchain mapとは主張せず、微分を忘れた次数付き分裂として扱う。

`Complexes/TensorGradedZero.lean` はchain条件のない次数0 cochainを任意複体で右tensorする。
加法・零・単位・合成・chain mapとの一致、純tensor上の公式を証明し、
左tensorの全次数dg作用との可換性を符号(-1)^(pi)込みで検証する。
これは一般モデル圏の転送ではなくCh(A)の具体的な次数付き計算である。

`Module/DiskFiltration.lean` はこれらを自由加群へ運び、
`freeDiskGradedSplit` により自由diskが上次数自由sphereと下次数自由sphereの拡大であり、
全斉次作用に関して分裂することを証明する。
`freeCellBoundary_mono`、`freeDiskToSphere_epi`、`freeDiskSphereCokernel` により
主dg加群圏の包含と真の商を確定する。任意A・非有界・独立対象宇宙で、flatness等の追加仮定はない。

受入入口 `Checks/DiskFiltration.lean` は全次数作用、各評価次数の短完全性、
主圏のcokernel普遍性、ℤの負次数・ZMod 2の正次数を検証する。
この入口・前段filtration入口・StageSix・既存Spectra.StageTwoの同時ビルドは成功（3210 jobs）。
直接実行の主要36宣言は標準公理のみ。累計622宣言。
全体文書検査の並行K系列importによる制限は§13.29の記録を維持する。

U10全受入は未完。各自由diskの二段分解は完了したが、初期disk被覆全体への余積による接続は残る。
次はu-small余積で全次数分裂が保たれることを証明し、初期被覆のsphere二段分解へ適用する。
後続商のshiftと余積・自由sphereとの同定を合わせ、証明付きsemifree filtrationを完成する。
続くHom計算・三角構造・Verdier商・余積/局所小性・一対象比較の残項目は引き続き保持する。


### 13.31 U10a10：u-small余積による全次数分裂の保存

`Module/GradedCoproduct.lean` は評価の各次数で余積包含が余積を与えることを、
既存moduleEvaluationの余極限保存とMathlibのcofan保存APIから構成する。
chain条件のない次数付き成分族を余積へ延長し、包含・合成・単位・零・加法・
通常加群射のSigma.mapとの一致を証明する。
`moduleCoproductGradedComponent_naturality` は各余積包含の全次数自然性から
全斉次作用との可換性を証明する。
`moduleCoproductGradedSplit` がu-smallな任意族の全次数分裂を余積に運ぶ。
添字Jの対象宇宙wは独立、仮定は `[Small.{u} J]`。

受入入口 `Checks/GradedCoproduct.lean` は一般族、主圏のmono/epi・cokernel普遍性、
各評価次数の短完全性、可算族と空族の宇宙を検証する。
この入口・初期被覆の適用入口・StageSix・既存Spectra.StageTwoの同時ビルドは成功（3198 jobs）。
直接実行の主要13宣言の公理監査は標準公理のみ。累計635宣言。
U10全受入は未完。共有一般モデル圏/転送一般論は複製していない。


### 13.32 U10a11：初期自由disk被覆全体の二段sphere分解

`Module/DiskCoverFiltration.lean` は全斉次生成元を添字とする被覆について、
上次数自由sphere族 `moduleDiskCoverUpperFamily` と下次数自由sphere族
`moduleDiskCoverLowerFamily` を構成する。
`moduleDiskCoverBoundary` は上次数族の余積から初期disk被覆への包含、
`moduleDiskCoverQuotient` は被覆から下次数族の余積への射影。
各自由diskのU10a9の分裂をU10a10で余積へ運び、
`moduleDiskCoverGradedSplit`・包含のmono性・射影のepi性を証明した。
`moduleDiskCoverSphereCokernel` は主dg加群圏の真の商の普遍性。
これで初期disk被覆全体のsphere二段分解が揃った。

受入入口 `Checks/DiskCoverFiltration.lean` は一般A/D、主圏の分裂と商、
各評価次数の短完全性、ℤとZMod 2での適用を検証する。
前段入口・StageSix・既存Spectra.StageTwoとの同時ビルドは§13.31のとおり成功。
直接実行の主要8宣言は標準公理のみ。累計643宣言。
U10全受入は未完。次は後続商 `(∐ freeSphere)[1]` の自由sphere余積との同定と、
初期二段分解を含めた証明付きsemifree filtrationの構成。
Hom計算・三角構造・Verdier商・余積/局所小性・一対象比較の残項目は保持する。
全体文書検査の並行K系列importによる制限は§13.29に記録済み。


### 13.33 U10a12：自由sphereのshiftと後続cell商の自由性

`Complexes/TensorShift.lean` は既存sign-free左tensor–shift比較について、
全斉次Homへのdg自然性を証明する。shift作用の(-1)^(sp)とtensor作用の(-1)^(p(i+s))を
成分上で照合し、元の(-1)^(pi)と一致することを示す。
`Module/TensorShift.lean` はその比較を全dg自然な主加群同型へ運び、free_xのshift比較を公開する。
`Module/FreeSphereShift.lean` はMathlibのsingleFunctors.shiftIsoを再利用し、
コチェイン規約の `sphere n[s] ≅ sphere (n-s)` と主圏の自由sphereの同型を構成する。

`Module/ShiftCoproduct.lean` はshiftの同値関手としての余積保存をMathlibから再利用し、
u-small余積とshiftの比較、およびshiftされた自由sphere余積の自由sphere余積表示を構成する。
`Module/ResolutionFreeQuotients.lean` の `moduleKernelCellQuotientFreeIso` により
真の商 `(∐ freeSphere(n+1))[1]` が次数nの自由sphere余積であることを主圏で確定した。
一般shift/余積/モデル圏一般論の重複はない。

受入入口 `Checks/ShiftCells.lean` は任意A/D・独立添字宇宙、全整数shift、
後続商の主圏の同型、ℤの正shift・ZMod 2の負shiftを検証する。
この入口・StageSix・既存Spectra.StageTwoの同時ビルドは成功（3211 jobs）。
直接実行の主要12宣言は標準公理のみ。累計655宣言。
U10全受入は未完。次は初期二段分解と各自由商を網羅的filtrationのデータにまとめ、
既存準同型射とともに任意加群へのsemifree解像度の存在を証明する。
その後のHom計算・三角構造・Verdier商・余積/局所小性・一対象比較の目標は保持する。


### 13.34 U10a13：証明付きsemifree filtrationと任意加群への解像度の存在

`Module/Semifree/Basic.lean` は `ModuleSphereFreePresentation` にu-smallな自由sphere余積の
具体的表示を保持する。添字のambient宇宙はmax u v、Hom/加群の宇宙はu。
`ModuleSemifreeFiltration` はℕ-indexedな段階と遷移、初期段の自由sphere表示、
各商の自由sphere表示と全次数分裂、coconeとIsColimit、最終対象への同型を保持する。
各商が主dg加群圏での真のcokernelであることも公開する。
主モデルを変更せず、単なるI-cell候補という定義では代用しない。

`Module/Semifree/Resolution.lean` は上次数sphere余積を初期段とし、
第1段をdisk被覆、その後を既存可算kernel cell列とする。
新しい列のcoconeのtailを既存列のcoconeへ制限し、余極限の普遍性を両方向に証明する。
各段の商・分裂・自由sphere表示を既存APIから組み立て、
`moduleResolutionSemifreeFiltration` と `moduleResolutionCandidate_semifree` を証明した。

`exists_semifree_resolution` は任意MについてPとq:P→Mを与え、
semifree性・次数ごとの全射性・指定objectwise quasiIsoを同時に証明する。
任意可換環・非有界複体・独立対象宇宙 `[Small.{u} D]` で成立し、
体・flatness・noetherian性・射影モデル構造を仮定しない。
これでU10aのsemifree解像度の存在を、filtrationと実際の準同型射の証明込みで満たした。

受入入口 `Checks/Semifree.lean` は一般A/Dの存在定理、実際のfiltration、余極限普遍性、
各段のmono性・主圏のcokernel・商の自由sphere表示、ℤとZMod 2の適用を検証する。
この入口・ShiftCells・StageSix・既存Spectra.StageTwoの同時ビルドは成功（3219 jobs）。
直接実行の主要18宣言は標準公理のみ。累計673宣言。
担当Lean範囲のsorry/admit/新規axiomは0件、担当diff --checkは成功。
全体文書検査の並行K系列importによる制限は§13.29の記録を維持する。

U10全受入は未完。次はfreeSphere・余積・このfiltrationについてHom endがacyclicを消すことを証明し、
導来Hom計算と解像度の選択独立性へ接続する。
K(D)/D(D)の三角構造・Verdier商比較、余積・局所小性の宇宙、一対象同値の三角形/余積保存も残る。
共有一般モデル圏/Quillen/転送/SM7は複製せず、D4m条件は§13.23のまま。


### 13.35 U10b2：自由sphereの全次数Homとhomotopically projective性

`Complexes/SphereHom.lean` はMathlibのfromSingleEquivを再利用し、
`Hom(sphere n,K)` の次数pの要素を `K.X (n+p)` へ同定する。
A線形同値・零・全微分との整合性を証明し、値域Kのacyclic性からHom複体のacyclic性を導く。
Homの次数を一律にshiftと見なして微分の符号を省くことはせず、全p/qの成分式を証明する。

`Derived/FreeSphereProjective.lean` の `freeSphere_homotopicallyProjective` は
free/evaluationの全次数Hom chain isoから主Hom endのacyclic性を証明する。
各評価複体のK-projective性では代用せず、任意の小さいdg圏上で成立する。
任意可換環・非有界複体・全整数次数で、Hom_Dのflatness/projectivityは不要。

受入入口 `Checks/FreeSphereProjective.lean` はA線形性・微分・全Hom endの条件、
ℤの負次数とZMod 2の正次数での適用を検証する。
この入口・ProductAcyclic・StageSix・既存Spectra.StageTwoの同時ビルドは成功（3193 jobs）。
直接実行の主要6宣言は標準公理のみ。累計679宣言。
U10全受入は未完。余積とfiltrationでの上記性質の証明を次に接続する。


### 13.36 U10b3a：acyclic複体のu-small直積

`Complexes/ProductAcyclic.lean` は複体の直積射影が各次数でも直積を与えることを、
Mathlibの評価の極限保存から構成する。
各cycleの境界の原像を成分ごとに選び、各次数の直積普遍性で一つの原像に組み立てる。
`complexProduct_acyclic` は任意のu-smallなacyclic非有界複体族の直積がacyclicとなることを証明する。
添字Jのambient宇宙wは独立で、必要な仮定は `[Small.{u} J]`。

受入入口 `Checks/ProductAcyclic.lean` は一般族・可算族・空族・各次数の直積普遍性を検証する。
同時ビルドは§13.35のとおり成功。直接実行の主要3宣言は標準公理のみ。累計682宣言。
担当Lean範囲のsorry/admit/新規axiomは0件、担当diff --checkは成功。
全体文書検査の並行K系列importによる制限は§13.29の記録を維持する。

U10全受入は未完。この直積補題だけから余積加群のHom endやfiltrationの逆極限のacyclic性は主張しない。
次は `Hom_D(∐ M_j,N) ≅ ∏ Hom_D(M_j,N)` を主Hom endのchain isoとして、
全斉次作用・包含との整合性付きで証明し、自由sphere余積のhomotopically projective性へ適用する。
filtrationでは次数付きdg分裂からHom制限の次数ごとの全射性とkernelの同定を得て、
互換な境界の原像を可算的に選ぶ証明が必要。一般の逆極限がacyclic性を保つとは仮定しない。
その後、導来Hom計算・選択独立性、三角構造・Verdier商、余積・局所小性、
一対象比較の三角形/余積保存を完成する。共有一般モデル圏等の重複はしない。


### 13.37 U10b3b：評価の反映と固定複体とのtensorの余極限保存

`Module/EvaluationReflects.lean` は主加群射の各評価が同型なら逆射も全dg自然であることを使い、
主圏の同型性を反映する。各評価の余極限が存在する図式について、
全評価で余極限となるcoconeが主圏でも余極限となることをU7の実際の構成から証明する。
大きい図式には評価の余極限存在を明示し、smallな図式で自動的に得る。

`Module/TensorSource.lean` は固定複体Kとのtensorを加群変数の関手として構成する。
全斉次作用との可換性・関手法則・評価との比較を証明し、
`moduleTensorLeftPreservesColimit` によりu-small図式の全余極限を保存する。
Kのflatnessを仮定しない。これは余極限保存であり、tensorの一般の完全性を主張しない。
Ch(A)固有の入力であり、共有モデル圏/Quillen/転送一般論は複製しない。

受入入口 `Checks/TensorSource.lean` は評価の反映、各次数のtensor射、
独立した図式の対象・射宇宙、可算余積の保存を検証する。
この入口・CoproductHom・StageSix・既存Spectra.StageTwoの同時ビルドは成功（3203 jobs）、警告なし。
直接実行の主要9宣言は標準公理のみ。累計691宣言。
U10全受入は未完。次にこの実際の余積保存をHom endの直積表示へ適用する。


### 13.38 U10b3c：余積の全Hom endの直積表示とhomotopically projective性

`Module/ParamCurry.lean` はtensor加群からの射と主Hom endへのパラメータ付きchain mapの
転置・逆転置の両方向一致を公開し、加群への前合成との整合性を証明する。
全次数の自然性は既存ModuleParamTransを通し、通常の自然変換へ弱めない。

`Module/CoproductHom.lean` は任意のu-smallな族に対して
`moduleCoproductHomIso : Hom_D(∐ M_j,N) ≅ ∏ Hom_D(M_j,N)` をchain isoとして構成する。
tensorの実際の余積保存から任意パラメータのliftを構成し、直積の普遍性を証明する。
`moduleCoproductHomIso_hom_π` は各直積射影が余積包含への前合成であることを証明する。
Z⁰/H⁰だけの同値で代用しない。

`Derived/CoproductProjective.lean` はHom endの直積表示と§13.36を使い、
homotopically projectiveな加群のu-small余積が再びhomotopically projectiveであることを証明する。
自由sphere余積の表示を持つ加群、従ってsemifree filtrationの初期段と各商についても
この性質を証明した。ここではfiltration全体の性質はまだ主張しない。

受入入口 `Checks/CoproductHom.lean` は一般A/D・独立添字宇宙、chain isoと包含の比較、
転置の往復、homotopically projective性、自由sphere表示とfiltrationの商、
ℤの可算正次数族とZMod 2の可算負次数族を検証する。
同時ビルドは§13.37のとおり成功。直接実行の主要17宣言は標準公理のみ。累計708宣言。
担当Lean範囲のsorry/admit/新規axiomは0件。
今回の `python3 scripts/check_documentation.py` は21 Markdown/311参照で0 failures。
§13.29で記録した並行K系列の未ビルドimportによる停止は、今回の実行では解消を確認した。
共有rootと並行系列のソースは編集していない。

U10全受入は未完。次は次数付き分裂に対するHom endのkernel同定と制限射の次数ごとの全射性を証明し、
各有限段のacyclic性と可算逆極限での互換な境界の原像の構成へ進む。
一般の逆極限の完全性は仮定しない。続いて導来Hom計算・選択独立性、三角構造・Verdier商、
余積・局所小性、一対象比較の三角形/余積保存を完成する。


### 13.39 U10b4a：主Hom endの全次数要素の構成と外延性

`Complexes/DiskGenerator.lean` はdiskからの射の逆構成について下の生成元の像を公開する。
`Module/HomElements.lean` は、全斉次作用に対してKoszul符号付きで自然なcochain族を
主Hom endの任意次数の要素へ構成する。diskの普遍性と既存equalizerを使用し、
cycle条件は要求しない。左右の豊穣自然性の成分公式、構成した要素の各射影、
射影による要素の外延性、任意の要素の全次数自然性、成分からの再構成の一致、
Hom微分の各射影との可換性を証明した。
これを次数付き分裂のretraction/sectionへ適用し、Hom制限射の次数ごとの分裂へ接続する。

`Checks/HomElements.lean` は一般A/Dと全整数次数で構成・再構成・外延性・微分を検証する。
同入口・StageSix・既存Spectra.StageTwoと次段のGradedSplitElementsの同時ビルドは成功
（3195 jobs）。直接実行による主要13宣言の公理監査は標準公理のみ。累計721宣言。
共有tensor基盤のimport整理で失われた依存はdg側で明示した：HomComplexからMathlibの
ModuleCat.Abelian、Biproductから既存PerfectComplex.CochainBiproductを再利用する。
共有root・PerfectComplex・共有基盤のソースは編集していない。
全体文書検査は並行K系列の未ビルドCyclicTwoFamily.oleanで停止し、成功とは扱わない。

U10全受入は未完。次数付き分裂に対するHom制限の次数ごとの全射性・kernel同定、
semifree全体のhomotopically projective性、導来Hom計算・選択独立性、三角構造・
Verdier商・余積/局所小性・一対象比較の保存性を引き続き完成する。
共有モデル圏一般論への新しい不足要求はない。


### 13.40 U10b4b：次数付き分裂から得られるHom制限の全射性

`Module/HomElementComposition.lean` は主Hom endの豊穣順合成を各射影で計算し、
次数p/qでのKoszul符号を明示する。通常の加群射による前合成の全次数成分式も公開する。
`Module/GradedSplitElements.lean` は全斉次作用と可換する次数零cochain族をend要素にし、
`ModuleGradedSplit` のretraction/sectionへ適用する。
retractionとの豊穣合成により `homRestrictionSection` を構成し、
包含への前合成との合成が任意次数qで恒等となること、従って
`homRestriction_surjective` を証明した。これらの分裂にchain map条件は課していない。

`Checks/GradedSplitHom.lean` は一般の分裂とsemifree filtrationの各遷移への適用を検証する。
同入口・StageSix・既存Spectra.StageTwoの同時ビルドは成功（3202 jobs）。
直接実行の主要12宣言は標準公理のみ。累計733宣言。
担当Leanにsorry/admit/新規axiomは0件。文書検査の並行K系列olean制限は§13.39のとおり。

U10全受入は未完。次は商からの前合成の単射性、Hom制限のkernel同定、
次数ごとの短完全列を確定し、有限段と可算filtration全体のHom acyclic性へ接続する。
導来Hom・選択独立性・三角構造・Verdier商・余積/局所小性・一対象比較の保存性も残る。


### 13.41 U10b4c：Hom短完全列とsemifree filtrationの有限段

`Module/GradedSplitHomExact.lean` はsectionとの斉次合成でHomのkernelの原像を構成する。
商への前合成との合成が恒等であることから単射性を得て、包含で零となる任意次数の要素を
商へ因子化する。全次数分裂のdecompositionを使い、各射影で因子化の一致を証明する。
`homShortComplex` と `homShortComplex_shortExact` は
`Hom_D(P,T) → Hom_D(N,T) → Hom_D(M,T)` の複体としての短完全性を公開する。

`Derived/GradedExtensionProjective.lean` はMathlibの短完全列のhomology一般論を再利用し、
全次数分裂する拡大で両端がhomotopically projectiveなら中央もそうであることを証明する。
これを初期段と各自由商へ帰納的に適用した
`ModuleSemifreeFiltration.stage_homotopicallyProjective` は全有限段に対して成立する。

`Checks/GradedExtensionProjective.lean` は短完全列・具体的kernel因子化・拡大閉性・有限段を検証する。
同入口・StageSix・既存Spectra.StageTwoの同時ビルドは成功（3214 jobs）。
直接実行の主要11宣言は標準公理のみ。累計744宣言。
担当Leanのsorry/admit/新規axiomは0件。文書検査の制限は§13.39を維持する。

U10全受入は未完。次はHom endの余極限に対する逆極限表示と、次数ごとに全射な
acyclic複体の可算塔で互換な境界の原像を実際に選ぶ補題を接続する。
semifree全体の性質と導来Hom計算・選択独立性、三角構造・Verdier商・余積/局所小性・
一対象比較の保存性は残る。共有一般論への不足APIの新しい要求はない。


### 13.42 U10b5a：全射的acyclic可算塔での互換な境界の原像

`Complexes/TowerPrimitives.lean` はacyclic複体のcycleの境界原像を取り出し、
次数ごとに全射なchain map `r:L→K` について、Kで指定した原像に一致するLの原像を構成する。
任意のLの原像bと指定原像tの差 `t-r(b)` はKのcycleなので境界である。
その一つ下の次数の原像をrに沿って持ち上げ、その微分でbを補正する。
これを依存型のNat再帰で反復し、可算塔の互換なcycle族に対して互換な境界原像族を得る。
`complexTower_compatible_primitives` は全整数次数・任意可換環で成立する。
一般の逆極限の完全性や、degreewise全射だけでのcycleの全射性は仮定していない。

`Checks/TowerPrimitives.lean` は塔全体にわたる存在命題を検証する。
同入口・StageSix・既存Spectra.StageTwoの同時ビルドは成功（3193 jobs）。
直接実行の主要3宣言は標準公理のみ。累計747宣言。
担当Leanのsorry/admit/新規axiomは0件。文書検査の制限は§13.39のとおり。

U10全受入は未完。次は余極限を源とする主Hom endが実際の極限となることを証明し、
この互換な原像族をHom endの要素へ組み立ててsemifree全体の射影性を得る。
導来Hom・選択独立性・三角構造・Verdier商・余積/局所小性・一対象比較の保存性も残る。


### 13.43 U10b5b：余極限を源とする主Hom endの極限普遍性

`Module/ColimitHom.lean` はu-smallな対象型J、独立の射宇宙を持つ図式Fと
指定した実際の余極限cについて、`Hom_D(c.pt,N)` の包含への前合成が
`F.op` 上の全Hom end図式の極限となることを証明する。
任意パラメータ複体Kのconeを逆転置し、Kとのtensorの余極限保存でdescを作り、
再転置してliftを得る。各射影との一致と一意性を同じ普遍性で証明する。
次数零やH⁰のみの表示ではなく、複体の圏でのIsLimitである。

`Checks/ColimitHom.lean` は対象・射の独立宇宙と可算列への適用を検証する。
同入口・StageSix・既存Spectra.StageTwoの同時ビルドは成功（3195 jobs）。
直接実行の主要6宣言は標準公理のみ。累計753宣言。
担当Leanのsorry/admit/新規axiomは0件。文書検査の制限は§13.39を維持する。

U10全受入は未完。次にこの極限普遍性と互換な境界原像の構成を接続して、
semifree全体のhomotopically projective性を完成する。
導来Hom・選択独立性・三角構造・Verdier商・余積/局所小性・一対象比較の保存性は残る。


### 13.44 U10b5c：semifree全体のhomotopically projective性と射影解像度

`Complexes/TowerLimitAcyclic.lean` は複体の評価の極限保存から、極限の各次数の要素を
射影で判定する補題を構成する。可算塔の互換なcycle族に§13.42の補正再帰を適用し、
各次数の極限普遍性で互換な境界原像を組み立て、極限複体のacyclic性を証明する。
仮定は各段のacyclic性と各隣接遷移の全整数次数での全射性である。

`Derived/SemifreeProjective.lean` はfiltrationのHomをこの可算塔と同定する。
§13.41の全有限段の射影性、§13.40のHom制限の全射性、§13.43の実際の極限普遍性から
`ModuleSemifreeFiltration.homotopicallyProjective` と
`moduleSemifree_homotopicallyProjective` を証明した。
`exists_homotopicallyProjective_resolution` は任意加群Mに対しPとq:P→Mを与え、
Pのhomotopically projective性・qの次数ごとの全射性・指定objectwise quasiIsoを証明する。
任意可換環・非有界複体・独立対象宇宙 `[Small.{u} D]` を維持し、
Hom_Dのflatness/projectivityや射影モデル構造を仮定しない。

`Checks/SemifreeProjective.lean` は全Hom endのacyclic性、解像度存在、一般の可算極限と
ZMod 2の実際のresolution candidateへの適用を検証する。
共有基盤更新後の同入口・StageSix・既存Spectra.StageTwoの同時ビルドは成功（3248 jobs）。
直接実行の主要5宣言は標準公理のみ。累計758宣言。
担当Leanのsorry/admit/新規axiomは0件。
全体文書再検査は並行系列の未生成Paper.Section5.CoreLengthPositivity.oleanで停止した。
この制限を解消したとは扱わず、root・並行系列のソースは編集していない。

U10全受入は未完。semifreeの存在と全Hom endによる射影性は揃ったが、
導来Homの計算・解像度の選択独立性はまだ局所化と接続する必要がある。
次は射影的始域からacyclic対象への全dg自然な零ホモトピーを公開し、
quasiIsoによるHomの不変性と局所化内の比較射・選択独立性を証明する。
K(D)/D(D)の三角構造・Verdier商比較、余積・局所小性の宇宙、
一対象同値の三角形/余積保存も引き続き残る。共有一般論の新しい不足要求はない。


### 13.45 U10b6a：射影的始域からacyclic加群への全dg自然なホモトピー

`Derived/ProjectiveHomotopy.lean` はhomotopically projectiveなMとacyclicなNについて、
任意の二射f/g:M→Nが `ModuleHomotopy` で結ばれることを証明する。
両射の閉次数零cycleの差に対し、主Hom endのacyclic性から次数−1の原像を取り出す。
従って全斉次作用に対して自然なホモトピーであり、対象ごとの独立なホモトピーで代用しない。
`moduleHomotopicallyProjective_homotopy_map_eq` はK(D)での像の一致を公開する。

`Checks/ProjectiveHomotopy.lean` は零射とのホモトピーとK(D)での二射の一致を検証する。
同入口・StageSix・既存Spectra.StageTwoの同時ビルドは成功（3199 jobs）。
直接実行の主要2宣言は標準公理のみ。累計760宣言。
共有基盤更新後、今回追加した受入入口全7本を直接Leanで再検査し、
今回の主要52宣言すべてが標準公理のみであることを再確認した。
担当Leanのsorry/admit/新規axiomは0件、担当diff --checkは成功。
全体文書検査の並行系列olean制限は§13.44を維持する。

U10全受入は未完。このホモトピー消滅だけで局所化内のHom計算が完了したとは主張しない。
次はquasiIsoの後合成による全Homの不変性を証明し、射影解像度から導来Homを計算して、
比較射・解像度の選択独立性を確定する。
その後K(D)/D(D)の三角構造・Verdier商比較、導来余積と局所小性、
一対象Aの既存導来圏との同値の三角形/余積保存を完成する。
共有一般モデル圏/Quillen/転送/SM7の重複はなく、これらの作業を先行条件にもしていない。


### 13.46 U10b6b：coneの斉次包含・射影と全次数後合成

`Module/ConeElements.lean` はconeの左包含（次数−1）、第一射影（次数+1）、
第二射影（次数0）を主Hom endの要素として構成する。
各射影はMathlibのmappingConeのcochainと一致し、全整数次数の加群作用に関する
Koszul符号付き自然性を証明した。
左包含の微分は元の射と右包含の合成の閉零cycle、第一射影の微分は零である。
第二射影は既存の次数付き分裂のretractionを再利用する。

`Module/Postcomposition.lean` は豊穣合成をbraiding後に転置し、
`Hom_D(M,N) → Hom_Ch(A)(Hom_D(T,M),Hom_D(T,N))` をchain mapとして構成する。
成分は通常順の合成となり、braidingと豊穣合成の二つのKoszul符号が相殺する。
全次数の評価・微分との整合性と、閉次数零射での既存後合成との一致を証明した。

`Checks/ConeElements.lean` とStageSix・既存Spectra.StageTwoの同時ビルドは成功（3205 jobs）。
直接実行の主要14宣言は標準公理のみ。累計774宣言。
全体文書検査は21 Markdown/311参照で0 failuresとなり、§13.44の未生成olean制限は今回解消した。
担当Leanのsorry/admit/新規axiomは0件、担当差分の空白検査は成功。

U10全受入は未完。次は左包含の微分をこの転置で運び、
`cone(Hom_D(T,f)) → Hom_D(T,cone(f))` をMathlibのdescから構成して全次数同型性を証明する。
その比較から射影的始域でのquasiIso不変性、導来Hom・選択独立性へ進む。
三角構造・Verdier商・導来余積/局所小性・一対象比較の保存性も残る。


### 13.47 U10b6c：全Hom endのcone比較のchain iso

`Module/HomCone.lean` は左包含への後合成を次数−1のcochainへ転置し、
その微分が `Hom_D(T,f)` とcone右包含への後合成の合成であることを証明する。
MathlibのmappingCone.descから `moduleHomConeComparison` を構成し、
各射影での成分がMathlibのliftCochainであることと、右包含との整合性を公開する。

`Complexes/ConeElements.lean` は各次数のcone要素を二成分から構成する補助APIを提供する。
`Module/HomConeIso.lean` は主Hom endの第一・第二射影への通常順合成から逆要素を構成し、
全整数次数で左右の逆関係を証明する。比較射の各成分の全単射性から真のchain iso
`moduleHomConeIso : cone(Hom_D(T,f)) ≅ Hom_D(T,cone(f))` を得る。
TやHom_Dに射影性・flatnessは要求せず、任意可換環・非有界複体の主モデルで成立する。

`Checks/HomCone.lean` は一般A/Dのchain iso、全整数次数の両逆、右包含との整合性を検証する。
同入口・StageSix・既存Spectra.StageTwoの同時ビルドは成功（3209 jobs）。
直接実行の主要19宣言は標準公理のみ。累計793宣言。
担当Leanのsorry/admit/新規axiomは0件。文書検査は§13.46で全体成功を確認した。

U10全受入は未完。次はこの同型と既存のconeによるquasiIso判定を組み合わせ、
homotopically projectiveなTからの全Homが指定quasiIsoを保つことを証明する。
導来Hom・選択独立性・三角構造・Verdier商・導来余積/局所小性・一対象比較の保存性は残る。


### 13.48 U10b6d：射影的始域からの全HomのquasiIso不変性

`Derived/ProjectiveHomQuasiIso.lean` はconeのchain isoと既存のobjectwise cone判定を使い、
`moduleHomotopicallyProjective_postcompose_quasiIso` を証明する。
homotopically projectiveなTと指定objectwise quasiIso f:M→Nについて、
後合成 `Hom_D(T,M) → Hom_D(T,N)` は全次数のHom複体のquasiIsoである。
`moduleSemifree_postcompose_quasiIso` は証明済みsemifree射影性による直接の適用である。

`Checks/ProjectiveHomQuasiIso.lean` は一般仮定と、実際のsemifree resolution candidateを
始域に取り、別の加群の実際のresolution mapへ適用する検査を含む。
同入口・StageSix・既存Spectra.StageTwoの同時ビルドは成功（3254 jobs）。
直接実行の主要2宣言は標準公理のみ。累計795宣言。
担当Leanにsorry/admit/新規axiomは0件。共有一般論の不足APIはない。

U10全受入は未完。次はこのquasiIsoのcycle持ち上げと境界反映を具体化し、
全dg自然なホモトピーまでの比較射とその一意性を得る。
それを射影解像度の選択独立性と局所化内の導来Hom計算へ接続する。
三角構造・Verdier商・導来余積/局所小性・一対象比較の保存性も引き続き残る。


### 13.49 U10b6e：ホモトピーまでの持ち上げ・一意性とK(D)のHom

`Complexes/QuasiIsoCycles.lean` はacyclic coneの境界原像を二つの射影で読むことで、
quasiIsoに沿うcycleの持ち上げ（境界まで）と境界の反映を、証人付きの存在命題として証明する。
`Module/HomCycles.lean` は既存closedHomEquivを再利用し、閉次数零要素からの主加群射の構成と、
cycle上の後合成が通常の加群射の合成と一致することを公開する。

`Derived/ProjectiveHomotopyLifting.lean` は射影的始域TとquasiIso f:M→Nについて、
任意のg:T→Nに対するs:T→Mと全dg自然な `ModuleHomotopy (s≫f) g` の存在を証明する。
また後合成した二射がその意味でホモトピックなら元の二射もホモトピックであることを証明する。
`Derived/ProjectiveHomotopyHom.lean` はこの存在と反映を境界商へ運び、
K(D)の `Hom(T,M) → Hom(T,N)` が全単射であることを証明する。
射影的対象間のquasiIsoはK(D)で同型となることも、実際の逆射を持ち上げて証明した。

`Checks/ProjectiveHomotopyLifting.lean` は全dg自然な持ち上げ、K(D)のHomの全単射性、
射影的対象間のquasiIsoの同型性を検証する。
同入口・StageSix・既存Spectra.StageTwoの同時ビルドは成功（3258 jobs）。
直接実行の主要13宣言は標準公理のみ。累計808宣言。
担当Leanのsorry/admit/新規axiomは0件。文書検査は§13.46で全体成功を確認した。

U10全受入は未完。次は二つの射影解像度の比較射の存在・一意性と三つの比較の整合性を公開する。
K(D)での比較を指定局所化内の導来Hom計算へ接続する必要があり、
三角構造・Verdier商・導来余積/局所小性・一対象比較の保存性も残る。


### 13.50 U10b6f：射影解像度の比較とK(D)での選択独立性

`Derived/ResolutionComparison.lean` は同じMへの二つの射影解像度p:P→M/q:Q→Mについて、
比較射s:P→Qを構成する。その射は指定quasiIsoであり、K(D)で同型となり、
K(D)で `s≫q=p` を満たす。semifree解像度への適用も公開する。
比較射のK(D)での像はこの可換条件により一意であり、三つの解像度の比較について
合成と直接比較がK(D)で一致するcocycle条件を証明した。
単に解像度間に何らかの同型が存在するという命題だけではなく、Mへの射との整合性を含む。

`Checks/ResolutionComparison.lean` は比較の存在・一意性と、自己比較が恒等射となることを検証する。
同入口・StageSix・既存Spectra.StageTwoの同時ビルドは成功（3259 jobs）。
直接実行の主要4宣言は標準公理のみ。累計812宣言。
担当Leanのsorry/admit/新規axiomは0件、担当diff --checkは成功。

U10全受入は未完。解像度のK(D)での比較と整合性は揃ったが、
全Hom複体を既存D(A)へ送り、指定D(D)の局所化へ延長する導来Hom関手と計算同型を
構成する必要がある。始域解像度の比較によるその関手の選択独立性も残る。
三角構造・Verdier商・導来余積/局所小性・一対象比較の保存性は引き続き残る。


### 13.51 U10b7a：射影的始域からの導来Hom関手と計算同型

`Derived/HomOut.lean` は主全Hom関手を既存D(A)へ合成し、§13.48により指定quasiIsoを
反転することを証明する。指定局所化の普遍性から
`moduleDerivedHomOut T hT : D(D) → D(A)` を構成した。
`moduleDerivedHomOut_fac` は加群圏上の全Homとの厳密な関手等式であり、
対象だけでなく射についても計算を保証する。
`moduleDerivedHomOutComputation` は既存全Hom複体のD(A)での像との計算同型を公開する。
`moduleResolvedHomOut M` は実際のsemifree resolution candidateを始域に取るこの関手である。

Aは任意可換環、対象は非有界。主dg加群圏と指定objectwise quasiIsoの局所化を維持する。
値域の射宇宙は既存APIと同じ `[HasDerivedCategory.{w} (ModuleCat.{u} A)]` で明示する。
新しい引用axiomやモデル構造の仮定はない。始域変数についてD(D)上の双関手を
構成したとはまだ主張しない。

`Checks/DerivedHomOut.lean` は独立した値域射宇宙w、厳密な分解、全Homによる計算同型、
実際のsemifree解像度による関手を検証する。
同入口・StageSix・既存Spectra.StageTwoの同時ビルドは成功（3255 jobs）。
直接実行の主要6宣言は標準公理のみ。累計818宣言。
全体文書検査は21 Markdown/311参照で0 failures。
今回§13.46〜§13.51の主要58宣言すべてについて公理監査ログを照合し、標準公理のみと確認した。
担当Leanのsorry/admit/新規axiomは0件、担当diff --checkは成功。

U10全受入は未完。次は始域の比較射による前合成を全Hom複体に運び、
射影解像度の比較から導来Hom関手間の自然同型とそのcocycle条件を構成する。
K(D)での解像度比較だけでこの関手の選択独立性が完了したとは扱わない。
局所化内のHom計算・始域についての関手性、K(D)/D(D)の三角構造・Verdier商比較、
導来余積・局所小性・一対象A比較の三角形/余積保存も残る。
共有一般モデル圏/Quillen/転送/SM7に新しい不足API要求はない。


### 13.52 U10b7b：前合成のホモトピーと射影的対象間のquasiIso

`Module/Precomposition.lean` は豊穣合成を転置し、全次数の前合成をHom複体間のcochainへ送る。
次数pの前合成は入力次数qについて豊穣順のKoszul符号を持つ。
微分と可換すること、閉次数零では既存の前合成と一致することを証明し、
`ModuleHomotopy` の像を通常のHom複体間のchain homotopyとして構成した。

`Derived/ProjectivePrecomposition.lean` は射影的対象間のquasiIsoをK(D)の同型として扱い、
その逆射を主加群圏へ取り出す。両逆の等式を全dg自然なホモトピーへ戻して前合成に運び、
`moduleProjectivePrecomposeHomotopyEquiv` を構成する。
従って任意Tに対し前合成 `Hom_D(N,T)→Hom_D(M,T)` は真のホモトピー同値でありquasiIsoである。
Tのacyclic性や射影性、D(A)の選択は不要である。

`Checks/ProjectivePrecomposition.lean` はホモトピーの像とホモトピー同値・quasiIsoを検証する。
同入口・StageSix・既存Spectra.StageTwoの同時ビルドは成功（3260 jobs）。
直接実行の主要7宣言は標準公理のみ。累計825宣言。
担当Leanのsorry/admit/新規axiomは0件、担当diff --checkは成功。

U10全受入は未完。次は前合成の自然変換を指定D(D)へ延長し、
比較射が準同型なら導来Hom関手間の自然同型になることと、ホモトピーによる独立性を証明する。
局所化内のHom計算・始域についての関手性、三角構造・Verdier商・導来余積/局所小性・
一対象比較の保存性も残る。


### 13.53 U10b7c：導来Homの前合成と自然同型

`Derived/HomOutPrecomposition.lean` は全Homの前合成をD(A)へ合成した自然変換を、
MathlibのLocalization.Construction.natTransExtensionで指定D(D)上へ延長する。
`moduleDerivedHomOutPrecomp` は射影的対象の任意の射による自然変換である。
元の加群上の成分は、既存計算同型で共役した全Homの前合成そのものであることを証明する。
恒等・合成法則と、全dg自然なホモトピーで結ばれる射、従ってK(D)で等しい射が
同じ自然変換を与えることを証明した。

射影的対象間のquasiIsoについては、§13.52の前合成のquasiIso性を使い、
局所化の全対象で成分が同型となることを証明して `moduleDerivedHomOutPrecompIso` を構成した。
値域の射宇宙wはHasDerivedCategoryで明示し、既存主Hom endとMathlib豊穣Homは同じ構造を使用する。

`Checks/DerivedHomPrecomposition.lean` は自然同型、K(D)での等式による独立性、合成法則を検証する。
同入口・StageSix・既存Spectra.StageTwoの同時ビルドは成功（3262 jobs）。
直接実行の主要11宣言は標準公理のみ。累計836宣言。
担当Leanのsorry/admit/新規axiomは0件、担当diff --checkは成功。

U10全受入は未完。次は射影解像度の比較をこの自然同型へ運び、
解像度を替えたときの導来Hom関手の選択独立性とcocycle条件を確定する。
局所化内のHom計算・始域についての関手性、三角構造・Verdier商・導来余積/局所小性・
一対象比較の保存性は引き続き残る。


### 13.54 U10b7d：解像度選択に依存しない導来Homの比較自然同型

`Derived/ProjectiveResolution.lean` は対象・増大射・全Homによる射影性・指定quasiIsoを
`ModuleProjectiveResolution` に保持し、実際のsemifree candidateから標準解像度を与える。
既存の比較存在定理から選んだ比較射について、準同型性・増大射とのK(D)での可換性・
K(D)での同型性・一意性・恒等・合成の整合性を公開する。

`Derived/HomChoice.lean` は任意の二つの射影解像度の導来Hom関手の間に自然同型を構成する。
元の加群上の成分は全Homの前合成で計算でき、増大射との可換条件を満たすどの比較射を
選んでも同じ自然変換を得る。自己比較は恒等自然同型、三つの解像度の比較はcocycle条件を満たす。
標準semifree解像度による既存moduleResolvedHomOutとの一致も公開する。
K(D)での対象の比較だけでなく、指定D(D)上のD(A)値関手の自然同型として選択独立性を得た。

`Checks/HomChoice.lean` は任意の比較射、三つの比較の整合性、標準解像度との比較を検証する。
同入口・ProjectiveResolutionLift・StageSix・既存Spectra.StageTwoの同時ビルドは成功（2589 jobs）。
共有基盤の整理による一時的なCochainConeTriangleの証明エラーとAcyclicCone.olean欠落は
この再実行では解消した。担当外のソースや並行作業の変更は編集・巻き戻していない。
直接実行の主要17宣言（解像度の構成子を含む）は標準公理のみ。累計853宣言。
担当Leanのsorry/admit/新規axiomは0件、担当diff --checkは成功。

U10全受入は未完。次は任意の基底の射を解像度へ持ち上げる関手法則を確定し、
始域についても指定局所化へ延長して全導来Hom双関手を構成する。
局所化内のHom計算、三角構造・Verdier商・導来余積/局所小性・一対象比較の保存性は残る。


### 13.55 U10b7e：基底の射の解像度への持ち上げと関手法則

`Derived/ProjectiveResolutionLift.lean` は任意f:M→Nと射影解像度P/Qについて、
増大射とK(D)で可換する持ち上げP.obj→Q.objを構成する。
そのK(D)での像の一意性、恒等・合成法則を証明する。
fが指定quasiIsoなら持ち上げも指定quasiIsoであることを、K(D)の準同型判定と
二つの増大射の準同型性から証明した。
恒等射の持ち上げと既存の解像度比較の一致、解像度を替えたときの比較との自然性も公開する。

`Checks/ProjectiveResolutionLift.lean` は増大射との可換性、合成法則と解像度比較の自然性を検証する。
同入口・HomChoice・StageSix・既存Spectra.StageTwoの同時ビルドは§13.54のとおり成功（2589 jobs）。
直接実行の主要8宣言は標準公理のみ。累計861宣言。
担当Leanのsorry/admit/新規axiomは0件、担当diff --checkは成功。

U10全受入は未完。次はこの持ち上げと導来Homの前合成を反変関手にまとめ、
任意の解像度族に対する双関手を両変数の指定局所化へ延長する。
局所化内のHom計算、三角構造・Verdier商・導来余積/局所小性・一対象比較の保存性も残る。


### 13.56 U10b7f：両変数の指定局所化上の全導来Hom双関手

`Derived/HomBifunctor.lean` は任意の証明付き射影解像度族Rについて、
解像度への射の持ち上げと導来Homの前合成を反変関手にまとめる。
持ち上げの恒等・合成法則はK(D)で証明済みであり、前合成のホモトピー独立性で
真の関手法則へ運ぶ。指定quasiIsoは自然同型へ送られる。
Mathlibのopposite局所化とliftを再利用して
`moduleResolutionDerivedHomBifunctor : D(D)ᵒᵖ → (D(D) → D(A))` を構成した。
局所化前の反変関手との比較自然同型と、R(M)による全Hom複体のD(A)像との計算同型を公開する。

`moduleDerivedHomBifunctor` は実際の標準semifree解像度族を選んだ全導来Hom双関手である。
`moduleDerivedHomBifunctorResolutionComputation` は標準族の値を任意の射影解像度P→Mで計算する。
値域射宇宙wはHasDerivedCategoryで指定し、主D(D)の対象・射宇宙を勝手に小さくしていない。

`Checks/HomBifunctor.lean` は両変数の関手、指定局所化との比較、任意の解像度族による計算、
任意の単一の射影解像度による標準双関手の計算を検証する。
同入口・HomBifunctorChoice・StageSix・既存Spectra.StageTwoの同時ビルドは成功（2591 jobs）。
直接実行の主要8宣言は標準公理のみ。累計869宣言。
担当Leanのsorry/admit/新規axiomは0件、担当diff --checkは成功。

U10全受入は未完。次は解像度族の比較が始域変数にも自然であることを使い、
双関手間の選択独立性を局所化上の自然同型とcocycle条件で公開する。
D(D)の射集合のK(D)による計算・局所小性、三角構造・Verdier商・導来余積・
一対象比較の三角形/余積保存も引き続き残る。


### 13.57 U10b7g：全導来Hom双関手の解像度族選択独立性

`Derived/HomBifunctorChoice.lean` は解像度族R/Sの比較を、始域についても自然な
反変関手間の自然同型へまとめる。自然性は§13.55の持ち上げと比較の可換四角形を
導来Homの前合成へ運んで証明する。
MathlibのliftNatIsoにより指定D(D)上へ延長し、両変数について自然な
`moduleResolutionDerivedHomBifunctorIso` を構成した。
局所化前の比較との成分公式、恒等比較、三つの解像度族の比較のcocycle条件を証明する。
`moduleDerivedHomBifunctorChoiceIso` は標準semifree族と任意の射影解像度族による双関手を比較する。

`Checks/HomBifunctorChoice.lean` は標準族との比較と局所化後の恒等・cocycle条件を検証する。
同入口・HomBifunctor・StageSix・既存Spectra.StageTwoの同時ビルドは成功（2591 jobs）。
直接実行の主要9宣言は標準公理のみ。累計878宣言。
今回§13.52〜§13.57の主要60宣言について公理監査ログを照合し、標準公理のみと確認した。
共有基盤更新後の受入入口6本・StageSix・既存Spectra.StageTwoの最終同時ビルドも成功（2595 jobs）。
その出力でも60宣言すべての公理を再照合した。
全体文書検査は並行Paper系列の未生成Paper.Section5.LengthAlgebraPositivity.oleanで停止し、
今回は成功とは扱わない。担当外のソースは編集していない。
担当Leanのsorry/admit/新規axiomは0件、担当diff --checkは成功。

これで全Homによる射影解像度の計算と、両変数の指定局所化上の全導来Hom双関手、
解像度族を替えたときの自然同型と整合性が揃った。
ただしU10全受入は未完であり、D(D)の射集合そのものの計算をこの結果だけから主張しない。
次の独立実装の型契約は、射影的Pと任意Nに対して
L=moduleHomotopyToDerivedClosedの射写像
`Hom_K(Q_K(P),Q_K(N)) → Hom_D(L(Q_K(P)),L(Q_K(N)))` が全単射であること。
K(D)のcoyonedaが指定quasiIsoを反転する事実と局所化の関手/自然変換の普遍性から進める。
これを標準解像度の増大射と組み合わせ、実際のD(D)のHom計算と
`LocallySmall.{u} (DerivedModuleCategory A D)` の宇宙を証明する。
K(D)/D(D)の三角構造・Verdier商比較、導来余積、一対象Aの既存導来圏との同値の
三角形/余積保存も残る。共有モデル圏/Quillen/転送/SM7への新しい不足要求はない。


### 13.58 U10b8a：宇宙を独立にした局所化Hom比較

`Category/LocalizationHom.lean` は、Wの局所化Lと、coyoneda(P)がWを反転するという
仮定から、`L.map : Hom(P,X) → Hom(L(P),L(X))` の全単射性を証明する。
局所化前後のHom宇宙は独立とし、ULiftで値域をそろえる。
恒等射の像から逆自然変換を構成し、局所化の自然変換に関する充満忠実性により
両合成が恒等であることを証明した。分数計算やモデル構造の仮定は不要。
`homEquiv`、`mapEquiv`、`mapEquiv_apply`、`map_bijective`を公開する。

Checks.LocalizationHom・StageSix・既存Spectra.StageTwoの同時ビルドは成功（2501 jobs）。
Checksの直接実行で主要15宣言を監査し、標準公理のみ。累計893宣言。
担当Leanのsorry/admit/新規axiomは0件。
全体文書検査は並行KTheory.Adams.KoszulSquareCoordinatesの未生成oleanで停止した。
U10は未完。次は射影的加群へ適用し、D(D)の射集合と局所小性を証明する。


### 13.59 U10b8b：射影的始域のK(D)/D(D)のHom同定

`Derived/ProjectiveLocalizationHom.lean` は射影的始域のcoyonedaが
`moduleHomotopyQuasiIso`を反転することを、既存のホモトピー持ち上げ・反映から証明した。
§13.58を適用した`moduleProjectiveLocalizationHomEquiv`と射写像の全単射性を公開する。
`moduleToHomotopyDerivedIso`で共役し、主局所化関手を用いる
`moduleProjectiveDerivedHomEquiv`も構成した。閉零射のホモトピー類の像が
主局所化関手の射写像と一致する公式を証明している。

Checks.ProjectiveLocalizationHom・StageSix・既存Spectra.StageTwoの同時ビルドは成功（2582 jobs）。
Checks直接実行の主要6宣言は標準公理のみ。累計899宣言。
U10は未完。次は任意加群の解像度による実際のHom計算と局所小性を公開する。


### 13.60 U10b8c：解像度による実際の射集合・roof表示・局所小性

`Derived/ResolutionHom.lean` の`moduleResolutionDerivedHomEquiv`は、任意の証明付き
射影解像度P→Mに対して、K(D)のHom(P,N)を主D(D)のHom(M,N)と同定する。
閉零射の像は増大射の導来像の逆との合成であることを明示した。
`moduleResolutionDerivedHom_surjective`はすべての導来射のroof表示を与え、
`moduleResolutionDerivedHom_eq_iff`は二つの表示の一致を全dg自然な加群ホモトピーと同値にする。

標準semifree解像度と上記同定から`moduleDerivedHom_small`を証明した。
主局所化の対象構成を展開して全対象へ適用し、
`moduleDerivedLocallySmall : LocallySmall.{u} (DerivedModuleCategory A D)`を構成した。
局所化の元の射宇宙を変更せず、u-smallな代表が存在することを証明している。
Checksでは任意の導来対象M/Nについて`Small.{u} (M ⟶ N)`が推論できることも検査する。

Checks.ResolutionHom・Checks.ProjectiveLocalizationHom・StageSix・既存Spectra.StageTwoの
同時ビルドは成功（2586 jobs）。Checks直接実行の主要6宣言は標準公理のみ。累計905宣言。
U10の実際の射集合計算・局所小性は受入を満たした。
U10全体は未完。残るのはK(D)/D(D)の三角構造、acyclic部分圏とVerdier商の比較、
導来余積、一対象A比較の三角形/余積保存である。
共有モデル構造・Quillen・転送・SM7への新規要求はない。


### 13.61 U10c1：全dg自然なホモトピーの貼り合わせとK(D)の余積

`Module/HomotopyCoproduct.lean`は、余積の各包含への前合成後に全dg自然な
ホモトピーがあるとき、余積からの二射の間にも全dg自然なホモトピーがあることを証明する。
主Hom endの直積表示と複体の各次数の直積普遍性から次数−1の要素を構成し、
chain isoの射影と微分の可換性でホモトピーの境界式を検証した。

`Module/HomotopyCoproductUniversal.lean`はK(D)の余積包含によるhom_ext、
余積coconeのdesc/fac/uniq、`moduleHomotopyCofanIsColimit`を公開する。
任意のu-small添字Jに対するK(D)の`HasColimitsOfShape (Discrete J)`と、
閉零圏→K(D)の商関手の余積保存も証明した。

Checks.HomotopyCoproduct・StageSix・既存Spectra.StageTwoの同時ビルドは成功（2515 jobs）。
Checks直接実行の主要9宣言は標準公理のみ。累計914宣言。
U10は未完。次は射影的対象族の余積をD(D)へ運び、解像度で任意の導来対象族に拡張する。


### 13.62 U10c2/d2：導来余積と一対象環の比較による保存

`Derived/Coproducts.lean`は射影的対象のHom計算の前合成自然性を証明し、
射影的対象族Mの余積の主局所化像と包含からなるcoconeの普遍性を構成する。
そのdescはK(D)の余積descを実際の導来Hom同定で移した射であり、fac/uniqを証明済み。
任意の導来対象族に標準semifree解像度を選び、増大射の同型による図式同型を使って、
`moduleDerivedHasCoproductsOfShape`を得た。任意のu-small添字Jに対応する。

`Derived/RingCoproducts.lean`は任意の指定された既存DerivedCategoryの宇宙で、
一対象Aの比較同値の順方向・逆方向がこの余積を保存することを証明する。
既存導来圏への余積の移送と、標準余積比較射が同型となることも公開した。
射影的でない加群族のunderived余積について主局所化関手が保存するという追加命題は、
ここでは主張していない。導来圏自体の余積の存在・普遍性と比較同値の保存は証明済み。

Checks.DerivedCoproducts・Checks.HomotopyCoproduct・Checks.ResolutionHom・StageSix・
既存Spectra.StageTwoの同時ビルドは成功（2593 jobs）。
直接実行の主要11宣言は標準公理のみ。累計925宣言。
今回§13.58〜§13.62の主要47宣言を直接実行ログで照合し、すべて標準公理のみと確認した。
担当Leanのsorry/admit/新規axiomは0件、担当diff --checkは成功。
全体文書検査は§13.58記載の担当外の未生成oleanで停止しており、成功とは扱わない。

U10全受入は未完。次はK(D)の標準cone三角形から三角構造を構成し、acyclic部分圏の
三角閉性とVerdier商の指定quasiIso局所化との比較を証明する。
その後D(D)の三角構造、主局所化関手の三角性、一対象Aの既存導来圏との同値の
三角形保存を完成させる。既存shift・cone・比較同値と今回のHom計算・余積を再利用する。
共有モデル構造・Quillen・転送・SM7への新規不足要求はなく、担当外ファイルは編集していない。


### 13.63 U10t1：全dg自然な境界によるconeからの延長

`Module/ConeHomotopyDesc.lean`は次数−1の主Hom要素hと閉零射b:M→Tから、
cone(a)→Tの候補を二つの射影と通常順の斉次合成で構成する。
既存の`moduleHomCompose_π`を再利用し、各評価がMathlibの`descCochain`と一致することを証明した。
d hがa≫bの閉零cycleであるとき候補は閉次数0となり、実際の加群射
`moduleConeDescOfBoundary`を得る。評価は既存`mappingCone.desc`に一致し、
標準右包含との合成がbであることも証明した。
任意の可換環、非有界複体、全次数dg自然性の契約を維持する。

Checks.ConeHomotopyDesc・StageSix・既存Spectra.StageTwoと標準cone三角形の入口の
同時ビルドは成功（2523 jobs）。直接実行の主要7宣言は標準公理のみ。累計932宣言。
U10全受入は未完。次はこの延長を用いてホモトピーまで可換なsquareのcone射と
K(D)の標準cone三角形の射の補完を公開する。


### 13.64 U10t2：ホモトピー可換squareのcone射と標準三角形の補完

`Module/ConeHomotopyMap.lean`は指定された全dg自然なホモトピーを、同じcochain成分を持つ
各評価の複体ホモトピーへ移す。次数−1の左入力を、左包含への前合成と
指定ホモトピーの右包含への後合成の和で構成し、その境界を証明した。
§13.63の延長により`moduleConeMapOfHomotopy`を得る。評価がMathlibの
`mappingCone.mapOfHomotopy`と一致し、右包含・connecting mapの両方と可換である。

`Module/HomotopyConeTriangle.lean`は主K(D)の標準cone三角形を定義し、
上記cone射を三角形の射へまとめた。第三の可換式では商関手のshift比較自然同型を明示する。
K(D)の任意の可換squareについて代表射と全dg自然なホモトピーを選び、
`moduleHomotopyConeTriangle_complete`で標準三角形の射への補完を証明した。

Checks.HomotopyConeTriangle・Checks.ConeHomotopyDesc・StageSix・既存Spectra.StageTwoの
同時ビルドは成功（2524 jobs）。直接実行の主要13宣言は標準公理のみ。累計945宣言。
全体文書検査は担当外のPaper.Section5.SecondComparisonの未生成oleanで停止した。
U10全受入は未完。K(D)の三角構造の残るcontractible・回転・八面体条件と、
D(D)の三角構造・Verdier比較・一対象比較の三角性を引き続き証明する。


### 13.65 U10t3：恒等射のconeの全dg自然な収縮とK(D)の零対象

`Module/ConeContractible.lean`は主Homの零射cycleを同定し、coneの次数−1の左包含を
f≫inrから零への全dg自然なホモトピーとして公開した。
恒等射のconeについて、第二射影と左包含の通常順合成で次数−1の自己Hom要素を構成する。
各評価がMathlibの恒等coneの収縮cochainに一致し、その境界が恒等射cycleであることを証明した。
`moduleConeIdHomotopy`と`moduleConeId_isZero`によりK(D)で零対象となる。
加法的な商関手による既存零対象の像から、K(D)の`HasZeroObject`も構成した。

Checks.ConeContractible・StageSix・既存Spectra.StageTwoの同時ビルドは成功（2524 jobs）。
並行依存更新時に直接監査でCompositionLaws.oleanの欠落を検出したため、
依存を再ビルドして同じ受入入口を再検証し、直接実行の主要8宣言を再監査した。
すべて標準公理のみ。累計953宣言。並行変更されたComplexes.Curryingは編集していない。
U10全受入は未完。次は標準coneと同型な三角形のクラスについて既存の補完・収縮を運ぶ。
