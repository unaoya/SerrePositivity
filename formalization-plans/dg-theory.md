# dg 理論（M5）の独立実装計画

作成・調査：2026-10-14。更新：2026-10-15。状態：U0〜U5 を実装・検証済み。
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
