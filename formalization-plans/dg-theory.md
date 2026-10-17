# dg 理論（M5）の独立実装計画

作成・調査：2026-10-14。更新：2026-10-17。状態：U0〜U11 を実装・検証済み（U11統合受入§17.159）。U12〜U17は部分実装済み、明示的dg商U15a/bと厳密普遍性U15cを受入（§17.144）。U10後の比較・整理案と後続詳細計画は§14〜§16。
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

## 0. 現行の分担と合流順（2026-10-17更新）

最新のユーザー指定により、このチャットはU12eの完成・受入→U16→U15eの分解版を担当する。
直近の受入対象はU12eとし、その受入後にU16へ進む。

ユーザー指定の分担変更により、以下をこの文書の従来の一系列実施順より優先する。

| 範囲 | 担当チャット・所有範囲 | 実装記録 |
| --- | --- | --- |
| U12eの完成・受入 → U16 → U15eの分解版 | このチャット。既存のdg加群・bimodule・導来合成の公開APIを管理 | この文書§17 |
| U14（指定生成元・endomorphism表示） | 「dg-U14」。`DifferentialGraded/Endomorphism/` | `dg-theory-u14.md` |
| U12f・U15d（係数変更）、追加のU17a・U13d | 「dg-U12f/U15d」。このチャットの担当外 | `dg-theory-scalar-extension.md` |
| U15eの局所K-flat版 → U17bの局所K-flatの場合 | U17a・U13dを終えたチャット。`Quotient/DerivedComparison*.lean`・`Verdier/` | `dg-theory-u17a-u13d.md`を参照 |
| D4m（dg加群モデル構造） | 当面未割当。U17までの主線には使わない | 未着手 |

両並行チャットは既存の`Derived/KFlatBimodule*`や`Bimodule/`の合成系を読み、再利用するが、
それらを編集しない。このチャットで公開APIの名前・型を変更する際は、変更名、旧型と新型、
仮定・宇宙の差、利用側の移行方法をこの文書§17へ記録する。
新規APIの追加でも使用条件と使用箇所を記録し、共有利用者が暗黙の仮定に依存しないようにする。
並行チャットの記録ファイルは各担当が管理し、この文書§17は引き続きこのチャットが管理する。
共有モデル圏・Quillen・転送・monoidal model・SM7一般論の所有は元のK理論系列のままとする。
ユーザー指定により履歴のamend・rebase・resetは禁止。検証済みの小単位を新規コミットで記録する。
新規ファイル作成前には同名既存ファイルの有無を確認する。共有ルートSerrePositivity.leanと
共有監査スクリプトを変更するときは自分のhunkだけをgit add -pでstageする。
U16bではEndomorphism/の再構成随伴・endomorphism比較と、受入済みの
Tensor/ScalarExtension*・Derived/ScalarExtension*を読み取り専用で再利用する。
このチャットはU12eを受け入れてからU16へ進み、その後U15eの分解版を扱う。
U15eの局所K-flat仮定を置く版はU17a・U13dを終えたチャットが担当し、
続けてU17bの局所K-flatの場合を扱う。この局所K-flat版の作業は、このチャットの合流待ちとは分離する。
U15e分解版の開始条件はU12f・U14・U16の受入条件がそろうことであり、
局所K-flat版の`Quotient/DerivedComparison*.lean`と`Verdier/`を読んで再利用する。
局所K-flat版の比較・Verdier一般論を重複実装せず、分解とその比較APIへの接続を担当する。
U16cでDG-MOR、U15eでDG-DRの引用採用が必要になったら、採用せず停止して報告する。
新しいsorry・axiom・引用は追加しない。この規則は以下の従来の引用許容案に優先する。

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

## 13. U6〜U10 の実装・受入記録（2026-10-15、受入済み）

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


### 13.66 U10t4：coneによる三角形のクラスと四つの条件

`Module/ContractibleTriangleIso.lean`は恒等coneの収縮を第三対象の同型として用い、
自明三角形と標準恒等cone三角形を比較する。対象を明示した独立定義にして、
大きな存在命題内でconeの対象定義を再展開することを避けた。
`Module/DistinguishedTriangles.lean`は標準cone三角形と同型な三角形を
`moduleDistinguishedTriangles`として定義する。
このクラスの同型閉性、任意のK(D)の射を三角形へ延長できること、
すべてのcontractible triangleが属すること、任意の可換squareを三角形の射へ補完できることを証明した。
補完は§13.64の標準三角形での補完を両側の三角形同型で共役して得る。
第一射と第二射の合成が零となることも、contractible triangleからの補完で導いた。

受入入口4本（ConeHomotopyDesc・HomotopyConeTriangle・ConeContractible・DistinguishedTriangles）と
StageSix・既存Spectra.StageTwoの最終同時ビルドは成功（2529 jobs）。
主要8宣言を含む今回の主要36宣言の直接監査は標準公理のみ。累計961宣言。
担当Leanのsorry/admit/新規axiomは0件。担当差分の空白検査も成功。
最終の全体文書検査は担当外のPaper.Section5.SelectedParameterPositivityの未生成oleanで停止した。
今回も全体文書検査を成功とは扱わない。

U10全受入は未完で、現時点ではPretriangulated/Triangulatedのインスタンスを置いていない。
次の実装は以下の型を主な入口とする。

1. 全dg自然な片側shiftのHom要素を構成し、Mathlibの`Cochain.leftShift`との成分比較を証明する。
2. 任意の閉零射f:M→Nについて、K(D)の`(moduleHomotopyConeTriangle f).rotate`と
   `moduleHomotopyConeTriangle (moduleConeInr f)`の同型を構成する。
   元の複体の回転比較の順・符号・収縮を各評価で照合し、全dg自然なHom要素として証明する。
3. 三角形のshift・回転閉性を完成させてPretriangulatedを構成し、八面体条件を証明する。
4. acyclic部分圏の三角閉性、Verdier商と指定quasiIso局所化の比較、D(D)の三角構造、
   主局所化関手と一対象A比較の三角性を完成させる。

共有モデル構造・Quillen・転送・SM7の新規不足要求はなく、これらを複製していない。


### 13.67 U10t5：始域だけをshiftする全次数Hom要素

`Module/LeftShiftElements.lean`は任意の整数sとq+s=q'に対し、主Homの次数qの要素を
始域だけをshiftした主Homの次数q'の要素へ移す`moduleHomLeftShiftElement`を構成する。
各評価はMathlibの`Cochain.leftShift`そのもの。作用のshift符号と元の次数qの自然性を
組み合わせ、次数q'について全dg自然であることを証明した。
微分は(-1)^s倍を伴って移る。加法・Aスカラー・零・負元の保存、単射性、
通常の閉零射による後合成との可換性も証明した。
MathlibのleftShiftの符号s*q'+s*(s-1)/2を含む規約をそのまま保持する。

Checks.LeftShiftElements・StageSix・既存Spectra.StageTwoを含む同時ビルドは成功（2520 jobs）。
Checksの直接実行で主要10宣言を監査し、すべて標準公理のみ。累計971宣言。
U10は未完。次は全Homのcone比較によるliftと、この片側shiftを回転比較射へ接続する。


### 13.68 U10t6：全Homのcone比較から得られるconeへのlift

`Module/ConeLift.lean`は、全Homの既存cone比較と各次数のcone要素constructorを用いて、
次数q+1とqの二つの主Hom要素から、coneを終域とする次数qの要素を構成する。
各評価が既存`mappingCone.liftCochain`に一致することを証明した。
次数1の入力が閉じ、次数0の入力の微分と前者の後合成の和が零である場合、
候補は閉次数0となり`moduleConeLiftOfCycle`を得る。閉性は各評価の
`mappingCone.liftCocycle`から証明し、実際の射の評価がMathlibの`mappingCone.lift`に一致する。

Checks.ConeLiftをビルドし、直接実行の主要6宣言を監査した。すべて標準公理のみ。
StageSix・既存Spectra.StageTwoの互換入口もビルド済み。累計977宣言。
U10は未完。次は片側shiftとこのliftから回転比較射を構成し、逆射と収縮を証明する。


### 13.69 U10t7：回転比較の両射と既存複体比較との一致

`Module/ConeRotationInputs.lean`は片側shiftとconeへのliftを接続し、
`M[1] → cone(inr f)`を構成する。二つの入力は、閉零射fのcycleの左shiftと
cone左包含の左shiftにそれぞれ負号を付けたもの。全Hom上で閉性を証明した。
`Module/ConeRotation.lean`は`cone(inr f) → M[1]`を零の左入力とconnecting mapから構成する。
右包含とconnectingの合成が零であること、順方向≫逆方向が恒等であることも証明した。

入れ子のconeの評価では、評価された加群射と既存のcone包含が命題的に等しい。
`Complexes/ConeRotation.lean`はこの等式を明示的に保持してMathlibの回転比較を移送し、
cochain公式・合成公式・二つの境界公式・connectingとの可換式を公開する。
両方の加群比較射の評価が、この指定された既存比較射と一致することを証明した。
全dg自然性をobjectwiseなホモトピーの存在だけに弱めていない。

Checks.ConeRotationのビルドと直接実行で主要21宣言を監査した。標準公理のみ。累計998宣言。
StageSix・既存Spectra.StageTwoを含む回転比較入口の同時ビルドも成功（2534 jobs）。
U10は未完。次は全dg自然な収縮を構成し、K(D)の回転同型と三角形の回転閉性へ運ぶ。


### 13.70 U10t8：全dg自然な回転収縮と標準三角形の回転同型

`Module/ConeRotationHomotopy.lean`は二つの次数−1の主Hom要素を、coneの包含・射影の
通常順の斉次合成で構成する。第一はconnecting後の回転比較と標準包含を結び、
第二は逆射≫順方向射を恒等射へ収縮する。それぞれの微分を主Hom内で証明し、
全dg自然な加群ホモトピーを得た。objectwiseホモトピーの存在だけを使用していない。
connectingとの厳密な可換式、K(D)の第三対象の同型、商関手のshift比較を含めた同型も公開する。

`Module/ConeRotationTriangle.lean`の`moduleHomotopyConeRotationIso`は
`(moduleHomotopyConeTriangle f).rotate ≅ moduleHomotopyConeTriangle (moduleConeInr f)`を与える。
connectingのホモトピーと商のshift比較の自然性により三つの可換条件を検証した。
三角形のクラスの順方向の回転閉性`moduleDistinguished_rotate`を得た。
既存の第一/第二射の零合成と合わせ、第二/第三射、および第三射/shiftした第一射の零合成も証明した。

受入入口4本（LeftShiftElements・ConeLift・ConeRotation・ConeRotationTriangle）と
StageSix・既存Spectra.StageTwoの最終同時ビルドは成功（2539 jobs）。
本段階の主要16宣言を含む今回の主要53宣言を直接実行で監査し、標準公理のみ。累計1014宣言。
担当Leanのsorry/admit/新規axiomは0件、担当差分の空白検査は成功。
全体文書検査は担当外のPaper.Section5.SelectedParameterPositivityの未生成oleanで停止した。
共有ルートimportと担当外の並行変更は編集していない。

U10全受入は未完。回転の順方向を示しただけでPretriangulatedを宣言しない。
次は以下を実装する。

1. `moduleShiftHom`でconeのfst/sndを移し、今回のliftで
   `moduleShiftObj s (moduleCone f) → moduleCone (f⟦s⟧')`を構成する。
   左包含のshiftと既存の境界延長で逆射を構成し、各評価をMathlibの`mappingCone.shiftIso`と照合する。
2. 標準三角形の整数shift比較、三角形のクラスのshift閉性を証明する。
   今回の回転同型と負shiftを組み合わせて逆回転閉性と回転の同値条件を完成させ、Pretriangulatedを構成する。
3. 八面体条件、acyclic部分圏の三角閉性とVerdier商比較、D(D)の三角構造、
   主局所化関手と一対象A比較の三角性を証明する。

共有モデル圏・Quillen・転送・SM7への新しい不足要求はない。


### 13.71 U10t9：cone shiftの既存比較とshift交換の整合性

`Complexes/ConeShift.lean`は加群射のshiftの評価と既存複体のshift射の等式を
明示的な引数に取り、Mathlibの`mappingCone.shiftIso`を指定されたconeへ移送する。
両射のcochain表示、lift/descの境界条件、右包含・connectingとの可換式を証明した。
`Module/ShiftElements.lean`は主Homのshift射を任意の斉次要素に適用した成分と微分を公開する。
成分の符号は(-1)^(s*q)で、既存の豊穣shiftをそのまま使用する。

`Module/ShiftCompatibility.lean`は、加法的な商関手のshift比較と充満・本質的全射性を使い、
K(D)の各整数shiftが加法的であることを証明した。
評価でshift交換同型が既存複体の交換同型に一致することも証明した。
Checks.ConeShiftCompatibilityのビルドと直接実行で主要11宣言を監査し、標準公理のみ。累計1025宣言。
U10は未完。次はcone shift同型を実際の加群圏に構成し、標準三角形へ運ぶ。


### 13.72 U10t10：実際のdg加群圏でのcone shift同型

`Module/ConeShiftElements.lean`はconeのfst・snd・左包含を既存の主Hom shift射で移す。
各成分はMathlibのshift比較の入力そのもので、次数1と−1の要素に(-1)^sを伴う。
liftの閉性とdescの境界条件を、全次数Hom内で証明した。
`Module/ConeShift.lean`は既存のlift/desc APIから両方向の加群射を構成する。
評価が指定された既存複体のcone shift同型の両射に一致すること、両合成が恒等射であることを証明した。
`moduleConeShiftIso s f`は`moduleShiftObj s (moduleCone f) ≅ moduleCone (moduleShiftMap s f)`であり、
ホモトピー圏だけでなく実際の閉零加群圏での同型である。

Checks.ConeShift・StageSix・既存Spectra.StageTwoの同時ビルドは成功（2523 jobs）。
主要16宣言の直接実行による公理監査は標準公理のみ。累計1041宣言。
U10は未完。次はこの同型を標準三角形のshiftへ運び、逆回転閉性とPretriangulatedを構成する。


### 13.73 U10t11：cone shiftの符号付き可換square

`Module/ConeShiftSquares.lean`は、整数shiftの符号を用いる自己同型と、評価関手による
符号スカラーの保存を公開する。実際の加群圏で、shiftした右包含とcone shift同型の
可換式、およびshiftしたconnecting・shift交換同型・cone shift同型の可換式を証明した。
後者では符号を合成全体へ作用させる表示と、第一因子へ作用させる表示を
`Linear.units_smul_comp`で区別し、Mathlibの既存複体比較と照合している。

Checks.ConeShiftSquares・StageSix・既存Spectra.StageTwoの同時ビルドは成功（2525 jobs）。
受入Checksの直接実行で主要5宣言を監査し、標準公理のみ。累計1046宣言。
担当Leanのsorry/admit/新規axiomは0件。
全体文書検査は担当外のPaper.Section5.ApproximationSecondComparisonの未生成oleanで停止した。

U10全受入は未完。三角形shift同型とPretriangulatedの草稿は未検証・未コミットである。
次は登録shiftと明示shiftを使う三角形の型変換を、coneに依存しない構成子へ分離する。
その後、逆回転閉性、Pretriangulated、八面体、acyclic部分圏とVerdier商、
D(D)の三角構造と局所化・一対象比較の三角性を順に完成させる。
共有モデル圏系列への新しい不足要求はなく、担当外ファイルは変更していない。


### 13.74 U10o1：八面体に用いる既存複体の合成cone比較

`Complexes/ConeComposition.lean`は、θ=f≫gと、指定されたcone射χとの等式を明示的に保持し、
Mathlibの`mappingConeCompHomotopyEquiv`をcone(g)とcone(χ)のホモトピー同値へ移送する。
両射のcochain表示、順方向≫逆方向の恒等式、逆順の合成を恒等射へ収縮する次数−1の
cochainと境界式、右包含・connectingとの二つの可換式を公開した。
これにより、後続の加群構成で評価された射とMathlibの射を定義的等式と仮定する必要がない。

Checks.ConeCompositionComplexes・StageSix・既存Spectra.StageTwoの同時ビルドは成功（2501 jobs）。
Checksの直接実行で主要7宣言を監査し、標準公理のみ。累計1053宣言。
これは既存複体側の比較であり、K(D)の八面体公理の完成ではない。
次は全dg自然な主Hom要素から両射と収縮を構成し、この比較へ評価で接続する。
三角形shift比較・Pretriangulatedの検証も継続中で、U10全受入は未完である。


### 13.75 U10t12：閉零加群圏の標準cone三角形の整数shift同型

`Module/ConeShiftTriangleOrdinary.lean`は、明示的な加群shift射を可換条件として受け取る
三角形同型の構成子を公開する。目標と入力の可換条件を同じshift表示へ正規化し、
巨大な豊穣coneの内部構成の展開を避ける。
`moduleConeTriangleShiftIso`は、shiftした標準cone三角形とshift射の標準cone三角形を比較する。
第一対象の比較は恒等、第二対象は(-1)^s倍、第三対象は既存の実際のcone shift同型である。
三つの可換条件を、§13.73の符号付き可換式から証明した。
`Module/TriangleShiftMap.lean`は、shiftと可換な加法的関手でこの種の同型を移す補助構成子を
任意の圏・関手について証明する。共有モデル圏一般論を追加していない。

Checks.ConeShiftTriangleOrdinary・Checks.ConeCompositionInputs・StageSix・既存Spectra.StageTwoの
同時ビルドは成功（2530 jobs）。本単位の主要4宣言の直接公理監査は標準公理のみ。累計1057宣言。
K(D)への移送と逆回転閉性・Pretriangulatedの検証は継続中で、U10全受入は未完である。


### 13.76 U10o2：合成cone比較の全dg自然な順方向射

`Module/ConeCompositionInputs.lean`は、標準cone射χ:cone(f)→cone(f≫g)と、
cone(g)からcone(f)への次数1・cone(f≫g)への次数0の主Hom要素を構成する。
前者はfst(g)の後にinr(f)を合成したもの、後者は零とinr(f≫g)からのdesc要素である。
次数1の入力の閉性と、二つの入力を結ぶ境界式を主Hom内で証明した。
`moduleConeCompHom`は既存の全Hom上のliftから得られる
cone(g)→cone(χ)の実際の加群射であり、評価が§13.74の既存複体比較の順方向射と一致する。
objectwiseな射やホモトピーの存在だけに弱めていない。

`Complexes/ConeComposition.lean`には、このliftの入力境界式を追加した。
複体成分の証明ではCochain.extを明示し、ModuleCatの元まで自動でextを進めない。
§13.75の同時ビルドは成功（2530 jobs）。本単位の主要11宣言をChecks.ConeCompositionInputsの
直接実行で監査し、標準公理のみ。累計1068宣言。

U10全受入は未完。次は逆方向のdesc射と全dg自然な次数−1の収縮を構成し、
K(D)で合成cone三角形がdistinguishedであることから八面体公理へ接続する。
三角形shift比較のK(D)への移送とPretriangulatedも検証を継続している。


### 13.77 U10o3：合成cone比較の全dg自然な逆方向射

`Complexes/ConeCompositionDesc.lean`は、逆方向比較に用いる二つのdesc境界式を、
θ=f≫gおよび指定されたcone射χとの等式を保持して証明する。
`Module/ConeCompositionDesc.lean`は次数−1の二つの主Hom要素を通常順の斉次合成で構成し、
それぞれの微分が指定された閉零射のcycleになることを主Hom内で証明した。
二重のdescから、cone(χ)→cone(g)の実際の加群射`moduleConeCompInv`を得る。
評価が既存複体比較の逆射と一致し、順方向≫逆方向が恒等射であることも証明した。

Checks.ConeCompositionDesc・StageSix・既存Spectra.StageTwoの同時ビルドは成功（2523 jobs）。
Checksの直接実行で主要13宣言を監査し、標準公理のみ。累計1081宣言。
U10全受入は未完。逆順の合成に対する全dg自然な次数−1の収縮と、K(D)での同型を次に完成させる。
三角形shift閉性・Pretriangulatedは引き続きカーネル検査の整理を継続している。


### 13.78 U10o4：合成cone比較の全dg自然な収縮とK(D)同型

`Module/ConeCompositionHomotopy.lean`は、coneの二つの左包含・fst(f≫g)・snd(χ)を
通常順の斉次合成で結び、全次数Hom内の次数−1の要素を構成する。
その評価は§13.74の既存複体の収縮cochainと一致し、微分が
逆方向≫順方向のcycleと恒等射のcycleの差になることを主Hom内で証明した。
`moduleConeCompInvHomHomotopy`は全dg自然な収縮であり、各対象だけで選んだ収縮ではない。
`moduleConeCompHomotopyIso`によりcone(g)とcone(cone(f)→cone(f≫g))がK(D)で同型となる。

Checks.ConeCompositionHomotopy・StageSix・既存Spectra.StageTwoの同時ビルドは成功（2524 jobs）。
Checksの直接実行で主要7宣言を監査し、標準公理のみ。累計1088宣言。
U10全受入は未完。次は二つの三角形射の可換式と合成cone三角形を接続し、
このK(D)同型からそのdistinguished性と八面体公理を証明する。
逆回転閉性・Pretriangulatedの受入検証も引き続き必要である。


### 13.79 U10t13：K(D)の整数shift閉性とPretriangulated構造

`Module/ConeShiftTriangle.lean`は§13.75の実際の加群三角形の同型を、商関手のshift比較を
含めてK(D)へ移す。標準cone三角形の同型閉包が任意整数の三角形shiftで閉じることを証明した。
`Module/Pretriangulated.lean`は二回の回転と負shiftの既存比較から逆回転閉性を得て、
回転の同値条件を証明する。既存の同型閉性・自明三角形・射の完成・三角形射の補完と合わせ、
`moduleHomotopyPretriangulated`を登録した。distinguished三角形のクラスは元の標準coneの同型閉包と
定義的に同じであることを明示した。八面体を証明する前にIsTriangulatedは宣言しない。

K(D)の標準cone shift同型は、一般の三角形・関手に関する補助構成子から得られる型を保持する。
shift閉性のカーネル検査は豊穣coneと商shiftの型変換を含むため、その宣言だけ
maxHeartbeats=800000を指定した。他の宣言やビルド全体の上限は変更していない。

Checks.Pretriangulated・Checks.ConeCompositionHomotopy・StageSix・既存Spectra.StageTwoの
同時ビルドは成功（2552 jobs）。Checksの直接実行で主要8宣言を監査し、標準公理のみ。累計1096宣言。
U10全受入は未完。次は合成cone三角形のdistinguished性からK(D)の八面体公理を証明し、
acyclic部分圏の三角閉性・Verdier商比較・D(D)の三角構造と局所化および一対象比較の三角性へ進む。
共有モデル圏系列への新しい不足要求はない。


### 13.80 U10v1：K(D)の評価関手の三角性

`Module/HomotopyEvaluationTriangles.lean`は、商に降ろした評価と元の複体評価の因子分解同型を
公開し、その同型が整数shiftと可換であることをMathlibのQuotient.lift APIから証明した。
shiftと可換な関手の可換squareを三角形の同型へ移す構成子から、評価された標準加群cone三角形と
既存複体の標準cone三角形を比較する。これにより、任意の対象xでのK(D)の評価関手が
すべてのdistinguished三角形を保存するインスタンスを登録した。
この段階にK(D)の八面体公理を前提とせず、§13.79のPretriangulated構造を使用する。

Checks.HomotopyEvaluationTriangles・StageSix・既存Spectra.StageTwoの同時ビルドは成功（2547 jobs）。
Checksの直接実行で主要5宣言を監査し、標準公理のみ。累計1101宣言。
次は評価先のacyclic部分圏の逆像を使い、K(D)のacyclic部分圏の三角閉性を証明する。
U10全受入は未完であり、Verdier商比較・導来圏の三角構造・局所化と一対象比較の三角性も引き続き必要。


### 13.81 U10o5：合成cone三角形のdistinguished性と第三射の比較

`Module/ConeCompositionTriangle.lean`は、cone(f≫g)→cone(g)の標準射を構成し、
cone(χ)の右包含の後に逆方向比較を合成するとこの射になることを証明した。
順方向比較はconnectingと厳密に可換である。
`moduleConeCompTriangle`はcone(f)→cone(f≫g)→cone(g)→cone(f)[1]であり、
K(D)へ移した三角形がχの標準cone三角形と同型、したがってdistinguishedであることを証明した。

第三射の比較では、商関手のshift比較の自然性を一般の関手について先に証明する。
`moduleHomotopyConeComp_mor₃`は、その一般比較から得られる実際の射の等式をそのまま述べる。
三角形のfieldによる表示への型変換を証明の型注釈へ埋め込まず、八面体の構成で使用する。
すべての加群射・収縮は§13.76〜13.78の全dg自然な構成である。

受入入口（Pretriangulated・ConeCompositionTriangle・Triangulated・HomotopyEvaluationTriangles）と
StageSix・既存Spectra.StageTwoの同時ビルドは成功（2557 jobs）。
本単位の主要13宣言の直接公理監査は標準公理のみ。累計1114宣言。
U10全受入は未完。八面体公理の受入記録は次節、acyclic部分圏とVerdier商への接続を引き続き進める。


### 13.82 U10o6：K(D)の八面体公理とIsTriangulated登録

`Module/Triangulated.lean`はK(D)の二つの射を商関手の充満性で実際の加群射へ持ち上げ、
f、g、f≫gの標準cone三角形を選ぶ。二つの厳密な可換squareから三角形射を構成し、
§13.81のdistinguishedな合成cone三角形と、商関手のshift比較を含む第三射の等式を使って
八面体を構成する。MathlibのIsTriangulated.mk'により任意のdistinguished三角形に対する
八面体公理へ移し、`moduleHomotopyIsTriangulated`を登録した。
objectwiseな八面体の存在を仮定せず、全dg自然な射と収縮から証明している。

§13.81の最終同時ビルドは成功（2557 jobs）。初回の直接監査は並行ビルド中の
Complexes.Enrichment.oleanの未生成で停止したため採用しなかった。
依存ビルド完了後にChecks.Triangulatedを再ビルド（2016 jobs）し、直接実行も終了コード0を確認した。
主要1宣言の公理は標準公理のみ。累計1115宣言。実装コミットは126e7be。
§13.79の局所maxHeartbeats指定の理由コメントを指定直後へ移し、行長の警告も修正した。
その変更を含むソースで再ビルド済みであり、共有ビルドの上限を変更していない。

U10全受入は未完。次はacyclic部分圏の三角閉性と指定準同型のVerdierクラスを接続し、
主導来圏の三角構造・局所化関手・一対象A比較の三角性まで完成させる。
共有モデル圏・Quillen・転送・SM7一般論への新しい不足要求はない。


### 13.83 U10v2：主局所化比較の整数shift整合性

`Derived/HomotopyShift.lean`はK(D)から主導来圏への既存局所化関手を保持し、
閉零圏経由の比較自然同型と、二つの局所化の比較逆関手について整数shiftとの整合性を証明した。
Mathlibのshift局所化の普遍性を使い、別の導来圏やshiftへ置換しない。
Checks.HomotopyDerivedShiftを含む導来比較5入口の同時ビルドは成功（2143 jobs）。
Checksの直接実行は終了コード0、主要5宣言の公理は標準公理のみ。累計1120宣言。
U10全受入は継続中。次はacyclic部分圏とVerdierクラスの接続を受け入れる。


### 13.84 U10v3：acyclic部分圏と指定Verdierクラス

`Module/AcyclicTriangulated.lean`は評価関手の三角性を使い、acyclic対象の同型閉性・零対象・整数shift閉性・三角閉性を証明した。
`moduleHomotopyAcyclic_trW_eq`はそのVerdier射のクラスが、既存の指定objectwise quasiIsoと等しいことを標準coneで証明する。
主要6宣言の直接公理監査は終了コード0、標準公理のみ。累計1126宣言。
導来比較5入口の同時ビルドは成功（2143 jobs）。U10全受入には独立入口の統合検証を引き続き要求する。


### 13.85 U10v4：主導来圏の三角構造

`Derived/Triangulated.lean`は指定quasiIsoの左右分数計算と三角構造との適合性を証明し、既存の主導来圏そのものに加法・三角構造を登録した。
K(D)からの既存局所化、標準局所化との比較逆関手が三角的であり、指定関手がacyclic.trWを局所化することも公開した。
主要16宣言の直接公理監査は終了コード0、標準公理のみ。累計1142宣言。
導来比較5入口の同時ビルドは成功（2143 jobs）。U10全受入には独立入口の統合検証を引き続き要求する。


### 13.86 U10v5：標準Verdier商との三角同値

`Derived/VerdierComparison.lean`は主導来圏とacyclic部分圏の標準Verdier局所化との同値を、同じ射のクラスの局所化普遍性から構成した。
局所化との比較自然同型の整数shift整合性、順逆両関手の三角性、counitのshift整合性を証明した。
主要9宣言の直接公理監査は終了コード0、標準公理のみ。累計1151宣言。
導来比較5入口の同時ビルドは成功（2143 jobs）。U10全受入には独立入口の統合検証を引き続き要求する。


### 13.87 U10v6：導来評価と一対象A比較の三角性

`Derived/EvaluationTriangles.lean`は標準加群cone三角形の導来評価を既存複体の標準cone三角形と比較し、任意対象での導来評価の三角性を証明した。
一対象Aの既存DerivedCategoryとの同値について、既存の順方向shift構造を保持したまま、順逆両関手の三角性と逆関手・counitのshift整合性を登録した。
宇宙wと`HasDerivedCategory.{w} (ModuleCat.{u} A)`を明示する。
主要9宣言の直接公理監査は終了コード0、標準公理のみ。累計1160宣言。
導来比較5入口の同時ビルドは成功（2143 jobs）。U10全受入には独立入口の統合検証を引き続き要求する。


### 13.88 U10統合受入・コード固定点

`StageSeven.lean`はU0〜U10の独立入口であり、既存StageSix・共有ルートimportを変更しない。
`Checks/StageSeven.lean`は同じimport下で以下を検査する。

| U10受入条件 | 実装・証拠 |
| --- | --- |
| 任意非有界加群のsemifree解像度 | `Module/Semifree/Resolution.lean`の`exists_semifree_resolution`。semifree・次数ごと全射・quasiIsoを同時に保持。Checks.Semifreeにはℤ・ZMod 2の例もある |
| 全Hom上の射影性 | `moduleSemifree_homotopicallyProjective`。対象ごとのホモトピーではなく全dg自然な主Hom endを使用 |
| 全導来Homと選択独立性 | `Derived/HomBifunctorChoice.lean`。両変数関手・比較自然同型・自己比較・三つの選択の推移整合性 |
| 実際の局所化の射集合 | `Derived/ResolutionHom.lean`のHom同値・roof全射・等式と全dgホモトピーの同値。Hom双関手の存在だけで代用しない |
| 宇宙・余積 | `moduleDerivedLocallySmall`はLocallySmall.{u}。`Derived/Coproducts.lean`は任意J : Type wとSmall.{u} Jで余積を構成。K(D)の余積も同じ条件 |
| K(D)の三角構造 | §13.79・13.81・13.82。全dg自然な回転・合成cone比較と収縮に基づくPretriangulated・八面体 |
| acyclic・Verdier・主D(D) | §13.84〜13.86。acyclic.trW＝既存W、主局所化への三角構造と標準Verdier商との三角同値 |
| 一対象Aとの比較 | 既存`ringDerivedEquivalence`を保持。`Derived/Ring.lean`・`RingCoproducts.lean`・`EvaluationTriangles.lean`で局所化比較・shift・余積・三角性を接続。必要なHasDerivedCategory宇宙を明示 |

最終統合ビルド：Checks.StageSeven・StageSix・既存Spectra.StageTwoを同時に実行し成功（2638 jobs、終了コード0）。
StageSevenの直接実行も終了コード0。主要11宣言の再監査は標準公理のみで、累計には重複加算しない。
導来比較5入口は別途2143 jobsで成功、直接実行45宣言もすべて標準公理のみ。
段階別主要監査の累計は1160宣言。担当Leanのsorry・admit・新規axiomは0件。
Lean v4.35.0-rc4、Mathlib e6bbacd0e1b7307ff6e17da09cd2455f60804fa6をmanifest・checkout双方で再確認した。
文書検査は22 Markdown・311 exposition参照、失敗0件。担当差分のgit diff --checkも成功。
以前の担当外olean不足による文書検査停止は、この最終実行では再現しなかった。

これで§13のU10受入を満たす。D3の左加群/bimodule・D4m・D5〜D10の全完了とは区別する。
この受入コミットをコード固定点とし、以後この依頼ではLeanコードをリファクタリングせず、
比較・共通化候補・後続工程を計画ファイルに記録する。採用済み引用は引き続き0件。
共有モデル圏一般論・他チャットの変更は編集していない。

## 14. U10後のリファクタリング検討（提案のみ、コード変更なし）

固定点は`78e8918`。以下は固定版Mathlibとリポジトリ内の他系列を実際に読んだ比較であり、
一般APIの新設・移動・改名を今回実行するものではない。後続U番号はこの節以降での新しい工程案。
共有側のソースの存在と型を確認したが、その系列全体の受入・公理監査をM5が代行したとはしない。

### 14.1 比較対象と判断

| 比較対象（実際のソース） | dg側との共通点／相違 | 方針 |
| --- | --- | --- |
| Mathlib `Algebra/Homology/HomotopyCategory/Triangulated.lean`の`mappingConeCompHomotopyEquiv`と`IsTriangulated.mk'` | 同じ合成coneの行列・収縮。dg側は評価先の式だけでなく全Hom endの自然性が必要 | `Complexes/ConeComposition*`で既に再利用。objectwise同値をdg同値と同一視する置換はしない |
| Mathlib `Algebra/Homology/DerivedCategory/Basic.lean`の`Triangulated.Localization.pretriangulated`等 | Kからacyclic.trW局所化へ三角構造を降ろす手順が共通 | `Derived/Triangulated.lean`は既に同じ一般構成を使用。新しい局所化型・三角構造移送論を作らない |
| Mathlib `CategoryTheory/Localization/HomEquiv.lean`・`SmallHom.lean` | 前者は二つの局所化間のHom比較、後者は小さい局所化Homの表現。dgの`Category/LocalizationHom.lean`は局所化前後のHom比較 | 適用範囲が異なる。dgのcoyoneda反転条件からの全単射を残し、将来SmallHomの標準表示へのアダプタを検討 |
| Mathlib `HomotopyCategory/KProjective.lean`の`CochainComplex.IsKProjective` | acyclicへの射のホモトピー消滅。dg側は全次数Hom endのacyclic性を定義に使う | 一対象Aについて両条件の同値を橋渡しする候補。任意Dへ普通複体のinstanceを直接流用しない |
| `PerfectComplex/HomotopyCategory.lean`・`CategoryTheory/HomotopyProperty.lean` | `PerfectHomotopy`は有界有限射影複体の通常K(A)内の部分圏。cone閉性から三角閉性を得る一般補題がある | U13の比較先として保持。dgのfinite cellとretractを既存型に定義的同一としない |
| `PerfectComplex/TensorAcyclic.lean`・`HomologicalAlgebra/CochainTensorBoundedAbove.lean` | 前者はstrictly perfect因子と任意quasiIso、後者は両側の上有界性を使う定理 | U12で再利用。ただし後者だけでは任意非有界acyclicを消すK-flat性を証明済みとしない |
| `CategoryTheory/Monoidal/ModuleInternalHom.lean`・`BalancedTensor.lean` | Homは作用のequalizer、tensorは二作用のcoequalizer。dg Hom end・多対象coendと同じ普遍性の形 | 普遍性のパターンを再利用。一つの内部モノイド上のModと、多対象dg圏上の加群を同一視しない |
| `CategoryTheory/Enriched/TensorCotensor.lean`・`EnrichedRepresentability.lean` | 通常Hom随伴と豊穣Hom対象同型を別契約にし、三変数自然性・points比較を保持 | U11/U12で具体的データを詰める候補。dgの既存full Homを別のmapping objectに置き換えない |
| `Spectra/ModelCategory/SimplicialLevelEnriched.lean`・共有`HomotopicalAlgebra/Enriched/TensorCotensor.lean` | tensor/cotensor/mappingのQuillen条件を共有の表現性へ接続 | 同じ抽象契約を使える。ただしdg圏にSSetのSM7を自動付与しない |
| 共有`Quillen/DerivedAdjunction.lean`の`leftChoiceIso`・unit/counitのchoice定理 | dgの解像度選択独立性も同じ局所化普遍性を使うが、現在はモデル構造に依存しない | D4mで既存Mathlib導来関手の証明を供給し比較する。モデル構造をU10の追加前提にしない |
| 共有`Transfer/EvaluationFamily.lean`・`EvaluationSmallness.lean`・`Monoidal/ManyObjectPresentability.lean` | free/evaluation随伴族、presentable生成元、monoid axiomから実際の多対象加群へ転送 | 一般認識・smallness移送は既に共有APIがある。M5はCh(A)の具体的入力とfree/evaluation同型を供給 |
| `CategoryTheory/VerdierKaroubi*.lean`・`Asymptotic/PaperRankQuotient.lean` | Karoubi/Verdier順序同値、shift・三角性・線形性、既存rank比較自然同型 | U17では既存比較へdg入力を接続。並行ファイルの再実装・変更をしない |

### 14.2 優先する整理案と移行条件

**R1（優先度高、一般補題の切り出し候補）**：
`Category/LocalizationHom.lean`の`LocalizationHom.mapEquiv`/`map_bijective`は
任意の`C,E`、独立Hom宇宙、`W : MorphismProperty C`、`L.IsLocalization W`、
`P : C`、`W.IsInvertedBy (coyoneda.obj (op P))`だけを仮定する。
dg固有の依存がないため、将来共有`CategoryTheory/Localization/`相当へ切り出す価値が高い。
Mathlibの二局所化間`Localization.homEquiv`とは異なる型である点をドキュメント化する。
受入は独立宇宙の例、`mapEquiv_apply`、標準局所化と任意局所化での同じ射の計算、
既存`Derived/ProjectiveLocalizationHom.lean`と`ResolutionHom.lean`の再ビルド・公理監査。
旧namespaceのaliasと旧import互換を保ち、共有所有者との合流時にだけ移動する。

**R2（優先度高、三角形比較の補助API）**：
`Module/TriangleShiftMap.lean`の2構成子、`Module/HomotopyEvaluationTriangles.lean`の
`mapTriangleSquareIso`、`Derived/EvaluationTriangles.lean`の`mapTriangleTripleSquareIso`は
任意のshift付き圏・関手と`NatTrans.CommShift`から三角形同型を作る。
共有`CategoryTheory/KaroubiTriangulatedFunctor.lean`にもshift比較を運ぶ実装がある。
共有`CategoryTheory/CommShiftOfPrecomp.lean`は、関手圏での前合成が完全忠実であることから
shift比較とその整合性を延長する一般APIを既に持つ。Karoubi側はこのAPI、dg局所化側は
Mathlibの`Functor.commShiftOfLocalization`を使用している。共通のshift移送を新設せず、
既存APIを再利用した上で、三角形squareの小さな構成子だけを切り出す候補にする。
受入は第三射のshift比較を含む可換式、K/D評価、cone shift、Karoubi側の既存入口。
coneや商shiftを展開する巨大な型注釈へ戻さず、同型を合成する現在の証明形を保つ。

**R3（優先度中、cone行列証明の局所整理）**：
`Complexes/ConeComposition*`、`Module/ConeCompositionInputs/Desc/Homotopy/Triangle`を
「既存複体の証明」「全Hom endの入力境界式」「K(D)への移送」に沿って読むための入口を整理する。
同じ斉次合成・包含・射影の書換えには小さな計算補題が有効だが、一般のpretriangulated dg圏の
巨大な構造体を今導入すると、既存Mathlibとの型変換とカーネル検査が増える懸念がある。
先に現状のビルド時間を基準に取り、代表的な回転・合成cone・shift閉性で比較する。
符号0/−1/1・ZMod 2・全自然な収縮の境界式を移行時の必須検査にする。
局所maxHeartbeats=800000の削減は測定してから判断し、単なる上限引上げを改善としない。

**R4（優先度中、Hom endと内部Homの比較）**：
dgの`moduleHom`は対象族の積と自然性equalizer、内部ModのHomは一つの作用equalizerである。
両者の普遍性のconstructor/ext/naturalityに共通部分がある。
将来、一対象dg algebraの場合の比較同型を先に作り、その実例を根拠に任意Vのend APIを共有へ要求する。
`EnrichedNatTrans`の閉零自然性だけでは全次数Homを置き換えられない。
受入は全パラメータKのHom同型、合成・単位・微分・符号との一致。普通Hom集合の同値だけでは不足。

**R5（後続機能と合わせる、解像度と導来関手）**：
`ModuleProjectiveResolution`のπ・HP・quasiIsoはdg固有の計算証拠を保持する。
共有側のMathlib `IsLeftDerivedFunctor`と比較すれば、選択独立性の一部を標準一意性へ委ねられる可能性がある。
ただしD4m前の独立した局所化計算を共有モデル圏依存に変更しない。
受入は比較自然変換の向き、πでの計算、自己/推移整合性、両変数Hom、導来随伴のunit/counit。

**R6（保守性、段階入口・監査台帳）**：
StageOne〜StageSevenは互換入口として保持し、将来は公開API索引と監査宣言一覧を
同じデータから生成する案を検討する。過去の累計と再監査件数を区別できる形式が必要。
Checksを削って件数だけ揃える整理はしない。共有ルートimportの変更をこの整理の一部に含めない。

推奨順はR1/R2の小さな共通補題→U11での具体的比較→R4/R5の判断。
R3の大規模なcone抽象化は最後に評価する。今回、これらのLean変更は一切実施していない。

## 15. 次工程の詳細計画（未実装、U11〜U17）

U0〜U10は右dg加群と導来圏の主経路。D3の左加群/bimodule、D5以降を以下に分割する。
各小単位は「定義＋主要法則＋具体例＋対象ビルド＋主要宣言公理監査＋計画記録」を一コミットの基本とする。
API名・配置は案であり存在宣言ではない。着手時に固定版と共有APIを再検索する。
任意可換環、非有界、dの次数+1、ホモトピー−1、Mathlib Enriched主モデルの契約を維持する。

### 15.1 U11：左加群・bimodule・相対tensor（D3の残りとD5入口）

| 小単位・配置案 | 作業・公開契約 | 受入・依存 |
| --- | --- | --- |
| U11a `Module/Left.lean` | 右加群のdg oppositeによる左加群、二重opposite比較。共変EnrichedFunctorとの比較と斉次作用を公開 | 任意A、独立対象宇宙、oppositeの(-1)^(pq)、一対象A、正負次数とZMod 2。U10のみで着手可 |
| U11b `Bimodule/Basic.lean` | 右B・左C作用を持つbimoduleを符号付き交換則付きで定義。Bᵒᵖ⊗CからCh(A)への共変EnrichedFunctor表示との同値を構成 | 積dg圏のHom tensor・合成の交差符号・単位・結合を先に証明。左右の作用の順を成分で固定 |
| U11c `Tensor/Balanced.lean` | 右M・左Nについて、⊕_{x,y} M(y)⊗B(x,y)⊗N(x)の二作用を⊕_x M(x)⊗N(x)へ送りcoequalizerを定義 | 添字がu-small、各tensorと必要余極限の宇宙を明示。balanced射とのHom同値、ext、両変数mapと法則、符号付き成分式 |
| U11d `Tensor/Yoneda.lean`・`Tensor/Bimodule.lean` | representable⊗_B N≅N(x)、M⊗_B左representable≅M(x)、bimodule合成の残る作用 | 同型が全dg自然であり一対象Aでは既存cochainTensorと比較できる。braidingの順とYoneda unit/counitを検査 |
| U11e `Tensor/Coherence.lean` | Fubini/coequalizerの普遍性から単位・結合比較。一般に成り立つ余極限保存とtensor–Hom随伴を構成 | unit/associatorの三角・五角、三変数自然性。既存BalancedTensorの一モノイド版を多対象版と無条件に同一視しない |

U11の全受入はcoequalizer対象を置くだけでは満たさない。評価同型・残る作用・自然性・整合性まで必要。
共有G2/G5/SM7の完成は前提にしない。一般coendの不足は小さな型として§16へ追加して独立部分を続ける。

### 15.2 U12：K-flatと導来tensor（D5）

| 小単位・配置案 | 作業・公開契約 | 必須の区別・受入 |
| --- | --- | --- |
| U12a `Tensor/KFlat.lean` | A上K-flatと、B上の右加群の相対K-flatを別predicateにする。後者はacyclic左B加群とのtensorがacyclic | 対象・射のquasiIso保存との同値、shift/cone/retract/必要な余積閉性。homotopically projectiveとの関係を定義で仮定しない |
| U12b `Tensor/Semifree.lean` | representable、sphere-free段階、graded-split拡張、逐次余極限からsemifree右加群の相対K-flat性を証明 | U11 YonedaとModuleCatの余極限完全性を使用。Hom_BのA-flat性なしの相対結果と、Hom_B(y,x)のA-K-flat性を要するobjectwise結果を分ける |
| U12c `Tensor/BoundedAbove.lean` | 次数ごとflatかつ上に有界なA複体は任意acyclic複体を消す | 既存bounded-flat定理と下からのstupid truncationのfiltered colimitを使う案。tensorのcolimit保存とfiltered colimitの完全性を明示。相手も上に有界な既存定理だけで終了しない |
| U12d `Derived/Tensor.lean` | U10のsemifree解像度から右加群・左加群の導来tensorを指定D上へ構成 | 右解像度間のhomotopy equivalenceとtensorのhomotopy保存、左変数のquasiIso保存を証明。両変数自然性、任意解像度の計算同型、自己/推移整合性 |
| U12e `Derived/BimoduleTensor.lean` | 導来bimodule合成・単位・結合比較とcoherence | Bᵒᵖ⊗C上semifreeからBに関する相対K-flat性を得る条件を別証明。必要な相手側Homのlocal K-flat性、又はdg圏の解像度を明記。無条件の二変数置換を仮定しない |
| U12f `Tensor/ScalarExtension.lean`・`Derived/ScalarExtension.lean` | A→A'のdg圏・加群・tensorの係数変更、restriction/extension随伴と導来比較 | underivedの直和/coequalizer比較とquasiIso保存条件を区別。A'のA-flat性なしの導来版を用意し、underivedとの一致に必要なK-flat仮定を明記。unit/assocと自然性を含む |

一対象Aでは通常の複体tensor・導来tensorと整合することを確認する。
U12の局所化による構成はD4mを待たず進める。Quillen bifunctorとしての再解釈だけ共有ゲートを待つ。

### 15.3 U13：perfect・compact・dg enhancement（D6）

| 小単位 | 作業と受入 |
| --- | --- |
| U13a `Perfect/FiniteCell.lean` | representableの有限和・整数shift・coneによるfinite cellを定義し、生成対象への依存・有限操作の証拠を保持。有限cellの全dg Homの射影性を再利用 |
| U13b `Perfect/Basic.lean` | D(B)内でfinite cellのretractからPerfを定義。thick閉性、Karoubiとの比較、compactに使う余積宇宙をuに固定。全加群圏の対象宇宙をsmallと仮定しない |
| U13c `Perfect/Compact.lean` | representableのHom＝評価のホモロジーをU10 Hom計算から証明し、u-small余積保存とcompact生成性を証明。Perf⇒compactを先に受け入れる |
| U13d `Perfect/CompactConverse.lean` | compact⇒Perfを証明するか、定義済みの圏・生成集合・宇宙に限定してDG-PERを採用ゲートへ提出。引用採用前に結論を定理として使わない |
| U13e `Perfect/Enhancement.lean`・`Perfect/RingComparison.lean` | homotopically projectiveな代表上の全Homを使うdg enhancementと小さい代表系。単なるD内retractの存在からstrict dg retractを選べるとしない。一対象Aの既存PerfectHomotopyとの比較をshift/cone/retract・線形性付きで構成 |

小さいenhancementは対象のコード化と代表の選択を別に検証し、局所小性だけから対象集合のsmall性を結論しない。
既存PerfectComplex/Idempotent*・Karoubi三角構造を再利用し、そのファイル群は変更しない。
U13a–eの最終受入・有限射影retract代表・元の比較同値の記録（2026-10-17）：[`dg-theory-u13-acceptance.md`](dg-theory-u13-acceptance.md)。

### 15.4 U14：指定dg生成元とendomorphism表示（D7）

U14a：U13のenhancement内の指定対象EからEnd(E)を一対象dg algebraとして定義し、
Hom(E,−) bimodule・evaluationと単位/余単位を構成する。
U14b：thick生成仮定の下でPerf上の比較を証明し、Hom quasiIsoと本質的全射の証拠を分ける。
U14c：導来圏全体の同値はcompact生成性がある場合だけ扱い、DG-GEN/DG-MORの採用候補とする。
生成集合を無限直和で一対象にまとめた際にcompact性が失われ得ることを仮定表に残す。
受入は既存Yoneda・導来tensorとの比較、shift/三角性・係数変更図式。
U14a–cの実装・明示的仮定・受入記録（2026-10-17）：[`dg-theory-u14.md`](dg-theory-u14.md)。

### 15.5 U15：明示的dg商（D8）

U15a `Quotient/Paths.lean`：full B⊂D、有限pathの添字、ε_bの次数−1、path項の直和とtensorを定義。
対象・path・Homの宇宙と空pathを固定し、元のHomが非正とは仮定しない。
U15b `Quotient/Differential.lean`：各Homの微分とdε_b=idをLeibnizで延長、d²=0、単位・結合・通常合成と豊穣合成の符号比較。
U15c `Quotient/Universal.lean`：Bの像の指定収縮を持つdg関手との厳密普遍性。収縮の存在だけと、収縮を選んだデータを区別する。
U15d `Quotient/ScalarExtension.lean`：path添字を固定した係数変更の同型・単位/合成整合性。underivedの構成法則として証明する。
U12f・U15d の係数変更の実装・明示仮定・検証記録：[dg-theory-scalar-extension.md](dg-theory-scalar-extension.md)。
U15e：局所K-flat仮定の版とdg圏の分解を使う版を分け、定義済みtriaのVerdier商と比較する。
局所K-flat版はU17a・U13dを終えたチャットが`Quotient/DerivedComparison*.lean`や
`Verdier/`で担当し、続けてU17bの局所K-flatの場合も扱う。
このチャットはU12e受入→U16の後に分解版を担当し、局所K-flat版の定義・比較定理を
読み取り専用で再利用して、分解とその変更に関する比較へ接続する。重複実装はしない。
現行§0の指定により、DG-DRの引用採用が必要になったら
採用せず停止して報告する。
局所 K-flat 版 U15e・U17b の担当記録：[dg-theory-u17a-u13d.md](dg-theory-u17a-u13d.md)。
元のHomが次数0の場合はpath長rの次数−rと正次数ホモロジー消滅を具体例として証明する。
対象・普遍性まではU11/U12と独立に先行可能だが、導来/Verdier比較はflatnessの受入後とする。

### 15.6 U16：導来Morita（D9）

U16a：U12の導来bimodule合成を使い、指定bimoduleが誘導する導来関手、unit/counit、identity/compを定義。
U16b：dg quasiEquivalenceからのrestriction/extensionが同値であることを、representable・生成性・Hom比較で証明。
U16c：一般bimoduleのMorita判定はperfect性・Hom quasiIso・compact生成の三条件を固定する。
現行§0の指定により、DG-MORの引用採用が必要になったら採用せず停止して報告する。
U16d：Perfへの制限と係数変更・中心作用の自然性、合成のcoherenceを検証する。
三角圏としての抽象同値だけをdg Morita同値の証拠にはしない。

### 15.7 U17：Verdier/KaroubiとM9への接続（D10）

U17a：tria(D)とBの像の三角閉包を定義し、殺す対象クラスの一致を証明する。
U17a・U13d の担当実装と検証記録：[`dg-theory-u17a-u13d.md`](dg-theory-u17a-u13d.md)。
U17b：H⁰(Perf_dg(D/B))とKaroubi(tria(D)/tria(B))の比較を、U15の商とU16の自然性から構成。
局所K-flatの場合はU17a・U13dを終えたチャットが、U15eの局所K-flat版に続けて担当する。
U17c：既存`karoubiVerdierOrderEquivalence`、`paperRankEquivalence`、`paperSequenceComparison`との可換squareをshift・三角性・線形性付きで公開。
U17d：中心局所化・支持・retract、係数変更、Gのstrict作用の比較を個別の図式として検証。
M9の環S・列s・小ランク条件は具体的当てはめで固定し、一般dg定理へ埋め込まない。
無限積のflatness・一般Tへの比較・スペクトルへの次数翻訳はそれぞれ担当系列の入力として分離する。

実施順の主線はU11→U12→U13→U14、U15のpath定義は先行可能、U16→U17で合流。
見積もりは行数でなく上記受入小単位を用い、U11eとU12c/U12eで証明難度を再評価する。

## 16. 共有系列への具体的要求と次の着手点

### 16.1 既存共有APIを使う契約（重複実装しない）

1. **G2/G5、多対象転送**：`SerrePositivity.ManyObjectModelTransfer.modelCategoryOfPresentableGenerators`。
   使用先はD4m。C=Ch(A)、加群圏をM、添字をDとし、L_x=freeAt x、R_x=moduleEvaluation A D x。
   入力は`L_x ⊣ R_x`、基底Ch(A)のModelCategory・CofibrantlyGenerated I J・HasMonoidAxiom、
   Small.{w} D、LocallySmall.{w} M、HasColimitsOfSize.{w,w} M、各R_xの同サイズ余極限/WalkingSpan保存、
   共通正則基数κに関するI/Jの始域のpresentability、`L_x ⋙ R_y ≅ tensorLeft (Hom_D(y,x))`。
   M5は既存free式K⊗Hom_D(y,x)をbraidingでこの向きへ運ぶ自然同型を供給する。
   初期はw=uで整合を確認し、任意の大きいwの余極限を既存u-small結果から自動推論しない。
   一般認識・small object移送・monoid axiomからのcell制御は共有所有。
2. **G1、導来随伴**：`SerrePositivity.Quillen.derivedAdjunction`とchoice/unit/counit定理。
   使用先はD4mとU12のQuillen比較。対象側のWは既存moduleQuasiIso、
   比較先は既存DerivedModuleCategoryに固定する。M5は通常随伴・左右Quillen条件と
   比較自然変換α/β、そのMathlib IsLeftDerivedFunctor/IsRightDerivedFunctor証拠を供給する。
   既存局所化の対象を差し替えず、U10の計算同型と同じπで一致することを証明する。
3. **G6、表現性・SM7**：`SerrePositivity.Enriched.TensorCotensor`と`EnrichedRepresentability`。
   使用先はU11のtensor–HomとD4mの豊穣モデル比較。V=Ch(A)、C=dg加群閉零圏、
   eHom=既存moduleHom、通常Hom随伴と全Hom対象自然同型、parameter自然性とpoints整合性を供給する。
   現状のtensorFamilyEquivだけではcotensor・三変数全Hom同型の全契約を満たさない。
   `HomotopicalAlgebra/Enriched/TensorCotensor.lean`の一般SM7同値は再実装しない。

### 16.2 未充足の具体的入力・要求

- **D4m基底Ch(A)**：W=quasiIso、Fib=次数ごと全射、Cof=llp(trivial Fib)の非有界射影モデル。
  Iはsphere→disk、Jは0→disk。球/円盤のpresentability、free(J)-cellのobjectwise quasiIso、
  Ch(A)のpushout-product・unit・monoid axiomの具体的証明はM5側の仕事。
  共有転送APIが存在することだけで基底モデルやdg加群モデルの完成を宣言しない。
  Hom_D(y,x)がA上cofibrantであるという仮定を追加して一般ケースを縮小しない。
- **U11 coendの一般化候補**：必要になれば、任意閉対称モノイダルV、u-small豊穣圏B、
  右/左豊穣加群M,N、対象/射の直和とcoequalizer、そのtensorによる保存を仮定し、
  balanced族とcoendからの射の自然同値を求める。使用先U11c〜e。
  既存BalancedTensorは一モノイド版なので多対象版の存在を推定しない。
  共有化の判断を待つ間はCh(A)固有の直和・関係式・符号を担当範囲で進められる。
- **小さい共通補題候補**：R1の局所化HomとR2の三角形squareは現にM5で証明済み。
  共有側へ移すなら独立宇宙・CommShift仮定・旧aliasを維持する。新たな一般論の証明待ちはない。
- **U12/13**：任意非有界相手へのbounded-above K-flat性、relative/objectwiseの比較、
  smallなperfect enhancementはM5の未実装項目。共有に依頼する場合も具体的型・宇宙・使用先を追記する。

次の実装開始点はU11a。最初のコミットは左加群とdg oppositeの比較・符号・一対象例までに限定し、
次にbimoduleの二作用とtensorの交差符号を確定する。
D4mは独立した比較工程として、上の既存共有APIと具体的Ch(A)入力の準備状況を再点検して着手する。
この依頼ではU11以降のLean実装も、§14のリファクタリングも実施しない。


### 16.3 今回の終了確認

U10統合受入コミット78e8918以降、担当Lean・Inputsのコード差分は0件。
追加したのは本計画§14〜§16の比較・提案のみであり、U11の実装やリファクタリングは行っていない。
比較対象の具体的な型・仮定・相違と、各提案の受入検査、次工程の依存・共有への入力を記録した。
計画追記後の文書検査も22 Markdown・311 exposition参照、失敗0件、終了コード0。
担当差分のwhitespace検査は成功。共有ルート・他系列の並行変更はそのまま保持する。


## 17. U11〜U17の実装記録（進行中）

ユーザー依頼「計画に沿ってU17まで完成、こまめにコミット」に基づき、§15の順で実装を開始した。
以前の「U10後はコードを固定」は前依頼の終了境界であり、新しい依頼により後続実装を進める。
共有ルート・共有一般論・他系列の編集を避け、一般論にsorry・引用axiomを追加しない。
Lean v4.35.0-rc4・Mathlib e6bbacd0e1b7307ff6e17da09cd2455f60804fa6を再確認した。

### 17.1 U11a：左dg加群・二重opposite・全次数作用

既存`LeftModule`（共変dg関手）を再利用し、`Module/Left.lean`に二重oppositeの合成比較と
恒等Homを持つ両向きdg関手を構成した。対称braidingの二乗が恒等であることから合成を比較する。
左加群とDᵒᵖ上の右加群の対象データの同値と、その両往復の等式を証明した。
`Module/LeftAction.lean`は全次数作用・単位・豊穣順合成の(-1)^(pq)を公開する。
通常の閉零自然性へ弱めず、既存Hom複体の評価を使う。

Checks.LeftModulesのビルドは成功（1779 jobs）。直接実行も終了コード0、主要11宣言の公理は標準公理のみ。
任意Aと独立対象宇宙、次数−1/0/1、一対象ℤ・ZMod 2の往復を検査した。
段階別主要監査は累計1171宣言。担当差分のgit diff --checkは成功。
U11全体・U17までの目標は継続中。次は全Hom endに値を持つ二作用bimoduleと符号付き交換則、
積dg圏へのuncurrying比較を順に受け入れる。

### 17.2 U11b1：全Hom endによるbimoduleと符号付き交換則

`Bimodule/Basic.lean`はCから右B加群の主dg豊穣圏への豊穣関手として、右B・左C bimoduleを定義した。
BにSmall.{u}を明示し、Cの対象宇宙は独立に保つ。Cを固定した右加群、Bを固定した左加群、
両対象での複体と左作用cochainを公開する。左作用は閉零自然性でなく全Hom endに値を持つ。
`interchange`は主Homの任意斉次要素の自然性から得る二作用のcochain交換則。
`Bimodule/Action.lean`は作用を元へ評価し、左次数qと右次数pを交換する符号(-1)^(qp)、
両作用の単位則を証明した。

Checks.BimoduleActionsのビルドは成功（1785 jobs）。直接実行も終了コード0、主要13宣言の公理は標準公理のみ。
独立したB/Cの宇宙、次数−1/1の交換、ZMod 2の左単位を検査した。監査累計1184宣言。
U11b全体は未完。次はBᵒᵖ⊗Cのdg圏構造とuncurrying比較、左右合成との整合性を検証する。


### 17.3 U11b2：Mathlib transportによるtensor積dg圏と交差braiding

`Category/Tensor.lean`はHomの組の積基底上の豊穣をMathlibのtensorモノイダル関手でtransportし、
対象B×C・Hom_B⊗Hom_Cのdg圏を構成した。単位と合成は同関手のε・tensorμに等しい。
Ch(A)の積monoidal構造だけを既存prodMonoidalから明示する。dgTensorEnrichmentは
重複するグローバルinstanceとして登録せず、Mathlibのtransport instanceを使う。
`Complexes/TensorInterchange.lean`はtensorμと既存cochainTensorShuffleの一致、
中央二因子の次数j,kを交換した符号(-1)^(jk)を、既存の斉次shuffle定理から証明した。

Checks.TensorCategoryの最終ビルドは成功（1770 jobs、警告なし）。直接実行も終了コード0、
主要9宣言の公理は標準公理のみ。監査累計1193宣言。
新しい入口3本と既存StageSeven・Spectra.StageTwoの同時再ビルドも進行中。
U11b全体は未完。次は純粋斉次Homの合成式とcurried bimoduleとのuncurrying比較。


### 17.4 U11b3：tensor積dg圏の斉次Homと合成式

`Category/TensorElements.lean`は純粋tensorから斉次Homを作る`dgTensorElement`と、
豊穣順の合成における交差符号(-1)^(qr)を証明した。
最初のHomの二因子の次数をp,q、次のHomをr,sとする。
各因子内の豊穣順合成をtensorし、中央二因子だけを交換する式であり、
通常順dg合成へ変換する際の追加符号と混同しない。
証明は既存tensorμ/shuffleの比較とtensorMapの斉次式を再利用する。

Checks.TensorElementsのビルドは成功（1771 jobs）、直接実行は終了コード0。
主要2宣言の公理は標準公理のみ。監査累計1195宣言。
U11bは継続中。次は作用族からの全Hom endへの構成子、積dg圏上の関手との両方向比較。


### 17.5 U11b4：全次数自然な作用族からの再構成

`Bimodule/OfActions.lean`はCの対象で添字づけた右B加群と、
各Hom_Cをパラメータとする全次数自然変換族、対象ごとの単位・合成式からbimoduleを構成する。
全Hom endへの射は既存`moduleHomEquiv`の逆写像であり、各評価での計算式を公開した。
既存bimoduleからの作用族の抽出、その単位・合成式、抽出して再構成した際の等式も証明した。
これはcurried作用族の往復であり、積dg圏上の関手とのuncurrying同値を証明済みとはしない。

Checks.BimoduleOfActionsのビルドは成功（1785 jobs、警告なし）。直接実行は終了コード0、
主要6宣言の公理は標準公理のみ。監査累計1201宣言。
§17.3の同時ビルド（新Checks3本・既存StageSeven・Spectra.StageTwo）は終了コード0で成功（2645 jobs）。
既存cone shift三角形の再検証に287秒を要したが、上限や共有APIは変更していない。
§17.4と本節はその後の個別Checksで検証した。
U11b全受入は未完。次はtensor積dg圏のHom射から作用族を抽出し、
本構成子へ接続してuncurryingの両往復・符号を検証する。その後U11cのbalanced tensorへ進む。
U12〜U17、D4m、リファクタリングは今回の実装ではまだ着手していない。


### 17.6 U11b5：通常順tensor合成のKoszul符号

`Category/TensorComposition.lean`は純粋斉次tensorの両因子の符号スカラーをまとめる式と、
通常順合成の交差符号(-1)^(ps)を証明した。最初の射の因子次数をp,q、次の射をr,sとする。
豊穣順合成の(-1)^(qr)へ通常順変換の符号を掛け、指数の差2qrを消去して得る。
これによりMathlibの前向き豊穣合成と通常dg合成のtensor規約を両方公開した。
Checks.TensorCompositionではp=s=1,q=r=0で通常順に負号が現れる例を検査した。

対象Checksのビルドは成功（1772 jobs、警告なし）。直接実行も終了コード0、主要2宣言は標準公理のみ。
監査累計1203宣言。文書検査の直近実行は22 Markdown・311 exposition参照、失敗0件。
担当Leanのsorry/admit/新規axiomは0件、担当差分のwhitespace検査も成功。
次の未完単位はU11bの積dg圏関手とcurried作用族の比較。U17までの目標は引き続き有効である。


### 17.7 U11b6：因子の包含と和次数を指定する合成式

`Functor/Components.lean`はHomのchain map、単位cycleの保存、全斉次合成の保存から
Mathlib dg関手を作る構成子と、既存dg関手の斉次単位・合成式を公開した。
`Category/TensorReindex.lean`は四つの因子次数に加え、四つの中間和次数を指定する合成式。
単に和次数をsimpで書き換える際の依存型のtransportを避け、呼出側の次数の等式を保持する。
`Category/TensorInclusions.lean`は既存freeUnitInsertを再利用して第一・第二因子のHom射を構成し、
全次数単位・合成を確認したMathlib dg関手として両包含を公開した。

Checks.TensorInclusionsとTensorMixedの同時ビルドは成功（1793 jobs）。
本単位の直接監査11宣言は終了コード0、標準公理のみ。監査累計1214宣言。
U11bの全受入は未完。次は混合合成の因子分解と、tensor積上の関手からの作用族の抽出。

### 17.8 U11b7：純粋Homの因子分解と混合交換

`Category/TensorMixed.lean`は純粋tensorのHomが第一因子の包含、第二因子の包含の
豊穣順合成に等しいことを証明した。逆順の合成は同じ純粋tensorに(-1)^(qp)を掛ける。
各単位と中間和次数を明示した§17.7の合成式を使い、有界性や対象のsmallnessを仮定しない。

§17.7の同時ビルドは成功（1793 jobs）。本単位の直接監査2宣言は終了コード0、標準公理のみ。
監査累計1216宣言。次はこの因子分解とdg関手の合成保存から、制限した作用の全次数交換則を得る。
U11b全受入、U11c以降は引き続き未完である。


### 17.9 U11b8：tensor積上の関手から全自然なbimoduleへ

`Bimodule/TensorFunctor.lean`はBᵒᵖ⊗CからCh(A)へのdg関手を両因子の包含へ制限し、
右B加群・左C加群を構成した。混合合成の因子分解とdg関手の合成保存から、
二作用のcochain交換則を証明した。豊穣順の符号と通常cochain合成の符号を二回照合している。
この交換則から全次数のパラメータ付き自然変換を得て主Hom endへ持ち上げ、
§17.5の構成子でcurriedなbimoduleへ変換した。その左作用の評価計算も公開する。
Small.{u} BはHom endへの持ち上げにだけ必要で、制限と交換則にCのsmallnessは要求しない。

Checks.BimoduleTensorFunctorのビルドは成功（1802 jobs、警告なし）。直接実行は終了コード0、
主要7宣言の公理は標準公理のみ。監査累計1223宣言。
U11b全受入は未完。次は逆向きのHom射・単位/合成保存から実際のuncurried関手を構成し、両往復を証明する。


### 17.10 U11b9：uncurryingのHom射と単位保存

`Bimodule/UncurryHom.lean`は右作用と左作用を豊穣順に合成するHomのchain mapを構成した。
純粋斉次tensorでの値は通常cochain合成に(-1)^(pq)を掛けたものであり、全次数成分式を公開した。
左作用の単位cochain、tensor積の単位cycleを恒等cochainへ送る式と、
単位複体からの射としての単位保存も証明した。
これは逆方向関手のHomと単位の証拠であり、合成保存を証明する前にdg関手とは宣言しない。

Checks.BimoduleUncurryHomのビルドは成功（1803 jobs、警告なし）。直接実行は終了コード0、
主要6宣言の公理は標準公理のみ。監査累計1229宣言。
文書検査の直近実行は22 Markdown・311 exposition参照、失敗0件。
次は両因子での制限計算と、二作用の交換則を用いる合成保存、両往復。


### 17.11 U11b10：uncurryHomの両因子での制限計算

`Bimodule/UncurryRestriction.lean`は第一因子の包含の後にuncurryHomを合成すると元の右作用、
第二因子では元の左作用に等しいことを、Hom複体のchain mapとして証明した。
単位cycleの保存と純粋斉次tensorの計算を用い、次数零の射だけには限定しない。

Checks.BimoduleUncurryRestrictionのビルドは成功（1804 jobs、警告なし）。
直接実行は終了コード0、主要2宣言の公理は標準公理のみ。監査累計1231宣言。
次はcochainの四重合成へ交換則を運び、uncurryHomの合成保存を証明する。
両因子の制限計算だけではuncurried dg関手の構成・U11b全受入とはしない。


### 17.12 U11b11：符号付き交換則と四重cochain合成

`Complexes/CochainInterchange.lean`は中央二因子の符号付き交換則を、前後のcochainとの四重合成へ運ぶ。
各中間次数と全次数nを明示し、既存Cochain.comp_assocとスカラー合成則を使って証明した。
合成の結合をobjectwiseに仮定するのでなく、主Homを評価した既存cochainの法則として利用できる。
この補題を次のuncurryHom合成保存へ使用する。

今回の受入入口6本・既存StageSeven・Spectra.StageTwoの同時ビルドは成功（2658 jobs、終了コード0）。
本単位の直接監査1宣言は終了コード0、標準公理のみ。監査累計1232宣言。
担当Leanのsorry/admit/新規axiomは0件、担当差分のgit diff --checkは成功。
U11bの残る受入はuncurried関手の合成保存と両往復であり、その後U11c〜eへ進む。
U17までの目標は引き続き継続中。共有一般論・共有ルート・他系列の変更は編集していない。


### 17.13 U11b12：uncurryHomの全Hom合成保存

`Functor/ComplexValued.lean`と`Bimodule/CochainComposition.lean`は豊穣合成の保存を、
通常cochain合成とその次数積符号で計算する補題を供給する。
`Bimodule/UncurryComposition.lean`は純粋な四重tensorにおいて二作用の交換則を適用し、
両側のKoszul指数の一致を整数の環計算で証明した。
既存の四重直和成分の外延性とTensorProduct.ext_fourfold'により、純粋tensorの計算を
Hom複体全体のchain mapの等式`uncurryHom_comp`へ拡張した。

Checks.BimoduleUncurryCompositionのビルドは成功（1807 jobs、警告なし）。
直接実行は終了コード0、主要5宣言の公理は標準公理のみ。監査累計1237宣言。
単位は§17.10、合成保存は本節で揃った。次は実際の逆方向dg関手と両往復の比較。


### 17.14 U11b13：実際のuncurried dg関手

`Bimodule/Uncurry.lean`は単位・全Hom合成保存を用いて、bimoduleからBᵒᵖ⊗C上の
Mathlib EnrichedFunctorを構成した。両因子へ制限したdg関手が元の右B加群・左C加群と
それぞれ等しいことを、既存の制限計算から証明した。

Checks.BimoduleUncurryのビルドは成功（1809 jobs、警告なし）。直接実行は終了コード0、
主要3宣言の公理は標準公理のみ。監査累計1240宣言。
次は二作用によるbimoduleの外延性を使い、curried/uncurriedの両往復を証明する。


### 17.15 U11b14：両往復の証明とU11b受入

`Bimodule/Ext.lean`は両因子への制限が等しいbimoduleの等式を、
主Hom endの評価による外延性から証明した。作用族の射の型が対象に依存するため、
対象関数を先に同一視し、関手の射の射影には局所的なHEqを用いる。
`Bimodule/TensorComparison.lean`はtensor積上の関手の純粋tensorの像を両制限の合成として計算し、
curried/uncurried変換の両往復の等式と`bimoduleEquivTensorFunctor`を公開した。
これは対象データの同値であり、まだ構成していない豊穣関手圏全体の豊穣同値を宣言するものではない。

これでU11bの二作用・Koszul交換則・積dg圏・共変EnrichedFunctor表示との同値を満たす。
対象宇宙v,wは独立、Hom endを作るためのSmall.{u} Bのみ明示する。
通常順と豊穣順のtensor合成の符号は§17.4/17.6で照合済み。

Checks.BimoduleTensorComparison・Uncurry・UncurryCompositionと既存StageSeven・Spectra.StageTwoの
同時ビルドは成功（2661 jobs、終了コード0）。本単位の主要7宣言の直接実行も終了コード0、標準公理のみ。
任意A・独立宇宙の両往復に加え、一対象ℤ・ZMod 2の例を検査した。監査累計1247宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。担当Leanのsorry/admit/新規axiomは0件、
担当差分のgit diff --checkも成功。共有ルート・共有一般論・並行変更は編集していない。

U11全体は未完。次はU11cの多対象balanced tensorを、二作用の余等化子として構成し、
balanced族との普遍性、両変数mapと法則、符号付き成分式まで証明する。
その後U11d/eのYoneda評価・残るbimodule作用・単位/結合coherenceへ進む。U12〜U17も継続対象である。


### 17.16 U11c1：多対象balanced tensorと普遍性

`Tensor/Actions.lean`は既存moduleActionChainをsigned braidingで右側へ運び、
M(y)⊗D(x,y)→M(x)の作用を構成した。成分式は加群値の次数rとHom次数pによる(-1)^(rp)を含む。
左作用D(x,y)⊗N(x)→N(y)は既存uncurryRightで構成し、対応する成分式を証明した。
`Tensor/Balanced.lean`は対象族⊕_x M(x)⊗N(x)と関係族⊕_{x,y}(M(y)⊗D(x,y))⊗N(x)を構成し、
二作用の余等化子をbalanced tensorとした。全chain mapのbalanced族とのHom同値、包含/descの計算、
外延性、終域の後合成に関する自然性とdescの後合成則を証明した。
添字DにSmall.{u}を明示し、任意可換環・非有界複体を維持する。一モノイド版のModへ置換しない。

Checks.BalancedTensorのビルドは成功（1823 jobs、警告なし）。直接実行は終了コード0、
主要22宣言の公理は標準公理のみ。任意宇宙と一対象ZMod 2の対象を検査した。監査累計1269宣言。
U11c全受入は未完。次は両変数の射を関係の直和へ運び、降下map・恒等/合成法則・成分式を揃える。
U11d/eのYoneda・残るbimodule作用・単位/結合coherenceとU12〜U17も継続対象である。


### 17.17 U11c2：作用可換な両変数のchain map族の降下

`Tensor/Maps.lean`は二つの加群のchain map族を対象・関係の直和へ運び、
右作用/左作用との可換性から二つの関係射の可換squareを証明した。
これらのsquareから余等化子へ`mapOfFamilies`を降ろし、包含での計算式、恒等・合成法則を公開した。
新しい加群射の型や代替圏は作らず、作用可換な成分族を取る補助APIとしている。
合成の法則は与えられた合成族の作用可換性証拠を受け取り、具体的な加群圏の射への接続で利用する。

Checks.BalancedTensorMaps・BalancedTensor・BimoduleTensorComparisonと既存StageSeven・Spectra.StageTwoの
同時ビルドは成功（2664 jobs、終了コード0、今回の追加ソースに警告なし）。
本単位の直接実行は終了コード0、主要8宣言の公理は標準公理のみ。監査累計1277宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。担当Leanのsorry/admit/新規axiomは0件、
担当差分のwhitespace検査も成功。

U11c全受入は継続中。次は既存右加群圏と、opposite比較で得る左加群の全Hom end圏の実際の射を
成分族へ評価し、その作用可換性を証明してbalanced tensorの双関手にする。
左右作用・降下の符号付き成分式も揃えてからU11cを受け入れる。
U11d/e、U12〜U17も引き続き未完であり、共有一般論・共有ルート・他系列の変更は編集していない。


### 17.18 U11c3：左加群の全Hom豊穣圏と通常射

`Module/LeftCategory.lean`は既存LeftModule対象を保持し、Dᵒᵖ上の右加群との比較で得る
主Hom endを用いてdg豊穣を登録した。閉零左加群圏、右opposite加群へのdg関手、
全Hom endの評価dg関手と通常の複体への評価を公開した。
`Module/LeftMorphisms.lean`は閉零射と単位パラメータ付き全次数自然変換の同値を与え、
実際の射の評価が任意次数の左作用と可換であることを二重opposite比較から証明した。
新しい通常射の構造体や代替加群対象は作らない。

Checks.LeftModuleCategoryのビルドは成功（1783 jobs、警告なし）、直接実行は終了コード0。
主要10宣言の公理は標準公理のみ。監査累計1287宣言。
次は左右の実際の加群射をbalanced tensorの降下mapへ接続し、双関手と成分式を受け入れる。


### 17.19 U11c4：実際の加群圏上の双関手と斉次成分式（U11c受入）

`Tensor/Functor.lean`は左右の閉零加群射を評価し、任意次数の作用との可換性から
既存mapOfFamiliesへ接続した。包含での計算、恒等・合成法則を証明し、
ModuleCategory × LeftModuleCategoryからCh(A)への実際の双関手を構成した。
`Tensor/Elements.lean`は純粋斉次tensorの像、右作用の符号(-1)^(ap)を保持するbalanced関係、
両変数mapの成分式を公開する。右作用の証明ではHom_Dとopposite Hom、評価対象と
元の加群値を明示して型を合わせ、符号や作用の仮定を弱めていない。

Checks.BalancedTensorFunctor・既存StageSeven・Spectra.StageTwoの同時ビルドは
成功（2647 jobs、終了コード0、追加ソースの警告なし）。主要10宣言の直接実行も終了コード0、
公理はpropext・Classical.choice・Quot.soundのみ。監査累計1297宣言。
任意可換環・独立対象宇宙・Small.{u} Dで双関手を検査し、一対象ZMod 2と次数1/-1の関係も確認した。
これで§17.16〜19を合わせ、U11cの対象・普遍性・外延性・両変数map/法則・符号付き成分式を満たす。
U11全体は未完。次はU11dの両側Yoneda評価同型とbimodule合成の残る作用、
その後U11eの随伴・単位/結合比較・三角/五角・全変数自然性を進める。
U12〜U17とD4mは引き続き未完。共有ルート・共有一般論・並行作業ファイルは変更していない。


### 17.20 U11d1：右representable tensorのYoneda評価同型

`Tensor/Yoneda.lean`は右representableのtensor作用を交換後の豊穣合成として計算し、
左加群の作用からbalanced族を構成した。左作用の合成則の符号と右tensor作用の符号は相殺する。
その降下によるyonedaEvaluation、単位Homを挿入するyonedaInsertion、包含と斉次元の計算式、
両合成が恒等であること、実際の複体の同型yonedaIsoを公開した。
逆向きの合成はbalanced関係を単位Homで評価して証明する。
和次数の名前を先に固定し、次数pと0+pやp+qと全次数nのtransportを明示している。
既存freeUnitInsert・signed braiding・非有界tensorの外延性を再利用し、任意可換環を保つ。

Checks.BalancedTensorYonedaのビルドは成功（1834 jobs、終了コード0、警告なし）。
直接実行も終了コード0、主要10宣言の公理はpropext・Classical.choice・Quot.soundのみ。
監査累計1307宣言。任意A・独立対象宇宙、一対象ZMod 2、次数-1/1の評価を検査した。
直前U11cの文書検査は22 Markdown・311 exposition参照、失敗0件。

これはU11dの第一の評価同型であり、U11d全受入ではない。
次は全dg自然性、左representableに関する反対側の同型、bimodule合成に残る全次数作用、
一対象Aの既存cochainTensorとの比較を揃える。その後U11eの随伴とcoherenceへ進む。
U12〜U17・D4mも未完。共有ルート・共有一般論・並行作業ファイルは変更していない。


### 17.21 U11d2：左representable tensorの評価同型

`Module/LeftRepresentable.lean`は二重opposite比較と既存右representableから
共変representable（値D(z,x)）を構成し、任意次数の作用を符号(-1)^(pq)付きで計算した。
`Tensor/LeftYoneda.lean`は右加群のtensor作用からbalanced族を構成する。
三重tensorの両辺の指数は(a+p)b+apとa(p+b)+pbで一致し、既存moduleAction_representableから
作用の結合を得る。その降下評価・斉次成分式・単位Hom挿入・両逆法則・leftYonedaIsoを公開した。
成分式の右作用には(-1)^(ap)が残り、無符号の評価へ変更していない。
`Complexes/AssociatorReindex.lean`は両方の中間和次数を指定する成分補題。
単位次数でp+0をpに合わせる際の依存型transportを、普遍的な再添字付けで処理する。

Checks.BalancedTensorLeftYonedaのビルドは成功（1837 jobs、終了コード0、警告なし）。
直接実行も終了コード0、主要12宣言の公理はpropext・Classical.choice・Quot.soundのみ。
監査累計1319宣言。任意A・独立対象宇宙・Small.{u} D、一対象ZMod 2、次数1/-1の符号を検査した。
担当差分のgit diff --checkも成功。
U11d全受入はまだ未完。両評価同型の全dg自然性、bimodule合成に残る作用、
一対象Aと既存cochainTensorとの比較が残る。次は自然性とパラメータ付きtensor作用を接続する。
U11eとU12〜U17・D4mも継続対象。共有ルート・共有一般論・並行作業ファイルは変更していない。


### 17.22 U11d3：両評価の通常自然性と任意次数の生成元比較

`Module/LeftHomElements.lean`は既存の主Hom endを評価するleftModuleHomπと、
任意次数qの要素と次数pの左作用の交換則(-1)^(qp)を公開した。
これは右opposite加群のmoduleHomElement_naturalityを二重opposite比較で運んだもので、
任意の中間次数を指定した元への評価式も含む。
`Tensor/YonedaNaturality.lean`は両Yoneda評価が実際の閉零加群射と可換であることを証明する。
また全Hom endの任意次数の要素に対する生成元上の比較式を両側で証明した。
左加群変数の生成元比較には(-1)^(qp)が現れ、右加群変数では評価の(-1)^(rp)と合わせて
(r+q)pに一致する。閉零自然性だけを任意次数自然性の代用にはしない。

Checks.BalancedTensorYonedaNaturality・LeftYonedaと既存StageSeven・Spectra.StageTwoの
同時ビルドは成功（2654 jobs、終了コード0、追加ソースの警告なし）。
本単位の主要7宣言の直接実行も終了コード0、標準公理のみ。監査累計1326宣言。
任意A・独立対象宇宙の自然性と、Hom次数-1・作用次数1の符号例を検査した。
担当差分のgit diff --checkも成功。

U11dの全受入は引き続き未完。全次数の生成元比較は得たが、パラメータ付きtensor作用を
余等化子全体へ降ろし、豊穣関手/自然変換として束ねる作業が残る。
次はこの作用とbimodule合成の残る作用を構成し、一対象Aの既存tensorとの比較を進める。
U11eの随伴・単位/結合coherence、U12〜U17、D4mは未完のまま継続する。
共有ルート・共有一般論・並行作業ファイルは変更していない。


### 17.23 U11d4：パラメータ付きbalanced族の普遍性

`Tensor/Parameter.lean`は任意の非有界複体Kについて、K⊗(M(x)⊗N(x))からのchain map族に
二作用の関係を課すParamFamilyを定義した。既に登録したCh(A)の左tensor–Hom随伴で
BalancedFamily(M,N,Hom(K,T))へ移し、既存descからparamDescを構成する。
包含での計算・tensor後の射の外延性・制限と降下のHom同値、終域の後合成とK変数の引戻しを証明した。
降下射を主Hom複体へ転置するparamHomMapと、各包含における計算式も公開する。
共有の一般coendや表現性を再実装せず、この具体的balanced tensorの普遍性として構成している。

Checks.BalancedTensorParameterのビルドと直接実行は終了コード0。
主要13宣言の公理はpropext・Classical.choice・Quot.soundのみ。監査累計1339宣言。
任意A・独立対象宇宙・任意非有界K/T、一対象ZMod 2を検査した。
この普遍性へ全次数自然変換の作用族を渡す段階はまだ未完であり、U11d全受入とはしない。
次はパラメータ付き右作用との可換性と、実際のbalanced作用族の構成・降下を続ける。
U11e・U12〜U17・D4mも継続対象。共有ルート・共有一般論・並行作業ファイルは変更していない。


### 17.24 U11d5：右加群変数の全次数パラメータ付きtensor作用

`Tensor/ParameterRightAction.lean`はKをパラメータとする全次数自然なHom族について、
右tensor作用との可換性をchain mapの等式として証明した。
斉次成分では右作用の(-1)^(rp)と自然性の(-1)^(kp)が((k+r)p)に一致する。
`Tensor/ParameterRight.lean`はこの可換性、元のbalanced関係、associatorの自然性と五角恒等式から
実際のrightParamFamilyを作り、§17.23の普遍性へ渡してrightParamMapを構成した。
包含での計算式、純粋斉次tensorでの作用式を公開する。
主Hom endの評価族に適用したrightHomMapは
Hom_DMod(M,M')→Hom_Ch(M⊗_D N,M'⊗_D N)という実際のchain mapであり、包含での転置計算も証明した。
全次数自然性を入力に取り、通常の閉零自然性だけに弱めていない。

Checks.BalancedTensorParameterRight・Parameter・YonedaNaturalityと既存StageSeven・Spectra.StageTwoの
同時ビルドは成功（2658 jobs、終了コード0、追加ソースの警告なし）。
主要7宣言の直接実行も終了コード0、標準公理のみ。監査累計1346宣言。
担当Leanのsorry/admit/新規axiomは0件、担当差分のgit diff --checkも成功。

U11dの残りは、左加群変数の符号付きパラメータ作用、左右の主Hom写像の単位/合成と交換、
Yoneda比較の豊穣自然性への束ね、bimodule合成の残る全次数作用、一対象Aの既存tensor比較。
特にrightHomMapだけから、まだdg関手の全法則を証明済みとは宣言しない。
次は左変数の作用を構成し、両変数を使うbimodule合成へ進む。
U11e・U12〜U17・D4mも継続対象。共有ルート・共有一般論・並行作業ファイルは変更していない。


### 17.25 U11d6：左加群変数の符号付きパラメータ作用

`Module/LeftParamNaturality.lean`は任意のKパラメータ付き全次数自然族の作用公式と、
左主Hom end評価族の全豊穣自然性を、既存二重opposite比較から証明した。
`Tensor/ParameterLeftAction.lean`はこの公式を任意非有界複体のchain mapの交換式へ束ねる。
`Complexes/ParameterCross.lean`はK⊗(P⊗Q)→P⊗(K⊗Q)の写像、両因子の自然性、
tensor積を横切る整合性、斉次符号(-1)^(kr)を公開する。
整合性は登録済みsigned braidingのhexagonとMathlibのmonoidal coherenceを利用する。
共有の一般SM7・表現性・モデル構造を複製していない。

`Tensor/ParameterLeft.lean`は右作用・balanced関係との自然性とparameterCrossの整合性から
leftParamFamilyを構成し、実際のleftParamMapへ降ろす。
包含と純粋斉次tensorにおける計算、主Hom間のleftHomMap、その包含での転置計算も公開した。
左変数作用はKの次数kと右加群値の次数rによる(-1)^(kr)を保持する。

Checks.BalancedTensorParameterLeft・ParameterRightと既存StageSeven・Spectra.StageTwoの
同時ビルドは成功（2656 jobs、終了コード0、追加ソースの警告なし）。
主要14宣言の直接実行も終了コード0、標準公理のみ。監査累計1360宣言。
任意A・独立対象宇宙・Small.{u} D、一対象ZMod 2、パラメータ次数-1/右加群値次数1の符号を検査した。
担当差分のgit diff --checkも成功。

U11d全受入はまだ未完。左右の主Hom写像は構成できたが、単位/全Hom合成の保存と左右交換を
証明して豊穣関手へ束ねる必要がある。次はこれらの法則とYoneda比較の豊穣自然性、
bimodule合成の残る作用、一対象Aの既存tensorとの比較を進める。
U11e・U12〜U17・D4mも継続対象。共有ルート・共有一般論・並行作業ファイルは変更していない。


### 17.26 U11d7：各変数の実際のdg関手と単位・全Hom合成保存

`Tensor/ElementsExt.lean`は余等化子射の各次数でのepi性と評価後の直和の普遍性から、
任意次数のcochainを純粋生成元で判定する外延性を証明した。次数零版と主Homへのchain mapの外延性も含む。
`Tensor/HomElements.lean`は左右の主Hom写像の任意次数成分式と中間和次数を指定する版を公開する。
`Tensor/HomUnits.lean`は既存Bimodule.complex_unitElementを再利用し、両写像の単位保存を証明した。
`Tensor/HomComposition.lean`は各評価でのHom合成とcochain合成を比較し、両変数の全次数合成保存を証明する。
左変数では(p+q)r+pq=pq+pr+qrを確認し、符号を消した合成へ弱めていない。
`Tensor/Enriched.lean`は以上をDGFunctor.ofHomMapsへ渡し、rightTensorDGとleftTensorDGという
実際のMathlib EnrichedFunctorを構成した。対象/主Homは既存balanced tensorと全Hom endのまま。

Checks.BalancedTensorEnrichedと既存StageSeven・Spectra.StageTwoの同時ビルドは
成功（2672 jobs、終了コード0、追加ソースの警告なし）。主要17宣言の直接実行も終了コード0、標準公理のみ。
監査累計1377宣言。任意A・独立対象宇宙、両dg関手と一対象ZMod 2を検査した。
担当差分のgit diff --checkも成功。

U11d全受入はまだ未完。左右の各変数のdg関手は得たが、両作用の全次数交換、
Yoneda同型の豊穣自然性への束ね、bimodule合成の残る作用、一対象Aの既存tensor比較が残る。
次は左右交換則をcochainの生成元上で証明し、実際のbimodule合成へ接続する。
U11e・U12〜U17・D4mも継続対象。共有ルート・共有一般論・並行作業ファイルは変更していない。


### 17.27 U11d8：左右の全次数交換と固定代表対象のYoneda豊穣自然性

`Tensor/Interchange.lean`は右Hom次数p・左Hom次数qの作用の交換則をcochainの等式として証明した。
生成元でのq(p+r)=pq+qrから交換符号(-1)^(pq)が得られ、微分や次数零の条件を課さない。
`Tensor/YonedaEnriched.lean`は§17.22の生成元比較を、§17.26のdg関手の主Hom写像へ接続した。
固定代表対象zについて、両Yoneda評価が主Hom複体全体と可換であるchain mapの等式を公開する。
Mathlib EnrichedNatTrans.out（閉零の通常自然性）だけで全次数自然性を代用していない。

Checks.BalancedTensorEnrichedNaturality・Enrichedと既存StageSeven・Spectra.StageTwoの
同時ビルドは成功（2680 jobs、終了コード0、追加ソースの警告なし）。
主要3宣言の直接実行も終了コード0、標準公理のみ。監査累計1380宣言。
次数1/1の左右交換の例、任意可換環・独立対象宇宙の全Hom自然性を検査した。
担当差分のgit diff --checkも成功。

U11d全受入はまだ未完。次はbimoduleの転置した作用を左加群の全Hom endへ構成して、
実際のbimodule合成の残る作用へ左右dg関手と交換則を適用する。
代表対象zの変数の自然性と一対象Aの既存cochainTensor比較も別途確認する。
U11eの単位/結合coherence・随伴、U12〜U17・D4mも継続対象。
共有ルート・共有一般論・並行作業ファイルは変更していない。


### 17.28 U11d9：bimoduleの転置した右作用を左加群Homへ持ち上げる

`Bimodule/Transpose.lean`は既存二作用の交換則を逆向きへ書き直し、
右BのHomをパラメータとする左C加群間の全次数自然変換transposeParamを構成した。
CのSmall.{u}を明示して既存moduleHomEquivの逆で左主Hom endへ持ち上げ、
transposeHom・各評価での計算式・単位/合成保存を備えた実際のdg関手transposeDGを公開した。
BとCの対象宇宙は独立。元のbimodule型や豊穣モデルは差し替えていない。

Checks.BimoduleTranspose・BimoduleTensorと既存StageSeven・Spectra.StageTwoの
同時ビルドは成功（2677 jobs、終了コード0、追加ソースの警告なし）。
本単位の主要5宣言の直接実行も終了コード0、標準公理のみ。監査累計1385宣言。
任意可換環・独立宇宙と一対象ZMod 2の転置を検査した。担当差分のgit diff --checkも成功。
次はこの転置と左右tensorのdg関手を合成し、残る二作用を既存bimodule構成子へ渡す。
U11d全受入・U11e・U12〜U17・D4mは引き続き未完。


### 17.29 U11d10：実際のdg bimoduleの相対tensor合成

`Tensor/BimoduleActions.lean`はP（右B・左C）とQ（右C・左E）から、
Q(c,e)⊗_C P(b,c)に残る右B加群と左E加群を既存dg関手の合成として構成した。
全Homの左右tensor交換則から残る二作用の交換を証明し、左EのHomをパラメータとする
右B加群間の全次数自然変換paramTransへ束ねる。
`Tensor/Bimodule.lean`はその単位・合成保存を検証し、既存Bimodule.ofParamTransへ渡して
実際のBimodule A B Eであるcomposeを構成した。
値の式、右BのHom作用、左EのHom作用を各B対象で評価した計算式も公開する。
B/C/Eの対象宇宙は独立。主Hom endとcoendのためSmall.{u} B/Cを要求し、Eのsmallnessは要求しない。
値のtensor順序はQ⊗Pと明記し、無符号でP⊗Qへ交換していない。

§17.28の同時ビルドは成功（2677 jobs、終了コード0、追加ソースの警告なし）。
本単位の主要10宣言の直接実行も終了コード0、標準公理のみ。監査累計1395宣言。
任意A・三つの独立対象宇宙と一対象ZMod 2の実際の合成を検査した。
担当差分のgit diff --checkも成功。

これでU11dのbimodule合成に残る全次数作用を実際の対象として構成できた。
U11d全受入には代表対象zの変数のYoneda自然性と、一対象Aの既存cochainTensor比較がなお残る。
U11eではこのcomposeの単位・結合比較と三角/五角、三変数自然性・随伴を検証する。
U12〜U17・D4mも未完のまま継続する。共有ルート・共有一般論・並行作業ファイルは変更していない。


### 17.30 U11d11：一対象環と既存cochainTensorの比較

`Module/LeftRing.lean`は任意非有界複体の一対象左加群ringLeftModuleと、
任意の一対象左加群の作用が単位保存から定まる式を公開した。
`Tensor/Ring.lean`は左右作用が通常のright/left unitorに一致することから、
任意の一対象右/左dg加群についてbalanced tensorと値の通常tensorの同型ringIsoを構成した。
包含・純粋斉次元での計算、実際の閉零加群射に関する両変数自然性を証明した。
指定複体P/Qの既存SerrePositivity.cochainTensorとの比較ringComplexTensorIsoも公開する。
任意可換環・非有界を保ち、flat性・体・標数の仮定を追加していない。

Checks.BalancedTensorRingと既存StageSeven・Spectra.StageTwoの同時ビルドは
成功（2649 jobs、終了コード0、追加ソースの警告なし）。主要10宣言の直接実行も終了コード0、標準公理のみ。
監査累計1405宣言。任意Aと一対象ZMod 2の非有界tensor比較を検査した。
担当差分のgit diff --checkも成功。

U11dの一対象Aの比較は得られたが、代表対象zを動かすYoneda自然性がなお残る。
次は代表加群のdg Yoneda関手と代表対象のHom作用を、既存全次数Yoneda同型から構成する。
その後U11d受入を照合し、U11eの単位/結合coherence・随伴へ進む。
U12〜U17・D4mも引き続き未完。共有ルート・共有一般論・並行作業ファイルは変更していない。


### 17.31 U11d12：dg Yonedaと代表対象の全Hom自然性（U11d受入）

`Module/YonedaFunctor.lean`は既存dgYonedaIsoの逆からyonedaHomを構成した。
全Hom endの要素を単位元での評価で判定する外延性、成分式、単位・合成保存を証明し、
実際のMathlib EnrichedFunctorであるdgYonedaを公開する。
`Module/LeftYonedaFunctor.lean`はopposite上のYoneda拡張を二重opposite表示へ運ぶ全次数自然族から
左representable間のHom写像を構成し、各評価と斉次成分を計算した。
対象同一視を伴うendへのcastで計算を済ませず、既存moduleHomEquivから直接構成している。
`Tensor/YonedaRepresentative.lean`は両Yoneda tensor評価について、代表対象zのHom変数に関する
自然性を主Hom複体へのchain mapの等式として証明した。反変側のoppositeとKoszul符号を保持する。

Checks.YonedaRepresentative・BalancedTensorRing・BimoduleTensorと既存StageSeven・Spectra.StageTwoの
同時ビルドは成功（2689 jobs、終了コード0、追加ソースの警告なし）。
本単位の主要14宣言の直接実行も終了コード0、標準公理のみ。監査累計1419宣言。
任意A・独立対象宇宙、dg Yoneda、一対象ZMod 2、左代表の次数-1/1の成分を検査した。
担当差分のgit diff --checkも成功。

U11dの受入照合：
- 右/左representableとのtensor評価同型と両逆法則：§17.20/21。
- 加群変数の全Hom自然性：§17.27。代表対象変数の全Hom自然性：本節。
- balanced tensorの左右の実際のdg関手と符号付き交換：§17.26/27。
- bimodule合成に残る全次数作用と実際の対象：§17.28/29。
- 一対象Aと既存cochainTensorの同型・包含/元の計算・両変数自然性：§17.30。
これでU11dを受け入れる。U11全体は未完で、次はU11eのFubini・tensor–Hom随伴、
bimodule合成の単位/結合同型と三角/五角・三変数自然性を進める。
U12〜U17・D4mも未完のまま継続。共有ルート・共有一般論・並行作業ファイルは変更していない。


### 17.32 U11e1：対角bimoduleと右単位の全Hom自然性

`Bimodule/Identity.lean`は既存dgYonedaを対角bimoduleとして公開し、右制限がrepresentable、
左制限が既存leftRepresentableであることを証明した。
`Tensor/RightUnit.lean`はcompose P diagonalの各値のYoneda同型、右Bの全Homに関する自然性、
実際の右B加群同型rightUnitIsoとその両向きの評価計算を構成した。
左Cの全Hom自然性を値ごとに証明し、さらに右B加群の主Hom endの等式へ束ねた。
固定cでの右加群同型だけで、左Cの自然性を済ませていない。

`Module/HomWhisker.lean`は既存Mathlib eHomWhiskerLeft/Rightと加群評価の薄い公開入口。
元のRightModule型の主Hom間の射・複体間の成分射として始域と終域を明示し、各射影での計算を公開する。
一般の豊穣前後合成を複製していない。大きなcompose式について閉零圏/元の加群型の表示を
暗黙のdefeqで揃えた旧証明はカーネルでタイムアウトしたが、この入口と射影計算では数秒で検証できた。

Checks.BimoduleRightUnit・BimoduleTensorと既存StageSeven・Spectra.StageTwoの同時ビルドは
成功（2689 jobs、終了コード0、追加ソースの警告なし）。主要17宣言の直接実行も終了コード0、標準公理のみ。
監査累計1436宣言。任意可換環・独立対象宇宙と一対象ZMod 2で実際の右単位同型を検査した。
担当差分のgit diff --checkも成功。

U11e全受入は未完。左単位、bimodule合成の結合同型、三角/五角、全変数自然性、
Fubini・tensor–Hom随伴・余極限保存は継続対象である。
随伴に必要な次の具体的APIは調査時未公開：
- Ch(A)の固定終域Tに対する反変dg関手：Ch(A)ᵒᵖ→Ch(A)、値Hom_A(P,T)。
  そのHom作用はHom_A(Q,P)→Hom_A(Hom_A(P,T),Hom_A(Q,T))で、全次数符号・単位/合成保存が必要。
- 左Nに対する右加群homRightModule N T：値x↦Hom_A(N(x),T)。
  balanced tensorからTへのchain mapと、この右加群への閉零加群射の自然同値を構成する。
環A:Type uは任意CommRing、Dの対象宇宙vは独立、Homはu。Hom end/余等化子を使う段階でSmall.{u} D。
この具体的dg APIはDG担当内で追加する。共有モデル/Quillen/転送/SM7一般論への重複実装・追加要求はない。
U12〜U17・D4mも未完のまま継続。共有ルート・共有一般論・並行作業ファイルは変更していない。


### 17.33 U11e2：左単位の両作用に関する全Hom自然性（2026-10-16）

`Tensor/LeftDiagonalValues.lean`は任意の右B加群Mについて、対角bimoduleの左制限とのtensorを
M(b)へ比較する同型・包含式・純粋斉次元の式を構成する。
`Tensor/ChangeLeft.lean`の等式輸送と既存leftYonedaIsoを再利用し、評価の符号は(-1)^(rs)である。
`Bimodule/IdentityTranspose.lean`と`Tensor/LeftDiagonalUnit.lean`は対角の転置Hom作用と
tensorの左Hom作用の成分を結び、右Bの全Hom自然性を証明した。
`Tensor/LeftUnitSigns.lean`は任意の右加群に対する作用の結合と符号の補題である。

`Tensor/ElementMap.lean`は包含で指定した射の評価と、balanced tensorの純粋生成元で
Hom複体の前後合成の等式を判定する入口を提供する。
左単位の具体的評価射を展開して自然性を証明した版はカーネルでタイムアウトした。
評価式を満たす任意の射について先に生成元自然性を証明し、具体的評価射は最後に代入する
leftUnitValue_element_naturality_of_evaluationへ分割した。最終ソースに検査上限の引上げや
診断用trace/一時的な上限指定はなく、LeftDiagonalUnitは2.4秒、LeftUnitは3.3秒でビルドされた。

`Tensor/LeftDiagonalHom.lean`は左representableの表示の等式輸送を一般のNについて処理し、
加群変数の全Hom自然性を既存のleftYonedaEvaluation_enriched_naturalityから得る。
`Tensor/LeftUnit.lean`はcompose diagonal Pの値の同型を実際の右B加群同型leftUnitIsoへ束ね、
両向きの評価式、左Cの全Hom自然性、主Hom endでのleftUnitIso_naturalityを公開した。
Aは任意CommRing、B/Cの対象宇宙は独立、Small.{u} Bのみを要求し、Small Cは要求しない。

Checks.BimoduleLeftUnit・Checks.BimoduleRightUnit・Checks.StageSeven・既存Spectra.StageTwoの
同時ビルドは成功（2698 jobs、終了コード0、警告なし）。任意Aと一対象ZMod 2の実際の同型を検査した。
本単位の主要30宣言の直接実行も終了コード0、すべて標準公理のみ。監査累計1466宣言。
担当Leanのsorry/admit/新規axiomは0件。文書検査は22 Markdown・311 exposition参照、失敗0件。

U11e全体は未完。左右の単位比較は両作用の全Hom自然性まで得られたが、
Fubini・tensor–Hom随伴・余極限保存、bimodule合成の結合同型、三角/五角、全変数自然性は継続対象。
次は§17.32の反変Hom dg関手とhomRightModuleから具体的tensor–Hom随伴を構成する。
その後Fubiniと結合同型・整合性へ進む。U12〜U17・D4mも引き続き未完。
共有系列への新規不足要求はなく、共有ルート・共有一般論・他チャットの並行作業ファイルは変更していない。


### 17.34 U11e3：反変Hom dg関手と右Hom加群（2026-10-16）

§17.32で未公開と記録した二つの具体的APIを構成した。
`Complexes/HomContravariant.lean`のhomContravariantDGは、Ch(A)自身の代表右加群を再利用する
実際のdg関手Ch(A)ᵒᵖ→Ch(A)である。Ch(A)全体のSmall.{u}は仮定しない。
値Hom_A(P,T)と、次数pのf:Q→Pが次数qのg:P→Tに作用する式
(-1)^(pq)・(g∘f)を公開した。単位/合成保存は既存representableの証明から引き継ぐ。

`Functor/Opposite.lean`はCh(A)豊穣関手のoppositeとidentity/comp法則を追加する。
両側のKoszul交換はMathlibのbraiding_naturalityを用いて比較し、
任意Vの豊穣一般論を新設していない。
`Module/HomRight.lean`のhomRightModule N TはN.opとhomContravariantDGの合成で、
値x↦Hom_A(N(x),T)、Nの全次数作用による符号付き前合成を持つ実際の右dg加群である。
この対象と作用の構成にDのsmallnessは不要。AとDの対象宇宙も独立に保つ。

`Module/HomRightFunctor.lean`はT→T'の後合成の全Hom自然性をcochainの結合則から証明し、
Small.{u} Dの下で主Hom endの実際の閉零加群射homRightModuleMapへ束ねる。
評価式、恒等/合成法則を持つhomRightFunctor : Ch(A)→ModuleCategory A Dを公開した。
この関手だけでtensor–Hom随伴の完成とはしない。次はbalanced族の条件と、
HomRight加群への全次数自然なchain map族の条件の同値をcurryingで証明し、
既存homEquiv/moduleMapFamilyEquivから随伴・unit/counitと自然性を構成する。

Checks.HomRight・Checks.BimoduleLeftUnit・Checks.StageSeven・既存Spectra.StageTwoの同時ビルドは
成功（2702 jobs、終了コード0、警告なし）。任意可換環・独立対象宇宙、Small Dなしの対象構成、
次数-1/1の負符号、一対象係数ZMod 2、Small Dの下での実際の関手を検査した。
主要13宣言の直接実行は終了コード0、すべて標準公理のみ。監査累計1479宣言。
担当Leanのsorry/admit/新規axiomは0件。文書検査は22 Markdown・311 exposition参照、失敗0件。
担当差分のgit diff --checkも成功。

U11eは未完。tensor–Hom随伴の受入、Fubini・余極限保存、結合同型と三角/五角・全変数自然性を
引き続き進める。U12〜U17・D4mも未完。共有系列への新しい不足要求はない。
共有ルート・共有一般論・並行作業ファイルは変更していない。


### 17.35 U11e4：閉零tensor–Hom随伴・単位/余単位と余極限保存（2026-10-16）

`Tensor/BalancedFamilyElements.lean`は任意のtensor射の族について、balancedなchain map条件を
純粋斉次生成元の式で評価・復元する入口を構成した。右作用の符号(-1)^(rp)を保持する。
この族の判定自体はDのSmall仮定を要求しない。
`Tensor/HomAdjunctionFamilies.lean`は対象ごとのcurryRight/uncurryRightから
balancedFamilyMapEquivを構成した。balanced族と、homRightModule N Tへの全次数自然な
chain map族が同値であり、両逆法則を持つ。自然性を通常の次数零のDの射だけには弱めない。

`Tensor/HomAdjunction.lean`は既存homEquivとmoduleMapFamilyEquivを合成して、主Hom endの
閉零射を値とするtensorHomEquivを構成する。評価での転置式・逆の包含式、M/Tの閉零射に
関する自然性を証明し、Mathlibの実際の随伴tensorHomAdjunctionを得た。
左側rightTensorFunctorの射は既存balanced tensorのmap h idであり、別のtensor対象を導入しない。

`Tensor/HomAdjunctionLaws.lean`は随伴の単位と余単位をこのHom同値で計算する。
単位の評価はbalanced tensorの包含の転置、余単位の包含上の式はuncurryRight(id)である。
余単位は生成元g⊗vをg(v)へ送る。随伴の左右の三角恒等式も公開した。
任意サイズの図式について、存在する余極限をrightTensorFunctorが保存するinstanceを
既存のleftAdjoint_preservesColimitsから構成した。全サイズの余極限の存在を主張してはいない。
Aは任意可換環、全複体は非有界、Dの対象宇宙は独立。主Hom endとcoequalizerにSmall.{u} Dを要求する。

Checks.TensorHomAdjunction・Checks.HomRight・Checks.BimoduleLeftUnit・Checks.StageSeven・
既存Spectra.StageTwoの同時ビルドは成功（2707 jobs、終了コード0、警告なし）。
任意A・独立対象宇宙、一対象ZMod 2、図式の独立した二つのサイズで余極限保存を検査した。
本単位の主要23宣言の直接実行は終了コード0、すべて標準公理のみ。監査累計1502宣言。
担当Leanのsorry/admit/新規axiomは0件。文書検査は22 Markdown・311 exposition参照、失敗0件。

U11eは引き続き未完。今回の随伴は全dg自然な射を持つ閉零加群圏上の通常随伴である。
これだけで、主Hom複体そのもののtensor–Hom同型や、全Hom変数の三変数自然性まで
証明済みとはしない。次は任意パラメータ複体Kに対してParamFamilyとModuleParamTransの
対応を構成し、主Hom複体の同型へ進める。
左加群変数側の余極限保存、Fubini、bimodule合成の結合同型・全変数自然性・三角/五角も残る。
本節の随伴の三角恒等式をbimodule合成の三角整合性と混同しない。
U12〜U17・D4mも未完。共有系列への新しい不足要求はなく、担当外ファイルは変更していない。


### 17.36 U11e5：主Hom複体のtensor–Hom同型と閉零比較（2026-10-16）

`Tensor/ModuleParameter.lean`は既存tensorModule K Mの右balanced作用について
rightAction_tensorModuleを証明した。右作用の交換とtensor加群の作用に現れるKの二つの符号が
打ち消し合い、通常のassociatorの後にK◁rightActionを取るchain mapに一致する。
任意可換環・非有界Kであり、flatnessやK-flatnessは要求しない。

`Tensor/ParameterTensorFamilies.lean`はassociatorの自然性とpentagonから、
Kを外に置いたParamFamilyとtensorModule K MのBalancedFamilyの条件の同値を証明する。
paramTensorFamilyEquivは両逆を持つ。この族の比較にはDのSmall仮定は不要である。
`Complexes/CurryingNaturality.lean`は逆転置のパラメータ前合成と二重転置の自然性を追加した。

`Tensor/EnrichedHomAdjunction.lean`のparamTransEquivは上記比較、§17.35のbalancedFamilyMapEquiv、
既存tensorFamilyEquivを合成し、任意KのModuleParamTransへの同値を与える。
Small.{u} Dの下で既存moduleHomEquivへ接続してenrichedTensorHomEquivを構成した。
その射影計算式とKに関する自然性から、
`enrichedTensorHomIso : Hom_A(M⊗_D N,T) ≅ moduleHom_D(M,homRightModule N T)`
という実際のchain isoを構成し、両逆法則を証明した。
任意Kからの転置がこのiso.homへの後合成と一致することも公開する。
主Hom endと既存Hom複体を保持し、別の弱い自然変換の対象へ置き換えていない。

`Tensor/EnrichedHomPoints.lean`は単位複体からの閉零射でこの比較を評価すると、
§17.35の通常tensor–Hom随伴の転置と一致することを証明する。
二重転置とunitorの比較を一般の複体・射について先に証明し、評価の射影計算で主Homへ戻した。
単なるHom集合の非自然な同値や、次数0だけの同型ではない。

Checks.EnrichedTensorHom・Checks.TensorHomAdjunction・Checks.BimoduleLeftUnit・Checks.StageSeven・
既存Spectra.StageTwoの同時ビルドは成功（2712 jobs、終了コード0、警告なし）。
任意A、独立対象宇宙、Small Dなしの族の比較、任意パラメータK、実際のchain iso、ZMod 2を検査した。
本単位の主要16宣言の直接実行も終了コード0、すべて標準公理のみ。監査累計1518宣言。
担当Leanのsorry/admit/新規axiomは0件。
全体文書検査は共有ルートSerrePositivity.oleanが現在存在しないためexportで停止し、今回は成功としない。
Markdown 22件のローカルリンクは別途検査して失敗0件。担当差分のgit diff --checkは成功。
共有ルートや他チャットのソースを編集・巻き戻ししていない。

U11e全受入は未完。次はこの主Hom同型のM/N/Tの全Hom自然性を公開し、
左加群変数の余極限保存とFubiniへ進める。bimodule合成の結合同型・全変数自然性・三角/五角も残る。
U12〜U17・D4mも引き続き未完。共有一般論への新規不足要求はなく、担当外ファイルは変更していない。


### 17.37 U11e6：右Hom加群のdg関手と終域の全Hom自然性（2026-10-16）

`Complexes/HomCovariant.lean`はCh(A)の左representableを再利用してhomCovariantDGを公開する。
その全次数作用は通常順の後合成で追加符号がなく、閉零射への制限は既存homPostcomposeに一致する。
`Module/HomRightEnriched.lean`は各N(x)からの共変Hom作用を、homRightModule N T間の
ModuleParamTransへ束ねた。前合成と後合成のKoszul交換をcochainの結合則から証明する。
この族はDのSmallを要求しない。

Small.{u} Dの下でhomRightHomMapを既存主Hom endへのchain mapとして構成し、
射影式・斉次元の式・単位/全次数合成保存を証明した。
homRightDG : Ch(A)→RightModule A Dは実際のMathlib豊穣関手であり、Ch(A)全体のSmallは不要。
閉零射への制限は§17.34のhomRightModuleMapと一致することも主Homへのchain mapの等式として公開する。

`Complexes/CurryingEvaluation.lean`は二重転置とassociatorを含む評価の全整数次数の式を提供する。
`Tensor/EnrichedHomElements.lean`はenrichedTensorHomIso.homの各主Hom射影をさらにm/vで評価すると
元のcochainをbalanced tensorの純粋元へ適用する式に一致することを証明した。
`Tensor/EnrichedHomTarget.lean`はこの計算と既存modulePostcompositionMapを用いて、
終域Tの全Homに関するenrichedTensorHomIsoの自然性をHom複体へのchain mapの等式として証明する。
T→T'の閉零射だけに限定していない。

Checks.EnrichedHomTarget・Checks.EnrichedTensorHom・Checks.TensorHomAdjunction・Checks.StageSeven・
既存Spectra.StageTwoの同時ビルドは成功（2674 jobs、終了コード0、警告なし）。
任意A・独立対象宇宙、Small DなしのHomパラメータ族、実際のdg関手、次数-1/1の後合成、ZMod 2を検査した。
主要17宣言の直接実行は終了コード0、すべて標準公理のみ。監査累計1535宣言。
担当Leanのsorry/admit/新規axiomは0件。文書検査は22 Markdown・311 exposition参照、失敗0件。
§17.36で停止した共有ルートolean不足はこの検査では再現しなかった。

U11eは未完。次はMの反変Hom自然性、Nの全Hom自然性と左加群変数の余極限保存へ進める。
Fubini・bimodule合成の結合同型・全変数自然性・三角/五角、U12〜U17・D4mも引き続き未完。
共有一般論への新しい不足要求はなく、担当外ファイル・共有ルートを変更していない。


### 17.38 U11e7：右加群変数の全Hom反変自然性（2026-10-16）

`Tensor/EnrichedHomSource.lean`はenrichedTensorHomIso_source_naturalityを証明した。
始域はM/M'間の主Hom end、値域はHom_A(M'⊗_D N,T)からmoduleHom_D(M,homRightModule N T)への
Hom複体である。左辺はrightHomMapからtensor複体の反変Hom作用を経て転置し、
右辺は既存modulePrecompositionMapで転置後の主Homを前合成する。
この二つがchain mapとして等しい。任意次数の加群射・入力cochain・評価元を保持する。
両辺の(-1)^(pq)を明示して消去し、既存rightHomMapの純粋元計算と§17.37の評価式へ帰着した。
中間の第二因子次数r+pを明示し、次数の可換則だけから依存型の未知次数を推定していない。

Checks.EnrichedHomSourceはT側の自然性と同時importし、任意可換環・独立対象宇宙と一対象ZMod 2で
この実際のchain mapの等式を検査する。同入口・Checks.EnrichedHomTarget・Checks.EnrichedTensorHom・
Checks.StageSeven・既存Spectra.StageTwoの同時ビルドは成功（2681 jobs、終了コード0、警告なし）。
主要1宣言の直接実行も終了コード0、標準公理のみ。監査累計1536宣言。
担当Leanのsorry/admit/新規axiomは0件。文書検査は22 Markdown・311 exposition参照、失敗0件。

これでM/T両変数の全Hom自然性が揃ったが、U11e全受入は未完。
次の具体的dg APIは、任意左N/N'・複体Tに対し
`leftModuleHom A D N N' → moduleHom A D (homRightModule A D N' T) (homRightModule A D N T)`
という反変Hom写像である。DのSmall.{u}、独立対象宇宙v、任意CommRing A : Type uを維持する。
各対象でleftModuleHomπからhomContravariantDGへの写像を合成し、次数p/qでは(-1)^(pq)の
前合成式を持たせる。Nの全次数自然性を使って主Homへ束ね、単位/合成保存と閉零比較を検証する。
これを使うN変数の転置自然性では、leftHomMapでMの次数rを越える(-1)^(pr)と
反変Homの(-1)^(pq)を両方保持する。この具体的APIはDG担当内で構成し、共有一般論を重複実装しない。
左加群変数の余極限保存、Fubini、bimodule合成の結合同型・三角/五角も継続対象。
U12〜U17・D4mも未完。担当外ファイル・共有ルート・並行作業の変更は編集していない。


### 17.39 U11e8：左加群変数の反変右Hom dg関手（2026-10-16）

`Module/HomRightContra.lean`は§17.38の具体的APIであるhomRightContraHomMapを構成した。
leftModuleHom(N,N')からmoduleHom(homRightModule N' T,homRightModule N T)へのchain mapである。
各対象では既存leftModuleEvaluationDGのoppositeとhomContravariantDGの合成を用い、
その斉次作用は(-1)^(pq)を伴う前合成である。左加群主Homの自然性から、右Hom加群間の
全次数自然性を証明し、既存moduleHomEquivでendへ束ねた。

射影計算・斉次計算・単位と豊穣合成の保存を証明し、
homRightContraDG : (LeftModule A D)ᵒᵖ→RightModule A Dを実際のMathlib豊穣関手として公開した。
oppositeの合成符号は各評価の既存dg関手へ運ぶため、全左加群対象のSmall仮定を追加しない。
Small.{u} D、任意CommRing A : Type u、独立対象宇宙vと非有界複体の契約を維持する。

`Complexes/HomContravariantMaps.lean`は閉零射での作用が通常のhomPrecomposeになる式を証明する。
`Module/HomRightContraMaps.lean`は左加群の閉零射での主Hom射影を計算し、
MathlibのforgetEnrichmentOppositeEquivalenceを介して通常の反変関手homRightContraFunctorも構成した。
その各評価の射はhomPrecompose ((leftModuleEvaluation x).map f) Tに一致する。
独自のopposite圏や弱い自然変換の型へ置き換えていない。

Checks.HomRightContra・Checks.EnrichedHomSource・Checks.EnrichedHomTarget・Checks.StageSeven・
既存Spectra.StageTwoの同時ビルドは成功（2682 jobs、終了コード0、警告なし）。
任意A・独立対象宇宙、実際の豊穣/通常反変関手、次数-1/1の負符号、一対象ZMod 2を検査した。
主要17宣言の直接実行は終了コード0、すべて標準公理のみ。監査累計1553宣言。
担当Leanのsorry/admit/新規axiomは0件。文書検査は22 Markdown・311 exposition参照、失敗0件。

U11e全受入は未完。次はこの反変Hom写像とleftHomMapを用い、N変数の転置自然性を証明する。
左加群変数の余極限保存、Fubini、bimodule合成の結合同型・全変数自然性・三角/五角、
U12〜U17・D4mも継続対象。共有一般論への追加要求はなく、担当外ファイルを変更していない。


### 17.40 U11e9：左加群変数の全Hom自然性と三変数の統合検証（2026-10-16）

`Tensor/EnrichedHomLeft.lean`はenrichedTensorHomIso_left_naturalityを証明した。
始域はleftModuleHom(N,N')で、左辺はleftHomMapによるtensorの作用から反変Homを経て転置し、
右辺は§17.39のhomRightContraHomMapを使って転置後の右Hom加群を後合成する。
両辺はHom_A(M⊗_D N',T)からmoduleHom_D(M,homRightModule N T)へのHom複体を値とするchain mapとして等しい。
左辺の前合成の(-1)^(pq)と、tensorのM次数rを越える(-1)^(pr)が、
右辺の反変右Hom作用の(-1)^(p(r+q))に一致することを全整数次数で検証した。
依存する中間次数を明示し、cochainの元の型を通常のHomogeneousにそろえてから評価式を使う。

Checks.EnrichedHomNaturalityはM/N/T三つの自然性を同時importし、任意可換環・独立対象宇宙と
一対象ZMod 2でN側のchain mapの等式を検査する。同入口・Checks.HomRightContra・
Checks.EnrichedTensorHom・Checks.StageSeven・既存Spectra.StageTwoの同時ビルドは成功
（2685 jobs、終了コード0、警告なし）。直接実行の3宣言はすべて標準公理のみ。
M/Tの2宣言は再監査であり、新規はN側の1宣言。監査累計1554宣言。
担当Leanのsorry/admit/新規axiomは0件。文書検査は22 Markdown・311 exposition参照、失敗0件。
担当差分のgit diff --checkも成功。

これで主Hom複体のtensor–Hom同型、閉零随伴との一致、Kパラメータ自然性、
M/N/Tそれぞれの全Hom自然性が揃った。U11e全受入は引き続き未完である。
残るのはN変数の余極限保存、Fubini、bimodule合成の結合同型・全変数自然性・三角/五角。

次の作業は、符号付き交換から
`BalancedTensor.obj A D M N ≅ BalancedTensor.obj A Dᵒᵖ N.toRightOpposite M.toFunctor`
を構成すること。生成元m^r⊗n^sは(-1)^(rs)を伴ってn⊗mへ送る。
右側の左加群はM.toFunctorそのものであり、不要な三重oppositeの表示へ移さない。
順逆は各々のbalanced族の降下で定義し、両逆とNに関する自然性を包含/元で検証する。
次に既存leftModuleToRightOppositeの閉零圏の同値を確認し、右側で証明済みの
rightTensorFunctorの余極限保存へ接続する。この構成をFubiniでのtensor順序の比較にも再利用する。
U12〜U17・D4mは未完。共有一般論への追加要求はなく、担当外ファイルを変更していない。


### 17.41 U11e10：opposite上のbalanced tensorとの符号付き交換（2026-10-16）

`Tensor/BalancedReindex.lean`はbalanced族の生成元関係を、左右作用の出力次数i/jを指定する形で公開した。
`Module/LeftActionComparison.lean`はN.toRightOppositeの二重opposite作用が元の左作用、
M.toFunctorの左作用が元の右作用に一致することを証明する。
`Tensor/SwapFamilies.lean`は任意終域Tについて、D上のBalancedFamily(M,N,T)と
Dᵒᵖ上のBalancedFamily(N.toRightOpposite,M.toFunctor,T)の同値を構成した。
作用の次数の和を途中で無理に同一視せず、上記i/jを指定したbalanced関係を使う。
この族の同値はDのSmallを要求しない。

`Tensor/Swap.lean`はSmall.{u} Dの下で両方の族を各coequalizerへ降ろし、swapHom/unswapHomと
実際のchain isoであるswapIsoを構成した。各包含での式と純粋斉次元の計算を公開し、
両逆法則は既存cochainTensorSymmetryの二乗恒等から証明する。
元m^r⊗n^sは(-1)^(rs)を伴ってn⊗mへ移る。任意可換環・非有界のままでflatnessは要求しない。
右側の左加群はM.toFunctorであり、別の三重opposite対象を作っていない。

Checks.BalancedSwap・Checks.LeftTensorColimits・Checks.EnrichedHomNaturality・Checks.StageSeven・
既存Spectra.StageTwoの同時ビルドは成功（2693 jobs、終了コード0、警告なし）。
任意A・独立対象宇宙、Smallなしの族の同値、実際のchain iso、次数-1/1の負符号、ZMod 2を検査した。
本単位の主要17宣言の直接実行は終了コード0、標準公理のみ。監査累計1571宣言。
担当Leanのsorry/admit/新規axiomは0件。文書検査は22 Markdown・311 exposition参照、失敗0件。

U11e全受入は未完。Nの閉零射に関する交換の自然性と左加群変数の余極限保存は次節で受け入れる。
この交換同型だけでFubini・bimodule合成の結合/三角/五角を完了とはしない。
U12〜U17・D4mも継続対象。共有一般論・共有ルート・担当外ファイルを変更していない。


### 17.42 U11e11：左加群圏の同値と左変数の余極限保存（2026-10-16）

`Module/LeftEquivalence.lean`は既存leftModuleToRightOppositeを保持し、主Hom end上の恒等写像から
FullyFaithfulを構成した。既存ofRightOpposite/to_ofRightOppositeから本質的全射性を証明し、
実際の閉零加群圏の同値leftRightOppositeEquivalenceを得た。全対象のSmallは要求しない。
比較関手の各評価での射が元のleftModuleEvaluationの射に一致することも公開した。

`Tensor/SwapNaturality.lean`はNの閉零加群射gについてswapHomの自然性を、両側の包含と
既存signedSwap_naturalityから証明する。
`Tensor/LeftColimits.lean`は既存map id gを射写像とするleftTensorFunctorを定義し、
leftTensorSwapIsoでleftModuleToRightOpposite ⋙ rightTensorFunctor A Dᵒᵖ M.toFunctorと自然同型にした。
同値関手の余極限保存と§17.35の右変数の余極限保存から、左変数でも
PreservesColimitsOfSize.{w,t}を構成した。図式の二つの宇宙w/tはu/vから独立である。
ここで証明したのは存在する余極限の保存であり、全サイズの余極限の存在ではない。

Checks.LeftTensorColimitsと§17.41の同時ビルドは成功（2693 jobs、終了コード0、警告なし）。
任意A・独立対象宇宙、閉零圏の同値、自然同型、任意サイズの余極限保存とZMod 2を検査した。
本単位の主要9宣言の直接実行は終了コード0、標準公理のみ。監査累計1580宣言。
担当Leanのsorry/admit/新規axiomは0件。文書検査は22 Markdown・311 exposition参照、失敗0件。
担当差分のgit diff --checkも成功。共有一般論・共有ルート・担当外ファイルは変更していない。

これでbalanced tensorの両変数の余極限保存が揃った。U11e全受入はなお未完である。
残るのはFubini、bimodule合成の結合同型・全変数自然性・三角/五角。
次はCh(A)の二つのcoendを交換する普遍性を、既存の直和/coequalizerと今回の保存性から構成する。
P:B→C、Q:C→E、R:E→Fについて、合成の値の順序は
R(e,f)⊗_E(Q(c,e)⊗_C P(b,c)) と (R(e,f)⊗_E Q(c,e))⊗_C P(b,c)である。
生成元の順をR,Q,Pに保ち、比較の成分は通常associatorの逆向きになる。
A : Type uとB/C/E/Fの対象宇宙を独立にし、Small.{u} B/C/Eを要求するがSmall Fは追加しない。
値の比較だけでなく、右Bの全Hom・左Fの全Homに関する自然性を検証して実際のbimodule比較へ束ねる。
その後三角/五角を反復balanced tensorの生成元で検証する。任意Vの一般coend理論は重複実装しない。
U12〜U17・D4mも継続対象。採用済み深い引用は引き続き0件。


### 17.43 U11e12：右パラメータ付きcoendの普遍性と三重生成元の評価（2026-10-16）

Fubiniで外側に置く複体の位置を固定するため、`Tensor/RightParameter.lean`に
RightParamFamily・rightParamDesc・rightParamRestrict・rightParamHomEquivを追加した。
対象ごとの(M(x)⊗N(x))⊗Kからの族について、二つの作用の後に▷Kを取るbalanced条件を保持する。
既存Ch(A)の右tensor–Hom随伴で族をHom_A(K,T)値のBalancedFamilyへ転置し、
同じbalanced tensorのcoequalizerから降下する。右に置いたKをbraidingで移動しない。
各包含との計算、生成元による外延性、制限/降下の両逆法則を証明した。
族自体にはDのSmallは不要。実際のcoendへの降下でSmall.{u} Dを要求する。

`Tensor/ParameterEvaluation.lean`は左右にKを置いた降下の斉次三重生成元の評価式を公開する。
内側のtensorの出力次数lを指定し、固定パラメータと共にcoendへ入れた元の評価が元の族の評価へ戻る。
左降下をcurryRightしたcochainの生成元式も追加した。
すべて任意可換環・非有界K/M/Nであり、flatnessやモデル構造を仮定しない。

Checks.RightParameter・Checks.EnrichedHomNaturality・Checks.LeftTensorColimits・Checks.StageSeven・
既存Spectra.StageTwoの同時ビルドは成功（2695 jobs、終了コード0、警告なし）。
任意A・独立対象宇宙、Small Dなしの族の転置、任意Kの右tensor Hom同値、一対象ZMod 2を検査した。
主要10宣言の直接実行は終了コード0、標準公理のみ。監査累計1590宣言。
担当Leanのsorry/admit/新規axiomは0件。文書検査は22 Markdown・311 exposition参照、失敗0件。

U11e全受入は未完。次はC/Eの両作用にbalancedな三重族から二つの反復coendへの降下を構成し、
共通の三重生成元で両逆を検証してFubini比較へ進む。
Fubiniの同型、bimoduleの結合比較・三角/五角、U12〜U17・D4mはこの補助APIだけでは完了しない。
共有一般論への追加要求はなく、担当外ファイル・共有ルートを変更していない。


### 17.44 U11e13：二重balanced族の左反復coend普遍性（2026-10-16）

`Tensor/FubiniData.lean`はR⊗_E(Q⊗_C N)と(R⊗_E Q)⊗_C N、および
R(e)⊗(Q(c,e)⊗N(c))から両者への包含を定義する。右側の包含は通常associatorの逆向きを使う。
両反復coendからの射が共通の三重生成元で決まることを証明した。
C/Eの対象宇宙v/wは係数環の宇宙uから独立で、各coendにSmall.{u}を要求する。

`Tensor/FubiniFamilies.lean`は内側Cのパラメータ付きbalanced条件と外側Eの全次数関係を
保持するDoubleFamilyを定義する。内側降下をcurryRightしたcochainの等式から外側へ降下し、
leftDesc・三重生成元の評価式・leftRestrictを構成した。
leftHomEquivは左反復coendからの射とDoubleFamilyの同値で、両逆法則まで証明済み。
内側総次数の異なる和表示を比較する補題は、添字と等式証拠を明示して輸送を扱う。
`Tensor/FubiniRightAction.lean`は右反復tensorの内側の右C作用について、
Rの次数kと作用の次数pによる符号(-1)^(p*k)を含む生成元公式を証明する。

Checks.FubiniFamilies・Checks.StageSeven・既存Spectra.StageTwoの同時ビルドは成功
（2683 jobs、終了コード0、警告なし）。任意A・独立対象宇宙、正負次数、ZMod 2を検査した。
主要21宣言の直接公理監査は終了コード0、標準公理のみ。監査累計1611宣言。
担当Leanのsorry/admit/新規axiomは0件。文書検査は22 Markdown・311 exposition参照、失敗0件。

U11e全受入は未完。次は同じDoubleFamilyを右反復coendへ降ろし、両降下と三重生成元の外延性から
Fubini同型を構成する。その後、bimoduleの全Hom自然性・結合同型・三角/五角を検証する。
U12〜U17・D4mも未完のまま継続。共有一般論への新しい不足要求はなく、担当外ファイルを変更していない。


### 17.45 U11e14：二重balanced族のE方向の降下（2026-10-16）

`Tensor/FubiniColumns.lean`はDoubleFamilyのC対象cを固定し、通常associatorの順方向で
(R(e)⊗Q(c,e))⊗N(c)からのcolumnMapsを構成する。N(c)を終域へ転置したcolumnCurryが
E-balancedであることを、外側Eの全次数関係から証明した。
columnFamilyは右パラメータ付きのbalanced族であり、columnDescは
(R⊗_E Q(c,−))⊗N(c)からの実際の射である。包含との可換式と三重生成元の評価式も証明した。
右作用の出力次数と内側総次数を明示したDoubleFamily.balanceE_of_sumsを使い、
r+pとp+rの表示の違いを型変換へ暗黙に押し込めない。

`Tensor/DegreeElementsExt.lean`のdegree_element_extは、coendの固定次数から任意のA加群への
線形射を純粋生成元で判定する。微分との可換性や出力次数を仮定しない。
`Tensor/ParameterBalancedElements.lean`は左パラメータを固定したbalanced関係の斉次成分式を証明する。
右作用の符号(-1)^(r*p)を保持し、外部パラメータの次数から余分な符号を導入しない。
これらは降下後のC-balanced関係の証明に使う。

Checks.FubiniColumns・Checks.FubiniFamilies・Checks.StageSeven・既存Spectra.StageTwoの
同時ビルドは成功（2688 jobs、終了コード0、警告なし）。任意A・独立対象宇宙・正負次数・ZMod 2を検査した。
主要9宣言の直接公理監査は終了コード0、標準公理のみ。監査累計1620宣言。
担当Leanのsorry/admit/新規axiomは0件。文書検査は22 Markdown・311 exposition参照、失敗0件。

これはE方向の内側降下であり、右反復coendからの降下全体の受入ではない。
次はcolumnDescが残るCのbalanced関係を保持することを、固定次数の外延性と
右C作用の符号(-1)^(p*k)、左パラメータ付きbalanced公式から証明する。
その後rightDescと三重包含での評価を構成し、Fubini同型・全Hom自然性・三角/五角へ進む。
U11全受入・U12〜U17・D4mは未完のまま継続する。共有系列への新しい不足要求はない。


### 17.46 U11e15：二重balanced族の右反復coendへの降下（2026-10-16）

`Tensor/FubiniRightFamilies.lean`はE方向のcolumnDescが残るCのbalanced関係を保つことを証明する。
固定次数の線形射にdegree_element_extを適用してEの純粋生成元へ帰着し、
右C作用の符号(-1)^(p*k)と外側のbalanced符号(-1)^((k+r)*p)の積が
元のQのbalanced符号(-1)^(r*p)になることを計算する。
DoubleFamily.balanceC_of_sumsは左右の内側総次数を別々に明示して、この比較に使う。
rightFamily・rightDescは実際の右反復coendからの降下を与え、
rightι_rightDescで共通の三重包含との合成が元の族へ戻ることを証明した。

Checks.FubiniRightFamilies・Checks.FubiniColumns・Checks.StageSeven・既存Spectra.StageTwoの
同時ビルドは成功（2689 jobs、終了コード0、警告なし）。任意A・独立対象宇宙・ZMod 2で降下を検査した。
主要5宣言の直接公理監査は終了コード0、標準公理のみ。監査累計1625宣言。
担当Leanのsorry/admit/新規axiomは0件。文書検査は22 Markdown・311 exposition参照、失敗0件。

左右への降下は揃ったが、Fubini同型はまだ未受入。
次は右反復coendからの射の三重族がC/Eの両方向でbalancedであることを示し、rightRestrictと
右側の普遍的同値を構成する。恒等射を双方の族へ制限し、両降下と外延性からFubini同型を得る。
その後bimodule結合同型の全Hom自然性と三角/五角、U12〜U17を継続する。
共有系列への新しい不足要求はなく、D4mの一般論を重複実装していない。


### 17.47 U11e16：Fubini同型と実際のbimodule合成の値への接続（2026-10-16）

`Tensor/ParameterBalancedConstructor.lean`は固定次数の三重tensorからの線形射の外延性と
paramFamilyMkを証明する。パラメータ付きの純粋斉次元の関係から、全chain map族のbalanced性を復元する。
`Tensor/FubiniRightRestriction.lean`は右反復coendへの包含の斉次評価、C/Eのbalanced関係を証明し、
rightRestrict・rightHomEquivと両逆法則を構成した。Cの関係では右作用の二つの符号の積を計算し、
Eの関係では内側coendのbalanced等式を外側の線形評価へ移す。

`Tensor/Fubini.lean`のisoはR⊗_E(Q⊗_C N)≅(R⊗_E Q)⊗_C Nを与える。
左右の恒等射をDoubleFamilyへ制限して他方へ降下し、三重生成元の外延性から両逆を証明する。
leftι_iso_hom・rightι_iso_invは生成元の順序R,Q,Nを保つことを示す。
両向きの同型とleftDesc/rightDescとの比較も公開した。任意可換環・非有界複体のままで、flatnessを仮定しない。

`Tensor/AssociatorValues.lean`はcompose_leftAt_eqにより既存composeの左加群構造と既存の左作用関手を
全Hom写像まで照合し、associatorValueIsoを実際の三つのbimodule合成の値の間に構成する。
B/C/E/Fの対象宇宙は係数環のuと独立、Small.{u}はB/C/Eにだけ要求し、右端Fには要求しない。
これは値ごとの同型であり、まだ右B/左Fの全Hom自然性を備えたbimodule同型とは主張しない。

Checks.Fubini・Checks.FubiniRightFamilies・Checks.StageSeven・既存Spectra.StageTwoの同時ビルドは成功
（2693 jobs、終了コード0、警告なし）。任意A・独立対象宇宙、正負次数の包含評価、ZMod 2、
Small Fなしの実際の合成の値の比較を検査した。主要18宣言の直接公理監査は終了コード0、標準公理のみ。
監査累計1643宣言。担当Leanのsorry/admit/新規axiomは0件。
文書検査は22 Markdown・311 exposition参照、失敗0件。担当差分の空白検査も成功。

Fubiniの対象同型と値への接続は完了。U11e全受入は引き続き未完である。
次は実際の三重包含とassociatorValueIsoの可換式を公開し、右B・左Fの全Hom自然性から
bimoduleの結合同型へ束ねる。三角/五角を反復balanced tensorの生成元で検証してU11を受け入れる。
U12のK-flat・導来tensor、U13〜U17、D4mも継続対象であり、受入済みとはしない。
共有一般論への新しい不足要求はなく、共有ルート・担当外の並行変更は編集していない。


### 17.48 U11e17：実際の結合比較の三重包含と全cochainの外延性（2026-10-16）

`Tensor/AssociatorGenerators.lean`は実際の左右の反復bimodule合成への三重包含を定義し、
associatorLeftι_hom・associatorRightι_invで結合比較の両方向との可換式を証明する。
左加群構造の等式輸送には既存ChangeLeftのι_changeLeft_homを再利用した。
changeLeftとeqToIso.homを明示的に正規化することで、局所maxHeartbeatsの追加なしで検証できた。
両括弧付けからの射が三重包含で決まる外延性も公開する。

`Tensor/AssociatorCochainExt.lean`は左括弧の実際の合成からの任意次数cochainを三重生成元で判定する。
外側のcochain_element_extと内側固定次数のdegree_element_extを組み合わせ、微分との可換性を要求しない。
これは閉零射だけでなく、主Hom全体の自然性を証明するための入口である。
`Tensor/BimoduleElements.lean`のcompose_leftAction_elementは、実際の合成の左作用が先頭因子へ作用する
全次数公式を証明する。入力・作用後・総次数を別々に指定でき、余分なKoszul符号はない。

Checks.AssociatorGenerators・Checks.Fubini・Checks.StageSeven・既存Spectra.StageTwoの同時ビルドは成功
（2697 jobs、終了コード0、警告なし）。任意A・独立対象宇宙・Small Fなしの包含比較、
作用次数−1と入力次数2/0、ZMod 2を検査した。主要9宣言の直接公理監査は終了コード0、標準公理のみ。
監査累計1652宣言。担当Leanのsorry/admit/新規axiomは0件。

U11全受入は引き続き未完。次は斉次三重生成元の結合比較による像を計算し、
二つの括弧付けでの左F作用の公式と今回の全cochain外延性から主Hom自然性を証明する。
右Bの全Hom自然性、実際のbimodule同型、三角/五角、U12〜U17・D4mも継続対象。
共有一般論への新しい不足要求はなく、共有ルート・担当外の並行変更は編集していない。


### 17.49 U11e18：実際の合成bimoduleの右作用の生成元公式（2026-10-16）

`Tensor/BimoduleRightElements.lean`のcompose_rightAction_elementは、右Bの次数pの作用を
相対tensorの先頭Q因子（次数k）から後ろのP因子へ移す際の符号(-1)^(p*k)を証明する。
実際のcomposeの右作用を用い、P.transposeHom_πと既存leftHomMap_element_of_sumを再利用する。
作用後のPの次数jと総次数nを明示し、任意の可換環・非有界複体を保つ。
これは後続の結合比較の右B全Hom自然性に使う。

Checks.BimoduleRightElements・Checks.AssociatorGenerators・Checks.StageSeven・既存Spectra.StageTwoの
同時ビルドは成功（2698 jobs、終了コード0、警告なし）。独立対象宇宙、作用次数−1とQ/Pの次数1/0、
ZMod 2の例を検査した。主要1宣言の直接公理監査は終了コード0、標準公理のみ。監査累計1653宣言。
担当Leanのsorry/admit/新規axiomは0件。文書検査は22 Markdown・311 exposition参照、失敗0件。

U11e全受入は未完。斉次三重生成元の像と左Fの主Hom自然性は草稿のビルド検証中であり、
今回の受入範囲には含めない。次は結合比較の等式輸送の成分評価を正規化してこれを完成させ、
右Bの全Hom自然性・bimodule同型・三角/五角へ進む。U12〜U17・D4mも未完のまま継続する。
共有系列への新しい不足要求はなく、担当外ファイル・共有ルートは変更していない。


### 17.50 U11e19：結合比較の斉次成分と両括弧付けの左作用（2026-10-16）

`Complexes/MapEvaluation.lean`は複体の合成等式を斉次元へ評価するchain_comp_apply_of_eq、
各次数の元から射の等式を構成するchain_ext_apply、および合成の評価式を公開する。
抽象的な複体の段階で評価を行うことで、実際の反復coendや等式輸送を全展開しない。

`Tensor/AssociatorElements.lean`は実際の左右の合成の斉次三重生成元と三重包含による表示を定義し、
associatorValueIso_hom_elementで結合比較がR,Q,Pの順の生成元を符号なしで送ることを証明した。
内側の総次数i/lを別々に指定でき、任意の非有界複体を保持する。
`Tensor/AssociatorLeftAction.lean`は両括弧付けの左F作用が先頭R因子へ作用する公式を証明する。
右括弧ではcompose_leftAction_elementを二回適用し、作用後のRの次数jと内側総次数l'を明示する。
これらの証明に局所maxHeartbeats指定は残していない。

Checks.AssociatorElements・Checks.AssociatorGenerators・Checks.StageSeven・既存Spectra.StageTwoの
同時ビルドは成功（2700 jobs、終了コード0、警告なし）。任意A・独立対象宇宙・Small Fなしの構成、
R/Q/Pの次数−1/2/−1、ZMod 2で結合比較の生成元公式を検査した。
主要10宣言の直接公理監査は終了コード0、標準公理のみ。監査累計1663宣言。
担当Leanのsorry/admit/新規axiomは0件。文書検査は22 Markdown・311 exposition参照、失敗0件。
担当差分の空白検査も成功。

U11e全受入は未完。次は今回の生成元の式を全cochain外延性で束ね、左Fの主Hom自然性を検証する。
その草稿AssociatorLeftNaturality/Checks.AssociatorLeftActionはまだ未受入・未コミットである。
右Bの主Hom自然性、bimodule同型、三角/五角、U12〜U17・D4mも継続対象。
共有系列への新しい不足要求はなく、担当外ファイル・共有ルートを編集していない。

### 17.51 U11e20：両括弧付けの右作用のKoszul符号（2026-10-16）

`Tensor/AssociatorRightAction.lean`は実際の三重合成の右B作用を両括弧で計算する。
左括弧では二回の作用による符号を合成し、右括弧ではR/Q因子の総次数を用いる。
両者は同じ符号 `(-1)^(p*(k+r))` を持ち、P因子だけに右作用が入る。
結合比較の等式輸送を定義境界に保つためassociatorValueIsoをirreducibleとし、
その三重包含公式では定義を明示的にunfoldする。対象や同型の定義内容は保持した。

Checks.AssociatorRightActionを含む関連入口・Checks.StageSeven・既存Spectra.StageTwoの
同時ビルドは成功（2704 jobs、終了コード0、警告なし）。任意A・独立対象宇宙・Small Fなし、
負次数の右作用とZMod 2の例を検査した。新規2宣言と変更した既存2宣言の直接公理監査は
標準公理のみ。監査累計1665宣言（既存2宣言の再監査は加算しない）。
文書検査は22 Markdown・311 exposition参照、失敗0件。担当差分の空白検査も成功。
今回の2ファイルにsorry/admit/新規axiomはない。

全Hom自然性の草稿は検証中であり、今回の受入には含めない。次は左右の全Hom自然性を
確定し、結合比較を実際のbimodule同型へ束ね、三角・五角と全変数自然性を証明する。
U11全受入・U12〜U17・D4mは未完。共有系列への追加要求はない。

### 17.52 U11e21：全Hom自然性のための抽象評価補題（2026-10-16）

`Complexes/HomMapEvaluation.lean`は閉零射と任意次数cochainの前後合成の評価式、
四つの元の可換squareからの等式、斉次cochainの等式から主Hom自然性を作る補題を公開する。
`Complexes/UnitScalarEvaluation.lean`はchain mapと整数単元の作用の可換式、
`Bimodule/ActionEvaluation.lean`はleftCochainの評価とleftActionの一致を公開する。
これらは反復coendを展開せず、抽象的な複体・bimoduleの段階で評価するためのAPIである。

Checks.ActionEvaluationの対象ビルドは成功（1788 jobs、終了コード0）。正負次数の合成、
ZMod 2での単元作用を検査した。主要6宣言の直接実行も終了コード0。
element_squareは公理なし、残る5宣言は標準公理のみ。監査累計1671宣言。
担当差分の空白検査は成功し、今回の4ファイルにsorry/admit/新規axiomはない。
結合比較の左右自然性と右加群同型の草稿は引き続き検証中であり、この受入に含めない。
U11全受入・U12〜U17・D4mは未完。共有一般論の重複実装・担当外ファイルの編集はない。

### 17.53 U12a1：K-flat性の区別・retract閉性・representable（2026-10-16）

U11eの自然性検査と独立に、受入済みYoneda評価を使うU12の入口を進めた。
`Tensor/KFlat.lean`は任意の非有界acyclic複体とのtensorを試験するcomplexKFlatと、
objectwise acyclic左dg加群とのbalanced tensorを試験するmoduleRelativeKFlatを区別する。
左加群のacyclic性、複体のacyclic性のretract保存、両K-flat条件の同型/retract保存を公開した。
representable_relativeKFlatはYoneda評価同型から証明し、dg圏のHomのA-flat性は要求しない。

Checks.KFlat・Checks.StageSeven・既存Spectra.StageTwoの同時ビルドは成功
（2657 jobs、終了コード0）。任意A・独立対象宇宙、representableのretractとZMod 2を検査。
新規9宣言の直接公理監査も終了コード0、標準公理のみ。監査累計1680宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。担当差分の空白検査も成功。
今回の2ファイルにsorry/admit/新規axiomはない。

U12a全受入にはshift/cone/余積閉性とquasiIso保存との同値がなお必要であり、
semifree・上有界flat・導来tensor・導来bimodule合成・係数変更も未完。
U11eの左右自然性・三角/五角、U13〜U17、D4mも未完。共有系列への追加要求はない。

### 17.54 U12a2：A上K-flatの閉性と準同型保存の同値（2026-10-16）

`Tensor/KFlatComplex.lean`はK-flat複体の単位・任意整数shift・cone・tensor閉性を証明した。
既存cochainTensorShiftLeft/cochainTensorConeLeftとacyclic複体の対応する閉性を再利用する。
complexKFlat_of_flat_boundsは既存bounded-flat定理を、相手が非有界でもよいK-flat条件へ接続する。
これは上有界flatの場合のU12c全受入を意味しない。
complexKFlat_quasiIso_left/rightは両方のtensor配置で準同型を保ち、
complexKFlat_iff_preserves_quasiIsoは任意準同型の保存とacyclic消滅条件の同値を証明する。
逆方向ではacyclic Lから零複体への準同型を使い、tensorが零対象を保つことを明示する。

Checks.KFlatComplex・Checks.KFlat・Checks.StageSeven・既存Spectra.StageTwoの
同時ビルドは成功（2771 jobs、終了コード0、警告なし）。任意A、整数shift−1/+1、
非有界cone/tensor、ZMod 2を検査した。主要8宣言の直接公理監査は終了コード0、標準公理のみ。
監査累計1688宣言。担当差分の空白検査は成功。今回の2ファイルにsorry/admit/新規axiomはない。

相対K-flatのshift/cone/余積閉性と準同型保存の同値はなお未完。
U11e右B成分整合性の草稿は既定カーネル予算でdeterministic timeoutとなったため、
該当補題に限りmaxHeartbeats 800000で再検査中。左右の自然性・bimodule同型の草稿は
受入済み宣言に含めない。三角/五角・U12の残部・U13〜U17・D4mも未完。
共有系列への追加要求はなく、既存PerfectComplex・共有ルート・担当外ファイルを編集していない。

### 17.55 U12a3：exactな余極限と相対K-flatの余積・逐次余極限閉性（2026-10-16）

`Complexes/ExactColimits.lean`はℤ次数の非有界複体図式を関手圏上の複体へ転置する。
objectwise acyclicなら転置複体もacyclicであり、ModuleCatのexactな余極限がacyclic性を保つことを
既存mapHomologyIsoとMathlibの実際の余極限coconeの普遍性から証明した。
図式の対象/射宇宙w/w'はAの宇宙uと独立で、対象族にSmall.{u} Jを明示する。

`Tensor/KFlatColimits.lean`はこの形の余極限に対するA上K-flat性と相対K-flat性の閉性を証明した。
後者は既存rightTensorFunctorの余極限保存を使う。u-small余積とℕ逐次余極限も公開する。
ℕの射/対象宇宙は0なので、ModuleCatのAB5を既存AB5OfSize_of_univLEで明示的に縮小した。

Checks.KFlatColimits・Checks.KFlatComplex・Checks.StageSeven・既存Spectra.StageTwoの
同時ビルドは成功（2805 jobs、終了コード0、警告なし）。独立した図式宇宙、有限代表加群族、
ℕ逐次図式とZMod 2を検査した。主要7宣言の直接公理監査は終了コード0、標準公理のみ。
監査累計1695宣言。文書検査は22 Markdown・311 exposition参照、失敗0件。
今回の3ファイルにsorry/admit/新規axiomはない。担当差分の空白検査も成功。

相対版のshift/cone閉性とquasiIso保存との同値、semifree・上有界flat・導来tensorはなお未完。
U11eの左右自然性のカーネル検査は継続中で、結合coherenceを受け入れたとはしない。
U13〜U17・D4mも未完。共有系列への追加要求はなく、担当外ファイルを編集していない。

### 17.56 U12b1：自由tensor評価とsphere-free段階の相対K-flat性（2026-10-16）

`Tensor/FreeEvaluation.lean`は右Hom加群をxで評価する関手とhomFunctor(N(x))の自然同型を構成する。
free/evaluation随伴とbalanced tensor/Hom随伴を合成し、既存tensorRight/Hom随伴との
左随伴の一意性からfreeTensorFunctorIsoを得る。freeTensorIsoは任意の非有界生成複体Kについて
free_x(K)⊗_D N≅K⊗_A N(x)を与え、Kの射についての自然性も公開する。
freeAt_relativeKFlatはKのA上K-flat性だけを要求し、Hom_Dのflat性は要求しない。

`Tensor/SphereFreeKFlat.lean`は既存complexSphereShiftIsoと単位のK-flat性から全整数次数の
sphereのK-flat性を証明した。自由sphere、さらに実際のModuleSphereFreePresentationを持つ
加群の相対K-flat性を証明する。表示のIndexはType(max u v)のまま保持し、
Small.{u} Indexの証拠とDiscrete/equivShrinkによるexact余積の移送を明示する。

Checks.SphereFreeKFlat・Checks.KFlatColimits・Checks.StageSeven・既存Spectra.StageTwoの
同時ビルドは成功（2807 jobs、終了コード0、警告なし）。任意A・独立対象宇宙・任意K、
sphere次数−1/+1とZMod 2を検査した。主要8宣言の直接公理監査は終了コード0、標準公理のみ。
監査累計1703宣言。文書検査は22 Markdown・311 exposition参照、失敗0件。
担当差分の空白検査も成功。今回の3ファイルにsorry/admit/新規axiomはない。

semifree全体の相対K-flat性は未完。次は全作用と可換するgraded-split拡張をtensorへ運び、
各段階のacyclic性を帰納した上で§17.55の逐次余極限閉性へ接続する。
U11eの結合coherence、相対版の残る閉性・quasiIso保存、U12残部・U13〜U17・D4mも未完。
共有系列への追加要求はなく、担当外ファイルを編集していない。

### 17.57 U12b2：graded-split拡張のtensor後の分裂と短完全性（2026-10-16）

`Tensor/GradedSplitElements.lean`は既存ModuleGradedSplitのsection/retractionを主Hom endの
次数0要素としてbalanced tensorへ送り、生成元上の公式を証明する。chain map条件は課さない。
rightTensorMapは既存rightTensorFunctor.mapを元のbalanced tensor対象間の射として読む。
`Tensor/GradedSplitLaws.lean`は純粋生成元の外延性から包含–retraction・section–射影・
分解恒等式をcochainの等式として証明した。
`Tensor/GradedSplit.lean`はそれらを各次数のShortComplex.Splittingへ束ね、
tensorShortComplexの短完全性、両端のacyclic性から中央のacyclic性、相対K-flat性の拡張閉性を得る。
任意左加群を使え、その対象やHomにflat性を仮定しない。

Checks.TensorGradedSplit・Checks.SphereFreeKFlat・Checks.StageSeven・既存Spectra.StageTwoの
同時ビルドは成功（2818 jobs、終了コード0、警告なし）。任意A・独立対象宇宙、
任意非有界coneの次数−1の分裂、ZMod 2を検査した。
主要15宣言の直接公理監査は終了コード0、標準公理のみ。監査累計1718宣言。
今回の4ファイルにsorry/admit/新規axiomはない。担当差分の空白検査も成功。

次はこの拡張閉性を実際のsemifree filtrationの各段階へ適用し、逐次余極限と網羅性の同型を使う。
U11eの左右自然性と結合coherence、U12残部・U13〜U17・D4mも未完。
共有系列への追加要求はなく、担当外ファイルを編集していない。

### 17.58 U12b3：semifreeの相対K-flat性と解像度の存在（2026-10-16）

`Tensor/Semifree.lean`は既存ModuleSemifreeFiltrationの各段階の相対K-flat性を帰納する。
初期段と各商にはsphere-free表示の定理を使い、全作用と可換するgraded-split拡張の
tensor短完全性で次段へ進む。逐次余極限閉性とfiltrationの実際のIsColimit・網羅性同型を使い、
moduleSemifree_relativeKFlatを証明した。
exists_relativeKFlat_resolutionは既存exists_semifree_resolutionへこの結果を追加し、
semifree・相対K-flat・次数ごと全射・指定quasiIsoを同時に保持する。
Hom_DのA-flat性やモデル圏は仮定しない。

Checks.SemifreeKFlat・Checks.TensorGradedSplit・Checks.StageSeven・既存Spectra.StageTwoの
同時ビルドは成功（2819 jobs、終了コード0、警告なし）。任意A・独立対象宇宙・非有界加群、
任意filtrationとZMod 2の解像度を検査した。新規4宣言の直接公理監査も終了コード0、標準公理のみ。
監査累計1722宣言。§17.57/58の文書検査は22 Markdown・311 exposition参照、失敗0件。
担当差分の空白検査も成功。今回の2ファイルにsorry/admit/新規axiomはない。

U12bの相対結果は得られたが、local A-K-flat Homの仮定からのobjectwise結果はなお未完。
相対K-flatのshift/cone閉性・quasiIso保存との同値、U12cの上有界flat、導来tensorと
導来bimodule合成・係数変更も未完。U11e・U13〜U17・D4mも未完のまま継続する。
共有系列への追加要求はなく、担当外ファイルを編集していない。

### 17.59 U12b4：local Hom仮定付きobjectwise K-flat性（U12b受入、2026-10-16）

`Tensor/ObjectwiseKFlat.lean`はlocalHomKFlatとmoduleObjectwiseKFlatを別々に定義し、
相対K-flat性と同一視しない。前者は対象のsmallnessなしでも定義できる。
次数ごと分裂するA複体の拡張についてK-flat性を証明し、評価後のgraded-split拡張へ適用する。
freeAt_objectwiseKFlatは生成複体のK-flat性と各HomのA上K-flat性を明示する。
評価の余極限保存、sphere-free表示、各filtration段階の帰納、exactな逐次余極限から
moduleSemifree_objectwiseKFlatを得る。exists_objectwiseKFlat_resolutionはsemifree・相対K-flat・
objectwise K-flat・次数ごと全射・指定quasiIsoを同時に保持する。

Checks.ObjectwiseKFlat・Checks.SemifreeKFlat・Checks.StageSeven・既存Spectra.StageTwoの
同時ビルドは成功（2820 jobs、終了コード0、警告なし）。独立対象宇宙、負次数sphere、
一対象環AのlocalHom条件、ZMod 2の追加flat仮定なしの解像度を検査した。
主要10宣言の直接公理監査は終了コード0、標準公理のみ。監査累計1732宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。担当差分の空白検査も成功。
今回の2ファイルにsorry/admit/新規axiomはない。

U12bの受入照合：representable (§17.53)、任意Kの自由tensor評価・sphere-free段階 (§17.56)、
全作用graded-split拡張 (§17.57)、実際の網羅的逐次余極限とsemifree解像度 (§17.58)、
local Homの仮定を付けたobjectwise結果 (本節) が揃った。相対結果にはlocalHomKFlatを加えていない。
これでU12bを受け入れるが、U12全体は未完。U12aの残り・U12cの上有界flat・U12d〜f、
U11eのcoherence・U13〜U17・D4mも継続する。共有系列への追加要求はない。

### 17.60 U12d1：tensorのホモトピー保存と射影的解像度比較（2026-10-16）

`Tensor/Homotopy.lean`は主rightHomMapの閉零要素が既存rightTensorMapのofHomに一致すること、
rightTensorDGの閉零制限が既存通常関手の射に一致することを生成元で証明した。
全dg自然なModuleHomotopyはtensorで既存chain homotopyになり、
rightTensorHomotopyFunctorは主K(D)から既存K(A)への関手と商関手との可換等式を公開する。

`Tensor/ProjectiveComparison.lean`は既存K(D)での準同型の逆を持ち上げ、
homotopically projective対象間の準同型のtensor像を実際のHomotopyEquivにする。
そのhomは元のrightTensorFunctor.map fである。任意の左加群を固定でき、flat条件は不要。
semifree対象間の準同型にも適用する。
`Tensor/ProjectiveKFlat.lean`はsemifree解像度とのこの比較から
moduleHomotopicallyProjective_relativeKFlatを証明し、射影性と相対K-flat性を別定義のまま接続した。

Checks.TensorHomotopy・Checks.ObjectwiseKFlat・Checks.StageSeven・既存Spectra.StageTwoの
同時ビルドは成功（2838 jobs、終了コード0、警告なし）。任意A・独立対象宇宙、
全dg自然なホモトピー、semifree解像度間の準同型、比較homの実際の射との一致、ZMod 2を検査。
主要9宣言の直接公理監査は終了コード0、標準公理のみ。監査累計1741宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。担当差分の空白検査も成功。
今回の4ファイルにsorry/admit/新規axiomはない。§17.57〜59の節順も番号順に整理した。

U12dの導来双関手・左変数の準同型保存・任意解像度計算・選択の自己/推移整合性はなお未完。
U12aの相対版の残り、U12c/e/f、U11eのcoherence・U13〜U17・D4mも継続する。
共有系列への追加要求はなく、担当外ファイルを編集していない。

### 17.61 U12d2：主導来圏からの解像度関手と選択整合性（2026-10-16）

`Derived/ResolutionFunctor.lean`は任意の証明付き射影解像度族Rを、主K(D)に値を持つ
moduleResolutionHomotopyFunctorへ関手化した。射は既存liftで与え、K(D)でのlift_id/compを使う。
指定objectwise quasiIsoを反転することを既存射影的対象間の比較で証明し、
同じ主局所化D(D)からのmoduleDerivedResolutionFunctor、Mathlib Lifting、計算自然同型を得る。
モデル構造を使わず、局所化や対象宇宙を別の型へ変更しない。

`Derived/ResolutionFunctorChoice.lean`は任意の二つの解像度族の比較を、K(D)とD(D)からの
両関手間の自然同型へ束ねた。比較射による成分、自己比較＝恒等、三つの選択の推移整合性を
それぞれ証明した。局所化上の自然同型は既存Localization.liftNatIsoを使用する。
後続の導来tensorでは、この関手とK(D)からの既存tensorを合成できる。

Checks.ResolutionFunctor・Checks.TensorHomotopy・Checks.StageSeven・既存Spectra.StageTwoの
同時ビルドは成功（2839 jobs、終了コード0、警告なし）。任意A・独立対象宇宙、
任意解像度族の計算と推移整合性、ZMod 2を検査。主要14宣言の直接公理監査は終了コード0、
標準公理のみ。監査累計1755宣言。文書検査は22 Markdown・311 exposition参照、失敗0件。
担当差分の空白検査も成功。今回の3ファイルにsorry/admit/新規axiomはない。

U12d全受入は未完。固定左加群との導来tensorの組立て、左変数の指定quasiIso保存と
両変数の導来双関手、任意解像度での計算比較を続ける。U11eのcoherence・U12残部・U13〜U17・D4mも未完。
共有系列への追加要求はなく、担当外ファイルを編集していない。

### 17.62 U12d3：固定左加群との導来tensorと任意解像度計算（2026-10-16）

`Derived/RightTensor.lean`は指定D(D)からK(D)への解像度関手と、固定左加群Lとのtensor、
既存K(A)→D(A)を合成し、moduleResolutionDerivedTensorと標準族によるmoduleDerivedTensorRightを構成した。
対象D(A)には独立した宇宙wとHasDerivedCategory.{w}(ModuleCat.{u} A)を明示する。
主局所化前のMで、R(M)⊗_D Lを使う計算同型を公開し、任意の二つの解像度族の変更を
自然同型に運ぶ。自己比較と三つの族の推移整合性も証明した。

`Derived/RightTensorResolution.lean`は任意の個別のModuleProjectiveResolution P,Qについて、
比較射のtensor像をD(A)で同型化し、そのhomの公式・自己/推移整合性を証明する。
moduleDerivedTensorRightResolutionComputationは標準族で定義した導来tensorを任意Pで計算する。
これらは固定Lにflat条件を要求しない。K(D)で等しい射のtensor像がD(A)で等しいことを
§17.60の全dg自然なホモトピー保存から使っている。

Checks.DerivedRightTensor・Checks.ResolutionFunctor・Checks.StageSeven・既存Spectra.StageTwoの
同時ビルドは成功（2688 jobs、終了コード0、警告なし）。任意A・独立対象宇宙・明示したD(A)宇宙、
任意の個別解像度と族、自己/推移整合性、ZMod 2を検査した。
主要13宣言の直接公理監査は終了コード0、標準公理のみ。監査累計1768宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。担当差分の空白検査も成功。
今回の3ファイルにsorry/admit/新規axiomはない。

これは固定左加群での構成であり、U12d全受入は未完。左加群の射に関する自然性と
指定quasiIso保存を示し、左側の主導来圏へも降ろす両変数関手を次に構成する。
U12aの残り・U12c/e/f、U11eの結合coherence・U13〜U17・D4mも継続する。
共有系列への追加要求はなく、担当外ファイルを編集していない。

### 17.63 U12d4：左加群の通常射に関する導来tensorの関手性（2026-10-16）

`Tensor/LeftNaturality.lean`は左加群の閉零射gから固定左加群との通常tensor関手間の
rightTensorLeftMapを構成した。両変数mapの既存合成則を使い、右変数の自然性とgの恒等/合成を証明する。
Mathlib Quotient.natTransLiftでこれを主K(D)上のrightTensorHomotopyLeftMapへ送り、
元の対象での成分・恒等/合成を検証した。rightTensorHomotopyBifunctorは左加群の閉零圏から
K(D)→K(A)関手の圏への実際の関手である。

`Derived/RightTensorLeftFunctor.lean`は解像度関手による前合成と既存K(A)→D(A)による後合成を使い、
moduleResolutionDerivedTensorLeftFunctorを構成する。その対象は既存の固定Lの導来tensorと一致し、
射の成分はQhで送ったrightTensorHomotopyLeftMapである。標準族を用いるmoduleDerivedTensorLeftFunctorも公開した。
左変数の通常射と、主D(D)の任意射の間の自然性を保持する。

Checks.DerivedTensorLeftNaturality・Checks.DerivedRightTensor・Checks.StageSeven・既存Spectra.StageTwoの
同時ビルドは成功（2690 jobs、終了コード0、警告なし）。任意A・独立対象宇宙・明示したD(A)宇宙、
K(D)の対象上の成分、主導来圏の任意射との可換square、ZMod 2を検査。
主要13宣言の直接公理監査は終了コード0、標準公理のみ。監査累計1781宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。担当差分の空白検査も成功。
今回の3ファイルにsorry/admit/新規axiomはない。

左変数の指定quasiIsoを反転する証明はなお未完であり、左側も導来化した双関手とはしない。
次は主dg関手による標準cone比較を構成して、相対K-flat条件と準同型保存の接続へ進む。
U11e・U12の残部・U13〜U17・D4mも未完。共有系列への追加要求はない。

### 17.64 U12a4：複体値dg関手と標準coneの比較射（2026-10-16）

`Functor/ClosedComplex.lean`は複体値dg関手の閉零制限をtoComplexFunctorとして読み、
主Homの閉零要素の像と通常chain mapのofHomとの一致、微分との可換式、通常順のcochain合成保存を公開する。
最後の公式では豊穣順から通常順への二つのKoszul符号が相殺する。
これにより、特定のtensorの実装を展開せずにdg関手の全次数情報を使える。

`Functor/ModuleCone.lean`は既存moduleConeInlElementの次数−1の像と微分を計算し、
既存mappingCone.descでmoduleConeImageComparisonを構成した。
これはcone(F(f))からF(cone(f))への実際のchain mapであり、次数0/−1の両包含の公式を証明した。
ここでは比較射の可逆性までは主張しない。

Checks.FunctorModuleCone・Checks.DerivedTensorLeftNaturality・Checks.StageSeven・既存Spectra.StageTwoの
同時ビルドは成功（2691 jobs、終了コード0、警告なし）。任意A・独立対象宇宙・任意複体値dg関手、
合成次数−1/+1、既存moduleEvaluationDGでの包含との一致、ZMod 2を検査。
主要9宣言の直接公理監査は終了コード0、標準公理のみ。監査累計1790宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。担当差分の空白検査も成功。
今回の3ファイルにsorry/admit/新規axiomはない。

次はconeの射影/包含の行列恒等式を主Homへ持ち上げ、dg関手による像でも比較射が可逆であることを証明する。
それを右/左tensorへ適用して相対K-flatのcone/shift閉性・指定quasiIso保存へ接続する。
U11e・U12残部・U13〜U17・D4mは未完。共有系列への追加要求はない。

### 17.65 U12a5：coneの主Hom行列恒等式とdg関手による保存（2026-10-16）

`Module/ConeElementRelations.lean`は閉零の第二包含を主Hom要素として読み、
次数−1/+1の第一包含/第一射影、次数0の第二包含/第二射影の四つの合成と
二つの射影–包含の和による恒等写像の分解を主Hom end内で証明した。
通常順composeを使い、対象ごとの独立な等式だけで代用しない。

`Functor/ModuleConeRelations.lean`は第一/第二射影のdg関手による像をcochainとして公開し、
上記五恒等式を任意の複体値dg関手へ運んだ。通常順の合成保存、閉零射/単位の既存公式を再利用する。
この一般化の仮定にtensorやflat性はなく、次のcone比較射の次数ごとの逆を構成する入力になる。

Checks.ConeElementRelations・Checks.FunctorModuleCone・Checks.StageSeven・既存Spectra.StageTwoの
同時ビルドは成功（2659 jobs、終了コード0、警告なし）。任意A・独立対象宇宙・任意複体値dg関手、
次数−1/+1の合成・分解とZMod 2を検査。主要14宣言の直接公理監査は終了コード0、標準公理のみ。
監査累計1804宣言。文書検査は22 Markdown・311 exposition参照、失敗0件。
担当差分の空白検査も成功。今回の3ファイルにsorry/admit/新規axiomはない。

cone比較の可逆性・相対K-flatと指定quasiIso保存の接続はなお未完。
U11e・U12残部・U13〜U17・D4mも継続する。共有系列への追加要求はない。

### 17.66 U12a6：cone比較の複体同型と相対K-flatのcone閉性（2026-10-16）

`Complexes/ConeRepresentation.lean`は任意複体の四つの包含/射影に五つの行列恒等式を仮定し、
既存mappingCone.descの各次数の逆をcomplexConeElementMkで明示した。
第一/第二射影との合成式、左右の逆恒等式、各次数の全単射を証明し、
MathlibのHom.isIso_of_componentsで比較射が同型となることを証明する。

`Functor/ModuleConeIso.lean`は§17.65のdg関手像の恒等式を渡し、
任意の複体値dg関手についてmoduleConeImageComparisonのIsIsoとmoduleConeImageIsoを公開する。
そのhomは§17.64で定義した比較射そのものである。
`Tensor/Cone.lean`は既存rightTensorDGの閉零比較を使って通常rightTensorFunctorへの同型に接続し、
moduleRelativeKFlat_coneを証明した。両端が相対K-flatなら任意の標準coneも相対K-flatである。

Checks.FunctorModuleConeIso・Checks.ConeElementRelations・Checks.StageSeven・既存Spectra.StageTwoの
同時ビルドは成功（2693 jobs、終了コード0、警告なし）。任意A・独立対象宇宙・任意dg関手、
評価関手・実際のbalanced tensor、相対K-flat cone、ZMod 2を検査した。
主要12宣言の直接公理監査は終了コード0、標準公理のみ。監査累計1816宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。担当差分の空白検査も成功。
今回の4ファイルにsorry/admit/新規axiomはない。

U12aの残るshift閉性と相対K-flat条件の指定quasiIso保存との同値、
左変数も導来化したtensor双関手、U12c/e/fはなお未完。
次はopposite上の既存左右加群同値とswapを使い、このcone比較を左変数の準同型保存へ適用する。
U11eのcoherence・U13〜U17・D4mも未完。共有系列への追加要求はない。


### 17.67 U12a7/d5：左加群の指定準同型と相対K-flat tensorの保存性（2026-10-16）

`Module/LeftQuasiIso.lean`は既存leftModuleToRightOppositeによるmoduleQuasiIsoの逆像として
leftModuleQuasiIsoを定義し、全対象での評価準同型との同値、乗法性・two-out-of-three・
retract閉性・同型整合性を公開する。対象宇宙は独立に保つ。

`Tensor/QuasiIsoLeft.lean`は既存左右同値のcounitと符号付きswapによって、相対K-flat右加群の
acyclic試験をopposite上へ運ぶ。そこで標準cone比較同型を適用し、左加群の指定準同型に対する
実際のleftTensorFunctorの準同型保存を証明した。自然同型の合成式の型を明示することで、
最終証明は既定heartbeat予算内で通過する。一般モデル圏・Quillenの入力は使わない。
`Tensor/ProjectiveLeftQuasiIso.lean`はhomotopically projectiveおよびsemifree右加群への系を公開する。

Checks.LeftTensorQuasiIso・Checks.FunctorModuleConeIso・Checks.StageSeven・既存Spectra.StageTwoの
同時ビルドは成功（2856 jobs、終了コード0、警告なし）。任意A・独立対象宇宙・ZMod 2を検査した。
主要10宣言の直接公理監査は終了コード0、標準公理のみ。監査累計1826宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。担当差分の空白検査も成功。
今回の4 Leanファイルにsorry/admit/新規axiomはない。

左変数の指定準同型保存は得られたが、指定局所化上の両変数導来tensor双関手の完成はなお必要。
次は射影解像度関手の計算同型を通じて、この保存性を既存moduleResolutionDerivedTensorLeftFunctorの
自然変換の可逆性へ運び、左変数の局所化へ延長する。
U12aのshift閉性・保存条件との逆向き、U12c/e/f、U11eのcoherence、U13〜U17・D4mも未完。
共有系列への追加要求はなく、担当外ファイルを編集していない。


### 17.68 U12d6：左右の指定局所化上の導来tensor双関手（2026-10-16）

`Derived/LeftBasic.lean`はleftModuleQuasiIsoによる実際の局所化DerivedLeftModuleCategory、
leftModuleToDerived、指定準同型の像の同型を公開する。射・対象の宇宙はMathlibの構成された
局所化に従い、小さいHom宇宙を追加主張しない。

`Derived/LeftTensorInversion.lean`は射影的右加群を固定した左準同型保存をD(A)の同型へ送り、
既存の解像度関手の計算同型と局所化関手の本質的全射性を用いて、
moduleResolutionDerivedTensorLeftFunctorが左の指定準同型を反転することを証明する。
`Derived/TensorBifunctor.lean`はこれをMathlibの局所化普遍性で延長し、
DerivedLeftModuleCategoryからDerivedModuleCategory上のD(A)値関手圏への双関手を構成した。
任意の右射影解像度族版、標準semifree解像度版、左の局所化前での厳密な因子化、
任意解像度族による具体的balanced tensorへの計算同型を公開する。

Checks.TensorBifunctor・Checks.LeftTensorQuasiIso・Checks.StageSeven・既存Spectra.StageTwoの
同時ビルドは成功（2864 jobs、終了コード0、警告なし）。任意可換環・独立対象宇宙・
独立したD(A)の射宇宙・ZMod 2を検査する。一般モデル圏・Quillen・転送を使わない。
主要13宣言の直接公理監査は終了コード0、標準公理のみ。監査累計1839宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。
今回の4 Leanファイルにsorry/admit/新規axiomはない。担当差分の空白検査も成功。

U12d全受入には解像度族比較の左変数を含めた自然性・自己/推移整合性と任意解像度計算の統合が残る。
次は既存moduleResolutionDerivedTensorIsoを左変数の射と可換にし、両変数局所化上へ延長する。
U12aの残部・U12c/e/f、U11eのcoherence、U13〜U17・D4mも未完。
共有系列への追加要求はなく、担当外ファイルを編集していない。


### 17.69 U12d7：両変数の解像度族比較と任意解像度計算の整合性（2026-10-16）

`Derived/TensorChoiceLeft.lean`は既存moduleResolutionDerivedTensorIsoの比較を、
左加群のすべての閉零射に関して自然なmoduleResolutionDerivedTensorLeftIsoへ束ねる。
証明は既存rightTensorHomotopyLeftMapの自然性を解像度関手の比較射へ適用する。
自己比較と三つの解像度族の推移法則も、既存の固定左加群版と一致する形で証明した。

`Derived/TensorBifunctorChoice.lean`はConstruction.liftの厳密な因子化をLiftingとして公開し、
Mathlib Localization.liftNatIsoで両変数の指定局所化上の比較自然同型を構成する。
局所化前の左加群における成分式、自己比較、推移法則を公開した。
左右の導来加群圏とD(A)の宇宙、準同型クラスは§17.68と同じである。

`Derived/TensorResolutionComparison.lean`は任意の個別の射影解像度Pによるtensor計算を
左加群変数の関手とし、P/Qの比較自然同型とその自己/推移法則を証明する。
両変数導来tensorから任意Pによる計算への同型、計算解像度をPからQへ変更した際の
比較との整合式も公開する。解像度族を選ぶことと、個別の任意解像度で計算することを分けて検証した。

Checks.TensorChoice・Checks.TensorBifunctor・Checks.StageSeven・既存Spectra.StageTwoの
同時ビルドは成功（2868 jobs、終了コード0、警告なし）。任意A・独立対象宇宙・独立D(A)射宇宙・
ZMod 2の比較を検査した。今回の4 Leanファイルにsorry/admit/新規axiomはない。
主要16宣言の直接公理監査は終了コード0、標準公理のみ。監査累計1855宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。
担当差分の空白検査も成功。

U12dの両変数自然性・解像度族選択独立性の自己/推移法則・任意解像度計算を実装した。
次の統合確認では局所化比較の成分式と実際の計算同型を結ぶ可換図式を検査してU12dを受け入れる。
U12aのshift閉性・保存条件の逆向き、U12c/e/f、U11eのcoherence、U13〜U17・D4mは未完。
共有系列への追加要求はなく、担当外ファイルを編集していない。


### 17.70 U12d8：比較と計算の可換図式（U12d受入、2026-10-16）

`Derived/TensorComputationNaturality.lean`は既存moduleTensorHomotopyComputationの
加群射に関する自然性と、QhおよびquotientCompQhIsoを通じたD(A)値計算同型の自然性を証明する。
解像度関手の比較成分を既存の因子化・K(D)の比較射へ展開し、
moduleResolutionDerivedTensorIsoが実際のmoduleProjectiveResolutionTensorIsoと
計算同型を通じて可換となることを証明した。

`Derived/TensorBifunctorComputationChoice.lean`は左変数の局所化前の比較成分と厳密な因子化の
整合式を公開し、それを既存の両変数導来tensorの計算同型へ接続する。
任意の同じ個別射影解像度Pで計算したとき、二つの解像度族R/Sによる計算が比較自然同型を通じて
一致することも証明した。新しい比較射を選び直さず、既存の比較射と計算同型そのものを使用する。

Checks.TensorComputation・Checks.TensorChoice・Checks.StageSeven・既存Spectra.StageTwoの
同時ビルドは成功（2870 jobs、終了コード0、警告なし）。任意A・独立対象宇宙・独立D(A)射宇宙・
任意の個別解像度・ZMod 2での射の自然性を検査した。
主要7宣言の直接公理監査は終了コード0、標準公理のみ。監査累計1862宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。
今回の3 Leanファイルにsorry/admit/新規axiomはない。担当差分の空白検査も成功。

U12dの受入照合：
- 右射影解像度間のtensorホモトピー同値とホモトピー保存：§17.60。
- 射影性から相対K-flat性、左準同型の保存：§17.60・67。
- 指定された左右の準同型局所化上の実際の双関手：§17.61〜63・68。
- 解像度族比較の両変数自然性・自己/推移整合性：§17.62・69。
- 任意解像度の計算と比較との可換図式：§17.62・69・本節。
これでU12dを受け入れる。導来bimodule合成・そのcoherence・係数変更はU12e/fであり未完。

次はU12aの相対K-flatのshift閉性と準同型保存条件の逆向きを完成させ、U12cの上有界flatを検証する。
U11eのcoherence・U12e/f・U13〜U17・D4mも未完。共有系列への追加要求はなく、担当外を編集していない。


### 17.71 U12a8：相対K-flat条件と左準同型保存の同値（2026-10-16）

`Module/LeftZero.lean`は既存leftRightOppositeEquivalenceの逆関手から左加群の具体的零対象を
構成し、完全忠実な比較関手による反映で零性を証明する。HasZeroObject、左評価の加法性、
各評価がこの零対象を零複体へ送ることを公開した。新しい左加群モデルは導入していない。

`Tensor/KFlatCriterion.lean`は§17.67の準同型保存の逆向きを証明する。
任意のobjectwise acyclic左加群から上記零対象への射は指定leftModuleQuasiIsoであり、
leftTensorFunctorの余極限保存による零対象保存と、既存の複体の準同型判定から
元のtensorのacyclic性を得る。これによりmoduleRelativeKFlat_iff_preserves_leftQuasiIsoを公開した。
零右加群の相対K-flat性も、既存rightTensorFunctorの零対象保存から証明した。

Checks.KFlatCriterion・Checks.TensorComputation・Checks.StageSeven・既存Spectra.StageTwoの
同時ビルドは成功（2872 jobs、終了コード0、警告なし）。任意A・独立対象宇宙・ZMod 2を検査する。
主要7宣言の直接公理監査は終了コード0、標準公理のみ。監査累計1869宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。
今回の3 Leanファイルにsorry/admit/新規axiomはない。担当差分の空白検査も成功。

U12aは相対K-flatの整数shift閉性がなお残るため全受入とはしない。
次は既存の全次数shift要素と複体値dg関手の主Hom写像を照合してtensorのshift比較を得る。
U12cの上有界flat、U11eのcoherence、U12e/f、U13〜U17・D4mも未完。
共有系列への追加要求はなく、担当外ファイルを編集していない。


### 17.72 U12c：上に有界なflat複体の非有界K-flat性（受入、2026-10-16）

`Complexes/LowerTruncationSequence.lean`は既存StupidTruncation.aboveと包含を再利用し、
下端b≤aについて二つの切り詰め間の包含を構成する。元の複体への包含との可換式、
恒等・合成則を証明し、下端0,−1,−2,…の可算図式と元の複体への余錐を公開した。
各次数qでは下端がq以下になった後の包含が同型となる。
Mathlib Functor.IsEventuallyConstantFrom.isColimitOfIsIsoとHomologicalComplex.isColimitOfEvalを
適用し、この余錐が実際に余極限であることとlowerTruncationColimitIsoを証明した。
一般的なeventually constant余極限論は新設していない。

`Tensor/BoundedAbove.lean`は任意可換環A上で、次数ごとflatかつ上に有界な複体Kについて
complexKFlat_of_flat_boundedAboveを証明する。下から切り詰めた各段階は両側有界flatであり、
既存complexKFlat_of_flat_boundsを使用する。ModuleCatのAB5と既存complexKFlat_colimitを
可算図式へ適用し、余極限同型でKへ運ぶ。tensorの余極限保存とexactな余極限による
acyclic性の保存は§17.55の証明済みAPIを使用した。
相手のacyclic複体には上界・下界を一切仮定しない。
左右どちらの因子としても任意の非有界準同型を保存する系を公開した。

Checks.BoundedAboveKFlat・Checks.KFlatCriterion・Checks.StageSeven・既存Spectra.StageTwoの
同時ビルドは成功（2853 jobs、終了コード0、警告なし）。任意A・任意上界b・非有界相手・
ZMod 2・実際の切り詰め余極限同型を検査した。
主要13宣言の直接公理監査は終了コード0、標準公理のみ。監査累計1882宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。
今回の3 Leanファイルにsorry/admit/新規axiomはない。担当差分の空白検査も成功。

これでU12cの「任意非有界acyclicを消す」という受入条件を満たす。
相手も上に有界な既存定理だけを使った結論ではない。
次はU12aの相対K-flat整数shift閉性を完成させる。
U11eのcoherence、U12e/f、U13〜U17・D4mは未完。共有系列への追加要求はなく、担当外を編集していない。


### 17.73 U12a9：複体値dg関手のshift比較と相対K-flat閉性（U12a受入、2026-10-16）

`Complexes/HomogeneousTransport.lean`は既存の始域次数輸送の逆向き補題を追加する。
`Module/ShiftUnitElements.lean`は既存moduleHomLeftShiftElementを単位へ適用して次数sの射影を作り、
右shiftした単位から次数−sの包含を作る。Mathlib leftShiftが持つ定数符号
(-1)^(s*s+s*(s-1)/2)を包含側で補正する。全次数自然性、射影の閉性、評価成分を証明した。
`Module/ShiftUnitRelations.lean`は両方の通常順合成が主Hom endの単位となることを証明する。

`Functor/ModuleShift.lean`は任意の複体値dg関手についてこの射影・包含の像を構成し、
微分と通常順合成の保存で閉性・両逆恒等式を運ぶ。
Mathlib Cocycle.equivHomShiftを用いて実際のchain map F(M[s])→F(M)[s]を作り、
各次数の逆を包含の像で明示して全単射・IsIso・moduleShiftImageIsoを公開した。
単なる各評価の同型からdg自然性を仮定せず、元の加群の全Hom要素を使用している。
一般のCommShiftインスタンスやshiftの加法coherenceまで今回のobject比較から主張するものではない。

`Tensor/Shift.lean`は実際のrightTensorDGへ適用し、balanced tensorの右加群整数shift比較、
moduleRelativeKFlat_shift、および既存HasShiftに対するmoduleRelativeKFlat_shiftObjを証明する。
任意整数s・任意可換環であり、Hom_DのA-flat性は仮定しない。

Checks.ShiftKFlat・Checks.KFlat・Checks.KFlatComplex・Checks.KFlatColimits・Checks.KFlatCriterion・
Checks.FunctorModuleConeIso・Checks.BoundedAboveKFlat・Checks.TensorComputation・Checks.StageSeven・
既存Spectra.StageTwoの同時ビルドは成功（2886 jobs、終了コード0、警告なし）。
任意A・独立対象宇宙・任意複体値dg関手・全整数shift、次数−1/0/+1の実例、ZMod 2を検査した。
主要22宣言の直接公理監査は終了コード0、標準公理のみ。監査累計1904宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。
今回の6 Leanファイルにsorry/admit/新規axiomはない。担当差分の空白検査も成功。

U12aの受入照合：A上/相対K-flatの区別と同型/retract不変性（§17.53）、
A上のshift/cone/tensor閉性と準同型保存の同値（§17.54）、相対の余積/逐次余極限閉性（§17.55）、
相対cone閉性（§17.66）、左準同型保存とその逆向き・零対象（§17.67・71）、
相対整数shift閉性（本節）。これでU12aを受け入れる。
U12a〜dが受入済みとなったが、U12全体は導来bimodule合成・coherence・係数変更（U12e/f）を残す。
U11eのcoherence、U13〜U17・D4mも未完。次はU11eの検査結果を確認し、導来bimodule合成へ進む。
共有系列への追加要求はなく、担当外ファイルを編集していない。

U11eの左右成分整合性の草稿検査はプロセスを確認し、両LeanプロセスともCPU使用を伴って継続中。
今回の受入・監査件数には含めず、検査の観測待ちだけを理由に再起動していない。


### 17.74 U13a1：指定生成元からの有限cell構成と有限support（2026-10-16）

U11eの左右成分整合性の草稿検査はそれぞれ同じ実行ハンドルを再確認して継続中。
独立に進められるU13aの構成データを先行した。U11eやU12e/fを受け入れたという意味ではない。

`Perfect/FiniteCell.lean`はModuleFiniteCellCode A D S MをType値の帰納的データとして定義する。
生成元集合S⊆D、具体的零加群、Sの代表加群、任意整数shift、既存moduleBiprod、既存moduleCone、
主加群圏の同型による輸送を構成子に持つ。対象の型・射・操作の木を保持し、
対象宇宙max (u+1) vを縮小しない。有限和は二項和の有限反復として扱う。
生成元集合の拡大mono、操作木のsize、実際に出現するFinset Dのsupport、support⊆S、
同じ対象をそのsupportだけから再構成するrestrictSupportを公開した。

moduleFiniteCellOver SはこのデータのNonempty、moduleFiniteCellはS=univで定義する。
零・代表・shift・二項直和・cone・同型での閉性、同型閉性instance、
「指定集合Sから構成可能であること」と「S内のある有限集合から構成可能であること」の同値、
全生成元版の有限生成元への依存も証明した。
ここでの任意の同型輸送を許す構成データから、対象全体やenhancementのsmallnessは主張しない。
既存PerfectComplex/PerfectHomotopyの型を置き換えず、比較はU13eで行う。

Checks.FiniteCell・Checks.ShiftKFlat・Checks.StageSeven・既存Spectra.StageTwoの同時ビルドは成功
（2713 jobs、終了コード0、警告なし）。任意A・独立対象宇宙・任意指定生成元集合・
cone・整数shift・有限supportへの再構成・ZMod 2を検査した。
主要19宣言の直接公理監査は終了コード0、標準公理のみ。監査累計1923宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。
今回の2 Leanファイルにsorry/admit/新規axiomはない。担当差分の空白検査も成功。

U13a全受入は未完。次は全Hom endによる射影性についてshift・二項直和・coneの閉性を
既存の全Homのshift要素、graded-split短完全列、余積Hom計算へ接続し、構成木の帰納法で証明する。
その後D(D)内のretractによるPerfとcompact性へ進む。
U11eのcoherence・U12e/f・U13残部・U14〜U17・D4mも未完。
共有モデル圏一般論への追加要求はなく、担当外ファイルを編集していない。


### 17.75 U13a2：主Homによる有限操作の射影性（U13a受入、2026-10-16）

`Complexes/ShiftRepresentation.lean`は任意の複体K/L、閉じた次数sのcochainと次数−sの逆cochainから、
実際のchain map K→L[s]を構成する。成分式、明示的な逆による各次数の全単射・IsIso、
complexShiftIsoを証明し、逆cochainの次数tとs+t=0を指定する版も公開した。
`Module/ShiftUnitDifferential.lean`は§17.73の包含の閉性も証明する。

`Functor/ModuleShiftOpposite.lean`は任意の反変複体値dg関手Fについて、
F(op(M[s]))≅F(op M)[−s]を構成する。opposite_composeの符号(-1)^(s*s)を明示して補正し、
主Homの微分・両逆合成の保存から比較を証明する。各評価だけの自然性では代用しない。

`Derived/ProjectiveFiniteOperations.lean`は主加群圏上の代表dg関手へ適用し、
moduleHomSourceShiftIso : Hom(M[s],N)≅Hom(M,N)[−s]を公開する。
これと既存のacyclic shiftから全Hom endの意味での射影性の整数shift閉性を証明する。
cone閉性は既存moduleConeGradedSplitと主Hom短完全列の拡大閉性、
二項直和閉性はWalkingPair添字の余積Hom計算と既存の直和・余積比較同型を使用した。
新しいモデル圏や射影性の定義は導入していない。

`Perfect/FiniteCellProjective.lean`は§17.74の構成木に帰納法を適用し、
指定生成元版・全生成元版のfinite cellがhomotopically projectiveであることを証明する。
既存の射影性⇒相対K-flat性からの系も公開した。Hom_DのA-flat性を仮定しない。

Checks.FiniteCellProjective・Checks.FiniteCell・Checks.ShiftKFlat・Checks.StageSeven・既存Spectra.StageTwoの
同時ビルドは成功（2869 jobs、終了コード0、警告なし）。任意A・独立対象宇宙・全整数shift・
任意の反変dg関手・任意生成元集合・cone構成木・ZMod 2を検査した。
主要21宣言の直接公理監査は終了コード0、標準公理のみ。監査累計1944宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。
今回の6 Leanファイルにsorry/admit/新規axiomはない。担当差分の空白検査も成功。

U13aの受入照合：有限操作の構成データ・生成元への依存・有限supportへの制限（§17.74）、
全Homによる有限cellの射影性（本節）。これでU13aを受け入れる。
小さいenhancementはまだ構成しておらず、U13b〜eでretract・compact性・対象のコード化を検証する。
次は指定D(D)内のfinite cellのretractとしてPerfを定義し、既存三角構造・Karoubiとの比較へ進む。
U11eのcoherence・U12e/f・U13残部・U14〜U17・D4mは未完。
共有系列への追加要求はなく、担当外ファイルを編集していない。


### 17.76 U13b1：指定導来圏内のPerf・retract・shift・有限生成元（2026-10-16）

`Perfect/Basic.lean`はderivedFiniteCellOver Sを既存moduleToDerivedによるfinite cellの本質的像、
modulePerfectOver SをMathlib ObjectProperty.retractClosureとして定義する。
modulePerfectはS=univとし、PerfectModuleCategoryOver/PerfectModuleCategoryは同じ指定D(D)の
充満部分圏とする。新しい導来圏や一般retract閉包は導入していない。

中間の同型をretractへ吸収し、実際のfinite cell MについてXがmoduleToDerived.obj Mのretractであるという
具体的な判定式を公開した。finite cellと代表対象の包含、生成元集合の単調性、retract・同型閉性、
零対象・非空性、有限個の生成元への制限、retract閉な性質への最小性も証明する。
このretractはD(D)内のものであり、加群上のstrict dg retractへ持ち上がるとは仮定しない。

`Perfect/Shift.lean`はfinite cellの整数shift閉性を登録し、既存moduleToDerived.commShiftIsoを用いて
本質的像のshift閉性を証明する。retract閉包のshift閉性と充満部分圏のHasShiftはMathlibを再利用し、
perfectModuleInclusionのCommShiftもその既存zero/add coherenceから得る。
対象宇宙は既存D(D)のままであり、smallなenhancementやcompact性はまだ主張しない。

Checks.PerfectBasic・Checks.FiniteCellProjective・Checks.StageSeven・既存Spectra.StageTwoの同時ビルドは成功
（2851 jobs、終了コード0、警告なし）。任意A・独立対象宇宙・任意生成元集合・
具体的retract判定・有限生成元・零対象を持つPerf・HasShift/CommShift・包含の忠実性・ZMod 2を検査した。
主要29宣言の直接公理監査は終了コード0、標準公理のみ。監査累計1973宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。
今回の3 Leanファイルにsorry/admit/新規axiomはない。担当差分の空白検査も成功。

U13b全受入は未完。次は既存KaroubiFullyFaithfulの本質像判定へ、finite cellの本質的像の
充満部分圏からの包含を渡してKaroubi比較を具体化する。厚い三角閉性ではfinite cellを始域とする
導来射を実際の加群射へ持ち上げ、cone計算との可換性を証明する。
U11eのcoherence・U12e/f・U13残部・U14〜U17・D4mも未完。
共有系列への追加要求はなく、担当外ファイルを編集していない。


### 17.77 U13b2：finite cellのKaroubi延長とPerfの本質像判定（2026-10-16）

`Perfect/KaroubiCriterion.lean`はderivedFiniteCellOver Sの充満部分圏
DerivedFiniteCellCategoryOver、指定D(D)への完全忠実な包含、既存functorExtension₂による
finiteCellKaroubiFunctorを構成する。比較先はKaroubi(D(D))である。
共有KaroubiFullyFaithfulの完全忠実性・本質像判定と、Mathlibの自然な因子化同型を再利用する。
共有一般論のファイルは変更していない。

modulePerfectOver_iff_karoubi_essImageは、D(D)の対象Xについて、
Perf_S(D)に属することとtoKaroubi(X)がこの延長の本質像に入ることの同値を証明する。
順方向はD(D)内のretractをtoKaroubiで送り、共有の本質像判定へ適用する。
逆方向は形式的対象の標準retractと因子化自然同型を合成し、
Karoubi.Hom.fを取り出して実際のD(D)内のretractを得る。
全生成元版modulePerfectについても同じ判定を公開した。

既存のObjectPropertyのshiftと共有KaroubiTriangulatedFunctorのCommShiftを再利用し、
元の包含、Karoubi延長、因子化自然同型のzero/add shift整合性も登録した。
この対象判定にはD(D)全体のIsIdempotentCompleteを追加していない。
Karoubi延長のすべての形式的対象をD(D)へ戻す同値の構成は、冪等分裂の検証とともに残る。

Checks.PerfectKaroubi・Checks.PerfectBasic・Checks.FiniteCellProjective・Checks.StageSeven・
既存Spectra.StageTwoの同時ビルドは成功（2865 jobs、終了コード0、警告なし）。
任意A・独立対象宇宙・任意生成元集合・完全忠実性・本質像判定・CommShift・ZMod 2を検査した。
主要13宣言の直接公理監査は終了コード0、標準公理のみ。監査累計1986宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。
今回の2 Leanファイルにsorry/admit/新規axiomはない。担当差分の空白検査も成功。

U13b全受入は未完。次はfinite cell間の導来射の加群射への持ち上げとconeの比較から
finite cellの本質的像の三角閉性を証明し、retract閉包へ運ぶ。
U11eのcoherence・U12e/f・U13残部・U14〜U17・D4mも未完。
共有系列への追加要求はなく、担当外ファイルを編集していない。


### 17.78 U13b3：finite cellの導来射・cone比較とPerfの厚い三角閉性（2026-10-16）

`Derived/ProjectiveDerivedLifting.lean`は既存moduleProjectiveDerivedHomEquivと
moduleToHomotopyの全射性を合成し、homotopically projectiveな始域からの指定D(D)の射が
実際の閉零加群射の像になることを証明する。終域の射影性は仮定しない。

`Derived/ConeTriangles.lean`はmoduleToDerived.mapTriangleによる実際のmoduleConeTriangleの像を
定義し、K(D)からD(D)への三角関手、既存の因子化自然同型とそのCommShiftを用いてdistinguished性を証明する。
主局所化・主cone・shift比較を変更していない。

`Perfect/Triangulated.lean`はfinite cellの本質的像に入る二対象間の導来射を上記で持ち上げ、
その標準cone三角形と与えられたdistinguished三角形をArrow同型から比較する。
finite cellのcone閉性を実際の第三対象へ運び、全shift・零対象と合わせて
ObjectProperty.IsTriangulated (derivedFiniteCellOver S)を証明した。

Perfの拡大閉性はMathlibのextensionProduct_retractClosure_retractClosure_leを適用して得る。
既存retract閉包・shift閉性と合わせてmodulePerfectOver SおよびmodulePerfectが三角閉かつretract閉となる。
充満部分圏の三角構造はMathlibを再利用し、finite cell包含・Perf包含・Karoubi延長の三角性も登録した。
一般の厚い閉包や三角構造の移送論を新設していない。

Checks.PerfectTriangulated・Checks.PerfectKaroubi・Checks.PerfectBasic・Checks.FiniteCellProjective・
Checks.StageSeven・既存Spectra.StageTwoの同時ビルドは成功（2869 jobs、終了コード0、警告なし）。
任意A・独立対象宇宙・任意生成元集合・射影的始域だけの導来射持ち上げ・厚い三角閉性・
三角部分圏と包含/Karoubi関手・ZMod 2を検査した。
主要16宣言の直接公理監査は終了コード0、標準公理のみ。監査累計2002宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。
今回の4 Leanファイルにsorry/admit/新規axiomはない。担当差分の空白検査も成功。

U13bの厚い三角閉性は受入を満たした。全体の残課題は、Karoubi延長の形式的対象をD(D)の
実際の対象へ戻す冪等分裂と、Perfとの圏同値としての比較の完成である。
§17.77の本質像判定や今回の三角性だけから全Karoubi対象のD(D)での実現は結論しない。
次は既存の冪等分裂APIとD(D)の余積を再確認し、この比較を完成させる。
U11eのcoherence・U12e/f・U13残部・U14〜U17・D4mも未完。
共有系列への追加要求はなく、担当外ファイルを編集していない。


### 17.79 U13b4：可算telescopeによる指定導来圏の冪等完備性（2026-10-16）

`Category/IdempotentTelescope.lean`は、preadditiveなpretriangulated圏内の冪等射pについて、
対象Xの可算余積だけを仮定して分裂を構成する。shift作用は加法的とし、対象・射の宇宙は独立に保つ。
余積上のshift sの第n成分をpと第n+1包含の合成とし、1−sの左逆を有限和で明示した。
そのdistinguished coneの第二射はepiとなり、定数成分pの射をconeから因子化する。
各包含のconeへの像が等しいことから二つの分裂恒等式を証明する。
一般の余極限の完全性、bounded t-structure、モデル構造は使っていない。

`Derived/IdempotentComplete.lean`は、既存のu-small導来余積と三角構造を同じ主導来圏に適用し、
`moduleDerivedIsIdempotentComplete`を登録した。Aは任意可換環、Dの対象宇宙は独立、Small.{u} Dを明示する。
一般モデル圏・Quillen・転送・SM7の共有APIは重複実装していない。

Checks.DerivedIdempotentComplete・Checks.PerfectTriangulated・Checks.StageSeven・既存Spectra.StageTwoの
同時ビルドは成功（2869 jobs、終了コード0、警告なし）。任意宇宙・冪等射の分裂とZMod 2を検査した。
主要7宣言の直接公理監査は終了コード0、標準公理のみ。監査累計2009宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。
今回の3 Leanファイルにsorry/admit/新規axiomはない。担当差分の空白検査も成功。

U13b全受入には、この分裂からKaroubi延長を主導来圏へ戻してPerfとの圏同値を構成し、
shift・三角性と元の包含との比較を検証することが残る。
U11eのcoherence・U12e/f・U13残部・U14〜U17・D4mも未完。共有系列への追加要求はない。


### 17.80 U13b5：finite cellのKaroubi包絡とPerfの三角同値（U13b受入、2026-10-16）

`Perfect/KaroubiEquivalence.lean`は§17.79の主導来圏の冪等完備性を使い、
既存toKaroubiEquivalenceの逆関手でfiniteCellKaroubiFunctorの値を実際のD(D)へ戻す。
`finiteCellKaroubiRealization`は完全忠実・shift整合的・三角的であり、その値はすべてPerf_S(D)に入る。
元のfinite cell包含との因子化自然同型、Karoubi圏への再埋込みとの自然同型を構成し、両方のCommShiftを検証した。
§17.77の本質像判定を使い、Perf_S(D)へのliftが本質的全射となることを証明する。

`finiteCellKaroubiPerfectEquivalence`は任意S : Set Dについて
Karoubi(DerivedFiniteCellCategoryOver A D S) ≌ PerfectModuleCategoryOver A D Sを与える。
順逆関手のshiftと三角性、unit/counitのshift整合性を保持する。
Perf_S(D)自身の冪等完備性も、この同値を通じて既存Karoubiの冪等完備性から得た。
形式的対象をstrict dg retractとして選ぶことはしておらず、dg enhancementの構成はU13eに残す。

Checks.PerfectKaroubiEquivalence・Checks.PerfectTriangulated・Checks.DerivedIdempotentComplete・
Checks.StageSeven・既存Spectra.StageTwoの同時ビルドは成功（2879 jobs、終了コード0、警告なし）。
独立対象宇宙・任意S・本質的全射・逆関手の三角性・unit/counitのCommShift・ZMod 2を検査した。
主要30宣言の直接公理監査は終了コード0、標準公理のみ。監査累計2039宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。
今回の2 Leanファイルにsorry/admit/新規axiomはない。担当差分の空白検査も成功。

U13bの受入照合：主D(D)内のfinite cellのretractとしての定義・有限support・shift（§17.76）、
Karoubiの本質像判定（§17.77）、厚い三角閉性（§17.78）、実際の冪等分裂（§17.79）、
完全忠実・本質的全射な三角同値と包含比較（本節）。これでU13bを受け入れる。
compact性で使う余積宇宙は引き続きu-smallであり、全加群圏の対象集合をsmallと仮定しない。

U11eのcoherence・U12e/f・U13c〜e・U14〜U17・D4mは未完。
次はU11eの既存検査を確認しつつ、独立なU13cのrepresentableのHom＝評価ホモロジーから進める。
共有系列への追加要求はなく、担当外ファイル・共有ルートを変更していない。


### 17.81 U13c1：主HomのH⁰と代表加群からの導来射（2026-10-16）

`Category/HomotopyHomology.lean`は任意の主dg圏について、cycleからH⁰の射への全射を構成し、
二つのcycleの像が等しい条件を−1境界の差で判定する。
MathlibのShortComplex.moduleCatLeftHomologyDataの具体的cycle/boundary商を使い、
その商から実際のH⁰の射への全単射を証明した。homologyIsoSc'とmoduleCatHomologyIsoにより
主Hom複体のMathlib homology 0への同値に接続し、cycle・閉零射での計算式を公開する。

`Perfect/RepresentableHomology.lean`は既存の射影的始域の局所化Hom同値と上記同値を合成し、
全Hom endのH⁰による実際の導来射の計算を与える。
representableの場合は全次数dg Yoneda同型のhomologyMapを合成し、任意の主導来対象Xについて
Hom_D(Q(representable x), X) ≃ (moduleDerivedHomology x 0).obj Xを構成する。
元の加群射に対する計算式と、任意X版がQ(N)上でこの計算に戻る式も検証した。
Aは任意可換環、Dの対象宇宙は独立、Small.{u} Dを明示し、Hom_DのA-flat性は仮定しない。

Checks.RepresentableHomology・Checks.PerfectKaroubiEquivalence・Checks.StageSeven・既存Spectra.StageTwoの
同時ビルドは成功（2880 jobs、終了コード0、警告なし）。任意対象でのHom同値、
全射・単射による射の判定、ZMod 2を検査した。
主要16宣言の直接公理監査は終了コード0、標準公理のみ。監査累計2055宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。
今回の3 Leanファイルにsorry/admit/新規axiomはない。担当差分の空白検査も成功。

U13c全受入は未完。今回の射集合の同値について自然性・加法との比較を公開し、
u-small余積保存、代表加群のcompact性・生成性、Perf⇒compactへ進める。
U11eのcoherence・U12e/f・U13d/e・U14〜U17・D4mも未完。
共有系列への追加要求はなく、担当外ファイル・共有ルートを変更していない。


### 17.82 U13c2：H⁰の線形比較とcycle類の自然性（2026-10-16）

`Category/HomotopyHomologyLinear.lean`は閉零射のcycle表示、cycle/boundary商、
H⁰の射と主Hom複体のホモロジーとの同値がA線形であることを証明する。
`Category/HomotopyHomologyNaturality.lean`は具体的なzeroCyclesからMathlibのcyclesへの写像を作り、
iCyclesによる包含とhomologyπによる類の一致を証明した。任意のchain mapに対するcycle類の自然性、
全dg圏のH⁰の射計算と閉零射による後合成の自然性も公開する。

`Derived/Linear.lean`は既存K(D)経由の因子化同型から主局所化moduleToDerivedの加法性を登録する。
導来圏と局所化関手のA線形構造はMathlib.Localization.Linearの既存構成をそのまま使う。
`Perfect/RepresentableHomologyLinear.lean`は射影的始域のK(D)/D(D)のHom同値の加法・スカラー保存を
閉零射への持ち上げから証明し、主HomのH⁰および代表加群による導来評価の同値を線形同値へ強めた。
任意導来対象での線形同値の台は§17.81の同じEquivである。

Checks.RepresentableHomologyLinear・Checks.RepresentableHomology・Checks.PerfectKaroubiEquivalence・
Checks.StageSeven・既存Spectra.StageTwoの同時ビルドは成功（2888 jobs、終了コード0、警告なし）。
任意宇宙・A線形構造・任意導来対象の線形Hom同値・スカラー保存・cycle類の自然性・ZMod 2を検査した。
主要23宣言の直接公理監査は終了コード0、標準公理のみ。監査累計2078宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。
今回の5 Leanファイルにsorry/admit/新規axiomはない。担当差分の空白検査も成功。

U13c全受入は未完。次は代表加群の全導来射に対する自然同型、u-small余積保存、compact性・生成性、
Perf⇒compactを検証する。U11eのcoherence・U12e/f・U13d/e・U14〜U17・D4mも未完。
共有系列への追加要求はなく、共有ルート・他系列のファイルを変更していない。


### 17.83 U13c3：代表加群によるHom表示の全導来射に関する自然同型（2026-10-16）

`Perfect/RepresentableHomologyNaturality.lean`は射影的始域からの任意導来射を閉零射へ持ち上げ、
§17.82のH⁰の後合成自然性を使って全Homのホモロジー計算に運ぶ。
全次数dg Yoneda同型と加群射による後合成の可換式を主Hom endの成分で証明し、
代表加群によるHom表示が元の加群射に対して自然であることを得た。

`Perfect/RepresentableHomologyNaturalIso.lean`は、Homの射宇宙max(u+1,v)と評価ホモロジーの宇宙uを
区別し、後者をULiftする関手moduleDerivedHomologyLiftを定義する。
主導来圏のcoyonedaとこの関手の、moduleToDerivedによる前合成上の自然同型を構成し、
Mathlib.Localization.liftNatIsoで主局所化そのものの自然同型に延長した。
対象ごとの成分が§17.81の同じHom同値であることを検証し、任意の導来射に対する自然性を公開する。
§17.82の線形同値についても同じ自然性が成り立つ。局所小性を使って主圏を別の小さい圏へ置き換えない。

Checks.RepresentableHomologyNaturality・Checks.RepresentableHomologyLinear・Checks.PerfectKaroubiEquivalence・
Checks.StageSeven・既存Spectra.StageTwoの同時ビルドは成功（2890 jobs、終了コード0、警告なし）。
任意導来射、指定quasiIsoの逆射、線形同値の自然性、自然同型の宇宙、ZMod 2を検査した。
主要11宣言の直接公理監査は終了コード0、標準公理のみ。監査累計2089宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。
今回の3 Leanファイルにsorry/admit/新規axiomはない。担当差分の空白検査も成功。

U13c全受入は未完。次はu-small余積における評価ホモロジーの有限support表示と保存性を証明し、
代表加群のcompact性・生成性、Perf⇒compactへ接続する。
U11eのcoherence・U12e/f・U13d/e・U14〜U17・D4mも未完。
共有系列への追加要求はなく、共有一般論・共有ルート・他系列のファイルを変更していない。


### 17.84 U13c4：任意u-small導来余積に関するrepresentableのcompact性（2026-10-16）

`Complexes/CoproductSupport.lean`は任意cofanの加群余積をMathlibの具体的DirectSumと比較し、
元の有限support表示を証明する。複体の次数ごとの余積に適用し、各成分へのchain mapを
cofanの普遍性から作ることでcycleも有限個の成分cycleの像の和となることを証明した。
複体は任意非有界、次数nは任意整数であり、相手の有界性を仮定しない。
`Complexes/CoproductHomologySupport.lean`はcycle類の全射性・和・自然性を使い、
余積のH⁰の元が有限個の成分H⁰の像の和で生成されることを得る。

`Perfect/RepresentableCoproductSupport.lean`は§17.83の自然性と線形性を使い、
Q(representable x)からQ(∐ M)への導来射を、有限個のQ(M j)への射とQ(ι j)の合成の和で表す。
`Perfect/Compact.lean`はu-small余積への射の有限support条件としてmoduleCompactを定義する。
任意の導来対象族Fを既存の射影解像度Pで表し、Q(∐ P)の実際の導来余積の普遍性から
Q(∐ P)→∐ Fと∐ F→Q(∐ P)を構成して後者の右逆恒等式を証明した。
これにより上記有限support表示を任意の主導来余積へ運び、moduleRepresentable_compactを証明する。
Hom_DのA-flat性、全加群圏のsmall性、モデル構造は仮定しない。

`Perfect/CompactComparison.lean`は標準線形写像
DirectSum J (fun j => Hom(X,F j)) →ₗ[A] Hom(X,∐ F)を構成する。
余積の各成分への射を用いてこの写像が常に単射であることを証明し、
moduleCompactの有限support条件がこの標準写像の全射性、従って全単射性と同値であることを証明した。
compact対象について実際の線形同値moduleCompactHomLinearEquivを公開する。
`Perfect/CompactRetracts.lean`はcompact性のretract・同型閉性と零対象の場合を証明した。

Checks.Compact・Checks.RepresentableHomologyNaturality・Checks.PerfectKaroubiEquivalence・
Checks.StageSeven・既存Spectra.StageTwoの同時ビルドは成功（2896 jobs、終了コード0、警告なし）。
任意A・独立対象宇宙・任意u-small族・任意整数次数のcycle・Hom直和比較の線形同値・
retract/同型閉性・ZMod 2上の可算余積を検査した。
主要21宣言の直接公理監査は終了コード0、標準公理のみ。監査累計2110宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。
今回の7 Leanファイルにsorry/admit/新規axiomはない。担当差分の空白検査も成功。

U13cのrepresentableのcompact性は得られたが、全受入は未完。
次は全shiftによる生成性、compact性のshift/三角閉性とPerf⇒compactを証明する。
compact⇒Perf・小さいdg enhancement・既存PerfectHomotopy比較は引き続きU13d/eに残る。
U11eのcoherence・U12e/f・U14〜U17・D4mも未完。
共有系列への追加要求はなく、共有一般論・共有ルート・他系列のファイルを変更していない。


### 17.85 U13c5：compact性のshift・三角閉性とPerf⇒compact（2026-10-16）

`Perfect/CompactShift.lean`は加法的な導来圏の自己同値がcompact性を保つことを、
加法的随伴Hom同値とMathlibの余積保存同型から証明し、整数shiftへ適用する。
`Derived/CoproductProjection.lean`は余積から各成分への射、有限supportへの射影、
指定supportに属する包含を補射影が殺す恒等式を証明した。

`Perfect/CompactTriangles.lean`は標準Hom直和比較の像を部分加群として使う。
三角形X→Y→Z→X[1]でX/Yがcompactなら、Zから余積への射fについてYからの合成のsupportを有限集合tへ取る。
fの有限射影成分は比較の像に入り、補射影成分はYからの合成が零となる。
三角形のHom完全性により後者をX[1]経由で因子化し、X[1]のcompact性から有限supportを得る。
これによりcompact対象の三角閉性を証明し、既存のshift・retract閉性と合わせて厚い部分圏となる。

`Perfect/PerfectCompact.lean`は主局所化でのshift・二項直和・標準coneにcompact性を運び、
ModuleFiniteCellCodeの構成木で帰納する。同型とretractの閉性から
任意生成集合SについてmodulePerfectOver_compact、全生成元についてmodulePerfect_compactを証明した。
compact⇒Perfは仮定しておらず、U13dの結論を先取りしない。

Checks.PerfectCompact・Checks.Compact・Checks.PerfectKaroubiEquivalence・Checks.StageSeven・
既存Spectra.StageTwoの同時ビルドは成功（2900 jobs、終了コード0、警告なし）。
任意整数shift・任意distinguished三角形・任意生成集合SのPerf⇒compact・ZMod 2を検査した。
主要25宣言の直接公理監査は終了コード0、標準公理のみ。監査累計2135宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。
今回の5 Leanファイルにsorry/admit/新規axiomはない。担当差分の空白検査も成功。

U13c全受入は代表加群の全shiftによる生成性を残して未完。
次は評価ホモロジーの全次数消滅と主導来対象の零性を比較し、生成性を証明する。
U11eのcoherence・U12e/f・U13d/e・U14〜U17・D4mも未完。
共有系列への追加要求はなく、担当外・共有ルートを変更していない。


### 17.86 U13c6：小さいcompact生成族と主導来圏の零性判定（U13c受入、2026-10-16）

`Derived/AcyclicZero.lean`はobjectwise acyclic加群への零加群からの射が指定quasiIsoであることを証明する。
主局所化でこの射を反転し、acyclic加群の像の零性を得た。
任意の主導来対象について全評価ホモロジーの消滅と零性が同値であり、
元の加群についてはQ(N)が零であることとmoduleAcyclic Nが同値となる。
主導来圏を別の局所化やモデル的Hoへ置き換えていない。

`Perfect/Generators.lean`は加群評価のCommShiftとMathlibのhomology shift同型を合成し、
H⁰(ev_x(N[n])) ≅ Hⁿ(ev_x N)を構成する。代表加群のHom計算と主局所化のshift比較により、
全x/nについてHom(Q(representable x), X[n])が零であることとIsZero Xの同値を証明した。
shift随伴で始域をshiftした同値へ変換し、D×ℤで添字付けたmoduleCompactGeneratorsを定義した。
その像はSmall.{u}で、各対象がcompactであり、この族からのHom消滅が正確に主導来対象の零性を検出する。
D(D)全体の対象集合がsmallであるとは主張しない。

Checks.CompactGenerators・Checks.PerfectCompact・Checks.Compact・Checks.StageSeven・既存Spectra.StageTwoの
同時ビルドは成功（2892 jobs、終了コード0、警告なし）。独立対象宇宙・生成族のsmallness・compact性・
Hom消滅による零性・acyclic判定・正負shift（2と−3）・ZMod 2を検査した。
主要11宣言の直接公理監査は終了コード0、標準公理のみ。監査累計2146宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。
今回の3 Leanファイルにsorry/admit/新規axiomはない。担当差分の空白検査も成功。

U13cの受入照合：代表加群による評価ホモロジーのHom計算（§17.81）、線形性（§17.82）、
全導来射での自然性（§17.83）、任意u-small余積での標準Hom直和比較とrepresentableのcompact性（§17.84）、
compact性の厚い閉性・Perf⇒compact（§17.85）、小さいcompact生成族と零性検出（本節）。
これでU13cを受け入れる。compact生成性の零性検出という用語はKeller v5 §3.5、p.8とも照合した。
採用済み引用は引き続き0件で、上記の主張はすべてLeanで証明した。

U13dのcompact⇒Perfは未完。DG-PERの原典Keller v5 Cor.3.7（p.8）は再確認したが、まだ採用していない。
採用する場合もfinite cell/retractとしての本Perfと原典のthick閉包の一致、対象・宇宙・射クラスを
固定した契約を先に照合する。U13eの小さいdg enhancement・既存perfect比較も未完。
U11eのcoherence・U12e/f・U14〜U17・D4mも未完。共有系列への追加要求はない。


### 17.87 U13d1：finite cellとPerfの最小性・原典の閉包との照合（2026-10-16）

`Perfect/UniversalProperty.lean`は主導来圏の任意の三角閉・同型閉な性質Pについて、
指定代表加群を含めばそのfinite cellの全本質的像を含むことを構成木の帰納法で証明する。
二項直和の場合は加法的主局所化のbiprod保存同型とdistinguishedなsplit三角形を使い、
標準coneの場合は既存moduleDerivedConeTriangleを使う。一般の閉包や三角構造を新設しない。

Pがさらにretract閉ならmodulePerfectOver S ≤ Pと「PがSの代表加群をすべて含む」ことが同値になる。
全生成元についてのmodulePerfect_le_iff_generatorsも公開した。
既存の厚い閉性と合わせ、現在定義したPerfは代表加群を含む最小の厚い部分圏である。
この最小性をP=compactへ適用する例で、別に証明済みのPerf⇒compactも再確認する。

Checks.PerfectUniversalProperty・Checks.CompactGenerators・Checks.PerfectCompact・Checks.StageSeven・
既存Spectra.StageTwoの同時ビルドは成功（2893 jobs、終了コード0、警告なし）。
任意生成集合・任意の三角閉かつretract閉なP・最小性からのPerf⇒compactを検査した。
主要6宣言の直接公理監査は終了コード0、標準公理のみ。監査累計2152宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。
今回の2 Leanファイルにsorry/admit/新規axiomはない。担当差分の空白検査も成功。

DG-PER原典の再照合：Keller math/0601185v5、2006-06-19版、§2.1〜2.2 pp.2〜4、§3.1〜3.2 pp.5〜6、§3.5 p.8、Cor.3.7。
原典は可換基礎環、非有界cochain複体（dの次数+1）、小さいdg圏、右dg加群の準同型局所化を扱う。
triaは代表加群からのshift/extension閉包、perはその直和因子閉包であり、今回の最小性が定義照合を与える。
compact性の標準Hom直和比較は§17.84、u-small生成族と零性検出は§17.86で証明済み。
採用する場合の対象は既存DerivedModuleCategory A D、射クラスはmoduleQuasiIso、
環A : Type u、D : Type vにSmall.{u} D、余積添字はType uに固定し、追加のflatnessを仮定しない。
採用範囲は逆方向compact⇒modulePerfectだけとし、Brown表現性・Morita・enhancementの存在を混ぜない。
今回も引用は採用していない。U13d全受入とU13eは未完で、採用済み引用は0件。
U11eのcoherence・U12e/f・U14〜U17・D4mも未完。共有系列への追加要求はない。


### 17.88 U13e1：全Hom endを持つ射影的perfect dg部分圏（2026-10-16）

`Category/FullSubcategory.lean`は主Enriched dg圏の対象を性質Pで制限し、Hom複体・微分・単位・合成を
そのまま使う充満dg部分圏を構成する。閉零包含の完全忠実性と境界関係の反映からH⁰包含も完全忠実となる。
`Derived/HomotopyLinear.lean`はQとの自然同型と商関手の充満・本質的全射性からK(D)→D(D)のA線形性を得る。

`Perfect/Enhancement.lean`は実際の右dg加群で、homotopically projectiveかつ主導来像がPerfOver Sに入る
対象の充満dg部分圏を構成した。Homは既存moduleHomの全次数endである。
射影対象からの局所化Hom計算によりH⁰→PerfOver Sは完全忠実であり、任意のPerf対象の
標準射影解像度が本質的全射性を与える。`Perfect/EnhancementLinear.lean`はこの比較・同値のA線形性と
主導来包含との比較自然同型を公開する。逆関手の加法性・線形性も確認した。

Checks.PerfectEnhancement・Checks.PerfectUniversalProperty・Checks.CompactGenerators・Checks.StageSeven・
既存Spectra.StageTwoの同時ビルドは成功（2897 jobs、終了コード0、警告なし）。
任意生成集合、全Homと微分の一致、完全忠実・本質的全射・線形性、ZMod 2、空生成集合を検査した。
主要30宣言の直接公理監査は終了コード0、標準公理のみ。監査累計2182宣言。
今回の5 Leanファイルにsorry/admit/新規axiomはない。
文書検査は22 Markdown・311 exposition参照、失敗0件。担当差分の空白検査も成功。

U13e全受入は未完。今回の対象型全体をsmallとは主張しない。
次はfinite cellの小さい代表系を構成し、固定版Mathlibの関手像・retract閉包の本質的小性を用いて
Perfの本質的小性を証明する。その小さい代表系の射影解像度へ全Homを制限し、
shift・三角構造の整合性、一対象Aと既存PerfectHomotopyの比較を完成させる。
U13dのcompact⇒Perf、U11eのcoherence、U12e/f、U14〜U17、D4mは未完。
採用済み引用は0件。共有系列への追加要求はなく、共有ルート・他系列のファイルを変更していない。


### 17.89 U13e2：finite cellの小さい段階別代表とPerfの本質的小性（2026-10-16）

`Perfect/SmallStages.lean`はType uの添字型と証明付き有限cell族の組を段階別に構成する。
零段階は零対象とShrink Sで添字付けた代表加群、後続段階は前段階・全整数shift・二項和・
前段階の任意の二対象間の全閉零射のconeを含む。各添字型と全段階のΣ型はType uに留まる。
段階間の包含は同じ対象を保ち、任意の二段階の代表を共通段階へ移せる。

`Perfect/SmallStageCover.lean`はModuleFiniteCellCodeの構成木で帰納し、任意の有限cellと
ある段階別代表との実際の加群同型を構成する。coneの枝では二対象の同型で射を移し、
既存Arrow圏とmoduleConeFunctorによりconeの同型を得る。
cone関手のmapIsoにはArrowの始終域を明示し、逆方向の型推論による大きな展開を避けた。
この実装は既定heartbeat予算でビルドできる。

`Perfect/EssentiallySmall.lean`はこの小さい被覆からfinite cellの本質的小性を証明し、
固定版Mathlibの関手像とretract閉包の本質的小性を主導来圏に適用する。
任意の生成集合SについてPerfOver Sは本質的にu-smallであり、実際のPerf対象からなる
u-smallな代表部分族も選べる。全加群圏・全導来圏・全射影的perfect対象型のsmall性は仮定しない。

Checks.PerfectSmallness・Checks.PerfectEnhancement・Checks.StageSeven・既存Spectra.StageTwoの
同時ビルドは成功（2878 jobs、終了コード0）。独立対象宇宙、任意S、空集合、ZMod 2、
小さい段階添字と既存SmallModel上のSmallCategoryを検査した。
主要17宣言の直接公理監査は終了コード0、標準公理のみ。監査累計2199宣言。
今回の4 Leanファイルにsorry/admit/新規axiomはない。警告のない再ビルドも成功。
文書検査は22 Markdown・311 exposition参照、失敗0件。担当差分の空白検査も成功。

次はこの小さいPerfモデルの射影的代表を選び、その像の充満dg部分圏を構成する。
U13e全受入にはさらにshift・三角構造の整合性と既存PerfectHomotopy比較が必要。
U13d・U11eのcoherence・U12e/f・U14〜U17・D4mは未完。採用済み引用は0件。
共有一般論と共有ルート・他系列のファイルを変更していない。


### 17.90 U13e3：小さい全Hom dg enhancementと包含の準同値（2026-10-16）

`Perfect/SmallEnhancement.lean`は主PerfOver SのMathlib SmallModel（対象はType u）の各対象を、
§17.88のH⁰同値の逆関手で実際の射影的perfect dg加群へ戻す。
その像の充満dg部分圏SmallPerfectDGModuleOverを定義した。
像の対象型はSmall.{u}であり、元の全加群圏のsmall性を仮定しない。
Homは元のmoduleHomの全次数endで、微分と豊穣合成もそのまま保持する。

小さい代表系から全射影的perfect dg圏への包含は、各Hom複体で恒等射であり、H⁰で完全忠実である。
主Perf上の同型を完全忠実比較で引き戻してH⁰包含の本質的全射性を証明し、実際のdg包含の
QuasiEquivalenceを得た。小さい代表系のH⁰と主Perfの同値も構成した。
順・逆関手のA線形性と加法性を検査し、選んだ代表の対象計算を公開する。
これは通常のSmallModelにdg構造の存在を仮定する構成ではなく、実際のdg加群の全Homを制限する構成である。

Checks.SmallPerfectEnhancement・Checks.PerfectSmallness・Checks.PerfectEnhancement・Checks.StageSeven・
既存Spectra.StageTwoの同時ビルドは成功（2880 jobs、終了コード0、警告なし）。
独立対象宇宙、任意S、空集合、ZMod 2、対象のsmall性、全Homと微分の一致、包含の準同値、
H⁰比較の同値・線形性・逆関手の加法性を検査した。
主要20宣言の直接公理監査は終了コード0、標準公理のみ。監査累計2219宣言。
今回の2 Leanファイルにsorry/admit/新規axiomはない。
文書検査は22 Markdown・311 exposition参照、失敗0件。担当差分の空白検査も成功。
前節の追記時に過去2節へ重複して入った検証文を削除し、過去の記録を元に戻した。

U13eの小さいdg代表系とH⁰の線形同値は構成できたが、全受入は未完。
次は実際の加群shift/coneによる閉性と比較の構造整合性を証明し、一対象Aで既存PerfectHomotopyと比較する。
U13dのcompact⇒Perf、U11eのcoherence、U12e/f、U14〜U17、D4mは未完。採用済み引用は0件。
共有系列への追加要求はなく、共有一般論・共有ルート・他系列のファイルを変更していない。


### 17.91 U13e4：実際の射影的perfect加群の有限操作と主局所化比較（2026-10-16）

`Category/Restriction.lean`は性質PをQへ送るdg関手を充満dg部分圏へ制限し、
制限後の包含と元の関手との可換性を全Hom上の関手等式として証明した。
抽象的な対象型でこの等式を証明することで、具体的な大きいHom endをカーネルで展開する問題を避ける。

`Perfect/EnhancementOperations.lean`は実際の右dg加群の零・整数shift・二項和・任意の閉零射の
標準coneが射影的perfectであることを証明した。射影性は既存の主Hom計算、perfect性は
主局所化のshift/biprod比較とdistinguished cone三角形から得る。
これらの実際の対象を全射影的perfect dg部分圏の対象として公開する。
整数shiftは既存moduleShiftDGを上の制限APIで制限した真のdg関手であり、包含との可換性も証明した。

閉零代表からH⁰比較を通る主導来関手と、全加群への包含の後に元のQを適用する関手との
自然同型perfectDGModuleClosedToDerivedIsoを構成した。
実際のdg shift対象の比較像と、比較像の主導来整数shiftの対象同型も公開する。
これはHasShiftのzero/add coherenceや三角構造の全比較を完成したという主張ではない。

Checks.PerfectEnhancementOperations・Checks.SmallPerfectEnhancement・Checks.PerfectSmallness・
Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功（2883 jobs、終了コード0、警告なし）。
任意A・独立対象宇宙・任意S、実際のshift/cone対象、全Hom関手等式、正負shift、ZMod 2を検査した。
主要14宣言の直接公理監査は終了コード0、標準公理のみ。監査累計2233宣言。
今回の3 Leanファイルにsorry/admit/新規axiomはない。
文書検査は22 Markdown・311 exposition参照、失敗0件。担当差分の空白検査も成功。

次は実際のshiftに対するH⁰のzero/add coherence、cone三角形と主Perfの構造比較、
小さい代表系への運搬、一対象Aと既存PerfectHomotopyの比較を進める。U13e全受入は未完。
U13dのcompact⇒Perf、U11eのcoherence、U12e/f、U14〜U17、D4mも未完。
採用済み引用は0件。共有一般論・共有ルート・他系列のファイルを変更していない。


### 17.92 U13e5：実際のdg shiftのH⁰と整合的な整数shift（2026-10-16）

`Module/ShiftHomotopyComparison.lean`は既存moduleShiftDGのH⁰関手とK(D)の商shiftとの
自然同型を、商のnatIsoLiftと閉零shiftの比較から構成した。
`Perfect/EnhancementShiftComparison.lean`は§17.91の全Hom関手等式をH⁰へ運び、
射影的perfect dg shiftのH⁰が包含後のK(D)のshiftと自然に可換であることを証明する。
既存K(D)→D(D)のCommShiftから主導来比較を得て、Perf包含への右whiskeringの完全忠実性から
主Perfへの自然比較も引き戻した。対象ごとの同型だけでなく、全H⁰射で自然な比較である。

`Perfect/EnhancementShift.lean`は主Perf同値の逆関手と上記の実際のshift関手との比較を構成し、
固定版MathlibのHasShift.inducedを適用する。
各整数のshift関手は実際のperfectDGModuleShiftDGのH⁰そのものであり、zero/addとその整合性を
既存の誘導shift APIから得る。各shiftは加法的であり、主Perf同値の順・逆関手、単位・余単位が
この整数shiftと整合する。主モデルの複体shiftを別の対象操作に置き換えない。

Checks.PerfectEnhancementShift・Checks.PerfectEnhancementOperations・Checks.SmallPerfectEnhancement・
Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功（2886 jobs、終了コード0、警告なし）。
任意A・独立対象宇宙・任意S、実際のdg shiftとの関手一致、順逆CommShift、同値のcoherence、
2と−3の合成、ZMod 2上の空生成集合を検査した。
主要12宣言の直接公理監査は終了コード0、標準公理のみ。監査累計2245宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。担当差分の空白検査も成功。
今回の4 Leanファイルにsorry/admit/新規axiomはない。

次はこの実際のshiftの下でcone三角形と主Perfの三角構造を比較し、
小さい代表系へ構造を運び、一対象Aで既存PerfectHomotopyとの比較を証明する。U13e全受入は未完。
U13d・U11eのcoherence・U12e/f・U14〜U17・D4mも未完。採用済み引用は0件。
共有一般論・共有ルート・他系列のファイルを変更していない。


### 17.93 U13e6：実際のdg shiftを保ったH⁰三角構造（2026-10-16）

`Category/TriangulatedTransport.lean`は既に与えた整数shiftと整合する加法的同値について、
対象側のdistinguished三角形の逆像がPretriangulatedの各公理を満たすことを証明する。
零対象は同値で選んで完全忠実性で反映する。coconeは対象側で選び、順関手の充満性で射を戻し、
三角形の同型を明示する。回転の公理はmapTriangleRotateIso、三角形の射の完成は
対象側の完成とshift比較の自然性から得る。一般モデル圏・Quillen・転送の理論は変更しない。

`Perfect/EnhancementTriangulated.lean`は上の構成を実際の射影的perfect dg加群のH⁰へ適用した。
§17.92で構成した各整数の実際のdg shiftのH⁰とzero/add coherenceをそのまま維持する。
主Perfへの比較は三角関手で、完全忠実性から八面体公理を反映する。
順・逆関手を含む三角同値と、主Perfでの像によるdistinguished性の判定を公開した。

Checks.PerfectEnhancementTriangulated・Checks.PerfectEnhancementShift・Checks.SmallPerfectEnhancement・
Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功（2896 jobs、終了コード0、警告なし）。
任意A・独立対象宇宙・任意S、零対象・三角構造・八面体・順逆三角関手、
distinguished性の反映・contractible三角形・ZMod 2上の空生成集合を検査した。
主要8宣言の直接公理監査は終了コード0、標準公理のみ。監査累計2253宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。担当差分の空白検査も成功。
今回の3 Leanファイルにsorry/admit/新規axiomはない。

三角構造を同値で引き戻せたことと、実際のdg coneによる標準三角形との一致は区別する。
次は小さい代表系のshift/三角比較を受け入れた後、標準cone三角形との一致と一対象Aの既存PerfectHomotopy比較を証明する。
U13e全受入・U13d・U11eのcoherence・U12e/f・U14〜U17・D4mは未完。採用済み引用は0件。
共有ルート・共有モデル一般論・他系列のファイルを変更していない。


### 17.94 U13e7：小さいdg代表系のH⁰三角構造と包含比較（2026-10-16）

`Perfect/SmallEnhancementTriangulated.lean`は小さい代表系のH⁰に整数shiftを与える。
主Perfへ送り、そこでshiftした後に選択した小さい射影的代表へ戻る関手を各整数に定め、
余単位で主Perfのshiftとの比較を構成する。固定版MathlibのFullyFaithful.hasShiftにより
zero/add coherenceを誘導し、同値の順逆関手と単位・余単位のCommShiftを得た。
小さい代表系が元の加群shiftで厳密に閉じているとは仮定しない。

主Perfのdistinguished三角形を引き戻し、前節の各公理の証明を再利用して、
小さい代表系のH⁰を三角圏とした。主Perfとの比較はshift整合的な三角同値である。
さらに、実際の小さいdg包含のH⁰と全射影的perfect H⁰との比較を構成した。
主Perfへの因子化の自然同型を通じてCommShiftとその整合性を引き戻し、
包含の三角性を完全忠実な主Perf比較で判定した。この包含は既に証明した完全忠実性・
本質的全射性により同値でもある。元のdg包含の準同値と全Homの一致は§17.90のまま保持する。

Checks.SmallPerfectEnhancementTriangulated・Checks.PerfectEnhancementTriangulated・
Checks.PerfectEnhancementShift・Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功
（2897 jobs、終了コード0、警告なし）。任意A・独立対象宇宙・任意S、対象のsmall性、
小さいH⁰の八面体・順逆三角比較、実際の包含のCommShift・三角性・同値、正負shift合成、
ZMod 2上の空生成集合を検査した。
主要19宣言の直接公理監査は終了コード0、標準公理のみ。監査累計2272宣言。
今回の2 Leanファイルにsorry/admit/新規axiomはない。
文書検査は22 Markdown・311 exposition参照、失敗0件。担当差分の空白検査も成功。

U13e全受入は、実際の標準dg cone三角形との一致と一対象Aの既存PerfectHomotopy比較を残す。
U13d・U11eのcoherence・U12e/f・U14〜U17・D4mも未完。採用済み引用は0件。
共有一般論・共有ルート・他系列のファイルを変更していない。


### 17.95 U13e8：実際のdg coneによるH⁰標準三角形と射の計算（2026-10-16）

`Perfect/EnhancementCone.lean`は実際の射影的perfect dg加群のH⁰対象と、閉零加群射のH⁰像を定義した。
全Homを共有する閉零包含の完全忠実性を明示し、そのpreimageで射を持ち上げる。
持ち上げた射は包含後に元のK(D)の像へ戻り、恒等射・合成・零射を保つ。
整数shiftの対象は既存の実際のdg shift対象と定義的に一致する。
主導来比較の像と元のQの射がmoduleToHomotopyDerivedIsoで可換となる計算式も証明した。

実際のmoduleConeとmoduleConeInr・moduleConeConnectingをそのまま使うH⁰三角形
perfectDGModuleConeTriangleを構成した。第三射の標的はshift 1であり、
前節の逆関手で恣意的なcone対象や射を選んだものではない。
第一射・第二射の計算式を公開し、最初の二射の合成が零となることを
包含の忠実性と元のK(D)の標準cone三角形から証明した。

Checks.PerfectEnhancementCone・Checks.SmallPerfectEnhancementTriangulated・
Checks.PerfectEnhancementTriangulated・Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功
（2898 jobs、終了コード0、警告なし）。任意A・独立対象宇宙・任意S、閉零包含の完全忠実性、
実際のcone対象、第一/第二射の零合成、負shift、ZMod 2上の空生成集合の標準三角形を検査した。
主要14宣言の直接公理監査は終了コード0、標準公理のみ。監査累計2286宣言。
今回の2 Leanファイルにsorry/admit/新規axiomはない。
文書検査は共有ルートのolean不在により一度実行できなかったが、再生成後の再試行は
22 Markdown・311 exposition参照、失敗0件。担当差分の空白検査も成功。

この標準三角形のdistinguished性はまだ証明していない。
残る照合は、§17.92で誘導した整合的CommShiftと標準connecting射の比較が、
主PerfのmapTriangleで用いる第三射と一致すること。その後に前節の三角構造でのdistinguished性を得る。
一対象Aの既存PerfectHomotopy比較も未完。U13e全受入、U13d、U11eのcoherence、U12e/f、U14〜U17、D4mは未完。
採用済み引用は0件。共有一般論・共有ルート・他系列のファイルを変更していない。


### 17.96 U13e9：shift比較の直接計算と主導来三角比較（2026-10-16）

`Perfect/EnhancementShift.lean`の誘導構成を、主Perfへの完全忠実関手と既に構成した自然同型から
FullyFaithful.hasShiftで直接与える形に整理した。各整数のshift関手は引き続き実際のdg shiftのH⁰であり、
既存の公開名・関手一致・加法性・順逆CommShift・単位/余単位の整合性を保持する。
逆関手の比較は順関手からMathlibの随伴APIで構成する。
これによりperfectDGModuleToPerfect_commShiftIsoは実際のdg shiftから作った自然同型との定義的な一致となる。
§17.92の逆関手経由の自然比較もAPIとして保持した。

`Perfect/EnhancementShiftComparison.lean`は主Perfの比較の成分を包含で写した計算式を証明する。
これは主導来比較と、Perf包含のshift比較の逆との合成である。
`Perfect/EnhancementDerivedComparison.lean`は主導来比較のCommShiftと、主Perf経由の因子化の
shift整合性を構成し、既存の三角包含との合成から主導来比較の三角性を得た。
その整合的CommShiftの各成分が、実際のdg shiftから構成した主導来比較と一致することも証明した。
標準coneの第三射を照合する際に、抽象的に選んだshift比較へ置き換えずに計算できる。

Checks.PerfectEnhancementDerivedComparison・Checks.PerfectEnhancementCone・
Checks.SmallPerfectEnhancementTriangulated・Checks.PerfectEnhancementTriangulated・
Checks.PerfectEnhancementShift・Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功
（2901 jobs、終了コード0、警告なし）。同じ対象・shiftの公開契約、小さい代表系の三角比較、
実際のcone三角形、主導来三角性・shift成分の一致、任意SとZMod 2上の空生成集合を検査した。
新規6宣言と影響する既存53宣言を合わせ、主要59宣言の直接公理監査は終了コード0、標準公理のみ。
新規分だけを加えた監査累計は2292宣言。
今回の5 Leanファイルにsorry/admit/新規axiomはない。
文書検査は22 Markdown・311 exposition参照、失敗0件。担当差分の空白検査も成功。

次は主導来shift比較を閉零代表上で計算し、moduleToHomotopyDerivedIsoのCommShift整合性と
connecting射の自然性から、実際の標準cone三角形の主導来比較を構成してdistinguished性を証明する。
U13e全受入・一対象Aの既存PerfectHomotopy比較、U13d、U11eのcoherence、U12e/f、U14〜U17、D4mは未完。
採用済み引用は0件。共有一般論・共有ルート・他系列のファイルを変更していない。


### 17.97 U13e10：閉零代表上のshift比較と大きい関手等式の評価（2026-10-16）

`Category/QuotientComparison.lean`は商へ降ろした自然同型を元の代表で評価し、
関手等式・左右whiskering・結合子を含む比較を対象ごとの合成へ計算する。
`Category/RestrictionComparison.lean`は対象の性質を保つdg関手の制限からH⁰比較を構成し、
その成分が包含した対象における元の比較となることを抽象的なdg圏で証明した。
主perfect比較の包含自然同型はこのコンストラクタを使う形へ整理し、公開名・型を保持した。
具体的な右dg加群の全Hom endを関手等式の輸送中に展開するカーネルのタイムアウトを避けるためである。

`Module/ShiftComparisonEvaluation.lean`はこの抽象評価を実際のdg加群shiftへ適用し、
閉零代表上で元の商関手のshift比較が得られることを証明した。
`Perfect/EnhancementShiftEvaluation.lean`は任意H⁰対象での包含比較の評価、閉零代表上での評価、
主導来比較が既存K(D)経由の合成関手のshift比較に一致することを証明した。
次数や対象の仮定は変更せず、負shiftと標数2も含む。

Checks.PerfectEnhancementShiftEvaluation・Checks.PerfectEnhancementDerivedComparison・
Checks.PerfectEnhancementCone・Checks.SmallPerfectEnhancementTriangulated・Checks.StageSeven・
既存Spectra.StageTwoの統合ビルドは成功（2904 jobs、終了コード0、警告なし）。
新規9宣言と影響する既存59宣言を合わせ、主要68宣言の直接公理監査は終了コード0、標準公理のみ。
新規分だけを加えた監査累計は2301宣言。
今回の6 Leanファイルにsorry/admit/新規axiomはない。
文書検査のLean環境exportは共有側TorFiniteCoefficients.olean不在で実行できなかった。
同じ対象集合22 Markdownのローカルリンクだけを別途検査し、失敗0件。exposition参照のexport検査は再試行待ち。
担当差分の空白検査は成功。

次はこれらの評価式、既存moduleToHomotopyDerivedIsoのshift整合性、connecting射に関する自然性を
合成し、実際の標準cone三角形と主導来cone三角形の同型を構成する。
U13e全受入・既存PerfectHomotopy比較、U13d、U11eのcoherence、U12e/f、U14〜U17、D4mは未完。
採用済み引用は0件。共有一般論・共有ルート・他系列のファイルを変更していない。


### 17.98 U13e11：実際の標準dg cone三角形と三角構造の一致（2026-10-16）

`Category/TriangleComparison.lean`は第三射の計算式をshift整合関手のmapTriangleへ運ぶ。
`Perfect/EnhancementCone.lean`は実際のconnecting射による第三射の計算式と、任意のshift整合関手で
写した第三射の計算式を公開した。関手を抽象的なまま評価してから主導来関手へ特殊化することで、
具体的な局所化関手の写像を投影の型照合中に展開するカーネルのタイムアウトを避けた。

`Perfect/EnhancementConeComparison.lean`は§17.97のshift評価、既存moduleToHomotopyDerivedIsoの
CommShift整合性、実際のconnecting射の自然性を合成する。
標準dg cone三角形の主導来像と、元の加群のmoduleDerivedConeTriangleとの同型を構成した。
三つの対象同型は既存moduleToHomotopyDerivedIsoの成分であり、第三射の比較も実際のconnecting射を使う。
主導来比較の完全忠実性と三角性から、標準dg cone三角形のdistinguished性を反映した。

さらにH⁰射を閉零代表へ持ち上げ、包含の完全忠実性で実際の加群射へ戻す計算式を証明した。
任意のdistinguished三角形の第一射をこの代表で表し、同じ第一射を持つdistinguished三角形の
既存比較定理から標準cone三角形との同型を得る。
これによりperfectDGHomotopy_distinguished_iff_coneを公開した。
移送した三角構造は、実際の射影的perfect dg加群の標準cone三角形の同型閉包と一致する。

Checks.PerfectEnhancementConeComparison・Checks.PerfectEnhancementShiftEvaluation・
Checks.PerfectEnhancementDerivedComparison・Checks.SmallPerfectEnhancementTriangulated・
Checks.PerfectEnhancementTriangulated・Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功
（2907 jobs、終了コード0、警告なし）。任意A・独立対象宇宙・任意S、標準coneの主導来同型、
distinguished性、第二/第三射の零合成、ZMod 2上の空生成集合を検査した。
主要9宣言の直接公理監査は終了コード0、標準公理のみ。監査累計2310宣言。
今回の4 Leanファイルにsorry/admit/新規axiomはない。
共有側TorFiniteCoefficients.oleanの再生成を確認し、文書検査を再試行した。
22 Markdown・311 exposition参照、失敗0件。前節で保留したexport検査もここで解消した。
担当差分の空白検査も成功。

U13eの実際のshift・標準cone三角形・小さい代表系と主Perfの三角比較は構成できた。
全受入には一対象Aの既存PerfectHomotopyとの比較と、そのretract・線形性を含む照合が残る。
U13dのcompact⇒Perf、U11eのcoherence、U12e/f、U14〜U17、D4mも未完。採用済み引用は0件。
共有一般論・共有ルート・他系列のファイルを変更していない。


### 17.99 U13e12：主dg複体H⁰と既存の非有界ホモトピー圏（2026-10-16）

`Category/ComplexHomotopyComparison.lean`は既存complex_boundary_iffを使い、
主dg複体圏Ch(A)のH⁰からMathlib HomotopyCategory (ModuleCat.{u} A) (.up ℤ)への関手を構成した。
複体・射を別モデルへ置き換えず、既存の閉零比較closedToComplexと既存のホモトピー商を合成して
境界関係で降ろす。比較の充満性は二つの商/比較の充満性、忠実性は既存の商での等式から
chain homotopyを取り境界関係へ戻すことで証明した。全対象は同じ複体の代表から得られる。

閉零比較のA線形性をHom cochainで証明し、H⁰比較の加法性・A線形性を商の充満・本質的全射性で降下した。
実際のA線形同値complexHomotopyEquivalenceと商関手の可換四角形を公開する。
環Aと加群の宇宙uを明示し、通常複体のHomotopyCategoryをdg加群の二重複体として扱わない。

Checks.ComplexHomotopyComparison・Checks.PerfectEnhancementConeComparison・Checks.StageSeven・
既存Spectra.StageTwoの統合ビルドは成功（2900 jobs、終了コード0、警告なし）。
任意可換環・非有界複体、実際のchain mapの商像の計算、順逆のA線形性と加法性、ZMod 2を検査した。
主要12宣言の直接公理監査は終了コード0、標準公理のみ。監査累計2322宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。担当差分の空白検査も成功。
今回の2 Leanファイルにsorry/admit/新規axiomはない。

次は既存strictlyPerfectComplexの対象へ制限し、その主Homを持つdg圏のH⁰を既存PerfectHomotopyと比較する。
これは一対象Aの主Perfとの比較の中間段階であり、主Perfのretract閉包と有限射影代表の一致を先取りしない。
U13e全受入・U13d・U11eのcoherence・U12e/f・U14〜U17・D4mは未完。採用済み引用は0件。
共有ルート・既存PerfectComplex・共有一般論・他系列のファイルを変更していない。


### 17.100 U13e13：既存有限射影複体の全Hom dg表示（2026-10-16）

`Perfect/StrictComplexEnhancement.lean`は既存strictlyPerfectComplexを対象条件に持つ
主dg複体圏の充満dg部分圏StrictPerfectDGComplexを構成した。Homは既存homComplexの
全整数次数を保つ。主H⁰から既存PerfectHomotopyへの比較を構成し、充満・忠実・本質的全射を証明した。
`Perfect/StrictComplexEnhancementLinear.lean`は比較と同値のA線形性・加法性、包含との自然同型を公開する。
この対象型全体のsmall性や、一対象Aの主Perfとの一致はまだ主張しない。

Checks.StrictComplexEnhancement・Checks.ComplexHomotopyComparison・Checks.PerfectEnhancementConeComparison・
Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功（3427 jobs、終了コード0、警告なし）。
任意可換環、全次数Homと微分の一致、順逆の線形性・加法性、ZMod 2を検査した。
主要18宣言の直接公理監査は標準公理のみ。監査累計2340宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。担当差分の空白検査も成功。
今回の実装にsorry/admit/新規axiomはない。

次は複体と一対象Aの右dg加群との実際のdg比較を確定し、有限射影複体の射影性と
主Perfのretract閉包との比較へ接続する。U13e全受入・U13d・U11eのcoherence・U12e/f・
U14〜U17・D4mは未完。採用済み引用は0件。共有ルート・既存PerfectComplex・他系列は変更していない。


### 17.101 U13e14：非有界複体と一対象Aの右dg加群の実際の準同値（2026-10-16）

`Module/RingDGComparison.lean`はringConstantHomIsoの逆を全Hom写像に用いてringConstantDGを構成する。
既存の評価の単位・合成保存を逆同型で反映し、全整数次数の豊穣合成を保つことを証明した。
評価との合成はdg恒等関手に等しい。既存ringModule_recoverによりH⁰の本質的全射を証明し、
ringConstantDGとmoduleEvaluationDGの双方が準同値であることを公開する。
各Hom写像は準同型であるだけでなくchain isoである。任意可換環・非有界複体を扱う。

Checks.RingDGComparison・Checks.StrictComplexEnhancement・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（3279 jobs、終了コード0）。任意A、HomのIsIso、dg恒等関手への復元、ZMod 2を検査した。
主要8宣言の直接公理監査は標準公理のみ。監査累計2348宣言。
全体文書検査は共有側CLMST.CompletedTargetLength.olean不在でexport段階が停止したため成功とは記録しない。
Markdownのローカルリンクは別途22ファイルを検査し失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

次は有限射影複体のK-projective性を全次数Homのacyclic性へ接続し、一対象加群の主射影性を証明する。
主Perfのretract閉包と有限射影代表の一致は残る。U13e全受入・U13d・U11eのcoherence・U12e/f・
U14〜U17・D4mは未完。採用済み引用は0件。共有ルート・既存PerfectComplex・他系列は変更していない。


### 17.102 U13e15：K-projective条件と全Hom endの射影性の照合（2026-10-16）

`Complexes/KProjectiveHom.lean`はMathlibのIsKProjectiveと全次数線形Homがacyclic対象を消す条件の同値を証明する。
次数nのcycleをN[n]への閉零射に移し、K-projective性によるchain homotopyをrightUnshiftで戻す。
微分の符号n.negOnePowを補正し、全整数次数で境界表示を得る。逆方向は次数0の境界から通常のchain homotopyを構成する。
任意可換環上の非有界複体で成立し、値域の有界性・flat性を仮定しない。

`Module/RingProjective.lean`は一対象AのHom end評価同型でこの判定を運び、
主moduleHomotopicallyProjective条件と評価複体のIsKProjective条件の同値を公開する。
一般の多対象dg圏で評価ごとの射影性を主Homの射影性と同一視する主張ではない。
`Perfect/StrictComplexProjective.lean`は既存strictlyPerfectComplexの上界と各次数のModule.Projectiveから
既存Mathlibの有界上射影判定を使い、一対象Aの主射影的dg加群となることを証明する。

Checks.StrictComplexProjective・Checks.RingDGComparison・Checks.StrictComplexEnhancement・Checks.StageSeven・
既存Spectra.StageTwoの統合ビルドは成功（3290 jobs、終了コード0、警告なし）。
任意A・非有界相手・全次数判定・有限射影対象・ZMod 2を検査した。
主要6宣言の直接公理監査は標準公理のみ。監査累計2354宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。前節の共有olean不在によるexport保留も再試行成功で解消した。
担当差分の空白検査は成功。今回の実装にsorry/admit/新規axiomはない。

次は有限射影複体の主導来像がPerfに入ることと、Perfのretractの有限射影代表を検証する。
今回の射影性だけから主Perfの本質的全射を主張しない。U13e全受入・U13d・U11eのcoherence・
U12e/f・U14〜U17・D4mは未完。採用済み引用は0件。共有ルート・既存PerfectComplex・他系列は変更していない。


### 17.103 U13e16：全Hom同型の境界反映と一対象AのH⁰同値（2026-10-16）

`Functor/HomIso.lean`は各Hom写像がchain isoである実際のdg関手について、閉零関手の完全忠実性、
境界関係の反映、H⁰関手の完全忠実性を証明する。逆chain mapでホモトピーを戻すため、
単なる閉零射の全単射性だけで境界反映を仮定していない。対象・Homの宇宙は独立のまま。
`Module/RingHomotopyComparison.lean`は一対象Aの全Hom評価同型とその逆に適用し、
ringConstantDGとmoduleEvaluationDGのH⁰が実際の圏同値であることを構成した。

Checks.RingHomotopyComparison・Checks.StrictComplexDerived・Checks.StrictComplexProjective・Checks.StageSeven・
既存Spectra.StageTwoの統合ビルドは成功（3296 jobs、終了コード0、警告なし）。
独立対象宇宙の一般判定、任意可換環、一対象Aの双方の同値、A線形H⁰関手、ZMod 2を検査した。
主要13宣言の直接公理監査は標準公理のみ。監査累計2367宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

次はこのH⁰の完全忠実性と主射影的始域の局所化Hom計算を合成する。
U13e全受入・U13d・U11eのcoherence・U12e/f・U14〜U17・D4mは未完。
採用済み引用は0件。共有一般論・共有ルート・既存PerfectComplex・他系列は変更していない。


### 17.104 U13e17：既存PerfectHomotopyから主dg導来圏への線形完全忠実関手（2026-10-16）

`Perfect/StrictComplexDerived.lean`は有限射影複体のdg包含とringConstantDGを合成する。
実際のdg関手のH⁰に、既存moduleHomotopyToDerivedClosedを合成し、指定準同型局所化への比較を構成した。
前節のH⁰の完全忠実性と、有限射影複体を一対象Aの主射影的dg加群へ移す§17.102の証明により、
moduleProjectiveLocalization_map_bijectiveを適用して比較の充満性・忠実性を証明した。

`Perfect/StrictComplexDerivedLinear.lean`はこの比較の加法性・A線形性を公開し、
既存PerfectHomotopyとのH⁰線形同値の逆を合成してperfectHomotopyToDGDerivedを構成する。
これは主dg加群導来圏へのA線形完全忠実関手であり、有限射影dg enhancementを経由する
自然同型strictPerfectDGComplexToPerfectCompDerivedも公開した。
像が主Perfに入ることや主Perfへの本質的全射はまだ主張しない。

Checks.StrictComplexDerived・Checks.RingHomotopyComparison・Checks.StrictComplexProjective・Checks.StageSeven・
既存Spectra.StageTwoの統合ビルドは成功（3296 jobs、終了コード0、警告なし）。
任意可換環、主dg比較と既存PerfectHomotopyの両関手の完全忠実性・A線形性・加法性、ZMod 2を検査した。
主要14宣言の直接公理監査は標準公理のみ。監査累計2381宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

次は像がPerfに入ることとPerfのretractの有限射影代表を証明する。
各次数の有限射影加群の有限自由加群へのretractには既存PerfectComplex.ProjectiveBoundsの
finiteProjective_exists_retractを再利用できることを確認した。ただし有界複体全体の比較や
ホモトピー冪等の分裂は別途必要である。U13e全受入・U13d・U11eのcoherence・U12e/f・
U14〜U17・D4mは未完。採用済み引用は0件。共有系列への追加要求はない。
共有ルート・既存PerfectComplex・共有モデル一般論・他系列は変更していない。


### 17.105 U13e18：全整数次数の有限射影項の主導来perfect性（2026-10-16）

`Perfect/FiniteProjectiveImage.lean`は指定生成集合の主Perfの有限biproduct閉性を、
主Perfの充満部分圏でのbiproductと包含の比較同型を使って証明する。
任意の加法的関手F:ModuleCat A→D(D)について、F(A)が指定Perfに入れば
任意の有限射影加群MのF像も入ることを証明した。有限自由加群へのretractは既存の
PerfectComplex.ProjectiveBounds.finiteProjective_exists_retractを再利用し、
Fの有限biproduct保存と主Perfのretract閉性を適用する。既存PerfectComplexは変更していない。

`Module/RingComplexFunctor.lean`はMathlibの明示的ForgetEnrichment.equivInverseと
既存ringConstantDGの閉零関手を合成し、通常のchain mapから実際の一対象A加群への
加法的関手complexToRingModuleを構成する。対象は元の複体のringModuleそのものである。
`Perfect/RingSingle.lean`は単位複体の定数加群と一対象の代表加群の厳密な一致を証明し、
次数0の有限射影加群の主導来像がperfectとなることを得た。

`Perfect/RingSingleShift.lean`はringModuleの実際のshift対象を厳密な復元で照合し、
sphere nとsphere 0の−n shiftの同型、主局所化のCommShiftを合成する。
これによりringSingleToDerived_finiteProjective_perfectを任意の整数次数nで公開した。
この段階ではshiftの対象同型を使用し、complexToRingModuleのCommShift coherenceを新しく主張しない。

Checks.RingSingle・Checks.StrictComplexDerived・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（3481 jobs、終了コード0、警告なし）。任意可換環、独立対象宇宙・指定S、
有限biproduct、任意加法的関手の有限射影像、全整数次数、ZMod 2の次数−3と2を検査した。
主要15宣言の直接公理監査は標準公理のみ。監査累計2396宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

次は有界有限射影複体全体の導来perfect性を証明する。
既存HomologicalAlgebra.BasicのbottomProjection・bottomProjection_epi・bottomProjectionKernelXIso、
およびPerfectComplex.KoszulLengthBoundsの有限幅帰納法を確認した。
下端項への射影の核の次数範囲と有限射影性を戻し、その短完全列を主導来三角形へ接続する。
Perfのretractの有限射影代表は別の残課題である。U13e全受入・U13d・U11eのcoherence・U12e/f・
U14〜U17・D4mは未完。採用済み引用は0件。共有系列への追加要求はない。
共有ルート・既存PerfectComplex・共有モデル一般論・他系列は変更していない。


### 17.106 U13e19：有界有限射影複体の主Perf像と実際のdg比較（2026-10-16）

`Perfect/RingExtensions.lean`は実際のringConstantDGと評価dg関手の合成比較から、
complexToRingModuleと通常評価との自然同型を構成する。豊穣forgetComp・forgetIdと
明示的ForgetEnrichment.equivのcounitを合成し、大きいHom endの射を直接展開しない。
主導来評価との比較、既存一対象導来同値のunitとの比較を得た。
通常複体の短完全列からの既存DerivedCategory.triangleOfSESを一対象同値の逆で戻し、
主導来像の両端がperfectなら中央もperfectであることを証明する。
比較は任意のHasDerivedCategory.{w}の選択に関して成立する。

`Perfect/RingBounded.lean`は有限の次数幅について帰納する。
既存bottomProjectionの核は下端次数で零、他の次数では元の項と同型であり、
有限射影性と一つ短い次数範囲を保つ。短完全列の両端を帰納仮定と§17.105の次数集中複体で扱う。
strictlyPerfectComplex_ringDerived_perfectにより、既存の任意の有界有限射影複体の
実際の主dg加群導来像がmodulePerfectに入ることを証明した。
証明内でのみHasDerivedCategory.standardを宇宙u+1で選び、結論には新しい選択仮定を残さない。

`Perfect/RingEnhancement.lean`はこのperfect性と既存の全Hom endの射影性を組み合わせ、
strictPerfectDGComplexToPerfectDGを主PerfectDGModule A PUnitへの実際のdg関手として構成する。
各Hom写像は既存のHom評価同型の逆であり、H⁰は完全忠実。
全加群dg圏への包含との可換性はDGFunctor.restrict_comp_inclusionを再利用した実際のdg関手等式である。
まだ主enhancement全体への本質的全射やretractの有限射影代表を主張しない。

Checks.RingEnhancement・Checks.RingSingle・Checks.StrictComplexDerived・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（3490 jobs、終了コード0、警告なし）。任意可換環、有界有限射影複体のperfect性、
実際の主dg対象・Hom写像のIsIso、H⁰の完全忠実性とA線形性、ZMod 2を検査した。
主要11宣言の直接公理監査は標準公理のみ。監査累計2407宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

次は既存PerfectHomotopyから主Perfへの線形完全忠実関手をこのdg比較から公開し、
retractの有限射影代表・本質的全射・shift/三角構造の整合性を完成する。
既存CochainIdempotent.image_strictlyPerfectは厳密なchain idempotentの像について再利用できるが、
ホモトピー冪等の厳密化は未証明であり両者を同一視しない。
U13e全受入・U13d・U11eのcoherence・U12e/f・U14〜U17・D4mは未完。
採用済み引用は0件。共有系列への追加要求はない。共有ルート・既存PerfectComplex・他系列は変更していない。


### 17.107 U13e20：既存PerfectHomotopyから主Perfへの線形完全忠実比較（2026-10-16）

`Perfect/RingPerfectComparison.lean`は実際のstrictPerfectDGComplexToPerfectDGのH⁰と
主射影的enhancementから主Perfへの既存同値を合成し、strictPerfectDGComplexToDGPerfectを構成する。
既存PerfectHomotopyとのH⁰線形同値の逆を合成し、perfectHomotopyToDGPerfectを公開した。
両関手は充満・忠実・加法的・A線形である。

dg包含との関手等式をDGFunctor.onHomotopy_compでH⁰へ送り、主局所化と合成することで、
既存のstrictPerfectDGComplexToDerivedとの自然同型を構成した。
主Perf包含と既存PerfectHomotopyからの主導来比較も
perfectHomotopyToDGPerfectCompInclusionによって自然同型で一致する。
対象ごとのperfect性だけでなく、実際のdg関手に基づく射の比較を保持する。

Checks.RingPerfectComparison・Checks.RingFiniteCell・Checks.RingEnhancement・Checks.StageSeven・
既存Spectra.StageTwoの統合ビルドは成功（3518 jobs、終了コード0、警告なし）。
任意可換環、両比較の完全忠実性・線形性・加法性、主Perf包含との自然同型、ZMod 2を検査した。
主要13宣言の直接公理監査は標準公理のみ。監査累計2420宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

U13e全受入には本質的全射とshift/三角構造・retractの比較が残る。
U13d・U11eのcoherence・U12e/f・U14〜U17・D4mも未完。採用済み引用は0件。
共有系列への追加要求はなく、共有ルート・既存PerfectComplex・他系列は変更していない。


### 17.108 U13e21：一対象Aのfinite cellの有限射影評価とH⁰本質像（2026-10-16）

`Perfect/StrictComplexOperations.lean`は担当範囲に既存strictlyPerfectComplexの補助APIを置く。
真の複体同型・零対象・任意整数次数の有限射影加群のsingleについて条件を保つことを証明する。
各項の線形同型を明示して、評価関手の対象の展開をtypeclass探索へ任せない。
二項直和とconeの閉性は既存PerfectComplexの定理を再利用した。

`Perfect/RingFiniteCell.lean`は一対象Aの実際のModuleFiniteCellCodeの有限操作について帰納する。
代表生成元は単位Aの次数0複体、shift・sum・coneは実際の評価構成であり、
同型操作は通常複体へのmapIsoで運ぶ。任意の指定Sについて
moduleFiniteCell_ringEvaluation_strictlyPerfectを証明した。

`Perfect/RingFiniteCellImage.lean`は主perfect dg対象の実際の加群がfinite cellである場合、
その評価の有限射影複体からringModule_recoverで厳密に復元する。
strictPerfectDGComplexToPerfectDG_essImage_of_finiteCellはH⁰比較の本質像に入ることを証明する。
retractは有限cellの構成木に含まれないため、この証明をPerf全体の本質的全射に拡張していない。

Checks.RingFiniteCell・Checks.RingPerfectComparison・Checks.RingEnhancement・Checks.StageSeven・
既存Spectra.StageTwoの統合ビルドは成功（3518 jobs、終了コード0、警告なし）。
任意可換環・任意指定S、零対象・全整数次数のsingle・有限操作の評価、ZMod 2を検査した。
本質像の定理を含む主要5宣言の直接公理監査は標準公理のみ。監査累計2425宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

次は導来retractを有限射影複体で表す証明と比較のshift/三角整合性を進める。
ホモトピー冪等とstrict chain idempotentを同一視しない。
U13e全受入・U13d・U11eのcoherence・U12e/f・U14〜U17・D4mは未完。
採用済み引用は0件。共有系列への追加要求はなく、共有ルート・既存PerfectComplex・他系列は変更していない。


### 17.109 U13e22：通常複体・一対象加群・導来評価のshift coherence（2026-10-16）

`Perfect/RingShiftComparison.lean`は実際のcomplexToRingModuleEvaluationIsoを
完全忠実なmoduleEvaluationに沿って持ち上げ、complexToRingModuleCommShiftを構成する。
Mathlib CommShift.ofCompの零・加法coherenceとofComp_compatibilityを再利用する。
既存のshift対象同型だけでなく、射に自然な整数shift比較と評価自然同型の整合性を得た。

既存complexToRingModuleDerivedEvaluationIsoの各whiskeringの整合性を明示して、
主導来評価と通常DerivedCategory.Qとの自然同型にもNatTrans.CommShiftを証明した。
既存一対象導来同値のcounit整合性からEquivalence.CommShift.mk''を適用し、
順逆のshiftのunit/counit整合性を公開する。
ringComplexDerivedUnitNatIsoは全複体に自然な逆比較であり、これにもshift整合性を証明した。
任意のHasDerivedCategory.{w}の選択を保持する。

Checks.RingShiftComparison・Checks.RingPerfectComparison・Checks.RingFiniteCell・Checks.StageSeven・
既存Spectra.StageTwoの統合ビルドは成功（3519 jobs、終了コード0、警告なし）。
任意可換環・非有界複体・全整数shift、加法coherence、任意の既存導来圏の宇宙w、ZMod 2を検査した。
主要6宣言の直接公理監査は標準公理のみ。監査累計2431宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

次はこの自然な比較を既存ホモトピー圏・PerfectHomotopyの比較へ降ろして、
主Perfへの実際のdg比較のshift/三角整合性を完成する。
retractの有限射影代表・本質的全射は引き続き残る。
U13e全受入・U13d・U11eのcoherence・U12e/f・U14〜U17・D4mは未完。
採用済み引用は0件。共有系列への追加要求はなく、共有ルート・既存PerfectComplex・他系列は変更していない。


### 17.110 U13e23：実際のPerfectHomotopy比較のshift・三角整合性（2026-10-16）

`Perfect/RingHomotopyDerivedComparison.lean`は閉零圏上の比較を実際の境界商へ降ろす。
complexClosedRingModuleIsoは明示的ForgetEnrichment同値のunitとdg関手で構成する。
主dg関手のH⁰→主局所化という経路と、通常ホモトピー圏→既存Qh→一対象導来同値の逆という経路を、
商への二つの可換四角形・moduleToHomotopyDerivedIso・既存quotientCompQhIsoで照合した。
complexHomotopyRingDerivedIsoは任意のHasDerivedCategory.{w}に自然な比較同型である。

`Perfect/RingPerfectTriangulated.lean`はこれを有限射影dg複体へ制限し、既存PerfectHomotopyとの
H⁰同値のcounitで戻す。strictPerfectDGComplexDerivedCanonicalIsoと
perfectHomotopyToDGDerivedCanonicalIsoを公開した。
後者は元のperfectHomotopyInclusion・既存Qh・一対象導来同値の逆との比較である。
このファイルでは標準の既存導来圏を宇宙u+1で選ぶ。主dg導来圏・主Perfの対象や射のクラスは変えない。

この自然同型でperfectHomotopyToDGDerivedに整数shiftの零・加法coherenceを運び、
比較自然変換のshift整合性とIsTriangulatedを証明した。
主Perf包含の完全忠実性と既存perfectHomotopyToDGPerfectCompInclusionを使って、
実際のperfectHomotopyToDGPerfectのCommShift・包含比較のNatTrans.CommShift・IsTriangulatedも得た。
したがって既存有限射影ホモトピー圏から主PerfへのA線形完全忠実比較は三角関手である。
別の比較関手へ置き換えず、§17.107の実際のdg比較に基づく関手に構造を証明した。

Checks.RingPerfectTriangulated・Checks.RingShiftComparison・Checks.RingPerfectComparison・
Checks.RingFiniteCell・Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功
（3522 jobs、終了コード0、警告なし）。任意可換環、両比較の整数shift・三角性、
包含比較のshift整合性、実際のdistinguished三角形の保存、ZMod 2を検査した。
主要10宣言の直接公理監査は標準公理のみ。監査累計2441宣言。
文書検査は22 Markdown・311 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

U13eの既存PerfectHomotopyとの線形・shift・三角比較は構成できたが、
主Perfへの本質的全射にはホモトピー冪等の分裂・retractの有限射影代表が残る。
U13e全受入・U13d・U11eのcoherence・U12e/f・U14〜U17・D4mは未完。
採用済み引用は0件。共有系列への追加要求はなく、共有ルート・既存PerfectComplex・他系列は変更していない。


### 17.111 U13e24：主Perfの全対象を既存有限射影比較像のretractで表す（2026-10-16）

`Perfect/RingRetract.lean`は一対象Aのfinite cell Mの実際の評価複体から
ringFiniteCellPerfectHomotopyを構成する。有限操作の評価がstrictlyPerfectComplexである
§17.108の証明を、既存perfectHomotopyProperty_quotientへ適用する。
§17.110の自然同型、既存quotientCompQhIso、一対象導来同値のunit比較、ringModule_recoverにより、
この有限射影対象の実際の主導来比較像が元のMの主局所化像と同型であることを証明した。

perfectModule_ring_retract_of_perfectHomotopyは主Perfの任意の対象Xについて、
既存PerfectHomotopyの対象Pと、XからperfectHomotopyToDGPerfect(P)へのretractを与える。
主導来圏内のretractを上の同型で運び、主Perfの充満部分圏の実際の射へ持ち上げる。
この結果はPの上のホモトピー冪等が有限射影複体で分裂することまでは主張しない。

Checks.RingRetract・Checks.RingKaroubi・Checks.RingPerfectTriangulated・Checks.StageSeven・
既存Spectra.StageTwoの統合ビルドは成功（3533 jobs、終了コード0、警告なし）。
任意可換環・任意の主Perf対象のretract表示とZMod 2を検査した。
主要3宣言の直接公理監査は標準公理のみ。監査累計2444宣言。
文書検査は23 Markdown・311 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

次はこのretract表示を共有Karoubi延長の本質像判定へ適用する。
U13e全受入・U13d・U11eのcoherence・U12e/f・U14〜U17・D4mは未完。採用済み引用は0件。
共有系列への追加要求はなく、共有ルート・既存PerfectComplex・他系列は変更していない。


### 17.112 U13e25：既存PerfectHomotopyのKaroubi包絡と主Perfの線形三角同値（2026-10-16）

`Perfect/RingKaroubi.lean`は既存perfectHomotopyToDGPerfectを共有functorExtension₂で延長する。
§17.111のretract表示と、Karoubi対象自身の標準retractを合成し、共有の
karoubiExtension_mem_essImageを適用した。両辺Karoubi包絡の間の延長が
充満・忠実・本質的全射であることを証明した。
共有Karoubi一般論・線形構造・shift/三角構造は再実装していない。

主Perfの既存の冪等完備性を使い、Mathlib functorExtensionで形式的retractを
実際の主Perf対象へ実現するringPerfectKaroubiRealizationを構成した。
実現は同値であり加法的・A線形である。再びtoKaroubiへ入れる自然同型を通じて
整数shiftと整合させ、主PerfのtoKaroubiの完全忠実性で三角性を反映した。
ringPerfectKaroubiEquivalenceはKaroubi(PerfectHomotopy A)と主Perfの実際の線形三角同値。
順逆のA線形性・加法性、shiftの零/加法coherenceと同値のunit/counit整合性を保持する。
元のPerfectHomotopy上では共有karoubiExtensionToCompleteFactorsによる
ringPerfectKaroubiRealization_facで実際の比較関手に自然同型となる。
このfactor自然同型そのもののNatTrans.CommShiftはまだ別途照合する必要がある。

Checks.RingKaroubi・Checks.RingRetract・Checks.RingPerfectTriangulated・Checks.StageSeven・
既存Spectra.StageTwoの統合ビルドは成功（3533 jobs、終了コード0、警告なし）。
任意可換環、実現の同値・完全忠実性、順逆の線形性・加法性、同値のshift/三角性、
元の比較への自然同型、ZMod 2を検査した。
主要25宣言の直接公理監査は標準公理のみ。監査累計2469宣言。
文書検査は23 Markdown・311 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

この同値は元のPerfectHomotopy自身の冪等完備性を証明するものではない。
U13e全受入にはホモトピー冪等の分裂・retractの有限射影代表を残しており、
Karoubiを付けた同値で元の一対象比較の本質的全射を代用しない。
次は元の比較へのfactorのshift整合性と、有限射影代表の構成を進める。
U13d・U11eのcoherence・U12e/f・U14〜U17・D4mも未完。採用済み引用は0件。
共有系列への追加要求はなく、共有ルート・既存PerfectComplex・他系列は変更していない。


### 17.113 U13e26：Karoubi実現のfactor・導来比較・三角形図式のshift整合性（2026-10-16）

`Category/EquivalenceComparison.lean`は同値の逆関手による実現の成分を、unit/counitの
三角恒等式と自然性で比較する。因子化自然同型を順関手で送ると、実現を埋め込みへ戻す比較と
元の延長の比較の合成になることを、任意の圏・関手を抽象的に保って証明した。
実際の大きいKaroubi対象や主dg導来関手の射を成分計算中に展開しない。

`Perfect/RingKaroubiFactors.lean`はこの抽象的な自然変換等式を、§17.112の実際の実現に適用する。
toKaroubiの忠実性に沿ってNatTrans.CommShiftを反映し、
ringPerfectKaroubiRealizationFacCommShiftを証明した。前節で保留したfactor自然同型の
shift整合性はここで解消した。ringPerfectKaroubiRealizationTriangleIsoは
元のPerfectHomotopy上の三角形関手と、Karoubi包含・実現による三角形関手を比較する。
主導来包含を合成するringPerfectKaroubiRealizationDerivedIsoと、そのshift整合性も公開する。

Checks.RingKaroubiFactors・Checks.RingKaroubi・Checks.RingPerfectTriangulated・Checks.StageSeven・
既存Spectra.StageTwoの統合ビルドは成功（3535 jobs、終了コード0、警告なし）。
任意可換環、実際のfactor・主導来比較のNatTrans.CommShift、三角形関手の自然同型、ZMod 2を検査した。
主要7宣言の直接公理監査は標準公理のみ。監査累計2476宣言。
文書検査は24 Markdown・311 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

元のPerfectHomotopy自身の冪等完備性と、一対象比較のKaroubiなしの本質的全射は残る。
U13e全受入・U13d・U11eのcoherence・U12e/f・U14〜U17・D4mは未完。採用済み引用は0件。
U11eの旧ジョブ7882・1019は双方Unknown process idでハンドルの消失を確認した。
旧ログは空で成功とは扱わず、再開時には証明構成を見直して新しい対象ビルドで検証する。
共有系列への追加要求はなく、共有ルート・既存PerfectComplex・他系列は変更していない。


### 17.114 U11e22：反復tensorの全次数作用写像の分離とcochain作用の局所検証（2026-10-16）

U11eの未受入部分へ戻り、左右の結合括弧におけるHom写像とcochain評価を
`Tensor/AssociatorLeftMaps.lean`・`Tensor/AssociatorRightMaps.lean`へ分離した。
左F作用は右B加群のHom endを評価して得る主Hom写像、右B作用は評価右加群の実際の写像である。
各斉次成分が既存の作用cochainに等しいことを証明し、任意整数次数の評価式を公開する。
対象宇宙は独立、B/C/Eはu-small、外側Fのsmall性は要求しない。

`Tensor/AssociatorCochainAction.lean`は左右の括弧付けそれぞれについて、F作用cochainと
右B作用cochainの三重生成元上の計算を独立の定理へ分離した。
F作用はR成分に作用し、B作用はP成分に作用する。後者の符号は左括弧で
(-1)^(p*(k+r))、右括弧で(-1)^(p*l)、l=k+rで一致する。
既存の作用公式と主Hom/cochain評価だけを使い、結合同型の自然性は仮定しない。

検査コストの切り分け：今回のAssociatorBimoduleビルドの左右compatibility検査が
3時間以上CPUを使用中であることをpsで確認し、自分の該当ビルドだけを停止した。
補助宣言までの両prefixは直接Lean検査に成功した。左の型だけの検査も成功。
証明本体の各段階を一時ファイルで計測した結果、すべての段階と最終項の組み立てに到達し、
その後にkernel deterministic timeoutとなることを確認した。
既約性を尊重する設定の別検査は45秒で意図的に停止し、成功とは数えていない。
上の4つのcochain作用定理への分離後は対象ファイルが2秒でビルドできた。
左の最終可換式は短い証明へ変更して検査したが、まだ受入に至らず意図的に停止した。
未受入のcompatibility/naturalityファイルは今回の受入やコミットへ含めない。

Checks.AssociatorMaps・Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功
（2707 jobs、終了コード0、警告なし）。任意可換環・独立対象宇宙・全整数次数のHom/cochain評価、
ZMod 2の次数−1を検査した。主要20宣言の直接公理監査は標準公理のみ。監査累計2496宣言。
全体文書検査は共有PrimeReduction.olean不在で一度停止したが、その再生成を確認後の再試行は
24 Markdown・311 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の受入実装にsorry/admit/新規axiomはない。

次は結合同型の可換式のkernel型照合をさらに分離し、全Homの左右自然性・実際のbimodule同型、
三角・五角coherenceへ進む。U11e全受入は未完。
U13eの元の有限射影代表・本質的全射、U13d・U12e/f・U14〜U17・D4mも未完。採用済み引用は0件。
共有系列への追加要求はなく、共有ルート・既存PerfectComplex・他系列は変更していない。


### 17.115 U15a1：有限path・次数−1記号・内部tensor直和（2026-10-16）

U11eのkernel型照合とU13eのホモトピー冪等の分裂は保持し、§15.5で独立に先行可能とした
U15aを実装した。`Quotient/Paths.lean`はfull部分圏を対象集合S⊆Dとして固定し、
中間対象の有限語Word S=List Sをpath添字とする。空語を許し、各中間対象には
complexSphere A (-1)による収縮記号を一つ置く。
term [] x yは元のHom_D(x,y)、term (b::w) x yは
Hom_D(x,b)⊗(epsilonComplex⊗term w b y)。元のHomの非正性・有界性・flat性は仮定しない。
記号の合計次数epsilonDegree w=−length(w)と、cons/appendに関する公式を証明した。

A:Type u、D:Type v、Homの加群はType u。tensor項はDのsmall性を要求せず定義する。
全path項の直和internalHomにはSmall.{u} Dを用い、Word Sもu-smallであることを証明した。
単一の記号を表すepsilonTermと全直和へのepsilon、空pathのoriginalHomを実際のchain mapで構成した。
ここでの微分は各Homとtensorの内部微分のみである。
dε=idによる長さを下げる微分はまだ追加しておらず、この段階のepsilonを最終dg商の閉じた射とは扱わない。

`Quotient/PathUniversal.lean`は内部微分の直和のdesc・包含との計算式・Hom同値を公開する。
S=∅では語が空に限られることからemptyHomIsoを構成し、元のHom複体と厳密に比較した。
これは後続の最終dg商の普遍性を先取りするものではない。
`Quotient/PathComposition.lean`は内部微分に関して、先頭Homの合成prependMapと
有限pathの連結appendMapを構成した。tensor因子の順を保ち、境界のHomだけをeCompで合成する。
空path同士の連結が主モデルの豊穣合成であることを証明した。
最終微分との両立、単位・結合・dg符号の成分比較はU15bに残す。

Checks.QuotientPaths・Checks.AssociatorMaps・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（2711 jobs、終了コード0、警告なし）。任意可換環・独立対象宇宙、
元の非有界複体圏のHomによるtensor項、u-small語、次数−1/−2、空部分圏のHom同型、
直和の普遍性、空pathの豊穣合成、ZMod 2を検査した。
主要23宣言の直接公理監査は標準公理のみ（公理非依存の宣言も含む）。監査累計2519宣言。
文書検査は24 Markdown・311 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

U15aの有限path添字・空path・tensor項・直和・宇宙の入口を受け入れる。
次はU15bの各ε消去による次数+1の項、内部微分との反交換、全微分の二乗零、
単位・結合・Koszul符号を証明し、実際のdg商を構成する。
U15cの指定収縮データ付き厳密普遍性・U15dの係数変更・U15eのVerdier比較も未完。
U11e全受入・U13eの有限射影代表と本質的全射・U13d・U12e/f・U14・U16/U17・D4mは未完。
採用済み引用は0件。共有系列への追加要求はなく、共有ルート・既存PerfectComplex・他系列は変更していない。


### 17.116 U15b1：全次数tensorによるε消去・任意位置のface・有限消去和（2026-10-16）

`Complexes/TensorRightHom.lean`はsigned symmetryによる共役から右tensorの全次数Hom写像を
構成した。純tensor上で左因子にcochainを作用させる際の追加符号が消えることを証明し、
全Homのchain mapが任意整数次数のcocycleを保つ補題も公開する。
`Quotient/EpsilonDifferential.lean`は次数−1のε複体から単位複体への次数+1のcochainを定義した。
唯一の非零成分・標準生成元の像・内部Hom微分に関する閉性を証明した。
`Quotient/EpsilonTensor.lean`では左・右tensorと中間εの消去を構成し、それぞれの閉性を証明する。
左因子の次数iを通る場合の符号は(-1)^i、右tensorでは追加符号なしである。

`Quotient/ErasureFaces.lean`は先頭εを消して隣接Homを豊穣合成するeraseFirstと、
任意位置のeraseFaceを再帰的に構成した。後方の消去は既存tensorLeftHomを二重に使うため、
先行するHomとεの次数に由来する符号を保持する。各faceが内部微分と反交換することを証明した。
`Quotient/ErasureRows.lean`は各faceを消去後のpathの包含と合成し、pathの有限長にわたって足す。
このeraseRowの閉性、空pathで零、単一記号の場合の公式を証明した。
faceの定義にはSmall Dを要求せず、全path直和を終域とする有限和のみSmall.{u} Dを要求する。
任意可換環・非有界複体・独立対象宇宙の規約を保持する。

Checks.ErasureFaces・Checks.QuotientPaths・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（2651 jobs、終了コード0、警告なし）。任意位置のfaceの型・閉性、
有限消去和の閉性、非有界複体の中間消去、ZMod 2で長さ2のpathを検査した。
主要29宣言のChecks直接実行による公理監査は標準公理のみ。監査累計2548宣言。
文書検査は24 Markdown・311 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

U15b全受入は未完。次は各eraseRowを全直和の次数+1自己cochainへ貼り合わせ、
二つのε消去の相殺と二乗零、元の内部微分との和の二乗零、合成・単位との両立を証明する。
U11e・U12e/f・U13d/e残部・U14・U15c〜e・U16/U17・D4mも未完。
採用済み引用は0件。共有一般論・共有ルートimport・他系列の変更は編集していない。


### 17.117 U15b2：全path直和の消去作用素と二重消去の有限和表示（2026-10-16）

`Quotient/ErasureOperator.lean`は各eraseRowを次数+1のcocycleとして保持し、
MathlibのCocycle.equivHomShiftでshift先へのchain mapへ移す。
その直和descでerasureToShiftを構成し、逆の同値から全path直和の自己cochain erasureを得た。
内部微分との反交換erasure_closedと、各pathへの制限が元の有限和と一致するerasure_precompを
証明した。元のHomを表す空pathへの制限は零である。

erasure_square_precompは、二重消去の各pathへの制限を
「最初のfaceと消去後のpathのeraseRowとの合成」の有限和へ展開する。
長さ0と長さ1のpathについて二重消去が零となる基底例も証明した。
任意長で異なる二つのεを消す際の符号付き相殺は未証明であり、
erasure自体の二乗零、全微分、最終dg商の存在をこの段階で主張しない。
shift先へのchain mapはcocycleの表示に用いるもので、最終dg商の閉零射と混同しない。

Checks.ErasureOperator・Checks.ErasureFaces・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（2652 jobs、終了コード0、警告なし）。独立対象宇宙・任意非有界Hom・
任意位置での制限と閉性、ZMod 2で長さ1の二重消去零を検査した。
主要11宣言の直接公理監査は標準公理のみ。監査累計2559宣言。
文書検査は24 Markdown・311 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

次は任意長のface間の符号付き交換式と有限和の相殺を証明し、erasureの二乗零へ進む。
その後に内部微分との和を最終Hom微分とし、path合成とのLeibniz・単位・結合を検証する。
U15b全受入、U11e・U12e/f・U13d/e残部・U14・U15c〜e・U16/U17・D4mは未完。
採用済み引用は0件。共有一般論・共有ルートimport・他系列は変更していない。


### 17.118 U15b3：後方二重消去の帰納式・添字の対合・二乗零微分の構成（2026-10-16）

`Complexes/TensorCochainComposition.lean`は豊穣合成の保存から通常順cochain合成の保存を
取り出し、共通のKoszul単位スカラーを消して証明した。左tensorが符号付き反交換式を保つ。
`Quotient/ErasureTailComposition.lean`は範囲外のeraseFaceが零であることと、二つの消去位置が
ともに先頭より後の場合の二重消去を短いpathの二重消去へ帰着する式を証明した。
後者は二重のtensorLeftHomが全次数合成を保つことを使い、任意非有界Homを扱う。

`Quotient/ErasureCancellation.lean`は、最初の位置iと消去後の位置jを反対の順序へ移す
swapErasureを定義し、固定点なし・対合・長さnとn−1の有限添字の保存を証明した。
この交換で互いに負となる項の二重和が零であることを、Finset.sum_involutionから証明する。
標数2を除外せず、任意のAddCommGroupに対して成立する。
実際のpathの項が互いに負になるという仮定はこの補題の入力であり、未証明のdg商の性質を
一般論や引用axiomとして導入したものではない。

`Complexes/Perturbation.lean`は次数+1の自己cochain θに対し、δθ=0からdとの反交換を、
θ²=0から成分の合成零を取り出し、d+θの二乗零を証明した。
この二つの証明を受け取って、各次数の加群を保持する非有界複体perturbComplexを構成する。
dg商に適用するには実際のerasureの二乗零を証明する必要があり、条件付きの最終dg商を
受入済みの対象として公開してはいない。

Checks.ErasureCancellation・Checks.ErasureOperator・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（2656 jobs、終了コード0、警告なし）。独立対象宇宙で範囲外face、
任意非有界複体の微分変更、消去順序の具体例、ZMod 2での有限和相殺を検査した。
主要15宣言の直接公理監査は標準公理のみ。監査累計2574宣言。
文書検査は24 Markdown・311 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

次は先頭εを含む二重消去の順序交換式と、eraseFirstの隣接Hom合成との整合性を証明する。
既存の後方帰納式と添字対合により任意長のerasure²=0へ接続し、perturbComplexに適用する。
U15b全受入、U11e・U12e/f・U13d/e残部・U14・U15c〜e・U16/U17・D4mは未完。
採用済み引用は0件。共有一般論・共有ルートimport・他系列は編集していない。


### 17.119 U15b4：全次数tensorの交差符号とε消去・後方cochainの反交換（2026-10-16）

`Complexes/TensorCochainInterchange.lean`は左因子への次数pのcochainと右因子への次数qのcochainの
作用順序を交換すると、(-1)^(pq)が付くことを全整数次数で証明した。
両側を純tensorで評価し、右tensorには追加符号がなく、左tensorの符号が
q*(i+p)とq*iで異なることを用いる。通常順cochain合成についての式であり、
主モデルの豊穣合成の順序・符号を変更しない。次数1同士の反交換を系として公開する。

`Quotient/ErasureInterchange.lean`はこの式を実際のeraseEpsilonに適用し、単位因子を除く前の
ε消去eraseRightTensorと後方の次数+1 cochainの反交換を証明した。
さらに任意非有界複体を左にtensorした式を、§17.118の合成・反交換保存から証明した。
この段階ではunitorによる単位因子の除去と、prependMapによる隣接Hom合成を含む
一般のeraseFirst交換式までは主張していない。

Checks.ErasureInterchange・Checks.ErasureCancellation・Checks.ErasureOperator・Checks.StageSeven・
既存Spectra.StageTwoの統合ビルドは成功（2659 jobs、終了コード0、警告なし）。
任意非有界複体の次数1同士の反交換、ZMod 2での実際のε消去の反交換を検査した。
主要4宣言の直接公理監査は標準公理のみ。監査累計2578宣言。
文書検査は24 Markdown・311 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

次はunitorとの全次数整合性、eraseFirstと後方消去・隣接Hom合成との整合性を証明する。
そこから後方帰納式と有限添字の対合を用いて全erasure²=0を証明し、全微分へ進む。
U15b全受入、U11e・U12e/f・U13d/e残部・U14・U15c〜e・U16/U17・D4mは未完。
採用済み引用は0件。共有一般論・共有ルートimport・他系列は変更していない。


### 17.120 U15b5：unitorの全次数自然性・中間ε消去の反交換・先頭成分式（2026-10-16）

`Complexes/TensorClosedZero.lean`はtensorLeftHomの閉零chain mapへの作用が実際のwhiskerLeftと
一致することを証明した。`Complexes/UnitorCochainNaturality.lean`は逆左unitorの純tensor表示と、
標準単位生成元の除去公式を公開する。その表示から左unitor・逆unitorが任意整数次数のcochainと
可換することを証明し、任意の前方複体をtensorした全次数自然性も証明した。
新しい逆unitorの評価補題はcomplexLeftUnitor_inv_applyとし、既存CategoryTheoryの同名候補と区別する。

`Quotient/ErasureMiddleInterchange.lean`は§17.119の反交換式へ上記unitor自然性を適用し、
単位因子を除いた実際のeraseMiddleと後方の次数+1 cochainの反交換を証明した。
標準ε生成元を含む純tensorを消すと、左因子の次数iに対し(-1)^i倍のtensorになることも証明した。
`Quotient/ErasureFirstEvaluation.lean`はこれを先頭εのeraseFirstへ適用し、
(-1)^i倍のprependMapによる隣接Hom合成となる成分式を証明した。
任意可換環・非有界複体・独立対象宇宙の契約を保持し、これらのface式にSmall Dを要求しない。

Checks.ErasureMiddle・Checks.ErasureInterchange・Checks.ErasureOperator・Checks.StageSeven・
既存Spectra.StageTwoの統合ビルドは成功（2660 jobs、終了コード0、警告なし）。
任意整数次数のunitor自然性、ZMod 2での中間ε消去の反交換を検査した。
主要9宣言を完全修飾名で直接公理監査し、標準公理のみ。監査累計2587宣言。
文書検査は24 Markdown・311 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

次はprependMapの隣接Hom合成と後方消去の整合性を、associatorの全次数自然性と
豊穣合成の結合則に接続し、eraseFirstを含む二重消去の順序交換式を証明する。
後方帰納式・有限添字対合・perturbComplexへの接続はその後であり、全erasure²=0は未証明。
U15b全受入、U11e・U12e/f・U13d/e残部・U14・U15c〜e・U16/U17・D4mは未完。
採用済み引用は0件。共有一般論・共有ルートimport・他系列は編集していない。


### 17.121 U15b6：associatorの全次数自然性と先頭Hom合成の後方自然性（2026-10-16）

`Complexes/AssociatorCochainNaturality.lean`はassociatorと逆associatorが、第三因子の
任意整数次数cochainと可換することを証明した。純tensor上の符号はp*(i+j)=p*i+p*jで照合する。
左因子のchain mapに関する既存全Hom自然性をcochainの式として取り出す補題も公開した。
両者から、前方二因子を任意のchain map c:U⊗V→Wで合成し括弧を変更する操作が、
残る右因子の全次数cochainと可換するtensorJoin_cochain_naturalityを証明した。

`Quotient/PrependTailNaturality.lean`はcを元のdg圏のeCompに特殊化し、先頭の中間対象を
保ったまま後方のtensor部分に任意次数cochainを作用させる場合のprependMapの自然性を証明した。
`Quotient/ErasureFaceEquations.lean`はeraseFaceのcons/succの再帰を一段だけ公開する。
後方の再帰呼出しを展開せずに使える等式であり、既存eraseFaceの定義は変更していない。
任意可換環・非有界Hom・独立対象宇宙を保持し、Small Dやflatnessは不要。

Checks.PrependTail・Checks.ErasureMiddle・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（2660 jobs、終了コード0、警告なし）。ZMod 2を含む任意整数次数で
associatorとcochainの可換式を検査した。主要6宣言の直接公理監査は標準公理のみ。
監査累計2593宣言。文書検査は24 Markdown・311 exposition参照、失敗0件。
担当差分の空白検査は成功。今回の実装にsorry/admit/新規axiomはない。

**未受入の適用草稿**：`Quotient/PrependErasureNaturality.lean`の実際のeraseFaceへの特殊化と、
`Quotient/ErasureFirstTailInterchange.lean`の先頭ε・非隣接後方εの反交換は未検証であり、
受入入口にimportしない。前者は一段の再帰式・型付き局所cochain・局所irreducible属性で
展開を限定しても、カーネルのwhnfで200000 heartbeatの上限に達した。
400000でも同じ箇所で上限に達したため、予算拡大は継続せず、標準設定の草稿を残す。
これらの失敗ジョブはすべて終了コード1であり、成功・実行中とは扱わない。

次はεを保持した後方cochainの適用をさらに抽象化するか、全Homのchain map等式として
自然性を先に構成し、実際のfaceへの適用時の型照合を小さくする。
その後、先頭εと非隣接消去の交換式、隣接εについての豊穣合成の結合則へ進む。
全erasure²=0、全微分、U15b全受入は依然未完。
U11e・U12e/f・U13d/e残部・U14・U15c〜e・U16/U17・D4mも未完。採用済み引用は0件。
共有一般論・共有ルートimport・他系列は編集していない。


### 17.122 U15b7：全Hom写像による型照合の解消と先頭・非隣接εの反交換（2026-10-16）

§17.121の適用草稿2件の型照合を解消した。
`Complexes/TensorJoinHomNaturality.lean`は、任意の複体間のchain map c:U⊗V→Wについて、
前方二因子の合成と後方tensor作用の可換式を全Homのchain map等式として証明する。
`Quotient/PrependHomNaturality.lean`はこれを元のdg圏のeCompへ特殊化し、
pathの型を保持するprependMap_tail_homを構成した。さらにεを保持するtensor写像を
先に合成したprependMap_suffix_homを公開した。
pathの型を含むHom等式を最初から直接証明する草稿は200000 heartbeatで失敗したが、
任意の複体上の補題を経由する形では同じ標準設定で通る。予算上限の増大は採用していない。

`Quotient/PrependErasureNaturality.lean`は全Hom等式へ実際のeraseFaceを代入し、
prependMapと先頭より後のeraseFaceの可換式を証明した。
`Quotient/ErasureFirstTailInterchange.lean`はこれと§17.120の中間消去の反交換を接続し、
先頭εと非隣接の後方εを消す順序の交換で負号が付くことを証明した。
これで上記2ファイルは未受入草稿から受入済みに移る。
隣接する二つのεの場合は、隣接Hom合成の結合則を用いる別の証明が必要であり、
全erasure²=0はまだ主張しない。任意可換環・非有界Hom・独立対象宇宙を保持し、Small Dは不要。

Checks.ErasureFirstTail・Checks.PrependTail・Checks.ErasureMiddle・Checks.StageSeven・
既存Spectra.StageTwoの統合ビルドは成功（2665 jobs、終了コード0、警告なし）。
任意dg圏・任意長path・任意の後方位置で先頭との非隣接反交換、ZMod 2の長さ3の例を検査した。
主要5宣言の直接公理監査は標準公理のみ。監査累計2598宣言。
文書検査は24 Markdown・311 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

次はprependMapの結合則と中間ε消去の括弧変更との整合性を証明し、隣接するεの二重消去を扱う。
その後、後方帰納式と有限添字の対合へ接続して全erasure²=0と全微分を構成する。
U15b全受入、U11e・U12e/f・U13d/e残部・U14・U15c〜e・U16/U17・D4mは未完。
採用済み引用は0件。共有一般論・共有ルートimport・他系列は編集していない。


### 17.123 U15b8：先頭Hom結合則・隣接εの反交換・先頭と任意位置の統一（2026-10-16）

`Complexes/TensorJoinAssociativity.lean`は、前方三因子の二通りの合成が一致するとき、
任意の右因子を残した括弧変更付き合成も一致することを証明した。
使用する構造射の等式はMathlibのmonoidal coherence、残る自然性は既存associator自然性から得る。
`Quotient/PrependAssociativity.lean`はこれと元のdg圏のe_assoc'を用い、任意長pathについて
二つの元のHomを先に合成する場合と、pathへ順に合成する場合の一致prependMap_assocを証明した。

`Quotient/ErasureHead.lean`は左端εを消して単位因子も除くeraseHeadとその閉性を構成する。
中間ε消去がeraseHeadの左tensorであることを証明し、tensorJoinの全次数自然性を使って
前方二因子の合成と中間ε消去の可換式を得た。
`Quotient/PrependFirstNaturality.lean`はこれをprependMap_assocへ接続し、最初のεの消去と
prependMapの可換式prependMap_eraseFirstを証明した。最終の等式適用では中間cochainの型を
明示し、カーネルの大きな型比較を避けて標準heartbeat設定で検証した。

`Quotient/ErasureAdjacentInterchange.lean`はprependMap_eraseFirstと中間消去の反交換から、
先頭の隣接する二つのεの二重消去が反交換することを証明した。
さらに§17.122の非隣接の場合と合わせ、先頭εと任意の後方位置の消去の反交換を
一つのeraseFirst_face_anticommuteへ統合した。空path・範囲外の位置も零として含む。
任意可換環・非有界Hom・独立対象宇宙を保持し、Small Dを要求しない。

Checks.ErasureAdjacent・Checks.ErasureFirstTail・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（2668 jobs、終了コード0、警告なし）。任意dg圏の先頭と任意後方位置の
反交換、ZMod 2の長さ2の隣接消去を検査した。
主要10宣言の直接公理監査は標準公理のみ。監査累計2608宣言。
文書検査は24 Markdown・311 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

次は二回消去後の語の同一視を明示し、先頭位置の反交換を後方二重消去の帰納式へ運ぶ。
一般の二位置の項を全path直和への包含後に比較し、swapErasureによる有限和相殺から
全erasure²=0へ進む。その後perturbComplexを適用し、最終Hom微分と合成のLeibnizを検証する。
全erasure²=0・全微分・U15b全受入は未完。
U11e・U12e/f・U13d/e残部・U14・U15c〜e・U16/U17・D4mも未完。採用済み引用は0件。
共有一般論・共有ルートimport・他系列は編集していない。


### 17.124 U15b9：依存対による二位置の反交換・実際の有限和相殺・全消去作用素の二乗零（2026-10-16）

`Quotient/DoubleFaces.lean`は二重消去の終域の語と次数2 cochainをDoubleFaceという依存対で保持する。
前方Homとεを残すprefixDoubleFace、負号の保存、後方二重消去と先頭消去の帰納式を構成した。
先頭の場合の反交換を後方へ帰納的に運び、i≤jについて「先にi、次にjを消す」と
「先にj+1、次にiを消す」の反交換を、終域の語も含めた依存対の等式として証明した。
終域の複体を曖昧に同一視せず、語の一致をこの等式の第一成分として保持する。

`Quotient/DoubleFaceSum.lean`は二重消去を対応するpathの包含と合成し、共通の全path直和を
終域とするerasurePairを構成した。swapErasureが実際の項を負にすることと、
長さnとn−1の範囲の実際の有限二重和が零であることを証明した。
`Quotient/PathCochainExt.lean`は複体の各次数の余積普遍性から、閉性を仮定しない任意次数の
cochainをpath包含への制限で判定する補題を構成した。
`Quotient/ErasureSquare.lean`は作用素の二乗を各pathへ制限し、実際の二重消去項の有限和へ
展開する。最初の消去が有効な範囲で消去後の語の長さがn−1となることを使い、有限和相殺と
上記extから全erasure²=0を証明した。この二乗零を外部仮定や引用として置いてはいない。
任意可換環・非有界Hom・独立対象宇宙を保持し、直和を使う部分のみSmall.{u} Dを要求する。

Checks.ErasureSquare・Checks.ErasureAdjacent・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（2676 jobs、終了コード0、警告なし）。任意の二位置の依存対等式、
任意dg圏での全消去作用素二乗零、ZMod 2で全pathを含む作用素の二乗零を検査した。
主要18宣言の直接公理監査は標準公理のみ。監査累計2626宣言。
文書検査は24 Markdown・311 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

次は証明済みの内部微分との反交換と全erasure²=0をperturbComplexへ適用し、
最終Hom複体・元のHomのchain mapとしての包含を構成する。
最終微分とpath合成のLeibniz、単位・結合・収縮方程式の検証は残るためU15b全受入は未完。
U11e・U12e/f・U13d/e残部・U14・U15c〜e・U16/U17・D4mも未完。採用済み引用は0件。
共有一般論・共有ルートimport・他系列は編集していない。


### 17.125 U15b10：最終Hom微分・元のHomの包含・空部分圏比較（2026-10-16）

`Quotient/Differential.lean`は、証明済みのerasure_closedとerasure_square_zeroを
perturbComplexへ適用し、quotientHomを構成した。
対象の各次数は内部path直和と同じであり、微分は内部微分とε消去作用素の和である。
二乗零は条件を外部から受け取らず、§17.124までの実際の消去作用素の証明から得る。
任意可換環・非有界Hom・独立対象宇宙とSmall.{u} Dを維持し、Homのflat性は仮定しない。

空path上の消去作用素が零となることから、元のHomの包含を最終微分に関する実際のchain map
originalHomInclusionとして構成した。各次数の射は元のpath包含と同じである。
空部分圏では全消去作用素が零であることをpathCochain_extから証明し、内部微分のemptyHomIsoを
同じ次数別同型で移してquotientHom_emptyIsoを構成した。その順方向が上記包含に一致することも
証明した。これは最終Hom複体に関する比較であり、まだ最終dg圏の同型を主張するものではない。

Checks.QuotientDifferential・Checks.ErasureSquare・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（2678 jobs、終了コード0、警告なし）。最終微分の公式、元のHomの包含、
空部分圏との複体同型、ZMod 2での最終微分の二乗零を検査した。
主要8宣言の直接公理監査は標準公理のみ。監査累計2634宣言。
文書検査は24 Markdown・311 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

次はpath連結についてε消去のLeibniz則を証明し、内部微分との既存両立式へ加えて
quotientHom上の豊穣合成を構成する。単位・結合・通常順dg合成とのKoszul符号比較、
指定εの収縮方程式も必要であり、U15b全受入や最終dg商の完成とはまだ扱わない。
U11e・U12e/f・U13d/e残部・U14・U15c〜e・U16/U17・D4mも未完。採用済み引用は0件。
共有一般論・共有ルートimport・他系列は編集していない。


### 17.126 U15b11：全path直和の内部合成・包含上の成分式・左単位（2026-10-16）

`Complexes/TensorCoproduct.lean`は指定した二つの複体余積のtensorからの普遍写像を構成した。
左tensorの余積保存は既存閉構造、右tensorの保存は既存tensorRightHomAdjunctionから得る。
片側のdescと包含上の公式、両側のdescと各二因子上の公式、二因子への制限によるhom_extを
公開する。添字は独立のType v/Type wで、各余積の存在を明示的に仮定し、宇宙を不当に縮小しない。
一般モデル圏・転送・SM7は使用も再実装もしていない。

`Quotient/InternalComposition.lean`は有限path連結appendMapをこの普遍性へ適用し、
内部微分を持つ全path Hom直和のchain map internalCompositionを構成した。
二つのpath包含への制限はappendMapの後に連結語の包含を合成したものに一致する。
空pathを左に置く公式、空path同士では元のeCompとなる公式、任意整数次数の純tensor上の
成分式、二つのpathへの制限によるhom_extを証明した。
ここでのchain mapは内部微分に関するもので、quotientHomの最終微分との両立は未証明である。

`Complexes/TensorJoinUnit.lean`は前方Hom合成の左単位則が右tensor因子を残しても保たれることを、
unitor/associatorの自然性とMathlib monoidal coherenceから証明した。
`Quotient/PrependUnit.lean`は任意長pathのprependMapの左単位則を元のdg圏のe_id_compから得る。
`Quotient/InternalUnit.lean`は元の単位を空pathへ入れたinternalIdentityを構成し、
各pathへの制限、tensorの交換式、上記prependMapの単位則からinternalCompositionの左単位を証明した。
任意可換環・非有界Hom・独立対象宇宙を保持し、全path直和にはSmall.{u} Dを要求する。

Checks.InternalComposition・Checks.QuotientDifferential・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（2683 jobs、終了コード0、警告なし）。元の豊穣合成との空path比較、
全path直和の左単位、ZMod 2での負/正次数の純tensor成分式を検査した。
主要18宣言の直接公理監査は標準公理のみ。監査累計2652宣言。
文書検査は24 Markdown・311 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

次はappendMapとε消去のLeibniz則を各有限path上で証明し、直和へ移してinternalCompositionと
最終Hom微分との両立へ接続する。先頭Homの作用についてはprependMap_eraseFirstと
prependMap_eraseFace_succを統合し、長いpathはappendMapの再帰式で処理する。
右単位・結合、最終Hom上の単位、収縮方程式と通常順dg合成の符号比較も残る。
内部合成の構成だけでU15bや最終dg商の完成とはしない。
U11e・U12e/f・U13d/e残部・U14・U15c〜e・U16/U17・D4mも未完。採用済み引用は0件。
共有一般論・共有ルートimport・他系列は編集していない。


### 17.127 U15b12：先頭Hom作用と全消去作用素のLeibniz基底式（2026-10-16）

`Quotient/PrependErasureRows.lean`はprependMap_eraseFirstとprependMap_eraseFace_succを統合し、
任意位置のε消去と先頭Hom合成の可換式prependMap_eraseFaceを証明した。空語・範囲外の位置も含む。
全path合成へ元のHomの空path包含を前合成したinternalPrependと、path包含上の計算式を構成する。
各消去項を消去後のpath包含へ送ったeraseSummandの可換式を証明し、加法準同型で有限和を移して
eraseRowの可換式へ拡張した。

`Quotient/TensorPathCochainExt.lean`は左tensorがpath直和を保存するcofanと次数別評価の余積保存から、
左tensorした全path直和の任意次数cochainを各pathへの制限で判定する補題を構成した。
`Quotient/PrependErasure.lean`はそのext、eraseRowの可換式、作用素のpathへの制限公式から、
internalPrependと全erasureの可換式を証明した。これは空pathを左に置く合成のε消去Leibniz基底式であり、
左の元のHomには消去項がない。斉次成分では右の消去に(-1)^pが付くことも全整数次数で証明した。
任意可換環・非有界Hom・独立対象宇宙を保持し、全path直和にはSmall.{u} Dを要求する。

Checks.PrependErasure・Checks.QuotientDifferential・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（2683 jobs、終了コード0、警告なし）。任意dg圏の全消去作用素との可換式と、
ZMod 2での全path先頭作用の型を検査した。
主要8宣言の直接公理監査は標準公理のみ。監査累計2660宣言。
文書検査は24 Markdown・311 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

次はこの基底式とinternalPrependのchain map条件を加え、元のHomとquotientHomのtensorから
quotientHomへの最終微分に関する先頭作用を構成する。一般の二つのpathについてはappendMapの
再帰と各側のε消去に分けたLeibniz則がなお必要である。
右単位・結合・収縮方程式も残り、U15b全受入や最終dg商の完成とは扱わない。
U11e・U12e/f・U13d/e残部・U14・U15c〜e・U16/U17・D4mも未完。採用済み引用は0件。
共有一般論・共有ルートimport・他系列は編集していない。


### 17.128 U15b13：最終Hom微分に関する先頭Hom作用（2026-10-16）

`Quotient/PrependDifferential.lean`はinternalPrependの内部chain map条件を斉次純tensorで評価し、
§17.127の消去Leibniz基底式を足し合わせた。得られるinternalPrepend_total_d_applyは、
左の元のHomの微分と、右のquotientHomの最終微分についてのLeibniz則を、全整数次数で与える。
右側の項には(-1)^pが付く。内部Homと最終Homは各次数の加群が同じであることを使うが、
異なる微分を持つ複体をchain mapとして無条件に同一視しない。

この成分式を既存tensorLiftへ渡し、実際のchain map
quotientPrepend : Hom_D(x,y)⊗quotientHom(S,y,z)→quotientHom(S,x,z)を構成した。
quotientPrepend_ιは各二次数のtensor包含への制限が従来の内部作用の成分と一致することを証明する。
これは左に空pathを置く合成の最終微分への移行である。
任意可換環・非有界Hom・独立対象宇宙・Small.{u} Dを保持し、flatnessやモデル構造の仮定は不要。

Checks.PrependDifferential・Checks.PrependErasure・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（2684 jobs、終了コード0、警告なし）。任意dg圏での最終微分のchain mapの型、
全整数次数のtensor包含上の成分式、ZMod 2での最終先頭作用を検査した。
主要3宣言の直接公理監査は標準公理のみ。監査累計2663宣言。
文書検査は24 Markdown・311 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

次は非空の左pathについて、ε消去和を先頭消去と後方消去に分ける再帰式を用い、
appendMapの再帰へLeibniz基底式を運ぶ。一般の二つのquotientHomのtensorからの最終合成は未構成。
その単位・結合・収縮方程式と通常順の合成符号の検証も残り、U15b全受入とはしない。
U11e・U12e/f・U13d/e残部・U14・U15c〜e・U16/U17・D4mも未完。採用済み引用は0件。
共有一般論・共有ルートimport・他系列は編集していない。


### 17.129 U15b14：非空path消去和と全消去作用素の前方因子再帰（2026-10-16）

`Quotient/PathPrefix.lean`は先頭Homとεを保持するtensor functorの合成がpath直和を保存する
cofanを構成した。その普遍性から前方Homとεを追加する内部chain map prefixPathと、
各path包含への制限公式を構成する。このtensor直和を始域とする任意次数cochainのextも公開する。

`Quotient/ErasureRowRecursion.lean`は後方cochainを二重tensorしてprefixPathへ送る
prefixTailCochainを、元の非空pathを始域とする型を明示して構成した。
後方の各eraseSummandが短いpathの消去項の持ち上げであること、非空pathのeraseRowが
「先頭εの消去」と「先頭を保持する後方の消去和」の和になることを証明した。
加法は同じ始域を持つcochainの型で取っており、定義的に等しい複体の別表記による
加法インスタンスの不一致を回避している。

`Quotient/ErasureHeadNaturality.lean`は左端と中間のε消去が右因子のchain mapと可換することを、
全次数tensorの交差式の次数1/0の場合とunitor自然性から証明した。
`Quotient/PrefixErasure.lean`はこれらを各pathの包含に制限して比較し、prefixPath後の全erasureを
先頭ε消去＋後方全消去の二項へ分けるprefixPath_erasureを証明した。
prefixPathが最終微分に関するchain mapであるとは主張しない。先頭εを消す第一項が
内部微分だけの場合からの差を表す。任意可換環・非有界Hom・独立対象宇宙・Small.{u} Dを保持する。

Checks.ErasureRowRecursion・Checks.PrependDifferential・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（2688 jobs、終了コード0、警告なし）。非空pathの消去和の型付き分解、
ZMod 2での前方追加、主要宣言の全作用素再帰式を検査した。
主要10宣言の直接公理監査は標準公理のみ。監査累計2673宣言。
文書検査は24 Markdown・311 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

次は左有限pathを固定した全pathへの連結を構成し、その空語・cons再帰をprefixPathと整合させる。
これらとprefixPath_erasureを使って、非空の左pathへ最終微分のLeibniz則を帰納的に運ぶ。
一般の最終Hom間の合成、単位・結合・収縮方程式は未完で、U15b全受入とはしない。
U11e・U12e/f・U13d/e残部・U14・U15c〜e・U16/U17・D4mも未完。採用済み引用は0件。
共有一般論・共有ルートimport・他系列は編集していない。


### 17.130 U15b15：左有限pathを固定した連結と空語・非空語再帰（2026-10-17）

`Quotient/AppendRight.lean`は左の有限path wを固定した内部chain map
appendRight : term(w,x,y)⊗internalHom(S,y,z)→internalHom(S,x,z)を右直和の普遍性で構成した。
各右path vへの制限はappendMap w vの後に連結語w++vの包含を合成したものに一致する。
全internalCompositionへ左path包含を前合成した場合とも一致することを証明した。
左の語が空の場合は、既存のinternalPrependと同じchain mapに戻る。

非空の左語b::wの場合のappendRight_consを証明した。
二度のassociatorによって右path直和を後方へ移し、短い左語wのappendRightをεと先頭Homで
tensorした後、prefixPathを合成した写像に一致する。
証明は各右pathへの制限、associatorの右因子に関する自然性、appendMapの再帰、
prefixPathの包含公式を用いる。余積cofanの射とpath包含の別表記は明示的に正規化する。
任意可換環・非有界Hom・独立対象宇宙・Small.{u} Dを保持する。

Checks.AppendRight・Checks.ErasureRowRecursion・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（2679 jobs、終了コード0、警告なし）。任意の左右pathへの連結公式、
空の左語との比較、ZMod 2で非空左pathから全右pathへの連結を検査した。
主要5宣言の直接公理監査は標準公理のみ。監査累計2678宣言。
文書検査は23 Markdown・311 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

次はこのcons再帰を全internalCompositionとprefixPathの可換図式へ拡張する。
その図式とprefixPath_erasureを用い、左語の長さに関する帰納で両側のε消去項を比較し、
一般の二つのpathのLeibniz則と最終Hom間の合成へ接続する。
ここでのappendRightは内部微分に関するchain mapであり、最終微分の合成とは扱わない。
単位・結合・収縮方程式も残り、U15b全受入は未完。
U11e・U12e/f・U13d/e残部・U14・U15c〜e・U16/U17・D4mも未完。採用済み引用は0件。
共有一般論・共有ルートimport・他系列は編集していない。


### 17.131 U15b16：先頭Hom作用と有限・全path連結の結合図式（2026-10-17）

`Complexes/TensorJoinRightAction.lean`は前方二因子の合成と後方二因子への任意のchain map作用の
交換図式を証明した。構造射の等式はMathlib monoidal coherence、残る部分はassociator自然性と
tensorの交換則から得る。
`Quotient/AppendPrepend.lean`はこれを元のdg圏の豊穣合成へ特殊化し、有限pathについて
prependMapの作用とappendMapの連結の結合則appendMap_prependを証明した。
左語が空の場合は既存prependMap_assoc、非空の場合は上記一般図式を用いる。

`Complexes/TensorCoproductExt.lean`は一つ又は二つの固定左tensor因子と固定右tensor因子を持つ
指定余積について、包含上の制限からchain mapの等式を判定する補題を構成した。
`Quotient/AppendRightPrepend.lean`は有限pathの図式を全右pathの余積へ拡張する。
`Quotient/CompositionPrepend.lean`はさらに左の全path直和へ拡張し、
internalPrependとinternalCompositionの結合図式internalComposition_prependを証明した。
任意可換環・非有界Hom・独立対象宇宙を保持し、全path直和にはSmall.{u} Dを要求する。
これらは内部微分に関するchain mapの等式であり、最終微分の一般合成の完成とは扱わない。

Checks.CompositionPrepend・Checks.AppendRight・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（2677 jobs、終了コード0、警告なし）。任意dg圏の全path図式、
ZMod 2で指定部分圏にわたる全path図式を検査した。
主要6宣言の直接公理監査は標準公理のみ。監査累計2684宣言。
文書検査は23 Markdown・320 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

先頭Homとεを同時に追加する図式の`Quotient/CompositionPrefix.lean`は別の未受入草稿である。
直接の余積保存と、任意複体の余積判定へ分離した形の両方で、カーネルのdeterministic timeoutを
検出した。前者・後者の失敗ジョブはともに終了コード1を確認済み。
各path上の左右・中間・外側の比較を独立補題に分けた検査を進めており、未検証の図式を
受入入口にはimportしていない。予算上限の増大や引用による置換は採用していない。

次はこの先頭追加図式のカーネル型照合を小さくし、prefixPath_erasureと今回の
internalComposition_prependを合わせ、非空左pathのLeibniz則へ運ぶ。
一般の最終Hom間の合成、単位・結合・収縮方程式、U15b全受入は未完。
U11e・U12e/f・U13d/e残部・U14・U15c〜e・U16/U17・D4mも未完。採用済み引用は0件。
共有一般論・共有ルートimport・他系列は編集していない。


### 17.132 U15b17：先頭Hom・ε追加と全path合成の図式、カーネル検査の解消（2026-10-17）

§17.131の未受入草稿`Quotient/CompositionPrefix.lean`を検証済みに移した。
各path上で、左側の先頭追加後の合成、中間associator、外側associatorの比較を独立した補題に分けた。
それらをappendRight_consへ接続するcomposition_prefix_restrictを構成し、
固定左右tensor因子を持つ余積のhom_extから全path図式internalComposition_prefixPathを証明した。
先頭Homとεを追加してから全path合成を行う場合と、後方の二つのHomを先に合成してから
同じ先頭を追加する場合が一致する。

分割後も比較式のEq.transでカーネルのdeterministic timeoutを検出したが、
比較式をつなぐ前にCategory.assocで合成の括弧を正規化することで解消した。
大きな複体射の合成の結合を定義的な簡約に任せず、明示した結合則の証明を使う。
標準設定で対象ビルドは4.4秒で成功し、heartbeat等の上限拡大は採用していない。
任意可換環・非有界Hom・独立対象宇宙・Small.{u} Dを保持する。
この図式は内部微分についてのもので、一般の最終微分のLeibniz則はまだ主張しない。

Checks.CompositionPrefix・Checks.CompositionPrepend・Checks.ErasureRowRecursion・Checks.StageSeven・
既存Spectra.StageTwoの統合ビルドは成功（2686 jobs、終了コード0、警告なし）。
任意dg圏の全path図式、ZMod 2で前方εを含む全path図式を検査した。
主要5宣言の直接公理監査は標準公理のみ。監査累計2689宣言。
文書検査は13 Markdown・320 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

次は各左語wについて、appendRight後の消去作用素を「左語のeraseRow」と「右の全erasure」の
二項へ分ける式を帰納的に証明する。空語では§17.127の基底式、非空語では
prefixPath_erasure・今回の図式・internalComposition_prependを用いる。
cochain合成の等式も、推移的に結ぶ前に括弧を明示して型照合の負荷を抑える。
一般の最終Hom間の合成、単位・結合・収縮方程式、U15b全受入は未完。
U11e・U12e/f・U13d/e残部・U14・U15c〜e・U16/U17・D4mも未完。採用済み引用は0件。
共有一般論・共有ルートimport・他系列は編集していない。


### 17.133 U15b18：右tensor合成保存・associator全次数自然性・ε消去との整合（2026-10-17）

`Complexes/TensorRightComposition.lean`は右tensorの任意整数次数の通常順cochain合成保存と
閉零chain mapとの一致を証明する。純tensorの成分比較では前合成を含む射の等式を
両辺ともcochain評価へ明示的に戻し、射の合成を元への作用へ移して検証した。
`Complexes/AssociatorCochainFactors.lean`は三重tensorの任意cochainのextと、
associatorの左・中間因子に関する全次数自然性を証明する。
中間因子の符号は左因子の次数iに対して(-1)^(p*i)となり、両辺で一致する。

`Quotient/ErasureTensorRight.lean`はこれらをeraseEpsilonへ適用し、eraseHeadの右tensor保存と、
eraseMiddleの二段階associatorを通じた整合式を証明する。
非空左pathの先頭εを消す項を、右の全pathを保ったまま移動するための補題である。
任意可換環・非有界・全整数次数の契約を維持し、特性2を除外しない。

Checks.TensorCochainFactors・Checks.ErasureTensorRight・Checks.CompositionPrefix・Checks.StageSeven・
既存Spectra.StageTwoの統合ビルドは成功（2679 jobs、終了コード0、警告なし）。
次数−1と+1の合成、およびZMod 2での中間因子自然性の受入例を検査した。
主要8宣言の直接公理監査は標準公理のみ。監査累計2697宣言。
文書検査は13 Markdown・320 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

次は固定前方Hom・εの括弧変更と後方cochainの自然性をつなぎ、appendRightの非空語帰納式で
先頭ε項・左語後方項・右語項の三項を識別する。
一般の最終Hom間の合成、単位・結合・収縮方程式、U15b全受入は未完。
U11e・U12e/f・U13d/e残部・U14・U15c〜e・U16/U17・D4mも未完。採用済み引用は0件。
共有一般論・共有ルートimport・他系列は編集していない。


### 17.134 U15b19：任意左path・全pathの消去Leibniz則と最終Hom間の合成（2026-10-17）

`Complexes/PrefixTensorCochain.lean`は固定前方二因子を持つ括弧変更と、後方・右因子の
任意次数cochainの自然性を証明する。`Quotient/ErasureTensorTransport.lean`は後方chain mapを
含む先頭ε消去の移送式を与え、`AppendErasureHead.lean`はこれをappendRightへ適用する。
`AppendLiftCochain.lean`は短い左語の連結cochainへ前方Homとεを戻す加法的な操作と、
左語後方項・右語項の移送式を公開する。大きなcochain合成は括弧を正規化してからつなぎ、
未展開のterm(b::w)が残る型照合はterm_consで明示的に揃えた。

`AppendErasureRecursion.lean`は非空左語の消去を「先頭ε」と「短い語の式の持ち上げ」に分解する。
`AppendErasure.lean`は左語の長さに関する帰納法により、任意の左pathについて左右の消去の
Leibniz則appendRight_erasureを証明する。
`TensorRightPathCochainExt.lean`は右tensorした全path直和の任意次数cochainのextを与える。
`CompositionErasure.lean`は各左pathへの制限から、全path合成に対する
internalComposition_erasureを証明する。右消去項のKoszul符号はtensorLeftHomから得る。

`CompositionDifferential.lean`はその成分式internalComposition_erasure_applyと内部微分の
chain map条件を加え、最終微分についてのinternalComposition_total_d_applyを証明する。
その結果、quotientComposition : quotientHom S x y ⊗ quotientHom S y z → quotientHom S x z
をtensorLiftにより実際のchain mapとして構成した。quotientComposition_ιは全次数のtensor成分が
既存internalCompositionの成分そのものであることを保証する。
任意可換環・非有界・独立対象宇宙・Small.{u} Dを維持する。

Checks.AppendErasure・Checks.CompositionDifferential・Checks.TensorCochainFactors・
Checks.ErasureTensorRight・Checks.CompositionPrefix・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（2708 jobs、終了コード0、警告なし）。
任意pathの式、次数−1と+1から次数0への合成成分、ZMod 2での最終Hom間合成を検査した。
主要16宣言の直接公理監査は標準公理のみ。監査累計2713宣言。
文書検査は13 Markdown・320 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

次は最終Homの単位を元のHomの包含から構成し、左右単位・全path合成の結合則を証明する。
さらに指定次数−1のεについて最終微分が恒等射となること、通常順と豊穣順の成分符号を照合する。
最終合成のchain map構成だけでU15b全受入や最終dg商の完成とは扱わない。
U11e・U12e/f・U13d/e残部・U14・U15c〜e・U16/U17・D4mは未完。採用済み引用は0件。
共有一般論・共有ルートimport・他系列は編集していない。


### 17.135 U15b20：最終合成の成分・元のHom包含の合成保存・恒等射と左単位（2026-10-17）

`Quotient/CompositionComparison.lean`はquotientCompositionの各次数の射が内部合成の射に
一致することを証明する。元のHomの包含について、最終合成との可換式
quotientComposition_originalを公開した。これは実際のchain mapの等式である。
`Quotient/Identity.lean`は元のdg圏のeIdとoriginalHomInclusionの合成を
quotientIdentityとして構成し、内部単位との成分比較と最終合成の左単位律を証明する。

左単位の移送を射全体の定義的等式へ任せた最初の二案はkernelのdeterministic timeoutとなった。
逆unitorの単位生成元表示とwhiskerRightの純tensor評価を両側で明示してから、
既存内部左単位の同じ評価へ照合することで解消した。標準設定の対象ビルドは16秒で成功。
heartbeat等の上限拡大は採用していない。

Checks.QuotientIdentity・Checks.CompositionDifferential・Checks.AppendErasure・Checks.StageSeven・
既存Spectra.StageTwoの統合ビルドは成功（2711 jobs、終了コード0、警告なし）。
任意dg圏の元のHom包含の合成保存と、ZMod 2で最終Homの左単位を検査した。
主要5宣言の直接公理監査は標準公理のみ。監査累計2718宣言。
文書検査は13 Markdown・320 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

次は右単位と全path合成の結合則、指定εの次数−1の元とdε=id、通常順と豊穣順の符号比較。
U15b全受入・最終dg商・U15cの指定収縮データ付き普遍性は未完。
U11e・U12e/f・U13d/e残部・U14・U15d/e・U16/U17・D4mも未完。採用済み引用は0件。
共有系列への追加要求はない。共有一般論・共有ルートimport・他系列は編集していない。


### 17.136 U15b21：任意左path・内部全直和・最終Homの右単位（2026-10-17）

`Complexes/TensorCarryUnit.lean`は右単位を固定左tensor因子の内側へ移す構造式を証明する。
`Quotient/AppendRightUnit.lean`は左語に関する帰納法と二つの固定前方因子への適用から、
appendRightの右単位律を証明する。帰納ステップの比較は具体的なterm(b::w)へ直接書き換えず、
抽象的tensorの等式を先に作りprefixPathへの後合成で結ぶ。
`InternalRightUnit.lean`はpath直和の普遍性とunitor自然性で全内部合成の右単位へ拡張する。
`Complexes/RightUnitorEvaluation.lean`は逆右unitorの単位生成元表示と順方向の評価式を公開する。
`Quotient/RightIdentity.lean`はその評価と既存の最終合成の成分比較により、
最終微分を持つHomの実際のchain mapの等式quotientComposition_right_unitを証明する。
任意可換環・非有界・独立対象宇宙・Small.{u} Dを維持する。

Checks.QuotientRightIdentity・Checks.QuotientIdentity・Checks.CompositionDifferential・
Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功（2716 jobs、終了コード0、警告なし）。
任意左pathの式とZMod 2での最終右単位を検査した。
主要6宣言の直接公理監査は標準公理のみ。監査累計2724宣言。
文書検査は13 Markdown・320 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

次は全path合成の結合則、指定εの次数−1の元とdε=id、通常順と豊穣順の符号比較。
U15b全受入・最終dg商・U15cの指定収縮データ付き普遍性は未完。
U11e・U12e/f・U13d/e残部・U14・U15d/e・U16/U17・D4mも未完。採用済み引用は0件。
共有系列への追加要求はない。共有一般論・共有ルートimport・他系列は編集していない。


### 17.137 U15b22：全path結合則・最終結合則・主豊穣dg商と包含（2026-10-17）

`Complexes/TensorCarryAssociativity.lean`は右作用の結合図式が固定左tensor因子の追加で保たれる
ことをassociator自然性とpentagonから証明する。`Quotient/AppendRightAssociativity.lean`は
先頭Hom作用を基底に、左語に関する帰納法でappendRightの結合図式を構成する。
`Complexes/TensorRightTwoCoproductExt.lean`は二つの右tensor因子を持つ指定余積からのhom_extを
与える。添字宇宙は独立で、余積の存在は明示的なHasCoproduct仮定にする。
`Quotient/InternalAssociativity.lean`はそれを使い内部全path合成の結合則を証明する。

最終微分への移送を一つの三重tensor成分証明で行った案はkernelのdeterministic timeoutとなった。
`Complexes/TensorCompositionAssociativity.lean`へ抽象複体の結合図式と純tensor成分式の往復を
分離し、`Quotient/CompositionEvaluation.lean`で最終合成の純tensor評価をtensorLiftの包含式から
直接取り出すことで解消した。成分射全体の定義的照合を繰り返さず、明示した評価式を使う。
`Quotient/Associativity.lean`の最終結合則は標準設定で1.8秒、主豊穣構造は2.7秒でビルド成功。
heartbeat等の上限拡大は採用していない。

`Quotient/Category.lean`は元のDと同じ対象宇宙vのQuotientObjectを置く。対象の対応は実際のEquiv。
最終Hom・閉単位・chain map合成・左右単位・結合則からMathlib EnrichedCategory (Complex A)を
構成し、quotientDGCategoryと空path包含によるdg関手inclusionを公開する。
新たな独立dg構造体は導入していない。quotientComposition_eq_signed_composeは全整数次数について
豊穣合成成分と通常順composeの(-1)^(p*q)比較を証明する。
任意可換環・非有界・独立対象宇宙・Small.{u} Dを維持する。

Checks.QuotientCategory・Checks.QuotientRightIdentity・Checks.QuotientIdentity・Checks.StageSeven・
既存Spectra.StageTwoの統合ビルドは成功（2725 jobs、終了コード0、警告なし）。
任意dg圏の商dg構造と包含、ZMod 2での主豊穣構造、次数−1/+1の通常順符号比較を検査した。
主要12宣言の直接公理監査は標準公理のみ。監査累計2736宣言。
文書検査は13 Markdown・320 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

指定ε生成元の成分とdε=idの証明を続ける。収縮方程式の受入前なのでU15b全受入とはしない。
U15cの指定収縮データ付き普遍性・U11e・U12e/f・U13d/e残部・U14・U15d/e・U16/U17・D4mは未完。
採用済み引用は0件。共有系列への追加要求はない。共有一般論・共有ルートimport・他系列は編集していない。


### 17.138 U15b23：指定次数−1生成元・収縮方程式dε=id・U15b受入（2026-10-17）

`Complexes/UnitSandwichEvaluation.lean`は任意複体の元の両側へ閉単位射を挿入した操作の
純tensor表示を証明する。`Quotient/EpsilonElement.lean`は単一ε pathの生成元が元の単位元・
ε生成元・元の単位元のtensorとなることを示し、最終Homの次数−1の元epsilonElementを定義する。
具体的なterm[b]の別名を含む型照合を直接繰り返さず、抽象複体の成分補題を適用する。
`Quotient/EpsilonContraction.lean`は先頭消去をこの生成元へ適用すると元の単位元になること、
全erasureの同じ評価、内部微分の零を証明する。最後に最終微分d_internal+erasureから
**differential_epsilonElement：dε_b=id_b**を実際の商dg圏のunitElementとの等式として証明する。
収縮の存在だけでなく、各bについて指定された次数−1の元を公開している。

U15bの受入との対応は次のとおり。

| 要求 | 実際の証拠 |
| --- | --- |
| 各Homの全微分・二乗零 | quotientHom・quotientHom_d、erasure_closed・erasure_square_zeroからperturbComplexへ渡す証明（§17.124/125） |
| 合成と最終微分の両立 | internalComposition_total_d_apply・quotientComposition（§17.134） |
| 左右単位・結合 | quotientIdentity・quotientComposition_left_unit/right_unit/assoc（§17.135〜137） |
| Enriched主モデル | quotientDGCategory : EnrichedCategory (Complex A) (QuotientObject D S)、対象対応のEquivとdg関手inclusion（§17.137） |
| 通常順との符号比較 | quotientComposition_eq_signed_compose、全整数次数で(-1)^(p*q)（§17.137） |
| 指定εの収縮方程式 | epsilonElementの次数−1とdifferential_epsilonElementの次数−1→0の等式（本節） |

任意可換環・非有界Hom・独立対象宇宙・Small.{u} Dを維持し、元のHomの非正性を仮定しない。
これでU15a/bを受入済みとする。入口はQuotient.CategoryとQuotient.EpsilonContraction。
厳密普遍性、係数変更、Verdier比較はこの受入に含めず、U15c〜eに保持する。

Checks.QuotientContraction・Checks.QuotientCategory・Checks.QuotientRightIdentity・Checks.QuotientIdentity・
Checks.CompositionDifferential・Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功
（2730 jobs、終了コード0、警告なし）。任意dg圏とZMod 2で収縮方程式を検査した。
主要7宣言の直接公理監査は標準公理のみ。§17.136以降の今回25宣言を直接ログで再照合した。
監査累計2743宣言。文書検査は13 Markdown・320 exposition参照、失敗0件。
担当差分の空白検査は成功。今回の実装にsorry/admit/新規axiomはない。

次のU15cでは、dg関手F:D→Eに対し、各b:SのHom_E(Fb,Fb)の指定次数−1の元h_bと
その微分がunitElementとなる等式をデータとして固定する。各pathのεをh_bへ送る評価を構成し、
消去微分との整合性から最終Homのchain mapを作り、dg関手への延長・制限との往復・一意性を証明する。
収縮の単なる存在を選択済みデータと同一視しない。U15dのunderived係数変更とU15eの
local K-flat版／解像度版のVerdier比較、次数0 Homの具体例は引き続き残る。
U11e・U12e/f・U13d/e残部・U14・U16/U17・D4mも未完。採用済み引用は0件。
共有系列への追加要求はない。共有一般論・共有ルートimport・他系列は編集していない。


### 17.139 U15c1：指定収縮付きdg関手・商からの制限・ε評価の微分（2026-10-17）

`Functor/ContractingElements.lean`はdg関手による微分の保存と、指定次数−1の元の微分が単位なら
その像も同じ収縮方程式を満たすことを証明する。
`Quotient/ContractedFunctor.lean`はdg関手F:D→Eと各b:Sの選択済み収縮元h_b、d h_b=idの等式を
ContractedFunctorとして保持する。Eの対象宇宙は独立で、Eのsmall性は仮定しない。
データのpostcomp、商の包含と指定εによるcanonicalContractedFunctor、商からの任意dg関手から
このデータを取り出すrestrictContractedFunctorと、その収縮元の評価式を公開する。
収縮の存在命題から任意に選択する構成へ弱めていない。

`Quotient/ContractionCochain.lean`はh_bをε複体からHom_E(Fb,Fb)への次数0 cochainへ移す。
標準ε生成元の像がh_bであり、そのHom微分がeraseEpsilon後に像対象の単位射を入れるcochainと
一致することを証明する。この次数0 cochainは閉じているとは主張しない。
これが任意pathの評価を最終Hom微分と両立させるための入力となる。
任意可換環・非有界Hom・独立対象宇宙の契約を維持する。

Checks.ContractedFunctor・Checks.QuotientContraction・Checks.QuotientCategory・Checks.StageSeven・
既存Spectra.StageTwoの統合ビルドは成功（2732 jobs、終了コード0、警告なし）。
任意の対象宇宙のEへの制限と収縮cochainの微分式、ZMod 2での標準収縮データを検査した。
主要9宣言の直接公理監査は標準公理のみ。監査累計2752宣言。
文書検査は13 Markdown・320 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

次は閉性を仮定しない次数0 cochainのtensorとその微分式から、各有限pathの評価を構成する。
消去和に関する微分の帰納式、全path直和への貼合せ、最終Hom上のchain map、dg関手の延長、
制限との往復・一意性を残すためU15c全受入は未完。
U11e・U12e/f・U13d/e残部・U14・U15d/e・U16/U17・D4mも未完。採用済み引用は0件。
共有系列への追加要求はない。共有一般論・共有ルートimport・他系列は編集していない。


### 17.140 U15c2：閉性を仮定しないtensor・有限path評価・全直和への評価貼合せ（2026-10-17）

`Complexes/TensorZeroCochain.lean`は二つの任意次数0 cochainのtensorを、既存右/左tensor Hom写像の
合成で構成する。閉性は仮定しない。chain mapのtensorとの一致、純tensor上の評価式、
左右のHom微分による二項の微分公式を証明した。Hom複体のchain mapが任意二次数のδを保つ
homComplexMap_differentialも公開する。次数引数を明示して成分型を揃え、上限拡大は行っていない。

`Quotient/PathEvaluation.lean`はContractedFunctorの実際のHom写像と指定収縮cochainを各pathの
因子へ作用させ、対象Eの豊穣合成で畳み込むpathEvaluationを構成する。
これは内部微分に関する閉性をまだ持たない次数0 cochainである。
空語の公式、前方Hom・標準ε・後方pathの純tensor公式、単一ε pathの単位因子を消した評価を
証明した。有限pathの構成・成分公式にはDのsmall性を要求しない。
具体的term(b::w)を含むcochainの評価は、両辺の始域表示を明示的に揃えて検証した。

`Quotient/PathCochainDesc.lean`は任意次数pのpath cochain族を全path直和からのcochainへ
貼り合わせ、その包含上の公式と一意性を証明する。閉性やshift先のchain mapへの変換は仮定しない。
評価関手による余積保存では、Discrete.functorとの合成図式の別名に依存せず、
isColimitOfHasCoproductOfPreservesColimitのcofanを使う。
`Quotient/InternalEvaluation.lean`はこの構成をpathEvaluationへ適用し、internalEvaluationと
各pathへの制限、元のHom上でF.mapとの一致、ε上で選択したcontractionCochainとの一致を証明する。
全直和では既存のSmall.{u} Dを使い、Eのsmall性・Homの有界性は仮定しない。

Checks.PathEvaluation・Checks.ContractedFunctor・Checks.QuotientContraction・Checks.QuotientCategory・
Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功（2737 jobs、終了コード0、警告なし）。
small性を要求しない単一pathの評価、全直和の空path、ZMod 2でのε上の一致を検査した。
主要16宣言の直接公理監査は標準公理のみ。監査累計2768宣言。
文書検査は13 Markdown・320 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

次はpathEvaluationの元のHomによるprependMapとの整合性を証明し、収縮cochainの微分公式と
tensorZeroCochain_differentialから、δ(pathEvaluation w)が各εを消して短いpathを評価した和と
一致することを帰納的に証明する。目標はδ 0 1 (internalEvaluation x y) =
(erasure x y).comp (internalEvaluation x y) (add_zero 1)。これを最終Homのchain map条件へ移す。
prepend整合性は空語でF.map_comp、非空語で前方二Homの合成保存と対象Eの結合則を使う。
既存tensorJoin_cochain_naturalityと、次数0のtensorの合成・括弧変更の補助式が使用候補。
商dg関手への延長、合成・単位保存、制限との往復・一意性を残し、U15c全受入は未完。
U11e・U12e/f・U13d/e残部・U14・U15d/e・U16/U17・D4mも未完。採用済み引用は0件。
共有系列への追加要求はない。共有一般論・共有ルートimport・他系列は編集していない。


### 17.141 U15c3：任意後方cochainの前方合成整合性と有限・全path評価のprepend則（2026-10-17）

`Complexes/RightTripleCochainExt.lean`は右括弧三重tensorの任意次数cochainの純tensor extと、
次数0の対角成分に固定したextを証明する。
`TensorJoinEvaluation.lean`は前方二因子の合成を保つchain map族、対象側の結合的な作用、
閉性を仮定しない任意の後方次数0 cochainについて、先に前方合成する場合と先に因子を評価する
場合の一致を証明する。次数0のextを使い、成分の始域・終域を同じ次数へ揃えてから検査した。
`Quotient/PathEvaluationPrepend.lean`は空語でF.map_comp、非空語でこの抽象補題と対象Eの
豊穣結合則を適用し、pathEvaluation_prependを証明する。有限語の結果にSmall仮定は不要。

`Complexes/TensorZeroCochainNaturality.lean`は右因子のchain mapによる前合成と、閉零の左写像を
持つcochain tensorの自然性を証明する。`Quotient/InternalEvaluationPrepend.lean`はpath直和の
包含への制限で有限語の結果を貼り合わせ、internalEvaluation_prependを得る。
これは内部微分に対する閉性を要求しないcochainの等式であり、最終Homのchain mapの存在を
この時点で仮定していない。任意可換環・非有界Hom・独立対象宇宙を維持する。

Checks.EvaluationPrepend・Checks.PathEvaluation・Checks.ContractedFunctor・Checks.QuotientContraction・
Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功（2742 jobs、終了コード0、警告なし）。
任意有限語、ZMod 2でεを含む非空pathを検査した。
主要6宣言の直接公理監査は標準公理のみ。監査累計2774宣言。
文書検査は13 Markdown・320 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

次はε評価と後方Homの合成をcontractionActionとして分離し、δ(contractionAction)=eraseHeadを証明する。
任意後方次数0 cochainとの合成の微分を、先頭ε消去と後方微分の二項に分ける。
これを元のHomによる作用へ運び、非空path評価のδの再帰式を作る。
全erasureとの微分整合性、最終Homのchain map、dg関手の延長と普遍性を残しU15c全受入は未完。
U11e・U12e/f・U13d/e残部・U14・U15d/e・U16/U17・D4mも未完。採用済み引用は0件。
共有系列への追加要求はない。共有一般論・共有ルートimport・他系列は編集していない。


### 17.142 U15c4：評価の微分＝ε消去後の評価・最終商Homの評価chain map（2026-10-17）

`Quotient/ErasureHeadCochainNaturality.lean`は閉性を仮定しない次数0 cochainに対して先頭・中間ε消去の
自然性を証明する。`ContractionAction.lean`は指定ε評価の像Homへの作用を固定cochainとして分離し、
その微分がeraseHeadに一致することを証明する。任意後方cochainとの合成の微分は先頭ε消去と
後方Hom微分の二項へ分かれる。対象Eのdg単位則から像の単位因子を消しており、追加仮定はない。

`Complexes/TensorZeroCochainLeftMap.lean`は閉零の左写像を任意次数0 cochainの後へ移す表示を与える。
`Quotient/EvaluationPrefix.lean`は元のHomによる閉作用evaluationOriginalAction、前方Hom・εの
評価evaluationPrefixAction、その微分、非空path評価の二重左tensorによる表示、後方cochainを
含む微分公式を証明する。`PathEvaluationDifferential.lean`はそれをprepend整合性へ接続し、
非空path評価の微分を先頭eraseFirstと短いpath評価の微分へ分ける。
後方任意次数cochainの持ち上げはpathEvaluationTailとして始域term(b::w)を明示的に保持する。
これにより異なるterm表示のHAddを暗黙の型照合へ任せない。

`InternalEvaluationPrefix.lean`は全pathの前方追加prefixPathと評価の整合性を各pathへの制限から証明する。
`EvaluationErasure.lean`はこれとeraseRow_consから左語に関する帰納法を行い、
**δ(pathEvaluation w) = eraseRow w · internalEvaluation**を証明する。
任意cochainのpath extとδの前合成保存から、全直和について
**internalEvaluation_differential：δ 0 1 (internalEvaluation x y) =
(erasure x y).comp (internalEvaluation x y) (add_zero 1)**を得た。

`Complexes/PerturbationMap.lean`は一般の閉じた二乗零θとδf=θfを入力に、始域の微分をd+θへ変更した
実際のchain mapを構成する。`Quotient/Evaluation.lean`は既に証明した全erasureと評価を入力し、
quotientEvaluation : quotientHom S x y → Hom_E(Fx,Fy)を構成する。
各次数の成分、元のHom包含との合成がF.mapであること、指定ε元の像が選択したh_bであること、
各pathの成分公式、単位射の保存を証明した。未証明の微分整合性を構造体の仮定へ移していない。
任意可換環・非有界Hom・独立対象宇宙を維持する。有限語の微分公式にDのsmall性は不要で、
全直和と主商Homの構成では既存のSmall.{u} Dを使う。Eのsmall性は仮定しない。

Checks.QuotientEvaluation・Checks.EvaluationPrepend・Checks.PathEvaluation・Checks.ContractedFunctor・
Checks.QuotientContraction・Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功
（2752 jobs、終了コード0、警告なし）。全直和の微分整合性と実際のchain map、
ZMod 2での指定ε保存を検査した。
主要26宣言の直接公理監査は標準公理のみ。§17.141以降の今回32宣言を直接ログで再照合した。
監査累計2800宣言。文書検査は13 Markdown・320 exposition参照、失敗0件。
担当差分の空白検査は成功。今回の実装にsorry/admit/新規axiomはない。

次は任意二pathの合成保存を証明する。有限語では
ofHom(appendMap w v).comp(pathEvaluation(w++v)) =
(tensorZeroCochain(pathEvaluation w)(pathEvaluation v)).comp(ofHom(eComp_E))を目標にし、
空の左語でpathEvaluation_prepend、非空語で前方評価の作用と対象Eの結合則を使う。
全直和へ拡張後、実際のchain mapの式
quotientComposition ≫ quotientEvaluation = (quotientEvaluation ⊗ₘ quotientEvaluation) ≫ eComp_E
を得て、既存quotientEvaluation_unitと共にdg関手への延長を構成する。
その後、任意の商dg関手の各path成分が制限データのpathEvaluationに一致することから
延長・制限の往復と一意性を証明する。対象の定義的等しさと同型を混同しない。
U15c全受入、U11e・U12e/f・U13d/e残部・U14・U15d/e・U16/U17・D4mは未完。
採用済み引用は0件。共有系列への追加要求はない。共有一般論・共有ルートimport・他系列は編集していない。


### 17.143 U15c5：任意二pathの合成保存・dg関手への延長・指定収縮データへの往復（2026-10-17）

`Complexes/TensorZeroCochainLaws.lean`は閉性を仮定しない次数0 tensorの合成保存、associatorとの
整合性、左右の恒等cochainとの一致を証明する。直接の成分型照合で検出した再帰深さの制限は、
既存tensorCochain_interchangeと左右Hom写像の合成保存を使って解消した。上限拡大は採用していない。
`TensorZeroCochainEvaluation.lean`は閉零写像による左右後合成と両因子前合成、結合的な三項の
評価式、評価の合成保存を固定左cochainの追加へ運ぶtensorCarry_evaluationを証明する。
固定左cochainの閉性も仮定しないので、指定εの評価にも適用できる。

`Quotient/PathEvaluationAppend.lean`は任意二pathについて
ofHom(appendMap w v).comp(pathEvaluation(w++v)) =
(tensorZeroCochain(pathEvaluation w)(pathEvaluation v)).comp(ofHom(eComp_E))を証明する。
左語の空語はprepend則、非空語は帰納仮定へεと元の前方Homを順に追加する二回のcarryで得る。
この有限語の結果はSmall仮定を必要としない。
`TensorTwoPathCochainExt.lean`は二つの全path直和のtensorからの任意次数cochainのextを与え、
`InternalEvaluationComposition.lean`は各二pathへの制限から全直和の合成保存を証明する。
`EvaluationComposition.lean`は純tensor上の最終合成の直接評価を使って、実際のchain mapの式
quotientComposition ≫ quotientEvaluation = (quotientEvaluation ⊗ₘ quotientEvaluation) ≫ eComp_E
を証明する。

`Quotient/Extension.lean`は既存quotientEvaluation_unitとこの合成保存から、
**extension : ContractedFunctor A D S E → DGFunctor A (QuotientObject D S) E**を構成する。
元の包含との合成がC.toDGFunctorに等しいこと、制限後の指定収縮元が元のh_bであること、
**restrict_extension：restrictContractedFunctor(extension C) = C**を証明した。
最後の等式は、dg関手だけでなく選択済み収縮を含む構造体そのものの等式である。
ContractedFunctor.extはdg関手の等式と依存する収縮族のHEqから証明し、不要なSmall仮定は置かない。
EnrichedFunctor.extでは両関手を明示して対象成分のrflによる誤ったメタ変数同一化を避けた。
任意可換環・非有界Hom・独立対象宇宙・全直和でのSmall.{u} Dを維持し、Eのsmall性は仮定しない。

Checks.QuotientExtension・Checks.QuotientEvaluation・Checks.EvaluationPrepend・Checks.PathEvaluation・
Checks.QuotientContraction・Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功
（2759 jobs、終了コード0、警告なし）。任意有限語の連結と実際のdg延長、
任意対象宇宙のEに対する指定収縮付きデータの往復、ZMod 2での同じ往復を検査した。
主要18宣言の直接公理監査は標準公理のみ。監査累計2818宣言。
文書検査は13 Markdown・320 exposition参照、失敗0件。担当差分の空白検査は成功。
今回の実装にsorry/admit/新規axiomはない。

次は逆向きのextension(restrict G)=Gと延長の一意性を証明し、厳密普遍性のEquivを構成する。
各pathが元のHomと指定εの反復合成で生成されることを具体的な成分等式として証明する。
単一ε pathを後方pathへ連結する式では、epsilonTermの両側の単位とprependMap_left_unitを使う。
前方の元のHomを合成する段階では、対象側の右単位則とassociator整合性を使ってprefixPathを復元する。
任意Gについてこれらの生成式とG.map_comp/G.map_unitElementからpath成分を同定する経路、
又は標準収縮データの評価が恒等となることと評価の後合成自然性を組み合わせる経路が候補。
一方の往復だけでU15c全受入や厳密普遍性の完成とはしない。
U11e・U12e/f・U13d/e残部・U14・U15d/e・U16/U17・D4mも未完。採用済み引用は0件。
共有系列への追加要求はない。共有一般論・共有ルートimport・他系列は編集していない。


### 17.144 U15c6：path生成・任意商dg関手の再構成・厳密普遍性の受入（2026-10-17）

`Complexes/TensorUnitInsertion.lean`は両側単位の挿入と三項tensorの結合比較を証明する。
`Quotient/EpsilonAppend.lean`と`PrefixGeneration.lean`は単一ε pathの連結からprefixPathを復元し、
`PathGeneration.lean`は各非空pathの純tensorを、元のHom・指定ε・後方pathの反復合成で表す。
`EpsilonCochainExt.lean`はε複体の次数−1の標準生成元による生成と他次数の零性から、
標準εを含む純tensor上の評価だけで次数0 cochainを判定する。有限pathの補題にSmall Dは不要。

`Quotient/Reconstruction.lean`は任意G:D/S→EのHom写像を内部graded族上のcochainとして読み、
path長の帰納法とGの合成保存から制限データのpath評価との一致を証明する。
これを全path直和へ貼り合わせ、**extension_restrict：extension(restrict G)=G**を得た。
型の別名term(b::w)と明示的tensor表示をまたぐrewriteの失敗は、評価の等式と合同を別に作り、
等式の推移で結ぶことで解消した。計算上限の拡大はしていない。

`Quotient/Universal.lean`は既存restrict_extensionと合わせて
**universalEquiv : DGFunctor A (QuotientObject D S) E ≃ ContractedFunctor A D S E**を構成する。
extension_unique・existsUnique_extensionは、指定収縮を含む制限データに対する厳密な一意性である。
restrictContractedFunctor_comp・extension_postcompは任意H:E→Tによる後合成との整合性を証明する。
任意CommRing A、非有界Hom、独立したD/E/Tの対象宇宙を保持する。
全path直和にはSmall.{u} Dを用い、E/Tのsmall性は要求しない。
収縮の単なる存在と選択済みデータを同一視しない。これでU15cを受入済みとする。

Checks.QuotientUniversal・Checks.QuotientExtension・Checks.QuotientEvaluation・
Checks.QuotientContraction・Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功
（2763 jobs、終了コード0）。独立対象宇宙、両方向の往復、一意存在、後合成自然性とZMod 2を検査した。
既存Checks.QuotientEvaluationの長行警告2件を観測した。
新規Checksの長行警告は修正して再ビルド成功。文書検査は13 Markdown・320 exposition参照、失敗0件。
担当差分の空白検査も成功。主要20宣言の直接公理監査は標準公理のみ、累計2838宣言。
今回の実装にsorry/admit/新規axiomはない。採用済み引用は0件。

次はU11eの残る作用・結合比較自然性・coherenceを完成し、U12e/fの導来bimodule合成と係数変更へ接続する。
U13d/e残部・U14・U15d/e・U16/U17・D4mも未完で、U17までの目標を保持する。
共有系列への追加要求はない。共有一般論・共有ルートimport・他系列は編集していない。


### 17.145 U11e再開時のカーネル検査（2026-10-17、未受入）

U15c受入コミットはb8f116c7。U11eの未コミット草稿AssociatorLeftCompatibilityを再検査し、
126秒で宣言のkernel deterministic timeoutを再現した。最終の合同・等式推移を既存の汎用
可換四角形補題element_squareへ変更した別検査も133秒で同じ宣言のkernel timeoutとなった。
両ビルドの終了コード1を確認した。実行時間の観測切れを失敗と扱ったものではない。
この変更や関連するnaturality草稿は受入・公理監査累計・実装コミットに含めない。

次は結合同型による三重生成元の輸送を、作用前と作用後の独立した宣言へ分離し、
各宣言の型照合と最終可換式の型照合を別に測定する。汎用四角形への最終項の置換だけでは
計算負荷が解消しないという今回の結果を踏まえ、同じ検査の無変更再実行は行わない。
計算上限の拡大やsorryによる回避は採用していない。U11e全体とU17までの残目標を保持する。


### 17.146 U11e23：作用の値表示と結合比較後の作用輸送（2026-10-17）

`Tensor/AssociatorRightTransport.lean`のassociatorRightCochain_transportは、
結合同型の後に左F作用を適用した生成元を、R成分へ作用した右括弧の生成元として計算する。
associatorValueIso_hom_elementと既存の右括弧の作用公式から証明し、単独ビルドは1.9秒で成功した。
`Bimodule/ActionElement.lean`はleftActionElementを全Hom cochainから定義する。
始域・終域の型をM.valueに固定し、既存の左加群作用との一致leftActionElement_eqを証明する。

`Tensor/AssociatorActionDegree.lean`は作用後の次数jと中間次数lを独立変数として、
hj:k+p=j、hl:j+r=l、hn:j+i=nを明示した生成元輸送を証明する。
全Homによる値表示と元のleftAction表示の両方を公開する。
この版の二宣言を含むビルドは1.8秒で成功した。
対して、jをk+pの式へ固定した元の作用表示の特殊化と全Hom値表示の特殊化は、
それぞれkernel deterministic timeoutとなった。後者は130秒で失敗を確認した。
したがって単なる作用表示の置換だけで解消したとは扱わない。

左右の二段へ分離した草稿も、左側の宣言で133秒のkernel timeoutとなった。
局所haveを使わない直接証明項の版も失敗した。
命題の型だけを定義した一時検査は成功しており、検査負荷は証明項側に残る。
未受入のLeftTransport/LeftCompatibility/Naturalityおよび実験用草稿は本受入やコミットに含めない。

Checks.AssociatorTransport・Checks.QuotientUniversal・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（2828 jobs、終了コード0、警告なし）。任意環、独立対象宇宙、全整数次数、
ZMod 2の次数−1作用を検査した。主要5宣言の直接公理監査は標準公理のみ。累計2843宣言。
文書検査は13 Markdown・320 exposition参照、失敗0件。担当差分の空白検査も成功。
今回の受入実装にsorry/admit/新規axiomはない。引用採用は0件。

次は独立次数版を左側の輸送と最終可換式へ接続する。必要なら作用の結果の元も独立変数として
指定し、その元との等式から元の作用公式へ戻す。U11eの両作用自然性・実際のbimodule同型・
三角/五角coherenceはなお未完。U12e/f・U13d/e残部・U14・U15d/e・U16/U17・D4mの目標を保持する。
共有系列への追加要求はない。共有一般論・共有ルートimport・他系列は編集していない。

§17.146の受入後、独立次数版を使う左輸送の別検査も136秒でkernel deterministic timeoutとなり、
終了コード1を確認した。独立次数版の生成元輸送そのものの成功と、cochain作用後の元への
結合同型適用の成功は別の検査である。後者は引き続き未受入とし、最終可換式の完成は主張しない。
今回作成した失敗実験専用の三つの草稿は整理し、左輸送とその後続の作業草稿を保持した。
次は作用結果の元を独立変数にした等式を入力として比較することで、合同の引数で発生する
型照合を分離する。共有系列への要求や受入済みAPIの変更はない。


### 17.147 U11e24：成分関数による再表示・両作用の全Hom自然性・右加群同型（2026-10-17）

`Complexes/MapComponentFunctions.lean`は既存chain map f、指定された全次数の成分関数F、
F n x=f.f n xの証拠から、成分をFで明示したchain mapを構成する。
加法・A線形性・微分整合性を証明し、成分評価と元のchain mapとの等式を公開する。
`Tensor/AssociatorLeftActionMap.lean`は作用の生成元公式を任意の値写像の後で使える形にする。
`AssociatorComponent.lean`は元の結合同型の成分を始域・終域を固定した関数として定義し、
元の成分との一致と三重生成元上の計算を証明する。
`AssociatorComponentTransport.lean`と`AssociatorComponentCompatibility.lean`は、
この関数表示を使って左作用後の輸送と左作用の可換式を証明した（各2秒前後）。

元の結合同型の成分表示へ各点で戻す草稿検査は成功しなかった。
そのため`AssociatorValueHom.lean`は上の一般構成で結合比較のchain mapを再表示し、
成分が指定関数であることと、**射全体として元の結合同型のhomに等しいこと**を証明した。
`AssociatorValueHomNaturality.lean`は再表示した射の左作用可換性と全Hom自然性を証明する。
`AssociatorLeftNaturality.lean`は射全体の等式を使って、元の結合同型の全Hom自然性へ戻す。
後者のビルドは1.9秒で成功した。最終の成分型照合を巨大な射の展開へ戻していない。

`AssociatorRightComponentCompatibility.lean`は同じ成分関数表示で右B作用の可換式を証明する。
符号は左括弧の(-1)^(p*(k+r))と右括弧の(-1)^(p*l)、l=k+rを比較し、
再表示したchain mapの線形性で符号を輸送する（2.0秒で成功）。
`AssociatorRightValueHomNaturality.lean`と`AssociatorRightNaturality.lean`は、
元の結合同型の右B作用の主Hom写像の自然性と実際の右B加群同型associatorRightModuleIsoを構成する。
評価すると順逆とも元の結合同型へ戻る。
`AssociatorBimodule.lean`はこの右加群同型の左F作用に関する自然性を、値のHomだけでなく
**右B加群の主Hom endへの射の等式**として証明した。
任意CommRing A、非有界複体、独立B/C/E/F宇宙、Small.{u} B/C/Eを保持し、Fのsmall性は不要。
新規の計算上限拡大や引用は使っていない。

Checks.AssociatorBimodule・Checks.AssociatorTransport・Checks.QuotientUniversal・Checks.StageSeven・
既存Spectra.StageTwoの統合ビルドは成功（2842 jobs、終了コード0、警告なし）。
任意対象宇宙での右加群同型と評価、両作用の全Hom自然性、ZMod 2の次数−1作用の可換式を検査した。
主要24宣言の直接公理監査は標準公理のみ。累計2867宣言。
文書検査は13 Markdown・320 exposition参照、失敗0件。担当差分の空白検査も成功。
今回の受入実装にsorry/admit/新規axiomはない。採用済み引用は0件。
未受入の古いLeftTransport/LeftCompatibility/RightCompatibility等は今回の依存閉包・コミットに含めない。

次は右加群同型族と左作用の全Hom自然性を、全次数自然なbimodule比較へ束ね、
三変数自然性と三角・五角coherenceを完成させる。通常の閉零関手間の自然同型だけを
全次数dg自然性の代用にはしない。U11e全受入はなお未完。
U12e/f・U13d/e残部・U14・U15d/e・U16/U17・D4mの目標を保持する。
共有系列への追加要求はない。共有一般論・共有ルートimport・他系列は編集していない。


### 17.148 U11e25：順逆の全次数bimodule自然変換と閉単位・評価の一致（2026-10-17）

`Bimodule/ClosedTransforms.lean`のBimoduleParamTrans K M Nは、Mathlibの
GradedNatTrans ((Center.ofBraided (Complex A)).obj K) M.toFunctor N.toFunctorの別名である。
閉零の射だけについての通常の自然性へ縮小しない。
closedFamily_naturality・closedFamilyTransは、右B加群射族と左C作用に関する主Hom endの
可換式から、単位パラメータの全豊穣自然変換を構成する。
対象Cのsmall性は必要としない。

`Module/HomIsoSquare.lean`は、可逆な右加群射に関する全Hom四角形の逆向きを、
MathlibのeHomWhiskerLeft/Rightの合成則・交換則から証明する。
元の加群型とForgetEnrichmentの対象型をまたぐunfold後のrewriteでは型照合が失敗したため、
この補題をModuleCategoryの対象変数に対して先に証明してから適用した。
moduleIso_closed_hom_invは、加群同型の順逆の閉成分の合成がeIdであることを証明する。
`Bimodule/ClosedIso.lean`は同型族の逆も全Hom自然であることを証明し、順逆の単位パラメータ変換、
その成分公式と両順序の閉単位の式を公開する。

`Tensor/AssociatorTransforms.lean`は§17.147のassociatorRightModuleIsoとその全Hom自然性から
**associatorHom・associatorInv**を実際のGradedNatTransとして構成する。
associator_hom_inv_app・associator_inv_hom_appは、単位unitorでパラメータを合わせた
両順序の合成が、右加群の主Hom endの閉単位元と一致することを証明する。
associatorHom_π・associatorInv_πは、各B対象での評価が元のassociatorValueIsoの順逆の閉成分へ
戻ることを証明する。Centerの単位パラメータの型をまたぐrewriteの失敗は、明示した評価等式と
合同・推移で結び直して解消した。計算上限は変更していない。
任意CommRing A・非有界・独立B/C/E/F宇宙、Small.{u} B/C/Eを維持し、Fのsmall性は不要。

Checks.AssociatorTransforms・Checks.AssociatorBimodule・Checks.QuotientUniversal・Checks.StageSeven・
既存Spectra.StageTwoの統合ビルドは成功（2846 jobs、終了コード0、警告なし）。
順逆の全次数自然変換、評価、両順序の閉単位、ZMod 2の具体的な順逆合成を検査した。
主要21宣言の直接公理監査は標準公理のみ。監査累計2888宣言。
文書検査は13 Markdown・320 exposition参照、失敗0件。担当差分の空白検査も成功。
今回の実装にsorry/admit/新規axiomはない。採用済み引用は0件。

次はこれらの全次数自然変換を保った結合比較の三変数自然性と三角・五角coherenceを完成させる。
Mathlibの通常のEnrichedNatTrans圏の同型を併用する場合も、上で証明した全Hom自然性を保持する。
U11e全受入は未完。U12e/f・U13d/e残部・U14・U15d/e・U16/U17・D4mの目標を保持する。
共有系列への追加要求はない。共有一般論・共有ルートimport・他系列は編集していない。


### 17.149 U11e26：全Hom自然な閉零bimodule圏・評価・実際の結合同型（2026-10-17）

`Bimodule/ClosedComponents.lean`は閉零の全豊穣自然変換から右B加群射の成分族を取り出し、
全Hom endの可換式を復元する。Centerの単位パラメータの半braidingを先に明示してから比較し、
閉零変換と成分族の両往復を証明した。
`ClosedMapFamily.lean`はこの全Hom自然な成分族をsubtypeとして表示し、
BimoduleParamTrans (𝟙_ (Complex A))とのEquivを構成する。
`Module/HomSquareComposition.lean`は既存の豊穣Homの前後合成則・交換則から四角形の恒等と合成を証明する。
これを使い、成分族の恒等・合成が全次数自然性を保つことを証明した。

`Bimodule/Category.lean`のBimoduleCategoryは、対象を既存Bimodule A B Cのままとする閉零射の圏である。
Homは上の全Hom自然な成分族とし、圏の両単位・結合則を成分ごとに証明した。
独立したdg圏構造体や弱い通常自然変換を主モデルに追加するものではない。
このHomは全次数のGradedNatTransと同値であり、Cのsmall性は要求しない。
`Evaluation.lean`は任意c:Cで右B加群へ評価する関手、評価による射の外延性、
Hom同値の成分公式と合成時の単位パラメータunitorの式を公開する。
`Isomorphism.lean`は全Hom自然な右加群同型族からこの圏の実際のIsoを構成し、
順逆の評価式と両順序の恒等式を証明する。

`Tensor/AssociatorIso.lean`は§17.147/148の全次数自然性と同型族から
**associatorIso**をBimoduleCategoryの実際のIsoとして構成する。
評価はassociatorRightModuleIsoへ戻り、Hom同値で順逆の射を読むと既存associatorHom・associatorInvに
構造体として一致する。したがって今回の圏での同型と前回の全次数自然変換は別々の比較ではない。
任意CommRing A・非有界・独立B/C/E/F宇宙を保持し、Small.{u} B/C/Eのみを使用する。
右端Fのsmall性や、すべてのHomが非正に集中する仮定は追加していない。

Checks.BimoduleCategory・Checks.AssociatorTransforms・Checks.QuotientUniversal・Checks.StageSeven・
既存Spectra.StageTwoの統合ビルドは成功（2853 jobs、終了コード0、警告なし）。
全次数変換とのHom同値、評価の合成保存、独立宇宙のFでの実際の結合同型、
ZMod 2でのbimodule射としての順逆合成の恒等式を検査した。
主要28宣言の直接公理監査は標準公理のみ。監査累計2916宣言。
文書検査は13 Markdown・320 exposition参照、失敗0件。担当差分の空白検査も成功。
今回の実装にsorry/admit/新規axiomはない。採用済み引用は0件。

次はBimoduleCategoryの射を相対tensorで運ぶ両変数mapと、その値・作用の成分公式を構成する。
それを結合比較の三変数自然性と三角・五角coherenceに使う。U11e全受入はなお未完。
U12e/f・U13d/e残部・U14・U15d/e・U16/U17・D4mの目標を保持する。
共有系列への追加要求はない。共有一般論・共有ルートimport・他系列は編集していない。


### 17.150 U11e27：左右の加群評価と相対tensorの各値の双関手（2026-10-17）

`Module/LeftClosedMaps.lean`は、全Hom自然なchain map成分族から既存の左加群Hom endの閉零射を
構成するleftModuleMorphismMk、評価式、評価による外延性を証明する。
既存LeftModule.toRightOppositeと右加群のmoduleMorphismMkを再利用し、二重oppositeの
恒等Hom写像を明示して自然性を移す。新しい左加群型やHom複体は定義していない。
二重opposite側の自然性だけの補題にSmall Dは要求しない。

`Bimodule/LeftEvaluation.lean`は、両対象で複体へ評価するvalueEvaluationを定義する。
既存の閉零bimodule射の全Hom自然性を主Hom endの各成分へ射影し、値成分の左作用自然性を証明する。
その族を上の構成子で左加群射へ持ち上げ、**leftEvaluation : BimoduleCategory A B C ⥤ LeftModuleCategory A C**
を構成した。恒等・合成保存と、さらにC対象で評価すると元の値の射へ戻る式を証明する。
左加群の型の推論に時間を要した箇所では始域・終域・成分族を明示して解消し、計算上限は変更していない。
leftEvaluationにはSmall.{u} Cが必要で、値成分の左作用自然性自体には不要である。

`Tensor/BimoduleValueMaps.lean`は、f:P→P'・g:Q→Q'を閉零bimodule射として、
**composeValueMap f g b e**を既存BalancedTensor.mapから構成する。
値はQ(c,e)⊗_C P(b,c)の順であり、第一因子へg、第二因子へfが作用する。
生成元包含への制限、恒等・合成保存を証明し、固定した両端b/eごとに実際の積圏
BimoduleCategory A B C × BimoduleCategory A C EからCh(A)への**valueFunctor**を構成した。
BalancedTensor.mapの閉零対象を明示し、型の別名をまたぐrewriteは評価等式の合同・推移で置き換えた。
`BimoduleValueElements.lean`は、任意整数次数の純tensor上でこのmapを評価し、
対応する各因子のchain mapを適用することを証明する。閉零射なので追加のKoszul符号はない。
任意CommRing A、非有界、独立B/C/E宇宙、Small.{u} B/Cを維持する。Eのsmall性は不要。

Checks.BimoduleTensorMaps・Checks.BimoduleCategory・Checks.QuotientUniversal・Checks.StageSeven・
既存Spectra.StageTwoの統合ビルドは成功（2857 jobs、終了コード0、警告なし）。
独立宇宙の評価・各値の双関手、生成元包含・恒等・合成、ZMod 2の次数−1と1の生成元評価を検査した。
主要14宣言の直接公理監査は標準公理のみ。監査累計2930宣言。
文書検査は13 Markdown・320 exposition参照、失敗0件。担当差分の空白検査も成功。
今回の実装にsorry/admit/新規axiomはない。採用済み引用は0件。

次はcomposeValueMapが外側の右B作用・左E作用と全Homに関して可換であることを証明し、
値のmapをBimoduleCategory A B Eの射へ束ねる。各値の双関手を構成しただけでは
このbimodule射への持ち上げや、結合同型の三変数自然性・三角/五角coherenceを完了とは扱わない。
U11e全受入、U12e/f・U13d/e残部・U14・U15d/e・U16/U17・D4mは引き続き未完。
U17までの目標を保持する。共有系列への追加要求はない。
共有一般論・共有ルートimport・他系列は編集していない。


### 17.151 U11e28：外側両作用の全Hom自然性・実際のbimodule合成双関手（2026-10-17）

`Complexes/HomNaturalityEvaluation.lean`は主Homのchain mapの可換式を任意整数次数の元へ評価する。
`Bimodule/ValueActions.lean`はこれと既存の閉零右加群射の作用公式を使い、
bimodule射の値成分が左作用・右作用と斉次元で可換であることを証明する。
`Tensor/BimoduleMapComponent.lean`は§17.150のcomposeValueMapを固定した成分関数として表示し、
元の成分との一致・生成元公式・整数単位によるスカラー倍との可換性を証明した。

`BimoduleMapLeftAction.lean`・`BimoduleMapRightAction.lean`は、値のmapと外側の両作用の
可換式をbalanced tensorの生成元上で証明する。右B作用の符号(-1)^(p*k)は両辺で一致し、
mapの線形性で輸送する。左E作用には追加符号は生じない。
`BimoduleValueHom.lean`は既存chainMapOfComponentFunctionsで値のmapを再表示する。
`BimoduleMapNaturality.lean`は生成元の外延性を使い、**右B作用・左E作用の全Hom chain mapの自然性**を証明した。
`BimoduleMapFamilies.lean`はこの値のmapを実際の右B加群射composeRightMapへ持ち上げ、
その射族が左E作用の右B加群の主Hom endに関しても全次数自然であることを証明する。

`Bimodule/ValueExt.lean`は全b/eでの複体評価が一致すれば閉零bimodule射が等しいことを証明する。
`Tensor/BimoduleFunctor.lean`は全Hom自然な射族から**composeMap**を構成し、
評価が元のcomposeValueMapへ戻る式、恒等・合成保存を証明した。
これにより**composeFunctor : BimoduleCategory A B C × BimoduleCategory A C E ⥤ BimoduleCategory A B E**
を構成した。対象は既存のbimodule合成のままであり、閉零自然性だけの射への置換はない。
任意CommRing A・非有界・独立B/C/E宇宙・Small.{u} B/Cを維持し、Eのsmall性は不要。
新規の計算上限拡大・共有モデル圏一般論の複製・引用は使用していない。

Checks.BimoduleComposition・Checks.BimoduleTensorMaps・Checks.BimoduleCategory・Checks.QuotientUniversal・
Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功（2869 jobs、終了コード0）。
新規Checksの長行警告2件を修正して再ビルド成功（1897 jobs、警告なし）。
独立対象宇宙での実際の合成双関手、値への評価、射としての合成保存、特性2の特殊化、
右作用次数−1・前方因子次数1・後方因子次数0の符号付き可換式を検査した。
主要25宣言の直接公理監査は標準公理のみ。監査累計2955宣言。
今回の実装にsorry/admit/新規axiomはない。採用済み引用は0件。担当差分の空白検査は成功。

全体文書検査は13 Markdown・320 exposition参照を検査し、別系列の互換宣言
BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの未解決参照1件で失敗した。
この宣言のソースはBhattScholze/Inputs/SemiperfectoidSurjectivity.leanに存在することを確認した。
共有ルートの読込環境での未解決をM5の変更で修正したとは扱わず、共有ルートや該当系列は編集していない。
Markdownのリンクについて追加の失敗は報告されていない。全体文書検査の成功は主張しない。

次はcomposeFunctorを反復した二つの三変数関手とassociatorIsoの自然性を構成する。
その後、単位比較を同じ閉零bimodule圏へ接続し、三角・五角coherenceを証明する。
U11e全受入、U12e/f・U13d/e残部・U14・U15d/e・U16/U17・D4mは引き続き未完。
U17までの目標を保持する。共有系列への新たなAPI要求はない。
共有一般論・共有ルートimport・他系列は編集していない。


### 17.152 U11e29：閉零bimodule射の三変数に関する結合自然同型（2026-10-17）

`Tensor/TripleFunctors.lean`は同じ三変数の積圏を源として、composeFunctorを二回使う
左括弧・右括弧の反復合成関手leftTripleFunctor/rightTripleFunctorを構成する。
`TripleMapElements.lean`は両括弧のmapを三重斉次生成元で計算し、R/Q/Pの各値に
対応する閉零射を適用することを証明する。内側のcomposeMapの値への評価は§17.151の式を再利用する。
`TripleMapComponents.lean`は固定した成分関数による同じ計算を公開する。

`AssociatorMapElements.lean`は、この二つのmap公式と元の結合同型の生成元公式を
可換四角形へ組み合わせ、三変数の閉零bimodule射についての生成元自然性を証明する。
`AssociatorMapNaturality.lean`は、反復tensorからのcochainの外延性でこれを全体へ貼り合わせ、
値のchain mapの等式へ移す。次数0の等式を除去する際は、m+0=nを先に正規化して
その等式を直接除去する。曖昧なsubstでn=m+0が残る型照合の失敗を解消した。
再表示した値のchain mapとの等式を使い、元のassociatorValueIsoのhomに対する自然性を得る。

`AssociatorValueEvaluation.lean`は、閉零bimodule結合同型の順逆を値の複体へ評価すると
元の結合同型の順逆のchain mapへ戻ることを証明する。
`AssociatorNaturality.lean`は全b/dの評価による外延性から、実際のbimodule射としての
**associatorIso_naturality**を証明し、**associatorNatIso : leftTripleFunctor ≅ rightTripleFunctor**
を構成する。その成分は構造体として既存associatorIsoに一致する。
任意CommRing A・非有界・独立B/C/E/F宇宙、Small.{u} B/C/Eを保持し、Fのsmall性は要求しない。
各変数の射は全Hom自然性を保持したBimoduleCategoryの射である。
今回受け入れる三変数自然性は閉零bimodule射に関するもの。
任意パラメータKのGradedNatTransに対する三変数の豊穣自然性は、この記録の受入に含めない。

Checks.AssociatorNaturality・Checks.BimoduleComposition・Checks.BimoduleCategory・Checks.QuotientUniversal・
Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功（2876 jobs、終了コード0、警告なし）。
独立対象宇宙での二つの三変数関手・自然同型・成分公式・射の自然性square、ZMod 2の特殊化を検査した。
主要14宣言の直接公理監査は標準公理のみ。監査累計2969宣言。
今回の実装にsorry/admit/新規axiomはない。採用済み引用は0件。担当差分の空白検査は成功。
全体文書検査は13 Markdown・320 exposition参照を検査し、§17.151と同じ担当外の
BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの未解決参照1件で失敗した。
共有ルートや別系列を編集していない。全体文書検査の成功は主張しない。

次は単位比較をBimoduleCategoryの同型へ持ち上げ、三角・五角coherenceを証明する。
閉零変数の自然性だけでU11eの全豊穣自然性を代用せず、任意パラメータ版も残課題として保持する。
U11e全受入、U12e/f・U13d/e残部・U14・U15d/e・U16/U17・D4mは引き続き未完。
U17までの目標を保持する。共有系列への新しいAPI要求はない。


### 17.153 U11e30：閉零bimodule単位同型と三角coherence（2026-10-17）

`Tensor/UnitBimoduleIso.lean`は既存のleftUnitIso/rightUnitIsoと両作用の全Hom自然性を再利用し、
BimoduleCategoryの実際の同型leftBimoduleUnitIso/rightBimoduleUnitIsoへ持ち上げる。
両対象での評価は順逆とも既存のleftUnitValueIso/rightUnitValueIsoに戻る。
左単位はSmall.{u} Bのみ、右単位はSmall.{u} B/Cを用いる。

`Complexes/TensorGeneratorMaps.lean`は、生成元を指定したmapをtensorの前後に合成する二つの法則と、
associatorでbalanced関係を移す法則を証明する。
`Tensor/TriangleGenerators.lean`は三角の両経路を実際の三重包含上で計算する。
型の別名を含む包含・whiskerのunfold後のrewriteは失敗したため、独立した複体変数に対して
先に証明した上の法則を、包含と単位評価へ適用して解消した。計算上限は変更していない。
一方は中間の対角HomをPの左作用で消す経路、他方はQの右作用で消す経路である。
`Tensor/Triangle.lean`のtriangleValueは既存BalancedTensor.conditionから両経路を同定する。
**triangle**は全b/eの評価による外延性でこれを戻した、実際の閉零bimodule射としての三角coherenceである。
右作用のKoszul符号は既存のbalanced関係に含まれ、符号を省略した別の関係式は使わない。
任意CommRing A・非有界・独立B/C/E宇宙・Small.{u} B/Cを維持し、Eのsmall性は不要。

Checks.Triangle・Checks.AssociatorNaturality・Checks.BimoduleComposition・Checks.QuotientUniversal・
Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功（2896 jobs、終了コード0、警告なし）。
独立宇宙での左右の単位同型、bimodule射としての三角式、ZMod 2の三角式を検査した。
主要13宣言の直接公理監査は標準公理のみ。監査累計2982宣言。
今回の実装にsorry/admit/新規axiomはない。採用済み引用は0件。担当差分の空白検査は成功。
全体文書検査は13 Markdown・320 exposition参照を検査し、§17.151/152と同じ担当外の
BhattScholze互換宣言の未解決参照1件で失敗した。共有ルートや該当系列は編集していない。

次は四重生成元で五角coherenceを証明する。単位同型のbimodule変数に関する自然性と、
任意パラメータの変換に関する三変数の豊穣自然性も、U11e全受入の残課題として保持する。
U12e/f・U13d/e残部・U14・U15d/e・U16/U17・D4mは引き続き未完。U17までの目標を保持する。
共有系列への新しいAPI要求はない。


### 17.154 U11e31：四重生成元と閉零bimodule射の五角coherence（2026-10-17）

`Tensor/AssociatorDegreeExt.lean`は三重生成元による各次数の線形写像の外延性を証明する。
`QuadElements.lean`は四つのbimoduleの両端と中間の括弧付けの斉次生成元を定義し、
`QuadCochainExt.lean`は完全左合成からの任意次数cochainを四重生成元で判定する。
合成P,Q,R,Sの完全左括弧付けの値はS⊗(R⊗(Q⊗P))であり、
完全右括弧付けの値は((S⊗R)⊗Q)⊗Pである。合成順と値のtensor順を区別した。

`Bimodule/ValueIdentity.lean`と`Tensor/BimoduleMapElementValues.lean`は恒等射と指定した値の
生成元評価を与える。`AssociatorIsoElements.lean`は実際の閉零結合同型を値へ評価し、
既存の固定成分関数の生成元公式に戻す。`PentagonShortElements.lean`は二辺、
`PentagonLongElements.lean`は三辺の経路を計算し、同じ完全右生成元へ移ることを証明した。
`Pentagon.lean`のpentagonValueHomは外延性で両経路を同定し、pentagonValueで元の値の
chain mapへ戻す。**pentagon**は全対象での値への評価による外延性を使った、
実際の閉零bimodule射の五角等式である。生成元上の等式だけで受入とはしていない。
任意CommRing A・非有界・独立B/C/E/F/G宇宙を保持し、Small.{u}はB/C/E/Fに要求する。
Gのsmall性は不要。計算上限の追加、共有一般論の複製、引用は使用していない。

Checks.Pentagon・Checks.Triangle・Checks.AssociatorNaturality・Checks.BimoduleComposition・
Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功（2788 jobs、終了コード0）。
Checksの長行警告を修正後、再ビルド成功（1952 jobs、警告なし）。
独立対象宇宙でのbimodule射の五角等式とZMod 2の特殊化を検査した。
主要15宣言の直接公理監査は標準公理のみ。監査累計2997宣言。
今回の実装にsorry/admit/新規axiomはない。採用済み引用は0件。
全体文書検査は13 Markdown・320 exposition参照を検査し、§17.151〜153と同じ担当外の
BhattScholze互換宣言の未解決参照1件で失敗した。共有ルートや該当系列は編集していない。

次は単位同型のbimodule変数に関する自然性と、任意パラメータKのGradedNatTransに
関する三変数の豊穣自然性を完成する。閉零射に関する五角と三変数自然性だけで
任意パラメータの自然性を代用しない。U11e全受入は引き続き未完。
U12e/f・U13d/e残部・U14・U15d/e・U16/U17・D4mも未完。U17までの目標を保持する。
共有系列への新しいAPI要求はない。


### 17.155 U11e32：単位同型の閉零bimodule変数自然性と単位自然同型（2026-10-17）

`Tensor/UnitMapNaturality.lean`のBalancedTensor.leftUnitValueHom_map_naturalityは
対角の左制限による単位評価の、右加群射に関する自然性を証明する。
包含上のmap公式・既存単位評価・rightAction_morphismから従い、符号付き右作用を保持する。
leftUnitValue_map_naturalityはこれをbimoduleの値へ適用し、
**leftBimoduleUnitIso_naturality**は値による射の外延性から実際のbimodule射の等式を得る。
右側は既存yonedaEvaluation_naturalityとleftEvaluation_map_evalを再利用して、
rightUnitValue_map_naturalityと**rightBimoduleUnitIso_naturality**を構成した。

`Tensor/UnitFunctors.lean`は対角bimoduleの定値関手と恒等関手の積をcomposeFunctorへ合成し、
leftUnitFunctor/rightUnitFunctorを定義する。
**leftUnitNatIso/rightUnitNatIso**は各単位合成関手から恒等関手への自然同型であり、
成分は既存のleftBimoduleUnitIso/rightBimoduleUnitIsoそのもの。
射は両作用に全Hom自然な閉零bimodule射のままである。
任意CommRing A・非有界・独立B/C宇宙を保持する。左単位の全結果はSmall.{u} Bのみで成立し、
Cのsmall性を要求しない。右単位ではSmall.{u} Cも明示する。

Checks.UnitNaturality・Checks.Pentagon・Checks.Triangle・Checks.AssociatorNaturality・
Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功（2790 jobs、終了コード0、警告なし）。
左単位をCのsmall性なしで検査し、左右の自然性squareとZMod 2の単位自然同型も検査した。
主要11宣言の直接公理監査は標準公理のみ。監査累計3008宣言。
今回の実装にsorry/admit/新規axiomはない。採用済み引用は0件。
全体文書検査は13 Markdown・320 exposition参照を検査し、§17.151〜154と同じ担当外の
BhattScholze互換宣言の未解決参照1件で失敗した。共有ルートや該当系列は編集していない。

次は任意パラメータKのGradedNatTransに関する三変数の豊穣自然性を完成する。
既存BalancedTensor.leftParamMap/rightParamMapと全Hom endへの評価を再利用し、
各変数のパラメータ付き作用と結合比較の可換式を、生成元計算から全chain mapへ上げる。
今回の閉零変数の単位自然性を任意パラメータの三変数自然性と同一視しない。
U11e全受入、U12e/f・U13d/e残部・U14・U15d/e・U16/U17・D4mは引き続き未完。
U17までの目標を保持する。共有系列への新しいAPI要求はない。


### 17.156 U11e33：任意パラメータの両対象評価と相対tensorへの値ごとの作用（2026-10-17）

`Bimodule/ParameterEvaluation.lean`は任意K : Complex Aについて、既存BimoduleParamTransを
Hom endの評価へ合成する**paramValue**を公開する。paramRightAtは元のmoduleHomEquivから
全次数自然な右B加群変換を取り出す。paramValue_left_naturalityは元のGradedNatTransの
自然性をmoduleHomπへ合成し、moduleComposition_πとtensor合成の法則で評価した全Hom等式。
**paramLeftAt**はこれを左C加群のパラメータ付き変換へまとめる。
左右の自然性、両評価の成分公式、全値でパラメータ付き変換の等式を判定するparamValue_extを証明した。
この評価にはSmall.{u} Bのみを要求し、Cのsmall性もKの閉性・有界性も要求しない。

`Tensor/BimoduleParameterValues.lean`は既存BalancedTensor.leftParamMap/rightParamMapへ
上の変換を渡し、**firstParamValue/secondParamValue**を構成する。
これらはK⊗compose(P,Q)の値から、P又はQを変換した合成の値への実際のchain map。
firstParamValue_elementはパラメータ次数kとQの値の次数rの交差符号(-1)^(kr)を証明し、
secondParamValue_elementには追加の交差符号がないことを証明する。
**firstParamHom/secondParamHom**は同じ作用の主Hom複体への転置表示。
任意CommRing A・非有界・独立B/C/E宇宙を保持し、相対tensorにはSmall.{u} B/Cを明示する。
Eのsmall性を要求しない。全Hom自然性を閉零自然性に弱めた代替変換は使わない。

Checks.BimoduleParameters・Checks.UnitNaturality・Checks.Pentagon・Checks.Triangle・
Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功（2786 jobs、終了コード0、警告なし）。
任意Kの変換、Cのsmall性なしの左加群評価と変換の外延性、独立宇宙の二つの作用、
パラメータ次数−1・Q次数1・P次数0の符号付き生成元、ZMod 2のHom表示を検査した。
主要14宣言の直接公理監査は標準公理のみ。監査累計3022宣言。
今回の実装にsorry/admit/新規axiomはない。計算上限の追加もなく、採用済み引用は0件。
全体文書検査は13 Markdown・320 exposition参照を検査し、§17.151〜155と同じ担当外の
BhattScholze互換宣言の未解決参照1件で失敗した。共有ルートや該当系列は編集していない。

今回の値ごとの作用は、まだ合成bimodule間のパラメータ付き変換へ束ねていない。
次は外側両作用の全Hom自然性を証明してその変換を構成し、三変数の各パラメータ作用と
associatorの可換式を生成元で証明して全chain mapへ上げる。
評価APIや生成元公式だけで任意パラメータに関する結合自然性の完成とはしない。
U11e全受入、U12e/f・U13d/e残部・U14・U15d/e・U16/U17・D4mは引き続き未完。
U17までの目標を保持する。共有系列への新しいAPI要求はない。


### 17.157 U11e34：任意パラメータの相対tensor作用の全Hom自然性と実際のbimodule変換（2026-10-17）

`Tensor/BimoduleParameterElements.lean`はfirstParamHom/secondParamHomのcochain評価を
任意の入出力次数で与える。作用と整数単位のスカラー倍、tensorの前方因子のスカラー倍の
補助式も証明した。`BimoduleParameterRight.lean`は外側の右B作用と各パラメータ作用の
符号付きcochain可換式を生成元の外延性から証明する。前の因子では元の変換の全Hom自然性、
後の因子ではk*p+p*(k+r)=p*r+2*(k*p)による符号の一致を使う。
**firstParamRightAt/secondParamRightAt**はこれを任意Kパラメータの全次数自然な右B加群変換へまとめる。
`BimoduleParameterLeft.lean`は外側の左E作用との対応する二つのcochain可換式を証明した。
前の因子ではk*(r+p)=k*r+k*p、後の因子では元の変換の左E作用に関する自然性を使う。

`Bimodule/ParameterFamily.lean`は左加群の符号付きcochain式から全Hom自然性を復元する
leftParamNaturality_of_cochainと、両作用の自然性を持つ右加群変換族から
BimoduleParamTransを構成する**paramFamilyTrans**を公開する。
後者の自然性は主Hom endを評価し、moduleComposition_πで合成を計算して証明する。
`Tensor/BimoduleParameters.lean`の**firstParam/secondParam**はこれを使う実際の
合成bimodule間の任意Kパラメータ変換であり、値への評価は既存firstParamHom/secondParamHomに戻る。
両外側作用の自然性を仮定として呼出し側へ残していない。
任意CommRing A・非有界・独立B/C/E宇宙・Small.{u} B/Cを維持し、Eのsmall性は不要。
Kの閉性・有界性を要求しない。Mathlibの閉零EnrichedNatTransによる代用も行っていない。

Checks.BimoduleParameterNaturality・Checks.BimoduleParameters・Checks.UnitNaturality・
Checks.Pentagon・Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功
（2788 jobs、終了コード0、警告なし）。独立宇宙での各変数の実際の変換、
元の値の作用との一致、三変数の左右括弧付けそれぞれへの六通りの反復適用、
ZMod 2での任意K変換を検査した。六通りの型の検査は結合自然性の等式の証明とは区別する。
主要18宣言の直接公理監査は標準公理のみ。監査累計3040宣言。
今回の実装にsorry/admit/新規axiomはない。計算上限の追加もなく、採用済み引用は0件。
全体文書検査は13 Markdown・320 exposition参照を検査し、§17.151〜156と同じ担当外の
BhattScholze互換宣言の未解決参照1件で失敗した。共有ルートや該当系列は編集していない。

次はfirstParam/secondParamの値の評価式を反復し、P/Q/R各変数のパラメータ作用と
associatorValueHomの前後合成の等式を三重生成元で証明する。
その等式を全chain map、主Hom end、実際のbimodule変換の比較へ上げる。
今回の変換の構成だけでassociatorの任意パラメータ自然性を受入済みとはしない。
U11e全受入、U12e/f・U13d/e残部・U14・U15d/e・U16/U17・D4mは引き続き未完。
U17までの目標を保持する。共有系列への新しいAPI要求はない。


### 17.158 U11e35：結合比較の任意パラメータ三変数自然性（2026-10-17）

`Tensor/AssociatorParameterExt.lean`は三重生成元の外延性から、K→Homの前後合成の等式を
生成元で判定するassociatorLeft_homMap_post_pre_eqを証明する。
`TripleParameterFirst.lean`と`TripleParameterRest.lean`は、P/Q/R各変数のパラメータ作用を
左右の反復合成の三重生成元で計算する六つの公式を公開した。
P変数では(-1)^(p*k)と(-1)^(p*r)が(-1)^(p*(k+r))に一致し、Q変数ではRの次数kとの
(-1)^(p*k)、R変数では追加の交差符号なしという式を保つ。

`AssociatorParameterValues.lean`はこれらと結合同型の固定成分公式を組み合わせ、
**associator_firstParam_value/middleParam_value/lastParam_value**を証明した。
これらは任意Kから値の主Hom複体へのchain mapとしての等式であり、生成元や閉零射だけの等式ではない。
`Bimodule/ParameterSquare.lean`は値の可換式を右加群の主Hom endへ戻すparam_square_of_valuesを与える。
`Tensor/AssociatorParameters.lean`の**associator_firstParam/middleParam/lastParam**は、
実際のfirstParam/secondParamと元のassociatorRightModuleIsoの射を使う全Hom endでの自然性。
各作用は§17.157で両外側作用の全次数自然性まで証明済みのbimodule変換である。
任意CommRing A・非有界・独立B/C/E/F宇宙・Small.{u} B/C/Eを維持し、Fのsmall性は不要。
Kの閉性・有界性・次数零性は課さない。閉零三変数の自然同型による代用は行っていない。

Checks.AssociatorParameters・Checks.BimoduleParameterNaturality・Checks.AssociatorNaturality・
Checks.UnitNaturality・Checks.Pentagon・Checks.Triangle・Checks.EnrichedHomNaturality・
Checks.LeftTensorColimits・Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功
（2835 jobs、終了コード0、警告なし）。独立宇宙で三つの全Hom endの等式、
ZMod 2でも任意Kに対する同じ主Hom endの自然性を検査した。
主要14宣言の直接公理監査は標準公理のみ。監査累計3054宣言。
今回の実装にsorry/admit/新規axiomはない。計算上限の追加もなく、採用済み引用は0件。


### 17.159 U11統合受入とU12e/fへの引継ぎ（2026-10-17）

U11の残る受入条件を元の§15.1と照合し、独立入口**StageEight.lean（U0〜U11）**を追加した。
既存StageSeven・共有ルートimportは変更していない。次の実装を同じ入口から利用できる。

| 受入条件 | 実装・証拠 |
| --- | --- |
| 左加群とopposite・符号 | Module.Left/LeftAction、既存の全Hom endによるLeftModuleCategory。U11aの既受入記録 |
| bimoduleと積dg圏表示 | Bimodule.TensorComparisonの往復を持つbimoduleEquivTensorFunctor。U11bの既受入記録 |
| 多対象balanced tensorと普遍性・map | Tensor.Balanced/Functor、任意パラメータの族の普遍性。U11cの既受入記録 |
| Yoneda・一対象環・残る両作用 | Tensor.Yoneda/LeftYoneda/YonedaRepresentative/Ring/Bimodule。U11dの既受入記録 |
| tensor–Homと全変数自然性 | Tensor.EnrichedHomAdjunction/Points/Source/Left/Target。主Hom複体の同型・閉零比較・K自然性・M/N/T全Hom自然性（§17.35〜40） |
| 両変数の余極限保存 | Tensor.HomAdjunctionLawsとLeftColimits。存在する余極限を保存し、全宇宙の余極限の存在を自動仮定しない（§17.35/42） |
| Fubiniと実際の結合同型 | Tensor.FubiniとAssociatorBimodule/AssociatorNaturality。両作用全Hom自然・実際のbimodule同型・閉零三変数自然同型 |
| 任意パラメータ三変数自然性 | Tensor.BimoduleParameters/AssociatorParameters。任意Kの実際の変換とP/Q/Rそれぞれに対する主Hom endでの等式（§17.156〜158） |
| 単位とcoherence | UnitFunctorsの左右単位自然同型、Triangle.triangle、Pentagon.pentagon。実際の閉零bimodule射としての等式（§17.153〜155） |

Checks.StageEight・Checks.AssociatorParameters・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（2840 jobs、終了コード0）。統合Checksの長行警告を修正した再ビルドも成功
（2426 jobs、警告なし）。StageEightだけのビルドも成功し、Checksの追加importに依存せず公開APIが揃う。
統合入口からの直接実行は終了コード0、主要16宣言の再監査は標準公理のみ。
この16宣言は既監査対象なので累計3054へ重複加算しない。
Lean v4.35.0-rc4・Mathlib e6bbacd0e1b7307ff6e17da09cd2455f60804fa6を再確認した。
全体文書検査は13 Markdown・320 exposition参照を検査し、§17.151〜157と同じ担当外の
BhattScholze互換宣言の未解決参照1件で失敗した。全体文書検査の成功は主張しない。
共有ルート・共有一般論・該当系列・他チャットの変更は編集していない。

これでU11a〜eを受入済みとする。U12a〜dの既存導来tensorを保持し、次はU12eで導来bimodule合成へ進む。
Bᵒᵖ⊗C上のsemifreeからBに関する相対K-flat性を得る条件を別証明し、必要なHomのlocal K-flat性と
dg圏の解像度を使う版を区別する。単純に二変数をsemifree置換して無条件の導来合成としない。
U12fの非flat係数変更の導来版、U13d/e残部、U14、U15d/e、U16/U17、D4mは未完。
U17までの目標を保持し、共有系列への新しいAPI要求はない。採用済み引用は0件。


### 17.160 U12e1：bimoduleの右相対K-flat性の合成閉性と準同型保存（2026-10-17）

`Bimodule/RelativeKFlat.lean`の**rightRelativeKFlat**は、Pの各左対象cにおける右B加群
P.rightAt cの相対K-flat性。A上のobjectwise K-flat性とは区別する。
全dg自然なbimodule同型・retractで不変であり、各右制限のsemifree性又は全Hom射影性から従う。
ここで要求するのは各右制限の性質そのものであり、積dg圏上のsemifree性からの制限定理を
仮定なしに導いたとはしていない。対角bimoduleはYoneda評価によりこの条件を満たす。
**rightRelativeKFlat_compose**はFubini同型を用いた合成閉性の証明。
acyclicな左B加群Nに対し、P⊗_B Nの各値がacyclicとなり、Qの右相対K-flat性により
Q⊗_C(P⊗_B N)がacyclicとなる。Fubiniでcompose(P,Q)⊗_B Nへ戻す。
この閉性には各HomのA-flat性やEのsmall性を追加しない。

`Bimodule/QuasiIso.lean`は全Hom自然な閉零BimoduleCategory上で、両対象の各値が複体の
quasiIsoとなる射のクラス**BimoduleCategory.quasiIso**を固定する。
二重iInfによる評価の逆像表示、恒等/合成・2-out-of-3・retract・同型整合性を証明し、
右加群評価と左加群評価が既存moduleQuasiIso/leftModuleQuasiIsoへ送ることも公開した。

`Tensor/BimoduleQuasiIso.lean`の**composeMap_first_quasiIso**は、後の因子Qの右制限が
相対K-flatなら、前の因子の任意の指定準同型を合成が保存することを証明する。
**composeMap_second_projective_quasiIso**は、Q/Q'の各右制限が全Hom射影的なら、
前の因子Pが任意でもQ→Q'の指定準同型を保存する。既存の射影的加群間の準同型の
tensorによるホモトピー同値を再利用し、Pの左制限へflat性を自動付与していない。
**composeMap_projective_quasiIso**は合成mapの因子分解から両変数の同時保存を得る。
任意CommRing A・非有界・独立B/C/E宇宙を保持。合成の中間CにSmall.{u}を要求し、Eには要求しない。

Checks.BimoduleKFlat・Checks.StageEight・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（3005 jobs、終了コード0、警告なし）。独立宇宙でのK-flat合成閉性、
準同型の2-out-of-3/retract、片側semifreeの十分条件、両変数の準同型保存、ZMod 2の対角例を検査した。
主要19宣言の直接公理監査は標準公理のみ。監査累計3073宣言。
今回の実装にsorry/admit/新規axiomはない。採用済み引用は0件。
全体文書検査は13 Markdown・320 exposition参照を検査し、§17.151〜159と同じ担当外の
BhattScholze互換宣言の未解決参照1件で失敗した。共有ルートや該当系列は編集していない。

次はこの準同型クラスの標準局所化を定義し、固定した右相対K-flat因子との合成を局所化へ降ろす。
さらにBᵒᵖ⊗C上のsemifreeから片側の相対K-flat性/全Hom射影性を得る制限定理を証明する。
相手側Homのlocal K-flat性が必要な版と、dg圏の解像度を使う版を区別し、
実際のbimodule解像度の存在・導来合成の両変数性・単位/結合coherenceまでU12eの残課題として保持する。
今回の十分条件・閉性・準同型保存だけでU12e全受入としない。
U12f・U13d/e残部・U14・U15d/e・U16/U17・D4mも未完。U17までの目標を保持する。
共有系列への新しいAPI要求はない。


### 17.161 U12e2：導来bimodule圏と固定K-flat因子による合成の降下・関手性（2026-10-17）

`Derived/BimoduleBasic.lean`の**DerivedBimoduleCategory**は、§17.160で固定した
全Hom自然な閉零BimoduleCategoryの値ごとのquasiIsoによるMathlibの構成された標準局所化。
**bimoduleToDerived**は指定局所化関手。反転する射の同型、反転する任意の関手の延長、
延長の厳密なfactorizationと一意性、自然変換の成分による外延性を既存Mathlibの普遍性から公開する。
任意A : Type u・B : Type v・C : Type wに対し標準射宇宙max (u+1) v wを使用する。
この段階でより小さいHomやモデル構造を仮定せず、Small.{u} Bのみを要求する。

`Derived/BimoduleTensor.lean`の**composeWith Q**は後の因子Qを固定した既存の合成関手。
Qの各右C制限の相対K-flat性があれば、前の因子の準同型を保存し、出力を標準局所化へ送った関手は
指定quasiIsoを反転する。これをMathlibの局所化普遍性で降ろしたのが**derivedComposeWith**。
**derivedComposeWith_fac**は局所化前の合成との厳密な一致、derivedComposeWith_uniqueは一意性。
具体的なLocalization.Lifting証拠と、元のbimodule対象における計算同型も公開する。
局所化の対象を別のモデルへ差し替えていない。

`Derived/BimoduleTensorMaps.lean`は後の因子の任意の射gからcomposeWithMapを作り、
合成双関手の法則から自然性・恒等・合成を証明する。
**derivedComposeWithMap**はこの自然変換を同じ局所化へ降ろしたもの。
元の対象上の成分は計算同型で元のcomposeMap(id,g)を挟む式に一致し、恒等・合成を保つ。
`BimoduleTensorFunctor.lean`のRightKFlatBimoduleCategoryは元の閉零bimodule圏の充満部分圏であり、
**derivedComposeWithFunctor**はこの圏から(DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E)
への実際の関手。後の因子も局所化済みの双導来関手を構成したとはしていない。
任意CommRing・非有界・独立B/C/E宇宙・Small.{u} B/Cを維持し、Eのsmall性は不要。

Checks.DerivedBimoduleTensor・Checks.BimoduleKFlat・Checks.StageEight・Checks.StageSeven・
既存Spectra.StageTwoの統合ビルドは成功（3010 jobs、終了コード0、警告なし）。
標準射宇宙max (u+1) v w、独立な対象/射宇宙の終域への局所化のfactorization、
固定因子との合成の降下・一意性、右K-flat部分圏での射の恒等/合成法則、ZMod 2の対角因子を検査した。
主要25宣言の直接公理監査は標準公理のみ。監査累計3098宣言。
今回の実装にsorry/admit/新規axiomはない。採用済み引用は0件。

全体文書検査は、共有ルートが参照する担当外CommutativeAlgebra.PerfectoidizationFunctorの
olean不足により、最初の宣言exportで終了コード1となった。今回の実行はMarkdown/expositionの検査に
到達しておらず、以前のBhattScholze参照エラーの再検査結果は得られていない。
共有ルートは他チャットにより変更中であり、M5から編集・巻き戻し・担当外ビルドは行っていない。
文書検査の成功は主張しない。

次は後の因子の準同型が誘導する自然変換の同型性と解像度選択独立性、
導来合成の単位・結合同型とcoherenceを接続する。
Bᵒᵖ⊗C上のsemifreeから片側の相対K-flat性を得る制限定理と、実際のbimodule解像度の存在は未完。
local Homの条件を固定した版とdg圏の解像度を使う版を区別する。
固定K-flat因子に対する関手性だけでU12e全受入としない。
U12f・U13d/e残部・U14・U15d/e・U16/U17・D4mも未完。U17までの目標を保持する。
共有系列への新しいAPI要求はない。


### 17.162 U12e3：射影的因子間の準同型比較と導来合成の右単位・結合自然同型（2026-10-17）

`Derived/BimoduleTensorComparison.lean`のcomposeWithProjectiveIsoは、Q/Q'の各右制限が
homotopically projectiveでありg:Q→Q'が指定quasiIsoであるとき、
出力を局所化した二つの合成関手の間の自然同型を与える。
**derivedComposeWithProjectiveIso**は、これを実際のDerivedBimoduleCategoryを始域とする
合成関手の比較自然同型へ降ろす。そのhomは元のgのderivedComposeWithMapに一致する。
**derivedComposeWithProjectiveIso_id/trans**は自己比較と三つの因子に関する推移整合性。
この比較は与えられた準同型gに対するもの。任意の二つのbimodule解像度の比較射の存在・
比較射に依存しないことを、この条件付き結果だけで証明済みとはしていない。

`BimoduleTensorUnit.lean`のrightUnitLocalizedIsoは既存の閉零単位自然同型を出力の局所化へ送り、
**derivedRightUnitIso**は対角因子が右相対K-flatであることを使って導来圏全体へ降ろす。
元のbimodule対象上での成分は、derivedComposeWithComputationと元の単位射の局所化の合成に一致する。
単位対象の右相対K-flat性はYoneda評価から従い、各HomのA-flat性を仮定していない。

`BimoduleTensorAssociator.lean`のcomposeWithAssociatorIsoは、Q/Rを固定して前のbimodule変数に
自然な既存の結合比較を束ねる。derivedComposeWithPair_facとそのLifting証拠で
二つの降下関手の合成が元の二重合成を降ろすことを固定する。
**derivedAssociatorIso**はQ/Rの右相対K-flat性とその合成閉性から構成した、
derivedComposeWith Q ⋙ derivedComposeWith RとderivedComposeWith (compose Q R)の自然同型。
元の対象上の成分は、指定したfactorizationの計算同型で元のassociatorIsoの局所化を挟む式に一致する。
任意CommRing A・非有界・独立B/C/E/F宇宙・Small.{u} B/C/Eを維持し、Fのsmall性は不要。

未受入の試作では、仮定の型を局所記法で書いたvariable宣言に由来する未証明項が
コンパイル後の宣言の型に残っていることを警告と直接公理監査で検出した。
採用版では当該記法を除去してunderlying対象と仮定の型を明示し、宣言の型を含む
全16宣言の直接監査でsorryAxがないことを確認した。警告付き試作を受入には含めていない。
計算上限の拡大や新規axiomでの回避は行っていない。

Checks.DerivedBimoduleComparison・Checks.DerivedBimoduleTensor・Checks.BimoduleKFlat・
Checks.StageEight・Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功
（3014 jobs、終了コード0、警告なし）。独立宇宙での条件付き比較・自己比較・推移則、
導来圏上の右単位、右相対K-flat二因子の結合比較、ZMod 2の右単位を検査した。
主要16宣言の直接公理監査は標準公理のみ。監査累計3114宣言。
採用版にsorry/admit/新規axiomはない。採用済み引用は0件。
全体文書検査は13 Markdown・320 exposition参照まで進み、担当外の
BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの
未解決参照1件で失敗した。§17.161のolean不足は今回再現しなかった。
共有ルート・共有一般論・該当系列・他チャットの変更は編集していない。

次は導来比較の三角/五角coherenceと固定因子の射に関する自然性、
実際のbimodule解像度からこれらの固定K-flat因子を得る工程へ接続する。
Bᵒᵖ⊗C上のsemifreeから片側の相対K-flat性を得る制限定理、bimodule解像度の存在、
任意の二つの解像度に対する選択独立性、両変数を局所化した導来合成は未完。
local Homの条件を明示した版とdg圏の解像度を使う版を区別し、U12e全受入とはしない。
U12f・U13d/e残部・U14・U15d/e・U16/U17・D4mも未完。U17までの目標を保持する。
共有系列への新しいAPI要求はない。


### 17.163 U12e4：固定因子の射に関する導来結合自然性と導来三角coherence（2026-10-17）

`Derived/BimoduleTensorEvaluation.lean`は、標準局所化の元の対象・射上の計算式を公開する。
derivedComposeWith_map_baseは局所化前の射fの像をcomposeMap(f,id)の局所化として計算し、
derivedComposeWithMap_base_appは固定因子の射gの自然変換をcomposeMap(id,g)の局所化として計算する。
derivedRightUnitIso_base_appとderivedAssociatorIso_base_appは対応する元の単位・結合射の像。
§17.161/162の計算同型を含む式から、構成された標準局所化のfactorizationの同型を
恒等射として計算して得る。任意の別の局所化で同じ厳密な計算が成立すると仮定していない。

`BimoduleTensorNaturality.lean`の**derivedAssociatorIso_naturality**は、Q/Q'・R/R'の
右相対K-flat性の下で、任意の閉零bimodule射g:Q→Q'・h:R→R'に関する結合比較の自然性。
二つの導来自然変換をwhiskerしてから結合比較を行う経路と、結合比較後にcomposeMap(g,h)の
導来自然変換を行う経路が、実際の導来圏を始域とする自然変換として等しい。
準同型や射影性をg/hへの追加仮定にしていない。
局所化の自然変換の外延性で元のPへ戻し、上の計算式とcomposeMapの因子分解、
元のassociatorIso_naturalityを使用する。中間対象の型の別名の書換え失敗は、
composeWith.objのまま扱わず、元のBimoduleCategory.ofの対象を明示して解消した。

`BimoduleTensorTriangle.lean`の**derivedTriangle**は、対角Cと右相対K-flatなQに対する
導来結合比較の後でQの左単位の射を作用させる経路が、前の変数Pの導来右単位を
Qとの導来合成で送る経路に一致する、自然変換としての三角coherence。
元の閉零bimodule射のtriangleを標準局所化に送り、元の対象だけの等式から
局所化上の自然変換全体の等式へ戻す。単に三角の各射の型を揃えただけではない。
任意CommRing A・非有界・独立対象宇宙を保持する。
自然性にはSmall.{u} B/C/Eを、三角にはSmall.{u} B/Cのみを要求し、終域のsmall性は要求しない。

Checks.DerivedBimoduleNaturality・Checks.DerivedBimoduleComparison・Checks.DerivedBimoduleTensor・
Checks.StageEight・Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功
（3017 jobs、終了コード0、警告なし）。独立宇宙での二射の自然性squareと導来三角等式、
ZMod 2でも任意の右相対K-flatなQに対する同じ三角等式を検査した。
主要6宣言の直接公理監査は標準公理のみ。監査累計3120宣言。
今回の実装にsorry/admit/新規axiomはない。採用済み引用は0件。
全体文書検査は13 Markdown・320 exposition参照まで進み、§17.162と同じ担当外の
BhattScholze互換宣言の未解決参照1件で失敗した。共有ルート・共有一般論・該当系列は編集していない。

次は三つの固定K-flat因子に関する導来五角coherenceを、同じ標準局所化の計算式から証明する。
Bᵒᵖ⊗C上のsemifreeから片側の相対K-flat性を得る制限定理、bimodule解像度の存在、
任意の二つの解像度に対する選択独立性、両変数を局所化した導来合成は引き続き未完。
local Homの条件を明示した版とdg圏の解像度を使う版を区別し、U12e全受入とはしない。
U12f・U13d/e残部・U14・U15d/e・U16/U17・D4mも未完。U17までの目標を保持する。
共有系列への新しいAPI要求はない。


### 17.164 U12e5：右K-flat三因子に関する導来五角coherence（2026-10-17）

`Derived/RightKFlatComposition.lean`は既存のRightKFlatBimoduleCategoryを使い、
**rightKFlatCompose**で元のbimodule合成と右相対K-flat合成閉性の証拠を同じ充満部分圏へ束ねる。
新しいbimodule対象や射のモデルを導入していない。
rightKFlatDerivedCompose/Map/Associatorは既存derivedComposeWith/Map/Associatorの型付き表示であり、
既存の標準局所化への対象・射上の計算式へ戻る三つの評価補題も公開する。
単一因子の射と自然変換の二つの評価補題には終域Eのsmall性を要求しない。

`Derived/BimoduleTensorPentagon.lean`の**derivedPentagon**は、右相対K-flatな
Q:C→E、R:E→F、S:F→Gの三つの固定因子に対する自然変換の五角等式。
二辺の経路はDQでR/Sの結合比較をwhiskerし、Qとcompose(R,S)の結合比較へ進む。
三辺の経路はQ/Rの結合比較をDSで送り、compose(Q,R)とSの結合比較を行い、
最後に元のassociatorIso(Q,R,S)が誘導する導来自然変換を作用させる。
両経路は実際のDerivedBimoduleCategory A B Cを始域とする自然変換として等しい。
局所化の自然変換の外延性と元の対象での計算式を使い、既存の閉零bimodule射のpentagonを
標準局所化へ送って証明した。中間のDQ(P)における成分は、元のcompose(P,Q)の対象を
明示して計算する。源PをK-flat対象へ制限していない。
任意CommRing A・非有界・独立B/C/E/F/G宇宙・Small.{u} B/C/E/Fを維持し、Gのsmall性は不要。

Checks.DerivedBimodulePentagon・Checks.DerivedBimoduleNaturality・Checks.DerivedBimoduleComparison・
Checks.DerivedBimoduleTensor・Checks.StageEight・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（3020 jobs、終了コード0、警告なし）。独立対象宇宙での五角等式と、
ZMod 2上でも対象宇宙を独立に保った同じ定理の特殊化を検査した。
特性2の全対象をPUnitに固定して型を再掲する試作検査はカーネル型照合の計算上限に達した。
上限を変更せず、採用する検査は対象宇宙を独立に保つ一般定理の直接特殊化とした。
この検査形の変更で定理の仮定・結論を弱めたり、五角の等式を型の検査だけに置換したりしていない。
主要8宣言の直接公理監査は標準公理のみ。監査累計3128宣言。
今回の実装にsorry/admit/新規axiomはない。採用済み引用は0件。
全体文書検査は13 Markdown・320 exposition参照まで進み、§17.162/163と同じ担当外の
BhattScholze互換宣言の未解決参照1件で失敗した。共有ルート・共有一般論・該当系列は編集していない。

固定した右K-flat因子に対する単位・結合比較、固定因子の射に関する結合自然性、
三角・五角は§17.161〜164で構成できたが、両変数を局所化した導来合成の全受入ではない。
次は積dg圏上の加群と主bimodule圏の射・評価の比較を整え、semifree解像度から
片側の右相対K-flat性を得る制限定理と実際のbimodule解像度の存在へ接続する。
相手側Homのlocal K-flat性を要求する版と、dg圏の解像度を使う版を区別する。
任意の二つの解像度の比較射・選択独立性も残課題とし、U12e全受入とはしない。
U12f・U13d/e残部・U14・U15d/e・U16/U17・D4mも未完。U17までの目標を保持する。
共有系列への新しいAPI要求はない。


### 17.165 U12e6：積dg圏上の加群から主bimodule圏への射・評価・準同型比較（2026-10-17）

`Category/TensorSmall.lean`はSmall.{u} B/CからDGTensorCategory A B Cの対象のSmall.{u}を与える。
Mathlib TransportEnrichmentの対象は元の積の型の別名であり、対象やHomの新モデルを作っていない。
`Module/LeftMapNaturality.lean`は既存LeftModuleCategoryの射の全Hom自然性を、
各複体への評価の前後合成のchain map等式として公開する。

`Bimodule/TensorModuleMaps.lean`の**BimoduleTensorModuleCategory**は、
Bᵒᵖ⊗C上の既存LeftModuleCategory。semifreeを扱うときには既存左右同値により
そのopposite上のRightModuleCategoryへ接続する向きを保持する。
rightMapはこの圏の射を各C対象で右B加群の射へ制限する。
積dg圏の全Hom自然性をdgTensorFirstHomに沿って前合成し、右Bに関する全次数自然性を証明する。
rightMap_left_naturalityはdgTensorSecondHomに沿った同じ制限から、主Hom endでの左C自然性を証明する。
端の対象とmoduleMorphismMkのM/Nを明示し、結合則の書換えによるHom endのequalizer展開は
型を固定したcongrArgとCategory.assocの合成に置換して解消した。
符号付きtensor圏の既存の包含関手を使い、閉零Homだけの通常自然性に弱めていない。

`TensorModuleFunctor.lean`の**BimoduleTensorModule.functor**は、既存の対象変換toBimoduleを
両作用に全Hom自然な閉零射の関手へ拡張する。恒等・合成を保存し、
**evaluationIso**はこの関手を値(b,c)へ評価すると元の積dg圏上の(op b,c)での評価に一致する自然同型。
全対象での評価による射の外延性から、この関手の忠実性も証明した。
`TensorModuleComparison.lean`は既存toTensorFunctorと対象の往復定理を使って
objectPreimage/objectPreimageIsoと本質的全射性を構成する。
**functor_quasiIso_iff**はBimoduleCategory.quasiIsoと元のleftModuleQuasiIsoの保存・反映を与える。
忠実性と本質的全射性だけで圏同値を宣言していない。充満性・逆向きの射の構成は残る。
任意CommRing A・非有界・独立B/C対象宇宙・Small.{u} B/Cを維持する。

Checks.BimoduleTensorModule・Checks.DerivedBimodulePentagon・Checks.DerivedBimoduleNaturality・
Checks.StageEight・Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功
（3023 jobs、終了コード0、警告なし）。積対象のsmall性、忠実性・本質的全射性、
評価の自然同型、元のbimoduleへの対象比較、準同型の保存・反映、合成保存、
ZMod 2でも独立対象宇宙の忠実性を検査した。
主要19宣言の直接公理監査は標準公理のみ。監査累計3147宣言。
今回の実装にsorry/admit/新規axiomはない。計算上限の追加もなく、採用済み引用は0件。
全体文書検査は13 Markdown・320 exposition参照まで進み、§17.162〜164と同じ担当外の
BhattScholze互換宣言の未解決参照1件で失敗した。共有ルート・共有一般論・該当系列は編集していない。

次は逆向きの射の構成と閉零圏の比較を完成し、積dg圏上のsemifree解像度を主bimodule圏へ運ぶ。
その後、各右制限の相対K-flat性を、生成cell・graded-split拡張・逐次余極限から証明する。
必要な相手側Homのlocal K-flat仮定と、dg圏の解像度を使う版を区別する。
bimodule解像度の存在・片側のK-flat性・任意の解像度の比較射と選択独立性・
両変数を局所化した導来合成は未完で、U12e全受入とはしない。
U12f・U13d/e残部・U14・U15d/e・U16/U17・D4mも未完。U17までの目標を保持する。
共有系列への新しいAPI要求はない。

### 17.166 U12e7：積dg圏上の加群と主bimodule圏の閉零圏同値（2026-10-17）

`Bimodule/UncurryNaturality.lean`の**valueMap_uncurry_naturality**は、
実際の閉零bimodule射がuncurryHomに関して全Hom自然であることを証明する。
tensorの純粋斉次元で外延性を適用し、uncurryHomの(p*q).negOnePowの符号を保持したまま、
左右の作用と値のchain mapとの可換式へ帰着した。通常の閉零Homだけの自然性には弱めていない。

`Bimodule/TensorModuleFull.lean`はこの式と元の積dg関手のHomの成分比較から
**preimage_naturality**を与え、**preimageMap**を既存leftModuleMorphismMkで構成する。
preimageMap_evalは各積対象での値が元のbimodule射の評価に一致することを示す。
**map_preimageMap/preimageMap_map**は射の両方向の往復、
**preimageMap_quasiIso_iff**は逆向きの射に関する指定準同型クラスの一致である。
これにより比較関手の**full/isEquivalence**を登録し、**equivalence**を公開した。
§17.165の忠実性・本質的全射性と合わせ、対象データだけの同値を実際の閉零圏の同値へ拡張した。
任意CommRing A・非有界・独立B/C対象宇宙・Small.{u} B/Cを維持する。

Checks.BimoduleTensorEquivalence・Checks.BimoduleTensorModule・Checks.DerivedBimodulePentagon・
Checks.StageEight・Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功
（3023 jobs、終了コード0、警告なし）。独立対象宇宙でのFull/IsEquivalence・射の往復、
ZMod 2での圏同値を検査した。主要10宣言の直接公理監査は標準公理のみ。
監査累計3157宣言。今回の実装にsorry/admit/新規axiomはなく、採用済み引用は0件。
全体文書検査は13 Markdown・320 exposition参照を検査し、従前と同じ担当外の
BhattScholze互換宣言の未解決参照1件で失敗した。共有ルート・共有一般論・該当系列は編集していない。

次は既存左右加群同値と今回の圏同値を使い、積dg圏のopposite上のsemifree解像度を
主bimodule圏の実際の準同型として移送する。その後、右制限の相対K-flat性を生成cell・
graded-split拡張・逐次余極限で証明する。必要な相手側Homのlocal K-flat仮定と
dg圏の解像度を使う版を区別し、global semifreeから各fiber semifreeを無条件に推論しない。
解像度比較・選択独立性・両変数の導来合成は残り、U12e全受入とはしない。
U12f・U13d/e残部・U14・U15d/e・U16/U17・D4mも未完で、U17までの目標を保持する。
共有系列への新しいAPI要求はない。

### 17.167 U12e8：任意bimoduleの積dg圏上semifree解像度と比較（2026-10-17）

`Bimodule/RightModuleComparison.lean`の**rightModuleBimoduleEquivalence**は、
既存左右加群同値と§17.166の圏同値を合成し、(Bᵒᵖ⊗C)ᵒᵖ上の右dg加群圏から
主BimoduleCategory A B Cへの同値を与える。
**rightModuleBimoduleEvaluationIso**は、値(b,c)での評価と元の右加群のop(op b,c)での
評価との自然同型。**rightModuleBimoduleEquivalence_quasiIso_iff**は指定準同型クラスの一致で、
左右同値のcounitの自然性と準同型クラスの同型不変性を使う。

`Bimodule/SemifreeResolution.lean`の**BimoduleSemifreeResolution**は、積dg圏のopposite上の
source加群、その実際のModuleSemifreeFiltration、同値で運んだ主bimoduleからMへの増大射π、
指定quasiIsoの証拠を保持する。各fiberのsemifree性・相対K-flat性は定義の仮定に含めない。
**bimoduleCanonicalSemifreeResolution**は既存の可算cell候補とfiltrationをそのまま利用し、
比較同値のcounitと合成してπを構成する。**exists_semifree_bimodule_resolution**により
任意Mへのこの解像度の存在を証明した。値ごとのπの準同型性も公開した。

`Derived/BimoduleSemifreeComparison.lean`は増大射を同値の充満性で右加群圏へ戻し、
**toProjectiveResolution/augmentation_fac**を与える。既存の射影解像度比較を再利用して
主bimodule圏の実際の**comparison**射とその準同型性を構成した。
**map_eq_of_source_homotopy**は、積dg圏上の全dg自然な加群ホモトピーを、
準同型を反転する関手のcylinderによる既存定理を使って導来bimodule圏で同一視する。
**comparison_fac**は導来bimodule圏で増大射と可換になること、**comparison_unique**は
その可換式を満たす射の像の一意性。**comparisonIso**と**comparisonIso_self/trans**は
この解像度族の比較同型と自己・推移整合性を与える。
Monoの型クラス探索での展開による時間超過は、指定したbimoduleDerivedIsoを使う
Iso.cancel_iso_hom_rightへ置換して解消し、計算上限は増やしていない。
主bimodule圏のホモトピー構造自体の構成や、任意右K-flat置換の比較をこの結果に含めない。

Checks.BimoduleSemifreeResolution・Checks.BimoduleTensorEquivalence・Checks.DerivedBimodulePentagon・
Checks.StageEight・Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功
（3026 jobs、終了コード0、警告なし）。独立B/C対象宇宙、評価自然同型、任意Mへの解像度、
semifree性、値ごとの準同型性、比較射・増大射の可換性・推移整合性とZMod 2の存在を検査した。
主要19宣言の直接公理監査は標準公理のみ。監査累計3176宣言。
今回の実装にsorry/admit/新規axiomはなく、採用済み引用は0件。
全体文書検査は13 Markdown・320 exposition参照を検査し、従前と同じ担当外の
BhattScholze互換宣言の未解決参照1件で失敗した。共有ルート・共有一般論・該当系列は編集していない。

次は右制限の相対K-flat性を証明する。生成cellを右B加群へ制限したときに現れる
相手側Hom_C(c₀,c)のA上K-flat性、graded-split拡張・逐次余極限との整合性を明示する。
この局所Hom条件を課す版とdg圏自体を解像度で置き換える版を区別する。
積dg圏上semifreeを各fiberのsemifreeや無条件の右相対K-flatと同一視しない。
右K-flat置換による両変数導来合成・その計算同型とcoherenceまでU12eの残課題に保持する。
U12f・U13d/e残部・U14・U15d/e・U16/U17・D4mも未完で、U17までの目標を保持する。
共有系列への新しいAPI要求はない。

### 17.168 U12e9：制限関手による分裂・余極限保存と右相対K-flat性の生成cellへの帰着（2026-10-17）

`Module/Restriction.lean`はF:Dᵒᵖ→Eᵒᵖというdg関手に沿った**restrictModule/moduleRestriction**を
構成する。対象は元の豊穣関手への前合成、射は元の全Hom自然性をFのHom射で前合成して作る。
**moduleRestrictionEvaluationIso**、零射保存と指定moduleQuasiIsoの保存を公開した。
閉零射だけの通常自然性へ弱めず、任意可換環・非有界・独立D/E対象宇宙を維持する。
`RestrictionGradedSplit.lean`の**ModuleGradedSplit.restrict**は、元のsection/retractionを
Fの対象で評価し、全斉次作用との自然性をFの斉次Hom射に沿って制限する。
分裂写像のchain map条件を新たに要求せず、inclusion/projectionと分解恒等式を保持する。

`RestrictionColimits.lean`は評価との関手等式と、評価の余極限保存・反映を使い、
**moduleRestrictionIsColimit**とu-smallな対象添字の**PreservesColimitsOfShape**を与える。
図式の射宇宙は独立で、任意の大きい対象添字の余極限を無条件に主張していない。
**moduleRestrictionColimitIso**は選ばれた余極限との標準比較。
`Tensor/RestrictionSemifree.lean`は、すべての自由sphereの制限が相対K-flatという明示的な
仮定hfreeの下で、sphere-free余積・graded-split拡張・網羅的な逐次余極限を順に扱い、
**moduleSemifree_restriction_relativeKFlat**を証明する。
余積の添字は実際のModuleSphereFreePresentation.smallIndexを使って縮小し、
逐次余極限ではModuleCatのAB5を適用する。

`Bimodule/RightRestriction.lean`は第一因子の包含とdgDoubleOppositeから
**tensorRightRestrictionInclusion/tensorRightRestriction**を構成し、右B制限の向きを固定する。
評価は元の積対象op(op b,c)での評価に一致する。
**rightModuleBimoduleRightRestrictionIso**は、選択された左右同値の逆を使う主bimoduleの
右制限とこの直接の制限との、全Hom自然な右B加群同型。
左右同値のcounitの評価成分を使い、二つの恒等Hom射の挿入を除いて自然性を証明した。
`Tensor/BimoduleRestrictionKFlat.lean`は、この同型と上記filtrationの定理を合わせ、
**rightModuleBimodule_semifree_rightRelativeKFlat**と解像度に対する
**BimoduleSemifreeResolution.rightRelativeKFlat_of_cells**を与える。
これらには各生成cellの右制限の相対K-flat性という仮定hcellが明示的に残っている。
localHomKFlatからhcellを証明済みとは扱わず、無条件のbimodule K-flat解像度の存在も主張しない。

Checks.ModuleRestriction・Checks.BimoduleSemifreeResolution・Checks.DerivedBimodulePentagon・
Checks.StageEight・Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功
（3032 jobs、終了コード0、警告なし）。独立対象宇宙・任意の制限dg関手、逐次余極限保存、
graded-split制限、準同型保存、生成cell条件からのsemifree制限、主bimoduleの右制限同型、
ZMod 2での右制限同型を検査した。主要24宣言の直接公理監査は標準公理のみ。
監査累計3200宣言。今回の実装にsorry/admit/新規axiomはなく、採用済み引用は0件。
全体文書検査は13 Markdown・320 exposition参照を検査し、従前と同じ担当外の
BhattScholze互換宣言の未解決参照1件で失敗した。共有ルート・共有一般論・該当系列は編集していない。

次の具体的な証明対象は、c,c₀:C、b₀:B、n:ℤについての右B加群同型
`tensorRightRestriction c (freeSphere (op(op b₀,c₀)) n) ≅
 freeAt b₀ (complexSphere n ⊗ Hom_C(c₀,c))`である（表示ではAと圏引数を省略）。
値のtensor因子を並べ替えるchain同型だけでなく、全Hom作用とのKoszul符号を照合する。
この同型からcomplexSphereとlocalHomKFlat A CによるK-flat生成複体を使い、hcellを証明する。
Hom_BのA上K-flat性をこの片側の主張に追加しない。
dg圏自体を解像度で置き換える経路、両変数の導来合成・計算同型・coherenceはなお残る。
U12e全受入、U12f・U13d/e残部・U14・U15d/e・U16/U17・D4mも未完で、U17までの目標を保持する。
共有系列への新しいAPI要求はない。

### 17.169 U12e10：生成cellの右制限の同型とlocal Hom条件下の右相対K-flat解像度（2026-10-17）

`Module/RestrictionAction.lean`は制限作用・代表作用・単位整数スカラーとの可換性の成分式を
公開する。`Bimodule/RestrictedRepresentableAction.lean`の**restrictedRepresentable_action**は、
(Bᵒᵖ⊗C)ᵒᵖの代表加群を右Bへ制限した作用を純tensor上で計算する。
Hom_B成分hの次数r、Hom_C成分gの次数s、作用する射fの次数pについて、
二つのoppositeと積dg圏の交差符号の指数和はp*(r+s)+s*p+r*p=2*p*(r+s)。
従って、右tensorされたHom_C成分を固定し、Hom_B成分だけに代表作用を施す形になる。
大きな代表加群の定義を一括展開するchangeでの時間超過は、汎用の作用補題へ分割して解消した。
TransportEnrichmentの対象の型を明示し、計算上限を増やしていない。

`Bimodule/RestrictedRepresentable.lean`の**restrictedRepresentableIso**は、この代表加群の
右制限とHom_C(c₀,c)を生成複体とする自由右B加群との同型。
値の写像はsignedSwap Hom_B(b,b₀) Hom_C(c₀,c)で、**hom_eval/inv_eval**も公開した。
元の全Hom自然性は、braidingの(r+p)*sと、tensor加群作用のr*s+p*sを照合して証明する。
`Module/RestrictionTensor.lean`は**restrictModule_tensor/moduleRestrictionTensorIso**と
**tensorModuleAssociatorIso**を与える。後者は既存の全次数cochainに関するassociator自然性を使う。
`Bimodule/RestrictedFree.lean`の**restrictedFreeIso**はこれらを合成し、任意の非有界複体Kについて
右制限を、生成複体K⊗Hom_C(c₀,c)の自由右B加群と同定する。

`Tensor/BimoduleSemifreeKFlat.lean`は**restrictedFree_relativeKFlat**と
**restrictedSphere_relativeKFlat**を証明する。使用条件はKのA上K-flat性と
localHomKFlat A Cのみで、Hom_BのA上K-flat性は要求しない。
これにより§17.168のhcellを具体的に充足し、
**BimoduleSemifreeResolution.rightRelativeKFlat**は実際の任意のsemifree解像度の右相対K-flat性を与える。
**exists_rightRelativeKFlat_bimodule_resolution**はlocalHomKFlat A Cの下で、
任意の主bimodule Mに対する右相対K-flat対象Pと指定準同型P→Mの存在を証明する。
任意可換環・非有界・独立B/C対象宇宙・Small.{u} B/Cを維持する。
local Hom条件なしの主張や、各fiber自体のsemifree性には強めていない。

Checks.BimoduleSemifreeKFlat・Checks.ModuleRestriction・Checks.BimoduleSemifreeResolution・
Checks.DerivedBimodulePentagon・Checks.StageEight・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（3045 jobs、終了コード0、警告なし）。任意Kの自由加群比較、
Hom_B条件を課さない解像度の右相対K-flat性・存在、次数−1と+1のbraidingの負号、
独立対象宇宙とZMod 2での存在を検査した。主要16宣言の直接公理監査は標準公理のみ。
監査累計3216宣言。今回の実装にsorry/admit/新規axiomはなく、採用済み引用は0件。
全体文書検査は共有ルートのExport.lean読込時に、担当外CLMST.SelectedParameterEuler.oleanの
欠落で停止した。今回のdg対象ビルドとは別であり、共有ルート・該当系列は編集していない。

次は右相対K-flatな因子間の準同型に対する合成の不変性を証明し、§17.161以降の固定因子関手を
因子の局所化にも降下させる。既存の第二因子の準同型保存は各fiberのhomotopically projective性を
仮定するため、今回得たrelative K-flat性だけでそれを充足したとは扱わない。
両側解像度を使うtensor比較を証明してから、任意解像度による計算同型・単位/結合coherenceへ接続する。
local Hom条件のないdg圏の解像度経路、U12e全受入、U12f・U13d/e残部・U14・U15d/e・U16/U17・D4mは残る。
U17までの目標を保持し、共有系列への新しいAPI要求はない。

### 17.170 U12e11：K-flat因子間の準同型比較と後因子の部分圏局所化（2026-10-17）

`Module/LeftQuasiIsoInverse.lean`は既存左右加群同値の逆関手による指定準同型クラスの
保存・反映を、counitの自然性と同型不変性から公開する。
`Tensor/LeftKFlatResolution.lean`の**leftModuleRelativeKFlat**は、既存の
toRightOppositeによりopposite上の右相対K-flat性として左条件を定義する。
**leftModuleRelativeKFlat_preserves_rightQuasiIso**は、元の準同型のconeを
objectwise acyclicな左Dᵒᵖ加群と読み、既存swapIsoとtensorのcone保存から準同型保存を証明する。
**exists_leftRelativeKFlat_resolution**は、opposite上の既存cell解像度を左右同値で移送して
任意の左加群への左相対K-flat解像度を与える。local Hom条件は不要。

`Tensor/KFlatComparison.lean`の**rightTensor_relativeKFlat_quasiIso**は、
右相対K-flatなM,N間の任意の準同型fについて、任意の非有界左加群Lとのtensorが準同型になると証明する。
Lを左K-flat解像度P→Lで置き換え、Pに対する上辺と、M,Nに対する両側辺が準同型になる
自然性squareを使う。これは各fiberのhomotopically projective性を仮定する既存結果とは別の定理。
`Tensor/BimoduleKFlatQuasiIso.lean`の**composeMap_second_kFlat_quasiIso/composeMap_kFlat_quasiIso**は、
後の因子の両端の右相対K-flat性だけで、bimodule合成の後変数・両変数の準同型保存を与える。
これらにもlocal Hom条件を追加していない。

`Derived/BimoduleTensorKFlatComparison.lean`の**composeWithKFlatIso/derivedComposeWithKFlatIso**は、
実際の準同型g:Q→Q'から固定因子の合成関手間の自然同型を構成する。
前者の成分は元のcomposeMapを指定局所化へ送った射、後者はそれを前変数の導来圏へ降下したもの。
homの式と恒等・推移整合性を公開した。
`Derived/KFlatBimoduleLocalization.lean`は右相対K-flat充満部分圏への包含から
**rightKFlatQuasiIso**を逆像として固定し、**DerivedRightKFlatBimoduleCategory/rightKFlatToDerived**を定義する。
**rightKFlatDerivedInclusion**はその標準局所化から全DerivedBimoduleCategoryへの比較関手。
**derivedComposeWithFunctor_inverts**により、後因子の準同型を自然同型へ送ることを証明し、
**rightFactorLocalizedComposeFunctor**を構成した。
これは前変数が全導来bimodule圏、後変数が右K-flat部分圏の局所化である関手で、
元の因子関手との厳密なfactorizationと、局所化前の射での計算式を持つ。
射の計算式はfactorizationのFunctor.hcongr_homから得ており、定義上の等式とは扱わない。

`Derived/KFlatBimoduleResolution.lean`はlocalHomKFlat A EとSmall.{u} Eの下で、
任意M:C–E bimoduleの右K-flat解像度を部分圏の対象として束ね、導来増大同型を構成する。
**rightKFlatDerivedInclusion_essSurj**は、これを使った比較関手の本質的全射性。
充満忠実性は未証明なので、全導来bimodule圏との同値や、全後変数での導来双関手の完成とは扱わない。
任意可換環・非有界・独立対象宇宙を保持し、Eのsmallnessは解像度の存在を使う箇所だけに要求する。

Checks.KFlatBimoduleLocalization・Checks.BimoduleSemifreeKFlat・Checks.BimoduleSemifreeResolution・
Checks.DerivedBimodulePentagon・Checks.StageEight・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（3053 jobs、終了コード0、警告なし）。左K-flat解像度、任意左因子とのtensor比較、
因子準同型による導来自然同型、後因子局所化のfactorization、本質的全射性とZMod 2を検査した。
主要26宣言の直接公理監査は標準公理のみ。監査累計3242宣言。
今回の実装にsorry/admit/新規axiomはなく、採用済み引用は0件。
全体文書検査は13 Markdown・320 exposition参照まで進み、担当外BhattScholze互換宣言の
未解決参照1件で失敗した。共有ルート・共有一般論・該当系列は編集していない。

次はrightKFlatDerivedInclusionの充満忠実性を、実際の解像度比較・ホモトピーの同一視から証明する。
既存の解像度のliftは全dg自然なホモトピーまで関手的であり、厳密な関手的解像度として
Mathlibのof_functorial_resolutions系定理へ渡すことはできない。必要ならK-flat部分圏内での
cylinderとホモトピーの同一視を先に整え、得られた比較同値から後因子を全導来圏へ拡張する。
単位・結合coherenceの輸送、local Hom条件のないdg圏解像度の経路もU12eに残る。
U12f・U13d/e残部・U14・U15d/e・U16/U17・D4mは未完で、U17までの目標を保持する。
共有系列への新しいAPI要求はない。

### 17.171 U12e12：K-flat cylinder・ホモトピー同一視と導来置換関手（2026-10-17）

`Tensor/TensorModuleIso.lean`の**tensorModuleIso**は、任意の非有界複体Kについて
`(K⊗M)⊗_D N ≅ K⊗(M⊗_D N)`を構成する。既存のパラメータ付きbalanced族の普遍性から
順逆射を作り、生成元の包含との式**ι_tensorModuleHom/Inv**と両方向の逆関係を証明した。
余極限の一般論を複製せず、元の全作用を保持するbalanced構成を再利用している。
`Tensor/ModuleCylinderKFlat.lean`は**complexKFlat_interval**と
**moduleRelativeKFlat_tensor/modulePrecylinder_relativeKFlat**を与える。
intervalのK-flat性は任意複体をtensorした既存の収縮同値から得る。

`Bimodule/CylinderKFlat.lean`の**rightModuleBimodule_cylinder_rightRelativeKFlat**は、
積dg圏のopposite上の加群Mを主bimoduleへ送った対象が右相対K-flatなら、
Mのcylinderを送った対象も右相対K-flatであることを証明する。
直接の右制限との比較同型、制限とtensorの同型、上記tensor閉性を合成する。
ここにlocal Hom条件は不要であり、対象ごとの独立なホモトピーを仮定していない。

`Derived/KFlatBimoduleHomotopy.lean`は、右相対K-flatな像を持つ積dg加群と射を
**rightKFlatOfModule/rightKFlatOfModuleMap**で実際の充満部分圏へ入れ、恒等・合成を保存する。
**rightKFlat_equalizes_source_boundary**は全dg自然な加群境界をこの部分圏の局所化で同一視する。
上記cylinderが部分圏内にあること、その射影が指定準同型であること、元のcylinder descの両端式を使う。
**rightKFlat_map_eq_of_source_homotopy**は元のK(D)で等しい射に対する同一視の公開形。
全導来bimodule圏へ送った後だけの等式に弱めず、K-flat部分圏自身の局所化で証明している。

`Derived/KFlatBimoduleReplacement.lean`は、比較同値の逆による指定準同型クラスの保存・反映、
**bimoduleSourceProjectiveResolution**と実際の持ち上げ射**rightKFlatReplacementMap**を与える。
localHomKFlat A Cの下で、持ち上げ射をK-flat部分圏の局所化へ送った後の恒等・合成則を
上記ホモトピー同一視から証明し、**rightKFlatReplacementFunctor**を構成した。
これは全閉零bimodule圏から部分圏の局所化への厳密な関手であり、
閉零圏での射の持ち上げ自体が厳密に関手的だとは主張していない。
指定準同型を反転することから、**derivedRightKFlatReplacement**を全導来bimodule圏から
K-flat部分圏の局所化への関手として構成し、**derivedRightKFlatReplacement_fac**を証明した。
Small.{u} B/C、独立対象宇宙、任意可換環、非有界の契約を保持する。

Checks.KFlatBimoduleReplacement・Checks.KFlatBimoduleLocalization・Checks.BimoduleSemifreeKFlat・
Checks.DerivedBimodulePentagon・Checks.StageEight・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（3057 jobs、終了コード0、警告なし）。任意生成複体とのbalanced tensor比較、
interval・加群cylinderのK-flat性、置換関手の型・合成・factorization、ZMod 2を検査した。
主要24宣言の直接公理監査は標準公理のみ。監査累計3266宣言。
今回の実装にsorry/admit/新規axiomはなく、採用済み引用は0件。
全体文書検査は13 Markdown・320 exposition参照まで進み、担当外BhattScholze互換宣言の
未解決参照1件で失敗した。共有ルート・共有一般論・該当系列は編集していない。

次は増大射から、rightKFlatDerivedInclusionとderivedRightKFlatReplacementの両合成の
自然同型を構成する。K-flat部分圏側の自然性はrightKFlat_map_eq_of_source_homotopyを使い、
全導来圏側では既存の準同型局所化でのホモトピー同一視を使う。
射影解像度のlift_fac、圏同値のcounit自然性、増大射の元の定義を組み合わせ、
両同型が証明できるまで充満忠実性や比較同値を宣言しない。
その後、後因子の全導来圏への拡張と単位・結合coherenceを輸送する。
local Hom条件のないdg圏解像度の経路、U12e全受入、U12f・U13d/e残部・U14・U15d/e・U16/U17・D4mは残る。
U17までの目標を保持し、共有系列への新しいAPI要求はない。

### 17.172 U12e13：K-flat局所化比較同値と両変数の全導来bimodule合成（2026-10-17）

`Derived/KFlatBimoduleAugmentation.lean`は実際のK-flat対象Mへの増大射を
**rightKFlatAugmentation**として充満部分圏の射にする。
**rightKFlatAugmentation_naturality**は、射影解像度のlift_facによる全dg自然な
ホモトピーを§17.171の部分圏内の局所化で同一視し、比較同値のcounitを後合成して証明する。
これにより**rightKFlatAugmentationIso**は包含後の置換関手と元の部分圏の局所化関手との自然同型を与える。
`Derived/KFlatBimoduleGlobalAugmentation.lean`は同じ増大射の自然性を全導来圏で証明し、
**rightKFlatGlobalAugmentationIso**を与える。射の計算には包含のfactorizationからの
**rightKFlatDerivedInclusion_map_base**を使い、定義上の射の一致には依存しない。

`Derived/KFlatBimoduleEquivalence.lean`は明示的なLocalization.Liftingとfactorization同型を与え、
上の二つの増大自然同型を局所化へ降下する。
**rightKFlatReplacementUnitIso/rightKFlatReplacementCounitIso**は比較関手と置換関手の両合成を
それぞれの恒等関手に結ぶ自然同型。**rightKFlatDerivedEquivalence**はこれらから
Mathlib CategoryTheory.Equivalence.mkのadjointificationを使い、三角恒等式も備えた圏同値を構成する。
**rightKFlatDerivedInclusion_isEquivalence/fullyFaithful**により、§17.170で未証明だった
比較関手の充満忠実性も証明できた。任意可換環・非有界・独立対象宇宙・Small.{u} B/C、
localHomKFlat A Cの条件を明示的に保持する。局所Hom条件を暗黙の型クラスへ変更していない。

`Derived/BimoduleComposition.lean`の**derivedBimoduleComposeFunctor**は、C–E因子の導来K-flat置換と
既存の後因子局所化関手を合成し、
`DerivedBimoduleCategory A C E ⥤
 (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E)`を構成する。
両変数とも全閉零bimodule圏の指定準同型局所化上にあり、後変数をK-flat対象に限定した関手ではない。
必要条件はlocalHomKFlat A EとSmall.{u} B/C/E。Hom_BやHom_Cの局所K-flat条件はこの関手自体には不要。
**derivedBimoduleComposeKFlatFamilyIso/KFlatIso**は後因子が右K-flatの場合の既存固定因子関手との比較、
**KFlatValueIso**は元のbimodule Pと右K-flat Qを使ったunderived合成の導来像との値の比較。
**derivedBimoduleComposeResolutionComputation**は任意の指定された右K-flat解像度R→Qにより
同じ導来合成関手を計算できる自然同型であり、標準解像度だけの式には限定していない。
**derivedBimoduleComposeKFlatIso_naturality**はK-flat因子間の任意の射に関する比較の自然性。

Checks.DerivedBimoduleComposition・Checks.KFlatBimoduleReplacement・Checks.KFlatBimoduleLocalization・
Checks.DerivedBimodulePentagon・Checks.StageEight・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（3062 jobs、終了コード0、警告なし）。比較関手のFull/Faithful、
圏同値の三角恒等式、独立した四対象宇宙での全導来合成、任意解像度の計算同型、ZMod 2を検査した。
主要21宣言の直接公理監査は標準公理のみ。監査累計3287宣言。
今回の実装にsorry/admit/新規axiomはなく、採用済み引用は0件。
全体文書検査は13 Markdown・320 exposition参照まで進み、担当外BhattScholze互換宣言の
未解決参照1件で失敗した。共有ルート・共有一般論・該当系列は編集していない。

次は全導来合成上の単位・結合比較と三角・五角coherenceを、既存K-flat因子上の図式から輸送する。
K-flat部分圏の局所化比較が同値であることを用い、元の固定因子でのcoherenceと
今回の全後因子上のcoherenceを同一視するための自然性・計算図式を証明する。
さらに解像度計算同型の自己・推移整合性を整理する。
local Hom条件のないdg圏自体の解像度経路、U12e全受入、U12f・U13d/e残部・U14・U15d/e・U16/U17・D4mは残る。
U17までの目標を保持し、共有系列への新しいAPI要求はない。


### 17.173 U12e14：全導来合成の左右単位と任意解像度表示（2026-10-17）

`Derived/BimoduleCompositionResolution.lean`は解像度計算同型の増大射との整合性
**derivedBimoduleComposeResolutionComputation_fac**、恒等解像度での自己整合性、
**derivedBimoduleComposeResolutionComputation_naturality**を証明する。
最後の自然性は増大squareが導来圏で可換であればよく、閉零圏での厳密な可換性や
解像度間の射の準同型性を要求しない。ホモトピーまで可換な射影的持ち上げにも使用できる。

`Derived/BimoduleCompositionRightUnit.lean`は対角bimoduleを右K-flat部分圏の対象
**rightKFlatDiagonal**として束ねる。**derivedBimoduleRightUnitIso**は全導来合成上の
右単位自然同型であり、元の閉零対象での値はK-flat値比較と既存右単位の導来像の合成。
`Derived/BimoduleCompositionLeftUnit.lean`は全導来合成を前因子の対角対象で評価する
**derivedBimoduleLeftUnitFunctor**、任意解像度を使った左単位表示とその自然性を構成する。
標準解像度への持ち上げと導来増大squareを用いて閉零対象上の自然同型を得て、
指定準同型局所化の普遍性から**derivedBimoduleLeftUnitIso**を全導来圏へ降下した。

`Derived/BimoduleCompositionLeftUnitComputation.lean`は局所化前の対象と右K-flat対象での
左単位の計算式、増大射との整合性、**derivedBimoduleLeftUnitIso_resolution_app**を証明する。
これにより全導来左単位は任意の指定右K-flat解像度からの表示と一致する。
異なる二解像度からの表示の一致には、それらの間の比較射を新たに選ぶ必要がない。
任意可換環・非有界・独立対象宇宙・Small.{u} B/Cを保持し、全導来単位の構成には
localHomKFlat A Cを明示的に要求する。条件なしの構成へ強めたとは扱わない。

Checks.DerivedBimoduleUnits・Checks.DerivedBimoduleComposition・Checks.KFlatBimoduleReplacement・
Checks.DerivedBimodulePentagon・Checks.StageEight・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（3066 jobs、終了コード0、警告なし）。左右自然同型、任意解像度の左単位表示と
選択独立性、導来増大squareでの計算自然性、独立対象宇宙とZMod 2を検査した。
主要18宣言の直接公理監査は標準公理のみ。監査累計3305宣言。
今回の実装にsorry/admit/新規axiomはなく、採用済み引用は0件。
全体文書検査は13 Markdown・320 exposition参照まで進み、担当外BhattScholze互換宣言の
未解決参照1件で失敗した。共有ルート・共有一般論・該当系列は編集していない。

次は全導来合成の結合自然同型を構成し、全因子に関する自然性と三角・五角coherenceを証明する。
既存の固定K-flat因子に対するcoherenceから、今回の全導来単位を含む図式への輸送が必要。
左右単位の存在のみでU12eのcoherence受入とはしない。
local Hom条件のないdg圏自体の解像度経路、U12e全受入、U12f・U13d/e残部・U14・U15d/e・
U16/U17・D4mは残る。U17までの目標を保持し、共有系列への新しいAPI要求はない。


### 17.174 U12e15：指定解像度による全導来結合比較と計算図式（2026-10-17）

`Derived/BimoduleCompositionPairResolution.lean`は二つの後因子Q:C–E、R:E–Fと、
指定右K-flat解像度S→Q、T→Rを使う三つの比較を構成する。
**derivedBimoduleComposePairResolutionIso**は全導来関手の逐次適用から既存固定K-flat関手の
逐次適用への自然同型。**derivedBimoduleComposeInnerResolutionIso**は
QとRの全導来合成の値を通常合成S⊗_E Tの導来像へ比較する。
Tによる導来関手がS→Qを同型へ送ることを使い、Q側に追加のfiber射影性を要求しない。
**derivedBimoduleComposeNestedResolutionIso**はこの値の同型を後因子の全導来合成関手へ送り、
右K-flat合成閉性で得たS⊗_E Tによる固定因子関手へ比較する。

`Derived/BimoduleCompositionAssociatorResolution.lean`の
**derivedBimoduleAssociatorResolutionIso**は上の二つの括り方の比較を既存
rightKFlatDerivedAssociatorで結び、全導来合成関手の間の自然同型を構成する。
前因子は全DerivedBimoduleCategory A B C上にあり、その任意の導来射に自然。
後二因子は元の閉零圏の対象を局所化したものとして指定し、それぞれの解像度を入力する。
**derivedBimoduleAssociatorResolutionIso_fac/base_fac**は、得た結合比較を解像度の
計算同型へ送ると、既存K-flat結合比較・元のbimodule結合同型の導来像に戻ることを証明する。
**derivedBimoduleAssociatorBaseIso**は標準解像度による特殊化。
任意可換環・非有界・五つの独立対象宇宙を保持し、Small.{u} B/C/E/Fと
localHomKFlat A E/Fを明示する。

Checks.DerivedBimoduleAssociatorResolution・Checks.DerivedBimoduleUnits・
Checks.DerivedBimodulePentagon・Checks.StageEight・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（3067 jobs、終了コード0、警告なし）。全導来関手間の結合比較、
前因子の任意の導来射に関する自然性、独立対象宇宙とZMod 2を検査した。
主要7宣言の直接公理監査は標準公理のみ。監査累計3312宣言。
今回の実装にsorry/admit/新規axiomはなく、採用済み引用は0件。
全体文書検査は13 Markdown・320 exposition参照まで進み、担当外BhattScholze互換宣言の
未解決参照1件で失敗した。共有ルート・共有一般論・該当系列は編集していない。

次は後二因子の射に関する自然性と解像度選択独立性を証明し、
局所化の全後因子上の結合自然同型へ降下する。その後、§17.173の左右単位を使う
三角恒等式と、全因子上の五角恒等式を固定K-flat計算図式へ比較して証明する。
今回の結合比較は前因子に自然な指定解像度版であり、全因子のcoherenceの完成とは扱わない。
local Hom条件のないdg圏自体の解像度経路、U12e全受入、U12f・U13d/e残部・U14・U15d/e・
U16/U17・D4mは残る。U17までの目標を保持し、共有系列への新しいAPI要求はない。


### 17.175 U12e16：全三因子に自然な導来結合同型（2026-10-17）

`Derived/BimoduleCompositionPairNaturality.lean`は、全導来後二因子の射を逐次合成へ送る
**derivedBimoduleComposePairMap**と、指定解像度比較の自然性を構成する。
`Derived/BimoduleCompositionInnerNaturality.lean`は合成された後因子の射
**derivedBimoduleComposeInnerMap**と、inner解像度計算同型の自然性を証明する。
両自然性は二つの増大squareの導来圏内での可換性だけを要求する。
解像度間の比較射に準同型性を要求せず、閉零圏での厳密な可換性へ強めていない。
innerの証明では前側増大同型の逆を含むsquareを作り、後側解像度比較の自然性と
固定K-flat関手の自然性、元のcomposeMapの合成則を使う。

`Derived/BimoduleCompositionAssociatorNaturality.lean`はnested解像度比較の自然性を証明し、
逐次合成・nested比較・既存の固定K-flat結合自然性を組み合わせて
**derivedBimoduleAssociatorResolutionIso_naturality**を得る。
**derivedBimoduleAssociatorBaseIso_naturality**は標準解像度への特殊化。
後二因子の任意の閉零射を射影的に持ち上げ、既存の全導来増大squareを使用する。

`Derived/BimoduleCompositionAssociatorFunctors.lean`は両括り方を
`D(E,F) ⥤ (D(C,E) ⥤ (D(B,C) ⥤ D(B,F)))`型の関手族
**derivedBimoduleAssociatorSource/Target**としてMathlibのwhiskering関手から構成する。
中間因子の閉零対象上で結合比較を自然同型に束ね、
`Derived/BimoduleCompositionAssociator.lean`で中間因子、最後の因子の順に
指定準同型局所化の普遍性を適用する。
**derivedBimoduleAssociatorIso**は上の両関手族の自然同型であり、全三因子の
任意の導来射に自然。後二因子をK-flat部分圏や局所化前の射に制限していない。
**derivedBimoduleAssociatorIso_outer_base_app/base_app**は、元の後因子を局所化した対象で
評価すると§17.174の標準解像度版の結合比較に戻ることを証明する。
任意可換環・非有界・五つの独立対象宇宙・Small.{u} B/C/E/F、localHomKFlat A E/Fを保持する。

Checks.DerivedBimoduleAssociator・Checks.DerivedBimoduleAssociatorResolution・
Checks.DerivedBimoduleUnits・Checks.DerivedBimodulePentagon・Checks.StageEight・Checks.StageSeven・
既存Spectra.StageTwoの統合ビルドは成功（3074 jobs、終了コード0、警告なし）。
全関手族間の結合自然同型、全三因子の任意の導来射の自然性、標準解像度への計算式、
独立対象宇宙とZMod 2を検査した。主要17宣言の直接公理監査は標準公理のみ。
監査累計3329宣言。今回の実装にsorry/admit/新規axiomはなく、採用済み引用は0件。
全体文書検査は13 Markdown・320 exposition参照まで進み、担当外BhattScholze互換宣言の
未解決参照1件で失敗した。共有ルート・共有一般論・該当系列は編集していない。

次は全導来結合同型を任意の指定K-flat解像度による表示と同一視する。
今回の自然性は比較射と可換squareが与えられた場合の定理であり、任意の二解像度の間の
比較射の存在をまだ含まない。標準射影解像度から任意解像度へホモトピーまで持ち上げて
そのsquareを作り、K-flat表示へ戻る計算式を得る。
その後、§17.173の左右単位と今回の結合同型を使う全因子上の三角・五角恒等式を証明する。
local Hom条件のないdg圏自体の解像度経路、U12e全受入、U12f・U13d/e残部・U14・U15d/e・
U16/U17・D4mは残る。U17までの目標を保持し、共有系列への新しいAPI要求はない。


### 17.176 U12e17：任意解像度による結合同型計算・選択独立性と分担変更（2026-10-17）

ユーザーの分担変更を本書§0へ記録した。「dg-U14」はU14を
`DifferentialGraded/Endomorphism/`で担当し、記録を`dg-theory-u14.md`で管理する。
「dg-U12f/U15d」はU12f/U15dと`dg-theory-scalar-extension.md`を担当する。
このチャットはU12eの受入からU16へ進み、U15e/U17はU12f・U14・U16がそろってから扱う。
この文書§17、既存Derived/KFlatBimodule*とBimodule合成系はこのチャットが管理する。
今回、既存公開APIの名前・型の変更はなく、以下の追加APIだけを導入した。

`Derived/BimoduleResolutionLift.lean`の**bimoduleCanonicalResolutionSourceLift**は、
任意の指定準同型q:N→Mへ標準bimodule解像度から持ち上げるsource dg加群射を与える。
標的Nの射影性・K-flat性、local HomのK-flat性は要求しない。
既存の圏同値のcounitを後合成した**bimoduleCanonicalResolutionLift**は実際のbimodule射。
**bimoduleCanonicalResolutionLift_fac**はその増大三角形の導来圏での可換性を証明する。
持ち上げは全dg自然なホモトピーまで可換であり、閉零圏での厳密可換性や
厳密な関手的解像度を宣言していない。Small.{u} B/C、任意可換環・非有界を保持する。
この追加APIはU12eの任意解像度比較に使用し、後続Morita比較にも再利用できる。

`Derived/BimoduleCompositionAssociatorIndependence.lean`は上の持ち上げを二つの後因子で使い、
§17.175の指定解像度版自然性の二squareを充足する。
**derivedBimoduleAssociatorBaseIso_resolution**は標準解像度版と任意指定解像度版の一致、
**derivedBimoduleAssociatorIso_resolution_app**は全導来結合同型の任意解像度計算式。
二つの任意解像度の間の比較射を入力として要求せず、両者は同じ全導来結合同型に一致する。
**derivedBimoduleAssociatorIso_resolution_fac**は任意解像度での計算比較図式を与える。
`Derived/BimoduleCompositionAssociatorKFlat.lean`は恒等解像度におけるpair/inner/nested比較の
自己整合性を証明し、**derivedBimoduleAssociatorIso_kFlat_fac**で全導来結合同型を
既存rightKFlatDerivedAssociatorへ比較する。後続の三角・五角coherence輸送の入口になる。
こちらはSmall.{u} B/C/E/F、localHomKFlat A E/Fと独立対象宇宙を明示する。

Checks.DerivedBimoduleAssociatorIndependence・Checks.DerivedBimoduleAssociator・
Checks.DerivedBimoduleUnits・Checks.DerivedBimodulePentagon・Checks.StageEight・Checks.StageSeven・
既存Spectra.StageTwoの統合ビルドは成功（3077 jobs、終了コード0、警告なし）。
標的の射影性を要求しない持ち上げ、任意解像度の計算と二解像度間の選択独立性、
独立対象宇宙・ZMod 2を検査した。主要10宣言の直接公理監査は標準公理のみ。
監査累計3339宣言。今回の実装にsorry/admit/新規axiomはなく、採用済み引用は0件。
全体文書検査は13 Markdown・320 exposition参照まで進み、担当外BhattScholze互換宣言の
未解決参照1件で失敗した。共有ルート・共有一般論・該当系列は編集していない。

次は全因子上の左右単位・結合同型の三角・五角恒等式を上記K-flat比較図式から証明する。
local Hom条件のないdg圏自体の解像度経路もU12eに残り、U12e全受入後にU16へ進む。
U12f/U14/U15dは並行担当の成果を受け取り、実装を重複しない。
U13d/e残部、D4mおよび合流後のU15e/U17は未完。共有一般論への新しいAPI要求はない。


### 17.177 U12e18：全導来因子上の三角恒等式（2026-10-17）

`Derived/BimoduleCompositionTriangle.lean`の**derivedBimoduleTriangle_kFlat**は、
右K-flatな後因子Qを全導来圏へ送った場合の三角恒等式を証明する。
§17.176のderivedBimoduleAssociatorIso_kFlat_facと左単位の計算式を使い、
Qへの元の左単位射についてK-flat計算同型の自然性を適用する。
全導来Qの計算同型を後合成して既存derivedTriangleへ帰着し、最後は計算同型の
右単位射に対する自然性と関手の合成保存で全導来右単位の経路へ戻す。
前因子は最初から任意の導来対象であり、局所化前の対象への限定は不要。

`Derived/BimoduleCompositionTriangleFamily.lean`は両経路の共通始域を
**derivedBimoduleTriangleSource**として束ね、**derivedBimoduleTriangleLeft/Right**を
後因子の全導来圏から関手圏への自然変換として構成する。
左経路は結合自然変換を対角因子で評価した後に左単位を適用するもの、
右経路はMathlibのwhiskering関手で右単位を適用するもの。
**derivedBimoduleTriangleFamily_kFlat**は上のK-flat三角恒等式を族の成分の等式にする。
**derivedBimoduleTriangle**はK-flat部分圏の局所化の普遍性で包含への前合成後の
等式を証明し、比較関手の本質的全射性と自然性から全後因子上の自然変換の等式を得る。
**derivedBimoduleTriangle_app**は任意の導来後因子での公開計算式。
この定理は固定K-flat因子だけのcoherenceではなく、全導来合成・§17.173の左右単位・
§17.175の全導来結合同型を使う三角恒等式である。
任意可換環・非有界・独立B/C/E対象宇宙・Small.{u} B/C/E、localHomKFlat A C/Eを保持する。

Checks.DerivedBimoduleTriangle・Checks.DerivedBimoduleAssociatorIndependence・
Checks.DerivedBimoduleUnits・Checks.DerivedBimodulePentagon・Checks.StageEight・Checks.StageSeven・
既存Spectra.StageTwoの統合ビルドは成功（3080 jobs、終了コード0、警告なし）。
全後因子上の自然変換の等式、前後両因子が任意導来対象である成分式、独立対象宇宙・ZMod 2を検査した。
主要7宣言の直接公理監査は標準公理のみ。監査累計3346宣言。
今回の実装にsorry/admit/新規axiomはなく、採用済み引用は0件。
全体文書検査は13 Markdown・320 exposition参照まで進み、担当外BhattScholze互換宣言の
未解決参照1件で失敗した。共有ルート・共有一般論・該当系列は編集していない。
既存BimoduleCompositionLeftUnitComputationの変更は長行の折返しだけで、公開APIの名前・型に変更はない。

次は全因子上の五角恒等式を、§17.176のK-flat結合比較図式と既存derivedPentagonから輸送する。
三角恒等式だけでU12e全受入とはしない。local Hom条件のないdg圏自体の解像度経路も残る。
U12e全受入後はこのチャットでU16を進める。U12f/U14/U15dは並行担当とし、
U15e/U17はU12f・U14・U16がそろってから扱う。共有一般論への新しいAPI要求はない。


### 17.178 U12e19：導来同型で指定したK-flat代表との結合比較と五角経路（2026-10-17）

`Derived/BimoduleCompositionAssociatorComponents.lean`は全結合同型の成分を
**derivedBimoduleAssociator**として公開する。入力は任意の導来Q:C–E、R:E–F、
localHomKFlat A E/Fで、出力は前因子全体に自然な結合同型。
既存derivedBimoduleAssociatorIsoの名前・型は変更せず、その二重評価の入口を追加した。
**derivedBimoduleAssociator_naturality**は任意の導来射f:Q→Q'、g:R→R'を同時に動かす自然性。
§17.175で局所化前の射について証明した自然性を、全局所化の任意の射へ拡張した公開形である。

`Derived/BimoduleCompositionAssociatorComparison.lean`は、導来対象Q/Rと右K-flat対象S/Tを結ぶ
任意の導来同型q:Q≅L(S)、r:R≅L(T)から、逐次合成・合成対象・その作用関手の比較同型
**derivedBimoduleComposePairComparisonIso/InnerComparisonIso/NestedComparisonIso**を構成する。
これらは元のbimodule射としての解像度を要求しない。
五角図式の中間因子Q⊗ᴸRを通常合成の導来像へ比較する場合にも使える。
**derivedBimoduleAssociator_comparison_fac**は、この一般の導来同型による比較と
全導来結合同型が既存rightKFlatDerivedAssociatorを介して可換であることを証明する。
証明は上の全導来射の同時自然性と§17.176のK-flat計算図式を合成する。

`Derived/BimoduleCompositionPentagonPaths.lean`は任意の導来Q:C–E、R:E–F、S:F–Gについて
**derivedBimodulePentagonShort/Long**を構成する。
短経路は後二因子の結合比較を前の合成関手でwhiskerしてから、前二因子の結合比較を適用する。
長経路は前二因子の結合比較を後の合成関手でwhiskerし、次の結合比較と
内側の三因子の結合射を全導来合成関手へ送った射を適用する。
両経路は同じ始域・終域の自然変換として型検査済みであるが、今回それらの一致はまだ証明していない。
任意可換環・非有界・六つの独立対象宇宙・Small.{u} B/C/E/F/GとlocalHomKFlat A E/F/Gを保持する。

Checks.DerivedBimodulePentagonPaths・Checks.DerivedBimoduleTriangle・
Checks.DerivedBimoduleAssociatorIndependence・Checks.DerivedBimodulePentagon・
Checks.StageEight・Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功
（3083 jobs、終了コード0、警告なし）。任意導来同型によるK-flat比較図式、
五角二経路の共通型、独立対象宇宙とZMod 2での全結合比較を検査した。
主要8宣言の直接公理監査は標準公理のみ。監査累計3354宣言。
今回の実装にsorry/admit/新規axiomはなく、採用済み引用は0件。
全体文書検査は15 Markdown・320 exposition参照まで進み、担当外BhattScholze互換宣言の
未解決参照1件で失敗した。共有ルート・共有一般論・並行所有ファイルは編集していない。

次は五角の各頂点を三つのK-flat因子の通常合成へ比較する。
特に内側の全結合射をInnerComparisonIsoで比較すると元の結合射の導来像に戻ること、
短・長の各経路を同じ両端比較で送ると既存derivedPentagonの両経路になることを証明する。
その後、比較同型の可逆性と全後因子への自然性で全五角恒等式を得る。
型が一致しただけではcoherenceを受け入れない。
local Hom条件のないdg圏自体の解像度経路、U12e全受入は残る。
分担は§0のまま、U12e受入後にU16へ進み、U15e/U17は指定の合流条件を待つ。
共有一般論への新しいAPI要求はなく、既存公開APIの名前・型の変更もない。


### 17.179 U12e20：K-flat三因子上の全導来五角恒等式（2026-10-17）

`Derived/BimoduleCompositionPentagonInner.lean`は三つの右K-flat因子Q:C–E、R:E–F、S:F–Gについて、
左括りと右括りの全導来合成の値を通常合成の導来像へ結ぶ
**derivedBimoduleTripleLeftValueIso/RightValueIso**を構成する。
**derivedBimoduleTripleValueIso_associator**は、内側の全導来結合射を両比較で送ると
元のassociatorIsoの導来像に戻ることを証明する。これは§17.178で必要とした内側の比較square。

`Derived/BimoduleCompositionPentagonComparison.lean`は三作用関手の共通始域比較
**derivedBimoduleTripleSourceIso**と、両括り方の作用関手の終域比較
**derivedBimoduleTripleLeftFunctorIso/RightFunctorIso**を構成する。
**derivedBimoduleTripleFunctorIso_associator**は内側のsquareを全導来作用関手へ送り、
通常結合射に関するK-flat計算同型の自然性を合成して、五角の最後の辺の比較を与える。

`Derived/BimoduleCompositionPentagonShort.lean`は、全導来五角の短経路の比較を証明する。
後二因子の結合比較と、導来合成された後因子R⊗ᴸSを扱う§17.178の一般比較を組み合わせる。
途中で、QのK-flat計算同型の射に関するR⊗Sの計算自然性と既存結合同型の自然性を使う。
**derivedBimodulePentagonShort_kFlat_fac**は共通の始域・終域比較を使った短経路の計算式。

`Derived/BimoduleCompositionPentagonKFlat.lean`の**derivedBimoduleTripleSourceAltIso_eq**は、
前二因子から先に計算する始域比較が、短経路で使った後二因子からの始域比較に一致することを証明する。
**derivedBimodulePentagonLong_kFlat_fac**は前二因子の結合比較、一般の導来代表による比較、
内側のsquareを合成して、長経路を同じ両端比較で既存K-flat五角の長経路へ送る。
**derivedBimodulePentagon_kFlat**は短・長の比較と既存derivedPentagonを使い、
可逆な終域比較をキャンセルして**全導来結合同型で作った**五角の二経路の一致を証明する。
前因子は任意の導来対象。後三因子は右K-flat対象の全導来像であり、
任意の全導来後因子への拡張は今回の定理には含めていない。
任意可換環・非有界・六つの独立対象宇宙・Small.{u} B/C/E/F/G、localHomKFlat A E/F/Gを保持する。

Checks.DerivedBimodulePentagonKFlat・Checks.DerivedBimodulePentagonPaths・
Checks.DerivedBimoduleTriangle・Checks.DerivedBimoduleAssociatorIndependence・
Checks.DerivedBimodulePentagon・Checks.StageEight・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（3088 jobs、終了コード0、警告なし）。全導来結合同型を使う五角の二経路の一致、
任意導来前因子への評価、独立対象宇宙とZMod 2を検査した。
主要14宣言の直接公理監査は標準公理のみ。監査累計3368宣言。
今回の実装にsorry/admit/新規axiomはなく、採用済み引用は0件。
全体文書検査は15 Markdown・320 exposition参照まで進み、担当外BhattScholze互換宣言の
未解決参照1件で失敗した。共有ルート・共有一般論・並行所有ファイルは編集していない。

次は五角の二経路を後三因子についても自然な族に束ねるか、各変数の導来同型に関する
可換squareを証明して、全後因子への置換に対する不変性を得る。
各因子のK-flat局所化比較同値と今回のK-flat三因子の五角から、
derivedBimodulePentagonShort=derivedBimodulePentagonLongを任意の全導来後因子で証明する。
それまでは全因子の五角coherenceを受け入れない。
local Hom条件のないdg圏自体の解像度経路とU12e全受入も残る。
U12e受入後はU16へ進み、U15e/U17はU12f・U14・U16がそろってから扱う。
公開APIの名前・型の変更、共有一般論への新しいAPI要求はない。


### 17.180 U12e21：任意の全導来因子上の五角恒等式（2026-10-17）

`Derived/CompositionFamilies.lean`は任意のパラメータ圏Tに対する関手族の点ごとの合成
**compositionFamily**と自然変換の合成**compositionFamilyMap**を、Mathlibのprod'・uncurry・
whiskeringLeftから構成する。**compositionFamilyAssociator**は通常のFunctor.associatorを
成分に持つ自然同型。共有モデル一般論を実装せず、dg合成で使う関手計算の補助を担当範囲に置いた。
Tと各関手の始域・終域の対象宇宙、射宇宙を独立に保つ。

`Derived/BimoduleCompositionFamilies.lean`は導来bimodule族の合成
**derivedBimoduleComposeFamily**、作用関手族の結合比較**derivedBimoduleAssociatorFamily**、
内側の合成対象族の結合比較**derivedBimoduleInnerAssociatorFamily**を構成する。
最後の自然性は、全導来結合同型の後二因子の同時自然性と前因子の自然性を合成して証明する。
`Derived/BimoduleCompositionPentagonFamilies.lean`はこれらを組み合わせて五角の二経路を
**derivedBimodulePentagonShortFamily/LongFamily**として自然変換に束ねる。
**ShortFamily_app/LongFamily_app**は各成分が§17.178の元の五角経路に一致する計算式。
この段階で後三因子を同時に動かした自然性が得られ、個別の射の分解を選ぶ必要がない。

`Derived/BimoduleCompositionPentagon.lean`の**exists_rightKFlat_derived_iso**は任意の全導来対象を
元の右K-flat対象の導来像と結ぶ同型の存在を与える。
K-flat部分圏の局所化比較の本質的全射性と、その局所化関手の本質的全射性を合成する。
**derivedBimodulePentagon**は後三因子の導来圏の積をパラメータ圏に取り、
それぞれのK-flat代表への同型を積圏の一つの同型に束ねる。
K-flat三因子での§17.179の経路一致を使い、上の両自然変換の自然性と
始域関手がその同型を同型へ送ることにより、元の任意の全導来後三因子での経路一致へ戻す。
前因子も任意の導来対象であり、結果はその全導来圏上の自然変換の等式。
これで主全導来合成・左右単位・結合同型について、全因子上の三角・五角coherenceがそろった。
任意可換環・非有界・六つの独立対象宇宙・Small.{u} B/C/E/F/G、localHomKFlat A E/F/Gを保持する。
これらの条件を暗黙化したり、dg圏の解像度なしに除いたりしていない。

Checks.DerivedBimoduleFullPentagon・Checks.DerivedBimodulePentagonKFlat・
Checks.DerivedBimoduleTriangle・Checks.DerivedBimoduleAssociatorIndependence・
Checks.StageEight・Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功
（3091 jobs、終了コード0、警告なし）。任意の全導来四因子の成分式、全後三因子の五角、
dg対象宇宙から独立した対象・射宇宙のパラメータ族、ZMod 2を検査した。
主要12宣言の直接公理監査は標準公理のみ。監査累計3380宣言。
今回の実装にsorry/admit/新規axiomはなく、採用済み引用は0件。
全体文書検査は15 Markdown・320 exposition参照まで進み、担当外BhattScholze互換宣言の
未解決参照1件で失敗した。共有ルート・共有一般論・並行所有ファイルは編集していない。

次はU12eの残条件であるlocal Hom条件なしのdg圏自体の解像度経路を具体化する。
解像度版のbimodule圏と、既存のunderived積dg圏上の主bimodule圏を無条件に同一視しない。
対象・準同型クラス・宇宙を別に固定し、local Hom条件下で主合成との比較を証明する方針。
dg圏の解像度を取っただけで、underivedな積dg圏も自動的に準同値になるとは扱わない。
今回のcoherence完成だけで残る解像度経路を完了とせず、U12e全受入は引き続き未完。
U12e受入後にU16へ進む。U12f/U14/U15dは並行担当、U15e/U17は指定の合流条件を待つ。
既存公開APIの名前・型の変更、共有一般論への新しいAPI要求はない。


### 17.181 U12e22：指定K-flat dg圏解像度と解像度版bimodule合成の入口（2026-10-17）

固定版MathlibのEnriched・PathCategory・Free関連と既存dgコードを再確認した。
通常の自由path圏、自由monoidal圏はあるが、任意の複体豊穣quiverの自由dg圏と
そのcell解像度の存在を返すAPIは確認できなかった。
共有モデル一般論を複製せず、まず解像度を使う対象・射・宇宙を具体化した。

`Resolution/Basic.lean`の**KFlatDGResolution.{u,v,w} A D**は、
source:Type w、DGCategory A source、Small.{u} source、
augmentation:DGFunctor A source D、その準同値の証拠、localHomKFlat A sourceを束ねる。
元のDの対象宇宙vとsourceの対象宇宙wは独立で、D自体のHomにK-flat性を要求しない。
**refl**は元から局所K-flatな小さいDの恒等解像度、**ofQuasiEquivalence**は指定準同値からの構成。
**postcompose**は標的の準同値D→Eを後合成し、同じK-flatなsourceを使う解像度を作る。
いずれも解像度の存在をaxiomや型クラスで仮定したAPIではない。

`Resolution/Bimodule.lean`の**ResolutionBimodule.DerivedCategory A P Q**は、
指定された二解像度のsource間の主bimodule圏をobjectwise準同型で局所化したもの。
元のunderived積dg圏Dᵒᵖ⊗Eのbimodule圏との同値は定義にも仮定にも含めていない。
**diagonal/composeFunctor/rightUnitIso/leftUnitFunctor/leftUnitIso/associator**を既存APIから構成し、
**triangle**と`Resolution/Coherence.lean`の**pentagon**で全導来因子のcoherenceを与える。
元のdg圏にsmallnessやlocal Hom条件を追加せず、指定データのsourceの証拠を使う。
**composeFunctor_refl**は恒等解像度で既存主導来合成に定義通り一致することを証明する。
任意可換環・非有界を維持し、元の各対象宇宙と各source宇宙を独立に指定できる。
公開APIの名前・型は変更せず、解像度版を別名前空間へ追加した。

Checks.DGCategoryResolution・Checks.DerivedBimoduleFullPentagon・Checks.DerivedBimoduleTriangle・
Checks.DerivedBimoduleAssociatorIndependence・Checks.StageEight・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（3094 jobs、終了コード0、警告なし）。元のHom条件を要求しない指定データ版の
合成・三角恒等式、恒等解像度との比較、独立source宇宙・ZMod 2を検査した。
主要14宣言（解像度のデータ型自体と導来圏の型を含む）の直接公理監査は標準公理のみ。
監査累計3394宣言。今回の実装にsorry/admit/新規axiomはなく、採用済み引用は0件。
全体文書検査は15 Markdown・320 exposition参照まで進み、担当外BhattScholze互換宣言の
未解決参照1件で失敗した。共有ルート・共有一般論・並行所有ファイルは編集していない。

未充足の存在契約は、任意のD:Type v、DGCategory A D、Small.{u} Dに対する
`Nonempty (KFlatDGResolution.{u,v,v} A D)`である。**現在この宣言・instanceは存在しない。**
sourceのHomがK-flatとなる自由dg圏/cell解像度を構成し、augmentationのHom準同型と
H⁰本質的全射を証明する必要がある。指定データを受け取る今回の関数だけで存在証明の代用とはしない。
続いて、異なる指定解像度でのbimodule圏・合成の比較と選択整合性、local Hom条件下の
元の主bimodule圏との比較を証明する。underived積の準同値保存を無条件に仮定しない。
この存在と比較はdg側の具体的構成であり、共有モデル一般論へ存在axiomを要求しない。
U12e全受入・U16は未完。分担とU15e/U17の合流条件は§0のまま。
ユーザーの追加指定によりamend・rebase・resetは禁止とし、この区切りも新規コミットで記録する。


### 17.182 U12e23：自由dg圏の有限path tensor・Hom直和・連結chain map（2026-10-17）

`Resolution/Free/Words.lean`は合成・単位を持たない複体値quiver
**FreeDGCategory.ComplexQuiver A D = D → D → Complex A**と非空有限pathのtensor項
**wordTensor**を定義する。内部頂点のリストで非空pathを表し、空リストは一辺pathである。
**wordMap**は辺のchain mapを全次数tensorへ延長し、恒等・合成則を証明する。
**wordTensor_kFlat**は各辺がA上K-flatなら有限path項もK-flatであることを証明する。
**wordConcatenationIso**は接続頂点をリストへ挿入した連結項との括弧比較を、
既存の複体tensorのassociatorから再帰的に構成する。

`Resolution/Free/Hom.lean`の**PathIndex D x y = PLift (x=y) ⊕ List D**は恒等pathと非空pathを区別する。
恒等pathの添字は端点の等式を持つので、異なる端点の間に形式的恒等射を加えない。
**pathTensor**は恒等pathを単位複体へ、非空pathをwordTensorへ送る。
Small.{u} Dから添字集合のSmall.{u}を得て、**homComplex**を全path項の直和として定義する。
**unitInclusion/edgeInclusion/pathInclusion**はそれぞれの包含。
**homComplex_kFlat**は各辺のK-flat性、単位・tensor閉性、ModuleCatのexactな余積から
全path直和のK-flat性を証明する。Dの対象宇宙vをAの宇宙uと同一視しない。

`Resolution/Free/Maps.lean`は恒等pathを固定する**pathMap**と直和への**homMap**を構成し、
path包含との式、unit/edge包含の保存、恒等・合成則を証明する。
`Resolution/Free/Composition.lean`は恒等pathをunitor、非空pathを上の連結同型で処理する
**pathComposition**を構成する。**composition**は既存tensorCoproductDescで二つの直和へ延長したchain map。
各path上の式、非空二pathの式、左単位pathの式と**composition_left_unit**を証明する。
これらの微分は既存の非有界コチェインtensorの内部微分であり、次数制限・体・標数零を課していない。
ε消去やcellの境界を付ける追加微分はまだ導入していない。

Checks.FreeDGPaths・Checks.DGCategoryResolution・Checks.DerivedBimoduleFullPentagon・
Checks.StageEight・Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功
（3098 jobs、終了コード0、警告なし）。一般複体値quiverのHom K-flat性と左単位、
二辺pathへの連結、恒等pathと一辺pathの別添字、独立対象宇宙・ZMod 2を検査した。
主要33宣言の直接公理監査は標準公理のみ。監査累計3427宣言。
今回の実装にsorry/admit/新規axiomはなく、採用済み引用は0件。
全体文書検査は15 Markdown・320 exposition参照まで進み、担当外BhattScholze互換宣言の
未解決参照1件で失敗した。共有ルート・共有一般論・並行所有ファイルは編集していない。

次は右単位・結合則を証明し、このHom直和を主EnrichedCategoryによる自由dg圏へ束ねる。
辺のchain mapを任意のdg圏へ送った場合のpath評価と、その単位・合成保存を証明して、
自由dg圏からのdg関手の普遍性を得る。
その後、既存pathのcycleを新生成元の微分とするcell付加を扱う。
この微分は辺複体の内部微分だけでは表せないので、今回のquiverの単なる直和では代用しない。
cell段階のgraded-split/filtration、Hom K-flat性、増大射のHom準同型とH⁰本質的全射を証明するまで、
KFlatDGResolutionの存在は未完。今回もまだdg圏instanceを宣言しておらず、U12e全受入とはしない。
既存APIの名前・型の変更、共有一般論への新しいAPI要求はない。
分担は§0のまま、U12e受入後にU16へ進む。amend・rebase・resetは使用せず、新規コミットで記録する。


### 17.183 U12e24：自由pathの右単位と任意dg圏への評価・合成保存（2026-10-17）

`Resolution/Free/Units.lean`は**pathComposition_right_unit**、
**composition_path_unit**、**composition_right_unit**を証明する。
恒等path同士の場合はMathlib MonoidalCategory.unitors_equalを使い、
一般の右単位は既存のtensorによる余積保存と各path上の右単位から得る。
これで§17.182のHom直和の連結chain mapは左右単位を満たす。

`Resolution/Free/Evaluation.lean`は任意の標的dg圏E、対象写像o:D→Eと辺のchain map
f(x,y):K(x,y)→Hom_E(o x,o y)から、**wordEvaluation/pathEvaluation/homEvaluation**を構成する。
非空pathは右括りの豊穣順合成、恒等pathはeIdに送る。
**pathInclusion_homEvaluation/unitInclusion_homEvaluation/edgeInclusion_homEvaluation**は
各path、単位、一辺での計算式。標的Eのsmallness、元の辺のK-flat性や有界性は要求しない。
Hom直和での評価だけSmall.{u} Dを使い、単一有限pathの評価には不要。

`Resolution/Free/EvaluationComposition.lean`の**evaluation_tensor_assoc**は、
任意の三つのHomへのchain mapについて、tensorのassociator・その自然性と
豊穣圏のe_assoc'を使って評価の括り方の整合性を証明する。
**wordEvaluation_concatenation**は有限pathの連結tensor同型の後で評価する射が、
二つのpathの評価を標的のeCompで合成する射に一致すると証明する。
**pathEvaluation_composition**は恒等pathの場合を左右単位の自然性から補い、
**homEvaluation_composition**はtensorCoproductの普遍性で全Hom直和へ延長する。
通常順へ無符号で入れ替えず、既存の複体tensor・豊穣順合成の符号契約を維持する。
任意可換環・非有界・独立したD/E対象宇宙を保つ。

Checks.FreeDGEvaluation・Checks.FreeDGPaths・Checks.DGCategoryResolution・
Checks.DerivedBimoduleFullPentagon・Checks.StageEight・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（3102 jobs、終了コード0、警告なし）。右単位、任意標的への評価の単位・合成保存、
有限pathでの連結評価、標的のsmallnessを要求しない型、独立対象宇宙・ZMod 2を検査した。
主要13宣言を完全修飾名で直接公理監査し、標準公理のみ。監査累計3440宣言。
今回の実装にsorry/admit/新規axiomはなく、採用済み引用は0件。
全体文書検査は15 Markdown・320 exposition参照まで進み、担当外BhattScholze互換宣言の
未解決参照1件で失敗した。共有ルート・共有一般論・並行所有ファイルは編集していない。

次はwordConcatenationIsoの三path連結に関する整合性を証明し、
自由path Hom自身のcompositionの結合則をtensorCoproductの普遍性へ降ろす。
標的dg圏で評価した後の結合整合性だけから、元のHomの結合則を推論しない。
左右単位と結合則がそろった時点で主EnrichedCategory instanceを構成し、今回の
homEvaluationを実際のDGFunctorへ束ね、普遍性を証明する。
その後、cycleを新生成元の微分とするcell付加・K-flat性・augmentation準同値の証明へ進む。
自由dg圏instanceとKFlatDGResolutionの存在は引き続き未完で、U12e全受入とはしない。
既存公開APIの名前・型の変更、共有一般論への新しいAPI要求はない。
分担・U16への着手順・U15e/U17の合流条件は§0のまま。履歴は新規コミットで記録する。


### 17.184 U12e25：自由dg圏の結合則・主豊穣instance・厳密普遍性（2026-10-17）

`Resolution/Free/AppendRight.lean`は左pathを固定する**appendPath**、非空左pathに対する
**appendWord**、一辺の先頭作用**edgePrefix**を既存tensorCoproductRightDescから構成する。
各path包含との式、合成の左path制限、先頭作用の恒等/非空pathでの式を証明した。
`Resolution/Free/AppendRecursion.lean`の**appendWord_cons**は、左pathの連結を先頭一辺と短いpathへ分解する。
右pathが恒等pathの場合にはrightUnitor_tensor_homを使い、非空の場合にはwordConcatenationIsoの再帰式を使う。

`Resolution/Free/PrefixAssociativity.lean`は**appendPath_edgePrefix**で有限左path上の先頭作用と
合成の整合性を証明し、tensorと余積の普遍性により**composition_edgePrefix**へ拡張する。
`Resolution/Free/Associativity.lean`はpathの長さに関する帰納法と既存tensorCarry_assocから
**appendWord_assoc**を証明し、恒等pathの場合をunitor自然性で補って**appendPath_assoc**を得る。
**composition_assoc**は左のpath直和に関する射の判定から全Hom連結の結合則を与える。
評価先での等式から元のHomの結合則を仮定せず、元の連結chain map自身について証明した。

`Resolution/Free/Category.lean`はquiver Kと結び付けた対象型**Objects A D K**を定義し、
既存のHom直和・単位・合成・左右単位則・結合則を使って**dgCategory**を
主Mathlib EnrichedCategory (Complex A)のinstanceとして構成する。
元のDのinstanceは変更しない。**homKFlat**は辺のK-flat性から全HomのK-flat性を与える。
**lift**は指定対象写像・辺のchain mapから実際のDGFunctorを作り、
§17.183の評価の単位・合成保存をその法則に使用する。

`Resolution/Free/Reconstruction.lean`は二つのpathの連結による生成を使って、任意のdg関手の
path上の値を生成辺で再構成する。**functor_word/functor_path**、
**homEvaluation_reconstruction**と**lift_reconstruction**を証明した。
`Resolution/Free/Universal.lean`の**GeneratorMap**は対象写像と生成辺のchain mapだけを束ねる。
**restrict/extend**と両方向の逆関係から
**universalEquiv : DGFunctor A (Objects A D K) E ≃ GeneratorMap A D E K**を構成し、
**extension_unique**で厳密な延長一意性を公開する。
任意可換環・非有界・独立D/E対象宇宙・Small.{u} Dを維持し、標的Eのsmallnessは不要。
生成辺のK-flat性はhomKFlatの結論にだけ要求し、自由dg圏・普遍性の構成自体には追加しない。

Checks.FreeDGUniversal・Checks.FreeDGEvaluation・Checks.FreeDGPaths・Checks.DGCategoryResolution・
Checks.DerivedBimoduleFullPentagon・Checks.StageEight・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（3115 jobs、終了コード0、警告なし）。主dg圏instance、Hom K-flat性、
生成辺からの一意なdg関手延長、再構成、独立対象宇宙とZMod 2を検査した。
主要32宣言（dg圏instance、ObjectsとGeneratorMapの型を含む）を完全修飾名で直接公理監査し、標準公理のみ。
監査累計3472宣言。今回の実装にsorry/admit/新規axiomはなく、採用済み引用は0件。
全体文書検査は15 Markdown・320 exposition参照まで進み、担当外BhattScholze互換宣言の
未解決参照1件で失敗した。共有ルート・共有一般論・並行所有ファイルは編集していない。

次はHomのcycleを持ち上げるK-flatな生成辺複体から自由dg圏への初期増大関手を作り、
増大射のHomホモロジーの全射性を証明する。
さらに、既存pathのcycleを新生成元の微分とするcell付加を行い、余分なホモロジーを消す。
その導分の二乗零と全作用のLeibniz、cell段階のK-flat性、増大射のHom準同型、
H⁰本質的全射を証明するまでKFlatDGResolutionの存在は未完。
自由dg圏とその厳密普遍性の完成を、dg圏解像度の存在やU12e全受入の代用とはしない。
公開APIの名前・型の変更、共有一般論への新しいAPI要求はない。
分担・U16への着手順・U15e/U17の合流条件は§0のまま。履歴は新規コミットで記録する。


### 17.185 U12e26：全cycle被覆とK-flat自由dg圏からの初期増大関手（2026-10-17）

前回のゴールターンは分担・計画確認のみで実装進捗がなかったため、
§17.184の次工程を実装した。LeanとMathlibの固定版を再確認し、共有モデル一般論は追加していない。

`Resolution/CycleCover.lean`の**ComplexCycleIndex/complexCycleCover**は、複体Kの
全整数次数の全cycleを添字とするsphereの直和である。
**complexCycleCoverπ**は各sphereの生成元を指定cycleへ送り、
**complexCycleCoverLift/complexCycleCoverLift_π/complexCycleCover_cycle_lift**が厳密な持ち上げを与える。
**complexCycleCover_kFlat**はsphereのK-flat性とexactな余積から従う。
一般のchain mapについての**complexCyclesMap_epi_of_cycle_lift**は厳密なcycle持ち上げから
MathlibのcyclesMapの全射性を証明し、**complexHomologyMap_epi_of_cycle_lift**が
homologyMapの全射性へ移す。準同型性や標的のK-flat性を仮定しない。

`Resolution/Initial.lean`の**DGCategoryCycleCover.edges/Source/augmentation**は、
各Homの上記被覆を生成辺とする自由dg圏と、対象を固定する実際のdg関手を構成する。
**source_homKFlat**、**sphereLift/sphereLift_augmentation/cycle_lift**、
**cyclesMap_epi/homologyMap_epi**を証明した。
**augmentation_essSurj**は対象写像が恒等であることからH⁰の本質的全射性を与える。
任意の可換環A:Type u、非有界コチェイン、D:Type v、Small.{u} Dを維持する。
元のHomのlocal K-flat性、体、有界性は不要であり、uとvは独立である。
公開APIの名前・型は変更せず、新規APIを追加した。

Checks.DGCategoryInitial・Checks.FreeDGUniversal・Checks.DGCategoryResolution・
Checks.DerivedBimoduleFullPentagon・Checks.StageEight・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（3116 jobs、終了コード0、警告なし）。独立対象宇宙、ZMod 2、
元のHomへのflatness仮定なしの全cycle持ち上げ・K-flat性・H⁰本質的全射性を型検査した。
主要24宣言（被覆・sourceの型を含む）の直接公理監査は標準3公理のみ。監査累計3496宣言。
今回の実装にsorry/admit/新規axiomはなく、採用済み引用は0件。
全体文書検査は15 Markdown・320 exposition参照を検査し、担当外の
BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの
未解決参照1件で失敗した。共有ルート・共有一般論・並行所有ファイルは編集していない。

次は増大射で境界へ送られるsourceのcycleを添字として、そのcycleより次数が1低い新生成元を付加する。
target側の原始元を指定したsphere/diskの可換squareを作り、既存pathを境界とする
追加微分の二乗零・Leibniz、filtrationとK-flat性、逐次余極限のHom準同型性を証明する。
初期増大のホモロジー全射性は単射性を含まず、準同値とは宣言していない。
KFlatDGResolutionの一般存在・解像度比較、U12e全受入・U16は引き続き未完。
U12f/U14/U15dの並行所有範囲には触れず、U15e/U17は§0の合流条件を保持する。


### 17.186 U12e27：境界cellの増大squareと逐次充填によるHom準同型判定（2026-10-17）

`Resolution/BoundaryCells.lean`の**ComplexBoundaryCell A f**は、任意の複体射f:K→Lについて
degree q、Kの次数q+1のcycle z、Lの次数qの原始元b、db=fzの証拠を束ねる。
f z=0に限定せず、ホモロジーの核の全代表を含める。
**attachingMap**はsphere(q+1)→K、**targetDiskMap**は生成元をbへ送るdisk(q)→Lであり、
**augmentation_square**がsphere境界包含との可換squareを証明する。
**HasFilling**はKでの原始元tをdt=zかつft=bとともに要求する。
**quasiIso_of_filling**は全cellの充填から既存の具体的cone判定でfの準同型性を得る。
これは条件付きの判定であり、充填の存在を宣言したものではない。
**DGCategoryBoundaryCells.Index**は全source対象対のcell添字である。
sourceがSmall.{u}なら添字もSmall.{u}で、targetの対象集合のsmallnessは不要。

`Resolution/BoundarySequence.lean`の**ComplexBoundaryCell.sequential_filling**は、
複体列F:ℕ→Complex A、二つのcocone s/a、sのIsColimitの証拠を受け取る。
各有限段の全cellが直後の段階でtransition後のcycleを境界とし、指定target原始元へ送られるなら、
IsColimit.descで得る最終増大射の全cellも埋まると証明する。
既存のfiltered余極限のcycle有限段表示、cocone可換性、chain mapの微分交換を使う。
transitionの単射性、増大の次数ごとの全射性、有界性、flatnessは不要。
**sequential_quasiIso**が最終増大射の準同型性を与える。
今後のdg圏cell列の各Homに適用する判定であり、dg圏cell列自体を仮定から取り出してはいない。

Checks.DGBoundarySequence・Checks.DGCategoryInitial・Checks.FreeDGUniversal・
Checks.DGCategoryResolution・Checks.DerivedBimoduleFullPentagon・Checks.StageEight・Checks.StageSeven・
既存Spectra.StageTwoの統合ビルドは成功（3119 jobs、終了コード0、警告なし）。
任意source/target宇宙、target smallness不要のcell添字、ZMod 2と初期増大のcell添字を検査した。
主要11宣言（cellのデータ型と充填条件を含む）の直接公理監査は標準3公理のみ。
監査累計3507宣言。今回の実装にsorry/admit/新規axiomはなく、採用済み引用は0件。
全体文書検査は15 Markdown・320 exposition参照を検査し、§17.185と同じ担当外の
BhattScholze互換宣言の未解決参照1件で失敗した。共有ルート・並行所有ファイルは編集していない。

残る中心作業は、既存pathのcycleを新生成元の微分とする実際のdg圏cell付加である。
追加微分の二乗零・全合成のLeibniz、filtrationによるHom K-flat性、列の構成と
今回の準同型判定への接続、解像度選択の比較が未完。境界squareや判定だけで存在証明とはしない。
公開APIの名前・型の変更と共有一般論への新しい要求はない。
分担とU16への着手順、U15e/U17の合流条件は§0のまま保持し、履歴は新規コミットで記録する。


### 17.187 U12e28：任意次数・別端点cellのpath項と指定境界置換作用素（2026-10-17）

既存dg商の有限path、内部Hom、ε消去、全次数tensor Homを再確認した。
収縮記号に限定せず、任意整数次数かつ異なる始点・終点を持つcell付加へ進めた。
`Resolution/Cells/Paths.lean`の**DGCellAttachment.Family**はcell添字I:Type wごとの
source/target:D、degree:ℤ、次数degree+1のboundary cycleを保持する。
**generator/term/generatorTerm**はsphereによる生成元と、既存Homを間に挟む有限path項。
空語は既存Homで、非空語の先頭はHom(x,source i)⊗(sphere(degree i)⊗tail(target i,y))。
**internalHom/inclusion/originalHom/generatorInclusion/internalHom_ext**は全語の直和とその包含・外延性。
添字IのSmall.{u}だけを使い、Dの対象集合のsmallnessは不要で、u/v/wは独立。
**term_kFlat/internalHom_kFlat**は既存Homのlocal K-flat性から内部微分版のK-flat性を証明する。
追加微分後のK-flat性とは区別する。**boundaryFamily**は§17.186の全境界cellをこの族へ変換する。

`BoundaryCochain.lean`の**boundaryCochain**は次数degreeの生成元を指定境界へ送る次数+1 cochain。
**boundaryCochain_closed/boundaryCochain_generator**で閉性と生成元の像を証明する。
**replaceMiddle/replaceMiddle_closed/replaceMiddle_apply**は左右の任意非有界複体の間で境界を挿入し、
左因子の次数pを通る符号(-1)^pを全次数tensor Homから得る。生成元を次数−1に制限しない。
`PathComposition.lean`の**prependMap/appendMap**は隣接する既存Homのみを豊穣合成するchain map。
`BoundaryFaces.lean`の**replaceFirst/replaceFace**は各生成元の境界置換を構成し、内部Hom微分での閉性を証明する。
`BoundaryOperator.lean`の**replaceSummand/replaceRow**は短いpathへの包含後の有限和。
**replacementToShift/replacement**は閉性付き有限和を全直和へ貼り合わせる。
**replacement_closed/replacement_precomp/replacement_originalHom**を証明した。
**replacement_square_precomp**は二重置換を最初のfaceと短いpathの置換和へ分解し、
**replacement_square_originalHom/replacement_square_singleton**は長さ0/1上での二乗零を与える。

Checks.DGCellBoundaryOperator・Checks.DGBoundarySequence・Checks.DGCategoryInitial・Checks.FreeDGUniversal・
Checks.DGCategoryResolution・Checks.DerivedBimoduleFullPentagon・Checks.StageEight・Checks.StageSeven・
既存Spectra.StageTwoの統合ビルドは成功（3125 jobs、終了コード0、警告なし）。
任意次数と別端点、独立宇宙、Dのsmallness不要の型、ZMod 2上の次数7の生成元を検査した。
主要37宣言（Familyの型を含む）の直接公理監査は標準3公理のみ。監査累計3544宣言。
今回の実装にsorry/admit/新規axiomはなく、採用済み引用は0件。
全体文書検査は共有ルートが参照する担当外CommutativeAlgebra.LocalizationComparisonBoundsの
olean不在で参照収集前に停止した。対象ビルドは成功しており、担当外のビルド・ファイルは変更していない。

次は二つの生成元の境界置換の反交換、有限和の相殺によるreplacementの二乗零、
追加微分d+replacement、合成のLeibnizと主dg圏instance、増大関手を構成する。
内部微分版のK-flat性や長さ0/1の二乗零を全体の代用とせず、filtrationによる最終HomのK-flat性も証明する。
実際のcell付加の完成、一般KFlatDGResolutionの存在・比較、U12e全受入・U16は引き続き未完。
公開APIの名前・型の変更と共有一般論への新しい要求はない。分担と合流条件は§0のまま。


### 17.188 U12e29：先頭Hom作用の結合・単位と指定境界挿入の反交換（2026-10-17）

`Resolution/Cells/PathAction.lean`の**Family.prependMap_assoc/prependMap_left_unit**は、
任意次数・別端点cellの有限path上で、既存Homの先頭作用が結合則と単位則を満たすことを証明する。
既存の具体的複体tensorの結合・単位補題と元のdg圏の豊穣合成則を使い、境界を無符号で交換しない。
**prependMap_tail_cochain**は先頭生成元を保持した後方tensor部分の任意次数cochainに対する自然性。

`BoundaryInterchange.lean`の**Family.replaceMiddle_tail_anticommute**は、
指定境界を挿入する次数+1 cochainと、その後ろの任意の次数+1 cochainとの反交換を証明する。
既存のtensorCochain_odd_anticommuteとtensorLeftHom_cochain_anticommuteを再利用する。
負号は二つの作用素の次数+1に由来し、生成元自身の次数を−1へ制限しない。
任意可換環・非有界・独立D/I宇宙を保ち、この有限pathの証明にSmallやlocal K-flat仮定は不要。

Checks.DGCellBoundaryInterchange・Checks.DGCellBoundaryOperator・Checks.DGBoundarySequence・
Checks.DGCategoryInitial・Checks.FreeDGUniversal・Checks.DGCategoryResolution・
Checks.DerivedBimoduleFullPentagon・Checks.StageEight・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（3130 jobs、終了コード0、警告なし）。追加4宣言の直接公理監査は標準3公理のみ。
監査累計3548宣言。今回の実装にsorry/admit/新規axiomはなく、採用済み引用は0件。
全体文書検査の直近結果は§17.187の担当外olean不在による停止である。

次はprependMapと境界置換の全位置での可換性を証明し、先頭生成元と任意後方生成元の
二重置換の反交換へ進む。隣接する生成元の場合にも元の豊穣合成の結合則を使う。
二乗零の一般版、d+replacementと実際のdg圏cell付加、最終K-flat性、解像度の存在・比較は未完。
この反交換補題だけでU12eを受入済みとせず、U12e受入後のU16と合流後のU15e/U17の目標を保持する。
公開APIの名前・型の変更と共有一般論への新しい要求はない。§0の分担を維持する。


### 17.189 U12e30：左端境界挿入への分解と全位置のHom作用自然性（2026-10-17）

`Complexes/TensorJoinActionNaturality.lean`の**tensorJoin_action_cochain**は、
前方二因子の合成と結合的な作用について任意次数cochainの自然性を証明する。
具体的な非有界複体tensor上の補題であり、共有の任意V豊穣一般論を複製しない。
型を小さくした補題を再利用することで、以下は標準heartbeat内で検査できる。

`Resolution/Cells/BoundaryHead.lean`の**Family.replaceHead**は、左端生成元を指定境界に置き換え、
後続pathへ元のHomとして作用させる次数+1 cochain。**replaceHead_closed**が閉性を与える。
**replaceFirst_eq_head**は先頭置換をこの左端操作と既存Hom作用へ分解し、
**prependMap_replaceHead/prependMap_replaceFirst**は前方Hom合成との自然性を証明する。
元の豊穣合成とprependMapの結合則を使うため、隣接cellを扱う際にも適用できる。

`BoundaryNaturality.lean`の**replaceFace_nil/replaceFace_zero/replaceFace_succ**は既存再帰定義の計算式。
**prependMap_tail_hom/prependMap_suffix_hom**は後方自然性を全Hom複体のchain mapの等式にまとめ、
**prependMap_replaceFace**が全ての置換位置で既存Hom作用との可換性を与える。
生成元の次数・端点の制限、Smallやlocal K-flat仮定は不要。公開APIの名前・型の変更はない。

Checks.DGCellBoundaryNaturalityの対象ビルドと主要12宣言の直接公理監査が成功。
全宣言の公理は標準3公理のみ。監査累計3560宣言。
今回の実装にsorry/admit/新規axiomはなく、採用済み引用は0件。
全位置の自然性を得ただけでcell付加を受入済みとはしない。
次に二重置換の反交換・相殺と最終Hom微分へ接続する。分担と合流順は§0のまま保持する。


### 17.190 U12e31：全pathの境界置換二乗零と追加微分後の非有界Hom複体（2026-10-17）

`Resolution/Cells/BoundaryHeadInterchange.lean`の**Family.replaceHead_face_anticommute**は、
左端の境界挿入と任意後方位置の置換の反交換を全位置のHom作用自然性から証明する。
**replaceFirst_face_anticommute**は先頭Homを戻した反交換で、隣接生成元の場合も含む。
生成元を次数−1に限定せず、各端点を独立に保持している。

`DoubleFaces.lean`の**replaceFace_succ_comp**は先頭を保持する二重置換の再帰式。
**DoubleFace/doubleFace/negateDoubleFace/prefixDoubleFace**は終域の語付き次数2 cochainを保持する。
**prefixDoubleFace_negate/doubleFace_cons_succ/doubleFace_cons_zero/doubleFace_swap_of_le**により、
異なる二位置の置換順を交換すると、終域のpathも含めて負になることを証明した。
`DoubleFaceSum.lean`の**includeDoubleFace/includeDoubleFace_negate/replacementPair**は全Hom直和への包含、
**replacementPair_swap_of_le/replacementPair_swap/replacementPair_double_sum_zero**は有限二重和の相殺。
既存dg商の純粋な有限和対合補題を再利用し、2の可逆性を要求していない。

`BoundarySquare.lean`の**pathCochain_ext**は任意次数cochainの各path上での判定。
**replacement_square_precomp_double_sum**で二重置換を有限二重和へ移し、
**replacement_square_zero**で全Hom直和上の作用素の二乗零を証明した。
長さ0/1に限定した結果や終域の等式を仮定した結果ではない。
`Differential.lean`の**attachedHom**は既存perturbComplexへ実際に証明した閉性と二乗零を渡し、
内部微分+replacementを微分とする非有界複体を構成する。
**attachedHom_X/attachedHom_d**が次数成分と微分式を与え、
**originalHomInclusion/originalHomInclusion_f**は追加微分後もchain mapとなる元のHom包含を与える。
Small.{u} Iだけを直和に要求し、Dの対象集合のsmallness、元のHomのK-flat性や有界性は不要。

Checks.DGCellDifferential・Checks.DGCellBoundaryNaturality・Checks.DGCellBoundaryOperator・
Checks.DGBoundarySequence・Checks.DGCategoryInitial・Checks.FreeDGUniversal・Checks.DGCategoryResolution・
Checks.DerivedBimoduleFullPentagon・Checks.StageEight・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（3141 jobs、終了コード0、警告なし）。独立宇宙、任意可換環・非有界、
ZMod 2とflatness仮定なしの最終複体・元のHomのchain map包含を型検査した。
新規25宣言と§17.189の12宣言を含む37宣言の直接公理監査はすべて標準3公理のみ。
監査累計3585宣言。今回の実装にsorry/admit/新規axiomはなく、採用済み引用は0件。
全体文書検査は15 Markdown・320 exposition参照を検査し、担当外の
BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの
未解決参照1件で失敗した。共有ルート・共有一般論・並行所有ファイルは編集していない。

次は有限pathの合成・単位・結合則とreplacementのLeibnizを全直和へ拡張し、
attachedHomを主EnrichedCategoryのHomとして束ねる。指定原始元への増大関手とcellの充填式を証明し、
長さfiltrationから追加微分後のHom K-flat性、列の余極限と§17.186の準同型判定へ接続する。
今回のattachedHomだけでdg圏cell付加や解像度の一般存在を受入済みとはしない。
解像度比較、U12e全受入、受入後のU16と合流後のU15e/U17は未完。
公開APIの名前・型の変更と共有一般論への新しい要求はない。§0の分担を維持する。


### 17.191 U12e32：任意次数cell pathの内部合成・左右単位・結合則（2026-10-17）

`Resolution/Cells/InternalComposition.lean`の**Family.internalComposition**は、有限path連結を
既存tensorCoproductDescで二つのHom直和へ延長する内部微分に関するchain map。
**internalComposition_inclusion/internalComposition_original_left/internalComposition_original_original**は
各二path・元のHomの計算式。**appendRight/appendRight_inclusion/internalComposition_left_inclusion**は
左有限pathを固定する全右pathへの合成と、その全合成への包含を与える。
**internalPrepend/internalPrepend_inclusion/internalIdentity/internalComposition_left_unit**で
元のHomの先頭作用・恒等射・左単位則を構成した。

`Prefix.lean`の**prefixCofanIsColimit/prefixPath/prefixPath_inclusion/prefixPathCochain_ext**は、
先頭Homと任意次数生成元を保った全path包含と、任意次数cochainの判定を与える。
`AppendRecursion.lean`の**appendRight_cons**は連結の再帰式。
`InternalUnits.lean`の**appendRight_right_unit/internalComposition_right_unit**で右単位則を証明する。

`AppendPrepend.lean`の**appendMap_prepend**、`AppendRightPrepend.lean`の**appendRight_prepend**、
`CompositionPrepend.lean`の**internalComposition_prepend**は先頭Hom作用との結合整合性。
`CompositionPrefix.lean`は各pathへの制限から**internalComposition_prefixPath**を証明する。
`AppendRightAssociativity.lean`の**appendRight_assoc**は左pathに関する帰納法と既存tensorCarry_assocを使い、
`InternalAssociativity.lean`の**internalComposition_assoc**が全Hom直和上の結合則を与える。
既存dg商のpath証明を再確認し、各生成元のsourceとtargetを別々に、sphere次数を任意整数に保った。
Small.{u} Iだけを直和に使い、Dのsmallness、元のHomのK-flat性・有界性は要求しない。
公開APIの名前・型は変更せず、新規APIを追加した。

Checks.DGCellInternalComposition・Checks.DGCellDifferential・Checks.DGCellBoundaryNaturality・
Checks.DGCellBoundaryOperator・Checks.DGBoundarySequence・Checks.DGCategoryInitial・Checks.FreeDGUniversal・
Checks.DGCategoryResolution・Checks.DerivedBimoduleFullPentagon・Checks.StageEight・Checks.StageSeven・
既存Spectra.StageTwoの統合ビルドは成功（3154 jobs、終了コード0、警告なし）。
任意次数・別端点、独立対象/添字宇宙、元のHomのflatness仮定なしの単位/結合則、
ZMod 2上の次数7の生成元を型検査した。主要28宣言の直接公理監査は標準3公理のみ。
監査累計3613宣言。今回の実装にsorry/admit/新規axiomはなく、採用済み引用は0件。
全体文書検査は15 Markdown・320 exposition参照を検査し、§17.190と同じ担当外BhattScholze互換宣言の
未解決参照1件で失敗した。共有ルート・共有一般論・並行所有ファイルは編集していない。

これらは内部微分に関する合成である。追加微分後の合成にはreplacementのLeibnizを別途証明し、
attachedHom間のchain mapへ移す必要がある。最終dg圏instance、cell生成元の充填式と増大、
filtrationによる最終Hom K-flat性、列と解像度の存在・比較、U12e全受入・U16は未完。
内部合成の結合則だけで最終dg圏の受入とせず、§0の分担とU15e/U17の合流条件を維持する。


### 17.192 U12e33：元のHomの先頭作用のLeibniz則と追加微分後のchain map（2026-10-17）

`Resolution/Cells/TensorPathCochainExt.lean`の**Family.tensorLeftPathCochain_ext**は、
左tensorした全path直和上の任意次数cochainの各pathによる判定。
`PrependBoundaryRows.lean`の**prependMap_replaceSummand/prependMap_replaceRow**は、
元のHomの先頭作用と、任意位置の境界置換項・その有限和の自然性を証明する。
`PrependBoundary.lean`の**internalPrepend_replacement**は全直和上の作用とreplacementの可換式で、
左側の元のHomには追加置換がない場合のLeibniz基底式である。
**internalPrepend_replacement_apply**はその斉次成分で、右側の置換に(-1)^pを保持する。

`PrependDifferential.lean`の**internalPrepend_total_d_apply**は内部chain mapの微分交換と
上の置換式を加え、d+replacementに関する符号付きLeibniz則を証明する。
**attachedPrepend : Hom_D(x,y) ⊗ attachedHom(y,z) → attachedHom(x,z)**は、
それを既存tensorLiftへ渡した、追加微分後の実際のchain map。
**attachedPrepend_ι**は純tensorの包含成分で内部先頭作用に一致する計算式を与える。
任意可換環・非有界・独立D/I宇宙・Small.{u} Iを維持し、Dのsmallness、Homのflatnessは不要。
既存APIの名前・型は変更していない。§17.191の記録位置を番号順へ整理した。

Checks.DGCellPrependDifferential・Checks.DGCellInternalComposition・Checks.DGCellDifferential・
Checks.DGCellBoundaryNaturality・Checks.DGCellBoundaryOperator・Checks.DGBoundarySequence・
Checks.DGCategoryInitial・Checks.FreeDGUniversal・Checks.DGCategoryResolution・
Checks.DerivedBimoduleFullPentagon・Checks.StageEight・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（3159 jobs、終了コード0、警告なし）。独立宇宙、flatness仮定なしの
実際のchain map・純tensor成分、ZMod 2を型検査した。
主要8宣言の直接公理監査は標準3公理のみ。監査累計3621宣言。
今回の実装にsorry/admit/新規axiomはなく、採用済み引用は0件。
全体文書検査は15 Markdown・320 exposition参照を検査し、§17.191と同じ担当外の
BhattScholze互換宣言の未解決参照1件で失敗した。共有ルート・並行所有ファイルは編集していない。

次は任意の左有限pathの連結について、先頭cellを境界へ置く項と後方へ置換を渡す項に分けて
replacementのLeibnizを証明する。その後、全Hom直和の最終合成chain mapとdg圏instanceへ進む。
今回の元のHomの先頭作用だけで、二つのattachedHom間の合成や最終dg圏を構成済みとはしない。
増大・cell充填、最終Hom K-flat性、解像度の存在と比較、U12e全受入・U16も未完。
§0の分担・U15e/U17の合流条件を維持し、共有一般論への新しいAPI要求はない。


### 17.193 U12e34：全Homの先頭境界・置換再帰式と連結の先頭項（2026-10-17）

`Complexes/TensorCarryCochain.lean`の**tensorRight_cochain_chain_naturality**は
任意次数cochainと右因子のchain mapの自然性。
**tensorCarry_cochain/tensorRight_action_cochain**は結合的な作用の下でのcochainの連結への輸送を証明する。
`PrefixTensorCochainPostcompose.lean`の**prefixTensor_cochain_middle_postcompose**と
**prefixTensor_cochain_right_postcompose**は前方二因子を保つ輸送に後合成を加えたもの。
いずれも具体的な非有界複体tensorの補題で、共有の任意V一般論は追加していない。

`Resolution/Cells/InternalBoundaryHead.lean`の**Family.internalReplaceHead/internalReplaceFirst**は、
先頭生成元の指定境界を全Hom直和へ作用させる次数+1 cochain。
前者はgenerator⊗Hom(target,y)→Hom(source,y)、後者は前方Homを戻したもの。
**internalReplaceHead_inclusion/internalReplaceFirst_inclusion**で有限path上の既存置換に一致する。
`BoundaryRowRecursion.lean`の**prefixTailCochain/replaceSummand_cons_succ/replaceRow_cons**は、
先頭生成元の境界置換と後方の置換和への分解を与える。
`PrefixBoundary.lean`の**prefixPath_replacement**がこの分解を全Hom直和上の作用素へ移す。
`AppendBoundaryHead.lean`の**appendRight_replaceHead/appendRight_replaceFirst**は、
後方pathの連結と先頭生成元の境界置換との整合性を証明する。
任意整数次数・別端点・独立対象/添字宇宙を保持し、HomのflatnessやDのsmallnessは要求しない。
公開APIの名前・型の変更はない。

Checks.DGCellBoundaryRecursion・Checks.DGCellPrependDifferential・Checks.DGCellInternalComposition・
Checks.DGCellDifferential・Checks.DGCategoryResolution・Checks.DerivedBimoduleFullPentagon・
Checks.StageEight・Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功
（3163 jobs、終了コード0、警告なし）。主要15宣言の直接公理監査は標準3公理のみ。
ZMod 2、任意次数・別端点の先頭境界作用素と全path再帰式を型検査した。
監査累計3636宣言。今回の受入部分にsorry/admit/新規axiomはなく、採用済み引用は0件。
全体文書検査は15 Markdown・320 exposition参照を検査し、担当外BhattScholze互換宣言の
未解決参照1件で失敗した。共有ルート・共有一般論・並行所有ファイルは編集していない。

後方cochainの持ち上げと全Leibnizの接続は進行中である。
`AppendLiftCochain.lean`の標準heartbeat内の型照合が未解決で、
同ファイルを通るCompositionDifferentialの対象ビルドはまだ失敗している。
この持ち上げと依存する一般Leibniz・最終合成の草稿は未受入・未コミットであり、
今回の成功した統合ビルドには含めていない。標準上限を引き上げず、式の計算・輸送の粒度を整理して続ける。
これらの完成、最終dg圏instance、増大・cell充填、最終K-flat性、解像度の存在と比較、
U12e全受入・U16は引き続き未完。§0の分担とU15e/U17の合流条件を維持する。


### 17.194 U12e35：任意左pathの全Leibniz則と最終Hom間の合成chain map（2026-10-17）

§17.193で未受入とした後方cochainの持ち上げを修復した。
`Resolution/Cells/PathEquations.lean`の**Family.term_nil/term_cons**は、未知の後続語全体を展開せずに
先頭一段の計算を行う。複体の型を明示し、具体的複体tensorの証明を小さい宣言へ分割して、
標準heartbeat内で以下を検査した。上限の引上げやunsafe reducibility設定は使用していない。

`Complexes/PrefixTensorCochainAction.lean`の**prefixTensor_cochain_action_left/right**は、
結合的な先頭追加の下で任意次数cochainを左右因子から持ち上げる。
`PrefixTensorCochainPrecomp.lean`の**prefixTensor_cochain_precomp**はchain map前合成との整合性。
いずれも具体的な複体上の補題で、共有の任意V一般論への追加ではない。

`Resolution/Cells/AppendLiftCochain.lean`の**Family.appendLiftCochain/appendLiftCochain_add**は、
前方Homと任意次数生成元を保つ後方cochainの持ち上げと加法性。
**appendLiftCochain_left/right**は左右因子の項を短いpathでの項の持ち上げとして計算する。
`AppendBoundaryRecursion.lean`の**appendRight_cons_factor/appendRight_replaceFirst_factored**は
先頭追加の因子分解とその先頭境界項、**appendRight_replacement_cons**は連結後の境界置換の再帰式。
`AppendBoundary.lean`の**appendRight_replacement**は左有限pathに関する帰納法で得る全Leibniz則。
先頭生成元を置換する項と、前方Hom・生成元を通って後方を置換する項の両方を保持する。

`TensorRightPathCochainExt.lean`の**tensorRightPathCochain_ext**は右tensorした全path直和のcochain判定。
`CompositionBoundary.lean`の**internalComposition_replacement**で上のLeibnizを両因子の全Hom直和へ拡張した。
`CompositionDifferential.lean`の**internalComposition_replacement_apply**は斉次成分式で、
右因子の置換に左因子の次数pからの符号(-1)^pを持つ。
**internalComposition_total_d_apply**は内部微分と置換を合わせた全微分のLeibniz則。
**attachedComposition : attachedHom(x,y) ⊗ attachedHom(y,z) → attachedHom(x,z)**は、
これを既存tensorLiftへ適用した実際のchain map。
**attachedComposition_ι**は純tensorの包含成分で内部合成に一致することを示す。
任意可換環・非有界・別端点・任意整数次数・独立D/I宇宙を維持し、Small.{u} Iだけを直和に使う。
元のHomのflatnessとDのsmallnessは不要で、既存APIの名前・型の変更はない。

Checks.DGCellCompositionDifferential・Checks.DGCellBoundaryRecursion・Checks.DGCellPrependDifferential・
Checks.DGCellInternalComposition・Checks.DGCellDifferential・Checks.DGCategoryResolution・
Checks.DerivedBimoduleFullPentagon・Checks.StageEight・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（3173 jobs、終了コード0、警告なし）。独立宇宙、元のHomのflatness仮定なしの
最終合成chain map・純tensor成分、ZMod 2を検査した。
主要19宣言の直接公理監査は標準3公理のみ。監査累計3655宣言。
今回の実装にsorry/admit/新規axiomはなく、採用済み引用は0件。
全体文書検査は15 Markdown・320 exposition参照を検査し、§17.193と同じ担当外の
BhattScholze互換宣言の未解決参照1件で失敗した。共有ルート・共有一般論・並行所有ファイルは編集していない。

次は内部合成との各次数の一致から左右単位と結合則を追加微分後へ移し、主dg圏instanceと
元のdg圏からの包含関手を構成する。指定原始元への増大、cell生成元の充填式、filtrationによる
最終Hom K-flat性、列と解像度の一般存在・比較は引き続き未完。
今回の最終合成chain mapだけでU12eを受入済みとはしない。受入後のU16、合流後のU15e/U17の
目標と§0の分担を維持し、共有一般論への新しいAPI要求はない。


### 17.195 U12e36：任意次数cell付加の主dg圏と包含dg関手（2026-10-17）

`Resolution/Cells/CompositionComparison.lean`の**Family.attachedComposition_f**は、
追加微分後の合成の各次数の射が内部合成と同じことを証明する。
**attachedComposition_original**は元のHomの包含と豊穣合成の可換式。
`CompositionEvaluation.lean`の**attachedComposition_apply**は純tensor成分での一致。
`Identity.lean`の**attachedIdentity/attachedIdentity_f/attachedComposition_left_unit**、
`RightIdentity.lean`の**attachedComposition_right_unit**と
`Associativity.lean`の**attachedComposition_assoc**で、閉単位・左右単位則・結合則を
追加微分後の実際のHom複体上に構成した。内部合成の法則を次数成分で輸送している。

`Category.lean`の**Family.Objects/objectEquiv**はcell族ごとに区別した対象型と元の対象型の同値。
**attachedDGCategory**は上のHom・単位・合成を持つMathlib豊穣dg圏instance。
**embedding : DGFunctor A D (C.Objects A D I)**は元のHomを空pathへ入れる実際のdg関手。
**attachedComposition_eq_signed_compose**で豊穣順と通常順の合成のKoszul符号を照合した。
A : Type u、D : Type v、I : Type wの独立宇宙を保ち、直和にはSmall.{u} Iを要求する。
DのsmallnessもHomのflatnessも主dg圏・包含関手には不要。
**objectsSmall**だけがSmall.{u} Dから対象型のSmall.{u}を得る。
これらは後続のcell充填・増大と解像度の反復構成で使う。既存公開APIの名前・型の変更はない。

Checks.DGCellCategory・Checks.DGCellCompositionDifferential・Checks.DGCellBoundaryRecursion・
Checks.DGCellPrependDifferential・Checks.DGCellInternalComposition・Checks.DGCellDifferential・
Checks.DGCategoryResolution・Checks.DerivedBimoduleFullPentagon・Checks.StageEight・
Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功（3183 jobs、終了コード0、警告なし）。
独立宇宙・任意整数次数・別端点・ZMod 2と、追加仮定なしの主instance・包含dg関手を型検査した。
主要14宣言の直接公理監査は標準3公理のみ。監査累計3669宣言。
今回の実装にsorry/admit/新規axiomはなく、採用済み引用は0件。
全体文書検査は担当外HomologicalAlgebra.AlgebraScalarExtensionModuleのolean欠落により
Export.leanのimport段階で失敗した。今回、Markdown参照検査の完了とは扱わない。
共有ルート・共有一般論・並行所有ファイルは編集していない。

次はcell生成元の指定境界式と指定原始元への増大を構成する。その後、filtrationによる
最終Hom K-flat性、列の反復、解像度の一般存在・比較を完成させてU12eを受け入れ、U16へ進む。
主dg圏の構成だけでU12e全体を受入済みとはしない。
§0の分担を維持し、U14とU12f/U15dの記録はそれぞれの担当文書を正本とする。
U15e/U17はU12f・U14・U16の受入条件がそろった後に扱う。
共有一般論への新しいAPI要求はない。


### 17.196 U12e37：生成cellの境界・disk squareと指定原始元による有限path評価（2026-10-17）

`Resolution/Cells/GeneratorBoundary.lean`の**Family.generatorTerm_apply**は、
別々の両端の単位を挿入する生成元pathの成分式。
**forward_units_of_sum**は中間和次数を明示した両側単位の評価である。
**replaceFirst_generatorTerm/replaceRow_singleton/replacement_generatorElement**で
一生成元pathの全置換が指定境界の空path包含になることを示した。
**generatorElement/internal_d_generatorElement/differential_generatorElement**は最終Hom内の
次数degree(i)の実際の生成元と、d(generatorElement)=originalHomInclusion(boundary(i))の式。
内部微分が零であることと追加置換による微分を区別して証明した。
`GeneratorDisk.lean`の**generatorDisk/generatorDisk_generator/generatorDisk_boundary**は
実際のdisk chain mapと、指定sphere境界の包含がこのdiskを通る可換squareを構成する。
Homのflatness・対象Dのsmallnessは不要で、全path直和を使う部分にはSmall.{u} Iだけを要求する。

`PrimitiveData.lean`の**Family.PrimitiveData**は、元のdg関手Fとcell族Cに対して
各生成cellの像を次数degree(i)の原始元として指定し、その微分がF(boundary(i))であることを保持する。
**PrimitiveData.cochain/cochain_generator/cochain_differential**は対応する次数0 cochainと
その生成元評価・Hom微分の式。元のcell生成元がsphereに属していても、原始元が閉じているとはしない。
**DGCategoryBoundaryCells.primitiveData**は、全境界cellの添字自身が持つ原始元を使う標準データ。
`PathEvaluation.lean`の**PrimitiveData.pathEvaluation/pathEvaluation_nil**は有限path評価を再帰的に構成し、
**pathEvaluation_cons_generator**は任意次数・別端点の三重tensorでの順合成表示、
**pathEvaluation_generatorTerm**は一生成元pathが指定原始元へ評価されることを証明する。
この有限path側にはD/Iのsmallness仮定を置かない。A : Type u、D : Type v、I : Type w、
E : Type zを独立に保つ。これらは次の全Hom評価・増大dg関手の構成で使う。
既存公開APIの名前・型の変更はない。

Checks.DGCellGeneratorBoundary・Checks.DGCellCategory・Checks.DGCellCompositionDifferential・
Checks.DGCellBoundaryRecursion・Checks.DGCellPrependDifferential・Checks.DGCellInternalComposition・
Checks.DGCellDifferential・Checks.DGCategoryResolution・Checks.DerivedBimoduleFullPentagon・
Checks.StageEight・Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功
（3189 jobs、終了コード0、警告なし）。独立宇宙、有限path側のSmall仮定なし、
生成元の任意整数次数、disk square、ZMod 2での境界式を型検査した。
主要20宣言の直接公理監査は標準3公理のみ。監査累計3689宣言。
今回の実装にsorry/admit/新規axiomはなく、採用済み引用は0件。
全体文書検査は15 Markdown・320 exposition参照を検査し、担当外BhattScholze互換宣言の
未解決参照1件で失敗した。共有ルート・共有一般論・並行所有ファイルは編集していない。

次は有限path評価を全Homのcochainへ貼り合わせ、Hom微分と全置換の整合性を証明して
最終chain map・増大dg関手を構成する。今回の有限path評価はまだ最終Homのchain mapではない。
その後、filtrationによる最終Hom K-flat性、反復列、解像度の一般存在・比較を完成させる。
U12e全受入・U16は未完。U15e/U17の合流条件と§0の分担を維持する。
共有一般論への新しいAPI要求はない。


### 17.197 U12e38：全Hom評価・増大dg関手と次段での全境界cell充填（2026-10-17）

ユーザーの再割当を§0へ反映した。このチャットの現行順はU12e完成・受入→U16a〜d→U15e。
U16bではEndomorphism/の再構成随伴・endomorphism比較と受入済みScalarExtension系を
読み取り専用で再利用する。U14、U17a、U13dは担当外。D4mは当面未割当で主線に使わない。
U16cでDG-MOR又はU15eでDG-DRの引用採用が必要になったら採用せず停止して報告する。
この現行指定は、過去のU17までの一系列担当や引用許容案に優先する。
新規ファイルは同名ファイルの有無を確認し、共有ルート・監査スクリプトの変更時は
自分のhunkだけをgit add -pでstageする規約を維持する。

`Resolution/Cells/PathCochainDesc.lean`の**Family.pathCochainDesc/precomp/unique**は、
任意次数cochainをpath直和へ次数ごとの余積の普遍性で貼り合わせる。
`InternalEvaluation.lean`の**PrimitiveData.internalEvaluation/precomp/original/generator**は、
有限path評価から得る次数0 cochainと、元のHom・各生成cellでの評価の一致。
`PathEvaluationPrepend.lean`で元のHomの先頭合成を保つことを証明した。

`PrimitiveAction.lean`の**primitiveAction/boundaryOriginalAction/primitiveAction_differential/evaluate**は、
指定原始元の後方Homへの作用、そのHom微分、任意の後方評価との整合性。
`BoundaryActionEvaluation.lean`の**boundaryAction_pathEvaluation**はこの微分を先頭境界置換の評価と照合する。
`EvaluationPrefix.lean`の**evaluationOriginalAction/evaluationPrefixAction/differential**と
**pathEvaluation_cons_action**は、元のHomと生成元の固定前方作用による評価の表示。
`PathEvaluationDifferential.lean`の**evaluationPrefix_boundary/pathEvaluationTail**と
**pathEvaluation_cons_differential**は、評価の微分を先頭境界項と後方微分項に分ける。
`InternalEvaluationPrefix.lean`でこれを前方Hom・生成元追加と全Hom評価へ接続した。
`EvaluationReplacement.lean`の**pathEvaluationTail_internalEvaluation/pathEvaluation_differential**と
**internalEvaluation_differential**により、全評価cochainのHom微分が
全境界置換の後で評価する次数1 cochainと一致することを証明した。

`Evaluation.lean`の**attachedEvaluation**は既存のperturbSourceMapによる最終Homの実際のchain map。
**attachedEvaluation_f/original/generator/path/unit**で成分、元のHom、指定原始元、全path、単位を照合した。
`PathEvaluationAppend.lean`は任意二有限pathの連結を評価が保つことを証明し、
`TensorTwoPathCochainExt.lean`の判定補題と`InternalEvaluationComposition.lean`で全Hom上へ移した。
`EvaluationComposition.lean`の**attachedEvaluation_composition**は追加微分後の合成保存。
`Extension.lean`の**PrimitiveData.extension**はこれらを持つ主豊穣モデル上の実際のdg関手。
**embedding_comp_extension**は元のdg関手への厳密な制限等式、
**extension_generator**は各生成cellの像が指定原始元そのものであることを示す。

`Augmentation.lean`の**DGCategoryBoundaryCells.attachedAugmentation**は全境界cell族への標準増大。
**embedding_comp_attachedAugmentation**は元の増大への制限、
**attachedAugmentation_fills**は、元の任意のcellの境界が次段の生成元で埋まり、
かつ増大で指定されたtarget原始元へ厳密に送られることを証明する。
一般の延長はA : Type u、D : Type v、I : Type w、E : Type zを独立に保ち、
Small.{u} Iだけを要求する。全境界cell族の標準増大にはSmall.{u} Dを使い、Eのsmallnessは不要。
Homのflatnessや有界性はどちらにも要求しない。既存公開APIの名前・型の変更はない。
これらは次のcell付加の反復列、増大の列、全境界充填による準同値の証明で使う。

Checks.DGCellEvaluation・Checks.DGCellGeneratorBoundary・Checks.DGCellCategory・
Checks.DGCellCompositionDifferential・Checks.DGCellBoundaryRecursion・Checks.DGCellPrependDifferential・
Checks.DGCellInternalComposition・Checks.DGCellDifferential・Checks.DGCategoryResolution・
Checks.DerivedBimoduleFullPentagon・Checks.StageEight・Checks.StageSeven・既存Spectra.StageTwoの
統合ビルドは成功（3212 jobs、終了コード0、警告なし）。独立宇宙・元のHomのflatness仮定なし・
任意次数/別端点の延長と標準増大・全境界充填・ZMod 2の延長を型検査した。
主要40宣言の直接公理監査は標準3公理のみ。監査累計3729宣言。
今回の実装にsorry/admit/新規axiomはなく、採用済み引用は0件。
全体文書検査は16 Markdown・320 exposition参照を検査し、担当外BhattScholze互換宣言の
未解決参照1件で失敗した。共有ルート・共有監査スクリプト・共有一般論・並行所有ファイルは編集していない。

次はpath長filtrationで最終HomのK-flat性を証明し、cell付加の反復列と極限増大を構成する。
解像度の一般存在・比較、既存の導来bimodule合成との接続を終えて§15.2のU12eを受け入れる。
増大が一段で全Hom準同型になるとは主張しない。U12e全受入・U16・U15eは未完。
共有一般論への新しいAPI要求はない。


### 17.198 U12e39：path長filtration・次数ごとの分裂と最終HomのK-flat性（2026-10-17）

`Complexes/CoproductSubfamily.lean`の**ComplexCoproduct.cochain_ext/cochainDesc/precomp**は
任意のsmallな複体族のcochain判定・貼合せ。
**subfamily/inclusion/projection/inclusion_projection**は部分族の直和と分裂する包含・射影。
**select/ι_select_mem/ι_select_not_mem/select_self/select_inclusion/select_comp/select_zero**と
**select_partition**で、二部分族間の成分選択と互いに素な分割による恒等射の分解を証明した。
`PerturbationRestriction.lean`の**cochain_postcomp_injective_of_retraction**は分裂包含への後合成の単射性。
**perturbation_closed_of_inclusion/perturbation_square_zero_of_inclusion**は、追加微分との可換式から
部分複体側の閉性・二乗零を導く。**perturbMap/perturbMap_f**は両側の微分変更後の実際のchain map。
いずれも具体的な非有界A複体の補助APIであり、共有の任意V一般論は追加していない。

`Resolution/Cells/LengthBoundary.lean`の**lengthSet/lengthInternalHom/lengthInclusion/lengthProjection**は
長さn以下のpath直和と内部複体での包含・射影。
**lengthReplacement**は元の全境界置換をこの部分族へ制限した次数1 cochain。
**replaceSummand_length_projection_inclusion/replaceRow_length_projection_inclusion**で
置換後の語も長さ上限内に留まることを示し、**lengthReplacement_inclusion**で元の置換との可換式を得た。
`LengthFiltration.lean`の**lengthReplacement_closed/square_zero/lengthHom/lengthHom_d**は
追加微分を含む実際の有限長段階。**lengthHomInclusion/f/degreewiseMono/mono**は最終Homへの包含。
この段階は内部微分だけのpath直和ではない。
`LengthTransition.lean`の**lengthInternalMap/inclusion/replacement**と**lengthMap/f/inclusion/self/comp**は
長さ上限を増やすchain mapとその圏法則、最終Homへの包含との整合性を与える。

`LengthGraded.lean`の**exactLengthSet/exactLengthHom/exactLengthProjection**は固定長のpath直和。
**replaceSummand_exactLength_projection/replaceRow_exactLength_projection**と
**lengthReplacement_quotient_zero**は、境界置換が語長を一つ減らすため固定最上位長の商で消えることを示す。
**lengthInternalQuotient/lengthQuotient/lengthQuotient_f**は追加微分後の段階からこの商へのchain map。
**exactLengthHom_kFlat**は元のHomの局所K-flat性から固定長直和のK-flat性を得る。
`LengthSplit.lean`の**lengthMap_quotient/lengthShortComplex/lengthSplitting**は隣接段階と固定長商の
実際の短複体、および各次数でのsection/retractionと分裂等式。
**lengthQuotient_zero_isIso**で初期段階を固定長0の内部複体と同型にし、
**lengthHom_kFlat**で既存の次数ごと分裂する拡張のK-flat閉性を使って全有限段階を帰納した。

`LengthColimit.lean`の**lengthDiagram/lengthCocone/lengthMap_ι/lengthEvalIsColimit/lengthIsColimit**は
最終Homが長さ段階の逐次余極限であることを証明する。
各pathが自分の語長の段階へ入ることから次数ごとの普遍性を直接構成し、
HomologicalComplex.isColimitOfEvalで複体の普遍性へ移した。
**Family.attachedHom_kFlat**は、有限段階のK-flat性とModuleCatのexactな逐次余極限を用いた最終結果。
**attachedDGCategory_localHomKFlat**はcell付加後の主dg圏の局所K-flat性を与える。
任意可換環・非有界・任意整数次数・別端点を維持する。
A : Type u、D : Type v、I : Type wは独立で、必要なのはSmall.{u} Iと元のlocalHomKFlat A D。
一般のcell付加のK-flat保存にSmall.{u} Dは不要。全境界cell族への適用ではその族のsmallnessに
Small.{u} Dを使い、target dg圏のHomのflatnessや対象smallnessは要求しない。
既存公開APIの名前・型の変更はない。このK-flat保存を解像度構成の各付加段階に使う。

Checks.DGCellLengthFiltration・Checks.DGCellEvaluation・Checks.DGCellGeneratorBoundary・
Checks.DGCellCategory・Checks.DGCellCompositionDifferential・Checks.DGCellBoundaryRecursion・
Checks.DGCellPrependDifferential・Checks.DGCellInternalComposition・Checks.DGCellDifferential・
Checks.DGCategoryResolution・Checks.DerivedBimoduleFullPentagon・Checks.StageEight・Checks.StageSeven・
既存Spectra.StageTwoの統合ビルドは成功（3221 jobs、終了コード0、警告なし）。
独立宇宙、一般cell付加のD-small仮定なし、分裂・余極限の実データ、標準全境界cell族への適用、
ZMod 2での最終局所K-flat性を型検査した。
主要76宣言の直接公理監査は標準3公理の範囲内。監査累計3805宣言。
今回の実装にsorry/admit/新規axiomはなく、採用済み引用は0件。
全体文書検査は16 Markdown・320 exposition参照を検査し、担当外BhattScholze互換宣言の
未解決参照1件で失敗した。共有ルート・共有監査スクリプト・共有一般論・並行所有ファイルは編集していない。

次は全境界cell付加の反復列とその増大、Homの極限と豊穣合成を構成する。
既存の列の境界充填criterionを適用して極限増大のHom準同型性を示し、初期cycle coverからの
対象上の全射性と合わせて小さいdg圏のK-flat解像度の一般存在へ接続する。
解像度の比較と既存の導来bimodule合成への接続も残る。
今回の最終Hom K-flat性だけでU12e全体を受入済みとはしない。U12e全受入・U16・U15eは未完。
§0の現行分担と引用禁止を維持し、共有一般論への新しいAPI要求はない。


### 17.199 U12e40：cell付加反復列と小さいK-flat dg圏解像度の一般存在（2026-10-17）

`Resolution/FixedObjectAugmentation.lean`の**FixedObjectAugmentation**はMathlibの
EnrichedCategoryをデータとして保持し、対象ラベルXと増大の対象写像o : X → Eを固定する。
独立したdg圏モデルを導入せず、元の対象型のglobal instanceも変更しない。
**toDGFunctor/CellIndex/cells/cellPrimitives**は既存の増大・全境界cell族・指定原始元への入口。
**attachedCategory/attach/transition**で同じX上の次段の豊穣構造と増大を構成し、
**transition_id/comp/augmentation**で遷移の単位・合成保存と増大の厳密な可換式を示した。
**attach_fills**は次段で全境界cellが埋まり、指定原始元へ送られる式、
**HomKFlat/attach_homKFlat**は局所K-flat性の保存である。
一般の固定対象増大はA : Type u、X : Type v、E : Type wを独立に保ち、
cell付加にはSmall.{u} Xだけを要求する。target Eのsmallnessは不要。

`CellSequence.lean`の**DGCategoryCellResolution.initial/stage**は既存の自由cycle coverを
初期増大とし、全境界cellの付加を逐次反復する実際の列。
**stage_homKFlat/stageHom/transition/stageAugmentation/transition_augmentation**で
全段階のK-flat性、各対象対のHom複体と増大の可換式を与える。
**homDiagram/augmentationCocone/stage_fills**で既存の逐次境界充填criterionへ接続した。
**candidateHom/candidateAugmentation/stageInclusion**はHom列の余極限と増大。
**stageInclusion_augmentation/transition_inclusion**はその計算式。
**candidateAugmentation_quasiIso**は全有限段のcell充填から極限増大のHom準同型性を証明し、
**candidateHom_kFlat**はexactな逐次余極限から得る。次数ごとの増大全射性はこの証明に使っていない。

`CellComposition.lean`の**candidateTensorIsColimit**は固定版MathlibのIsColimit.tensorを使う。
ℕのIsSiftedはIsFiltered.isSiftedから局所的に与え、共有一般論やglobal instanceを追加しない。
**compositionCocone/candidateComposition/stage/apply_stage**は各段階の豊穣合成を極限Hom上の
実際のchain mapへ貼り合わせる。**candidateUnit/stage**は全段階で一致する閉単位。
**candidateUnit_augmentation/candidateComposition_augmentation**で増大の単位・合成保存を示す。
`CellUnits.lean`の左右単位則、`CellAssociativity.lean`の**stageComposition_assoc**と
**candidateTripleIsColimit/candidateComposition_assoc**で極限の三つの豊穣圏法則を証明した。
合成・結合則は同じ有限段のtensorへの制限で照合し、複体をH⁰へ置き換えていない。

`FixedObjectCategory.lean`の**FixedObjectAugmentation.Objects/objectEquiv/objectsSmall**と
**objectsDGCategory/augmentation/objects_homKFlat**は、保持した豊穣構造を別対象型上へ登録する。
`CellCategory.lean`の**DGCategoryCellResolution.candidate/Source/augmentation**が主dg圏と増大関手。
**source_homKFlat/augmentation_homQuasiIso/augmentation_essSurj/augmentation_quasiEquivalence**は、
局所K-flat性、全Hom準同型性、H⁰の本質的全射、増大準同値を個別に与える。
対象写像は元のDの対象ラベルを保つので、H⁰の本質的全射に生成性の引用は不要。
**resolution**を既存のKFlatDGResolutionデータへまとめた。

新しい公開入口は**KFlatDGResolution.canonical**と**KFlatDGResolution.nonempty**。
前者は[Small.{u} D]の下でKFlatDGResolution.{u, v, v} A Dを返し、後者はそのNonemptyを証明する。
Aは任意可換環、Dは非有界Homを持つ任意の小さいA線形dg圏であり、
元のHomの局所K-flat性・次数ごとのflatness・有界性を要求しない。
構成したsourceの対象宇宙はv、Hom加群の宇宙はuのまま。
既存ResolutionBimodule.composeFunctorへこれらの標準解像度をそのまま入力できる。
既存公開APIの名前・型の変更はなく、新しいsorry・axiom・引用もない。

Checks.DGCellResolutionExistence・Checks.DGCellLengthFiltration・Checks.DGCellEvaluation・
Checks.DGCellGeneratorBoundary・Checks.DGCellCategory・Checks.DGCellCompositionDifferential・
Checks.DGCellBoundaryRecursion・Checks.DGCellPrependDifferential・Checks.DGCellInternalComposition・
Checks.DGCellDifferential・Checks.DGCategoryResolution・Checks.DerivedBimoduleFullPentagon・
Checks.StageEight・Checks.StageSeven・既存Spectra.StageTwoの統合ビルドは成功
（3231 jobs、終了コード0、警告なし）。独立対象宇宙、元のHomのflatness仮定なしの
標準解像度・準同値・K-flat性、ZMod 2での一般存在、一般固定対象増大の独立target宇宙、
既存の導来bimodule合成への無条件の入力を型検査した。
主要63宣言の直接公理監査は標準3公理の範囲内。監査累計3868宣言。採用済み引用は0件。
全体文書検査は16 Markdown・320 exposition参照を検査し、担当外BhattScholze互換宣言の
未解決参照1件で失敗した。共有ルート・共有監査スクリプト・共有一般論・並行所有ファイルは編集していない。

次は解像度間の比較用dg関手・zigzagと、解像度上の導来bimodule合成の比較を構成する。
この一般存在定理だけで比較の選択独立性や解像度変更のcoherenceを証明したことにはしない。
これらを確認して§15.2のU12eを受け入れ、その後U16a〜d、U15eへ進む。
U12e全受入・U16・U15eは未完。§0の現行分担と引用禁止を維持する。
共有一般論への新しいAPI要求はない。


### 17.200 U12e41：cell延長の一意性・初期比較と付加後のHom比較（2026-10-17）

前回の分担確認を終え、解像度比較の実装を再開した。一般存在は§17.199で受入済みだが、
解像度変更の比較とcoherenceはまだ未完である。

`Complexes/TensorTwoUnitInsertion.lean`は両端のHom・単位を区別したtensor補題を追加する。
`Complexes/SphereCochainExt.lean`の**sphereMiddleCochain_ext₀**は、任意整数次数dの
sphereを中央に持つtensorからの次数0 cochainを、その標準生成元上で判定する。
他次数のsphere成分が零であることも証明に用い、標数零や次数の正性は要求しない。

`Resolution/Cells/GeneratorAppend.lean`・`PrefixGeneration.lean`・`PathGeneration.lean`は、
先頭cellを付けたpathを元のHom・指定生成元・tailの二回の豊穣合成で表す。
`RestrictionData.lean`は付加後のdg関手から元の関手と各cell原始元の像を取り出す。
`Reconstruction.lean`はpath帰納法と全Hom cochainの判定から**extension_restrict**を証明する。
`Universal.lean`の**extension_unique**・**functor_ext**は、元の関手とcell生成元の像が
一致するdg関手の一意性を与える。対象・cell添字・targetの宇宙は独立で、
必要なsmallnessはcell添字のSmall.{u}のみ。元のHomのflatness・有界性は要求しない。

`Resolution/CycleCoverFunctor.lean`はcycleのchain mapによる移送、全cycle被覆の写像、
identity/comp、被覆増大との可換性を与える。
`InitialComparison.lean`の**DGCategoryCycleCover.map**は任意dg関手Fに沿う初期自由被覆間の
実際のdg関手で、**map_augmentation**は増大の厳密な可換squareである。
`InitialStageComparison.lean`はこれを**DGCategoryCellResolution.initialComparison**へまとめる。

`Resolution/FixedObjectMap.lean`の**FixedObjectAugmentation.Map S T F**は、
対象写像F.obj、単位・合成を保つHom chain map、増大との可換squareを保持する。
SはD上・TはE上の固定対象増大で、D/Eの対象宇宙は独立。
**Map.cellMap**はcycleと指定原始元を同時に送り、cellの整数次数を保存する。
`FixedObjectMapExtension.lean`の**Map.attachedFunctor/attachedHom**は、移送したcellの
生成元を像に指定して付加後へ延長する。**transition_attachedHom**は元のHom包含との可換性、
**attachedHom_id/attachedHom_comp**は単位・合成保存を証明する。
ここではD/EのSmall.{u}を要求し、各HomのK-flat性は要求しない。
段階の豊穣instanceを明示的に固定し、元のdg圏のinstanceと混同しない。
既存公開APIの名前・型は変更していない。すべて解像度比較用の新規APIである。

**検証。** Checks.DGCellComparison・Checks.DGCellResolutionExistence・
Checks.DGCellLengthFiltration・Checks.DerivedBimoduleFullPentagon・Checks.StageEight・
Checks.StageSeven・Spectra.StageTwoの統合ビルド成功（3234 jobs、警告なし）。
任意次数・別端点cellの再構成、独立した対象/添字/target宇宙、初期増大比較、ZMod 2での
比較を型検査した。主要46宣言の直接公理監査は宣言名の重複・欠落なく標準3公理以内。
監査累計3914宣言。採用済み引用は0件。新しいsorry・axiom・引用は追加していない。
全体文書検査は16 Markdown・320 exposition参照を検査し、従来と同じ担当外の
BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの
未解決参照1件で失敗した。共有ルート・監査スクリプト・並行担当ファイルは編集していない。

**次の受入課題。** 付加後の比較と増大との可換性を証明してMap.attachへまとめ、
全反復段階と逐次余極限へ比較を延長する。さらに準同値性、解像度変更の導来bimodule合成の
比較・選択独立性・coherenceを証明してU12eを受け入れる。
今回の一段のHom比較だけでU12e全体の受入とはしない。
その後U16a〜dへ進む。U14・係数変更系は読み取り専用で再利用し、
U15e/U17の合流条件と引用禁止は§0のまま保持する。共有一般論への新しいAPI要求はない。


### 17.201 U12e42：全段階・最終解像度の関手比較と任意解像度との準同値zigzag（2026-10-17）

前回§17.200は実装進捗のあったターンとして継続し、付加後の増大との可換性から再開した。
`Resolution/FixedObjectGenerators.lean`の**cellGenerator**は固定対象cell付加の生成元を、
対象instanceの切替を利用側へ露出させず公開する。**attach_map_cellGenerator**は増大像が
指定原始元になる式、**Map.attachedHom_cellGenerator**は比較による生成元の移送式である。

`FixedObjectMapAugmentation.lean`では、比較後の増大と増大後の元のdg関手という二つの
実際のdg関手を構成した。元のHomへの制限は比較の増大squareで一致し、生成cell上では
指定原始元の移送式で一致する。§17.200の延長一意性から**attachedFunctor_augmentation**を得た。
**attachedHom_augmentation**を使った**Map.attach**は、増大比較Map S T Fを
Map S.attach T.attach Fへ延長する。D/EのSmall.{u}のみを要求し、局所Hom K-flat性は不要。

`Resolution/CellComparison.lean`の**stageComparison**は任意dg関手Fに沿って全段階を比較する。
**transition_comparison**により逐次列のsquareが可換し、**comparisonCocone/comparisonHom**で
最終Homの逐次余極限へ降ろす。**stageInclusion_comparison**は各有限段階での計算式、
**comparisonHom_augmentation/unit/comp**は増大・単位・合成保存である。
合成保存はMathlibのfiltered対角tensor余極限の普遍性と各段階の合成保存から証明した。
**comparison/comparisonFunctor**は標準解像度間の実際の増大比較/dg関手で、
**comparisonFunctor_augmentation**は元のdg関手Fと増大の厳密な可換squareを与える。
**comparisonHom_quasiIso/comparisonFunctor_homQuasiIso**はHom準同型を保存する。
証明は両増大のHom準同型と2-out-of-3を用い、モデル構造や深い比較定理を使わない。

`Functor/QuasiIsoHomology.lean`は解像度に依存しない一般APIである。
**closedHomEquiv_map/homotopyHomologyEquiv_map_naturality**は、閉零射とH⁰の射を
主Hom複体のcycle/Mathlib homologyへ送る比較のdg関手自然性を証明する。
**onHomotopy_map_bijective_of_homQuasiIso**は、Homの次数零homology写像が同型であることから
H⁰の各射写像の全単射性を導く。
**onHomotopy_full_of_homQuasiIso/onHomotopy_faithful_of_homQuasiIso**により完全忠実性を公開した。
この一般APIは対象型のsmallness・HomのK-flat性・有界性を要求しない。
U12eの比較の本質的全射性に使用し、後続U16bの準同値に沿う比較でも再利用できる。

`CellComparisonQuasiEquivalence.lean`の**comparisonFunctor_essSurj**は、標的増大の
H⁰完全忠実性と増大squareから比較の本質的全射性を反映する。
**comparisonFunctor_quasiEquivalence**は元のdg準同値が標準解像度間の準同値を誘導する定理。

`Resolution/CanonicalZigzag.lean`では、任意の指定KFlatDGResolution Pについて
P.source ← Source(P.source) → Source(D)という具体的なzigzagを構成した。
**ComparisonSource/comparisonLeft/comparisonRight**が対象と両脚、
**comparisonLeft_quasiEquivalence/comparisonRight_quasiEquivalence**が両脚の準同値性、
**comparisonSource_homKFlat**が中間dg圏の局所Hom K-flat性を与える。
**comparison_augmentation**は両経路のDへの増大が厳密に一致することを証明する。
DとP.sourceの対象宇宙v/wは独立で、canonical側を作るDのSmall.{u}以外に
元のdg圏のHom flatness仮定を加えない。任意の二つの指定解像度はこの標準解像度を介して
準同値zigzagで比較できる。既存公開APIの名前・型の変更はなく、今回も追加のみである。

**検証。** Checks.DGResolutionComparison・Checks.DGCellComparison・
Checks.DGCellResolutionExistence・Checks.DerivedBimoduleFullPentagon・Checks.StageEight・
Checks.StageSeven・Spectra.StageTwoの統合ビルド成功（3243 jobs、警告なし）。
Hom flatness仮定なし、独立した解像度source宇宙、両脚の準同値と増大square、ZMod 2での
比較を型検査した。H⁰完全忠実性は対象smallnessなしでも型検査した。
主要34宣言の直接公理監査は宣言名の重複・欠落なく標準3公理以内。監査累計3948宣言。
新しいsorry・axiom・引用は追加していない。採用済み引用は0件。
全体文書検査は19 Markdown・320 exposition参照を検査し、担当外の
BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの
未解決参照1件で失敗した。共有ルート・監査スクリプト・並行担当ファイルは編集していない。

**残る受入条件。** 解像度dg圏そのものの一般存在と準同値zigzagによる比較は証明できた。
次はこの比較に沿う導来bimodule圏の比較と、解像度版合成・単位・結合の自然性、
選択独立性・coherenceを構成し、§15.2のU12eを受け入れる。
今回のdg圏zigzagだけから導来bimodule合成のcoherence完成を主張しない。
U12e全受入後はU16a〜dへ進み、U15e/U17は§0の合流条件を維持する。
共有一般論への新しいAPI要求はない。


### 17.202 U12e43：一般dg関手に沿う導来制限と解像度bimodule比較の実際の関手（2026-10-17）

解像度変更の導来比較のため、既存の加群制限・opposite・積dg圏表示・局所化を再確認した。
`Functor/Opposite.lean`の既存**DGFunctor.op/op_id/op_comp**を再利用し、重複定義しなかった。
このファイルは変更していない。

`Derived/Restriction.lean`の**moduleDerivedRestriction**は、opposite上の指定dg関手に沿う
主導来加群圏の制限である。既存moduleRestriction_quasiIsoと局所化の普遍性を用いる。
**dgDerivedRestriction**は通常向きのdg関手から既存opを使う入口。
両者の**_fac**は閉零加群圏からの厳密な計算式を与える。
環は任意可換環、対象宇宙は独立、Small.{u}は両対象型に課す。
元のHomのflatness・有界性・dg関手の準同値性を要求しない。

`Module/RestrictionCoherence.lean`は**moduleRestrictionIdObjIso/IdIso**と
**moduleRestrictionCompObjIso/CompIso**を追加する。
全Hom自然な加群同型を既存moduleIsoMkで構成し、各評価成分は恒等chain mapである。
**moduleRestrictionIdObjIso_hom_eval/moduleRestrictionCompObjIso_hom_eval**が計算式。
`Derived/RestrictionCoherence.lean`はこれらを局所化のliftNatIsoで導来圏へ持ち上げる。
**moduleDerivedRestrictionIdIso/CompIso**が比較同型、**moduleDerivedRestrictionComp_fac**と
**moduleDerivedRestrictionCompIso_hom_app**が局所化前の対象における計算式。
今回の恒等・合成比較同型の構成だけで、制限の全coherence図式を証明済みとはしない。

`Functor/Tensor.lean`の**DGFunctor.tensor**は二つのdg関手のtensor積。
Hom chain mapは二つのHom写像のtensor積であり、単位保存と合成保存は既存のtensor積dg圏の
計算式とMathlib tensorμ_naturalから証明した。Koszul交換を通常圏の合成で置き換えない。
四つの対象宇宙は独立で、対象smallnessやHom flatnessは要求しない。

`Derived/BimoduleRestriction.lean`は、B→DとC→Eに沿う
**bimoduleRestriction/derivedBimoduleRestriction**を追加する。
既存rightModuleBimoduleEquivalenceで積dg圏のopposite上の右加群へ移し、
(F.op.tensor G).op.opに沿って制限して主bimodule圏へ戻す。
二重oppositeにより右加群制限の向きを固定する。
**bimoduleRestriction_quasiIso**は準同型保存、**derivedBimoduleRestriction_fac**は
主bimodule局所化からの厳密な計算式。両側とも全次数の作用と自然性を保持する。
四つの対象型にSmall.{u}を要求し、HomのK-flat性は要求しない。

`Derived/BimoduleRestrictionEvaluation.lean`の**bimoduleRightModuleEvaluationIso**は
積表示の逆同値と元の値評価の自然比較。
**bimoduleRestrictionEvaluationIso**は、制限後の(b,c)の値が
元のbimoduleの(F(b),G(c))の値と自然同型であることを証明する。
既存の評価比較・制限評価・同値の余単位を組み合わせ、抽象的な圏の輸送だけで済ませない。

`Resolution/Restriction.lean`の**ResolutionBimodule.restriction**は任意の指定解像度source間の
dg関手に沿う実際の導来bimodule制限。
**comparisonLeft/comparisonRight**は§17.201の準同値zigzagの両脚から、
指定解像度上/標準解像度上の導来bimodule圏を共通の中間圏へ送る関手を構成する。
sourceの対象宇宙は元のdg圏の宇宙と独立。元のHomの局所K-flat性は不要。
既存公開APIの名前・型は変更していない。追加APIはU12eの解像度変更に使用する。

**検証。** Checks.DGDerivedRestriction・Checks.DGResolutionComparison・
Checks.DGCellResolutionExistence・Checks.DerivedBimoduleFullPentagon・Checks.StageEight・
Checks.StageSeven・Spectra.StageTwoの統合ビルド成功（3250 jobs、警告なし）。
独立した四つの対象宇宙、Hom flatness仮定なしの両側制限/評価、独立した解像度source宇宙、
制限の導来合成比較、ZMod 2の一般導来制限を型検査した。
主要25宣言（局所化Liftingのinstanceを含む）の直接公理監査は重複・欠落なく標準3公理以内。
監査累計3973宣言。新しいsorry・axiom・引用は追加していない。採用済み引用は0件。
全体文書検査は19 Markdown・320 exposition参照を検査し、担当外の
BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの
未解決参照1件で失敗した。共有ルート・監査スクリプト・並行担当ファイルは編集していない。

**残る受入条件。** 構成した比較関手が準同値に沿って同値になることは、今回まだ証明していない。
次はdg関手に付随する加群/tensor延長と制限の比較を構成し、準同値の場合の導来同値性を示す。
そのうえで解像度変更と導来bimodule合成・対角単位・結合同型の自然性、選択独立性・coherenceを
接続してU12eを受け入れる。単なる制限関手の存在をU12e全受入の代用としない。
その後のU16a〜d、U15eの順と§0の分担・合流条件・引用禁止を保持する。
共有一般論への新しいAPI要求はない。


### 17.203 U12e44：graph tensorの導来延長と代表加群での延長・制限比較（2026-10-17）

前回の導来制限に対応する延長の構成を進めた。U14のModuleComparison・ModuleAdjunction・
HomotopyAdjunction・DerivedAdjunction・DerivedTensor・TensorProjectiveを読み、
全Hom自然なtensor関手、主Kを通る導来化、解像度比較の構成を確認した。
係数変更のScalarExtensionHomotopyと既存dg oppositeも確認し、同名APIを重複実装しない。
Endomorphism/・Tensor/ScalarExtension*・Derived/ScalarExtension*は編集していない。

`Module/FunctorExtension.lean`の**functorGraph A D E F**は、dg関手F:D→Eと既存dgYonedaの
合成から右E・左D bimoduleを作る。値はHom_E(e,Fd)であり、全次数の両作用を持つ。
**dgModuleExtension**は、このgraphと恒等dg関手を既存BimoduleTensor.composeへ入力した
実際のdg関手RightModule D→RightModule E。
**dgModuleExtension_value**はbalanced tensorによる各値の式、
**dgModuleExtensionRepresentableIso**は右代表D(-,d)をE(-,Fd)へ送る同型である。
後者は既存の全Hom自然なtensor右単位を直接再利用した。
D/Eの対象宇宙は独立、直和に必要なSmall.{u}を仮定し、
全加群型のsmallness・元のHomのK-flat性・有界性は要求しない。

`Module/FunctorGraphActions.lean`の**functorGraph_leftAt**は、graphの左D作用が
共変representable Hom_E(e,−)をFに沿って制限した作用と等しいことを証明する。
U14の既存**endomorphismYonedaApp**を実際の証明に再利用し、重複証明しなかった。
この作用比較自体はsource対象型DのSmallを要求しない。
**dgModuleExtensionValueIso**は延長の各値をこの制限左加群とのbalanced tensorとして計算する。

`Derived/FunctorExtension.lean`は、既存の証明付き射影解像度関手と
**dgExtensionHomotopyToDerived**を合成して**dgResolutionDerivedExtension/dgDerivedExtension**を構成する。
一般のunderived延長が全準同型を保つことは仮定せず、主Kを通してから主導来圏へ送る。
**dgResolutionDerivedExtensionComputation/dgDerivedExtensionResolutionComputation**は、
指定した任意の射影解像度による実際の計算同型である。
**dgResolutionDerivedExtensionIso**と**_self/_trans**は、解像度族の変更による自然同型と
自己・推移整合性。これらは既存moduleDerivedResolutionIsoをwhiskerして得た。

`Derived/ModuleFunctorProjective.lean`の**dgModuleFunctor_projective_quasiIso**は、
任意のdg加群関手がホモトピー射影的加群間の準同型を保つことを証明する。
主Kでその射が同型になり、dg関手のH⁰関手と各ホモロジー関手がそれを保つためである。
**dgModuleExtension_projective_quasiIso**はgraph tensorへの適用。
相手側のHom flatnessやモデル構造を仮定しない。

`Module/RestrictionRepresentable.lean`の**representableRestrictionMap**は、
各成分がF.map(x,d)である代表D加群→制限代表E加群の全Hom自然な閉零射。
**representableRestriction_naturality**は任意整数次数の合成保存から証明し、
**representableRestrictionMap_eval/_quasiIso**は評価式とHom準同型の下での準同型性を与える。

`Derived/FunctorExtensionRepresentable.lean`は、既にホモトピー射影的な加群の恒等解像度
**moduleIdentityProjectiveResolution**を追加し、
**dgDerivedExtensionRepresentableIso**で代表加群の導来延長を計算する。
**representableDerivedRestrictionIso**はHom準同型の下での代表加群の導来比較、
**dgDerivedRoundTripRepresentableIso**は代表加群と導来延長後の導来制限との同型である。
これは代表加群ごとの同型の構成までであり、全加群上の随伴単位を構成・同定したとは主張しない。
既存公開APIの名前・型の変更はなく、今回も追加のみ。

**検証。** Checks.DGFunctorExtension・Checks.DGDerivedRestriction・
Checks.DGResolutionComparison・Checks.DerivedBimoduleFullPentagon・Checks.StageEight・
Checks.StageSeven・Spectra.StageTwoの統合ビルド成功（3301 jobs、警告なし）。
独立したsource/target宇宙、Hom flatness仮定なしの導来延長と任意射影解像度計算、
Hom準同型の下での代表加群の往復同型、source smallnessなしのgraph作用比較、
ZMod 2での代表加群の導来延長と射影的加群間の準同型保存を型検査した。
主要26宣言の直接公理監査は重複・欠落なく標準3公理以内。監査累計3999宣言。
新しいsorry・axiom・引用は追加していない。採用済み引用は0件。
全体文書検査は19 Markdown・320 exposition参照を検査し、担当外の
BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの
未解決参照1件で失敗した。共有ルート・監査スクリプト・並行担当ファイルは編集していない。

**残る受入条件。** 次は延長・制限の全加群での単位・余単位/随伴を構成し、
代表加群上の比較との一致と、semifree列・準同値の本質的全射性を用いた導来同値性を証明する。
その後、解像度変更と導来bimodule合成・対角単位・結合の自然性、選択独立性・coherenceを
接続してU12eを受け入れる。代表加群ごとの往復同型だけで一般同値やU12e完成とはしない。
U12e全受入後のU16a〜d、U15eの順と§0の分担・合流条件・引用禁止を維持する。
共有一般論への新しいAPI要求はない。

### 17.204 U15eの局所K-flat版と分解版の分担更新（2026-10-17）

ユーザー指定により§0・§15.5・§15.7の現行分担を更新した。
このチャットはU12eの完成・受入→U16a〜d→U15eの分解版を担当する。
U17a・U13dを終えたチャットがU15eの局所K-flat版を担当し、
続けてU17bの局所K-flatの場合を扱う。
分解版を構成する際は、その成果である`Quotient/DerivedComparison*.lean`と`Verdier/`を
読んで再利用し、比較定理やVerdier側の構成を重複実装しない。
局所K-flat版の作業を、このチャットのU12e・U16の受入待ちとはしない。
§17の管理と、公開APIの名前・型を変更する際の記録責任はこのチャットが保持する。

この項は分担変更の記録であり、U12e・U16・U15eの受入完了を意味しない。
Leanの検証・公理監査の受入済み結果と累計は§17.203のまま。
進行中の全加群での延長–制限随伴から作業を継続する。

### 17.205 U12e45：graph延長の評価・自然な余単位・単位挿入成分（2026-10-17）

**追加API。** `Tensor/RestrictBalanced.lean`でdg関手に沿う左右作用のchain map比較と
`BalancedTensor.restrictFamily`を構成した。右作用のKoszul交換を保ってbalanced関係を
引き戻す。対象型の宇宙は独立とし、左右作用の比較にはsource smallnessを要求しない。
`Module/FunctorExtensionEvaluation.lean`で`functorExtensionEvaluationFamily`と
`functorExtensionEvaluationComponent`を定義した。既存の
`endomorphismYonedaApp`を読み取り専用で再利用してgraphの左作用を照合した。
任意整数次数r,sの生成元m⊗hの評価は`(-1)^(r*s) • moduleAction h m`である。

`Module/FunctorExtensionCounit.lean`の`functorExtensionEvaluation_naturality`は
全Homの自然性を証明し、`functorExtensionCounit`を実際の閉零加群射として構成する。
`Module/FunctorExtensionMaps.lean`ではgraph延長のHom写像を
`BalancedTensor.rightHomMap`と、閉零射の評価を`rightTensorMap`と照合した。
これを用いた`Module/FunctorExtensionCounitNaturality.lean`の`dgModuleCounit`は
制限→延長から恒等関手への自然変換である。
`Module/FunctorExtensionInsertion.lean`では単位挿入chain map成分と、
制限加群を挿入して評価すると恒等射になる式を証明した。
既存公開APIの名前・型の変更はない。元のHomのflatness・有界性を仮定しない。

**検証。** 新規`Checks.DGFunctorCounit`は独立宇宙・任意整数次数の評価式・
ZMod 2上の自然な余単位・挿入と評価の恒等式を型検査する。
同チェックとChecks.DGFunctorExtension・Checks.DGDerivedRestriction・
Checks.DGResolutionComparison・Checks.DerivedBimoduleFullPentagon・Checks.StageEight・
Checks.StageSeven・Spectra.StageTwoの統合ビルド成功（3308 jobs、警告なし）。
主要21宣言の直接公理監査は重複・欠落なく標準3公理以内。監査累計4020宣言。
今回の受入ソースのsorry・admit・新規axiom・資源上限変更は0件。採用済み引用は0件。
全体文書検査は20 Markdown・320 exposition参照を検査し、担当外の
BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの
未解決参照1件で失敗した。この計画書のローカルリンクと担当差分の空白検査は成功。

**残る受入条件。** 単位の挿入成分を全Hom自然な加群射へ束ねる作業は継続中である。
未受入の`Module/FunctorExtensionUnit.lean`は型の照合エラーが残る草稿で、
今回のチェックのimport・受入・コミットには含めない。自然な単位、両三角恒等式、
随伴の導来化、準同値に沿う全加群の導来同値を証明し、解像度変更と導来bimodule合成の
自然性・単位・結合のcoherenceへ接続する。今回の余単位だけでU12e全体を受け入れない。
その後U16a〜d、U15eの分解版へ進む。局所K-flat版は§0の並行担当成果を再利用する。
共有モデル一般論への新しいAPI要求はない。共有ルート・Endomorphism/・係数変更系列は変更していない。

### 17.206 U12e46：graph延長–制限の自然な単位と両三角恒等式（2026-10-17）

**追加API。** `Tensor/BalancedUnitElements.lean`に、出力次数の等式を変えた
左作用のHEq比較と`BalancedTensor.element_balanced_zero`を追加した。
後者は右側のtensor因子が次数0の場合のbalanced関係であり、一般の左加群について
`p+0=p`に伴う依存型の移送を処理する。graphのHom endやtensorの余極限を展開せずに適用できる。

前項で未受入だった`Module/FunctorExtensionUnit.lean`の型照合を解消した。
`functorGraph_leftAction_unit`は既存の`endomorphismYonedaApp`を再利用し、
graphの左作用を単位で評価するとdg関手のHom写像になることを示す。
`functorExtensionInsertion_action`は任意整数次数のHom作用に関する挿入の自然性であり、
`functorExtensionUnit`はその全Hom自然な閉零加群射である。
`Module/FunctorExtensionUnitNaturality.lean`の`functorExtensionInsertion_map`と
`dgModuleUnit`により、単位を加群変数についても自然変換へ束ねた。

`Module/FunctorExtensionAdjunction.lean`で`dgModule_left_triangle`と
`dgModule_right_triangle`を証明し、`dgModuleExtensionRestrictionAdjunction`を構成した。
左三角恒等式はtensor生成元上で二つのKoszul符号を相殺し、右三角恒等式は
既存の挿入–評価恒等式を用いる。任意可換環、独立のsource/target宇宙、u-smallな対象型で、
元のHomのflatness・有界性を仮定せず、全dg加群の閉零射圏上の随伴を得る。
既存公開APIの名前・型の変更はない。

**検証。** 新規`Checks.DGFunctorAdjunction`は全次数作用の自然性、両三角恒等式、
source smallnessを使わないgraph左作用の単位計算、ZMod 2上の随伴を型検査する。
同チェック、Checks.DGFunctorCounit・Checks.DGFunctorExtension・Checks.DGDerivedRestriction・
Checks.DGResolutionComparison・Checks.DerivedBimoduleFullPentagon・Checks.StageEight・
Checks.StageSeven・Spectra.StageTwoの統合ビルド成功（3313 jobs、警告なし）。
主要11宣言の直接公理監査は重複・欠落なく標準3公理以内。監査累計4031宣言。
今回の受入ソースのsorry・admit・新規axiom・資源上限変更は0件。採用済み引用は0件。
全体文書検査は20 Markdown・320 exposition参照を検査し、担当外の
BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの
未解決参照1件で失敗した。計画書のローカルリンクと担当差分の空白検査は成功。

**次の接続。** 通常加群圏の随伴を主Kへ降下させ、制限の準同型保存と合わせて延長の
ホモトピー射影性保存を証明する。U14の主K・導来再構成随伴とその射集合同値の構成を
読み取り専用で確認した。既存の局所化Hom自然性・射影的始域のHom計算を再利用し、
現在の射影解像度による`dgDerivedExtension`と`dgDerivedRestriction`の導来随伴へ接続する。
代表加群上の単位の同定、準同値に沿う全加群の導来同値、解像度変更とbimodule合成の
自然性・単位・結合のcoherenceは引き続き必要である。U12e全体はまだ受け入れない。
その後U16a〜d、U15eの分解版へ進む。局所K-flat版の所有と再利用方針は§0を保持する。
共有一般論への新しいAPI要求はなく、共有ルート・Endomorphism/・係数変更系列は変更していない。

### 17.207 U12e47：全Hom制限・主K随伴・延長の射影性保存と導来Hom同値（2026-10-17）

**追加API。** `Module/RestrictionEnriched.lean`で`moduleRestrictionParam`により
任意パラメータの全次数自然変換を引き戻し、`moduleRestrictionHom`を主Hom endへの
chain mapとして構成した。単位・豊穣合成を保つ`dgModuleRestriction`を定義し、
`dgModuleRestriction_map_eval`と`dgModuleRestriction_onClosed_eq`で、閉零制限が
既存の`moduleRestriction`と一致することを証明した。パラメータ付き変換の引き戻し自体には
対象型のsmallnessは不要。主Hom endを取るdg関手では両対象型をu-smallとする。

`Functor/HomotopyAdjunction.lean`の`DGFunctor.homotopyAdjunction`は、
任意の二つのdg関手の閉零随伴から主ホモトピー圏上の随伴を構成する。
単位・余単位と両三角恒等式を境界商へ送り、対象型のsmallnessは要求しない。
U14の降下実装を参照し、graph固有の同じ降下を別実装せず、このdg一般補題に切り出した。

`Derived/FunctorExtensionProjective.lean`では`dgModuleHomotopyAdjunction`を得た。
制限の主K上の準同型保存と、U14の既存
`moduleHomotopicallyProjective_of_coyoneda_inverts`を読み取り専用で再利用し、
`dgModuleExtension_homotopicallyProjective`を証明した。
これは任意dg関手のgraph延長がホモトピー射影的右加群を保つ定理で、
元のHomのflatness・有界性やFのHom準同型性を仮定しない。

`Derived/FunctorExtensionHom.lean`では、既存の射影的始域の局所化Hom計算と
主K随伴、指定射影解像度による延長計算同型を組み合わせた。
`dgProjectiveDerivedExtensionHomEquiv`、`dgDerivedExtensionHomEquivOnModules`、
`dgDerivedExtensionHomEquiv`により、実際の主導来関手の射集合同値を得た。
この段階では両変数自然性はまだ証明しておらず、導来随伴としては受け入れない。
既存公開APIの名前・型の変更はない。

**検証。** `Checks.DGExtensionProjective`で、独立宇宙の主K随伴・射影性保存・
導来射集合同値、対象型のsmallnessを要求しないdg一般の随伴降下と単位成分、
ZMod 2上の射影性保存を検査した。同チェックとChecks.DGFunctorAdjunction・
Checks.DGFunctorCounit・Checks.DGFunctorExtension・Checks.DGDerivedRestriction・
Checks.DGResolutionComparison・Checks.DerivedBimoduleFullPentagon・Checks.StageEight・
Checks.StageSeven・Spectra.StageTwoの統合ビルド成功（3319 jobs、警告なし）。
主要21宣言の直接公理監査は重複・欠落なく標準3公理以内。監査累計4052宣言。
固定Lean v4.35.0-rc4とMathlib e6bbacd0e1b7307ff6e17da09cd2455f60804fa6を再確認し、
Mathlib HEADとmanifestは一致した。新しいsorry・axiom・引用・資源上限変更は0件。
全体文書検査は20 Markdown・320 exposition参照を検査し、担当外の
BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの
未解決参照1件で失敗した。計画書のローカルリンクと担当差分の空白検査は成功。

**残る接続。** 射集合同値の実際の加群射に対する両変数自然性、解像度liftとの整合性を
証明する。U14の既存局所化Hom自然性APIを再利用して全導来射へ延長し、
導来随伴の単位・余単位と代表加群上の比較の一致を得る。
準同値に沿う全加群の導来同値、解像度変更とbimodule合成の自然性・単位・結合のcoherenceは未完。
U12e全受入→U16a〜d→U15eの分解版という順序と局所K-flat版の並行所有は維持する。
共有一般論への新しいAPI要求はない。共有ルート・Endomorphism/・係数変更系列は変更していない。

### 17.208 U12e48：導来延長Hom同値の両変数自然性と実際の導来随伴（2026-10-17）

**追加API。** `Functor/HomotopyAdjunction.lean`に
`DGFunctor.homotopyAdjunction_homEquiv_map`を追加し、実際の閉零射の像について
主K随伴のHom同値と商への関手が可換であることを証明した。
`Derived/FunctorExtensionProjectiveNaturality.lean`では、射影的始域における
`dgProjectiveDerivedExtensionHomEquiv`の実際の射上の計算式と両変数自然性を証明した。
射の持ち上げは既存`moduleProjectiveToDerived_map_surjective`を再利用する。

`Derived/FunctorExtensionNaturality.lean`で主K経由の計算同型と、任意の指定解像度族による
導来延長計算同型の自然性を証明した。標準解像度を再度指定した計算同型の一致は
`ModuleProjectiveResolution.comparison_self`を用い、選択したchain map自体が恒等であるとは
仮定しない。標準解像度間のliftに対する計算同型の逆射の自然性も得た。

`Derived/FunctorExtensionHomNaturality.lean`では、解像度liftの増大とのsquareを
境界の局所化による等化で証明し、実際の加群射について導来Hom同値の両変数自然性を得た。
`Derived/FunctorExtensionAdjunction.lean`はU14の既存
`localizationHom_naturality_left/right`を読み取り専用で再利用し、
局所化後の任意の射へ自然性を延長する。
`dgDerivedExtensionRestrictionAdjunction`は実際の主導来関手
`dgDerivedExtension ⊣ dgDerivedRestriction`の随伴である。
`dgDerivedExtensionUnit`・`dgDerivedExtensionCounit`と両三角恒等式を公開した。
任意可換環・独立対象宇宙・u-smallな対象型で、元のHomのflatness・有界性や
FのHom準同型性は要求しない。既存公開APIの名前・型の変更はない。

**検証。** `Checks.DGDerivedExtensionAdjunction`は任意の導来射に対する両変数自然性、
導来随伴、両三角恒等式、ZMod 2上の随伴を型検査した。
同チェック、Checks.DGExtensionProjective・Checks.DGFunctorAdjunction・Checks.DGFunctorCounit・
Checks.DGFunctorExtension・Checks.DGDerivedRestriction・Checks.DGResolutionComparison・
Checks.DerivedBimoduleFullPentagon・Checks.StageEight・Checks.StageSeven・Spectra.StageTwoの
統合ビルド成功（3325 jobs、警告なし）。主要21宣言の直接公理監査は重複・欠落なく標準3公理以内。
監査累計4073宣言。今回の受入ソースのsorry・admit・新規axiom・資源上限変更は0件。
採用済み引用は0件。全体文書検査は共有ルート読込時に、担当外の
BhattScholze.Andre.MonicRootedExtension.olean不在で参照収集前に停止した。
担当外のソース・ビルドや共有監査スクリプトは変更していない。

**残る受入条件。** 次は代表加群上の既存往復同型と今回の実際の導来単位の一致を示し、
Hom準同型性の下でその単位の同型性を得る。U14のiso locusと局所化・生成性の既存APIを再利用して
全加群へ拡張し、準同値に沿う導来同値を証明する。
解像度変更と導来bimodule合成・対角単位・結合の自然性およびcoherenceへの接続は未完。
導来随伴を得たことだけでU12e全体を受け入れない。
U12e全受入→U16a〜d→U15eの分解版の順と局所K-flat版の並行所有を維持する。
共有一般論への新しいAPI要求はない。Endomorphism/・係数変更系列は読み取り専用で保持した。

### 17.209 U12e49：代表加群上の実際の単位と導来単位の可逆性（2026-10-17）

**追加API。** `Module/FunctorExtensionRepresentableUnit.lean`で
`functorExtensionUnit_representable`を証明した。代表加群の通常単位に、延長代表加群の
Yoneda同型を制限した射を後合成すると、各成分がFのHom chain mapである既存の
`representableRestrictionMap`に一致する。
`functorExtensionUnit_representable_quasiIso`はHom準同型性だけから通常単位の準同型性を得る。
本質的全射性、元のHomのflatness、有界性は要求しない。

`Derived/FunctorExtensionUnitComputation.lean`では、閉零随伴の単位と構成済みの
`functorExtensionUnit`の一致、および実際の導来随伴のHom同値と構成済み射集合同値の一致を
証明した。後者はMathlibの`Adjunction.mkOfHomEquiv_homEquiv`を再利用し、
随伴のHom同値が構成時の同値と定義的に等しいとは仮定しない。
`dgDerivedExtensionUnit_computation`により、標準解像度Pの延長計算同型をeとすると、
導来単位ηにR(e.hom)を後合成した射は、増大Q(π)の逆、Q上の通常単位η_P、
導来制限計算同型の逆の合成になることを証明した。

既存`dgModuleEnrichedRestrictionAdjunction`の構成を、右関手の等式による直接の書換えから
同じ等式の自然同型に沿う`Adjunction.ofNatIsoRight`へ変更した。
公開名・型・仮定・宇宙は変更していない。成分が恒等射である右関手の比較を明示し、
今回の単位計算で巨大な関手等式の証明を展開しないための変更である。

`Derived/FunctorExtensionRepresentableUnit.lean`の
`functorExtensionUnit_resolution_quasiIso`は、射影的加群上の通常単位が準同型なら、
その任意の射影解像度上でも通常単位が準同型になることを、単位の自然性と
延長による射影的加群間の準同型保存から証明する。
これを標準解像度と導来単位の計算式に適用し、
`dgDerivedExtensionUnit_representable_isIso`を得た。
先行して構成した往復同型の存在だけを根拠にせず、今回の実際の導来随伴の単位自体を判定した。

**検証。** 新規`Checks.DGRepresentableExtensionUnit`は通常単位とHom比較の一致、
二つの閉零随伴モデルの単位の一致、独立宇宙とZMod 2での導来単位の可逆性を検査した。
同チェックと、Checks.DGDerivedExtensionAdjunction以降の既存graph延長・制限・分解比較・
導来bimodule五角形・StageEight・StageSeven・Spectra.StageTwoの統合ビルド成功
（3329 jobs、警告なし）。新規主要8宣言と既存随伴1宣言の計9宣言の直接公理監査は
重複・欠落なく標準3公理以内。新規監査累計4081宣言（今回の再監査1件は重複加算しない）。
今回の受入ソースにsorry・admit・新規axiom・資源上限変更は0件。採用済み引用は0件。
全体文書検査は20 Markdown・320 exposition参照を検査し、担当外の
BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの
未解決参照1件で失敗した。担当外のソース・ビルド・共有監査スクリプトは変更していない。

**残る受入条件。** 次は制限の導来関手についてshift・三角性・余積保存を接続し、
導来随伴の整合的shiftをMathlibから得る。U14の既存iso locusと局所化・生成性APIを再利用して
代表加群上の単位の同型性を全加群へ拡張し、準同値の本質的全射性と合わせて導来同値を得る。
解像度変更と導来bimodule合成・対角単位・結合の自然性およびcoherenceへの接続は未完。
U12e全受入→U16a〜d→U15eの分解版の順と局所K-flat版の並行所有は維持する。
共有一般論への新しいAPI要求はない。Quotient/DerivedComparisonRestriction.leanを参照したが、
局所K-flat版・Verdier/・Endomorphism/・係数変更系列は編集していない。

### 17.210 U12e50：導来制限の三角性・余積保存と全対象の単位の可逆性（2026-10-17）

**shiftと三角性。** `Derived/RestrictionShift.lean`は、全Hom制限と既存の導来制限の
因子分解を`Localization.Lifting`として固定し、U14の
`dgModuleFunctorCommShift`を局所化して`dgDerivedRestrictionCommShift`を構成する。
`Derived/RestrictionTriangles.lean`では、主K経由の制限と導来制限の自然同型および
そのshift整合性を証明した。U14の`dgModuleFunctorHomotopyIsTriangulated`を再利用し、
実際の導来制限の三角性と加法性を得た。
`Derived/FunctorExtensionTriangles.lean`はMathlibの三角随伴APIを用いて、
実際の導来随伴と整合する延長のshift・三角性、単位と余単位のshift整合性を公開する。
dg関手のshiftやcone像の成分計算は新設せず、U14の既存一般APIを用いた。

**compactと余積。** `Derived/FunctorExtensionPerfect.lean`は既存のPerfの生成普遍性と
代表加群の延長計算から、導来延長がperfect対象を保つことを証明する。
並行U13dの`moduleCompact_perfect`を読み取り専用で再利用し、compact保存も得た。
外部のcompact⇒perfect仮定は追加していない。
`Derived/CompactAdjunctionCoproducts.lean`では、独立の多対象dg圏D/Eの主導来圏間の
加法的随伴について、左随伴がcompactを保てば右随伴がu-small余積を保つことを証明した。
U14のcompactな始域からの射による同型判定と、既存の有限支持による射の判定を再利用する。
この補題はgraph固有ではなく、指定した随伴とcompact保存の証拠を受け取る。

**実際の単位の全対象での可逆性。** `Derived/FunctorExtensionUnitAll.lean`では、
上記結果を適用して`dgDerivedRestriction_preservesCoproductsOfShape`を得た。
U14の`derivedNatTransIsoLocus`に、Mathlibの`NatTrans.retractArrowApp`を使うretract閉性を追加し、
今回の導来単位の同型性を代表加群からperfect対象へ拡張した。
U14の`moduleLocalizing_all`と余積保存により、`dgDerivedExtensionUnit_isIso_all`を証明した。
仮定は`HomQuasiIso F`だけで、本質的全射性、元のHomのflatness、有界性を要求しない。
`dgDerivedExtensionFullyFaithful`はこの実際の単位から導来延長の完全忠実性を与える。
既存公開APIの名前・型の変更はない。

**検証。** 新規`Checks.DGDerivedUnitAll`は独立宇宙での制限の三角性、単位のshift整合性、
余積保存、compact保存、任意の導来対象の単位の可逆性と完全忠実性、ZMod 2上の全対象の判定を検査した。
同チェックと既存の代表単位・導来随伴・graph延長・制限・分解比較・導来bimodule五角形・
StageEight・StageSeven・Spectra.StageTwoの統合ビルド成功（3389 jobs、警告なし）。
主要28宣言の直接公理監査は重複・欠落なく標準3公理以内。新規監査累計4109宣言。
今回の受入ソースのsorry・admit・新規axiom・資源上限変更は0件。採用済み引用は0件。
全体文書検査は20 Markdown・320 exposition参照を検査し、担当外の
BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの
未解決参照1件で失敗した。担当外のソース・ビルド・共有監査スクリプトは変更していない。

**次の接続。** 準同値の本質的全射性から、Fの像の代表加群が終域のすべての代表加群を
主導来圏内の同型まで含むことを示す。これを既存の零性検出へ渡して導来制限の保守性を証明し、
右三角恒等式から余単位の可逆性と実際の導来同値を得る。
解像度変更と導来bimodule合成・対角単位・結合の自然性およびcoherenceは引き続き未完。
U12e全受入→U16a〜d→U15eの分解版の順と局所K-flat版の並行所有を維持する。
共有一般論への新しいAPI要求はない。Perfect/・Endomorphism/・局所K-flat版の所有範囲は編集していない。

### 17.211 U12e51：準同値に沿う導来同値とdg圏解像度の主導来加群比較（2026-10-17）

**保守性。** `Derived/RestrictionConservative.lean`でdg Yonedaを主Kへ送り、
加群の主導来圏へ局所化する`representableHomotopyToDerived`と実際の代表加群での計算同型を構成した。
`dgDerivedExtension_representable_essImage`は主K上の本質的全射性だけから、
延長の像に終域の全代表加群が導来同型まで含まれることを示す。
既存の導来随伴、shift比較、`moduleRepresentables_detect_zero`を再利用し、
`dgDerivedRestriction_reflectsZero`と`dgDerivedRestriction_reflectsIso`を証明した。
これらはHom準同型性を必要とせず、F.onHomotopyの本質的全射性だけを仮定する。
明示した条件下で利用する`ReflectsIsomorphisms`の証拠も公開した。

**実際の導来同値。** `Derived/FunctorDerivedEquivalence.lean`では、
前項の全対象の導来単位の可逆性、右三角恒等式、今回の保守性から
`dgDerivedExtensionCounit_isIso_all`を得た。
`dgFunctorDerivedEquivalence`は任意の`QuasiEquivalence F`について
主導来圏D(D)≌D(E)を構成し、順方向が既存の`dgDerivedExtension`、逆方向が
既存の`dgDerivedRestriction`であること、単位・余単位が実際の導来随伴のものと一致することを公開する。
任意可換環、独立対象宇宙、u-smallな対象型で、元のHomのflatness・有界性は仮定しない。
抽象的な同値の存在だけでなく、指定された実際の両関手とその単位・余単位を保持する。

**dg圏解像度への適用。** `Resolution/DerivedEquivalence.lean`は指定K-flat dg圏解像度Pの
増大に沿う`P.moduleDerivedEquivalence`、標準zigzagの両脚に沿う導来同値を構成する。
`P.changeModuleDerivedEquivalence Q`は元のdg圏を経由した二つの指定解像度の主導来加群圏の比較で、
公開した順方向・逆方向は対応する実際の導来延長と導来制限の合成である。
解像度sourceの宇宙は独立に許し、元のdg圏のHomに局所K-flat性は課さない。
既存公開APIの名前・型の変更はない。

**検証。** 新規`Checks.DGFunctorDerivedEquivalence`は本質的全射性だけでの保守性、
実際の導来同値と逆関手・単位の一致、指定解像度の比較と独立source宇宙、ZMod 2上の同値を検査した。
同チェックと既存の全対象単位・代表単位・導来随伴・graph延長・制限・分解比較・
導来bimodule五角形・StageEight・StageSeven・Spectra.StageTwoの統合ビルド成功
（3393 jobs、警告なし）。主要18宣言の直接公理監査は重複・欠落なく標準3公理以内。
新規監査累計4127宣言。今回の受入ソースにsorry・admit・新規axiom・資源上限変更は0件。
採用済み引用は0件。
全体文書検査は20 Markdown・320 exposition参照を検査し、担当外の
BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの
未解決参照1件で失敗した。計画書のローカルリンクと担当差分の空白検査は成功。

**残るU12e受入条件。** 今回の主導来加群圏の不変性を、局所K-flatな比較source間の
積dg関手と既存の右加群–bimodule比較同値を通して、導来bimodule制限の同値性へ接続する。
tensor積のHom準同型保存に必要な複体のK-flat性を明示し、元のunderived積上への無条件の同値は主張しない。
その後、解像度変更と導来bimodule合成・対角単位・結合の自然性およびcoherenceを接続する。
今回のdg準同値不変性だけでU12e全体を受け入れず、受入後のU16a〜d、U15eの分解版の順を保持する。
共有一般論への新しいAPI要求はない。共有ルート・Perfect/・Endomorphism/・局所K-flat版は編集していない。

### 17.212 U12e52：指定解像度の導来bimodule圏の比較同値（2026-10-17）

**oppositeと積の準同値。** `Category/OppositeHomotopy.lean`はMathlibの豊穣opposite比較を
境界関係の商へ送り、smallnessなしで`homotopyOppositeFunctor`を構成する。
`Functor/QuasiEquivalenceOpposite.lean`はoppositeによる準同値保存を証明する。
`Functor/QuasiEquivalenceTensor.lean`はF:B→D、G:C→Eに対し、
CとDの局所K-flat性を明示して`quasiEquivalence_tensor`を証明する。
Hom写像をF⊗id、id⊗Gの順に分解した際の相手のK-flat性をそれぞれ使う。
積関手の主K上の本質的全射性自体にはflatnessもsmallnessも不要である。

**実際の導来制限。** `Derived/BimoduleModuleEquivalence.lean`は、既存の閉零での
右加群–bimodule同値と値ごとの準同型の一致から、同じ射のクラスの局所化として
`rightModuleBimoduleDerivedEquivalence`を構成する。Homのflatnessは要求しない。
`Derived/BimoduleRestrictionEquivalence.lean`は既存の導来bimodule制限と積dg圏上の
右加群の導来制限との自然な比較正方形を局所化の普遍性で構成する。
F、Gの準同値性および前述の交差する局所K-flat仮定から、既存の実際の
`derivedBimoduleRestriction`そのものを順方向とする同値を得る。
既存公開APIの名前・型の変更はない。

**指定解像度。** `Resolution/BimoduleDerivedEquivalence.lean`は標準zigzagの両脚の
既存の制限関手`comparisonLeft`、`comparisonRight`を順方向とする同値を構成する。
比較sourceと解像度sourceの既証の局所K-flat性を使い、元のdg圏のHomには仮定しない。
`canonicalComparisonEquivalence`と`changeEquivalence`は、独立のsource宇宙を持つ
両側の指定解像度の導来bimodule圏を同時に比較する。左脚は元の対象型のsmallnessも要求しない。

**検証。** 新規`Checks.DGBimoduleResolutionEquivalence`はopposite・積の必要仮定、
実際の制限関手との一致、独立した四つの解像度source宇宙、ZMod 2の場合を検査した。
既存の導来同値・単位・随伴・graph延長・制限・分解比較・導来bimodule五角形・
StageEight・StageSeven・Spectra.StageTwoとの統合ビルド成功（3400 jobs、警告なし）。
主要28宣言の直接公理監査は重複・欠落なく標準3公理以内。新規監査累計4155宣言。
今回の7受入Leanファイルのsorry・admit・新規axiom・資源上限変更は0件。
採用済み引用は0件。全体文書検査は20 Markdown・320 exposition参照を検査し、
担当外のBhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの
未解決参照1件で失敗した。担当外のソース・共有監査スクリプトは変更していない。

**残る受入条件と分担。** 圏同値の構成だけでU12e全体を受け入れない。
解像度変更と既存の導来bimodule合成・対角単位・結合子の比較自然同型、
および解像度変更のcoherenceが残る。準同値に沿う制限と導来tensor合成の比較を構成し、
既存の局所K-flat合成系の三角形・五角形を移すことが次の作業である。
U12e受入→U16a〜d→U15e分解版の順を維持する。
U15e局所K-flat版と続くU17b局所K-flatの場合はU17a/U13d側の担当であり、
分解版の着手時に`Quotient/DerivedComparison*.lean`と`Verdier/`の成果を読み再利用する。
新しい共有モデル圏API要求はない。共有ルート・Perfect/・Endomorphism/・局所K-flat版は編集していない。

### 17.213 U12e53：制限tensorの比較chain mapと代表加群・反復制限の計算（2026-10-17）

**実際の比較写像。** `Tensor/RestrictionComparison.lean`で、任意のdg関手F:D→Eと
右E加群M・左E加群Nに対し、(F* M)⊗_D(F* N)→M⊗_E Nを構成した。
`restrictionComparison`は既存の全次数balanced族の引き戻しを余等化子へ降ろしたchain mapである。
生成元の包含との可換式、任意次数の純粋tensorを同じ元へ送る式、任意のbalanced族への後合成、
作用と可換な両変数のchain map族に関する自然性を証明した。
右作用の既存Koszul交換を再利用し、比較自体には追加の符号を入れない。
`Tensor/RestrictionComparisonNaturality.lean`は実際の`moduleRestriction`と
`rightTensorFunctor`を使う`restrictionTensorComparison`へ束ねる。
元の加群圏の射は引き続き全Hom自然な閉零射であり、通常関手圏の射へ置き換えていない。

**代表加群での準同型性。** `Tensor/RestrictionComparisonYoneda.lean`は既存の
`representableRestrictionMap`を制限された左因子とtensorし、今回の比較とYoneda評価に続けると
source側のYoneda評価そのものになることを証明する。
`restrictionComparison_representable_quasiIso`は`HomQuasiIso F`と
`leftModuleRelativeKFlat A D (F.comp N)`の下で、M=representable(Fd)における
実際の比較chain mapが準同型であることを示す。本質的全射性はこの段階では使わない。
制限後の左相対K-flat性は明示的な仮定であり、準同値だけから自動的に導出したとは主張しない。

**反復制限の比較。** `Tensor/RestrictionComparisonCoherence.lean`ではF:D→E、G:E→Tに対し、
反復制限と合成関手による制限のtensorを恒等成分で比べる`restrictionComparisonCompIso`を構成した。
その順逆の生成元での計算と、二段階の比較chain mapが一段階の比較と可換になる
`restrictionComparison_comp`を証明した。これはunderived balanced tensorでの整合性であり、
U12eが求める導来bimodule合成・結合子のcoherence全体の受入とは区別する。
既存公開APIの名前・型の変更はない。

**検証。** Lean v4.35.0-rc4、Mathlib manifest/HEAD
`e6bbacd0e1b7307ff6e17da09cd2455f60804fa6`を再確認した。
新規`Checks.DGTensorRestrictionComparison`は独立対象宇宙、任意の正負整数次数、
実際の関手上の自然性、代表加群での準同型性、反復制限との整合性、ZMod 2の場合を検査した。
既存の解像度bimodule同値・導来随伴・単位・制限・合成五角形・StageEight・StageSeven・
Spectra.StageTwoとの統合ビルド成功（3405 jobs、警告なし）。
主要20宣言の直接公理監査は重複・欠落なく標準3公理以内。新規監査累計4175宣言。
今回の5受入Leanファイルのsorry・admit・新規axiom・資源上限変更は0件。採用済み引用0件。
全体文書検査は20 Markdown・320 exposition参照を検査し、担当外の
BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの
未解決参照1件で失敗した。担当外ソース・共有ルート・共有監査スクリプトは変更していない。

**次の接続と残件。** 今回の比較を外側の両dg作用に自然なbimodule射へ束ね、
既存の指定解像度による導来合成計算と接続する。制限された因子のK-flat性を無条件に仮定せず、
必要な場合は制限後の解像度を使う。一般の導来bimodule合成の比較自然同型、対角単位・結合子との
整合性と解像度変更coherenceは引き続き未完で、U12e全体は未受入である。
その後U16a〜d、U15e分解版へ進む。局所K-flat版のQuotient/DerivedComparison*・Verdier/、
Endomorphism/、ScalarExtension*は再利用対象であり編集していない。
共有モデル圏一般論への新しいAPI要求はない。

### 17.214 U12e54：中間dg圏の制限と全Hom自然なbimodule合成比較（2026-10-17）

**既存の豊穣制限による二因子。** `Bimodule/MiddleRestriction.lean`ではF:D→Cに対し、
P:B–Cの左側の制限をFへの前合成、Q:C–Eの右側の制限を既存の
`dgModuleRestriction A D C F.op`への後合成として定義した。
いずれもMathlibのdg関手の合成であり、右加群の全Hom endを保持する。
左因子のleftAt比較と、右因子の左作用の全次数評価を公開した。
既存の`bimoduleRestriction`の名前・型・定義は変更していない。

**実際のbimodule射。** `Tensor/BimoduleMiddleComparison.lean`は前項の
`BalancedTensor.restrictFamily`を再利用し、中間圏を制限した合成の各値から元の合成へ送る
`middleRestrictionComparisonValue`を構成した。包含と任意次数の純粋tensorでの計算式を公開する。
`Tensor/BimoduleMiddleActions.lean`は外側の右B作用と左E作用に対する可換性を証明する。
右作用のKoszul符号は先頭因子の次数との積で既存の合成公式と一致し、左作用には追加符号がない。
純粋斉次元での計算から主Hom複体の前後合成の等式へ戻した。
`Tensor/BimoduleMiddleMap.lean`はこれを全Hom自然な右加群射族、さらに
`middleRestrictionComparisonMap`という実際の閉零bimodule射へ束ねる。
値での計算に加え、外側の任意次数Homに対する自然性を証明済みである。
この段階ではEの対象型のsmallnessも要求しない。

**制限後の解像度を使う導来比較。** `Derived/BimoduleMiddleComparison.lean`は
制限された後因子への増大qを合成に入れる`middleRestrictionResolvedMap`を定義し、
厳密な増大squareに関する合成式を証明した。
`middleRestrictionSourceComputation`は既存の全導来合成と指定右K-flat解像度での計算を結ぶ。
`derivedMiddleRestrictionComparison`は、後因子Qの右K-flatモデルと、制限後の右K-flat解像度Rを
指定して、既存の二つの`derivedBimoduleComposeFunctor`の値の間の射を構成する。
`derivedMiddleRestrictionCanonicalComparison`は制限後の既存標準semifree解像度を選んだもの。
仮定する局所Hom K-flat性は終端Eのもので、C・Dの局所Hom K-flat性や
制限されたQの右相対K-flat性を追加要求しない。
元のQの右K-flatモデルは既存の`rightKFlatResolutionObj`で得られる。
これは比較射の構成であり、準同値Fの場合の可逆性・解像度独立性は未証明である。

**検証。** 新規`Checks.DGBimoduleMiddleComparison`は独立した四つの対象宇宙、
Eのsmallnessなしでの全Hom自然な射、任意整数次数の値の計算、
制限後のK-flat仮定なしでの標準解像度による導来比較、ZMod 2の場合を検査した。
既存のtensor制限比較・解像度bimodule同値・導来随伴・単位・制限・導来bimodule五角形・
StageEight・StageSeven・Spectra.StageTwoとの統合ビルド成功（3411 jobs、警告なし）。
主要25宣言の直接公理監査は重複・欠落なく標準3公理以内。新規監査累計4200宣言。
今回の6受入Leanファイルのsorry・admit・新規axiom・資源上限変更は0件。採用済み引用0件。
Lean v4.35.0-rc4とMathlib manifest/HEAD
`e6bbacd0e1b7307ff6e17da09cd2455f60804fa6`を再確認した。

全体文書検査は20 Markdown・320 exposition参照を検査し、担当外の
BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの
未解決参照1件で失敗した。計画書のローカルリンクと担当差分の空白検査は成功。

**残件と次工程。** 今回の比較射を両因子の閉零射および既存の積dg圏表示の制限と比較し、
増大squareがホモトピーで可換な場合の解像度独立性を証明する。
そのうえで準同値の場合の可逆性を示し、全導来圏上の合成比較自然同型へ降ろす。
対角単位・結合子との整合性と解像度変更coherenceは引き続き未完であり、U12e全体は未受入。
U12e受入→U16a〜d→U15e分解版の順と、局所K-flat版の並行所有を維持する。
共有モデル圏一般論への新しいAPI要求はない。
共有ルート・共有監査スクリプト・Perfect/・Endomorphism/・ScalarExtension*・
Quotient/DerivedComparison*・Verdier/は編集していない。

### 17.215 U12e55：両因子の自然性と前因子の全導来圏への比較の降下（2026-10-17）

**実際の閉零制限関手。** `Bimodule/MiddleRestrictionMaps.lean`は前項の二因子の制限を
全Hom自然な閉零射へ拡張し、`middleLeftRestrictionFunctor`、`middleRightRestrictionFunctor`を構成する。
左側は指定dg関手Fへの前合成、右側は既存の`moduleRestriction`による射の制限を使う。
右側の射族が左作用の全Hom endに対して自然であることを、各対象の主Homへの評価で証明した。
両側の値での評価式と恒等・合成の保存を公開する。
既存の積dg圏表示の`bimoduleRestriction`の名前・型・定義は変更していない。

**両変数の自然性。** `Tensor/BimoduleMiddleNaturality.lean`は既存の`composeMap`と
`composeValueMap`を再利用し、前項の比較射が両因子の任意の閉零射と可換であることを証明する。
`middleRestrictionComparisonNatTrans`は実際の閉零bimodule圏の積上の自然変換である。
対象型Eのsmallness、Fの準同値性、局所Homのflatnessはこの段階では不要。
`Derived/BimoduleMiddleNaturality.lean`は解像度への増大も変わる場合の比較を証明し、
厳密な増大squareの下で両因子の射と解像度の射に関する自然性を得た。
固定された後因子Q・制限後のモデルR・増大qに対し、前因子の閉零圏上の
`middleRestrictionResolvedNatTrans`へ束ねている。

**導来比較の自然な族。** `Derived/BimoduleMiddleComparisonFamily.lean`は既存の
全導来合成の指定解像度での計算自然同型を前合成・whiskeringで組み合わせる。
`derivedMiddleRestrictionComparisonFamily`は前因子の閉零圏上で自然であり、
その成分が前項の実際の`derivedMiddleRestrictionComparison`に一致することを証明した。
単なる対象ごとの比較射から、すべての閉零射と可換な族へ進めた。

**前因子の全導来圏。** `Derived/BimoduleMiddleComparisonLocalization.lean`では、
sourceの関手族が値ごとの準同型を反転することを、左制限による準同型保存と
既存の導来合成から示した。`middleDerivedSourceLift`はこの合成の指定局所化への延長であり、
局所化前との厳密なfactorizationと`Localization.Lifting`を備える。
`derivedMiddleRestrictionComparisonLocalized`は前因子の全導来圏上の自然変換で、
後因子Qの指定右K-flatモデルと制限後の指定右K-flat解像度Rを使う。
局所化前の対象で実際の比較射を計算する成分公式も証明した。
制限されたQそのもののK-flat性、C・Dの局所Hom K-flat性は仮定していない。
sourceを既存の積dg圏表示の導来制限と導来合成の合成に同定する比較は、別途残す。

**検証。** 新規`Checks.DGBimoduleMiddleNaturality`は独立対象宇宙、後端smallnessなしでの
両因子自然性、指定解像度の導来比較との成分一致、前因子の全導来圏上の自然変換、
ZMod 2の場合を検査した。既存の中間圏比較・tensor制限・分解同値・導来随伴・単位・制限・
導来bimodule五角形・StageEight・StageSeven・Spectra.StageTwoとの統合ビルド成功
（3417 jobs、警告なし）。主要27宣言の直接公理監査は重複・欠落なく標準3公理以内。
新規監査累計4227宣言。今回の6受入Leanファイルのsorry・admit・新規axiom・資源上限変更は0件。
採用済み引用0件。Lean v4.35.0-rc4とMathlib manifest/HEAD
`e6bbacd0e1b7307ff6e17da09cd2455f60804fa6`を再確認した。
全体文書検査は20 Markdown・320 exposition参照を検査し、担当外の
BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの
未解決参照1件で失敗した。計画書のローカルリンクと担当差分の空白検査は成功。

**残件。** 増大squareがホモトピーで可換な場合の解像度独立性、後因子も全導来圏へ降ろした比較、
既存の積dg圏表示の制限との同定、準同値の場合の可逆性が残る。
これらを解像度変更の導来合成比較へ接続し、対角単位・結合子との整合性とcoherenceを証明する。
U12e全体は引き続き未受入で、受入後にU16a〜d、U15e分解版へ進む。
共有モデル圏一般論への新しいAPI要求はない。共有ルート・共有監査スクリプト・Perfect/・
Endomorphism/・ScalarExtension*・Quotient/DerivedComparison*・Verdier/は編集していない。

### 17.216 U12e56：合成後のsourceホモトピー同一視と増大square（2026-10-17）

**cylinder計算。** 任意の前因子との合成は任意の準同型を保存するとは限らないため、
必要なホモトピー同一視をK-flat仮定なしで別に証明した。
`Bimodule/RightRestrictionNaturality.lean`は既存の積dg圏表示の右制限比較を自然同型へ束ねる。
`Tensor/TensorModuleNaturality.lean`は既存の`tensorModuleIso`の生成複体に関する自然性を証明し、
標準interval射影を任意の左因子とbalanced tensorした射が準同型であることを示す。
`Tensor/RestrictionCylinder.lean`は制限と標準cylinder射影の可換式を計算し、
制限後の相対K-flat性なしで、制限された射影のtensor像が準同型になることを証明する。
全体で微分次数やcontracting homotopyの規約は既存のintervalとtensor実装をそのまま使う。

**任意の前因子。** `Tensor/BimoduleCylinder.lean`の`composeAfter`は既存の合成双関手で
前因子Pを固定する通常関手である。
`composeAfter_sourcePrecylinderProjection_quasiIso`は、積dg圏上の主加群の標準cylinderを
既存の右加群–bimodule同値で送った射影が、任意のPとの合成後も値ごとの準同型になることを示す。
P・source加群のK-flat性、射影性、Homのflatnessは要求しない。
右加群制限の自然比較と各値でのtensor計算を用い、独立な対象ごとのホモトピーを
全dg自然なホモトピーの代用にはしていない。

**ホモトピー同一視。** `Derived/BimoduleComposeHomotopy.lean`は前項の射影の導来像を反転し、
cylinderの二つの包含の像を同一視する。
`composeAfter_equalizes_source_boundary`と`composeAfter_map_eq_of_source_homotopy`は
積dg圏表示の全dg自然な境界・主K上の射の一致を、合成後の主導来圏での一致へ送る。
`composeAfter_map_eq_of_inverse_source_homotopy`は同値の余単位の自然性で任意の実際の
bimodule射へ戻した形であり、やはりflat条件は課さない。

**増大squareへの適用。** `Derived/BimoduleMiddleHomotopy.lean`では、
`middleRestrictionResolvedMap_eq_of_source_homotopy`が増大射を全dg自然なホモトピーで替えた際の
比較の計算射の導来像の一致を与える。
`middleRestrictionResolvedMap_comp_of_source_homotopy`は、解像度の射rと増大s・qについて、
r≫sとqの積dg圏表示の主Kでの一致から、合成後の導来圏での増大squareの可換性を得る。
前項の厳密な増大squareの式を、この主K上の仮定まで弱めた。
これは計算射の整合性であり、全導来比較自然変換の解像度独立性の受入とはまだ区別する。
既存公開APIの名前・型・定義は変更していない。

**検証。** 新規`Checks.DGBimoduleComposeHomotopy`は独立対象宇宙で、flat条件のない
cylinder射影の準同型性と実際のbimodule射のホモトピー同一視、ZMod 2の場合を検査した。
既存の中間圏自然性・比較・tensor制限・解像度同値・導来随伴・単位・制限・導来bimodule五角形・
StageEight・StageSeven・Spectra.StageTwoとの統合ビルド成功（3424 jobs、警告なし）。
主要16宣言の直接公理監査は重複・欠落なく標準3公理以内。新規監査累計4243宣言。
今回の7受入Leanファイルのsorry・admit・新規axiom・資源上限変更は0件。採用済み引用0件。
Lean v4.35.0-rc4とMathlib manifest/HEAD
`e6bbacd0e1b7307ff6e17da09cd2455f60804fa6`を再確認した。
全体文書検査は20 Markdown・320 exposition参照を検査し、担当外の
BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの
未解決参照1件で失敗した。計画書のローカルリンクと担当差分の空白検査は成功。

**次の接続。** 今回のホモトピー可換な計算squareを、既存の導来合成の指定解像度計算自然同型と
組み合わせて、`derivedMiddleRestrictionComparison`および前因子の全導来圏上の比較の
解像度独立性へ接続する。その後、後因子の導来化、既存の積dg圏表示の制限との同定、
準同値の場合の可逆性を進める。対角単位・結合子との整合性とcoherenceも残り、U12e全体は未受入。
U12e受入→U16a〜d→U15e分解版の順を維持する。共有一般論への新しいAPI要求はない。
共有ルート・共有監査スクリプト・Perfect/・Endomorphism/・ScalarExtension*・
Quotient/DerivedComparison*・Verdier/は編集していない。

### 17.217 U12e57：導来中間圏比較の制限後semifree解像度からの独立性（2026-10-17）

**値での計算同型の変換則。** `Derived/BimoduleCompositionResolutionValues.lean`は
既存の`derivedBimoduleComposeResolutionComputation_naturality`を再利用し、
指定解像度による値の計算同型`derivedBimoduleComposeResolutionValueIso`を構成した。
増大squareが導来圏で可換なら、値の計算同型の変更は既存の`composeMap`の導来像によることを示す。
`derivedComposeWithMap_computation`が局所化前の値での可換squareを補う。
`Derived/BimoduleSourceHomotopy.lean`は既存のsemifree比較のホモトピー同一視と
右加群–bimodule同値の余単位の自然性から、任意の実際のbimodule射の逆表示での主Kの一致を
主導来圏の射の一致へ送る補助APIを公開する。

**実際の比較射の一致。** `Derived/BimoduleMiddleIndependence.lean`は、
増大squareと合成後の計算squareの二つの導来可換性から
`derivedMiddleRestrictionComparison`自体の一致を示す。
`derivedMiddleRestrictionComparison_eq_of_source_homotopy`は前項のホモトピー整合性を適用し、
増大squareが積dg圏表示の主Kで可換なら十分であることを証明する。
この段階ではFの準同値性を必要としない。

**任意の制限後semifree解像度。** `Derived/BimoduleSemifreeComposeComparison.lean`は
既存の任意semifree解像度間の比較射と、sourceでの射影解像度比較のホモトピー可換式を使う。
`composeAfter_comparison_fac`は、任意の前因子と合成した後も、標準の比較増大squareが
導来圏で可換であることを証明する。前因子のflatnessを追加せず、前項のcylinder計算を再利用する。
`Derived/BimoduleMiddleSemifreeIndependence.lean`の
`derivedMiddleRestrictionComparison_semifree_independent`は、制限後に選ぶ任意の二つの
semifree解像度R・Sについて、実際の導来比較射が一致することを証明した。
追加の比較射・可換squareの仮定を利用者に要求しない。
同じ独立性を前因子の閉零圏上の自然変換と、前因子の全導来圏上の自然変換にも証明した。
`derivedMiddleRestrictionCanonicalLocalized`は既存の制限後標準semifree解像度を使う
全導来圏上の自然変換であり、任意の指定semifree解像度を使う自然変換と一致する。
Qの指定右K-flatモデルと終端Eの局所Hom K-flat性を保持し、制限されたQ自体のK-flat性や
C・Dの局所Hom K-flat性は追加していない。
任意の単なる右K-flat解像度について無条件の独立性を示したとの主張とは区別する。
既存公開APIの名前・型・定義は変更していない。

**検証。** 新規`Checks.DGBimoduleMiddleIndependence`は独立した四つの対象宇宙、
追加squareの仮定なしでの任意の二つのsemifree解像度の比較射の一致、
前因子の全導来圏上の自然変換の一致、標準解像度との一致、ZMod 2の場合を検査した。
既存のホモトピー・中間圏自然性・tensor制限・解像度同値・導来随伴・単位・制限・
導来bimodule五角形・StageEight・StageSeven・Spectra.StageTwoとの統合ビルド成功
（3430 jobs、警告なし）。主要14宣言の直接公理監査は重複・欠落なく標準3公理以内。
新規監査累計4257宣言。今回の6受入Leanファイルのsorry・admit・新規axiom・資源上限変更は0件。
採用済み引用0件。Lean v4.35.0-rc4とMathlib manifest/HEAD
`e6bbacd0e1b7307ff6e17da09cd2455f60804fa6`を再確認した。
全体文書検査は20 Markdown・320 exposition参照を検査し、担当外の
BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの
未解決参照1件で失敗した。計画書のローカルリンクと担当差分の空白検査は成功。

**残件。** 後因子の射に関する自然性と全導来化、既存の積dg圏表示の制限との同定、
準同値の場合の比較の可逆性を進める。それらをdg圏解像度変更へ適用し、
導来合成・対角単位・結合子の整合性とcoherenceを仕上げる。
U12e全体は未受入であり、U12e受入→U16a〜d→U15e分解版の順を維持する。
共有モデル圏一般論への新しいAPI要求はない。共有ルート・共有監査スクリプト・Perfect/・
Endomorphism/・ScalarExtension*・Quotient/DerivedComparison*・Verdier/は編集していない。

### 17.218 U12e58：後因子自然性と両因子の全導来圏上の比較（2026-10-17）

**異なるsemifree解像度間の持ち上げ。** `Derived/BimoduleSemifreeLift.lean`は
既存の射影解像度の`lift`を積dg圏表示の同値で戻す。
元の後因子間の任意の射を、指定された異なる二つのsemifree解像度間へ持ち上げる。
その増大squareの主導来圏での可換性と、任意の前因子と合成した後の導来可換性を証明した。
持ち上げの厳密な可換性や前因子のflatnessは要求しない。
前項のcylinderによるsourceホモトピー同一視を再利用している。

**後因子の射と計算同型。** `Derived/BimoduleCompositionValueNaturality.lean`は
既存の導来合成の指定解像度計算自然性を値での計算へ移し、後因子の射を含む可換squareを公開する。
`Derived/BimoduleMiddleSecondFactor.lean`は、増大と計算の二つの導来可換squareから、
実際の`derivedMiddleRestrictionComparison`の後因子自然性を導く。
`Derived/BimoduleMiddleSemifreeSecondFactor.lean`は指定semifree解像度の持ち上げを適用して、
追加squareの仮定を利用者に要求しない自然性を証明する。
特に標準解像度による比較射は任意の右K-flat後因子の閉零射と可換である。
`Derived/BimoduleMiddleSecondFamily.lean`はこれを自然変換の等式へ束ね、
前因子の全導来圏上の`derivedMiddleRestrictionCanonicalLocalized`についても後因子自然性を証明した。
局所化の`comp_liftNatTrans`で、局所化前の自然性を保持している。

**後因子も全導来化。** `Derived/BimoduleMiddleKFlatFamily.lean`はsourceの後因子への作用の
恒等・合成を証明し、右K-flat後因子の圏から前因子の全導来圏上の関手への関手族
`middleDerivedSourceKFlatFunctor`を構成する。標準比較をこの圏上の自然変換へ束ね、
source関手族が値ごとの指定準同型を反転することを示した。
制限された後因子自体のK-flat性を使わず、既存の導来合成と制限の準同型保存を使う。
`Derived/BimoduleMiddleFullComparison.lean`は右K-flat後因子の指定局所化へ降ろし、
既存の`derivedRightKFlatReplacement`および`rightKFlatReplacementCounitIso`を通して
`middleFullDerivedSource`と`middleFullDerivedComparison`を構成した。
両変数とも既存の全導来bimodule圏上にあり、後因子の任意の導来射・前因子の任意の導来射に自然。
targetは既存の`derivedBimoduleComposeFunctor`そのものである。
右K-flat局所化前で標準比較へ戻る計算式と、全導来後因子での置換による成分計算式も公開した。
局所Hom K-flat性の仮定は終端Eだけで、C・Dや制限後の因子へ追加していない。
sourceを既存の積dg圏表示の導来制限と導来合成の合成に同定する比較は、別途残す。
今回構成したのは自然変換であり、準同値Fの場合の自然同型性は未証明である。
既存公開APIの名前・型・定義は変更していない。

**検証。** 新規`Checks.DGBimoduleMiddleFullComparison`は独立した四つの対象宇宙、
C・Dの局所Hom-flat性および制限後のK-flat仮定なしでの全導来比較、
両変数それぞれの任意の導来射に対する自然性、ZMod 2の場合を検査した。
既存の解像度独立性・ホモトピー・中間圏自然性・tensor制限・解像度同値・導来随伴・単位・制限・
導来bimodule五角形・StageEight・StageSeven・Spectra.StageTwoとの統合ビルド成功
（3438 jobs、警告なし）。主要37宣言の直接公理監査は重複・欠落なく標準3公理以内。
新規監査累計4294宣言。今回の8受入Leanファイルのsorry・admit・新規axiom・資源上限変更は0件。
採用済み引用0件。Lean v4.35.0-rc4とMathlib manifest/HEAD
`e6bbacd0e1b7307ff6e17da09cd2455f60804fa6`を再確認した。
全体文書検査は20 Markdown・320 exposition参照を検査し、担当外の
BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの
未解決参照1件で失敗した。計画書のローカルリンクと担当差分の空白検査は成功。

**次工程と残件。** sourceを既存の導来制限と導来合成の合成へ比較し、準同値の場合の可逆性を証明する。
これをdg圏解像度変更の比較へ適用し、導来合成・対角単位・結合子の整合性とcoherenceを仕上げる。
U12e全体は未受入であり、受入後にU16a〜d、U15e分解版へ進む。
共有モデル圏一般論への新しいAPI要求はない。共有ルート・共有監査スクリプト・Perfect/・
Endomorphism/・ScalarExtension*・Quotient/DerivedComparison*・Verdier/は編集していない。


### 17.219 U12e59：明示的uncurry表示と左右制限のHom比較（2026-10-17）

**表示の比較。** `Bimodule/UncurryClosedFunctor.lean`は既存の全Hom自然性を使い、
閉零bimodule射を積dg圏上の左加群射へ送る`uncurryMap`と`uncurryFunctor`を構成した。
`uncurryCounitIso`は既存の戻り関手との合成を恒等関手へ比較する自然同型である。
各値で恒等となる右加群同型族を`moduleIsoMk`と`isoOfFamily`で束ね、
全次数の左作用との自然性も証明した。
`Bimodule/ExplicitRightModuleFunctor.lean`の`rightModuleFunctor`はこれを既存の
左加群・反対圏上の右加群比較へ接続する。
`rightModuleFunctor_map_value`は閉零射の値を保持する計算式、
`rightModuleCounitIso`は既存の戻り関手との比較、`rightModuleInverseIso`は既存の
`rightModuleBimoduleEquivalence`が選択した逆関手との自然同型である。
独立した対象宇宙とSmall仮定だけを使い、局所Hom K-flat性は要求しない。

**左右の制限。** `Bimodule/MiddleRestrictionUncurry.lean`は、
`leftRestriction_uncurryHom`と`rightRestriction_uncurryHom`を証明した。
直接構成した左右の制限の全Hom写像が、元のuncurryHomに積dg関手のHom写像を前合成したものと
一致する。次数ごとのtensorの純元で証明し、豊穣合成の順序を保持している。
既存の公開APIの名前・型・定義は変更していない。
これらは§17.218のsourceを既存の積dg圏表示へ接続するための補助APIであり、
この段階では左右の制限関手自体の自然同型や、その全導来化を完成したとは主張しない。

**検証。** 新規`Checks.DGBimoduleUncurryPresentation`は独立した対象宇宙、
局所K-flat仮定なしでの表示比較と射の値の保持、ZMod 2の場合を検査した。
全導来中間比較・解像度同値・導来bimodule五角形・StageEight・StageSeven・Spectra.StageTwoとの
統合ビルド成功（3421 jobs、警告なし）。主要15宣言の直接公理監査は重複・欠落なく標準3公理以内。
新規監査累計4309宣言。今回の4受入Leanファイルのsorry・admit・新規axiom・資源上限変更は0件。
採用済み引用0件。Lean toolchain v4.35.0-rc4とMathlib manifest/HEAD
`e6bbacd0e1b7307ff6e17da09cd2455f60804fa6`を再確認した。
全体文書検査は21 Markdown・320 exposition参照を検査し、担当外の
BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの
未解決参照1件で失敗した。

**分担と次工程。** §0・§15・§17.204のU15e分割を確認し、
U12e全受入→U16a〜d→U15e分解版の順を維持する。
U15e局所K-flat版と続くU17b局所K-flatの場合はU17a/U13d側の担当である。
分解版の着手時に`Quotient/DerivedComparison*.lean`と`Verdier/`を読み再利用し、重複実装しない。
U12eでは、左右の制限と積dg圏表示の制限の自然同型、その全導来化、準同値の場合の可逆性、
解像度変更と導来合成・対角単位・結合子の整合性とcoherenceを引き続き仕上げる。
U12e全体は未受入。共有モデル圏一般論への新しいAPI要求はない。
共有ルート・共有監査スクリプト・Perfect/・Endomorphism/・ScalarExtension*・
Quotient/DerivedComparison*・Verdier/は編集していない。


### 17.220 U12e60：左右制限の同定と全導来sourceの既存APIへの接続（2026-10-17）

**閉零制限の同定。** `Bimodule/MiddleRestrictionPresentation.lean`は前項のuncurryHom比較を使い、
直接構成した左右の制限と、積dg関手に沿う右加群制限との可換squareを自然同型として構成した。
`middleLeftPresentationObjIso`・`middleRightPresentationObjIso`は各値で恒等となる加群同型であり、
全次数のHom作用との自然性を満たす。
`middleLeftPresentationIso`・`middleRightPresentationIso`は任意の閉零bimodule射に自然である。
`Derived/MiddleRestrictionIdentification.lean`はこれを既存の選択された表示同値へ接続し、
`middleLeftRestrictionIso`・`middleRightRestrictionIso`によって直接の左右制限を既存の
`bimoduleRestriction`と同定した。
`middleLeftRestrictionDerivedIso`・`middleRightRestrictionDerivedIso`は、局所化後の制限と既存の
`derivedBimoduleRestriction`との自然な可換式である。
これらの比較はSmall仮定だけを使い、局所Hom K-flat性を要求しない。

**全導来sourceの同定。** `Derived/BimoduleMiddleSourceIdentification.lean`は、
既存の`derivedBimoduleRestriction`と`derivedBimoduleComposeFunctor`だけで表す関手族
`middleRestrictionDerivedSource`を定義した。
Qに右制限、Pに左制限を施してDを中間圏として導来合成する、両変数の全導来圏上のsourceである。
`middleClosedSourceIdentification`は閉零の両因子に自然な表示比較、
`middleDerivedSourceLiftIdentification`は前因子の全導来圏上の自然同型である。
その後因子の任意の閉零射についての自然性も証明した。
`Derived/BimoduleMiddleSourceFull.lean`は後因子の右K-flat局所化へ降ろし、
既存の右K-flat置換同値の余単位を使って`middleFullDerivedSourceIdentification`を構成した。
これで§17.218の`middleFullDerivedSource`は、既存の導来制限と導来合成の合成へ
両変数の全導来射に自然な自然同型で接続された。
`derivedMiddleRestrictionNatTrans`はその同型で移した実際の中間圏比較であり、
`derivedMiddleRestrictionNatTrans_transport`と`derivedMiddleRestrictionNatTrans_app`は移送の計算式である。
局所Hom K-flat性の仮定は終端Eだけで、C・Dや制限後の因子には追加していない。
今回の比較は自然変換であり、準同値Fの場合の可逆性をまだ主張しない。
既存の公開APIの名前・型・定義は変更していない。

**検証。** 新規`Checks.DGBimoduleMiddleSourceIdentification`は独立した四つの対象宇宙、
C・Dの局所Hom K-flat性および制限後のK-flat性なしでのsource同定、
既存の導来制限と導来合成をそのまま使った比較射の型、両因子の任意の導来射についての自然性、
ZMod 2の場合を検査した。
明示的uncurry表示・全導来中間比較・解像度独立性・ホモトピー・中間圏自然性・tensor制限・
解像度同値・導来随伴・単位・制限・導来bimodule五角形・StageEight・StageSeven・Spectra.StageTwoとの
統合ビルド成功（3447 jobs、警告なし）。主要26宣言の直接公理監査は重複・欠落なく標準3公理以内。
新規監査累計4335宣言。今回の5受入Leanファイルのsorry・admit・新規axiom・資源上限変更は0件。
採用済み引用0件。Lean v4.35.0-rc4とMathlib manifest/HEAD
`e6bbacd0e1b7307ff6e17da09cd2455f60804fa6`を再確認した。
全体文書検査は21 Markdown・320 exposition参照を検査し、担当外の
BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの
未解決参照1件で失敗した。

**残件と引継ぎ。** 全導来sourceと既存の導来制限・導来合成の同定は今回仕上げた。
次に準同値の場合の比較の可逆性を証明し、dg圏解像度変更に適用する。
導来合成・対角単位・結合子の整合性とcoherenceを仕上げてU12e全体の受入条件を確認する。
U12eは引き続き未受入であり、受入後のU16a〜d、U15e分解版の順を維持する。
U15e分解版では局所K-flat版のQuotient/DerivedComparison*・Verdier/を読んで再利用する。
共有モデル圏一般論への新しいAPI要求はない。共有ルート・共有監査スクリプト・Perfect/・
Endomorphism/・ScalarExtension*・Quotient/DerivedComparison*・Verdier/は編集していない。


### 17.221 U12e61：準同値に沿う中間圏比較の全導来自然同型（2026-10-17）

**K-flatモデルの延長と単位。** `Derived/FunctorExtensionKFlatUnit.lean`は既存の導来単位の
計算式と全対象上の可逆性を逆向きに使い、標準の射影解像度上の実際の延長単位が準同型であることを
証明した。`dgModuleExtension_relativeKFlat_quasiIso`はgraph延長が右相対K-flat加群間の
準同型を保存することを示す。単位の自然性と合わせ、
`functorExtensionUnit_relativeKFlat_quasiIso`はHom準同型に沿う単位の準同型性を
任意の右相対K-flat加群へ拡張した。対象ごとのA-K-flat性や元のdg圏のHomのflatnessは使わない。
`moduleRestriction_reflects_quasiIso`は主K上の本質的全射性から制限の準同型反映を導く。
`functorExtensionTranspose`は制限への指定射の実際の閉零随伴転置であり、
`functorExtensionTranspose_quasiIso`は準同値に沿う右K-flat増大の転置が準同型になることを示した。
転置先の右加群のK-flat性は、この段階の準同型性には要求しない。

**実際のtensor比較との同一視。** `Tensor/FunctorExtensionProjection.lean`は
既存の全Hom自然なYoneda評価とFubini同型を使い、任意の右D加群R・左C加群Nについて
(F_!R)⊗_C N ≅ R⊗_D F^*Nを実際の複体同型`functorExtensionTensorIso`として構成した。
`graphTensorYonedaIso`は左D加群の全Hom自然な同型であり、単なる対象ごとの評価ではない。
三重生成元の順R,graph,Nを保つ計算式を証明し、graph延長による右相対K-flat性の保存も導いた。
`Tensor/FunctorRestrictionQuasiIso.lean`は制限後の指定モデルからのchain map
`resolvedRestrictionComparison`を定義する。
`functorExtensionTensorIso_resolvedComparison`は射影公式を通すとこの実際の比較が
随伴転置とのtensorになることを証明した。balanced関係・associator自然性・既存の余単位の
生成元計算を使い、符号や合成順序を省略していない。
`resolvedRestrictionComparison_quasiIso`は、準同値と両端の右相対K-flat性から比較の準同型性を示す。
制限された元の右加群自体や、左加群NのK-flat性を追加していない。

**全導来bimodule比較の可逆性。** `Derived/BimoduleMiddleQuasiIso.lean`は左制限の表示変更同型を
明記し、既存の`middleRestrictionResolvedMap`の各値を前項のtensor比較へ同定する。
`middleRestrictionResolvedMap_quasiIso`は、任意の前因子と、元の後因子および制限後モデルの
指定右K-flat性の下で、任意の準同型増大を使う実際のbimodule比較が準同型になることを示した。
`Derived/BimoduleMiddleEquivalence.lean`はこの結果を指定局所化へ持ち上げ、
`derivedMiddleRestrictionComparison`、前因子の局所化後の比較、右K-flat後因子族、
後因子の局所化後の比較、両変数の全導来比較の各段階で可逆性を証明した。
`derivedMiddleRestrictionIso`は§17.220の既存導来制限・導来合成で表したsourceから
`derivedBimoduleComposeFunctor`への、両変数の任意の導来射に自然な自然同型である。
そのhomは既存の`derivedMiddleRestrictionNatTrans`そのものであり、別の比較射に置き換えていない。
全導来段階の局所Hom K-flat仮定は終端Eだけで、元の中間圏C・Dには課さない。
既存公開APIの名前・型・定義は変更していない。

**検証。** 新規`Checks.DGBimoduleMiddleEquivalence`は独立した四つの対象宇宙、
C・Dの局所Hom K-flat性なしでの自然同型、任意の指定右K-flat解像度による比較の可逆性、
両変数の任意の導来射に対する自然性、指定された任意のdg圏解像度の増大への適用、ZMod 2を検査した。
全導来source同定・uncurry表示・解像度独立性・ホモトピー・tensor制限・解像度同値・
導来随伴・単位・制限・導来bimodule五角形・StageEight・StageSeven・Spectra.StageTwoとの
統合ビルド成功（3453 jobs、警告なし）。主要31宣言の直接公理監査は重複・欠落なく標準3公理以内。
新規監査累計4366宣言。今回の6受入Leanファイルのsorry・admit・新規axiom・資源上限変更は0件。
採用済み引用0件。Lean v4.35.0-rc4とMathlib manifest/HEAD
`e6bbacd0e1b7307ff6e17da09cd2455f60804fa6`を再確認した。
全体文書検査は21 Markdown・320 exposition参照を検査し、担当外の
BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの
未解決参照1件で失敗した。

**残件。** 準同値に沿う実際の全導来中間圏比較の可逆性は今回仕上げた。
これを共通dg圏解像度による変更へ適用し、比較の自己・推移整合性、対角単位・結合子との整合性、
coherenceを仕上げてU12e全体の受入条件を確認する。
U12eは未受入であり、受入後のU16a〜d、U15e分解版の順を保持する。
U15e分解版では局所K-flat版のQuotient/DerivedComparison*・Verdier/を読んで再利用する。
共有一般論への新しいAPI要求はない。共有ルート・共有監査スクリプト・Perfect/・Endomorphism/・
ScalarExtension*・Quotient/DerivedComparison*・Verdier/は編集していない。


### 17.222 U12e62：指定モデルと標準解像度による中間比較の自己・推移則（2026-10-17）

**制限の恒等・合成比較。** `Bimodule/ValueIsomorphism.lean`は右加群同型族の左作用との
全Hom自然性を、値のHom複体で確認して`isoOfFamily`へ束ねる入口を追加した。
`Bimodule/MiddleLeftRestrictionCoherence.lean`と`Bimodule/MiddleRightRestrictionCoherence.lean`は、
直接の左右制限の恒等・合成比較を、任意の閉零bimodule射に自然な自然同型として構成した。
左制限は各左対象で恒等の右加群同型を使い、右制限は既存の加群制限の恒等・合成同型を再利用する。
いずれも値の成分は恒等で、全次数の左作用との自然性を別に証明している。
局所Hom K-flat性や準同値性は要求しない。

**指定増大とtensorの自己・推移則。** `Tensor/ResolvedRestrictionCoherence.lean`は
二段階のモデルの増大を合成関手への増大へまとめ、各値の計算式と準同型性の保存を証明した。
左作用の反復制限と合成制限の間の表示同型を明記したうえで、
`resolvedRestrictionComparison_comp`は二段階の実際のtensor比較が合成増大による比較と一致することを示す。
`Tensor/ResolvedRestrictionIdentity.lean`は恒等関手の場合の式を証明し、
表示を戻して正規化した増大とtensorする射そのものになることを示した。
これらのchain mapの等式にはモデルのK-flat性さえ要求しない。
`Bimodule/ResolvedRestrictionAugmentation.lean`は同じ増大の恒等・合成処理を全Hom自然な
bimodule射として構成し、値の計算と準同型保存を証明した。

**実際のbimodule比較の整合性。** `Derived/BimoduleMiddleResolvedCoherence.lean`は
左右制限の表示同型を指定後因子との合成のsource同型へ送る。
`ι_middleRestrictionResolvedMap_value`で既存の比較を各coend包含において計算し、
`middleRestrictionResolvedMap_functor_comp`は二段階の指定増大による既存の実際の比較射が
合成増大による一段階の比較と可換であることを閉零bimodule圏で証明した。
`middleRestrictionResolvedMap_functor_id`とそのexchange形は恒等関手の比較を正規化した増大と
左制限の恒等同型で計算する。新しい比較射を作って等式を定義で仮定したものではない。

**実際の導来比較の自己・推移則。** `Derived/BimoduleMiddleIdentity.lean`の
`derivedMiddleIdentitySourceIso`は既存の左右の恒等制限比較を実際の全導来合成へ送った同型である。
`derivedMiddleRestrictionComparison_functor_id`は任意の指定右K-flat解像度による既存の導来比較が
この同型のhomに一致することを示した。右因子の計算同型の前因子自然性と、
指定増大の正規化を通じて証明し、解像度を含まない右辺を得ている。
`Derived/BimoduleMiddleFunctorComposition.lean`は後因子の準同型増大をさらに制限した射と
左制限の合成同型から`derivedMiddleCompositeSourceIso`を構成した。
同じ最終モデルを用いた計算との可換式を証明したうえで、
`derivedMiddleRestrictionComparison_functor_comp`は二つの実際の導来比較と合成関手の比較の
可換式を証明した。指定増大の導来合成計算式と前項の厳密な比較射の合成則を再利用する。
元の中間圏D・E・Tの局所Hom K-flat性も、二つの関手F・Gの準同値性も要求しない。
使う局所Hom K-flat性は終端Lだけで、Q・R・Sには指定右相対K-flatモデルを使う。

**標準解像度への接続。** `Bimodule/SemifreeRetarget.lean`はsourceとfiltrationを保持して
semifree解像度の増大を準同型で後合成する。
`Derived/BimoduleMiddleCanonicalComposition.lean`はこの操作で二段階目の標準解像度を
合成関手への増大を持つ解像度に読み替え、既存の任意semifree解像度による比較の独立性を適用した。
`derivedMiddleRestrictionCanonicalComparison_functor_comp`は二段階の標準解像度と、
合成関手へ直接適用する標準比較の合成則である。
解像度間の追加の比較射や可換squareを利用者に要求しない。
標準解像度の恒等則も`derivedMiddleRestrictionCanonicalComparison_functor_id`として公開した。
既存公開APIの名前・型・定義は変更していない。

**検証。** 新規`Checks.DGBimoduleMiddleFunctorCoherence`は独立した五つの対象宇宙、
D・E・Tの局所Hom K-flat性およびF・Gの準同値性なしでの指定モデルの実際の導来合成則、
前因子のK-flat性なしの恒等則、追加squareなしの標準解像度の合成則、ZMod 2での恒等則を検査した。
準同値での可逆性・全導来source同定・解像度独立性・ホモトピー・tensor制限・解像度同値・
導来随伴・単位・制限・導来bimodule五角形・StageEight・StageSeven・Spectra.StageTwoとの
統合ビルド成功（3465 jobs、警告なし）。主要60宣言の直接公理監査は重複・欠落なく標準3公理以内。
新規監査累計4426宣言。今回の12受入Leanファイルのsorry・admit・新規axiom・資源上限変更は0件。
採用済み引用0件。Lean v4.35.0-rc4とMathlib manifest/HEAD
`e6bbacd0e1b7307ff6e17da09cd2455f60804fa6`を再確認した。
全体文書検査は21 Markdown・320 exposition参照を検査し、担当外の
BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの
未解決参照1件で失敗した。

**残件と次工程。** 今回の自己・推移則は、前因子の閉零対象と指定右K-flat後因子上の
実際の導来比較および標準semifree計算について証明したものである。
これらの等式とsource同型を両変数の全導来圏上の関手族へ束ねて降ろし、
§17.220の既存の導来制限表示と整合させる作業を残す。
さらに共通dg圏解像度による変更に適用し、対角単位・結合子との整合性とcoherenceを仕上げる。
U12e全体は未受入であり、受入後のU16a〜d、U15e分解版の順を維持する。
U15e分解版では局所K-flat版のQuotient/DerivedComparison*・Verdier/を読んで再利用する。
共有一般論への新しいAPI要求はない。共有ルート・共有監査スクリプト・Perfect/・Endomorphism/・
ScalarExtension*・Quotient/DerivedComparison*・Verdier/と、並行作業のTensor/Associator*は編集していない。


### 17.223 U12e63：恒等中間比較の全導来化と指定モデルでの計算（2026-10-17）

**分担の再確認。** ユーザー指定に従い、このチャットはU12e受入→U16a〜d→U15e分解版を担当する。
U15e局所K-flat版と続くU17b局所K-flatの場合はU17a/U13dを終えたチャットが担当し、
Quotient/DerivedComparison*.lean・Verdier/に置かれる成果を分解版で読んで再利用する。
局所K-flat版の比較・Verdier一般論を重複実装しない。§17の管理と公開API変更記録はこのチャットが保持する。

**恒等則の全導来化。** Derived/BimoduleMiddleIdentityFamily.leanは左右の恒等制限の
自然同型からmiddleClosedIdentityIsoを構成し、既存の指定モデル上の恒等則と一致させた。
前因子の局所化を通じてmiddleIdentitySourceLiftIsoへ降ろし、
Derived/BimoduleMiddleIdentityFull.leanで後因子の右K-flat局所化と置換を通して
両変数の全導来圏上へ移した。derivedMiddleIdentityIsoは既存導来制限・導来合成で表したsourceの
正規化同型であり、比較射をasIsoで包んで定義したものではない。
derivedMiddleRestrictionNatTrans_functor_idは既存の実際の全導来比較がそのhomに一致することを証明する。
任意の可換環・独立した対象宇宙を保持し、局所Hom K-flat性は合成の終端Lだけに要求する。
中間Dの局所Hom K-flat性や、前因子のK-flat性は要求しない。

**指定モデルでの計算。** Derived/BimoduleMiddleComparisonComputation.leanは
全導来比較を置換余単位による共役として計算し、右K-flat局所化へ前合成すると
元の局所化比較を回復することを証明した。完全忠実性と余単位を用い、
指定置換の元の単位が随伴化後の単位と同じという仮定は使わない。
derivedMiddleRestrictionNatTrans_app_rightKFlatと_app_baseは、既存の実際の全導来比較を
任意の指定右K-flat後因子および閉零前因子上で計算する入口である。
Derived/BimoduleLiftIso.leanは指定局所化への前合成で与えた自然同型を導来関手間へ降ろし、
hom・invの元の対象上の計算式を公開した。次の合成則の全導来化に用いる。
既存公開APIの名前・型は変更せず、新規APIだけを追加した。

**検証。** Checks.DGBimoduleMiddleIdentityFullは両変数とも任意の導来対象での恒等則、
独立した対象宇宙、ZMod 2での恒等則を検査する。統合ビルドは3470 jobsで成功し、警告なし。
主要26公開宣言の直接公理監査は重複・欠落なく標準3公理以内。新規監査累計4452宣言。
今回の5 Leanファイルにsorry・admit・新規axiom・資源上限変更は0件。採用済み引用0件。
Lean v4.35.0-rc4とMathlib manifest/HEAD e6bbacd0e1b7307ff6e17da09cd2455f60804fa6を再確認した。
文書検査は21 Markdown・320 exposition参照を検査し、担当外の
BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの
既存未解決参照1件で失敗した。

**残件と引継ぎ。** 合成則の両変数の全導来関手族への降下、共通dg圏解像度による変更、
対角単位・結合子との整合性とcoherenceを残す。U12e全体は未受入、U16・U15e分解版は未着手。
共有モデル圏一般論への新しいAPI要求はない。
共有ルート・Perfect/・Endomorphism/・ScalarExtension*・Quotient/DerivedComparison*・Verdier/・
並行作業のTensor/Associator*と他チャットの記録は編集していない。


### 17.224 U12e64：導来制限の合成同型と二段階比較の全導来source（2026-10-17）

**左右の導来制限の合成。** Derived/MiddleRestrictionComposition.leanは
直接制限の既存合成同型と、直接制限・積dg圏表示による制限の既存表示同型を組み合わせる。
middleLeftDerivedCompPreIso・middleRightDerivedCompPreIsoを元の閉零対象に前合成した上で作り、
指定局所化を通じてmiddleLeftDerivedCompIso・middleRightDerivedCompIsoへ降ろした。
これらは既存のderivedBimoduleRestriction同士の自然同型である。
新しい制限関手を代替定義せず、比較射を仮定して定義してもいない。
元の対象上のhomの計算式、局所化への前合成の等式、直接制限との表示同型に関する
合成squareの可換性を公開した。局所Hom K-flat性・準同値性は要求しない。
任意の可換環と独立した四つのdg圏の対象宇宙を保持する。

**二段階中間比較の関手族。** Derived/BimoduleMiddleCompositeFamily.leanは
middleIteratedDerivedSourceを既存の導来制限・導来合成の合成として構成し、
左右の導来制限の合成同型だけからmiddleIteratedDerivedSourceIsoを作った。
その終域は合成dg関手F.comp Gに対する既存middleRestrictionDerivedSourceである。
middleIteratedDerivedComparisonは既存の全導来比較を実際に二段階で適用する自然変換であり、
両変数とも任意の導来対象を扱う。source正規化・二段階比較の成分計算式も公開した。
ここで必要な局所Hom K-flat性は終端Lだけで、中間D・E・Tの仮定もF・Gの準同値性も不要。

middleDerivedFamily_extは、この種の全導来関手族の自然変換の等式を、任意の指定右K-flat後因子と
任意の閉零前因子上で検査できることを証明する。後因子の標準semifree解像度の導来同型と自然性を用い、
前因子は既存の局所化の射の等式判定を再利用する。
既存公開APIの名前・型は変更せず、16公開宣言を追加した。

**検証。** 新規Checks.DGBimoduleMiddleCompositeFamilyは独立した五つの対象宇宙、
中間圏の局所Hom K-flat性・準同値性なしのsource正規化、任意の導来前因子の射に関する自然性、
右K-flat対象上での等式判定、ZMod 2での右制限合成を検査した。
既存恒等則・指定モデル合成則・導来同値・source同定・解像度独立性・導来随伴・五角形・
StageEight・StageSeven・Spectra.StageTwoを含む統合ビルド成功（3473 jobs、警告なし）。
16公開宣言の直接公理監査は重複・欠落なく標準3公理以内。新規監査累計4468宣言。
今回の3 Leanファイルにsorry・admit・新規axiom・資源上限変更は0件。採用済み引用0件。
Lean v4.35.0-rc4とMathlib manifest/HEAD e6bbacd0e1b7307ff6e17da09cd2455f60804fa6を再確認した。

文書検査は21 Markdown・320 exposition参照を検査し、担当外の
BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの
既存未解決参照1件で失敗した。

**残件と次工程。** sourceの正規化と二段階比較を構成した段階であり、
middleIteratedDerivedSourceIso.homと合成関手の比較の合成がmiddleIteratedDerivedComparisonに
一致するという全導来合成則はまだ証明していない。
次にmiddleDerivedFamily_extで後因子を指定右K-flatモデルへ帰着し、
§17.223のapp_baseおよび今回の左右表示squareを使って、§17.222の標準解像度上の合成則へ接続する。
その後、共通dg圏解像度の変更と対角単位・結合子の整合性・coherenceを仕上げて§15.2を監査する。
U12e全体は未受入、U16a〜d・U15e分解版は未着手であり、全体の目標を縮小しない。
共有一般論への新しいAPI要求はない。
局所K-flat版のQuotient/DerivedComparison*・Verdier/は分解版で読んで再利用する。
共有ルート・共有監査スクリプト・Perfect/・Endomorphism/・ScalarExtension*・並行作業の
Tensor/Associator*および他チャットの記録を編集していない。


### 17.225 U12e65：二段階source表示の正規化squareと移送付き比較計算（2026-10-17）

**二段階表示。** Derived/MiddleRestrictionIteratedPresentation.leanは二段階の直接左右制限の
局所化を、既存の二段階導来制限へ送る自然同型を構成した。
middleLeftIteratedDerivedIso_normalize・middleRightIteratedDerivedIso_normalizeは、
この表示同型に導来制限の合成同型を続ける経路と、直接制限の合成同型に一段階の表示同型を
続ける経路の一致を自然変換の等式として証明する。§17.224の表示squareを再利用する。
任意の可換環と独立した四つのdg圏の対象宇宙を保ち、K-flat性・準同値性は要求しない。

**実際の全導来sourceとの整合性。** Derived/BimoduleMiddleCompositePresentation.leanは
middleIteratedClosedSourceIsoで閉零両因子上の二段階sourceを既存の全導来sourceへ送り、
middleIteratedClosedNormalizationIsoで同じ閉零表示を合成dg関手のsourceへ正規化する。
middleIteratedClosedSourceIso_normalizeは、この二つの経路と既存の全導来source正規化・
一段階の表示同型からなるsquareの可換性を証明した。
左右の表示squareを導来合成関手の両変数の自然性で貼り合わせる証明であり、
source同型を比較射から逆算して定義したものではない。
必要な局所Hom K-flat性は終端Lだけで、D・E・Tの仮定やF・Gの準同値性は不要。

**比較射の移送付き計算。** Derived/BimoduleMiddleTransportComputation.leanの
base_facは既存source表示同型を全導来比較へ前合成すると標準K-flatモデル計算を回復することを示す。
transport_facは、任意の導来射g・fで両因子を移送してから比較する経路を、
元の指定右K-flatモデルで比較してから同じ導来射で移送する経路と一致させる。
g・fの可逆性や、移送先が閉零対象から指定されることは要求しない。
これにより二段階目のsourceに現れる導来制限の値を、標準semifreeモデルとその増大を通して
計算する入口を得た。既存APIの名前・型は変更せず、9公開宣言を追加した。

**検証。** 新規Checks.DGBimoduleMiddleCompositePresentationは、独立した五つの対象宇宙、
中間圏の局所Hom K-flat性・関手の準同値性なしの実際のsource square、
可逆性を課さない任意の導来射での移送式、ZMod 2での右制限表示の正規化を検査した。
既存全導来恒等則・指定モデル合成則・導来同値・解像度独立性・導来随伴・五角形・
StageEight・StageSeven・Spectra.StageTwoを含む統合ビルド成功（3477 jobs、警告なし）。
9公開宣言の直接公理監査は重複・欠落なく標準3公理以内。新規監査累計4477宣言。
今回の4 Leanファイルにsorry・admit・新規axiom・資源上限変更は0件。採用済み引用0件。
Lean v4.35.0-rc4とMathlib manifest/HEAD e6bbacd0e1b7307ff6e17da09cd2455f60804fa6を再確認した。

文書検査は21 Markdown・320 exposition参照を検査し、担当外の
BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの
既存未解決参照1件で失敗した。

**残件と次工程。** 全導来比較の合成則そのものは未証明である。
次に後因子のG制限の標準semifree増大を指定し、今回のsource squareとtransport_facを使って
二段階の実際の全導来比較を§17.222の標準モデル上の合成式へ接続する。
その等式を§17.224のmiddleDerivedFamily_extで全導来圏へ降ろす。
その後、共通dg圏解像度の変更と対角単位・結合子との整合性・coherenceを仕上げ、§15.2を監査する。
U12e全体は未受入、U16a〜d・U15e分解版は未着手。全体の目標と順序を保持する。
共有一般論への新しいAPI要求はない。U15e分解版では局所K-flat版の
Quotient/DerivedComparison*・Verdier/を読んで再利用し、重複実装しない。
共有ルート・共有監査スクリプト・Perfect/・Endomorphism/・ScalarExtension*・並行作業の
Tensor/Associator*と他チャットの記録を編集していない。


### 17.226 U12e66：中間圏比較の全導来合成則と共通解像度sourceへの適用（2026-10-17）

**指定増大から全導来sourceへ。** Derived/BimoduleMiddleAugmentedSource.leanは、
Gに沿う制限への指定増大qをさらにFで制限して、二段階の全導来sourceへ送る
middleIteratedAugmentedSourceMapを構成した。元の増大には準同型性を課さない。
qが準同型のとき、全導来sourceの正規化との合成が、§17.222の既存の
実際のモデル上のderivedMiddleCompositeSourceIsoと一段階の表示同型の合成に一致する。
Derived/BimoduleMiddleAugmentedTransport.leanは同じsource射を、前段比較のsourceを
両因子の導来射で移送した射と一致させた。右制限表示の全Hom自然性と導来合成の自然性を使い、
新しいsource同型を比較射から逆算していない。

**二段階比較のモデル計算。** Derived/BimoduleMiddleIteratedComputation.leanの
middleIteratedAugmentedComparison_facは、指定source射を二段階の実際の全導来比較へ前合成すると、
Fの標準モデル比較、増大qによる既存導来合成関手の射、Gの標準モデル比較の順の合成になることを示す。
後因子Qと制限後の指定モデルRには右相対K-flat性を要求するが、qの準同型性は不要。
前因子PのK-flat性も要求しない。

**全導来合成則。** Derived/BimoduleMiddleFullComposition.leanの
**derivedMiddleRestrictionNatTrans_functor_comp**は、独立に構成した
middleIteratedDerivedSourceIso.homと合成dg関手F.comp Gの既存比較の合成が、
既存比較を二段階で適用したmiddleIteratedDerivedComparisonに一致することを証明した。
G制限の標準semifree増大を使う場合、さらにFで制限した増大も対象ごと準同型であり、
指定source射は可逆になる。それを前合成して上記のモデル計算・source正規化squareを適用し、
§17.222の標準解像度上の合成則へ帰着した。
最後に§17.224のmiddleDerivedFamily_extを用い、両変数の全導来圏上の自然変換の等式に降ろした。
_appは両変数とも任意の導来対象に適用できる成分式である。
この合成則にF・Gの準同値性や中間D・E・Tの局所Hom K-flat性は要求しない。
局所Hom K-flat性は合成の終端Lだけで、任意の可換環と独立した五つの対象宇宙を保持する。

準同値F・Gの場合はmiddleIteratedDerivedIsoを既存の比較自然同型の二段階合成として構成し、
derivedMiddleRestrictionIso_functor_compで自然同型そのものの推移整合性を証明した。
比較射の可逆性だけから合成則を仮定したものではない。

**dg圏解像度の比較脚。** Resolution/MiddleCompositionComparison.leanは共通比較sourceの
両脚comparisonLeft・comparisonRightに、この既存導来制限・導来合成の自然同型を適用する。
middleComparisonLeftIsoは元のdg圏の対象型のsmallnessを要求しない。
middleComparisonRightIsoは既存の標準解像度を作るために元の対象型のsmallnessを明示する。
どちらも元のHomのK-flat性は不要であり、outer終端Lだけの局所Hom K-flat性を使う。
_refineは共通sourceを任意の準同値Hでさらに細分したときの、一段階と二段階の比較の一致である。
Hのsourceの局所Hom K-flat性を追加しない。既存公開APIの名前・型は変更せず、12公開宣言を追加した。

**検証。** Checks.DGBimoduleMiddleFullCompositionは、両変数とも任意の導来対象での
実際の合成則、準同値での自然同型の合成則、元の対象型のsmallnessなしの比較左脚、
右脚のsmallnessの明示、独立した対象宇宙とZMod 2での全導来合成則を検査した。
既存全導来恒等則・モデル合成則・source表示・導来同値・解像度独立性・導来随伴・五角形・
StageEight・StageSeven・Spectra.StageTwoを含む統合ビルド成功（3483 jobs、警告なし）。
12公開宣言の直接公理監査は重複・欠落なく標準3公理以内。新規監査累計4489宣言。
今回の6 Leanファイルにsorry・admit・新規axiom・資源上限変更は0件。採用済み引用0件。
Lean v4.35.0-rc4とMathlib manifest/HEAD e6bbacd0e1b7307ff6e17da09cd2455f60804fa6を再確認した。

文書検査は21 Markdown・320 exposition参照を検査し、担当外の
BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの
既存未解決参照1件で失敗した。

**残件と次工程。** 中間圏制限に沿う比較の自己・推移則は両変数の全導来圏上まで証明した。
今回の比較脚への適用だけで、両端の解像度を同時に変更する既存changeEquivalenceが
導来合成・対角単位・結合子を保存することまで証明したとはしない。
次に外側の左右制限と合成の比較、対角単位・結合子との整合性を接続し、
共通dg圏解像度による変更のcoherenceを仕上げて§15.2全体を監査する。
U12e全体は未受入、U16a〜d・U15e分解版は未着手。全体の目標と順序を保持する。
共有一般論への新しいAPI要求はない。U15e分解版では局所K-flat版の
Quotient/DerivedComparison*・Verdier/を読んで再利用し、重複実装しない。
共有ルート・共有監査スクリプト・Perfect/・Endomorphism/・ScalarExtension*・並行作業の
Tensor/Associator*と他チャットの記録を編集していない。


### 17.227 U12e67：外側左制限と両変数の全導来合成の自然同型（2026-10-17）

**underivedの全Hom作用。** Tensor/ComposeLeftRestriction.leanのcompose_leftRestrictionは
Pと、後因子Qの外側左作用をF : D → Eで制限したものの相対tensor合成が、
PとQを合成してから同じ外側左作用を制限したものに一致することをdg関手の等式で証明する。
右加群対象はそのままで、左作用の全Homへの射を既存compose_leftMap_πと豊穣合成の結合性で比較した。
composeLeftRestrictionIsoは実際の閉零bimodule圏上の同型であり、値の成分は恒等である。
両因子の任意の全Hom自然な閉零射に関する自然性を証明した。
E・Dのsmallnessや、いずれのHomのK-flat性、Fの準同値性もこのunderived結果には要求しない。

**右K-flatモデルの制限。** Derived/KFlatBimoduleLeftRestriction.leanは、外側左制限が
右相対K-flat性と対象ごとの準同型を保存することを証明し、rightKFlatLeftRestrictionを構成した。
Qの各右加群をF.obj dで再選択するため、追加のlocal Hom条件は不要である。
rightKFlatInclusionとの因子化と右K-flat部分圏の準同型保存も公開した。
この操作は中間圏の右作用を制限する場合とは区別する。

**固定後因子の導来比較と自然性。** Derived/BimoduleLeftRestrictionBase.leanは
underivedの比較を既存middleLeftRestrictionDerivedIsoで出力側の既存導来制限へ接続し、
前因子の指定局所化を通じてderivedComposeWithLeftRestrictionIsoへ降ろした。
後因子は任意の指定右K-flatモデルで、前因子は任意の導来対象を扱う。
この固定モデル版にはE・D・Cのlocal Hom K-flat性もFの準同値性も要求しない。
既存の導来制限を構成するための対象型のsmallnessは明示する。
Derived/BimoduleLeftRestrictionFamily.leanは元の前因子上の成分計算式を公開し、
両側の固定因子計算同型による表示から、後因子の任意の閉零射への自然性を証明した。
leftRestrictionKFlatComposeIsoとして、実際の固定因子の導来合成関手族間の自然同型へ束ねた。

**両変数の全導来圏への移送。** Derived/RightKFlatIsoLift.leanは
rightKFlatDerivedIsoOfPrecompを追加した。右K-flatモデルへの前合成上で与えた自然同型を、
右K-flat部分圏の指定局所化と既存の置換余単位を使って、指定された二つの全導来関手間へ移す。
対象はdg bimoduleの既存局所化に限定し、新しいモデル圏一般論を作らない。
rightKFlatComposePresentationIsoは既存の全導来合成を固定因子関手族へ自然に比較する入口である。

Derived/BimoduleLeftRestrictionFull.leanの**derivedBimoduleComposeLeftRestrictionIso**は、
合成後に出力の外側左作用を制限する関手族と、後因子の外側左作用を制限してから合成する関手族を
自然同型で比較する。両者とも既存のderivedBimoduleRestriction・derivedBimoduleComposeFunctorだけで
定義し、両変数とも任意の導来対象を扱う。
全導来合成を両側で構成するためE・Dの局所Hom K-flat性を明示するが、Cの条件やFの準同値性は不要。
右K-flatモデル上の両側の表示同型から移送しており、比較を仮定するpredicateを作っていない。
任意の可換環と独立した四つの対象宇宙を保持する。
既存公開APIの名前・型は変更せず、27公開宣言を追加した。

**検証。** Checks.DGBimoduleLeftRestrictionは、固定モデル版にlocal Hom条件が不要なこと、
両変数とも任意の導来対象での比較、Cの局所Hom K-flat性・Fの準同値性なしの型、
後因子の任意の射への自然性、独立した対象宇宙とZMod 2での全導来自然同型を検査した。
既存中間比較の全導来合成則・恒等則・解像度比較・導来同値・導来随伴・五角形・
StageEight・StageSeven・Spectra.StageTwoを含む統合ビルド成功（3490 jobs、警告なし）。
27公開宣言の直接公理監査は重複・欠落なく標準3公理以内。新規監査累計4516宣言。
今回の7 Leanファイルにsorry・admit・新規axiom・資源上限変更は0件。採用済み引用0件。
Lean v4.35.0-rc4とMathlib manifest/HEAD e6bbacd0e1b7307ff6e17da09cd2455f60804fa6を再確認した。

文書検査は21 Markdown・320 exposition参照を検査し、担当外の
BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの
既存未解決参照1件で失敗した。

**残件と次工程。** 外側左制限の全導来自然同型を構成した段階であり、
移送後の全導来比較の指定モデル上の計算式、恒等・合成と他の制限比較との整合性は残す。
外側右制限、対角単位・結合子の保存、両端の解像度を同時に変えるchangeEquivalenceとの整合性も必要である。
これらを接続して共通dg圏解像度による変更のcoherenceを仕上げ、§15.2全体を監査する。
U12e全体は未受入、U16a〜d・U15e分解版は未着手。全体の目標と順序を保持する。
共有一般論への新しいAPI要求はない。U15e分解版では局所K-flat版の
Quotient/DerivedComparison*・Verdier/を読んで再利用し、重複実装しない。
共有ルート・共有監査スクリプト・Perfect/・Endomorphism/・ScalarExtension*・並行作業の
Tensor/Associator*と他チャットの記録を編集していない。


### 17.228 U12e68：K-flatモデルからの移送の計算・合成保存と外側左比較の一意性（2026-10-17）

**既存APIと内部整理。** Derived/RightKFlatIsoLift.leanでは、既存の
rightKFlatDerivedIsoOfPrecompの名前・引数・型・宇宙・仮定を保ったまま、
内部の右K-flat部分圏の局所化上の構成をrightKFlatLocalizedIsoOfPrecompへ切り出した。
局所化上だけの構成には終端Eのlocal Hom K-flat性を要求しない。
全導来圏への移送で使う置換余単位と構成の順序は保持し、利用側の移行は不要である。

**移送前の成分の回復。** Derived/RightKFlatIsoLiftComputation.leanは、全導来移送のhomを
指定置換余単位による局所化上の比較の共役として計算する。
包含の完全忠実性と比較の自然性を使い、右K-flat局所化への前合成で元の比較を回復することを示した。
元の置換単位がMathlibの随伴化後の単位と同じという三角恒等式は仮定しない。
rightKFlatDerivedIsoOfPrecomp_hom_appは任意の指定右K-flat閉零モデル上の元の成分との等式、
_precompは自然同型そのものを回復する等式である。
rightKFlatDerivedNatTrans_extは全導来関手の自然変換を同じモデル上で判定する入口を与える。
値域は任意の圏であり、その対象宇宙・Hom宇宙は環やdg圏の宇宙から独立に保持する。

**移送の自己・推移整合性。** 同ファイルの_refl・_trans・_whiskerRightは、
移送が恒等自然同型・自然同型の合成・任意の関手への後合成を保つことを証明した。
移送後の成分計算と等式判定を使うため、追加の置換の単位・余単位の整合性を利用側に要求しない。
これらはモデル上の比較の恒等・合成式を全導来比較へ移す際に使う。

**外側左制限比較のモデル計算。** Derived/BimoduleLeftRestrictionComputation.leanの
_precomp・_app_rightKFlatは、§17.227のderivedBimoduleComposeLeftRestrictionIsoを
指定右K-flatモデルへ制限すると、既存のsource表示、固定K-flatモデル比較の逆、target表示の逆の
合成を回復することを証明した。
_model_squareは両側の表示同型を固定した可換squareであり、元の固定モデル比較を厳密に回復する。
_model_square_appは前因子が任意の導来対象の場合の式である。
derivedBimoduleComposeLeftRestriction_hom_uniqueは、同じモデルsquareを満たす任意の自然変換が
既存の全導来比較のhomに一致することを示す。比較候補の可逆性を先に仮定する必要はない。
Cの局所Hom K-flat性やFの準同値性は追加していない。

**検証。** Checks.DGRightKFlatIsoLiftComputationは、独立した値域の対象・Hom宇宙での成分回復、
自然同型の合成保存、前因子が任意の導来対象での外側左比較のモデルsquare、
ZMod 2での恒等保存を検査した。
既存外側左比較・中間比較の全導来合成則・恒等則・解像度比較・導来同値・導来随伴・五角形・
StageEight・StageSeven・Spectra.StageTwoを含む統合ビルド成功（3493 jobs、警告なし）。
既存2宣言と新規14宣言の計16公開宣言の直接公理監査は重複・欠落なく標準3公理以内。
新規監査累計4530宣言。今回の4 Leanファイルにsorry・admit・新規axiom・資源上限変更は0件。
採用済み引用0件。Lean v4.35.0-rc4とMathlib manifest/HEAD
e6bbacd0e1b7307ff6e17da09cd2455f60804fa6を再確認した。

文書検査は21 Markdown・320 exposition参照を検査し、担当外の
BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの
既存未解決参照1件で失敗した。

**残件と次工程。** 外側左比較の移送後の指定モデル計算は今回証明した。
この計算・一意性を使った外側左制限の恒等・合成や他の比較との整合性は引き続き必要である。
外側右制限の全導来比較、対角単位・結合子の保存、両端の解像度を同時に変える
changeEquivalenceとの整合性を接続して、共通dg圏解像度変更のcoherenceを仕上げる。
U12e全体は未受入、U16a〜d・U15e分解版は未着手。目標全体と順序を保持する。
共有一般論への新しいAPI要求はない。U15e分解版では局所K-flat版の
Quotient/DerivedComparison*・Verdier/を読んで再利用し、重複実装しない。
共有ルート・共有監査スクリプト・Perfect/・Endomorphism/・ScalarExtension*・並行作業の
Tensor/Associator*と他チャットの記録を編集していない。


### 17.229 U12e69：外側右制限と両変数の全導来合成の比較（2026-10-17）

**右作用制限後の左加群。** Bimodule/RightRestrictionLeftEvaluation.leanの
rightRestriction_leftAt_eqは、F : D → Bに沿って右作用を制限した前因子Pをdで左C加群として評価すると、
元のPをF.obj dで評価した左C加群に一致することを証明した。
全Homへの射を既存rightRestriction_leftAt_mapで照合しており、左作用の閉零部分だけで比較していない。
この対象の等式にはCのsmallnessを要求しない。
左加群圏上の実際の同型と、その各値でのhom・invが恒等となる計算式も公開した。

**tensorの値と全次数作用。** Tensor/ComposeRightRestrictionValue.leanは、
既存のbalanced tensorの左加群変数の関手に上の同型を送って値の同型を構成した。
coend包含と純粋斉次元での計算式を証明し、対象の等式によるtransportを暗黙に消したことにしていない。
Tensor/ComposeRightRestrictionActions.leanは、既存の右作用の生成元公式を通して、
制限前後のKoszul符号が同じHom次数と先頭Q因子の次数の積になることを照合した。
残る左作用との可換性も証明し、両側の作用の全Hom複体上の自然性へ持ち上げた。
Tensor/ComposeRightRestriction.leanでこれらを右加群同型、続いて実際の閉零bimodule同型
composeRightRestrictionIsoへ束ねた。
Tensor/ComposeRightRestrictionNaturality.leanは、両因子の任意の全Hom自然な閉零射について
この同型の自然性を、coend包含と既存tensor射の公式から証明した。
このunderived比較にいずれのHomのK-flat性もFの準同値性も要求しない。

**固定後因子の導来比較。** Derived/BimoduleRightRestrictionBase.leanは
underived比較を既存の入出力双方のmiddleRightRestrictionDerivedIsoへ接続した。
derivedComposeWithRightRestrictionIsoは、既存の入力側導来制限に続けてD–C–Eで合成する経路と、
B–C–Eで合成してから既存の出力側導来制限を適用する経路を自然同型で比較する。
後因子は任意の指定右相対K-flatモデルで、前因子は任意の導来対象を扱う。
この固定モデル版にはB・D・C・Eの局所Hom K-flat性もFの準同値性も不要。
必要な対象型のsmallnessは既存の導来制限・合成に合わせて明示する。
Derived/BimoduleRightRestrictionFamily.leanは元の前因子上の成分計算式を公開し、
入力表示同型の逆と、既存の固定因子自然変換の全導来前因子に関する自然性を使って、
後因子の任意の閉零射への自然性も証明した。
rightRestrictionKFlatComposeIsoとして右K-flat後因子の関手族上の自然同型へ束ねた。

**両変数の全導来比較と計算。** Derived/BimoduleRightRestrictionFull.leanの
**derivedBimoduleComposeRightRestrictionIso**は、両変数とも任意の導来対象について
外側右制限と導来合成の自然同型を構成した。
両側の関手族は既存のderivedBimoduleRestrictionとderivedBimoduleComposeFunctorだけで表す。
後因子自体は右作用制限で変わらないため、終端Eの局所Hom K-flat性だけで全導来化できる。
B・D・Cの同条件やFの準同値性は追加しない。
前回のrightKFlatDerivedIsoOfPrecompを再利用し、新しい置換や局所化を作っていない。
_app_rightKFlat・_model_squareは任意の指定K-flatモデル上の固定因子比較の回復を証明する。
derivedBimoduleComposeRightRestriction_hom_uniqueは同じモデルsquareを満たす自然変換の一意性であり、
比較候補の可逆性を先に要求しない。
任意の可換環と独立した四つの対象宇宙を保持する。
既存公開APIの名前・型は変更せず、35公開宣言を追加した。

**検証。** Checks.DGBimoduleRightRestrictionは、左加群の等式のC-smallnessなしの型、
全Hom複体での右作用自然性、固定モデル版のlocal Hom条件なしの型、
両変数の任意の導来対象・終端Eだけの局所Hom K-flat性による比較、モデルsquare、
独立した対象宇宙とZMod 2での全導来自然同型を検査した。
既存外側左比較・K-flat移送計算・中間比較の全導来合成則・恒等則・解像度比較・導来同値・
導来随伴・五角形・StageEight・StageSeven・Spectra.StageTwoとの統合ビルド成功（3502 jobs、警告なし）。
35公開宣言の直接公理監査は重複・欠落なく標準3公理以内。新規監査累計4565宣言。
今回の9 Leanファイルにsorry・admit・新規axiom・資源上限変更は0件。採用済み引用0件。
Lean v4.35.0-rc4とMathlib manifest/HEAD e6bbacd0e1b7307ff6e17da09cd2455f60804fa6を再確認した。

全体文書検査は共有ルートの環境export時に、担当外の
SerrePositivity.CLMST.SelectedParameterEuler.oleanが未生成のため停止した。
今回はexposition参照の全体検査結果を確定していない。
同じリンク検査ロジックを独立に実行し、21 Markdownの相対リンクは失敗0件を確認した。

**残件と次工程。** 外側左右・中間圏の比較は、それぞれ全導来圏上まで構成した。
外側の恒等・合成則、左右・中間制限の比較を組み合わせた整合性は引き続き必要である。
対角単位・結合子の保存と、両端を同時に変更するchangeEquivalenceの合成保存を接続し、
共通dg圏解像度変更のcoherenceを仕上げて§15.2全体を監査する。
U12e全体は未受入、U16a〜d・U15e分解版は未着手。目標全体と順序を保持する。
共有一般論への新しいAPI要求はない。U15e分解版では局所K-flat版の
Quotient/DerivedComparison*・Verdier/を読んで再利用し、重複実装しない。
共有ルート・共有監査スクリプト・Perfect/・Endomorphism/・ScalarExtension*・並行作業の
Tensor/Associator*と他チャットの記録を編集していない。


### 17.230 U12e70：三圏同時制限と既存changeEquivalenceの導来合成保存（2026-10-17）

**左右の直接制限。** Bimodule/PairedRestriction.leanは左作用、次に右作用を制限する
pairedRestrictionFunctorを構成し、uncurry HomがF.op.mapとG.mapのtensorに一致することを証明した。
既存の左右制限のuncurry式とtensor合成則を再利用する。
左右制限の交換をdg関手の等式で証明し、右加群ごとに恒等の同型と閉零射への自然性も公開した。
この直接制限の結果にHomのK-flat性・準同値性は不要で、左作用側の対象型のsmallnessも課さない。
Bimodule/PairedRestrictionPresentation.leanは積dg圏上の既存の右加群表示へ接続し、
値で恒等の全Hom自然なmodule同型と閉零射に自然な表示squareを証明した。

**既存の同時導来制限との同定。** Derived/PairedRestrictionIdentification.leanは
直接制限を既存bimoduleRestriction F Gへ比較し、pairedRestrictionDerivedIsoで局所化squareを得た。
pairedRestrictionPartialDerivedIsoは左制限→右制限、pairedRestrictionReverseDerivedIsoは右制限→左制限の
二つの既存導来制限の合成を、同じ既存derivedBimoduleRestriction F Gへ送る自然同型である。
それぞれの元の対象上のhom計算式を公開した。いずれも任意の可換環上で、flatness・準同値性は不要。
新しい両端制限を既存の導来制限の代わりに定義したものではない。

**外側両端と三圏の同時制限。** Derived/BimoduleEndpointRestriction.leanは
外側右比較、外側左比較の逆、上の出力側の両端制限同定を合成し、
derivedBimoduleComposeEndpointRestrictionIsoを構成した。
Derived/BimoduleSimultaneousRestriction.leanのsourceは、両因子へ既存の同時導来制限を施してから
新しい中間圏上で合成する関手族であり、targetは元の合成の出力へ既存の同時導来制限を施す関手族である。
sourceの同型は左右順序を含む両端制限の同定から独立に構成し、既存の中間圏比較を適用している。
simultaneousRestrictionDerivedComparisonは任意のF・G・Hについて定義した自然変換、
**derivedBimoduleComposeRestrictionIso**は中間Gだけが準同値の場合の自然同型であり、
そのhomが前者に一致することも証明した。
外側F・Hの準同値性や、B・D・C・Kの局所Hom K-flat性は要求しない。
必要なlocal Hom条件は元と制限後の終端E・Lだけで、六つの対象宇宙を独立に保持する。
両変数とも任意の導来対象を扱い、閉零モデルだけで比較を終えていない。

**共通sourceへの両脚。** Resolution/CompositionComparison.leanのcomparisonLeftComposeIsoは、
三つの指定解像度から共通比較sourceへの既存comparisonLeftを両因子と合成出力に使う、実際の導来合成比較である。
元のdg圏B・C・Eの対象型のsmallnessやHomのK-flat性は追加しない。
comparisonRightComposeIsoは標準解像度側から同じ共通sourceへの既存comparisonRightについて同様の比較を与える。
標準解像度を作るための元の対象型のsmallnessは後者で明示する。

**既存の解像度変更同値の合成保存。** Resolution/CompositionChange.leanの
inverseCompositionComparisonは、三つの圏同値と与えられたcurried合成比較から、
その逆同値に沿う合成比較を単位・余単位で構成する。
この圏論的操作を右脚の既存同値へ適用し、左脚の合成比較と組み合わせて
canonicalComparisonComposeIsoを構成した。
**changeComposeIso**は変更前後の標準比較同値に同じ操作を適用し、
既存のchangeEquivalenceが導来bimodule合成を自然同型で保つことを示す。
対象は実際の既存の同値のfunctorであり、選択した別の比較関手で代用していない。
変更前後の六つの解像度source宇宙は独立で、元のHomのK-flat性は不要。
対角単位・結合子とのcoherenceをこの構成の定義に仮定していない。
既存公開APIの名前・型は変更せず、34公開宣言を追加した。

**検証。** Checks.DGBimoduleSimultaneousRestrictionは、左右逆順の導来制限同定、
中間Gだけが準同値の場合の三圏同時比較と任意Gでの自然変換、独立した六つの対象宇宙、
元の対象型のsmallnessなしの比較左脚、変更前後の独立した六つのsource宇宙での
既存changeEquivalenceによる任意の導来両因子の合成保存、ZMod 2の同時比較を検査した。
既存外側左右比較・K-flat移送計算・中間比較の全導来合成則・恒等則・解像度比較・導来同値・
導来随伴・五角形・StageEight・StageSeven・Spectra.StageTwoとの統合ビルド成功（3510 jobs、警告なし）。
34公開宣言の直接公理監査は重複・欠落なく標準3公理以内。新規監査累計4599宣言。
今回の8 Leanファイルにsorry・admit・新規axiom・資源上限変更は0件。採用済み引用0件。
Lean v4.35.0-rc4とMathlib manifest/HEAD e6bbacd0e1b7307ff6e17da09cd2455f60804fa6を再確認した。

文書検査は21 Markdown・320 exposition参照を検査し、担当外の
BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの
既存未解決参照1件で失敗した。

**残件と次工程。** 両端の解像度を同時に変える既存changeEquivalenceの合成保存は今回構成した。
これらの比較が対角単位・結合子、および解像度変更の自己・推移比較と整合するcoherenceは残る。
外側左右・中間制限の比較の組合せの恒等・合成則も、モデル計算と一意性へ帰着して確認する必要がある。
これらを仕上げて§15.2全体を監査する。U12e全体は未受入、U16a〜d・U15e分解版は未着手。
目標全体と順序を保持する。共有一般論への新しいAPI要求はない。
U15e分解版では局所K-flat版のQuotient/DerivedComparison*・Verdier/を読んで再利用し、重複実装しない。
共有ルート・共有監査スクリプト・Perfect/・Endomorphism/・ScalarExtension*・並行作業の
Tensor/Associator*と他チャットの記録を編集していない。

### 17.231 U12e71：対角bimoduleの制限比較と既存解像度変更による保存（2026-10-17）

**Hom写像からの対角比較。** Bimodule/DiagonalRestriction.leanは、既存の
representableRestrictionMapを各右加群成分として使い、diagonalRestrictionMapを構成した。
対角の左作用との可換性はYonedaの全次数公式とdg関手の通常順合成保存で証明し、
Koszul符号を閉次数零だけに制限していない。各値の複体で比較射がF.mapそのものになる。
diagonalRestrictionMap_quasiIso_iffは比較射の準同型性とHomQuasiIso Fの同値であり、
本質的全射性を条件に含まない。いずれのdg圏にも局所Hom K-flat性を追加しない。

**既存の導来制限への接続。** Derived/DiagonalRestriction.leanは上の射を局所化し、
pairedRestrictionDerivedIsoで既存derivedBimoduleRestriction F Fへ送る
derivedDiagonalRestrictionMapを定義した。
derivedDiagonalRestrictionIsoはHomQuasiIso Fだけからこの射を同型化し、homの一致も証明する。
既存の右相対K-flat対角を再利用し、新しい対角や導来圏を定義していない。

**解像度変更。** Resolution/DiagonalComparison.leanのcomparisonLeftDiagonalIsoは、
指定解像度の対角を共通比較sourceの対角へ送る既存comparisonLeftの同型である。
元の対象型のsmallness・HomのK-flat性は不要。
comparisonRightDiagonalIsoとcanonicalComparisonDiagonalIsoは標準解像度側への接続であり、
標準解像度に必要な元の対象型のsmallnessを明示する。
changeDiagonalIsoは既存changeEquivalenceの実際のfunctorによる対角対象の保存を与える。
変更前後のsource宇宙は独立で、逆同値の単位同型を明示して構成した。
既存公開APIの名前・型は変更せず、14公開宣言を追加した。
これは対角対象の保存であり、changeComposeIsoと左右単位子との可換squareの証明ではない。

**検証。** Checks.DGDiagonalRestrictionは、Hom写像での値、HomQuasiIsoとの同値、
本質的全射性・局所Hom K-flat性なしの導来同型、元の対象型のsmallnessなしの比較左脚、
変更前後の独立したsource宇宙、ZMod 2を検査した。
既存同時制限・左右制限・K-flat移送・中間比較・解像度比較・導来同値・導来随伴・五角形・
StageEight・StageSeven・Spectra.StageTwoとの統合ビルド成功（3514 jobs、警告なし）。
14公開宣言の直接公理監査は重複・欠落なく標準3公理以内。新規監査累計4613宣言。
今回の4 Leanファイルにsorry・admit・新規axiom・資源上限変更は0件。採用済み引用0件。
Lean v4.35.0-rc4とMathlib manifest/HEAD e6bbacd0e1b7307ff6e17da09cd2455f60804fa6を再確認した。
文書検査は21 Markdown・320 exposition参照を検査し、担当外の
BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotientの
既存未解決参照1件で失敗した。

**残件と順序。** 合成保存と対角対象保存は既存の解像度変更同値へ接続した。
左右単位子・結合子とのcoherence、変更の自己・推移比較との整合性、
外側左右・中間制限の組合せの恒等・合成則を続け、§15.2全体を監査する。
U12eは未受入であり、U16a〜d、続くU15e分解版は未着手。目標全体の完了とはしない。
共有一般論への新しいAPI要求はない。U15e分解版では別担当の局所K-flat版
Quotient/DerivedComparison*・Verdier/を読んで再利用し、重複実装しない。
共有ルート・共有監査スクリプト・Perfect/・Endomorphism/・ScalarExtension*・並行作業の
Tensor/Associator*と他チャットの記録を編集していない。

### 17.232 U12e72：両端制限と対角比較の恒等・合成則（2026-10-17）

**直接の両端制限。** Bimodule/PairedRestrictionCoherence.leanは、既存の左右制限の
恒等比較・合成比較と、左右交換比較を組み合わせてpairedRestrictionIdIsoと
pairedRestrictionCompIsoを構成した。合成比較で左右交換を省略していない。
どちらも任意の閉零bimodule射に自然であり、値の複体へのhomが恒等となる計算式を公開する。
六つの対象宇宙は独立で、左作用側のsmallness・HomのK-flat性・準同値性は不要。

**通常の対角比較の法則。** Bimodule/DiagonalRestrictionCoherence.leanは
前回の実際のdiagonalRestrictionMapについて恒等則と合成則を証明した。
恒等関手の比較に恒等制限比較を続けると恒等射になり、Fの比較、FによるGの比較の制限、
二段階制限の合成比較を続けるとF.comp Gの対角比較そのものになる。
値で元のdg関手のHom写像へ計算し、dg関手合成の既存定義を使う。

**全導来制限と対角比較。** Derived/PairedRestrictionCoherence.leanは上の二つの自然同型を
pairedRestrictionDerivedIsoと既存の局所化前合成APIで持ち上げた。
pairedRestrictionIdDerivedIsoとpairedRestrictionCompDerivedIsoは既存の
actual derivedBimoduleRestrictionの恒等・合成比較であり、任意の導来対象で定義される。
元のbimodule上の成分を回復する計算式も公開した。local Hom K-flat性や準同値性は不要。
Derived/DiagonalRestrictionCoherence.leanのderivedDiagonalRestrictionMap_id・_compは、
これらの比較を使う実際の導来対角比較射の恒等・合成則である。
局所化表示同型の自然性と、通常の対角比較の法則から証明した。
既存公開APIの名前・型は変更せず、16公開宣言を追加した。

**検証。** Checks.DGDiagonalRestrictionCoherenceは六宇宙の任意の導来対象での
両端制限の合成・恒等比較と、ZMod 2で任意のF・Gに対する導来対角比較の合成則を検査した。
前回の対角保存・同時制限・左右制限・中間比較・解像度比較・導来同値・導来随伴・五角形・
StageEight・StageSeven・Spectra.StageTwoとの統合ビルド成功（3519 jobs、警告なし）。
16公開宣言の直接公理監査は重複・欠落なく標準3公理以内。新規監査累計4629宣言。
今回の5 Leanファイルにsorry・admit・新規axiom・資源上限変更は0件。採用済み引用0件。
固定版は前節と同じLean v4.35.0-rc4、Mathlib manifest/HEAD
e6bbacd0e1b7307ff6e17da09cd2455f60804fa6で作業した。
文書検査の再実行は21 Markdown・328 exposition参照、失敗0件。
前節の担当外未解決参照は今回の実行では再現しなかった。担当外文書は編集していない。

**残件と順序。** 対角比較自体の恒等・合成則は今回証明したが、
導来合成の左右単位子・結合子と三圏同時制限比較との可換図式はなお必要である。
その後、既存changeEquivalenceの合成保存・対角保存を自己・推移比較と照合し、
外側左右・中間比較を組み合わせた恒等・合成則を仕上げて§15.2を監査する。
U12eは未受入、U16a〜dとU15e分解版は未着手。全体の目標と順序を保持する。
共有一般論への新しいAPI要求はない。U15e分解版では別担当の局所K-flat版の
Quotient/DerivedComparison*・Verdier/を読んで再利用し、重複実装しない。
共有ルート・共有監査スクリプト・Perfect/・Endomorphism/・ScalarExtension*・並行作業の
Tensor/Associator*と他チャットの記録を編集していない。

### 17.233 U12e73：全導来中間比較と右単位子、任意K-flat解像度の比較（2026-10-17）

**現行目標。** ユーザーの目標更新を§0へ反映した。このチャットはU12eの完成・受入までを担当する。
U16・U15eは現行目標から外し、その従来の順序・分担は引継ぎ情報として保持する。

**通常の右単位square。** Tensor/RightUnitRestriction.leanは、対角のHom比較を後因子に作用させ、
中間圏制限比較、外側左制限の合成比較、制限した右単位子を続ける射が、
制限後の右単位子に一致することをrightUnitRestrictionで証明した。
各値ではbalanced tensorの包含とYoneda評価の式へ帰着し、既存の左作用の制限公式を使う。
Fは任意のdg関手で、HomのK-flat性・Hom準同型性・本質的全射性はいずれも不要。

**任意の右K-flat解像度への比較。** Derived/BimoduleResolutionLiftTensor.leanは既存の
bimoduleCanonicalResolutionLiftを再利用し、任意の前因子との相対tensor後も、
持ち上げの増大三角形が導来可換となることを証明した。
全dg自然なsourceホモトピーを既存のcylinder経由で同一視し、前因子のK-flat性は追加しない。
Derived/BimoduleMiddleKFlatIndependence.leanの
**derivedMiddleRestrictionComparison_kFlat_eq_canonical**は、この増大squareと既存の
解像度変更squareから、任意の右相対K-flat解像度による中間比較が既存標準比較に一致することを示す。
従来のsemifree解像度間の比較を、semifree性を持たない右K-flat解像度にも拡張した。
この結果にはFの準同値性は不要。終端Eの局所Hom K-flat性は既存の全導来合成と同じ条件である。

**対角によるモデル計算。** Derived/RightUnitRestriction.leanはHomQuasiIso Fの場合に、
既存対角を制限後の解像度として選び、増大射と導来合成の解像度計算同型の打消しを証明した。
derivedRightUnitRestriction_modelは実際のderivedMiddleRestrictionComparisonについて、
通常の右単位squareを局所化した計算式である。
Cの局所Hom K-flat性やFの本質的全射性は要求せず、Dの局所Hom K-flat性を明示する。

**全導来前因子上の右単位square。** Derived/RightUnitRestrictionFull.leanは、対角のHom比較、
既存の右側導来制限表示、実際のderivedMiddleRestrictionNatTrans、外側左制限の比較、
既存右単位子を合成し、rightUnitRestrictionDerivedComparisonを構成した。
これは任意Fで定義できる自然変換で、別の中間比較に置き換えていない。
source表示の成分を既存の前後因子の表示へ分解する式と、標準モデル計算への帰着も証明した。
Derived/RightUnitRestrictionCoherence.leanの
**rightUnitRestrictionDerivedComparison_eq**は、HomQuasiIso Fの下でこの自然変換が
制限後の既存derivedBimoduleRightUnitIsoに一致することを証明する。
前因子は任意の導来対象であり、その任意射に関する自然性を保持する。
Dだけに局所Hom K-flat性を要求し、Cの同条件・Fの本質的全射性・環の体や標数条件は追加しない。
独立した四つの対象・係数宇宙を保持する。既存公開APIの名前・型は変更せず、13公開宣言を追加した。

**検証。** Checks.DGRightUnitRestrictionは任意の導来前因子での右単位square、
任意の右K-flat解像度と標準モデルの一致、ZMod 2での全自然変換の等式を検査した。
対角比較の恒等・合成則、三圏同時制限、外側左右制限、中間比較の全導来合成則・恒等則、
解像度比較・導来同値・導来随伴・五角形・StageEight・StageSeven・Spectra.StageTwoとの
統合ビルド成功（3526 jobs、警告なし）。13公開宣言の直接公理監査は重複・欠落なく標準3公理以内。
新規監査累計4642宣言。今回の7 Leanファイルにsorry・admit・新規axiom・資源上限変更は0件。
採用済み引用0件。Lean v4.35.0-rc4とMathlib manifest/HEAD
e6bbacd0e1b7307ff6e17da09cd2455f60804fa6を再確認した。
文書検査は21 Markdown・326 exposition参照、失敗0件。

**受入に残る作業。** 左単位子・結合子との同様の可換図式、および今回の右単位経路と
既存の三圏同時制限の正規化の一致を確認する。
そのうえでchangeEquivalenceの合成保存・対角保存を、単位・結合・自己・推移比較へ接続する。
外側左右・中間比較を組み合わせた恒等・合成則を仕上げ、dg圏解像度の既存の一般的存在・比較と
§15.2全体を照合してU12eを受け入れる。U12e全体はなお未受入であり、目標を完了扱いにしない。
共有一般論への新しいAPI要求はない。共有ルート・共有監査スクリプト・Perfect/・Endomorphism/・
ScalarExtension*・並行作業のTensor/Associator*と他チャットの記録を編集していない。

### 17.234 U12e74：左単位squareの通常・増大・指定解像度での計算（2026-10-17）

**通常の左単位square。** Tensor/LeftUnitRestriction.leanのleftUnitRestrictionは、
対角のHom比較を前因子に作用させ、外側右制限比較、中間圏比較、制限した左単位子を続ける射が、
制限後の左単位子そのものに一致することを証明した。
ι_leftUnitRestriction_comparisonは最初の二つの比較をcoend包含で計算する式であり、
外側右制限比較が保持する左加群の同一視を省略していない。
最後は既存のYoneda評価とrightAction_restrictへ帰着する。
任意の可換環・任意のF : D → Bを扱い、Hom準同型性・本質的全射性・局所Hom K-flat性は不要。
終端Cの対象型のsmallnessも不要で、B・Dのsmallnessだけを明示する。

**任意の増大射。** Tensor/LeftUnitRestrictionAugmentation.leanは
q : R → rightRestriction F Pを任意の閉零bimodule射として扱う。
leftUnitRestriction_augmentation_exchangeは、qを対角比較および外側右制限比較と交換する式であり、
既存の外側右制限の自然性とcomposeMapの合成則から証明した。
leftUnitRestriction_augmentationは、中間比較へqを先に作用させる経路の出力が、
Rの左単位子にqを続けた射と一致することを示す。qの準同型性・RのK-flat性はここでは不要。
新たな解像度の選択や、別の中間比較を導入していない。

**既存の導来左単位子によるモデル計算。** Derived/LeftUnitRestrictionModel.leanはこのsquareを
既存局所化へ送ったleftUnitRestriction_localized_augmentationを証明した。
この局所化の式にもC-smallnessは要求しない。
derivedLeftUnitRestriction_resolutionは、Rを任意の指定右相対K-flatモデル、qを準同型としたとき、
既存の導来合成の解像度計算、対角比較、外側比較、qを使う実際のmiddleRestrictionResolvedMap、
左単位子を続けた射が、既存derivedBimoduleLeftUnitIsoそのものになることを示す。
元のPのK-flat性や制限によるK-flat保存を仮定せず、制限後のRにだけ右相対K-flat性を要求する。
Fは任意のままで、全導来合成に必要な終端Cの局所Hom K-flat性を明示する。
B・Dの同条件は追加しない。

**実際の中間比較からの計算回復。** Derived/BimoduleMiddleCalculation.leanの
derivedMiddleRestrictionComparison_calculationは、任意の前因子・指定後因子モデル・制限後モデルについて、
source計算同型の逆、既存derivedMiddleRestrictionComparison、target計算同型を続けると、
既存の通常の解像度比較射を局所化した射に一致することを証明した。
後続の制限表示の移送に使う一般補題であり、具体的対角への特殊化や左単位coherenceの完成とは区別する。
既存公開APIの名前・型は変更していない。一般API 8宣言とChecksの標数2検査宣言1件を追加した。

**検証。** Checks.DGLeftUnitRestrictionは終端Cのsmallnessなしの通常左単位square、
元のPのK-flat性なしの任意の指定解像度による導来左単位子の計算、ZMod 2での包含計算を検査した。
前回の全導来右単位square・任意K-flat解像度の中間比較独立性、対角の恒等・合成則、三圏同時制限、
外側左右制限、中間比較の全導来合成則・恒等則、解像度比較・導来同値・導来随伴・五角形・
StageEight・StageSeven・Spectra.StageTwoとの統合ビルド成功（3531 jobs、警告なし）。
9公開宣言の直接公理監査は重複・欠落なく標準3公理以内。新規監査累計4651宣言。
今回の5 Leanファイルにsorry・admit・新規axiom・資源上限変更は0件。採用済み引用0件。
Lean v4.35.0-rc4とMathlib manifest/HEAD e6bbacd0e1b7307ff6e17da09cd2455f60804fa6を再確認した。
文書検査は21 Markdown・326 exposition参照、失敗0件。

**受入に残る作業。** 左単位子のモデルsquareは今回証明したが、既存の全導来中間比較・
外側右制限比較・制限表示同型で構成する自然変換の可換図式は未完である。
一般の両因子で表示同型の自然性を先に証明し、対角を代入してモデルsquareを全導来対象へ運ぶ。
結合子の保存、左右単位経路と三圏同時制限の正規化の一致、changeEquivalenceの単位・結合保存と
自己・推移比較、外側左右・中間比較の恒等・合成則も仕上げ、§15.2全体を監査する。
U12e全体は未受入。現行目標をU12eの完成・受入に保ち、U16・U15eへは着手していない。
共有一般論への新しいAPI要求はない。共有ルート・共有監査スクリプト・Perfect/・Endomorphism/・
ScalarExtension*・並行作業のTensor/Associator*と他チャットの記録を編集していない。

### 17.235 U12e75：外側・中間の全導来比較の任意モデル計算と左単位経路（2026-10-17）

**出力制限への表示移送。** Derived/BimoduleMiddleOutputRestriction.leanは、前回の
実際のderivedMiddleRestrictionComparisonのモデル計算を、既存の出力側導来右制限へ送った。
derivedMiddleRestrictionComparison_output_restrictionと_expandedは、source表示を通して比較してから
出力を制限する経路と、通常のモデル計算射の右作用を制限してから局所化表示を通す経路の一致である。
通常の解像度比較射に対するmiddleRightRestrictionDerivedIsoの自然性を使う。
外側・中間の二つのdg関手には、Hom準同型性や本質的全射性を要求しない。

**外側右比較の任意解像度による計算。** Derived/BimoduleRightRestrictionResolution.leanは、
rightKFlatComposePresentationIsoのモデル成分が既存derivedBimoduleComposeKFlatIsoそのものになる
計算式を証明した。関手のfac等式によるeqToIsoの成分を明示しており、輸送を暗黙に消していない。
derivedBimoduleComposeRightRestrictionIso_resolution_squareは、任意の通常の後因子Qと
指定右相対K-flat解像度R → Qについて、実際の全導来外側右比較を固定Rの比較で計算するsquareである。
全導来比較の自然性と、増大射による解像度計算同型の既存fac式を使う。
_resolution_app_calcは元の前因子P上で、この計算が通常のcomposeRightRestrictionIsoと
既存の出力側局所化表示へ戻ることを証明した。QのK-flat性は不要。

**全導来中間比較の任意モデル計算。** Derived/BimoduleMiddleFullCalculation.leanの
middleDerivedSourceFamilyIdentification_hom_app_calcは、source表示を前因子・後因子の
二つの既存制限表示に分ける成分式である。
derivedMiddleRestrictionNatTrans_resolution_calculationは、全導来中間比較そのものを、
制限後の任意の指定右相対K-flat解像度で計算する式を証明する。
標準解像度での既存計算と§17.233の任意K-flat解像度の比較を接続した。
_resolution_output_restrictionは、その計算を既存の出力側導来右制限へ送った可換squareである。
semifreeモデルだけに限定せず、環や関手に追加条件を課していない。

**外側と中間を続けたモデルsquare。** Derived/BimoduleRestrictionModelCalculation.leanの
restrictedMiddleModelPrefixは、指定モデルから入力側の右制限表示と実際の全導来外側右比較を続ける射である。
**derivedBimoduleRestriction_model_calculation**は、これに出力で制限した全導来中間比較と
K-flat計算同型を続けると、通常の外側比較と実際のmiddleRestrictionResolvedMapを制限した経路に
一致することを証明した。
貼合せに必要な圏論的な打消しをprivate補題へ分離し、既存比較の可逆性やcoherenceを仮定していない。
六つの係数・対象宇宙を独立に保持し、局所Hom K-flat性は終端Eだけに要求する。
この結果は任意の両因子についての計算squareであり、対角への特殊化を済ませたという主張ではない。

**全導来左単位経路の構成。** Derived/LeftUnitRestrictionFull.leanは、対角のHom比較を
既存の外側右制限表示へ送るleftUnitRestrictionDerivedDiagonalMapを定義した。
**leftUnitRestrictionDerivedComparison**は、その射、既存の全導来外側右制限比較、前因子の左制限表示、
実際のderivedMiddleRestrictionNatTrans、既存の導来左単位子を順に続けた自然変換である。
前因子を閉零モデルへ限定せず、任意の導来対象と任意の導来射について定義される。
_appは各成分が実際の既存比較の成分の合成になる計算式。
F : D → Bは任意、局所Hom条件は終端Cだけで、HomQuasiIso Fや局所Hom条件をB・Dに加えていない。
既存の導来左単位子とこの自然変換との一致は、今回の構成・自然性とは区別して未完とする。
既存公開APIの名前・型は変更せず、一般API 13宣言とChecksの標数2検査宣言1件を追加した。

**検証。** Checks.DGRestrictionModelCalculationは、外側・中間の関手に準同値性を課さない
任意の指定右K-flatモデルによる組合せの計算、独立した六宇宙、標数2で任意の導来射についての
左単位経路の自然性を検査した。
前回の左単位モデルsquare、全導来右単位square、対角の恒等・合成則、三圏同時制限、外側左右比較、
中間比較の全導来合成則・恒等則、解像度比較・導来同値・導来随伴・五角形・StageEight・StageSeven・
Spectra.StageTwoとの統合ビルド成功（3537 jobs、警告なし）。
14公開宣言の直接公理監査は重複・欠落なく標準3公理以内。新規監査累計4665宣言。
今回の6 Leanファイルにsorry・admit・新規axiom・資源上限変更は0件。採用済み引用0件。
Lean v4.35.0-rc4とMathlib manifest/HEAD e6bbacd0e1b7307ff6e17da09cd2455f60804fa6を再確認した。
文書検査は21 Markdown・326 exposition参照、失敗0件。

**受入に残る作業。** 左単位経路の一致証明では、後因子の右制限表示を外側比較の自然性で移し、
前因子の左制限表示と上のsource成分式を合わせるsource正規化を先に確認する。
それを今回の組合せのモデルsquareへ接続し、対角射に関する解像度計算の自然性と
§17.234の左単位モデルsquareを適用する。最後にsource表示・解像度計算の同型を打ち消し、
K-flatモデル上の等式を全導来後因子へ持ち上げる。
結合子保存、左右単位経路と三圏同時制限の正規化の一致、changeEquivalenceの単位・結合保存と
自己・推移比較、外側左右・中間比較の恒等・合成則も仕上げて§15.2全体を監査する。
U12e全体は未受入。現行目標はU12eの完成・受入のままで、U16・U15eへは着手していない。
共有一般論への新しいAPI要求はない。共有ルート・共有監査スクリプト・Perfect/・Endomorphism/・
ScalarExtension*・並行作業のTensor/Associator*と他チャットの記録を編集していない。

### 17.236 U15e分割とこのチャットの担当順の再指定（2026-10-17）

最新のユーザー指定を§0へ反映した。このチャットの担当順は
U12eの完成・受入→U16→U15eの分解版とする。
§17.233〜17.235のU12eのみへの目標限定は、その時点の記録として保持し、
今後の担当範囲には今回の指定を優先する。U12eは引き続き未受入である。

U15eの局所K-flat仮定を置く版は、U17a・U13dを終えたチャットが担当し、
続けてU17bの局所K-flatの場合も扱う。成果の配置は
`Quotient/DerivedComparison*.lean`と`Verdier/`、担当記録は
[`dg-theory-u17a-u13d.md`](dg-theory-u17a-u13d.md)を参照する。
分解版に着手する際は、その定義・仮定・宇宙・比較APIを読み、再利用する。
局所K-flat版の比較やVerdier一般論を重複実装せず、分解および分解変更との接続を担当する。
公開APIの名前・型を変更する場合の§17への記録責任も保持する。

今回は担当境界と順序のみを更新した。Leanコード・公開API・受入済み検証結果・監査累計は変更しない。

### 17.237 U12e76：source正規化と対角でのモデル経路・全導来左単位子の計算（2026-10-17）

**一般のsource正規化。** Derived/BimoduleRestrictionSourceNormalization.leanの
restrictedMiddleSourcePrefixは、後因子の右制限表示、前因子の右制限表示、実際の全導来外側右比較、
出力で制限した前因子の左制限表示を続ける経路である。
restrictedMiddleSourcePrefix_normalizeは、後因子の表示を自然性で移すと、
既存middleDerivedSourceFamilyIdentificationを使う経路に一致することを証明した。
外側比較と両合成関手の自然性の三つのsquareを、privateの圏論的貼合せ補題で接続する。
restrictedMiddleSourcePrefix_modelは、任意の指定右相対K-flat解像度の計算同型の逆を前置すると、
既存restrictedMiddleModelPrefixと中間source表示を続ける経路に一致する式である。
六つの宇宙を独立に保持し、局所Hom K-flat性は終端Eだけ、F・Gは任意のdg関手のままである。

**対角への特殊化。** Derived/LeftUnitRestrictionNormalization.leanは、
既存の対角bimoduleをそのまま使うleftUnitRestrictedModelPrefixと、
対角射、既存の外側・中間比較、K-flat計算同型、通常左単位子を続ける
leftUnitRestrictionModelPathを定義した。
leftUnitRestrictionModelPath_eqは、この経路がRの通常左単位子の局所化、増大射qの局所化、
後因子Qの右制限表示を続けた射に一致することを証明する。
§17.235の実際のモデル計算square、制限表示の自然性、§17.234の増大付き左単位squareを接続する。
同じ圏が複数引数に現れる特殊化では増大射と証拠を関数の引数として推論させ、
型照合でcoendの内部を過剰に展開する問題を避けた。資源上限は変更していない。

**既存の全導来左単位子との同一sourceでの計算。** Derived/LeftUnitRestrictionSource.leanの
leftUnitRestrictionModelSourceIsoは、指定解像度の計算同型の逆と、
右制限表示を既存derivedBimoduleLeftUnitFunctorへ送った同型の合成である。
leftUnitRestrictionModelSourceIso_leftUnitは、このsource表示を通した実際の全導来左単位子が、
上と同じRの通常左単位子・増大射・右制限表示に計算されることを証明した。
leftUnitRestrictionModelPath_eq_sourceLeftUnitで二つの計算を接続した。
Qは右相対K-flat、Rは制限後の任意の指定右相対K-flat解像度、qは準同型であり、
F : D → Bの準同値性やB・Dの局所Hom K-flat性は仮定しない。終端Cの条件だけを使う。
既存の公開APIの名前・型は変更せず、一般APIを9宣言追加した。

**検証。** Checks.DGRestrictionSourceNormalizationは、任意のFと独立した対象宇宙についての
宣言型、ZMod 2での指定モデル経路と既存全導来左単位子の一致を検査した。
前回のモデル計算・左右単位・対角恒等/合成則・三圏同時制限・中間比較の全導来合成則・
解像度比較・導来同値・随伴・五角形・StageEight・StageSeven・Spectra.StageTwoとの
統合ビルド成功（3541 jobs、警告なし）。直接公理監査は9公開宣言を重複・欠落なく網羅し、
全てpropext・Classical.choice・Quot.sound以内。新規監査累計4674宣言。
今回の4 Leanファイルにsorry・admit・新規axiom・資源上限変更は0件。採用済み引用0件。
Lean v4.35.0-rc4、Mathlib manifest/HEAD e6bbacd0e1b7307ff6e17da09cd2455f60804fa6を再確認した。
文書検査は21 Markdown・326 exposition参照、失敗0件。

**受入に残る作業。** leftUnitRestrictionDerivedComparisonそのものを、今回のsource表示を通して
leftUnitRestrictionModelPathへ計算する等式はまだ証明していない。
対角射に対する解像度計算同型と後因子制限表示の自然性を使って対角射を移し、
restrictedMiddleSourcePrefix_modelへ接続する。その後今回の一致式でsource同型を打ち消し、
K-flat対象上の等式を全導来後因子へ持ち上げる。
結合子保存、左右単位経路と三圏同時制限の正規化の一致、changeEquivalenceの単位・結合保存と
自己・推移比較、外側左右・中間比較の恒等・合成則も残り、§15.2全体の受入監査は未完である。
U12e全体は未受入。共有一般論への新しいAPI要求はない。
共有ルート・共有監査スクリプト・並行担当ファイル・他チャットの記録は編集していない。

### 17.238 U12e77：全導来左単位経路と既存左単位子の一致（2026-10-17）

**対角射の輸送。** Derived/LeftUnitRestrictionTransport.leanの
leftUnitRestrictionModelSourceIso_diagonalは、対角の通常Hom比較を局所化した射について、
指定解像度計算同型と後因子の右制限表示を続けた自然変換の自然性を適用する式である。
これにより、source表示の後で全導来関手に対角射を作用させる経路を、
固定Rの導来合成に対角射を作用させてからsource表示へ進む経路へ移す。
補助の自然性は通常の関手圏のprivate補題で証明し、dg比較のcoherenceを仮定していない。

**全導来経路のモデル計算。** leftUnitRestrictionDerivedPrefixは、既存の全導来経路の
対角射・外側右比較・前因子の左制限表示までの部分である。
leftUnitRestrictionDerivedPrefix_modelは、この部分を上の対角輸送と§17.237の
restrictedMiddleSourcePrefix_modelで計算したsquareである。
leftUnitRestrictionDerivedComparison_modelは、さらに実際の全導来中間比較と
既存全導来左単位子を続けると、§17.237のleftUnitRestrictionModelPathそのものに
一致することを証明する。モデル経路の存在だけで全導来比較との一致を代用していない。
対角部分と残りの中間比較・左単位部分を分けて検証し、資源上限は変更していない。

**任意の導来対象上の左単位coherence。** Derived/LeftUnitRestrictionCoherence.leanの
leftUnitRestrictionDerivedComparison_kFlatは、任意の指定右相対K-flat解像度Rと準同型qについて、
既存source同型を打ち消し、右K-flat後因子Q上で実際の全導来比較と既存左単位子を同一視する。
leftUnitRestrictionDerivedComparison_eqは、制限後の標準右K-flat解像度と
rightKFlatDerivedNatTrans_extを使い、任意の全導来後因子へこの一致を持ち上げる。
公開結論は次の自然変換の等式である。

```lean
leftUnitRestrictionDerivedComparison A B D C F hC =
  whiskerLeft (derivedBimoduleRestriction A D C B C F (DGFunctor.id C))
    (derivedBimoduleLeftUnitIso A D C hC).hom
```

係数Aは任意の可換環、B・D・Cの対象宇宙は独立、各対象添字にSmall.{u}を要求する。
F : D → Bは任意で、HomQuasiIso・本質的全射性・準同値性を要求しない。
局所Hom K-flat性は終端Cだけで、B・Dには追加しない。
旧公開APIの名前・型は変更せず、新規一般APIを6宣言追加した。

**検証。** Checks.DGLeftUnitRestrictionCoherenceは、指定解像度を使うモデル計算の型、
指定モデルの打消し、全導来自然変換の一致を検査した。
ZMod 2でも任意の導来対象Q上の成分の一致を、Fの準同値性なしで検査している。
前回のsource正規化・モデル計算、左右単位、対角恒等/合成則、三圏同時制限、
中間比較の恒等/合成則、解像度比較・導来同値・随伴・五角形・StageEight・StageSeven・
Spectra.StageTwoとの統合ビルド成功（3544 jobs、警告なし）。
直接公理監査は6公開宣言を重複・欠落なく網羅し、標準3公理以内。新規監査累計4680宣言。
今回の3 Leanファイルにsorry・admit・新規axiom・資源上限変更は0件。採用済み引用0件。
Lean v4.35.0-rc4とMathlib manifest/HEAD e6bbacd0e1b7307ff6e17da09cd2455f60804fa6を再確認した。
文書検査は21 Markdown・326 exposition参照、失敗0件。

**次の受入作業。** 全導来左単位経路の一致は今回証明した。
次は結合子保存の通常/指定解像度squareを構成し、既存の
derivedBimoduleAssociatorResolutionIso_base_facと解像度変更の独立性を使って
全三因子に自然な結合比較へ運ぶ。局所Hom K-flat条件や後二因子の指定モデルを省略しない。
左右単位経路と既存三圏同時制限の正規化の一致、changeEquivalenceの単位・結合保存と
自己・推移比較、外側左右・中間比較の恒等・合成則も仕上げ、§15.2全体を監査する。
U12e全体はなお未受入であり、今回の左単位coherenceだけで目標を完了扱いにしない。
共有一般論への新しいAPI要求はない。共有ルート・共有監査スクリプト・並行担当の
Tensor/Associator*・Perfect/・Endomorphism/・ScalarExtension*・他チャットの記録は編集していない。

### 17.239 U12e78：外側左作用の制限と通常結合子の可換square（2026-10-17）

**通常の三因子の比較。** 新規Tensor/AssociatorLeftRestriction.leanは、
既存composeLeftRestrictionIsoとassociatorIsoをそのまま使う。
composeMap_leftRestrictionIso_valueは、内側合成Q⊗Rの外側左制限比較を
後因子の射としてPとの合成へ作用させると、各値で恒等射になることを証明した。
既存ι_composeValueMapとcomposeLeftRestrictionIso_hom_valueを明示的に適用し、
coendの包含による射の判定を使う。
associatorValue_leftRestrictionは、結合子の各値がRを左制限してから評価しても、
元のRをGの対象写像で評価しても同じになる式である。
結合子の値に隠された等式輸送の定義を必要な箇所だけ明示して確認した。

**associatorIso_leftRestriction**は、P : B–C、Q : C–E、R : E–T、G : D → Tに対し、
次の二つの経路の一致を全Hom自然な閉零bimodule射の圏で証明する。

- (P⊗Q)⊗G*Rから結合子でP⊗(Q⊗G*R)へ進み、内側Q⊗Rの左制限比較、
  外側P⊗(Q⊗R)の左制限比較を続ける経路。
- (P⊗Q)⊗G*Rから外側左制限比較でG*((P⊗Q)⊗R)へ進み、
  元の結合子をG*で制限する経路。

係数Aは任意の可換環で、六つの宇宙を独立に保持する。
smallnessはB・C・Eだけに要求し、終端T・Dには要求しない。
局所Hom K-flat性、GのHom準同型性・本質的全射性は仮定しない。
通常の射の一致であり、固定K-flat導来結合子や全導来三因子の比較を完了したとはしない。
旧公開APIの名前・型は変更せず、一般APIを3宣言追加した。

**検証。** Checks.DGAssociatorLeftRestrictionは上のsquareの全仮定・宇宙を確認し、
ZMod 2でT・Dのsmallnessやflatnessなしの値の比較を検査した。
§17.238までの全導来左単位・source正規化・右単位・三圏同時制限・解像度比較・
中間比較の恒等/合成則・導来随伴・同値・五角形・StageEight・StageSeven・
Spectra.StageTwoとの統合ビルド成功（3546 jobs、警告なし）。
3公開宣言の直接公理監査は重複・欠落なく標準3公理以内。新規監査累計4683宣言。
今回の2 Leanファイルにsorry・admit・新規axiom・資源上限変更は0件。採用済み引用0件。
固定環境は§17.238と同じ。文書検査は21 Markdown・326 exposition参照、失敗0件。

**次工程。** この通常squareを、既存derivedComposeWithLeftRestrictionIsoと
rightKFlatDerivedAssociatorの局所化前の計算式へ適用し、固定した後二つの右相対K-flat因子と
任意の導来前因子で外側左制限が結合子を保つ図式へ運ぶ。
次いで指定解像度の計算squareと独立性を使って全三因子へ移す。
外側右・中間制限との結合子square、三圏同時制限との正規化、changeEquivalenceの
単位・結合保存と自己・推移比較、恒等・合成則も残り、U12e全体は未受入である。
共有一般論への新しいAPI要求はない。既存の並行担当Tensor/AssociatorLeftCompatibility・
AssociatorLeftTransport・AssociatorRightCompatibilityとそのChecks、共有ルート・共有監査スクリプト・
他チャットの記録は編集していない。

### 17.240 U12e79：固定K-flat因子の結合子保存と実際の全導来比較のモデルsquare（2026-10-17）

**固定K-flat二因子。** Derived/AssociatorLeftRestrictionBase.leanの
derivedComposeWithLeftRestrictionIso_base_appは、固定右相対K-flat後因子の左制限比較を、
元の前因子上で通常比較の局所化と既存の出力制限表示の合成へ正規化する。
Derived/AssociatorLeftRestrictionKFlat.leanの
rightKFlatDerivedAssociator_leftRestrictionは、Q : C–E、R : E–Tを右相対K-flatとし、
G : D → Tの左制限について、次の二経路の一致を任意の導来前因子に自然な自然変換として証明した。

- QとG*Rの固定K-flat導来結合子、内側の通常左制限比較を導来合成へ送った射、
  Q⊗Rの固定K-flat左制限比較を続ける経路。
- Rの固定K-flat左制限比較をQとの導来合成へ作用させ、
  Q・Rの既存固定K-flat導来結合子を出力の左制限へ送る経路。

§17.239の通常squareを局所化し、出力制限表示の自然性を接続する証明である。
前因子のK-flat性、局所Hom K-flat性、GのHom準同型性・本質的全射性は不要。
係数Aは任意の可換環、B・C・E・T・Dの対象宇宙は独立、各添字にSmall.{u}を要求する。

**実際の全導来左比較の逆の計算。** Derived/AssociatorLeftRestrictionPresentation.leanは、
既存derivedBimoduleComposeLeftRestrictionIsoの逆について、指定モデルの可換squareを証明した。
derivedBimoduleComposeLeftRestrictionIso_inv_model_squareは、既存hom側のsquareからの打消しで得る。
leftRestrictionDerivedComposeSourceBaseIso_hom_appと
leftRestrictionDerivedComposeTargetBaseIso_hom_appは、
source表示をK-flat合成表示の出力制限、target表示を後因子制限表示の逆と
制限後K-flat合成表示の合成として同定する。
derivedBimoduleComposeLeftRestrictionIso_inv_model_calculationは、この計算を
任意の導来前因子に自然な固定K-flat比較として明示した式である。
_inv_base_calculationは、元の前因子Pに対して、実際の逆比較とK-flat値計算を続ける経路が、
後因子の表示の逆、制限後のK-flat値計算、通常左制限比較、出力制限表示に戻る式である。
これらは終端二圏の局所Hom K-flat条件を明示し、PのK-flat性は要求しない。

**内側・入れ子・二段階合成の表示。** Derived/AssociatorLeftRestrictionInner.leanの
derivedLeftRestriction_inner_model_squareは、上の逆比較を、既存の
derivedBimoduleComposeInnerComparisonIsoによる両側の内側合成の表示へ接続した。
Derived/AssociatorLeftRestrictionNested.leanのderivedLeftRestriction_nested_prefix_squareと
_nested_model_squareは、その内側square、実際の全導来比較の自然性、
K-flat合成表示の自然性を貼り合わせ、既存の入れ子表示を通して固定モデルの経路へ計算する。
Derived/AssociatorLeftRestrictionPair.leanのderivedLeftRestriction_pair_model_squareは、
二段階合成側でも既存derivedBimoduleComposePairComparisonIsoを通した同じ計算を証明する。
貼合せは通常の圏・関手圏のprivate補題で行い、coherenceを新しい仮定にしていない。
全導来逆比較の計算を独立した補題として検証してから貼り合わせ、資源上限は変更していない。

**既存の全導来結合子との合流。** Derived/AssociatorLeftRestrictionModel.leanの
derivedBimoduleAssociator_leftRestriction_rightKFlatは、後二因子が指定Q・Rの局所化像の場合に、
実際のderivedBimoduleAssociatorと実際の全導来左制限比較の逆からなる二経路を同一視する。
両側の既存associator比較square、入れ子側と二段階合成側の計算、
今回の固定K-flat結合子保存を接続し、共通の入れ子表示同型を右から打ち消す。
前因子は任意の導来対象、局所Hom K-flat条件はE・T・Dで、B・Cには追加しない。
Gは任意のままであり、後二因子も任意の導来対象とした結論はまだ主張しない。
旧公開APIの名前・型は変更していない。一般APIを12宣言、Checksの標数2検査を1宣言追加した。

**検証。** Checks.DGAssociatorLeftRestrictionKFlatは、標数2・任意の導来前因子について、
局所Hom K-flat条件やGの準同値性なしの固定因子の可換図式を検査した。
実際の全導来モデルsquareの型もZMod 2へ適用して確認している。
§17.239までの通常square、全導来左単位・右単位・source正規化・三圏同時制限・
中間比較の恒等/合成則・解像度比較・導来随伴・同値・五角形・StageEight・StageSeven・
Spectra.StageTwoとの統合ビルド成功（3554 jobs、警告なし）。
13公開宣言の直接公理監査は重複・欠落なく標準3公理以内。新規監査累計4696宣言。
今回の8 Leanファイルにsorry・admit・新規axiom・資源上限変更は0件。採用済み引用0件。
Lean v4.35.0-rc4とMathlib manifest/HEAD e6bbacd0e1b7307ff6e17da09cd2455f60804fa6を再確認した。
文書検査は21 Markdown・326 exposition参照、失敗0件。

**次工程と未受入条件。** 今回の外側左制限の全導来結合子squareは、
後二因子が指定K-flatモデルの局所化像である場合までである。
次は両経路を後二因子にも自然な関手族として束ねるか、既存の導来同型による比較squareを使い、
任意の全導来後二因子へ持ち上げる。必要なE・T・Dの局所Hom条件を省略しない。
外側右・中間制限の結合子square、左右単位経路と三圏同時制限の正規化、
changeEquivalenceの単位・結合保存と自己・推移比較、外側左右・中間の恒等・合成則も残る。
§15.2全体の受入監査は未完であり、U12e全体を完了扱いにしない。
共有一般論への新しいAPI要求はない。共有ルート・共有監査スクリプト・既存の並行担当
Tensor/Associator*・Perfect/・Endomorphism/・ScalarExtension*・他チャットの記録は編集していない。


### 17.241 U12e80：全三因子の外側左制限と通常の外側右制限の結合子square（2026-10-17）

**担当順の保持。** 最新のユーザー指定に従い、U12eの完成・受入→U16→U15e分解版の順を維持する。
U15e局所K-flat版と続くU17b局所K-flatの場合はU17a/U13dを終えたチャットの担当である。
分解版では、そのQuotient/DerivedComparison*.leanとVerdier/の定義・仮定・宇宙・比較APIを
読んで再利用し、比較・Verdier一般論を重複実装しない。分担の詳細は§0・§17.236を参照する。

**全導来三因子の外側左制限。** Derived/AssociatorLeftRestrictionFamilies.leanは、
左右両経路を後二因子R・Qにも自然な関手族の自然変換として束ねる。
leftRestrictionAssociatorLeftPath_app・RightPath_appはその成分を既存比較の合成へ計算する。
Derived/AssociatorLeftRestrictionCoherence.leanのleftRestrictionAssociatorPaths_eqは、
rightKFlatDerivedNatTrans_extを二回適用し、§17.240の固定モデルsquareから両経路の一致を証明する。
derivedBimoduleAssociator_leftRestrictionは、任意の導来Q : C–E、R : E–Tと
任意の導来前因子に対する、実際の全導来結合子と外側左制限比較の可換squareである。
局所Hom K-flat性はE・T・Dに要求し、B・Cには要求しない。G : D → Tは任意のdg関手。
六つの宇宙を独立に保持し、対象添字にSmall.{u}を要求する。一般API11宣言と標数2検査1宣言を追加した。

**通常の外側右制限。** Tensor/AssociatorRightRestrictionElements.leanと
AssociatorRightRestrictionPathElements.leanは、三つの斉次元からなる両経路の計算を証明する。
Tensor/RightRestrictionValueHom.leanは既存chainMapOfComponentFunctionsを再利用し、
右制限比較を固定成分関数で表示する。composeRightRestrictionValueHom_eqにより、
元のcomposeRightRestrictionValueIsoのhomと同じ射である。新しい比較データや符号規約は導入しない。
Tensor/AssociatorRightRestrictionComponents.lean・AssociatorRightRestrictionValues.leanは、
成分計算と既存三重tensorの外延性を使って値のchain mapの一致へ運ぶ。
Tensor/AssociatorRightRestriction.leanのassociatorIso_rightRestrictionは、その値の一致から
通常bimodule圏で外側右制限が結合子を保つsquareを証明する。
F : D → Bは任意、局所Hom K-flat性は不要、終端Tのsmallnessも要求しない。
係数は任意の可換環、六つの宇宙を独立に保持する。一般API16宣言と標数2検査1宣言を追加した。
標数2検査は次数−2・3・−1の三因子を扱う。

**検証。** Checks.DGAssociatorLeftRestrictionCoherenceとDGAssociatorRightRestriction、
§17.240までの制限比較・単位子・解像度・中間比較・導来随伴・五角形・StageEight・StageSeven・
Spectra.StageTwoを含む統合ビルドに成功した（3564 jobs、警告なし）。
今回の29公開宣言を直接公理監査し、重複・欠落なくpropext・Classical.choice・Quot.sound以内。
新規監査累計4725宣言。今回の10 Leanファイルにsorry・admit・新規axiom・資源上限変更は0件。
旧公開APIの名前・型は変更していない。採用済み引用0件。
Lean v4.35.0-rc4とMathlib manifest/HEAD e6bbacd0e1b7307ff6e17da09cd2455f60804fa6を再確認した。
文書検査は21 Markdown・326 exposition参照、失敗0件。

**残条件。** 外側左制限の結合子squareは全導来三因子まで完了した。
外側右制限は今回通常版までであり、次にそのsquareを固定K-flat導来比較、全導来比較へ運ぶ。
中間制限の結合子square、左右単位経路と三圏同時制限の正規化、changeEquivalenceの
単位・結合保存と自己・推移比較、外側左右・中間の恒等・合成則も残る。
§15.2全体の受入監査は未完であり、U12e全体を完了扱いにしない。U16・U15e分解版は未着手。
共有一般論への新しいAPI要求はない。共有ルート・共有監査スクリプト・並行担当Tensor/Associator*・
Perfect/・Endomorphism/・ScalarExtension*・Quotient/DerivedComparison*・Verdier/・
他チャットの記録は編集していない。
