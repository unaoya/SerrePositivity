# BS-D3　drafts の主張の具体化　作業報告

## 第1部　停止点1完了・A5 の先行定義（基準 main `789259c90`）

### 完全 site と比較写像

- A0 の site には `perfectPrism_quotientEquiv` と R → S の合成で A/d 代数構造を与え、cutoff の上界から小さい模型を選んだ。完全対象の包含に沿って O を A 代数値、CAlg_A 値、D(A) 値の順に読む。flat 位相の生成 sieve は一つの (p,d) 完全忠実平坦射からなる被覆のもの。層性の証明で使うのは B₁ ⊗̂_{B₀} B₁ の相対 Čech 項。
- Perfd の余積では、T₁ ⊗̂_R T₂ の中で二つの S 作用の差を割り、その商に既存の `exists_perfectoidization_of_perfectoid_surjective_quotient` を適用する。完備標的への延長で (T₁ ⊗̂_S T₂)_perfd の単位を得る。左右の構造射を指定した `BinaryCofan` を反復し、各標準脚と有限余積の普遍性で単体写像を定めた。A5-2 の普遍環も Prop 8.5 もこの構成には使わない。
- Lemma 4.8 は承認された有界標的版。商の射を一意に持ち上げる証明は `Andre.existsUnique_perfectPrismHomLift_to_bounded` そのもの。B ↦ (S → B/J) を Hom 上も指定して κ 以下の perfectoid 標的への同値を取る。有界性は A0 の site の対象がもつ。原典の Lemma 4.8 の標的は任意の prism。[Bhatt–Scholze, Lemma 4.8](https://arxiv.org/pdf/1905.08229#page=38)
- D3-01 により、第0脚は S2 の CAlg 値 RΓ の射影の型にした。多項式分解では射影を各段で取り、Frobenius 両立性は O の Frobenius の自然性から得る。A3 の `prismMapOfDiscrete` は離散性の仮定の下で H⁰ を読んだもの。各段の脚は τ = Res_{φ_A} として τⁿ(f) に φ_B⁻ⁿ を後合成する。同じ錐の脚として全 B と全 n の整合性を指定し、塔の余極限の脚と完備化単位に沿って Δ_perf から O の極限への比較射を記述した。[Bhatt–Scholze, §8.1](https://arxiv.org/pdf/1905.08229#page=64)

### Semiperfectoid の場合

- G-A5-17 は A_inf の射を有界版 Lemma 4.8 で選び、A2 の完備底変換の単位と S⊗ᴸ_R R₁ → S を合成した比較辺の可逆性を述べる。完備余接複体は A2 の `cotangentWedge` の第1外冪で読む。semiperfectoid の場合はその上界 −1、HT の連結性、Δ と Δ_perf の連結性を順に指定した。L^∧ が次数 −1 に集中するという仮定は使わない。離散性から perfectoid 性へは A7 の `DiscreteCore` を使う。
- `IsSemiperfectoid` に S 自身の導来 p 完備性と perfectoid 環の全射商という条件を置いた。R 線形な全射表示は別の (α)。Cor 7.3 の一つの存在証人から普遍環、環インスタンス、指定単位を取る。Thm 7.4 の全射性でこの標的は cutoff 内にあり、その試験 prism への比較の脚を mod d、H⁰ と順に写すと `perfectoidizationToUniversal` になる。分裂は S の下で、最終比較は環同型とその H⁰ に一致する CAlg_R の頂点同型。
- 根変数は有限台の指数をもつ加法モノイド環で表した。核の生成元を同時に発根する p 完備忠実平坦な拡大を取り、第0段の変数を殺した完備商から底変換後の S への評価を、各段の根の像で指定した。π₁(L/p) の全射性は標準多項式表示の余接複体の p 倍の cone の H⁻¹ をサイクルと境界で指定した。有限部分集合の包含による余錐と完備圏での perfd の余極限を経て、有限変数では全段の根を殺す商を Prop 7.10 で得る。最後に全射性を反映する。

### 依存先・要確認

- `PerfectSite.lean` の `-- 要確認：ScalarRestriction へ` は1件、`discreteRestrictionIso`。離散な A 代数 B の構造射を φ_A と合成したものの離散埋め込みと、元の埋め込みの `cAlgRestrictScalars φ_A` による制限を比較する。この同型を通して完備な試験環の Frobenius の逆を読んだ。`ScalarRestriction.lean` は編集していない。
- 第0脚の仮置きは A0/S2 の CAlg 値 RΓ の射影待ち。A2 の `prismaticCohomologyCAlg` はこの基準でまだ `True`。A4 の `discreteDeltaFrobenius`、`completeCAlgInclusion`、`modPrismFunctor`、`directHodgeTateUnit` を既存の名前で使用した。A2 の底変換 (4)、HT filtration の具体化も証明の依存先。W9-III-08 の完備テンソルの perfectoid 性は、2a 後の E3 非依存の芯を使う予定。
- D3-02（`2bb0d406c`）で、全 `PerfUnder_u` の opposite に対し S3 側の `CechNerveDataLarge` の四欄を供給できた。κ 以下の完全 site は小さい `CechNerveData` のまま。大きい版の極限判定 `isLimitCone_iff_restrict_cech_large` は基盤待ちで、使用先は次の停止点の `limit_perfUnder_eq_tot`。停止点1では両極限の一致は使わない。

### 件数と確認範囲

基準にあった結論 `True` を PerfectSite で8件、SemiperfectoidCase で17件、計25件具体化した。さらに `universalPerfectoidRing : Type u := sorry` を選択した普遍環に置き換えた。二種類の集計は計26件。既に型を持っていた `perfectFlatTopology`、`IsSemiperfectoid`、`universalPerfectoidUnit` の本体、環インスタンスや比較用の補助宣言は別集計。対象2ファイルの `True` 宣言・`Type u := sorry` はいずれも0件。`-- 要確認：` は PerfectSite 1件、SemiperfectoidCase 0件。

設計側の `3acedf8eb`（有界版 Lemma 4.8）、`1480a4e5c`（D3-01）、`2bb0d406c`（D3-02）を読み、最後の二つに取り込まれた A5 の途中差分も含めて照合した。ほかに新しい設計判断はない。原典と照合した箇所、既存の宣言名と引数、基準の25件の名前、import パス、括弧、差分の空白を静的に確認した。指示どおり Lean の型検査・ビルドは行っていない。停止点2には進んでいない。

## 第2部　停止点2・A5 の降下と Prop 8.5（基準 main `624dfe2f2`）

### 具体化した宣言

| ファイル | 基準で結論が `True` だった宣言 | 主張 |
| --- | ---: | --- |
| RootAdjunction | 2 | 通常の環の filtered 余極限の比較射 `colimit.post` は同型。多項式環への根添加の標準射は p 完備忠実平坦。 |
| StrongDescent | 11 | Δ と Δ_perf の根添加の射についての Lemma 8.6、一変数への帰着、任意の離散係数での RHom、Koszul による上界、de Rham 比較と Cartier 射。 |
| WeaklyInitialAndDescent | 15 | E 被覆、弱始対象、大小の Čech 極限、filtered 余極限との交換、有限型への帰着、Lemma 8.6 による左右の降下。 |
| PerfectSiteComparison | 8 | Prop 8.5 の比較射と位相版、κ 版・Type u 版の極限、prism の選択、Cor 7.3 との一致、animated 版と系4。 |

計36件。指示書の PerfectSiteComparison は7件とあるが、列挙された名前と基準ファイルには系4を含めて8件ある。別に、既に型のあった `rootClosure_isSemiperfectoid` で perfectoid 基底の証人 `hR` を明示した。四ファイルで結論 `True` と `Type u := sorry` はいずれも0件。

- 根添加では、E の各段を多項式環の商、E を通常の環の可算余極限とした。係数と変数の添字を同じ射で移すので、filtered 比較は指定された `colimit (D ⋙ E) → E (colimit D)`。S̃ の各段では完備化し、用途を弱始性と濃度評価に限った。有限型への帰着に使う被覆では `E(colimit D)^∧` と各段の完備余極限を比較する。多項式環から T_∞ への射は変数を第0段の根に送る。平坦性はこの射の加群構造についての `IsCompletelyFaithfullyFlat`。
- Lemma 8.6 は実際の根添加射を `discreteDeltaFunctor` と `directPerfectionFunctor` で送った二辺について `IsDescendableOver` を述べる。一変数の内部補題にだけ index ≤ 2 が現れる。C=A/(p,φ⁻¹(d)) 上の任意の離散加群 L を取ると、二乗した fiber からの RHom は `(∏ (C[X^p] ⊗_C L))[1]` で上界は −1。有限二元 Koszul 複体 K の Postnikov 各段に随伴を適用し、双対可能な K での RHom とテンソルの比較を経て、冪の塔の逆極限で M に戻る。de Rham 比較は両端の同型が根添加射と可換であること、Cartier は次数 0・1 の積を保つ指定鎖写像が擬同型であることを型にした。
- E 被覆の弱始性は `C^∧ → E(C)^∧ → Q(E(C)^∧)` に対する補題として明示した。全 perfectoid 標的には `IsWeaklyTerminalLarge`、κ 側には小さい S3 を使い、E3 の `targetCAlgDiagram` の極限錐を同じ Tot の頂点に取る。完全 site 上の O の極限は perfectoid 試験環の prism を与える関手の点ごとの右 Kan 拡張で関手化した。mod d を取った Ō は別の CAlg_R 値前層。降下の両側に用いる錐は S → S̃^• の増大から得る指定錐で、射影は広い押し出しの構造射と完備化単位の合成。
- Prop 8.5 は停止点1の比較射自身の `IsIso`。J ≤ flat のときは O の J 層性と S2 により同じ比較を RΓ_J に移す。animated 版の始域は `CompleteAnimatedAlgebra p R`、試験 site は π₀ S で取る。系4は切り捨て単位 S → π₀ S の `prismaticPerfectionAnimated` と `perfectoidizationAnimated` による像の可逆性。どの同型を用いるかが分かるよう、単に両端の頂点が同型であるという形から射を区別した。

### 要確認と依存先

`-- 要確認：` は RootAdjunction 0件、StrongDescent 5件、WeaklyInitialAndDescent 1件、PerfectSiteComparison 3件。内訳は次のとおり。

| 場所 | 待っているもの |
| --- | --- |
| StrongDescent・`fiberSquareRHom` | M15 の Mod_D の fiber・相対テンソル・内部 Hom と D(A) への忘却。D は一般に非離散。 |
| StrongDescent・`prismScalarExtension` | ScalarRestriction へ。M13 の `cAlgRestrictScalars q` の左随伴としての CAlg 係数拡大。D 側は既存の `derivedInfinityBaseChange`。 |
| StrongDescent・`rootDeRhamSource` | A1-5。一変数の外積付き de Rham cdga の E∞ 実現。 |
| StrongDescent・`rootDeRhamAugmentation` | A1-5。X を第0段の変数に、dX を 0 に送る射の実現。 |
| StrongDescent・`rootMap_modP_eq_deRham` | A1-5 の `deRham_iso_polynomial_modP`、`deRham_iso_rootAlgebra_modP` の型と自然性。 |
| WeaklyInitialAndDescent・`limit_perfUnder_eq_tot` | D3-02。S3 の `isLimitCone_iff_restrict_cech_large` とその錐の延長。小さい版の `exists_limitCone_of_cech` は型付き。 |
| PerfectSiteComparison・`perfectCoefficientPresentable` | G12 の CAlg_A の presentability。S4 の `sheafification_exists_cAlg` に渡す。 |
| PerfectSiteComparison・`perfdOverPerfectPrism` | BS-D4 で、別の完全 prism 上の離散 Frobenius を、Lemma 4.8 を通じて A4 の `discreteDeltaFrobenius` の同じ成分に接続する。 |
| PerfectSiteComparison・`piZeroReflection` | A2 の π₀ と切り捨て単位。完備な離散代数の埋め込み `completeDiscreteToAnimated` の左随伴の型で指定。 |

A2 待ちの Δ、Frobenius、完備 CAlg への反射、mod d には、A4・A7 の `discreteDeltaFrobenius`、`completeCAlgInclusion`、`reflectCompleteCAlg`、`modPrismFunctor`、`prismaticPerfectionAnimated`、`perfectoidizationAnimated` を通した。後二者は既存の `animatedDelta` と `animatedDeltaFrobenius` を使う。G-A5-17、(5) と完備テンソルとの可換性、任意の位相に対する S2・S4 は証明の依存先。A7 の UniversalProperty に依存する単位を A5 に持ち込まず、π₀ の単位は A7-1 の離散埋め込みから取った。

### 設計との差と確認範囲

途中で、離散環上の `IsDescendable` と当初は引数のなかった `IsDescendableOver` のどちらも Δ_T 上の射を受け取れないことを報告した。D3-04（`df86ebb71`）で基盤側に非離散底の型が確定したので、それに合わせた。押し出し・Tot・テンソル・RHom・Frobenius 余極限・完備化の証明は Shared/Descendable の一般底版 (a)〜(h) 待ち。ほかに設計上の変更はない。

基準との差分には `df86ebb71` に入った RootAdjunction と WeaklyInitialAndDescent の途中差分も含めて照合した。指定四ファイルの元の宣言名と件数、既存の定義の向き、実ファイルの import パス、括弧と空白を静的に確認した。Lean の型検査・ビルドは実行していない。停止点3の A6 は未着手。

## 第3部　停止点3完了・A6 の excision（基準 main `0ba4a1ce5`、S8 の入口 `4f5235673`）

### 集合の層と Cor 8.12

- S → T × S/I は、I が試験射の核に含まれるかどうかで二つの延長を分ける。両方で W=V を取る。対角の射は T ⊗̂_S T からの乗法と商の完備テンソルへの射の対。後者は通常の環の押し出しの比較を `completionMap` で送る。S/I → S′/IS′ の左逆は S′=T×S/I としたときの第二射影で、H⁰ 完備化でも分裂が残る。
- 冪等元の因子 eT は T/(1−e) とした。二つの perfectoid 標的の積とその構造射を与える関手に `isIntegralPerfectoid_prod` を使い、圏同値を逆向きに読んだ。perfd の積保存は二本の環射影を脚とする錐の極限性。取り替え後の引き戻しの cospan は (g,id_C) と (h,id_C) で、g は T からの商射、h は S/I からの比較射に由来する。
- D3-06（`d0ee7ce76`）に従い、集合の層の延長は Mathlib の比較同値の `.functor`、制限は `.inverse` とした。延長を制限する単位同型と、延長の値を S→P の圏で取る極限は別の宣言。集合の等化子の判定は有限積保存と一点被覆の生成 sieve での相対 Čech 条件を使う。得られる集合の引き戻しと、Hom 層の対応する押し出しは、それぞれ指定した四射の `IsPullback`・`IsPushout`。商の脚の `Mono` は完備化前の商射の全射性から得る。
- O の係数は global な site で `ArcZ = ULift ℤ`。F_U の元 (P,l) における R 代数構造を R→U→P とし、`elementStructure_forget` で ℤ に制限すると元の O の引き戻しに戻る。S・I の完備性から得る商の完備性は S/I について述べた。T/IT を含む四角形ではすべての環の射を H⁰ 完備化関手で送る。Hom 層の完備化同型は `completionUnit` に沿う前合成を成分とする自然同型。
- Fontaine の式は W(PreTilt(R×S)) をまず W(PreTilt R × PreTilt S)、次に W(PreTilt R) × W(PreTilt S) へ送り、θ_R × θ_S と合成する環準同型の等式。両同型の順方向は環射影から定めた。θ を使う節には両因子で p が非単元という既存の仮定があり、零環の因子は外側の積定理で扱う。

### D3-07 で具体化した3件

- **完備な T の切断。** 小さい圏の対象 (P,l : T→P) に R→T→P を付けると、R の構造射を指定した perfectoid 試験環上の Hom 前層の元になる。`markedTargetEquiv` はその圏同値。これを S8 の `sectionsOf_eq_limit_elements` に渡し、A5 の `perfectoidization_isLimit` の錐と同じ頂点の錐に移して、`sectionsOf_homSheaf_eq_perfectoidization` を CAlg_R の `VertexIso` とした。A5 の cutoff 以下の弱始対象と Čech 項が共通の κ に入ることを仮定に明示した。
- **押し出しの局所同値。** `homPresheafPushout_localEquiv` は、完備化した四隅を Yoneda で表す affCompl_κ と、Hom 層で表す affPerfd_κ の二つで、S8 の `presheafPushout` から F_S への指定射が `IsLocalEquivSet` を満たすことを述べる。前者は全ての集合の arc 層に `sheafOfSets_excision` を適用する。後者には S8 の `sections_localEquiv_iso` を適用し、Γ(F_S,O) → Γ(P,O) の向きで可逆性を得る。
- **非完備な入力と四角形の自然性。** `sectionsOf_homSheaf_eq_e3Perfd` は U が非完備でも Γ(F_U,O) と e3Perfd(U) を比較する。U とその射に共通の κ を取り、`homPresheaf_completionRing_iso` を経て、関手の自然同型 `sectionsFunctorIsoE3` の U 成分を使う。`sections_excision_square` は Γ の指定四角形の引き戻し性。`perfectoidization_excision` は、同じ四角形にこの自然同型を適用した `IsPullbackSquare`。T/IT に完備性を要求せず、商写像と二つの合成二単体も比較に含めた。

### BS-D3 全体の件数

開始時の main `789259c90` と完了時の同名宣言を照合した。既存宣言 **88件**を具体化した。新設の補助宣言と、既に具体的な型だった `e3Excision` は件数に含めていない。

| 停止点 | 結論の `True` を具体化 | 環の `Type u := sorry` を具体化 |
| --- | ---: | ---: |
| 1・完全 site と semiperfectoid の場合 | 25 | 1 |
| 2・降下と Prop 8.5 | 36 | 6 |
| 3・集合の層、Cor 8.12、Fontaine θ | 20 | 0 |
| 合計 | 81 | 7 |

環の型7件は `universalPerfectoidRing`、`rootAdjunctionStep`、`rootClosure`、`algebraicRootClosure`、`polyAlgebra`、`polyRootAlgebra`、`rootCover`。停止点3の20件の内訳は SheafOfSetsExcision の13件、Excision の6件、PerfectoidFiniteProduct の1件。指示書に Excision は5件とあるが、完備化同型と Γ の自然同型を別々に数えると列挙された宣言は6件になる。

### 要確認と基盤待ち

- **停止点3の名前の照合。** A6 の今回の3ファイルに新しい仮名を示す `-- 要確認：` は0件。従来の有限積ファイルには Fin の積を分解する Mathlib 名の確認注記がある。可逆性の名前は `SerrePositivity.InfinityCategories.IsInvertibleEdge`（本体 `InfinityCategories/Core/InvertibleEdgeLifting.lean`）。引数は `SSet.Truncated.Edge` で、A6 は `(Sheaves.sectionsOf_map …).toTruncated` と明示した。Mathlib の `SSet.Edge` はこの切り捨ての辺と定義上等しい。
- **A2・A0/S2。** `prismaticEvaluation` は CAlg 値 RΓ の指定射影待ち（D3-01）。離散 Frobenius は `discreteDeltaFrobenius`、Δ と完備化・mod d は A4 の `completeCAlgInclusion`、`reflectCompleteCAlg`、`modPrismFunctor`、単位は `directHodgeTateUnit` を参照する。animated 版は A7 の `animatedDelta` と `animatedDeltaFrobenius`、離散切り捨ては A5 の `piZeroReflection`。A6 の Γ の比較では A2 の仮名を追加していない。
- **S3・係数制限・降下。** 大きい添字の極限判定と錐の延長（D3-02）、G12 の CAlg の presentability、A1-5 の `rootDeRhamSource`・`rootDeRhamAugmentation`・`rootMap_modP_eq_deRham`、M15 の `fiberSquareRHom` と `IsDescendableOver` の一般底版の性質（D3-04）が証明待ち。離散係数の比較は D3-03 の `cAlgRestrictScalars_algebraEmbedding`、係数拡大と忘却との両立は D3-05 の `cAlgBaseChange` と `cAlgBaseChange_forget` で入口が確定済み。停止点1・2で付けた個々の確認項目は第1・2部の表にある。
- **S8。** D3-07 によって集合の前層の局所同値、`sectionsOf`、`sectionsOf_map`、`sections_localEquiv_iso`、`sectionsOf_eq_limit_elements` を型つきで使用できる。S8-4 の `sectionsOf_pushout` は `True` のままで、Cor 8.12 の証明理由に「sectionsOf_pushout（引き戻しの述語）待ち」と記した。離散な押し出しと空間値層化の比較（S8-2・3）も基盤側の証明待ち。

停止点3で確認を要した設計の扱いは D3-06 の延長の向きと D3-07 の S8 の入口で解決した。数学的な主張は変更していない。D3-07 のコミットに取り込まれた途中差分も含めて、名前・型の向き・変更対象・import の実在・括弧・差分の空白を静的に確認した。指示どおり Lean の型検査・ビルドは実行していない。

### 残る True の一覧

BS-D3 の対象9ファイルの結論 `True` は0件。以下は D3-07 を含む完了時の drafts 全体の一覧で、仮定・構造の欄・コメント・証明内の `True` は数えていない。

<details>
<summary>drafts 全体に残る、結論が True の名前つき宣言（119件）</summary>

- `A1/CrystallineInput.lean`（2件）　`crystalline_deRham_polynomial_Zp`、`hodgeTate_of_deRham_cartier`
- `A1/DeRhamComparisonPoly.lean`（4件）　`deRham_iso_polynomial_crystalline`、`deRham_iso_polynomial_universal`、`deRham_iso_polynomial_modP`、`deRham_iso_rootAlgebra_modP`
- `A1/HodgeTateComparison.lean`（14件）　`hodgeTate_iso_polynomial_Zp`、`hodgeTate_iso_crystalline`、`universalOrientedPrism_frobenius_flat`、`crystallineCoverMap_conservative`、`crystallineCoverMap_torAmplitude`、`crystallineCoverMap_prismaticCohomology`、`hodgeTate_iso_of_construction61`、`baseChangeB`、`baseChangeC`、`baseChangeB_conservative`、`baseChange_cechAlexanderAffine_eq`、`hodgeTate_iso`、`bockstein_sq_zero'`、`prismaticCohomology_baseChange'`
- `A1/HodgeTateMap.lean`（5件）　`reducedModel`、`hodgeTateMapZero`、`hodgeTateMapOne`、`bockstein_sq_zero`、`hodgeTateMap`
- `A2/AnimatedAlgebra.lean`（5件）　`polyCoproduct_isCoproduct`、`polyYoneda_fullyFaithful`、`animatedAlgebra_siftedColimits`、`discreteToAnimated_poly`、`discreteToAnimated_fullyFaithful`
- `A2/BaseChangeAndTensor.lean`（5件）　`derivedPrismaticCohomology_baseChange`、`derivedPrismaticCohomology_siftedColimit`、`prismaticCohomologyPoly_tensor`、`derivedPrismaticCohomology_tensor`、`derivedPrismaticCohomology_completion_animated`
- `A2/DerivedPrismaticCohomology.lean`（9件）　`completeCAlg_siftedColimits`、`prismaticCohomologyCAlg`、`prismaticCohomologyCAlg_eq_totEInfinity`、`prismaticFrobeniusPoly`、`derivedPrismaticCohomology_preservesSifted`、`derivedPrismaticCohomology_poly`、`derivedPrismaticFrobenius`、`derivedPrismaticCohomologyDerived`、`derivedPrismaticCohomology_h0_ring`
- `A2/HodgeTateFiltration.lean`（7件）　`hodgeTatePoly_gr`、`hodgeTatePoly_bounded`、`hodgeTateFiltration_step`、`hodgeTateFiltration_gr`、`hodgeTateFiltration_exhaustive`、`hodgeTateFiltration_zero`、`hodgeTateUnitCAlg`
- `A3/DiscreteCase.lean`（3件）　`deltaStructure_of_envelopeIso`、`discrete_weaklyInitial`、`exists_initial_of_discrete`
- `A3/LciAndQuasiregular.lean`（10件）　`lciDerivedEnvelope`、`lciDerivedEnvelope_eq_prismatic`、`lciDerivedEnvelope_isEnvelope_of_discrete`、`lci_envelope_surjective_invert_p_universal`、`prismaticCohomology_lci_eq_envelope`、`qrsp_isDiscretePrismatic`、`qrsp_completelyFaithfullyFlat`、`regularSemiperfectoid_prismatic`、`qrsp_initial`、`rootQuotient_prismatic_perfection_eq`
- `DerivedGeneral/CompletionFunctor.lean`（5件）　`completion_isReflective`、`completion_tensor_koszul`、`completion_exact`、`complete_colimit`、`completedBaseChange`
- `DerivedGeneral/ScalarRestriction.lean`（4件）　`derivedInfinityBaseChange_restrictScalars_adjunction`、`cAlgBaseChange_restrictScalars_adjunction`、`derivedInfinityRestrictScalars_completion`、`cAlgRestrictScalars_h0`
- `DerivedGeneral/Truncation.lean`（5件）　`truncationLE_counit`、`truncation_cofiber`、`tStructure_axioms`、`truncationLE_of_isConnective`、`derived_nakayama`
- `Shared/CosimplicialBockstein.lean`（4件）　`regularShortExact`、`bockstein_leibniz`、`bockstein_sq`、`bockstein_natural`
- `Shared/CosimplicialCupProduct.lean`（1件）　`cohomologyCup_map`
- `Shared/CosimplicialEInfinity.lean`（5件）　`totEInfinity_forget`、`totEInfinity_cohomologyRing`、`totEInfinity_isLimitCone`、`totEInfinity_map`、`derivedGlobalSectionsCAlg_eq_totEInfinity`
- `Shared/Descendable.lean`（16件）　`isDescendableOver_unit_iff`、`isDescendableOver_pushout`、`isDescendableOver_comp`、`isDescendableOver_tensor`、`isDescendableOver_tot_equiv`、`hasDescentIndexLEOver_two_of_rhom`、`hasDescentIndexLEOver_frobeniusColimit`、`isDescendableOver_complete`、`isDescendable_baseChange`、`isDescendable_comp`、`isDescendable_tensor`、`isDescendable_tot_equiv`、`hasDescentIndexLE_two_of_rhom`、`hasDescentIndexLE_frobeniusColimit`、`isDescendable_complete`、`isDescendable_of_faithfullyFlat`
- `Shared/EInfinityPowerOperation.lean`（4件）　`powerOperationZero_zero`、`powerOperationZero_natural`、`powerOperationZero_natTrans`、`powerOperationZero_eq_frobenius_tot`
- `Sheaves/CAlgValued.lean`（3件）　`forget_conservative`、`forget_sheafify`、`forget_derivedGlobalSections`
- `Sheaves/CechConerveLimit.lean`（1件）　`isLimitCone_iff_restrict_cech_large`
- `Sheaves/GlobalSections.lean`（1件）　`sheafifyUnit_isEquivalence_of_isSheaf`
- `Sheaves/SpaceValued.lean`（6件）　`sheafification_exists_spaces`、`sheafify_discrete_eq`、`localEquiv_of_sheafifyIso`、`discretePushout_isDiscrete`、`sectionsOf_pushout`、`sectionsOf_colimit`

</details>
